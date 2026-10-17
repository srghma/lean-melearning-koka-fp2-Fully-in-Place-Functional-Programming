module

public import RequestProject.Named.Sec2_Calculus.DeBruijn.Syntax

@[expose] public section

/-!
# `Term 0` is exactly the closed expressions

`Expr.toTerm Γ e` succeeds exactly when every free name of `e` is bound by the scope `Γ`
(`Expr.toTerm_isSome_iff`).  In particular a named expression has a de Bruijn
representation `Term 0` exactly when it has no free name (`Expr.toClosed_isSome_iff`), and
a function definition has a well-scoped version exactly when its body mentions no name
other than its parameters (`FunDef.toTFunDef_isSome_iff`).
-/

namespace FIPNamed

theorem Scope.extend_isSome {n : Nat} (Γ : Scope n) :
    ∀ (xs : List Binder) (s : String),
      (Γ.extend xs s).isSome ↔ (s ∈ xs.map (·.name) ∨ (Γ s).isSome)
  | [], s => by simp [Scope.extend]
  | x :: xs, s => by
    by_cases h : x.name = s
    · simp [Scope.extend, h]
    · simp only [Scope.extend, h, if_false, Option.isSome_map, List.map_cons, List.mem_cons]
      rw [Scope.extend_isSome Γ xs s]
      have h2 : ¬ s = x.name := fun e => h e.symm
      simp [h2]

theorem Scope.empty_isSome (s : String) : (Scope.empty s).isSome = false := rfl

private theorem isSome_bind_pure {α β γ : Type} (x : Option α) (y : Option β) (f : α → β → γ) :
    (do let a ← x; let b ← y; pure (f a b) : Option γ).isSome ↔ x.isSome ∧ y.isSome := by
  cases x <;> cases y <;> simp

mutual
theorem Val.toTVal_isSome_iff {n : Nat} (Γ : Scope n) :
    ∀ v : Val, (v.toTVal Γ).isSome ↔ ∀ s, Var.name s ∈ v.fv → (Γ s).isSome
  | .var (.name s) => by simp [Val.toTVal, Val.fv]
  | .var (.loc l) => by simp [Val.toTVal, Val.fv]
  | .fn f => by simp [Val.toTVal, Val.fv]
  | .ctor c vs => by
    simp only [Val.toTVal, Val.fv, Option.isSome_map]
    exact Val.toTVals_isSome_iff Γ vs
  | .lit k => by simp [Val.toTVal, Val.fv]
theorem Val.toTVals_isSome_iff {n : Nat} (Γ : Scope n) :
    ∀ vs : List Val, (Val.toTVals Γ vs).isSome ↔ ∀ s, Var.name s ∈ Val.fvList vs → (Γ s).isSome
  | [] => by simp [Val.toTVals, Val.fvList]
  | v :: vs => by
    simp only [Val.toTVals, Val.fvList, List.mem_append]
    rw [isSome_bind_pure, Val.toTVal_isSome_iff Γ v, Val.toTVals_isSome_iff Γ vs]
    constructor
    · rintro ⟨h1, h2⟩ s (h | h)
      exacts [h1 s h, h2 s h]
    · intro h
      exact ⟨fun s hs => h s (.inl hs), fun s hs => h s (.inr hs)⟩
end

private theorem filter_mem_iff (l : List Var) (xs : List Binder) (s : String) :
    Var.name s ∈ l.filter (fun v => v ∉ Binder.vars xs) ↔
      Var.name s ∈ l ∧ s ∉ xs.map (·.name) := by
  simp [Binder.vars]

private theorem extend_cond {n : Nat} (Γ : Scope n) (xs : List Binder) (l : List Var) :
    (∀ s, Var.name s ∈ l → (Γ.extend xs s).isSome) ↔
      ∀ s, Var.name s ∈ l.filter (fun v => v ∉ Binder.vars xs) → (Γ s).isSome := by
  simp only [filter_mem_iff, Scope.extend_isSome]
  constructor
  · rintro h s ⟨hs, hn⟩
    rcases h s hs with h | h
    · exact absurd h hn
    · exact h
  · intro h s hs
    by_cases hn : s ∈ xs.map (·.name)
    · exact .inl hn
    · exact .inr (h s ⟨hs, hn⟩)

mutual
/-- `Expr.toTerm Γ e` succeeds exactly when every free name of `e` is in scope. -/
theorem Expr.toTerm_isSome_iff {n : Nat} (Γ : Scope n) :
    ∀ e : Expr, (e.toTerm Γ).isSome ↔ ∀ s, Var.name s ∈ e.fv → (Γ s).isSome
  | .ret vs => by
    simp only [Expr.toTerm, Expr.fv, Option.isSome_map]; exact Val.toTVals_isSome_iff Γ vs
  | .app e1 e2 => by
    simp only [Expr.toTerm, Expr.fv, List.mem_append]
    rw [isSome_bind_pure, Expr.toTerm_isSome_iff Γ e1, Expr.toTerm_isSome_iff Γ e2]
    exact ⟨fun ⟨h1, h2⟩ s h => h.elim (h1 s) (h2 s),
      fun h => ⟨fun s hs => h s (.inl hs), fun s hs => h s (.inr hs)⟩⟩
  | .call f e1 e2 => by
    simp only [Expr.toTerm, Expr.fv, List.mem_append]
    rw [isSome_bind_pure, Expr.toTerm_isSome_iff Γ e1, Expr.toTerm_isSome_iff Γ e2]
    exact ⟨fun ⟨h1, h2⟩ s h => h.elim (h1 s) (h2 s),
      fun h => ⟨fun s hs => h s (.inl hs), fun s hs => h s (.inr hs)⟩⟩
  | .letIn xs e1 e2 => by
    simp only [Expr.toTerm, Expr.fv, List.mem_append]
    rw [isSome_bind_pure, Expr.toTerm_isSome_iff Γ e1, Expr.toTerm_isSome_iff _ e2,
      extend_cond]
    exact ⟨fun ⟨h1, h2⟩ s h => h.elim (h1 s) (h2 s),
      fun h => ⟨fun s hs => h s (.inl hs), fun s hs => h s (.inr hs)⟩⟩
  | .bmatch e bs => by
    simp only [Expr.toTerm, Expr.fv, List.mem_append]
    rw [isSome_bind_pure, Expr.toTerm_isSome_iff Γ e, Expr.toBranches_isSome_iff Γ bs]
    exact ⟨fun ⟨h1, h2⟩ s h => h.elim (h1 s) (h2 s),
      fun h => ⟨fun s hs => h s (.inl hs), fun s hs => h s (.inr hs)⟩⟩
  | .dmatch e bs => by
    simp only [Expr.toTerm, Expr.fv, List.mem_append]
    rw [isSome_bind_pure, Expr.toTerm_isSome_iff Γ e, Expr.toBranches_isSome_iff Γ bs]
    exact ⟨fun ⟨h1, h2⟩ s h => h.elim (h1 s) (h2 s),
      fun h => ⟨fun s hs => h s (.inl hs), fun s hs => h s (.inr hs)⟩⟩
  | .drop x e => by
    simp only [Expr.toTerm, Expr.fv, List.mem_append]
    rw [isSome_bind_pure, Val.toTVal_isSome_iff Γ x, Expr.toTerm_isSome_iff Γ e]
    exact ⟨fun ⟨h1, h2⟩ s h => h.elim (h1 s) (h2 s),
      fun h => ⟨fun s hs => h s (.inl hs), fun s hs => h s (.inr hs)⟩⟩
  | .free k e => by
    simp only [Expr.toTerm, Expr.fv, Option.isSome_map]; exact Expr.toTerm_isSome_iff Γ e
  | .prim op vs => by
    simp only [Expr.toTerm, Expr.fv, Option.isSome_map]; exact Val.toTVals_isSome_iff Γ vs
/-- `Expr.toBranches Γ bs` succeeds exactly when every free name of `bs` is in scope. -/
theorem Expr.toBranches_isSome_iff {n : Nat} (Γ : Scope n) :
    ∀ bs : List Branch, (Expr.toBranches Γ bs).isSome ↔
      ∀ s, Var.name s ∈ Expr.fvBranches bs → (Γ s).isSome
  | [] => by simp [Expr.toBranches, Expr.fvBranches]
  | .mk c xs e :: bs => by
    simp only [Expr.toBranches, Expr.fvBranches, List.mem_append]
    rw [isSome_bind_pure, Expr.toTerm_isSome_iff _ e, extend_cond,
      Expr.toBranches_isSome_iff Γ bs]
    exact ⟨fun ⟨h1, h2⟩ s h => h.elim (h1 s) (h2 s),
      fun h => ⟨fun s hs => h s (.inl hs), fun s hs => h s (.inr hs)⟩⟩
end

/-- **`Term 0` means closed.**  A named expression has a closed de Bruijn
    representation exactly when it has no free (program) name. -/
theorem Expr.toClosed_isSome_iff (e : Expr) :
    e.toClosed.isSome ↔ ∀ s, Var.name s ∉ e.fv := by
  rw [Expr.toClosed, Expr.toTerm_isSome_iff]
  simp [Scope.empty_isSome]

/-- A function definition is well scoped (its body becomes a `Term (|x̄| + |ȳ|)`) exactly
    when the only free names of its body are its parameters. -/
theorem FunDef.toTFunDef_isSome_iff (fd : FunDef) :
    fd.toTFunDef.isSome ↔
      ∀ s, Var.name s ∈ fd.body.fv → s ∈ fd.borrowed.map (·.name) ∨ s ∈ fd.owned.map (·.name) := by
  rw [FunDef.toTFunDef, Option.isSome_map, Expr.toTerm_isSome_iff]
  refine forall_congr' fun s => imp_congr_right fun _ => ?_
  rw [Scope.extend_isSome]
  simp only [Scope.ofBinders, Option.isSome_map, Scope.extend_isSome, Scope.empty_isSome]
  simp

end FIPNamed
