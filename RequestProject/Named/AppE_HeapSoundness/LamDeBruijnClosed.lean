module

public import RequestProject.Named.AppE_HeapSoundness.LamDeBruijn

@[expose] public section

/-!
# Which `λfip` expressions have a de Bruijn representation

`LExpr.toLTerm Γ e` succeeds exactly when `LExpr.Scoped` holds: the free names of `e` are
in scope and every lambda body only mentions its parameters and its recorded variables
(`LExpr.toLTerm_isSome_iff`).  In particular `LTerm 0` represents exactly the closed
expressions whose lambdas are correctly annotated (`LExpr.toLTerm_empty_isSome_iff`).
`LExpr.Scoped` is stronger than "every free name is in scope" (`LExpr.Scoped.fv`), since the
free variables `fv` of a lambda are, by definition, its recorded variables `z̄`:
`lam_wrong_annotation` is a lambda with no free variable and no de Bruijn representation.
-/

namespace FIPNamed.Lam

theorem Scope.ofCaptured_isSome :
    ∀ (zs : List LVal) (s : String), (Scope.ofCaptured zs s).isSome ↔ s ∈ capturedNames zs
  | [], s => by simp [Scope.ofCaptured, capturedNames]
  | z :: zs, s => by
    have ih := Scope.ofCaptured_isSome zs s
    cases z with
    | var x =>
      cases x with
      | name s' =>
        by_cases h : s' = s
        · subst h; simp [Scope.ofCaptured, capturedNames]
        · have h' : ¬ s = s' := fun e => h e.symm
          simp [Scope.ofCaptured, capturedNames, h, h', ih]
      | loc l => simp [Scope.ofCaptured, capturedNames, ih]
    | _ => simp [Scope.ofCaptured, capturedNames, ih]

private theorem isSome_bind_pure {α β γ : Type} (x : Option α) (y : Option β) (f : α → β → γ) :
    (do let a ← x; let b ← y; pure (f a b) : Option γ).isSome ↔ x.isSome ∧ y.isSome := by
  cases x <;> cases y <;> simp

private theorem extend_pred {n : Nat} (Γ : Scope n) (xs : List Binder) :
    (fun s => (Γ.extend xs s).isSome = true) = fun s => s ∈ xs.map (·.name) ∨ (Γ s).isSome := by
  funext s; rw [FIPNamed.Scope.extend_isSome]

private theorem captured_pred (zs : List LVal) (xs : List Binder) :
    (fun s => ((Scope.ofCaptured zs).extend xs s).isSome = true) =
      fun s => s ∈ xs.map (·.name) ∨ s ∈ capturedNames zs := by
  funext s; rw [FIPNamed.Scope.extend_isSome, Scope.ofCaptured_isSome]

mutual
theorem LVal.toLTVal_isSome_iff {n : Nat} (Γ : Scope n) :
    ∀ v : LVal, (v.toLTVal Γ).isSome ↔ LVal.Scoped (fun s => (Γ s).isSome) v
  | .var (.name s) => by simp [LVal.toLTVal, LVal.Scoped]
  | .var (.loc l) => by simp [LVal.toLTVal, LVal.Scoped]
  | .fn f => by simp [LVal.toLTVal, LVal.Scoped]
  | .ctor c vs => by
    simp only [LVal.toLTVal, LVal.Scoped, Option.isSome_map]
    exact LVal.toLTVals_isSome_iff Γ vs
  | .lam zs xs e => by
    simp only [LVal.toLTVal, LVal.Scoped]
    rw [isSome_bind_pure, LVal.toLTVals_isSome_iff Γ zs, LExpr.toLTerm_isSome_iff _ e,
      captured_pred]
theorem LVal.toLTVals_isSome_iff {n : Nat} (Γ : Scope n) :
    ∀ vs : List LVal, (LVal.toLTVals Γ vs).isSome ↔ LVal.ScopedList (fun s => (Γ s).isSome) vs
  | [] => by simp [LVal.toLTVals, LVal.ScopedList]
  | v :: vs => by
    simp only [LVal.toLTVals, LVal.ScopedList]
    rw [isSome_bind_pure, LVal.toLTVal_isSome_iff Γ v, LVal.toLTVals_isSome_iff Γ vs]
theorem LExpr.toLTerm_isSome_iff {n : Nat} (Γ : Scope n) :
    ∀ e : LExpr, (e.toLTerm Γ).isSome ↔ LExpr.Scoped (fun s => (Γ s).isSome) e
  | .ret vs => by
    simp only [LExpr.toLTerm, LExpr.Scoped, Option.isSome_map]
    exact LVal.toLTVals_isSome_iff Γ vs
  | .app e1 e2 => by
    simp only [LExpr.toLTerm, LExpr.Scoped]
    rw [isSome_bind_pure, LExpr.toLTerm_isSome_iff Γ e1, LExpr.toLTerm_isSome_iff Γ e2]
  | .call f e1 e2 => by
    simp only [LExpr.toLTerm, LExpr.Scoped]
    rw [isSome_bind_pure, LExpr.toLTerm_isSome_iff Γ e1, LExpr.toLTerm_isSome_iff Γ e2]
  | .letIn xs e1 e2 => by
    simp only [LExpr.toLTerm, LExpr.Scoped]
    rw [isSome_bind_pure, LExpr.toLTerm_isSome_iff Γ e1, LExpr.toLTerm_isSome_iff _ e2,
      extend_pred]
  | .match x bs => by
    simp only [LExpr.toLTerm, LExpr.Scoped]
    rw [isSome_bind_pure, LVal.toLTVal_isSome_iff Γ x, LExpr.toLBranches_isSome_iff Γ bs]
  | .dup x e => by
    simp only [LExpr.toLTerm, LExpr.Scoped]
    rw [isSome_bind_pure, LVal.toLTVal_isSome_iff Γ x, LExpr.toLTerm_isSome_iff Γ e]
  | .drop x e => by
    simp only [LExpr.toLTerm, LExpr.Scoped]
    rw [isSome_bind_pure, LVal.toLTVal_isSome_iff Γ x, LExpr.toLTerm_isSome_iff Γ e]
  | .dropru x k e => by
    simp only [LExpr.toLTerm, LExpr.Scoped]
    rw [isSome_bind_pure, LVal.toLTVal_isSome_iff Γ x, LExpr.toLTerm_isSome_iff Γ e]
  | .free k e => by
    simp only [LExpr.toLTerm, LExpr.Scoped, Option.isSome_map]
    exact LExpr.toLTerm_isSome_iff Γ e
  | .alloc k e => by
    simp only [LExpr.toLTerm, LExpr.Scoped, Option.isSome_map]
    exact LExpr.toLTerm_isSome_iff Γ e
theorem LExpr.toLBranches_isSome_iff {n : Nat} (Γ : Scope n) :
    ∀ bs : List LBranch, (LExpr.toLBranches Γ bs).isSome ↔
      LExpr.ScopedB (fun s => (Γ s).isSome) bs
  | [] => by simp [LExpr.toLBranches, LExpr.ScopedB]
  | .mk c xs e :: bs => by
    simp only [LExpr.toLBranches, LExpr.ScopedB]
    rw [isSome_bind_pure, LExpr.toLTerm_isSome_iff _ e, extend_pred,
      LExpr.toLBranches_isSome_iff Γ bs]
end

/-- **`LTerm 0` means closed.**  A named `λfip` expression has a closed de Bruijn
    representation exactly when it has no free name and the body of each of its lambdas
    only mentions its parameters and recorded variables. -/
theorem LExpr.toLTerm_empty_isSome_iff (e : LExpr) :
    (e.toLTerm Scope.empty).isSome ↔ LExpr.Scoped (fun _ => False) e := by
  rw [LExpr.toLTerm_isSome_iff]
  have : (fun s => (Scope.empty s).isSome = true) = fun _ => False := by
    funext s; simp [Scope.empty]
  rw [this]

mutual
theorem LVal.Scoped.fv {P : String → Prop} :
    ∀ {v : LVal}, LVal.Scoped P v → ∀ s, Var.name s ∈ v.fv → P s
  | .var (.name s'), h, s, hs => by
    simp only [LVal.fv, List.mem_singleton, Var.name.injEq] at hs; subst hs; exact h
  | .var (.loc _), _, s, hs => by simp [LVal.fv] at hs
  | .fn _, _, s, hs => by simp [LVal.fv] at hs
  | .ctor _ vs, h, s, hs => LVal.ScopedList.fv (v := vs) h s (by simpa [LVal.fv] using hs)
  | .lam zs _ _, h, s, hs => LVal.ScopedList.fv (v := zs) h.1 s (by simpa [LVal.fv] using hs)
theorem LVal.ScopedList.fv {P : String → Prop} :
    ∀ {v : List LVal}, LVal.ScopedList P v → ∀ s, Var.name s ∈ LVal.fvList v → P s
  | [], _, s, hs => by simp [LVal.fvList] at hs
  | v :: vs, h, s, hs => by
    simp only [LVal.fvList, List.mem_append] at hs
    rcases hs with hs | hs
    · exact LVal.Scoped.fv h.1 s hs
    · exact LVal.ScopedList.fv h.2 s hs
end

mutual
/-- A well-scoped expression has all its free names (in the sense of `LExpr.fv`) in
    scope. -/
theorem LExpr.Scoped.fv {P : String → Prop} :
    ∀ {e : LExpr}, LExpr.Scoped P e → ∀ s, Var.name s ∈ e.fv → P s
  | .ret vs, h, s, hs => LVal.ScopedList.fv (v := vs) h s (by simpa [LExpr.fv] using hs)
  | .app e1 e2, h, s, hs => by
    simp only [LExpr.fv, List.mem_append] at hs
    exact hs.elim (LExpr.Scoped.fv h.1 s) (LExpr.Scoped.fv h.2 s)
  | .call _ e1 e2, h, s, hs => by
    simp only [LExpr.fv, List.mem_append] at hs
    exact hs.elim (LExpr.Scoped.fv h.1 s) (LExpr.Scoped.fv h.2 s)
  | .letIn xs e1 e2, h, s, hs => by
    simp only [LExpr.fv, List.mem_append, List.mem_filter, decide_eq_true_eq] at hs
    rcases hs with hs | ⟨hs, hn⟩
    · exact LExpr.Scoped.fv h.1 s hs
    · rcases LExpr.Scoped.fv h.2 s hs with h' | h'
      · exact absurd (by simpa [Binder.vars] using h') hn
      · exact h'
  | .match x bs, h, s, hs => by
    simp only [LExpr.fv, List.mem_append] at hs
    exact hs.elim (LVal.Scoped.fv h.1 s) (LExpr.ScopedB.fv h.2 s)
  | .dup x e, h, s, hs => by
    simp only [LExpr.fv, List.mem_append] at hs
    exact hs.elim (LVal.Scoped.fv h.1 s) (LExpr.Scoped.fv h.2 s)
  | .drop x e, h, s, hs => by
    simp only [LExpr.fv, List.mem_append] at hs
    exact hs.elim (LVal.Scoped.fv h.1 s) (LExpr.Scoped.fv h.2 s)
  | .dropru x _ e, h, s, hs => by
    simp only [LExpr.fv, List.mem_append] at hs
    exact hs.elim (LVal.Scoped.fv h.1 s) (LExpr.Scoped.fv h.2 s)
  | .free _ e, h, s, hs => LExpr.Scoped.fv (e := e) h s (by simpa [LExpr.fv] using hs)
  | .alloc _ e, h, s, hs => LExpr.Scoped.fv (e := e) h s (by simpa [LExpr.fv] using hs)
theorem LExpr.ScopedB.fv {P : String → Prop} :
    ∀ {bs : List LBranch}, LExpr.ScopedB P bs → ∀ s, Var.name s ∈ LExpr.fvB bs → P s
  | [], _, s, hs => by simp [LExpr.fvB] at hs
  | .mk _ xs e :: bs, h, s, hs => by
    simp only [LExpr.fvB, List.mem_append, List.mem_filter, decide_eq_true_eq] at hs
    rcases hs with ⟨hs, hn⟩ | hs
    · rcases LExpr.Scoped.fv h.1 s hs with h' | h'
      · exact absurd (by simpa [Binder.vars] using h') hn
      · exact h'
    · exact LExpr.ScopedB.fv h.2 s hs
end

/-- The lambda `λ^[] x. y` records no variable, so it has no free variable (`fv`), but its
    body mentions `y`: it has no de Bruijn representation, in any scope. -/
theorem lam_wrong_annotation :
    (LVal.lam [] [{ name := "x" }] (.ret [.var (.name "y")])).fv = [] ∧
      ∀ {n : Nat} (Γ : Scope n),
        (LVal.toLTVal Γ (.lam [] [{ name := "x" }] (.ret [.var (.name "y")]))).isSome = false := by
  refine ⟨rfl, fun Γ => ?_⟩
  rfl

end FIPNamed.Lam
