module

public import RequestProject.Named.Sec2_Calculus.DeBruijn.Syntax

@[expose] public section

/-!
# From indices back to names: every `Term n` comes from a named expression

`Term.toExpr nm t` prints a de Bruijn term with names: the variable bound at *level* `l`
(the `l`-th binder from the outside) is called `nm l`.  For an injective naming `nm`,
resolving the names of the printed expression gives back the term
(`Term.toExpr_toTerm`); in particular every closed term `t : Term 0` is the resolution of a
closed named expression (`Term.toExpr_toClosed`).  So `Expr.toTerm` is onto, and `Term n`
is exactly the named syntax up to the choice of bound names.

`primeName` (`x`, `x'`, `x''`, …) is a concrete injective naming.
-/

namespace FIPNamed

section
variable (nm : Nat → String)

/-- The binders `x̄` introduced at levels `n, …, n + |sc| - 1`: the `j`-th binder (index `j`)
    is at level `n + |sc| - 1 - j`. -/
def mkBinders (n : Nat) : List Bool → List Binder
  | [] => []
  | b :: sc => { name := nm (n + sc.length), scalar := b } :: mkBinders n sc

theorem flags_mkBinders (n : Nat) : ∀ sc : List Bool, Binder.flags (mkBinders nm n sc) = sc
  | [] => rfl
  | b :: sc => by simp [mkBinders, Binder.flags] at *; exact flags_mkBinders n sc

mutual
/-- Print a value of scope `n`: the index `i` is the variable at level `n - 1 - i`. -/
def TVal.toVal {n : Nat} : TVal n → Val
  | .bvar i => .var (.name (nm (n - 1 - i)))
  | .loc l => .var (.loc l)
  | .fn f => .fn f
  | .ctor c vs => .ctor c (TVal.toVals vs)
  | .lit k => .lit k
/-- Print a list of values. -/
def TVal.toVals {n : Nat} : List (TVal n) → List Val
  | [] => []
  | v :: vs => TVal.toVal v :: TVal.toVals vs
end

mutual
/-- Print a term of scope `n` with named binders. -/
def Term.toExpr {n : Nat} : Term n → Expr
  | .ret vs => .ret (TVal.toVals nm vs)
  | .app e1 e2 => .app (Term.toExpr e1) (Term.toExpr e2)
  | .call f e1 e2 => .call f (Term.toExpr e1) (Term.toExpr e2)
  | .letIn sc e1 e2 => .letIn (mkBinders nm n sc) (Term.toExpr e1) (Term.toExpr e2)
  | .bmatch e bs => .bmatch (Term.toExpr e) (TBranches.toBranches bs)
  | .dmatch e bs => .dmatch (Term.toExpr e) (TBranches.toBranches bs)
  | .drop x e => .drop (TVal.toVal nm x) (Term.toExpr e)
  | .free k e => .free k (Term.toExpr e)
  | .prim op vs => .prim op (TVal.toVals nm vs)
/-- Print branches. -/
def TBranches.toBranches {n : Nat} : TBranches n → List Branch
  | .nil => []
  | .cons c sc e bs => .mk c (mkBinders nm n sc) (Term.toExpr e) :: TBranches.toBranches bs
end

/-- The scope of the levels `0, …, n - 1`: the name `nm l` resolves to the index
    `n - 1 - l`. -/
def levelScope : (n : Nat) → Scope n
  | 0 => fun _ => none
  | n + 1 => fun s => if nm n = s then some ⟨0, by omega⟩ else (levelScope n s).map Fin.succ

theorem levelScope_nm (hnm : Function.Injective nm) :
    ∀ (n : Nat) (i : Fin n), levelScope nm n (nm (n - 1 - i)) = some i
  | 0, i => i.elim0
  | n + 1, i => by
    simp only [levelScope]
    by_cases hi : i.val = 0
    · rw [show i = ⟨0, by omega⟩ from Fin.ext hi]; simp
    · have hne : nm n ≠ nm (n + 1 - 1 - i) := fun h => by have := hnm h; omega
      rw [if_neg hne]
      have : n + 1 - 1 - i.val = n - 1 - (i.val - 1) := by omega
      rw [this, levelScope_nm hnm n ⟨i.val - 1, by omega⟩]
      simp only [Option.map_some, Option.some.injEq]
      ext; simp; omega

/-- Two scopes that agree up to the identification of their index types. -/
def Scope.Agree {m n : Nat} (Γ : Scope m) (Γ' : Scope n) : Prop :=
  ∀ s, (Γ s).map Fin.val = (Γ' s).map Fin.val

theorem Scope.extend_mkBinders_agree {m n : Nat} {Γ : Scope m} (hΓ : Scope.Agree Γ (levelScope nm n)) :
    ∀ sc : List Bool,
      Scope.Agree (Γ.extend (mkBinders nm n sc)) (levelScope nm (n + sc.length))
  | [] => hΓ
  | b :: sc => by
    intro s
    have ih := Scope.extend_mkBinders_agree hΓ sc s
    have hL : levelScope nm (n + (b :: sc).length) s =
        if nm (n + sc.length) = s then some ⟨0, by simp⟩
        else (levelScope nm (n + sc.length) s).map Fin.succ := rfl
    rw [hL]
    simp only [Scope.extend, mkBinders]
    by_cases h : nm (n + sc.length) = s
    · simp [h]
    · simp only [h, if_false]
      rcases hX : Scope.extend (mkBinders nm n sc) Γ s with _ | i <;>
        rcases hY : levelScope nm (n + sc.length) s with _ | j <;>
        simp_all

theorem Scope.Agree.eq_some {n : Nat} {Γ Γ' : Scope n} (h : Scope.Agree Γ Γ') {s : String}
    {i : Fin n} (hs : Γ' s = some i) : Γ s = some i := by
  have := h s
  rw [hs] at this
  obtain ⟨j, hj, hji⟩ := Option.map_eq_some_iff.mp this
  rw [hj]; congr; exact Fin.ext hji

mutual
theorem TVal.toVal_toTVal (hnm : Function.Injective nm) {n : Nat} {Γ : Scope n}
    (hΓ : Scope.Agree Γ (levelScope nm n)) :
    ∀ v : TVal n, (TVal.toVal nm v).toTVal Γ = some v
  | .bvar i => by
    simp [TVal.toVal, Val.toTVal, hΓ.eq_some (levelScope_nm nm hnm n i)]
  | .loc l => rfl
  | .fn f => rfl
  | .ctor c vs => by
    simp [TVal.toVal, Val.toTVal, TVal.toVals_toTVals hnm hΓ vs]
  | .lit k => rfl
theorem TVal.toVals_toTVals (hnm : Function.Injective nm) {n : Nat} {Γ : Scope n}
    (hΓ : Scope.Agree Γ (levelScope nm n)) :
    ∀ vs : List (TVal n), Val.toTVals Γ (TVal.toVals nm vs) = some vs
  | [] => rfl
  | v :: vs => by
    simp [TVal.toVals, Val.toTVals, TVal.toVal_toTVal hnm hΓ v, TVal.toVals_toTVals hnm hΓ vs]
end

end

theorem Option.exists_of_heq_some {α : Nat → Type} {a b : Nat} (hab : a = b) {x : Option (α a)}
    {y : α b} (h : HEq x (some y)) : ∃ y', x = some y' ∧ HEq y' y := by
  subst hab; cases h; exact ⟨y, rfl, .rfl⟩

theorem Term.letIn_congr {n : Nat} {sc sc' : List Bool} (h : sc = sc') (t1 : Term n)
    {t2 : Term (n + sc.length)} {t2' : Term (n + sc'.length)} (h2 : HEq t2 t2') :
    Term.letIn sc t1 t2 = Term.letIn sc' t1 t2' := by
  subst h; cases h2; rfl

theorem TBranches.cons_congr {n : Nat} (c : CName) {sc sc' : List Bool} (h : sc = sc')
    {t2 : Term (n + sc.length)} {t2' : Term (n + sc'.length)} (h2 : HEq t2 t2')
    (bs : TBranches n) : TBranches.cons c sc t2 bs = TBranches.cons c sc' t2' bs := by
  subst h; cases h2; rfl

section
variable (nm : Nat → String)

mutual
theorem Term.toExpr_toTerm' (hnm : Function.Injective nm) :
    ∀ {n : Nat} (t : Term n) {m : Nat} (Γ : Scope m), n = m → Scope.Agree Γ (levelScope nm n) →
      HEq ((Term.toExpr nm t).toTerm Γ) (some t)
  | _, .ret vs, _, Γ, hm, hΓ => by
    subst hm; simp [Term.toExpr, Expr.toTerm, TVal.toVals_toTVals nm hnm hΓ vs]
  | _, .app e1 e2, _, Γ, hm, hΓ => by
    subst hm
    obtain ⟨a, ha, h1⟩ := Option.exists_of_heq_some rfl (Term.toExpr_toTerm' hnm e1 Γ rfl hΓ)
    obtain ⟨b, hb, h2⟩ := Option.exists_of_heq_some rfl (Term.toExpr_toTerm' hnm e2 Γ rfl hΓ)
    cases h1; cases h2
    simp [Term.toExpr, Expr.toTerm, ha, hb]
  | _, .call f e1 e2, _, Γ, hm, hΓ => by
    subst hm
    obtain ⟨a, ha, h1⟩ := Option.exists_of_heq_some rfl (Term.toExpr_toTerm' hnm e1 Γ rfl hΓ)
    obtain ⟨b, hb, h2⟩ := Option.exists_of_heq_some rfl (Term.toExpr_toTerm' hnm e2 Γ rfl hΓ)
    cases h1; cases h2
    simp [Term.toExpr, Expr.toTerm, ha, hb]
  | n, .letIn sc e1 e2, _, Γ, hm, hΓ => by
    subst hm
    obtain ⟨a, ha, h1⟩ := Option.exists_of_heq_some rfl (Term.toExpr_toTerm' hnm e1 Γ rfl hΓ)
    cases h1
    have hl : n + (Binder.flags (mkBinders nm n sc)).length = n + sc.length := by
      rw [flags_mkBinders]
    obtain ⟨b, hb, h2⟩ := Option.exists_of_heq_some hl
      (Term.toExpr_toTerm' hnm e2 (Γ.extend (mkBinders nm n sc)) hl.symm
        (Scope.extend_mkBinders_agree nm hΓ sc))
    simp only [Term.toExpr, Expr.toTerm, ha, hb]
    exact heq_of_eq (congrArg some (Term.letIn_congr (flags_mkBinders nm n sc) e1 h2))
  | _, .bmatch e bs, _, Γ, hm, hΓ => by
    subst hm
    obtain ⟨a, ha, h1⟩ := Option.exists_of_heq_some rfl (Term.toExpr_toTerm' hnm e Γ rfl hΓ)
    cases h1
    simp [Term.toExpr, Expr.toTerm, ha, TBranches.toBranches_toBranches hnm bs Γ hΓ]
  | _, .dmatch e bs, _, Γ, hm, hΓ => by
    subst hm
    obtain ⟨a, ha, h1⟩ := Option.exists_of_heq_some rfl (Term.toExpr_toTerm' hnm e Γ rfl hΓ)
    cases h1
    simp [Term.toExpr, Expr.toTerm, ha, TBranches.toBranches_toBranches hnm bs Γ hΓ]
  | _, .drop x e, _, Γ, hm, hΓ => by
    subst hm
    obtain ⟨a, ha, h1⟩ := Option.exists_of_heq_some rfl (Term.toExpr_toTerm' hnm e Γ rfl hΓ)
    cases h1
    simp [Term.toExpr, Expr.toTerm, ha, TVal.toVal_toTVal nm hnm hΓ x]
  | _, .free k e, _, Γ, hm, hΓ => by
    subst hm
    obtain ⟨a, ha, h1⟩ := Option.exists_of_heq_some rfl (Term.toExpr_toTerm' hnm e Γ rfl hΓ)
    cases h1
    simp [Term.toExpr, Expr.toTerm, ha]
  | _, .prim op vs, _, Γ, hm, hΓ => by
    subst hm; simp [Term.toExpr, Expr.toTerm, TVal.toVals_toTVals nm hnm hΓ vs]
theorem TBranches.toBranches_toBranches (hnm : Function.Injective nm) :
    ∀ {n : Nat} (bs : TBranches n) (Γ : Scope n), Scope.Agree Γ (levelScope nm n) →
      Expr.toBranches Γ (TBranches.toBranches nm bs) = some bs
  | _, .nil, _, _ => rfl
  | n, .cons c sc e bs, Γ, hΓ => by
    have hl : n + (Binder.flags (mkBinders nm n sc)).length = n + sc.length := by
      rw [flags_mkBinders]
    obtain ⟨b, hb, h2⟩ := Option.exists_of_heq_some hl
      (Term.toExpr_toTerm' hnm e (Γ.extend (mkBinders nm n sc)) hl.symm
        (Scope.extend_mkBinders_agree nm hΓ sc))
    simp only [TBranches.toBranches, Expr.toBranches, hb,
      TBranches.toBranches_toBranches hnm bs Γ hΓ]
    exact congrArg some (TBranches.cons_congr c (flags_mkBinders nm n sc) h2 bs)
end

/-- **Printing and resolving are inverse**: resolving the names of a printed term (in the
    scope of its levels) gives back the term. -/
theorem Term.toExpr_toTerm (hnm : Function.Injective nm) {n : Nat} (t : Term n) :
    (Term.toExpr nm t).toTerm (levelScope nm n) = some t :=
  eq_of_heq (Term.toExpr_toTerm' nm hnm t (levelScope nm n) rfl fun _ => rfl)

/-- **Every closed term is the resolution of a closed named expression.** -/
theorem Term.toExpr_toClosed (hnm : Function.Injective nm) (t : Term 0) :
    (Term.toExpr nm t).toClosed = some t :=
  Term.toExpr_toTerm nm hnm t

end

/-- A concrete injective naming of levels: `x`, `x'`, `x''`, … -/
def primeName (l : Nat) : String := String.ofList ('x' :: List.replicate l '\'')

theorem primeName_injective : Function.Injective primeName := by
  intro a b h
  have := String.ofList_injective h
  simp only [List.cons.injEq, true_and] at this
  simpa using congrArg List.length this

end FIPNamed
