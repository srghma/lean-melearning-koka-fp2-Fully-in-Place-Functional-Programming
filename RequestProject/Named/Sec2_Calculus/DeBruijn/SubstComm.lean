module

public import RequestProject.Named.Sec2_Calculus.DeBruijn.ScopeLemmas

@[expose] public section

/-!
# Name resolution commutes with substitution

The key lemma relating the two representations: substituting **closed** values for names
in a named expression and then resolving its names gives the de Bruijn substitution of the
resolved term (`Expr.toTerm_subst`).  Closedness of the substituted values is what makes
the (capturing) named substitution `Expr.subst` agree with the capture-free de Bruijn one.
-/

namespace FIPNamed

mutual
/-- Resolution commutes with substitution, for values. -/
theorem Val.toTVal_subst {m n : Nat} {Γ : Scope m} {Δ : Scope n} {σ : Subst}
    {τ : Fin m → TVal n}
    (hτ : ∀ s i, Γ s = some i → ((Val.var (.name s)).subst σ).toTVal Δ = some (τ i)) :
    ∀ (v : Val) (t : TVal m), v.toTVal Γ = some t → (v.subst σ).toTVal Δ = some (t.subst τ)
  | .var (.name s), t, h => by
    simp only [Val.toTVal, Option.map_eq_some_iff] at h
    obtain ⟨i, hi, rfl⟩ := h
    exact hτ s i hi
  | .var (.loc l), t, h => by simp [Val.toTVal] at h; subst h; rfl
  | .fn f, t, h => by simp [Val.toTVal] at h; subst h; rfl
  | .ctor c vs, t, h => by
    simp only [Val.toTVal, Option.map_eq_some_iff] at h
    obtain ⟨ts, hts, rfl⟩ := h
    have := Val.toTVals_subst hτ vs ts hts
    simp only [Val.subst, Val.substList_eq_map, Val.toTVal, TVal.subst, TVal.substList_eq_map]
    simp [this]
  | .lit k, t, h => by simp [Val.toTVal] at h; subst h; rfl
/-- Resolution commutes with substitution, for lists of values. -/
theorem Val.toTVals_subst {m n : Nat} {Γ : Scope m} {Δ : Scope n} {σ : Subst}
    {τ : Fin m → TVal n}
    (hτ : ∀ s i, Γ s = some i → ((Val.var (.name s)).subst σ).toTVal Δ = some (τ i)) :
    ∀ (vs : List Val) (ts : List (TVal m)), Val.toTVals Γ vs = some ts →
      Val.toTVals Δ (vs.map (Val.subst σ)) = some (ts.map (TVal.subst τ))
  | [], ts, h => by simp [Val.toTVals] at h; subst h; rfl
  | v :: vs, ts, h => by
    simp only [Val.toTVals] at h
    cases hv : Val.toTVal Γ v <;> cases hvs : Val.toTVals Γ vs <;> simp_all
    subst h
    simp [Val.toTVals, Val.toTVal_subst hτ v _ hv, Val.toTVals_subst hτ vs _ hvs]
end

/-- The hypotheses of `Expr.toTerm_subst` are preserved under binders. -/
theorem subst_hyp_up {m n : Nat} {Γ : Scope m} {Δ : Scope n} {σ : Subst}
    {τ : Fin m → TVal n}
    (hσ : ∀ s v, σ.lookup s = some v → ∀ s', Var.name s' ∉ v.fv)
    (hτ : ∀ s i, Γ s = some i → ((Val.var (.name s)).subst σ).toTVal Δ = some (τ i))
    (xs : List Binder) :
    ∀ s i, Γ.extend xs s = some i →
      ((Val.var (.name s)).subst (σ.remove xs)).toTVal (Δ.extend xs) =
        some (Subst.up (Binder.flags xs).length τ i) := by
  intro s i h
  rcases Scope.extend_some Γ xs s i h with ⟨hi, hs, hΔ⟩ | ⟨hi, hs, hΓ⟩
  · simp only [Val.subst, Subst.remove_lookup, hs, if_true, Option.getD_none, Val.toTVal,
      hΔ Δ, Option.map_some, Subst.up, hi, dif_pos]
  · have hτ' := hτ s _ hΓ
    simp only [Val.subst, Subst.remove_lookup, hs, if_false] at hτ' ⊢
    simp only [Subst.up, Nat.not_lt.mpr hi, dif_neg, not_false_eq_true]
    rw [Val.toTVal_rename Δ (Δ.extend xs) (fun j => ⟨(Binder.flags xs).length + j, by omega⟩),
      hτ']
    · rfl
    · intro s' hs'
      cases hl : σ.lookup s with
      | some v => rw [hl] at hs'; exact absurd hs' (hσ s v hl s')
      | none =>
        rw [hl] at hs'
        simp only [Option.getD_none, Val.fv, List.mem_singleton, Var.name.injEq] at hs'
        subst hs'
        exact Scope.extend_not_mem Δ xs s' hs

theorem subst_hyp_remove {σ : Subst} (hσ : ∀ s v, σ.lookup s = some v → ∀ s', Var.name s' ∉ v.fv)
    (xs : List Binder) :
    ∀ s v, (σ.remove xs).lookup s = some v → ∀ s', Var.name s' ∉ v.fv := by
  intro s v h
  rw [Subst.remove_lookup] at h
  split at h
  · simp at h
  · exact hσ s v h

private theorem bind2_eq_some {α β γ : Type} {x : Option α} {y : Option β} {f : α → β → γ}
    {c : γ} (h : (do let a ← x; let b ← y; pure (f a b) : Option γ) = some c) :
    ∃ a b, x = some a ∧ y = some b ∧ c = f a b := by
  cases x <;> cases y <;> simp_all

mutual
/-- **Resolution commutes with substitution.**  If the substituted values are closed and
    every name `s` that `Γ` resolves to `i` becomes, after substitution, a value resolving
    in `Δ` to `τ i`, then resolving `e[σ]` in `Δ` gives `t[τ]`. -/
theorem Expr.toTerm_subst {m n : Nat} {Γ : Scope m} {Δ : Scope n} {σ : Subst}
    {τ : Fin m → TVal n}
    (hσ : ∀ s v, σ.lookup s = some v → ∀ s', Var.name s' ∉ v.fv)
    (hτ : ∀ s i, Γ s = some i → ((Val.var (.name s)).subst σ).toTVal Δ = some (τ i)) :
    ∀ (e : Expr) (t : Term m), e.toTerm Γ = some t → (e.subst σ).toTerm Δ = some (t.subst τ)
  | .ret vs, t, h => by
    simp only [Expr.toTerm, Option.map_eq_some_iff] at h
    obtain ⟨ts, hts, rfl⟩ := h
    simp [Expr.subst, Expr.toTerm, Term.subst, Val.toTVals_subst hτ vs ts hts]
  | .app e1 e2, t, h => by
    obtain ⟨t1, t2, h1, h2, rfl⟩ := bind2_eq_some h
    simp [Expr.subst, Expr.toTerm, Term.subst, Expr.toTerm_subst hσ hτ e1 t1 h1,
      Expr.toTerm_subst hσ hτ e2 t2 h2]
  | .call f e1 e2, t, h => by
    obtain ⟨t1, t2, h1, h2, rfl⟩ := bind2_eq_some h
    simp [Expr.subst, Expr.toTerm, Term.subst, Expr.toTerm_subst hσ hτ e1 t1 h1,
      Expr.toTerm_subst hσ hτ e2 t2 h2]
  | .letIn xs e1 e2, t, h => by
    obtain ⟨t1, t2, h1, h2, rfl⟩ := bind2_eq_some h
    simp [Expr.subst, Expr.toTerm, Term.subst, Expr.toTerm_subst hσ hτ e1 t1 h1,
      Expr.toTerm_subst (subst_hyp_remove hσ xs) (subst_hyp_up hσ hτ xs) e2 t2 h2]
  | .bmatch e bs, t, h => by
    obtain ⟨t1, t2, h1, h2, rfl⟩ := bind2_eq_some h
    simp [Expr.subst, Expr.toTerm, Term.subst, Expr.toTerm_subst hσ hτ e t1 h1,
      Expr.toBranches_subst hσ hτ bs t2 h2]
  | .dmatch e bs, t, h => by
    obtain ⟨t1, t2, h1, h2, rfl⟩ := bind2_eq_some h
    simp [Expr.subst, Expr.toTerm, Term.subst, Expr.toTerm_subst hσ hτ e t1 h1,
      Expr.toBranches_subst hσ hτ bs t2 h2]
  | .drop x e, t, h => by
    obtain ⟨t1, t2, h1, h2, rfl⟩ := bind2_eq_some h
    simp [Expr.subst, Expr.toTerm, Term.subst, Val.toTVal_subst hτ x t1 h1,
      Expr.toTerm_subst hσ hτ e t2 h2]
  | .free k e, t, h => by
    simp only [Expr.toTerm, Option.map_eq_some_iff] at h
    obtain ⟨t', ht, rfl⟩ := h
    simp [Expr.subst, Expr.toTerm, Term.subst, Expr.toTerm_subst hσ hτ e t' ht]
  | .prim op vs, t, h => by
    simp only [Expr.toTerm, Option.map_eq_some_iff] at h
    obtain ⟨ts, hts, rfl⟩ := h
    simp [Expr.subst, Expr.toTerm, Term.subst, Val.toTVals_subst hτ vs ts hts]
/-- `Expr.toTerm_subst` for the branches of a match. -/
theorem Expr.toBranches_subst {m n : Nat} {Γ : Scope m} {Δ : Scope n} {σ : Subst}
    {τ : Fin m → TVal n}
    (hσ : ∀ s v, σ.lookup s = some v → ∀ s', Var.name s' ∉ v.fv)
    (hτ : ∀ s i, Γ s = some i → ((Val.var (.name s)).subst σ).toTVal Δ = some (τ i)) :
    ∀ (bs : List Branch) (t : TBranches m), Expr.toBranches Γ bs = some t →
      Expr.toBranches Δ (Expr.substBranches σ bs) = some (t.subst τ)
  | [], t, h => by simp [Expr.toBranches] at h; subst h; rfl
  | .mk c xs e :: bs, t, h => by
    obtain ⟨t1, t2, h1, h2, rfl⟩ := bind2_eq_some h
    simp [Expr.substBranches, Expr.toBranches, TBranches.subst,
      Expr.toTerm_subst (subst_hyp_remove hσ xs) (subst_hyp_up hσ hτ xs) e t1 h1,
      Expr.toBranches_subst hσ hτ bs t2 h2]
end

end FIPNamed
