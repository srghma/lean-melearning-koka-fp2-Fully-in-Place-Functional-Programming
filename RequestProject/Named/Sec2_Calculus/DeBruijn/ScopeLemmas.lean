module

public import RequestProject.Named.Sec2_Calculus.DeBruijn.Closed

@[expose] public section

/-!
# Facts about scopes, name resolution and named substitutions

Technical lemmas used by `RequestProject/Sec2_Calculus/DeBruijn/SubstComm.lean`: how
`Scope.extend` resolves a name, how `zipSubst` and `Subst.remove` look a name up, and how
resolving the names of a value depends on the scope.
-/

namespace FIPNamed

/-- A name that is not among the binders resolves in the outer scope, shifted past them. -/
theorem Scope.extend_not_mem {n : Nat} (Γ : Scope n) :
    ∀ (xs : List Binder) (s : String), s ∉ xs.map (·.name) →
      Γ.extend xs s = (Γ s).map (fun i => ⟨(Binder.flags xs).length + i, by omega⟩)
  | [], s, _ => by
    rcases h : Γ s with _ | i <;> simp [Scope.extend, h]
  | x :: xs, s, h => by
    simp only [List.map_cons, List.mem_cons, not_or] at h
    have hx : ¬ x.name = s := fun e => h.1 e.symm
    simp only [Scope.extend, hx, if_false]
    rw [Scope.extend_not_mem Γ xs s h.2]
    cases Γ s with
    | none => rfl
    | some i => simp only [Option.map_some, Option.some.injEq]; ext; simp; omega

/-- A name among the binders resolves to the same index, whatever the outer scope. -/
theorem Scope.extend_mem :
    ∀ (xs : List Binder) (s : String), s ∈ xs.map (·.name) →
      ∃ j, ∃ hj : j < (Binder.flags xs).length, ∀ {n : Nat} (Δ : Scope n),
        Δ.extend xs s = some ⟨j, by omega⟩
  | [], s, h => by simp at h
  | x :: xs, s, h => by
    by_cases hx : x.name = s
    · exact ⟨0, by simp, fun Δ => by simp [Scope.extend, hx]⟩
    · have h' : s ∈ xs.map (·.name) := by
        simp only [List.map_cons, List.mem_cons] at h
        rcases h with h | h
        · exact absurd h.symm hx
        · exact h
      obtain ⟨j, hj, hΔ⟩ := Scope.extend_mem xs s h'
      refine ⟨j + 1, by simpa using hj, fun Δ => ?_⟩
      simp only [Scope.extend, hx, if_false, hΔ, Option.map_some]
      rfl

/-- How a name resolved in an extended scope was resolved. -/
theorem Scope.extend_some {n : Nat} (Γ : Scope n) (xs : List Binder) (s : String)
    (i : Fin (n + (Binder.flags xs).length)) (h : Γ.extend xs s = some i) :
    (∃ hi : i.val < (Binder.flags xs).length, s ∈ xs.map (·.name) ∧
        ∀ {n' : Nat} (Δ : Scope n'), Δ.extend xs s = some ⟨i.val, by omega⟩) ∨
      (∃ hi : (Binder.flags xs).length ≤ i.val, s ∉ xs.map (·.name) ∧
        Γ s = some ⟨i.val - (Binder.flags xs).length, by omega⟩) := by
  by_cases hs : s ∈ xs.map (·.name)
  · obtain ⟨j, hj, hΔ⟩ := Scope.extend_mem xs s hs
    have : i.val = j := by rw [hΔ Γ] at h; cases h; rfl
    subst this
    exact .inl ⟨hj, hs, hΔ⟩
  · rw [Scope.extend_not_mem Γ xs s hs] at h
    obtain ⟨i', hi', rfl⟩ := Option.map_eq_some_iff.mp h
    refine .inr ⟨by simp, hs, ?_⟩
    rw [hi']; congr; ext; simp

/-- Looking up a binder in `[x̄ := v̄]`: the value at the index the binder resolves to. -/
theorem zipSubst_lookup_of_extend :
    ∀ (xs : List Binder) (vs : List Val) (s : String) {n : Nat} (Γ : Scope n)
      (i : Fin (n + (Binder.flags xs).length)),
      Γ.extend xs s = some i → i.val < (Binder.flags xs).length →
      (zipSubst xs vs).lookup s = vs[i.val]?
  | [], _, _, _, _, i, _, hi => by simp at hi
  | x :: xs, [], s, _, Γ, i, _, _ => by simp [zipSubst]
  | x :: xs, v :: vs, s, _, Γ, i, h, hi => by
    by_cases hx : x.name = s
    · simp only [Scope.extend, hx, if_true, Option.some.injEq] at h
      subst h
      simp [zipSubst, hx]
    · simp only [Scope.extend, hx, if_false] at h
      obtain ⟨i', hi', rfl⟩ := Option.map_eq_some_iff.mp h
      have hne : (s == x.name) = false := by simpa using fun e => hx e.symm
      have := zipSubst_lookup_of_extend xs vs s Γ i' hi' (by simp at hi ⊢; omega)
      simp only [zipSubst, List.map_cons, List.zip_cons_cons, List.lookup, hne] at this ⊢
      simpa using this

/-- A name that is not a binder is not substituted by `[x̄ := v̄]`. -/
theorem zipSubst_lookup_not_mem :
    ∀ (xs : List Binder) (vs : List Val) (s : String), s ∉ xs.map (·.name) →
      (zipSubst xs vs).lookup s = none
  | [], _, _, _ => by simp [zipSubst]
  | x :: xs, [], s, _ => by simp [zipSubst]
  | x :: xs, v :: vs, s, h => by
    simp only [List.map_cons, List.mem_cons, not_or] at h
    have hne : (s == x.name) = false := by simpa using h.1
    have := zipSubst_lookup_not_mem xs vs s h.2
    simp only [zipSubst, List.map_cons, List.zip_cons_cons, List.lookup, hne] at this ⊢
    exact this

/-- The values of `[x̄ := v̄]` are among `v̄`. -/
theorem zipSubst_lookup_mem :
    ∀ (xs : List Binder) (vs : List Val) (s : String) (v : Val),
      (zipSubst xs vs).lookup s = some v → v ∈ vs
  | [], _, _, _, h => by simp [zipSubst] at h
  | x :: xs, [], s, _, h => by simp [zipSubst] at h
  | x :: xs, w :: vs, s, v, h => by
    simp only [zipSubst, List.map_cons, List.zip_cons_cons, List.lookup] at h
    split at h
    · cases h; simp
    · exact List.mem_cons_of_mem _ (zipSubst_lookup_mem xs vs s v h)

/-- Removing the binders `x̄` from a substitution. -/
theorem Subst.remove_lookup (xs : List Binder) (s : String) :
    ∀ σ : Subst, (σ.remove xs).lookup s = if s ∈ xs.map (·.name) then none else σ.lookup s
  | [] => by simp [Subst.remove]
  | (a, v) :: σ => by
    have ih := Subst.remove_lookup xs s σ
    simp only [Subst.remove] at ih ⊢
    by_cases ha : a ∈ xs.map (·.name)
    · rw [List.filter_cons_of_neg (by simpa using ha), ih]
      by_cases hs : s ∈ xs.map (·.name)
      · simp [hs]
      · have : (s == a) = false := by
          simp only [beq_eq_false_iff_ne]; rintro rfl; exact hs ha
        simp [hs, List.lookup, this]
    · rw [List.filter_cons_of_pos (by simpa using ha)]
      by_cases hsa : s = a
      · subst hsa; simp [List.lookup, ha]
      · have : (s == a) = false := by simpa using hsa
        simp only [List.lookup, this]
        exact ih

mutual
/-- Resolving the names of a value in two scopes that agree up to a renaming `ρ` on the
    free names of the value. -/
theorem Val.toTVal_rename {m n : Nat} (Γ : Scope m) (Δ : Scope n) (ρ : Fin m → Fin n) :
    ∀ v : Val, (∀ s, Var.name s ∈ v.fv → Δ s = (Γ s).map ρ) →
      v.toTVal Δ = (v.toTVal Γ).map (TVal.subst (TVal.bvar ∘ ρ))
  | .var (.name s), h => by
    have := h s (by simp [Val.fv])
    simp only [Val.toTVal, this]
    cases Γ s <;> rfl
  | .var (.loc l), _ => rfl
  | .fn f, _ => rfl
  | .ctor c vs, h => by
    have ih := Val.toTVals_rename Γ Δ ρ vs (fun s hs => h s (by simpa [Val.fv] using hs))
    simp only [Val.toTVal, ih]
    cases Val.toTVals Γ vs <;> simp [TVal.subst]
  | .lit k, _ => rfl
/-- `Val.toTVal_rename` for a list of values. -/
theorem Val.toTVals_rename {m n : Nat} (Γ : Scope m) (Δ : Scope n) (ρ : Fin m → Fin n) :
    ∀ vs : List Val, (∀ s, Var.name s ∈ Val.fvList vs → Δ s = (Γ s).map ρ) →
      Val.toTVals Δ vs = (Val.toTVals Γ vs).map (List.map (TVal.subst (TVal.bvar ∘ ρ)))
  | [], _ => rfl
  | v :: vs, h => by
    have h1 := Val.toTVal_rename Γ Δ ρ v (fun s hs => h s (by simp [Val.fvList, hs]))
    have h2 := Val.toTVals_rename Γ Δ ρ vs (fun s hs => h s (by simp [Val.fvList, hs]))
    simp only [Val.toTVals, h1, h2]
    cases Val.toTVal Γ v <;> cases Val.toTVals Γ vs <;> simp
end

/-- A value resolved in some scope has, in that scope, no name outside it; in particular
    a value resolved in the empty scope has no free name. -/
theorem Val.closed_of_toTVal_empty {v : Val} {t : TVal 0} (h : v.toTVal Scope.empty = some t) :
    ∀ s, Var.name s ∉ v.fv := by
  have := (Val.toTVal_isSome_iff Scope.empty v).mp (by simp [h])
  intro s hs
  simpa [Scope.empty_isSome] using this s hs

theorem Val.toTVals_length {n : Nat} (Γ : Scope n) :
    ∀ (vs : List Val) (ts : List (TVal n)), Val.toTVals Γ vs = some ts → ts.length = vs.length
  | [], ts, h => by simp [Val.toTVals] at h; simp [← h]
  | v :: vs, ts, h => by
    simp only [Val.toTVals] at h
    cases hv : Val.toTVal Γ v <;> cases hvs : Val.toTVals Γ vs <;> simp_all
    rw [← h]; simp [Val.toTVals_length Γ vs _ hvs]

theorem Val.toTVals_getElem {n : Nat} (Γ : Scope n) :
    ∀ (vs : List Val) (ts : List (TVal n)), Val.toTVals Γ vs = some ts →
      ∀ (i : Nat) (h1 : i < vs.length) (h2 : i < ts.length), Val.toTVal Γ vs[i] = some ts[i]
  | [], ts, _, i, h1, _ => by simp at h1
  | v :: vs, ts, h, i, h1, h2 => by
    simp only [Val.toTVals] at h
    cases hv : Val.toTVal Γ v <;> cases hvs : Val.toTVals Γ vs <;> simp_all
    subst h
    cases i with
    | zero => simpa using hv
    | succ i => simpa using Val.toTVals_getElem Γ vs _ hvs i (by simpa using h1) (by simpa using h2)

end FIPNamed
