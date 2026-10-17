module

public import RequestProject.Named.AppE_HeapSoundness.LamDeBruijnWf
public import RequestProject.Named.Sec2_Calculus.DeBruijn.ScopeLemmas

@[expose] public section

/-!
# Name resolution commutes with substitution, for `λfip`

The key lemma relating the named and the de Bruijn presentations of `λfip`:
substituting **closed** values for names in a named expression and then resolving its
names gives the closure-instantiating de Bruijn substitution `LTerm.isubst` of the
resolved term (`LExpr.toLTerm_subst`).

The named substitution enters the body of a lambda `λ^z̄ x̄. e` and replaces there the
recorded variables `zᵢ` that it substitutes; `LTerm.isubst` does the same through the
captured values (`LSubst'.cap`).  With the plain substitution `LTerm.subst`, which never
enters a lambda body, the lemma is false: after `z := v`, the named closure mentions `v` in
its body, while the plain de Bruijn closure still refers to its captured value.
-/

namespace FIPNamed.Lam

/-! ## Closed values -/

mutual
theorem LTVal.lower_zero : ∀ (v : LTVal 0), v.lower = some v
  | .bvar i => i.elim0
  | .loc l => rfl
  | .fn f => rfl
  | .ctor c vs => by simp [LTVal.lower, LTVals.lower_zero vs]
  | .lam zs sc body => by simp [LTVal.lower, LTVals.lower_zero zs]
theorem LTVals.lower_zero : ∀ {k : Nat} (vs : LTVals 0 k), vs.lower = some vs
  | _, .nil => rfl
  | _, .cons v vs => by simp [LTVals.lower, LTVal.lower_zero v, LTVals.lower_zero vs]
end

mutual
theorem LTVal.lower_subst {n m : Nat} (σ : Fin n → LTVal m) :
    ∀ (v : LTVal n) {c : LTVal 0}, v.lower = some c → (v.subst σ).lower = some c
  | .bvar i, _, h => by simp [LTVal.lower] at h
  | .loc l, _, h => h
  | .fn f, _, h => h
  | .ctor c vs, _, h => by
    simp only [LTVal.lower, Option.map_eq_some_iff] at h
    obtain ⟨ws, hws, rfl⟩ := h
    simp [LTVal.subst, LTVal.lower, LTVals.lower_subst σ vs hws]
  | .lam zs sc body, _, h => by
    simp only [LTVal.lower, Option.map_eq_some_iff] at h
    obtain ⟨ws, hws, rfl⟩ := h
    simp [LTVal.subst, LTVal.lower, LTVals.lower_subst σ zs hws]
theorem LTVals.lower_subst {n m : Nat} (σ : Fin n → LTVal m) :
    ∀ {k : Nat} (vs : LTVals n k) {c : LTVals 0 k}, vs.lower = some c →
      (LTVals.subst σ vs).lower = some c
  | _, .nil, _, h => h
  | _, .cons v vs, _, h => by
    simp only [LTVals.lower] at h
    cases hv : LTVal.lower v <;> cases hvs : LTVals.lower vs <;> simp_all
    subst h
    simp [LTVals.subst, LTVals.lower, LTVal.lower_subst σ v hv, LTVals.lower_subst σ vs hvs]
end

@[simp] theorem LTVal.lower_weaken {m : Nat} (c : LTVal 0) : (c.weaken : LTVal m).lower = some c :=
  LTVal.lower_subst _ c (LTVal.lower_zero c)

@[simp] theorem LTVal.capOf_bvar {n m : Nat} (σ : Fin n → LTVal m) (j : Fin n) :
    (LTVal.bvar j).capOf σ = (σ j).lower := rfl

/-! ## Name resolution in different scopes -/

mutual
/-- Resolving the names of a value in two scopes that agree up to a renaming `ρ` on the
    free names of the value (the body of a lambda is resolved in its own scope). -/
theorem LVal.toLTVal_rename {m n : Nat} (Γ : Scope m) (Δ : Scope n) (ρ : Fin m → Fin n) :
    ∀ v : LVal, (∀ s, Var.name s ∈ v.fv → Δ s = (Γ s).map ρ) →
      v.toLTVal Δ = (v.toLTVal Γ).map (LTVal.subst (LTVal.bvar ∘ ρ))
  | .var (.name s), h => by
    have hs := h s (by simp [LVal.fv])
    simp only [LVal.toLTVal, hs]
    cases Γ s <;> simp [LTVal.subst]
  | .var (.loc l), _ => by simp [LVal.toLTVal, LTVal.subst]
  | .fn f, _ => by simp [LVal.toLTVal, LTVal.subst]
  | .ctor c vs, h => by
    have := LVal.toLTVals_rename Γ Δ ρ vs (fun s hs => h s (by simpa [LVal.fv] using hs))
    simp only [LVal.toLTVal, this]
    cases LVal.toLTVals Γ vs <;> simp [LTVal.subst]
  | .lam zs xs e, h => by
    have := LVal.toLTVals_rename Γ Δ ρ zs (fun s hs => h s (by simpa [LVal.fv] using hs))
    simp only [LVal.toLTVal, this]
    cases LVal.toLTVals Γ zs <;> cases LExpr.toLTerm ((Scope.ofCaptured zs).extend xs) e <;>
      simp [LTVal.subst]
/-- `LVal.toLTVal_rename` for lists of values. -/
theorem LVal.toLTVals_rename {m n : Nat} (Γ : Scope m) (Δ : Scope n) (ρ : Fin m → Fin n) :
    ∀ vs : List LVal, (∀ s, Var.name s ∈ LVal.fvList vs → Δ s = (Γ s).map ρ) →
      LVal.toLTVals Δ vs = (LVal.toLTVals Γ vs).map (LTVals.subst (LTVal.bvar ∘ ρ))
  | [], _ => by simp [LVal.toLTVals, LTVals.subst]
  | v :: vs, h => by
    have h1 := LVal.toLTVal_rename Γ Δ ρ v (fun s hs => h s (by simp [LVal.fvList, hs]))
    have h2 := LVal.toLTVals_rename Γ Δ ρ vs (fun s hs => h s (by simp [LVal.fvList, hs]))
    simp only [LVal.toLTVals, h1, h2]
    cases LVal.toLTVal Γ v <;> cases LVal.toLTVals Γ vs <;> simp [LTVals.subst]
end

/-- A closed value has no free name. -/
theorem LVal.no_name_of_closed {v : LVal} {c : LTVal 0} (h : v.toLTVal Scope.empty = some c) :
    ∀ s, Var.name s ∉ v.fv := by
  have hs : (v.toLTVal Scope.empty).isSome := by simp [h]
  rw [LVal.toLTVal_isSome_iff] at hs
  intro s hmem
  have := LVal.Scoped.fv hs s hmem
  simp [Scope.empty] at this

/-- A closed value resolves to the same closed value in every scope. -/
theorem LVal.toLTVal_closed {v : LVal} {c : LTVal 0} (h : v.toLTVal Scope.empty = some c)
    {n : Nat} (Δ : Scope n) : v.toLTVal Δ = some c.weaken := by
  rw [LVal.toLTVal_rename Scope.empty Δ Fin.elim0 v
    (fun s hs => absurd hs (LVal.no_name_of_closed h s)), h]
  simp only [Option.map_some, LTVal.weaken]
  congr 2
  funext i; exact i.elim0

/-- A closed value is not a name. -/
theorem LVal.ne_name_of_closed {v : LVal} {c : LTVal 0} (h : v.toLTVal Scope.empty = some c)
    (s : String) : v ≠ .var (.name s) := by
  rintro rfl; simp [LVal.toLTVal, Scope.empty] at h

/-! ## Lists of values and recorded variables -/

/-- The `i`-th resolved value is the resolution of the `i`-th value. -/
theorem LVal.toLTVals_get {n : Nat} (Γ : Scope n) :
    ∀ (vs : List LVal) (ts : LTVals n vs.length), LVal.toLTVals Γ vs = some ts →
      ∀ i : Fin vs.length, LVal.toLTVal Γ vs[i] = some (ts.get i)
  | [], _, _, i => i.elim0
  | v :: vs, ts, h, i => by
    simp only [LVal.toLTVals] at h
    cases hv : LVal.toLTVal Γ v <;> cases hvs : LVal.toLTVals Γ vs <;> simp_all
    subst h
    rcases i with ⟨_ | i, hi⟩
    · simpa [LTVals.get] using hv
    · simpa [LTVals.get] using LVal.toLTVals_get Γ vs _ hvs ⟨i, by simpa using hi⟩

/-- A recorded variable resolves to the position of a recorded name. -/
theorem Scope.ofCaptured_get :
    ∀ (zs : List LVal) (s : String) (i : Fin zs.length), Scope.ofCaptured zs s = some i →
      zs[i] = .var (.name s)
  | [], _, i, _ => i.elim0
  | z :: zs, s, i, h => by
    have step : ∀ (j : Fin zs.length), Fin.succ j = i → zs[j] = LVal.var (.name s) →
        (z :: zs)[i] = LVal.var (.name s) := by
      rintro j rfl hj; simpa using hj
    cases z with
    | var x =>
      cases x with
      | name s' =>
        simp only [Scope.ofCaptured] at h
        split at h
        · cases h; simp_all
        · obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.mp h
          exact step j rfl (Scope.ofCaptured_get zs s j hj)
      | loc l =>
        obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.mp h
        exact step j rfl (Scope.ofCaptured_get zs s j hj)
    | _ =>
      obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.mp h
      exact step j rfl (Scope.ofCaptured_get zs s j hj)

open Classical in
private theorem ofCaptured_cons_val (z : LVal) (zs : List LVal) (s : String) :
    (Scope.ofCaptured (z :: zs) s).map Fin.val =
      if z = .var (.name s) then some 0 else ((Scope.ofCaptured zs s).map Fin.val).map (· + 1) := by
  cases z with
  | var x =>
    cases x with
    | name s' =>
      by_cases h : s' = s
      · subst h; simp [Scope.ofCaptured]
      · simp [Scope.ofCaptured, h, Option.map_map, Function.comp_def]
    | loc l => simp [Scope.ofCaptured, Option.map_map, Function.comp_def]
  | _ => simp [Scope.ofCaptured, Option.map_map, Function.comp_def]

open Classical in
/-- Substituting closed values for other names does not move a recorded name that is not
    substituted. -/
theorem Scope.ofCaptured_substList {σ : LSubst} {s : String} (hs : σ (.name s) = none)
    (hσ : ∀ x v, σ x = some v → v ≠ .var (.name s)) :
    ∀ zs : List LVal, (Scope.ofCaptured (LVal.substList σ zs) s).map Fin.val =
      (Scope.ofCaptured zs s).map Fin.val
  | [] => rfl
  | z :: zs => by
    simp only [LVal.substList]
    rw [ofCaptured_cons_val, ofCaptured_cons_val, Scope.ofCaptured_substList hs hσ zs]
    have : (LVal.subst σ z = .var (.name s)) ↔ (z = .var (.name s)) := by
      constructor
      · intro h
        cases z with
        | var x =>
          simp only [LVal.subst] at h
          cases hx : σ x with
          | none => simpa [hx] using h
          | some v => rw [hx] at h; exact absurd h (hσ x v hx)
        | fn f => simp [LVal.subst] at h
        | ctor c vs => simp [LVal.subst] at h
        | lam zs xs e => simp [LVal.subst] at h
      · rintro rfl; simp [LVal.subst, hs]
    by_cases h : z = .var (.name s)
    · rw [if_pos h, if_pos (this.mpr h)]
    · rw [if_neg h, if_neg (mt this.mp h)]

/-! ## Transport along equal scope sizes -/

/-- The same family member, seen at two propositionally equal indices. -/
theorem sigma_app {F : Nat → Type} {X : Type} (g : (k : Nat) → F k → X) {k k' : Nat}
    {a : F k} {a' : F k'} (h : (⟨k, a⟩ : Σ k, F k) = ⟨k', a'⟩) : g k a = g k' a' := by
  cases h; rfl

theorem sigma_cons {n : Nat} (v : LTVal n) {k k' : Nat} {a : LTVals n k} {a' : LTVals n k'}
    (h : (⟨k, a⟩ : Σ k, LTVals n k) = ⟨k', a'⟩) :
    (⟨k + 1, .cons v a⟩ : Σ k, LTVals n k) = ⟨k' + 1, .cons v a'⟩ := by
  cases h; rfl

theorem sigma_lam {n : Nat} (sc : List Bool) {k k' : Nat} {a : LTVals n k} {a' : LTVals n k'}
    {b : LTerm (k + sc.length)} {b' : LTerm (k' + sc.length)}
    (h1 : (⟨k, a⟩ : Σ k, LTVals n k) = ⟨k', a'⟩)
    (h2 : (⟨k, b⟩ : Σ k, LTerm (k + sc.length)) = ⟨k', b'⟩) :
    LTVal.lam a sc b = LTVal.lam a' sc b' := by
  cases h1; cases h2; rfl

/-- A scope of size `k' + p` seen as a scope of size `k + p`, for `k' = k`. -/
def Scope.castLen {k k' p : Nat} (h : k' = k) (Δ : Scope (k' + p)) : Scope (k + p) :=
  fun s => (Δ s).map (Fin.cast (by omega))

theorem LExpr.toLTerm_castLen {k k' p : Nat} (h : k' = k) (Δ : Scope (k' + p)) (e : LExpr)
    {y : LTerm (k + p)} (hy : e.toLTerm (Scope.castLen h Δ) = some y) :
    ∃ b, e.toLTerm Δ = some b ∧ (⟨k', b⟩ : Σ k, LTerm (k + p)) = ⟨k, y⟩ := by
  subst h
  have : Scope.castLen rfl Δ = Δ := by
    funext s; simp only [Scope.castLen]; cases Δ s <;> rfl
  rw [this] at hy
  exact ⟨y, hy, rfl⟩

theorem LVal.substList_length (σ : LSubst) :
    ∀ vs : List LVal, (LVal.substList σ vs).length = vs.length
  | [] => rfl
  | _ :: vs => by simp [LVal.substList, LVal.substList_length σ vs]

/-! ## Named substitutions -/

theorem LSubst.remove_name (σ : LSubst) (xs : List Binder) (s : String) :
    σ.remove xs (.name s) = if s ∈ xs.map (·.name) then none else σ (.name s) := by
  unfold LSubst.remove
  by_cases h : s ∈ xs.map (·.name)
  · have : Var.name s ∈ Binder.vars xs := by
      simp only [Binder.vars, List.mem_map] at h ⊢
      obtain ⟨b, hb, rfl⟩ := h; exact ⟨b, hb, rfl⟩
    simp [this, h]
  · have : Var.name s ∉ Binder.vars xs := by
      simp only [Binder.vars, List.mem_map, Var.name.injEq] at h ⊢
      exact h
    simp [this, h]

theorem LSubst.remove_loc' (σ : LSubst) (xs : List Binder) (l : Nat) :
    σ.remove xs (.loc l) = σ (.loc l) := by
  unfold LSubst.remove
  have : Var.loc l ∉ Binder.vars xs := by simp [Binder.vars]
  simp [this]

theorem LSubst.remove_closed {σ : LSubst}
    (hσ : ∀ x v, σ x = some v → ∃ c, v.toLTVal Scope.empty = some c) (xs : List Binder) :
    ∀ x v, σ.remove xs x = some v → ∃ c, v.toLTVal Scope.empty = some c := by
  intro x v h
  unfold LSubst.remove at h
  split at h
  · simp at h
  · exact hσ x v h

/-- The hypothesis of `LExpr.toLTerm_subst`, pushed under binders. -/
theorem lsubst_hyp_up {m n : Nat} {Γ : Scope m} {Δ : Scope n} {σ : LSubst}
    {τ : Fin m → LTVal n}
    (hσ : ∀ x v, σ x = some v → ∃ c, v.toLTVal Scope.empty = some c)
    (hτ : ∀ s i, Γ s = some i → ((LVal.var (.name s)).subst σ).toLTVal Δ = some (τ i))
    (xs : List Binder) :
    ∀ s i, Γ.extend xs s = some i →
      ((LVal.var (.name s)).subst (σ.remove xs)).toLTVal (Δ.extend xs) =
        some (LSubst'.up (Binder.flags xs).length τ i) := by
  intro s i h
  rcases Scope.extend_some Γ xs s i h with ⟨hi, hs, hΔ⟩ | ⟨hi, hs, hΓ⟩
  · simp only [LVal.subst, LSubst.remove_name, hs, if_true, Option.getD_none, LVal.toLTVal,
      hΔ Δ, Option.map_some, LSubst'.up, hi, dif_pos]
  · have hτ' := hτ s _ hΓ
    simp only [LVal.subst, LSubst.remove_name, hs, if_false] at hτ' ⊢
    simp only [LSubst'.up, Nat.not_lt.mpr hi, dif_neg, not_false_eq_true]
    rw [LVal.toLTVal_rename Δ (Δ.extend xs) (fun j => ⟨(Binder.flags xs).length + j, by omega⟩),
      hτ']
    · rfl
    · intro s' hs'
      cases hl : σ (.name s) with
      | some v =>
        rw [hl] at hs'
        obtain ⟨c, hc⟩ := hσ _ v hl
        exact absurd hs' (LVal.no_name_of_closed hc s')
      | none =>
        rw [hl] at hs'
        simp only [Option.getD_none, LVal.fv, List.mem_singleton, Var.name.injEq] at hs'
        subst hs'
        exact Scope.extend_not_mem Δ xs s' hs

/-- The hypothesis of `LExpr.toLTerm_subst`, for the body of a lambda. -/
theorem lsubst_hyp_cap {m n : Nat} {Γ : Scope m} {Δ : Scope n} {σ : LSubst}
    {τ : Fin m → LTVal n}
    (hσ : ∀ x v, σ x = some v → ∃ c, v.toLTVal Scope.empty = some c)
    (hτ : ∀ s i, Γ s = some i → ((LVal.var (.name s)).subst σ).toLTVal Δ = some (τ i))
    (zs : List LVal) (ts : LTVals m zs.length) (hts : LVal.toLTVals Γ zs = some ts)
    (xs : List Binder) (hlen : (LVal.substList σ zs).length = zs.length) :
    ∀ s i, (Scope.ofCaptured zs).extend xs s = some i →
      ((LVal.var (.name s)).subst (σ.remove xs)).toLTVal
          (Scope.castLen hlen ((Scope.ofCaptured (LVal.substList σ zs)).extend xs)) =
        some (LSubst'.cap τ ts (Binder.flags xs).length i) := by
  intro s i h
  rcases Scope.extend_some _ xs s i h with ⟨hi, hs, hΔ⟩ | ⟨hi, hs, hΓ⟩
  · simp only [LVal.subst, LSubst.remove_name, hs, if_true, Option.getD_none, LVal.toLTVal,
      Scope.castLen, hΔ, Option.map_some, LSubst'.cap, hi, dif_pos]
    rfl
  · -- `s` is a recorded variable, at position `i - |x̄|`
    have hi' : i.val - (Binder.flags xs).length < zs.length := by have := i.isLt; omega
    have hget := Scope.ofCaptured_get zs s ⟨i.val - (Binder.flags xs).length, hi'⟩ hΓ
    have htg := LVal.toLTVals_get Γ zs ts hts ⟨i.val - (Binder.flags xs).length, hi'⟩
    simp only [Fin.getElem_fin] at hget htg
    rw [hget] at htg
    simp only [LVal.toLTVal, Option.map_eq_some_iff] at htg
    obtain ⟨j, hj, htj⟩ := htg
    have hτj := hτ s j hj
    have hcap : LSubst'.cap τ ts (Binder.flags xs).length i =
        match (τ j).lower with
        | some c => c.weaken
        | none => .bvar i := by
      unfold LSubst'.cap
      rw [dif_neg (Nat.not_lt.mpr hi)]
      have : ts.get ⟨i.val - (Binder.flags xs).length, hi'⟩ = .bvar j := htj.symm
      rw [this]; rfl
    rw [hcap]
    simp only [LVal.subst, LSubst.remove_name, hs, if_false] at hτj ⊢
    cases hl : σ (.name s) with
    | some v =>
      rw [hl] at hτj
      obtain ⟨c, hc⟩ := hσ _ v hl
      simp only [Option.getD_some] at hτj
      rw [LVal.toLTVal_closed hc] at hτj
      have hτc : τ j = c.weaken := (Option.some.inj hτj).symm
      rw [hτc, LTVal.lower_weaken]
      exact LVal.toLTVal_closed hc _
    | none =>
      rw [hl] at hτj
      simp only [Option.getD_none, LVal.toLTVal, Option.map_eq_some_iff] at hτj
      obtain ⟨j', -, hj'⟩ := hτj
      rw [← hj']
      simp only [LTVal.lower, Option.getD_none, LVal.toLTVal, Scope.castLen]
      rw [Scope.extend_not_mem _ xs s hs]
      have hval := Scope.ofCaptured_substList (σ := σ) hl
        (fun x v hv => LVal.ne_name_of_closed (hσ x v hv).choose_spec s) zs
      rw [hΓ] at hval
      cases hc : Scope.ofCaptured (LVal.substList σ zs) s with
      | none => rw [hc] at hval; simp at hval
      | some i'' =>
        rw [hc] at hval
        simp only [Option.map_some, Option.some.injEq] at hval
        simp only [Option.map_some, Option.some.injEq, LTVal.bvar.injEq]
        apply Fin.ext; simp only [Fin.val_cast]; omega

theorem lbind2_eq_some {α β γ : Type} {x : Option α} {y : Option β} {f : α → β → γ}
    {c : γ} (h : (do let a ← x; let b ← y; pure (f a b) : Option γ) = some c) :
    ∃ a b, x = some a ∧ y = some b ∧ c = f a b := by
  cases x <;> cases y <;> simp_all

theorem lbind2_some {α β γ : Type} {x : Option α} {y : Option β} {f : α → β → γ}
    {a : α} {b : β} (hx : x = some a) (hy : y = some b) :
    (do let a ← x; let b ← y; pure (f a b) : Option γ) = some (f a b) := by
  subst hx hy; rfl

/-! ## The commutation lemma -/

mutual
/-- Resolution commutes with substitution, for values. -/
theorem LVal.toLTVal_subst {m n : Nat} {Γ : Scope m} {Δ : Scope n} {σ : LSubst}
    {τ : Fin m → LTVal n}
    (hσ : ∀ x v, σ x = some v → ∃ c, v.toLTVal Scope.empty = some c)
    (hloc : ∀ l, σ (.loc l) = none)
    (hτ : ∀ s i, Γ s = some i → ((LVal.var (.name s)).subst σ).toLTVal Δ = some (τ i)) :
    ∀ (v : LVal) (t : LTVal m), v.toLTVal Γ = some t →
      (v.subst σ).toLTVal Δ = some (t.isubst τ)
  | .var (.name s), t, h => by
    simp only [LVal.toLTVal, Option.map_eq_some_iff] at h
    obtain ⟨i, hi, rfl⟩ := h
    exact hτ s i hi
  | .var (.loc l), t, h => by
    simp only [LVal.toLTVal, Option.some.injEq] at h; subst h
    simp [LVal.subst, hloc, LVal.toLTVal, LTVal.isubst]
  | .fn f, t, h => by
    simp only [LVal.toLTVal, Option.some.injEq] at h; subst h
    simp [LVal.subst, LVal.toLTVal, LTVal.isubst]
  | .ctor c vs, t, h => by
    simp only [LVal.toLTVal, Option.map_eq_some_iff] at h
    obtain ⟨ts, hts, rfl⟩ := h
    obtain ⟨a, ha, hsa⟩ := LVal.toLTVals_subst hσ hloc hτ vs ts hts
    simp only [LVal.subst, LVal.toLTVal, ha, Option.map_some, LTVal.isubst]
    exact congrArg some (sigma_app (F := LTVals n) (fun k a => LTVal.ctor c a) hsa)
  | .lam zs xs e, t, h => by
    obtain ⟨ts, tb, hts, htb, rfl⟩ := lbind2_eq_some h
    obtain ⟨a, ha, hsa⟩ := LVal.toLTVals_subst hσ hloc hτ zs ts hts
    have hlen := LVal.substList_length σ zs
    have hb := LExpr.toLTerm_subst (LSubst.remove_closed hσ xs)
      (fun l => by rw [LSubst.remove_loc']; exact hloc l)
      (lsubst_hyp_cap hσ hτ zs ts hts xs hlen) e tb htb
    obtain ⟨b, hb', hsb⟩ := LExpr.toLTerm_castLen hlen _ _ hb
    simp only [LVal.subst, LVal.toLTVal, LTVal.isubst]
    rw [lbind2_some ha hb']
    exact congrArg some (sigma_lam _ hsa hsb)
/-- Resolution commutes with substitution, for lists of values. -/
theorem LVal.toLTVals_subst {m n : Nat} {Γ : Scope m} {Δ : Scope n} {σ : LSubst}
    {τ : Fin m → LTVal n}
    (hσ : ∀ x v, σ x = some v → ∃ c, v.toLTVal Scope.empty = some c)
    (hloc : ∀ l, σ (.loc l) = none)
    (hτ : ∀ s i, Γ s = some i → ((LVal.var (.name s)).subst σ).toLTVal Δ = some (τ i)) :
    ∀ (vs : List LVal) (ts : LTVals m vs.length), LVal.toLTVals Γ vs = some ts →
      ∃ a, LVal.toLTVals Δ (LVal.substList σ vs) = some a ∧
        (⟨_, a⟩ : Σ k, LTVals n k) = ⟨vs.length, LTVals.isubst τ ts⟩
  | [], ts, h => by
    simp only [LVal.toLTVals, Option.some.injEq] at h; subst h
    exact ⟨.nil, rfl, rfl⟩
  | v :: vs, ts, h => by
    obtain ⟨t, ts', ht, hts', rfl⟩ := lbind2_eq_some h
    obtain ⟨a, ha, hsa⟩ := LVal.toLTVals_subst hσ hloc hτ vs ts' hts'
    refine ⟨.cons (t.isubst τ) a, ?_, ?_⟩
    · simp only [LVal.substList, LVal.toLTVals]
      exact lbind2_some (LVal.toLTVal_subst hσ hloc hτ v t ht) ha
    · exact sigma_cons _ hsa
/-- **Resolution commutes with substitution.**  If the substituted values are closed and
    every name `s` that `Γ` resolves to `i` becomes, after substitution, a value resolving
    in `Δ` to `τ i`, then resolving `e[σ]` in `Δ` gives the closure-instantiating
    substitution `t[τ]`. -/
theorem LExpr.toLTerm_subst {m n : Nat} {Γ : Scope m} {Δ : Scope n} {σ : LSubst}
    {τ : Fin m → LTVal n}
    (hσ : ∀ x v, σ x = some v → ∃ c, v.toLTVal Scope.empty = some c)
    (hloc : ∀ l, σ (.loc l) = none)
    (hτ : ∀ s i, Γ s = some i → ((LVal.var (.name s)).subst σ).toLTVal Δ = some (τ i)) :
    ∀ (e : LExpr) (t : LTerm m), e.toLTerm Γ = some t →
      (e.subst σ).toLTerm Δ = some (t.isubst τ)
  | .ret vs, t, h => by
    simp only [LExpr.toLTerm, Option.map_eq_some_iff] at h
    obtain ⟨ts, hts, rfl⟩ := h
    obtain ⟨a, ha, hsa⟩ := LVal.toLTVals_subst hσ hloc hτ vs ts hts
    simp only [LExpr.subst, LExpr.toLTerm, ha, Option.map_some, LTerm.isubst]
    exact congrArg some (sigma_app (F := LTVals n) (fun k a => LTerm.ret a) hsa)
  | .app e1 e2, t, h => by
    obtain ⟨t1, t2, h1, h2, rfl⟩ := lbind2_eq_some h
    simp only [LExpr.subst, LExpr.toLTerm, LTerm.isubst]
    exact lbind2_some (LExpr.toLTerm_subst hσ hloc hτ e1 t1 h1)
      (LExpr.toLTerm_subst hσ hloc hτ e2 t2 h2)
  | .call f e1 e2, t, h => by
    obtain ⟨t1, t2, h1, h2, rfl⟩ := lbind2_eq_some h
    simp only [LExpr.subst, LExpr.toLTerm, LTerm.isubst]
    exact lbind2_some (LExpr.toLTerm_subst hσ hloc hτ e1 t1 h1)
      (LExpr.toLTerm_subst hσ hloc hτ e2 t2 h2)
  | .letIn xs e1 e2, t, h => by
    obtain ⟨t1, t2, h1, h2, rfl⟩ := lbind2_eq_some h
    simp only [LExpr.subst, LExpr.toLTerm, LTerm.isubst]
    exact lbind2_some (LExpr.toLTerm_subst hσ hloc hτ e1 t1 h1)
      (LExpr.toLTerm_subst (LSubst.remove_closed hσ xs)
        (fun l => by rw [LSubst.remove_loc']; exact hloc l) (lsubst_hyp_up hσ hτ xs) e2 t2 h2)
  | .match x bs, t, h => by
    obtain ⟨t1, t2, h1, h2, rfl⟩ := lbind2_eq_some h
    simp only [LExpr.subst, LExpr.toLTerm, LTerm.isubst]
    exact lbind2_some (LVal.toLTVal_subst hσ hloc hτ x t1 h1)
      (LExpr.toLBranches_subst hσ hloc hτ bs t2 h2)
  | .dup x e, t, h => by
    obtain ⟨t1, t2, h1, h2, rfl⟩ := lbind2_eq_some h
    simp only [LExpr.subst, LExpr.toLTerm, LTerm.isubst]
    exact lbind2_some (LVal.toLTVal_subst hσ hloc hτ x t1 h1)
      (LExpr.toLTerm_subst hσ hloc hτ e t2 h2)
  | .drop x e, t, h => by
    obtain ⟨t1, t2, h1, h2, rfl⟩ := lbind2_eq_some h
    simp only [LExpr.subst, LExpr.toLTerm, LTerm.isubst]
    exact lbind2_some (LVal.toLTVal_subst hσ hloc hτ x t1 h1)
      (LExpr.toLTerm_subst hσ hloc hτ e t2 h2)
  | .dropru x k e, t, h => by
    obtain ⟨t1, t2, h1, h2, rfl⟩ := lbind2_eq_some h
    simp only [LExpr.subst, LExpr.toLTerm, LTerm.isubst]
    exact lbind2_some (LVal.toLTVal_subst hσ hloc hτ x t1 h1)
      (LExpr.toLTerm_subst hσ hloc hτ e t2 h2)
  | .free k e, t, h => by
    simp only [LExpr.toLTerm, Option.map_eq_some_iff] at h
    obtain ⟨t', ht, rfl⟩ := h
    simp [LExpr.subst, LExpr.toLTerm, LTerm.isubst, LExpr.toLTerm_subst hσ hloc hτ e t' ht]
  | .alloc k e, t, h => by
    simp only [LExpr.toLTerm, Option.map_eq_some_iff] at h
    obtain ⟨t', ht, rfl⟩ := h
    simp [LExpr.subst, LExpr.toLTerm, LTerm.isubst, LExpr.toLTerm_subst hσ hloc hτ e t' ht]
/-- `LExpr.toLTerm_subst` for the branches of a match. -/
theorem LExpr.toLBranches_subst {m n : Nat} {Γ : Scope m} {Δ : Scope n} {σ : LSubst}
    {τ : Fin m → LTVal n}
    (hσ : ∀ x v, σ x = some v → ∃ c, v.toLTVal Scope.empty = some c)
    (hloc : ∀ l, σ (.loc l) = none)
    (hτ : ∀ s i, Γ s = some i → ((LVal.var (.name s)).subst σ).toLTVal Δ = some (τ i)) :
    ∀ (bs : List LBranch) (t : LTBranches m), LExpr.toLBranches Γ bs = some t →
      LExpr.toLBranches Δ (LExpr.substB σ bs) = some (t.isubst τ)
  | [], t, h => by
    simp only [LExpr.toLBranches, Option.some.injEq] at h; subst h; rfl
  | .mk c xs e :: bs, t, h => by
    obtain ⟨t1, t2, h1, h2, rfl⟩ := lbind2_eq_some h
    simp only [LExpr.substB, LExpr.toLBranches, LTBranches.isubst]
    exact lbind2_some
      (LExpr.toLTerm_subst (LSubst.remove_closed hσ xs)
        (fun l => by rw [LSubst.remove_loc']; exact hloc l) (lsubst_hyp_up hσ hτ xs) e t1 h1)
      (LExpr.toLBranches_subst hσ hloc hτ bs t2 h2)
end

end FIPNamed.Lam
