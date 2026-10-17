module

public import RequestProject.AppB_StoreSoundness.StoreAlloc
public import RequestProject.AppB_StoreSoundness.FunSteps

@[expose] public section

/-!
# The main invariant of the proof of Theorem 1 (Appendix B.5)

The proof of Theorem 1 proceeds by induction on the length of the functional reduction and
on the derivation of `Δ | Γ ⊢ e`.  To avoid substituting into well-formedness derivations,
the expression evaluated by the store semantics is kept in the form `e[ρ]`, where
`e : Expr m` is the well-formed expression and `ρ : Fin m → Val 0` maps its de Bruijn
indices to locations and top-level functions.  Under a binder, `ρ` is extended by
`Subst.inst`.

* `Borrowed sig S₁ ρ x`: the borrowed variable `x` denotes a location of the borrowed
  store `S₁`, or an annotated top-level function;
* `Owned ρ Γ S₂`: the owned environment `Γ`, renamed by `ρ`, is exactly the set of roots of
  the owned store `S₂` (up to credits of size `0`, which occupy no memory).
-/

namespace FIP

/-- Rename an owned variable by a substitution into closed values.  (An owned variable is
    always renamed to a location; the last case does not occur.) -/
def Res.substR {m : Nat} (ρ : Fin m → Val 0) : Res m → Res 0
  | .var x => match Val.subst ρ (.var x) with
    | .var y => .var y
    | _ => .var (.loc 0)
  | .credit k => .credit k
  | .alloc => .alloc

/-- Discard the reuse credits of size `0`. -/
def Ctx.nz {m : Nat} (Γ : Ctx m) : Ctx m := Γ.filter (· ≠ Res.credit 0)

/-- The owned environment `Γ[ρ]` is the set of roots of `S₂`. -/
structure Owned {m : Nat} (ρ : Fin m → Val 0) (Γ : Ctx m) (S₂ : Store) : Prop where
  var : ∀ x, Res.var x ∈ Γ → ∃ l, Val.subst ρ (.var x) = .var (.loc l)
  roots : Ctx.nz (Γ.map (Res.substR ρ)) = S₂.roots

/-- The borrowed variable `x` denotes a location of `S₁` or an annotated function. -/
def Borrowed {m : Nat} (sig : Sig) (S₁ : Store) (ρ : Fin m → Val 0) (x : Var m) : Prop :=
  (∃ l, Val.subst ρ (.var x) = .var (.loc l) ∧ Var.loc l ∈ S₁.dom) ∨
  (∃ g fd, Val.subst ρ (.var x) = .fn g ∧ sig.lookup g = some fd ∧ fd.annot ≠ .plain)

/-- A substitution by locations and top-level functions. -/
def Subst.Atomic {m : Nat} (ρ : Fin m → Val 0) : Prop :=
  ∀ i, (∃ l, ρ i = .var (.loc l)) ∨ ∃ g, ρ i = .fn g

/-- The conclusion of Theorem 1 for `S₁, S₂ | e`. -/
def StoreResult (sig : Sig) (fbip : Bool) (S₁ S₂ : Store) (e : Expr 0)
    (σ : Nat → Option (Val 0)) (vs : List (Val 0)) : Prop :=
  ∃ (S₃ : Store) (xs : List (Var 0)) (σ₃ : Nat → Option (Val 0)),
    SSteps sig fbip (S₁ + S₂) e (S₁ + S₃) (.ret (xs.map .var)) ∧
    S₃.roots = (xs.map Res.var : Multiset (Res 0)) ∧ OwnedInv S₁ S₃ σ₃ ∧
    (∀ n, Var.loc n ∈ S₁.dom → σ₃ n = σ n) ∧
    xs.map (fun x => Val.substLoc σ₃ (.var x)) = vs

/-- The statement proved by induction on the length `n` of the functional reduction. -/
def MainClaim (sig : Sig) (fbip : Bool) (n : Nat) : Prop :=
  ∀ {m : Nat} {cfg : Cfg} {U Δ : Finset (Var m)} {Γ : Ctx m} {e : Expr m},
    cfg.Compatible sig fbip → U = ∅ → e.scalarFree = true → Wf cfg U Δ Γ e →
    ∀ {ρ : Fin m → Val 0} {S₁ S₂ : Store} {σ : Nat → Option (Val 0)} {vs : List (Val 0)},
    Subst.Atomic ρ →
    (∀ x ∈ Δ, Borrowed sig S₁ ρ x) → Owned ρ Γ S₂ → S₁.Sound → OwnedInv S₁ S₂ σ →
    StepsN sig n ((e.subst ρ).substLoc σ) (.ret vs) →
    StoreResult sig fbip S₁ S₂ (e.subst ρ) σ vs

/-! ## Atomic substitutions -/

/-- Under an atomic substitution, a variable becomes a location or a function. -/
theorem Subst.Atomic.subst_var {m : Nat} {ρ : Fin m → Val 0} (h : Subst.Atomic ρ) (x : Var m) :
    (∃ l, Val.subst ρ (.var x) = .var (.loc l)) ∨ ∃ g, Val.subst ρ (.var x) = .fn g := by
  cases x with
  | loc l => exact .inl ⟨l, rfl⟩
  | bvar i => exact h i

/-- The atomic values (locations and functions) of an extended substitution. -/
theorem Subst.Atomic.inst {m : Nat} {ρ : Fin m → Val 0} (h : Subst.Atomic ρ) {k : Nat}
    {ws : List (Val 0)} (hl : ws.length = k)
    (hws : ∀ w ∈ ws, (∃ l, w = .var (.loc l)) ∨ ∃ g, w = .fn g) :
    Subst.Atomic (Subst.inst k ws ρ) := by
  intro i
  by_cases hi : i.val < k
  · rw [Subst.inst_lt _ _ _ _ hi, List.getD_eq_getElem _ _ (by omega)]
    exact hws _ (List.getElem_mem _)
  · rw [Subst.inst_ge _ _ _ _ (by omega)]
    exact h _

/-! ## Extending a substitution under binders -/

/-- A weakened variable is substituted as before. -/
theorem Val.subst_inst_shift {n m : Nat} (k : Nat) (ws : List (Val m)) (ρ : Fin n → Val m)
    (x : Var n) : Val.subst (Subst.inst k ws ρ) (.var (x.shift k)) = Val.subst ρ (.var x) := by
  rw [← Val.shift_var, Val.shift_subst_inst]

/-- A new binder is substituted by its value. -/
theorem Val.subst_inst_newB {n m : Nat} {k : Nat} {ws : List (Val m)} (ρ : Fin n → Val m)
    (hl : ws.length = k) (j : Fin k) :
    Val.subst (Subst.inst k ws ρ) (.var (Var.newB j)) = ws[j.val]'(by omega) := by
  simp only [Var.newB, Val.subst_bvar]
  rw [Subst.inst_lt _ _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp; omega)]

/-! ## Scalar-free binders -/

theorem Binder.select_false_of_all {N : Nat} {xs : List Bool} (h : xs.all (!·) = true)
    (f : Fin xs.length → Var N) : Binder.select xs false f = (List.finRange xs.length).map f := by
  unfold Binder.select
  congr 1
  refine List.filter_eq_self.mpr fun j _ => ?_
  have := List.all_eq_true.mp h xs[j] (List.getElem_mem _)
  simpa using this

theorem Binder.select_true_of_all {N : Nat} {xs : List Bool} (h : xs.all (!·) = true)
    (f : Fin xs.length → Var N) : Binder.select xs true f = [] := by
  unfold Binder.select
  simp only [List.map_eq_nil_iff, List.filter_eq_nil_iff]
  intro j _
  have := List.all_eq_true.mp h xs[j] (List.getElem_mem _)
  simpa using this

theorem Binder.scalars_of_all {n : Nat} {xs : List Bool} (h : xs.all (!·) = true) :
    (Binder.scalars xs : Finset (Var (n + xs.length))) = ∅ := by
  simp [Binder.scalars, Binder.scalarsAt, Binder.select_true_of_all h]

theorem Binder.owned_of_all {n : Nat} {xs : List Bool} (h : xs.all (!·) = true) :
    (Binder.owned xs : Ctx (n + xs.length)) =
      (((List.finRange xs.length).map fun j => Res.var (Var.newB (n := n) j) :
        List (Res (n + xs.length))) : Multiset (Res (n + xs.length))) := by
  simp [Binder.owned, Binder.ownedAt, Binder.select_false_of_all h, List.map_map,
    Function.comp_def]

theorem Binder.ownedSet_of_all {n : Nat} {xs : List Bool} (h : xs.all (!·) = true) :
    (Binder.ownedSet xs : Finset (Var (n + xs.length))) =
      ((List.finRange xs.length).map Var.newB).toFinset := by
  simp [Binder.ownedSet, Binder.ownedSetAt, Binder.select_false_of_all h]

/-! ## Renaming owned environments -/

theorem Ctx.nz_add {m : Nat} (Γ Γ' : Ctx m) : Ctx.nz (Γ + Γ') = Ctx.nz Γ + Ctx.nz Γ' := by
  simp [Ctx.nz, Multiset.filter_add]

theorem Res.substR_var {m : Nat} {ρ : Fin m → Val 0} {x : Var m} {y : Var 0}
    (h : Val.subst ρ (.var x) = .var y) : (Res.var x).substR ρ = .var y := by
  simp [Res.substR, h]

theorem Ctx.map_substR_congr {m m' : Nat} {ρ : Fin m → Val 0} {ρ' : Fin m' → Val 0} {Γ : Ctx m}
    {f : Res m → Res m'}
    (hf : ∀ r ∈ Γ, ∀ k, r = .credit k → f r = .credit k) (hfa : ∀ r ∈ Γ, r = .alloc → f r = .alloc)
    (h : ∀ x, Res.var x ∈ Γ → ∃ x', f (.var x) = .var x' ∧
      Val.subst ρ' (.var x') = Val.subst ρ (.var x)) :
    (Γ.map f).map (Res.substR ρ') = Γ.map (Res.substR ρ) := by
  rw [Multiset.map_map]
  refine Multiset.map_congr rfl fun r hr => ?_
  cases r with
  | var x =>
    obtain ⟨x', hx', hs⟩ := h x hr
    simp only [Function.comp_apply, hx', Res.substR, hs]
  | credit k => simp [hf _ hr k rfl, Res.substR]
  | alloc => simp [hfa _ hr rfl, Res.substR]

/-- Renaming a weakened environment with an extended substitution. -/
theorem Ctx.shift_substR {m : Nat} (k : Nat) (ws : List (Val 0)) (ρ : Fin m → Val 0)
    (Γ : Ctx m) : (Γ.shift k).map (Res.substR (Subst.inst k ws ρ)) = Γ.map (Res.substR ρ) := by
  refine Ctx.map_substR_congr (fun r _ j hr => by subst hr; rfl) (fun r _ hr => by subst hr; rfl)
    fun x _ => ⟨x.shift k, rfl, Val.subst_inst_shift k ws ρ x⟩

theorem Binder.owned_substR {m : Nat} {ρ : Fin m → Val 0} {xs : List Bool}
    (hall : xs.all (!·) = true) {ls : List (Var 0)} (hl : xs.length = ls.length) :
    (Binder.owned xs : Ctx (m + xs.length)).map
        (Res.substR (Subst.inst xs.length (ls.map .var) ρ)) =
      ((ls.map Res.var : List (Res 0)) : Multiset (Res 0)) := by
  rw [Binder.owned_of_all hall, Multiset.map_coe, List.map_map]
  congr 1
  apply List.ext_getElem (by simp [hl])
  intro i h1 h2
  simp only [List.length_map, List.length_finRange] at h1
  simp only [List.getElem_map, Function.comp, List.getElem_finRange]
  rw [Res.substR_var (y := ls[i]'(hl ▸ h1))
    (by rw [Val.subst_inst_newB ρ (by simp [hl])]; simp)]

theorem Ctx.nz_owned {N : Nat} {xs : List Bool} {f : Fin xs.length → Var N} :
    Ctx.nz (Binder.ownedAt xs f) = Binder.ownedAt xs f := by
  simp only [Ctx.nz, Multiset.filter_eq_self]
  intro r hr
  simp only [Binder.ownedAt, Multiset.mem_coe, List.mem_map] at hr
  obtain ⟨b, -, rfl⟩ := hr
  simp

theorem Ctx.nz_vars (ls : List (Var 0)) :
    Ctx.nz ((ls.map Res.var : List (Res 0)) : Multiset (Res 0)) =
      ((ls.map Res.var : List (Res 0)) : Multiset (Res 0)) := by
  simp only [Ctx.nz, Multiset.filter_eq_self]
  intro r hr
  simp only [Multiset.mem_coe, List.mem_map] at hr
  obtain ⟨b, -, rfl⟩ := hr
  simp

theorem Ctx.nz_credit {m : Nat} {ρ : Fin m → Val 0} (k : Nat) :
    Ctx.nz (Multiset.map (Res.substR ρ) {Res.credit k}) = Cell.credits (.credit k) := by
  by_cases hk : k = 0 <;> simp [Ctx.nz, Res.substR, Cell.credits, hk]

/-! ## Renaming well-formed values -/

/-- Renaming the owned variables of a well-formed value (both statements at once). -/
theorem WfVal.substR_both {m : Nat} {Δ : Finset (Var m)} {Δ' : Finset (Var 0)}
    {ρ : Fin m → Val 0} :
    (∀ {Γ : Ctx m} {v : Val m}, WfVal ∅ Δ Γ v →
      (∀ x, Res.var x ∈ Γ → ∃ y, Val.subst ρ (.var x) = .var y) →
      WfVal ∅ Δ' (Γ.map (Res.substR ρ)) (v.subst ρ)) ∧
    (∀ {Γ : Ctx m} {vs : List (Val m)}, WfVals ∅ Δ Γ vs →
      (∀ x, Res.var x ∈ Γ → ∃ y, Val.subst ρ (.var x) = .var y) →
      WfVals ∅ Δ' (Γ.map (Res.substR ρ)) (Val.substList ρ vs)) := by
  let M1 : (Γ : Ctx m) → (v : Val m) → WfVal ∅ Δ Γ v → Prop := fun Γ v _ =>
    (∀ x, Res.var x ∈ Γ → ∃ y, Val.subst ρ (.var x) = .var y) →
      WfVal ∅ Δ' (Γ.map (Res.substR ρ)) (v.subst ρ)
  let M2 : (Γ : Ctx m) → (vs : List (Val m)) → WfVals ∅ Δ Γ vs → Prop := fun Γ vs _ =>
    (∀ x, Res.var x ∈ Γ → ∃ y, Val.subst ρ (.var x) = .var y) →
      WfVals ∅ Δ' (Γ.map (Res.substR ρ)) (Val.substList ρ vs)
  have m1 : ∀ x, M1 {Res.var x} (.var x) (.var x) := fun x h => by
    obtain ⟨y, hy⟩ := h x (Multiset.mem_singleton_self _)
    rw [hy, Multiset.map_singleton, Res.substR_var hy]
    exact .var y
  have m2 : ∀ x (hx : x ∈ (∅ : Finset (Var m))), M1 0 (.var x) (.svar x hx) := fun x hx _ => by
    simp at hx
  have m3 : ∀ c, M1 0 (.ctor c []) (.atom c) := fun c _ => by
    simpa [Val.subst, Val.substList] using WfVal.atom (U := ∅) (Δ := Δ') c
  have m4 : ∀ n, M1 0 (.lit n) (.lit n) := fun n _ => by
    simpa [Val.subst] using WfVal.lit (U := ∅) (Δ := Δ') n
  have m5 : ∀ c vs Γ (hne : vs ≠ []) (hvs : WfVals ∅ Δ Γ vs), M2 Γ vs hvs →
      M1 (Γ + {Res.credit vs.length}) (.ctor c vs) (.reuse c vs Γ hne hvs) := by
    intro c vs Γ hne _ ih h
    obtain ⟨v0, vs0, rfl⟩ := List.exists_cons_of_ne_nil hne
    have hl : (Val.substList ρ vs0).length = vs0.length := by simp
    have h' := ih (fun x hx => h x (Multiset.mem_add.mpr (.inl hx)))
    have := WfVal.reuse (U := ∅) (Δ := Δ') c (Val.substList ρ (v0 :: vs0)) _
      (by simp [Val.substList]) h'
    have e1 : (Val.substList ρ (v0 :: vs0)).length = (v0 :: vs0).length := by
      simp only [Val.substList, List.length_cons, hl]
    have e2 : Val.subst ρ (.ctor c (v0 :: vs0)) = .ctor c (Val.substList ρ (v0 :: vs0)) := by
      simp only [Val.subst]
    have e3 : (Γ + {Res.credit (v0 :: vs0).length}).map (Res.substR ρ) =
        Γ.map (Res.substR ρ) + {Res.credit (v0 :: vs0).length} := by
      simp [Res.substR]
    show WfVal ∅ Δ' _ _
    rw [e2, e3, ← e1]
    exact this
  have m6 : M2 0 [] .nil := fun _ => by
    simpa [Val.substList] using WfVals.nil (U := ∅) (Δ := Δ')
  have m7 : ∀ Γ₁ Γ₂ v vs (hv : WfVal ∅ Δ Γ₁ v) (hvs : WfVals ∅ Δ Γ₂ vs), M1 Γ₁ v hv →
      M2 Γ₂ vs hvs → M2 (Γ₁ + Γ₂) (v :: vs) (.cons Γ₁ Γ₂ v vs hv hvs) := by
    intro Γ₁ Γ₂ v vs _ _ ih1 ih2 h
    have := WfVals.cons _ _ _ _
      (ih1 (fun x hx => h x (Multiset.mem_add.mpr (.inl hx))))
      (ih2 (fun x hx => h x (Multiset.mem_add.mpr (.inr hx))))
    simpa [Val.substList] using this
  exact ⟨fun hv => WfVal.rec (motive_1 := M1) (motive_2 := M2) m1 m2 m3 m4 m5 m6 m7 hv,
    fun hvs => WfVals.rec (motive_1 := M1) (motive_2 := M2) m1 m2 m3 m4 m5 m6 m7 hvs⟩

theorem WfVal.substR {m : Nat} {Δ : Finset (Var m)} {Δ' : Finset (Var 0)} {ρ : Fin m → Val 0}
    {Γ : Ctx m} {v : Val m} (hv : WfVal ∅ Δ Γ v)
    (h : ∀ x, Res.var x ∈ Γ → ∃ y, Val.subst ρ (.var x) = .var y) :
    WfVal ∅ Δ' (Γ.map (Res.substR ρ)) (v.subst ρ) := WfVal.substR_both.1 hv h

theorem WfVals.substR {m : Nat} {Δ : Finset (Var m)} {Δ' : Finset (Var 0)} {ρ : Fin m → Val 0}
    {Γ : Ctx m} {vs : List (Val m)}
    (hvs : WfVals ∅ Δ Γ vs) (h : ∀ x, Res.var x ∈ Γ → ∃ y, Val.subst ρ (.var x) = .var y) :
    WfVals ∅ Δ' (Γ.map (Res.substR ρ)) (Val.substList ρ vs) := WfVal.substR_both.2 hvs h

mutual
theorem WfVal.no_credit_zero {m : Nat} {U Δ : Finset (Var m)} :
    ∀ {Γ : Ctx m} {v : Val m}, WfVal U Δ Γ v → Res.credit 0 ∉ Γ
  | _, _, .var x => by simp
  | _, _, .svar x _ => by simp
  | _, _, .atom c => by simp
  | _, _, .lit n => by simp
  | _, _, .reuse c vs Γ hne hvs => by
    simp only [Multiset.mem_add, Multiset.mem_singleton, Res.credit.injEq, not_or]
    exact ⟨WfVals.no_credit_zero hvs, by intro h; apply hne; exact List.length_eq_zero_iff.mp h.symm⟩
theorem WfVals.no_credit_zero {m : Nat} {U Δ : Finset (Var m)} :
    ∀ {Γ : Ctx m} {vs : List (Val m)}, WfVals U Δ Γ vs → Res.credit 0 ∉ Γ
  | _, _, .nil => by simp
  | _, _, .cons Γ₁ Γ₂ v vs hv hvs => by
    simp only [Multiset.mem_add, not_or]
    exact ⟨WfVal.no_credit_zero hv, WfVals.no_credit_zero hvs⟩
end

/-! ## Locations of a substituted expression -/

theorem locs_subst {cfg : Cfg} {m : Nat} {U Δ : Finset (Var m)} {Γ : Ctx m} {e : Expr m}
    (h : Wf cfg U Δ Γ e) (hU : U = ∅) {ρ : Fin m → Val 0} {D : Var 0 → Prop}
    (hΔ : ∀ x ∈ Δ, ∀ l, Var.loc l ∈ Val.fv (Val.subst ρ (.var x)) → D (.loc l))
    (hΓ : ∀ x, Res.var x ∈ Γ → ∀ l, Var.loc l ∈ Val.fv (Val.subst ρ (.var x)) → D (.loc l))
    (l : Nat) (hl : Var.loc l ∈ (e.subst ρ).fv) : D (.loc l) := by
  obtain ⟨x, hx, hl'⟩ := Expr.fv_subst ρ (.loc l) e hl
  rcases Wf.fv_subset h x hx with h1 | h1 | h1
  · subst hU; simp at h1
  · exact hΔ x h1 l hl'
  · exact hΓ x h1 l hl'

end FIP
