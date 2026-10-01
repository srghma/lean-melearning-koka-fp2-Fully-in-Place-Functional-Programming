module

public import RequestProject.FIP.StoreAlloc
public import RequestProject.FIP.FunSteps

@[expose] public section

/-!
# The main invariant of the proof of Theorem 1 (Appendix B.5)

The proof of Theorem 1 proceeds by induction on the length of the functional reduction and
on the derivation of `Δ | Γ ⊢ e`.  To avoid substituting into well-formedness derivations,
the expression evaluated by the store semantics is kept in the form `e[ρ]`, where `e` is
the well-formed expression and `ρ` maps its free program names to locations and top-level
functions.

* `Borrowed sig S₁ ρ x`: the borrowed variable `x` denotes a location of the borrowed
  store `S₁`, or an annotated top-level function;
* `Owned ρ Γ S₂`: the owned environment `Γ`, renamed by `ρ`, is exactly the set of roots of
  the owned store `S₂` (up to credits of size `0`, which occupy no memory).
-/

namespace FIP

/-- Rename an owned variable by a name substitution. -/
def Res.substR (ρ : Subst) : Res → Res
  | .var x => match Val.subst ρ (.var x) with
    | .var y => .var y
    | _ => .var x
  | r => r

/-- Discard the reuse credits of size `0`. -/
def Ctx.nz (Γ : Ctx) : Ctx := Γ.filter (· ≠ Res.credit 0)

/-- The owned environment `Γ[ρ]` is the set of roots of `S₂`. -/
structure Owned (ρ : Subst) (Γ : Ctx) (S₂ : Store) : Prop where
  var : ∀ x, Res.var x ∈ Γ → ∃ l, Val.subst ρ (.var x) = .var (.loc l)
  roots : Ctx.nz (Γ.map (Res.substR ρ)) = S₂.roots

/-- The borrowed variable `x` denotes a location of `S₁` or an annotated function. -/
def Borrowed (sig : Sig) (S₁ : Store) (ρ : Subst) (x : Var) : Prop :=
  (∃ l, Val.subst ρ (.var x) = .var (.loc l) ∧ Var.loc l ∈ S₁.dom) ∨
  (∃ g fd, Val.subst ρ (.var x) = .fn g ∧ sig.lookup g = some fd ∧ fd.annot ≠ .plain)

/-- A name substitution by locations and top-level functions. -/
def Subst.Atomic (ρ : Subst) : Prop :=
  ∀ p ∈ ρ, (∃ l, p.2 = .var (.loc l)) ∨ ∃ g, p.2 = .fn g

/-- The conclusion of Theorem 1 for `S₁, S₂ | e`. -/
def StoreResult (sig : Sig) (fbip : Bool) (S₁ S₂ : Store) (e : Expr) (σ : Nat → Option Val)
    (vs : List Val) : Prop :=
  ∃ (S₃ : Store) (xs : List Var) (σ₃ : Nat → Option Val),
    SSteps sig fbip (S₁ + S₂) e (S₁ + S₃) (.ret (xs.map .var)) ∧
    S₃.roots = (xs.map Res.var : Multiset Res) ∧ OwnedInv S₁ S₃ σ₃ ∧
    (∀ n, Var.loc n ∈ S₁.dom → σ₃ n = σ n) ∧
    xs.map (fun x => Val.substLoc σ₃ (.var x)) = vs

/-- The statement proved by induction on the length `n` of the functional reduction. -/
def MainClaim (sig : Sig) (fbip : Bool) (n : Nat) : Prop :=
  ∀ {cfg : Cfg} {U Δ : Finset Var} {Γ : Ctx} {e : Expr}, cfg.Compatible sig fbip → U = ∅ →
    e.scalarFree = true → Wf cfg U Δ Γ e →
    ∀ {ρ : Subst} {S₁ S₂ : Store} {σ : Nat → Option Val} {vs : List Val}, ρ.Atomic →
    (∀ x ∈ Δ, Borrowed sig S₁ ρ x) → Owned ρ Γ S₂ → S₁.Sound → OwnedInv S₁ S₂ σ →
    StepsN sig n ((e.subst ρ).substLoc σ) (.ret vs) →
    StoreResult sig fbip S₁ S₂ (e.subst ρ) σ vs

/-! ## Atomic substitutions -/

theorem Subst.Atomic.noName {ρ : Subst} (h : ρ.Atomic) : ρ.NoName := by
  intro p hp s hs
  rcases h p hp with ⟨l, hl⟩ | ⟨g, hg⟩
  · rw [hl] at hs; simp [Val.fv] at hs
  · rw [hg] at hs; simp [Val.fv] at hs

theorem Subst.Atomic.remove {ρ : Subst} (h : ρ.Atomic) (xs : List Binder) :
    (ρ.remove xs).Atomic := fun p hp => h p (List.mem_of_mem_filter hp)

theorem Subst.Atomic.append {ρ1 ρ2 : Subst} (h1 : ρ1.Atomic) (h2 : ρ2.Atomic) :
    (ρ1 ++ ρ2).Atomic := by
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · exact h1 p hp
  · exact h2 p hp

theorem Subst.atomic_zipSubst (xs : List Binder) (vs : List Val)
    (h : ∀ v ∈ vs, (∃ l, v = .var (.loc l)) ∨ ∃ g, v = .fn g) : (zipSubst xs vs).Atomic := by
  intro p hp
  exact h p.2 (List.of_mem_zip hp).2

theorem Subst.lookup_mem {ρ : Subst} {s : String} {v : Val} (h : ρ.lookup s = some v) :
    ∃ p ∈ ρ, p.2 = v := by
  induction ρ with
  | nil => simp at h
  | cons q ρ ih =>
    obtain ⟨t, u⟩ := q
    by_cases hst : s = t
    · subst hst; simp at h; exact ⟨_, List.mem_cons_self, h⟩
    · have : (s == t) = false := by simpa using hst
      simp only [List.lookup_cons, this] at h
      obtain ⟨p, hp, hp'⟩ := ih h
      exact ⟨p, List.mem_cons_of_mem _ hp, hp'⟩

/-- Under an atomic substitution, a variable becomes itself, a location or a function. -/
theorem Subst.Atomic.subst_var {ρ : Subst} (h : ρ.Atomic) (x : Var) :
    Val.subst ρ (.var x) = .var x ∨ (∃ l, Val.subst ρ (.var x) = .var (.loc l)) ∨
      ∃ g, Val.subst ρ (.var x) = .fn g := by
  cases x with
  | loc n => exact .inl rfl
  | name s =>
    simp only [Val.subst]
    cases hl : ρ.lookup s with
    | none => exact .inl rfl
    | some v =>
      obtain ⟨p, hp, rfl⟩ := Subst.lookup_mem hl
      rcases h p hp with ⟨l, hl'⟩ | ⟨g, hg⟩
      · exact .inr (.inl ⟨l, by simp [hl']⟩)
      · exact .inr (.inr ⟨g, by simp [hg]⟩)

/-! ## Extending a substitution under binders -/

theorem Val.subst_ext_not_mem (ρ : Subst) (xs : List Binder) (ws : List Val) {x : Var}
    (hx : x ∉ Binder.vars xs) :
    Val.subst (ρ.remove xs ++ zipSubst xs ws) (.var x) = Val.subst ρ (.var x) := by
  rw [← Val.subst_var_remove ρ xs x hx]
  cases x with
  | loc n => rfl
  | name s =>
    have : s ∉ xs.map (·.name) := by
      intro h; apply hx; simp only [Binder.vars, List.mem_map] at h ⊢
      obtain ⟨b, hb, rfl⟩ := h; exact ⟨b, hb, rfl⟩
    simp only [Val.subst, List.lookup_append, lookup_zipSubst_of_not_mem this, Option.or_none]

theorem Val.subst_ext_mem (ρ : Subst) {xs : List Binder} {ws : List Val}
    (hn : (xs.map (·.name)).Nodup) (hl : xs.length = ws.length) {i : Nat} (hi : i < xs.length) :
    Val.subst (ρ.remove xs ++ zipSubst xs ws) (.var (.name (xs[i]).name)) = ws[i]'(hl ▸ hi) := by
  have hmem : (xs[i]).name ∈ xs.map (·.name) := List.mem_map_of_mem (List.getElem_mem hi)
  simp [Val.subst, List.lookup_append, lookup_remove, hmem, lookup_zipSubst_of_mem hn hl hi]

/-! ## Scalar-free binders -/

theorem Binder.scalars_of_all {xs : List Binder} (h : xs.all (!·.scalar) = true) :
    Binder.scalars xs = ∅ := by
  simp only [Binder.scalars, List.toFinset_eq_empty_iff, List.map_eq_nil_iff,
    List.filter_eq_nil_iff]
  intro b hb hs
  have := List.all_eq_true.mp h b hb
  simp_all

theorem Binder.filter_of_all {xs : List Binder} (h : xs.all (!·.scalar) = true) :
    xs.filter (fun b => !b.scalar) = xs :=
  List.filter_eq_self.mpr fun b hb => List.all_eq_true.mp h b hb

theorem Binder.owned_of_all {xs : List Binder} (h : xs.all (!·.scalar) = true) :
    Binder.owned xs = ((xs.map fun b => Res.var (.name b.name) : List Res) : Multiset Res) := by
  simp only [Binder.owned, Binder.filter_of_all h]

theorem Binder.ownedSet_of_all {xs : List Binder} (h : xs.all (!·.scalar) = true) :
    Binder.ownedSet xs = (Binder.vars xs).toFinset := by
  simp only [Binder.ownedSet, Binder.filter_of_all h, Binder.vars]

/-! ## Renaming owned environments -/

theorem Ctx.nz_add (Γ Γ' : Ctx) : Ctx.nz (Γ + Γ') = Ctx.nz Γ + Ctx.nz Γ' := by
  simp [Ctx.nz, Multiset.filter_add]

theorem Res.substR_var {ρ : Subst} {x y : Var} (h : Val.subst ρ (.var x) = .var y) :
    (Res.var x).substR ρ = .var y := by
  simp [Res.substR, h]

theorem Ctx.map_substR_congr {ρ ρ' : Subst} {Γ : Ctx}
    (h : ∀ x, Res.var x ∈ Γ → Val.subst ρ' (.var x) = Val.subst ρ (.var x)) :
    Γ.map (Res.substR ρ') = Γ.map (Res.substR ρ) := by
  refine Multiset.map_congr rfl fun r hr => ?_
  cases r with
  | var x => simp [Res.substR, h x hr]
  | _ => rfl

theorem Binder.owned_substR {ρ : Subst} {xs : List Binder} (hall : xs.all (!·.scalar) = true)
    (hn : (xs.map (·.name)).Nodup) {ls : List Var} (hl : xs.length = ls.length) :
    (Binder.owned xs).map (Res.substR (ρ.remove xs ++ zipSubst xs (ls.map .var))) =
      ((ls.map Res.var : List Res) : Multiset Res) := by
  rw [Binder.owned_of_all hall, Multiset.map_coe, List.map_map]
  congr 1
  apply List.ext_getElem (by simp [hl])
  intro i h1 h2
  simp only [List.length_map] at h1
  simp only [List.getElem_map, Function.comp]
  rw [Res.substR_var (y := ls[i]'(hl ▸ h1))
    (by rw [Val.subst_ext_mem ρ (ws := ls.map Val.var) hn (by simp [hl]) h1]; simp)]

theorem Ctx.nz_owned {xs : List Binder} : Ctx.nz (Binder.owned xs) = Binder.owned xs := by
  simp only [Ctx.nz, Multiset.filter_eq_self]
  intro r hr
  simp only [Binder.owned, Multiset.mem_coe, List.mem_map] at hr
  obtain ⟨b, -, rfl⟩ := hr
  simp

theorem Ctx.nz_vars (ls : List Var) :
    Ctx.nz ((ls.map Res.var : List Res) : Multiset Res) = ((ls.map Res.var : List Res) : Multiset Res) := by
  simp only [Ctx.nz, Multiset.filter_eq_self]
  intro r hr
  simp only [Multiset.mem_coe, List.mem_map] at hr
  obtain ⟨b, -, rfl⟩ := hr
  simp

theorem Ctx.nz_credit (k : Nat) :
    Ctx.nz (Multiset.map (Res.substR ρ) {Res.credit k}) = Cell.credits (.credit k) := by
  by_cases hk : k = 0 <;> simp [Ctx.nz, Res.substR, Cell.credits, hk]

/-! ## Renaming well-formed values -/

/-- Renaming the owned variables of a well-formed value (both statements at once). -/
theorem WfVal.substR_both {Δ Δ' : Finset Var} {ρ : Subst} :
    (∀ {Γ : Ctx} {v : Val}, WfVal ∅ Δ Γ v →
      (∀ x, Res.var x ∈ Γ → ∃ y, Val.subst ρ (.var x) = .var y) →
      WfVal ∅ Δ' (Γ.map (Res.substR ρ)) (v.subst ρ)) ∧
    (∀ {Γ : Ctx} {vs : List Val}, WfVals ∅ Δ Γ vs →
      (∀ x, Res.var x ∈ Γ → ∃ y, Val.subst ρ (.var x) = .var y) →
      WfVals ∅ Δ' (Γ.map (Res.substR ρ)) (Val.substList ρ vs)) := by
  let M1 : (Γ : Ctx) → (v : Val) → WfVal ∅ Δ Γ v → Prop := fun Γ v _ =>
    (∀ x, Res.var x ∈ Γ → ∃ y, Val.subst ρ (.var x) = .var y) →
      WfVal ∅ Δ' (Γ.map (Res.substR ρ)) (v.subst ρ)
  let M2 : (Γ : Ctx) → (vs : List Val) → WfVals ∅ Δ Γ vs → Prop := fun Γ vs _ =>
    (∀ x, Res.var x ∈ Γ → ∃ y, Val.subst ρ (.var x) = .var y) →
      WfVals ∅ Δ' (Γ.map (Res.substR ρ)) (Val.substList ρ vs)
  have m1 : ∀ x, M1 {Res.var x} (.var x) (.var x) := fun x h => by
    obtain ⟨y, hy⟩ := h x (Multiset.mem_singleton_self _)
    rw [hy, Multiset.map_singleton, Res.substR_var hy]
    exact .var y
  have m2 : ∀ x (hx : x ∈ (∅ : Finset Var)), M1 0 (.var x) (.svar x hx) := fun x hx _ => by
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

theorem WfVal.substR {Δ Δ' : Finset Var} {ρ : Subst} {Γ : Ctx} {v : Val} (hv : WfVal ∅ Δ Γ v)
    (h : ∀ x, Res.var x ∈ Γ → ∃ y, Val.subst ρ (.var x) = .var y) :
    WfVal ∅ Δ' (Γ.map (Res.substR ρ)) (v.subst ρ) := WfVal.substR_both.1 hv h

theorem WfVals.substR {Δ Δ' : Finset Var} {ρ : Subst} {Γ : Ctx} {vs : List Val}
    (hvs : WfVals ∅ Δ Γ vs) (h : ∀ x, Res.var x ∈ Γ → ∃ y, Val.subst ρ (.var x) = .var y) :
    WfVals ∅ Δ' (Γ.map (Res.substR ρ)) (Val.substList ρ vs) := WfVal.substR_both.2 hvs h

mutual
theorem WfVal.no_credit_zero {U Δ : Finset Var} :
    ∀ {Γ : Ctx} {v : Val}, WfVal U Δ Γ v → Res.credit 0 ∉ Γ
  | _, _, .var x => by simp
  | _, _, .svar x _ => by simp
  | _, _, .atom c => by simp
  | _, _, .lit n => by simp
  | _, _, .reuse c vs Γ hne hvs => by
    simp only [Multiset.mem_add, Multiset.mem_singleton, Res.credit.injEq, not_or]
    exact ⟨WfVals.no_credit_zero hvs, by intro h; apply hne; exact List.length_eq_zero_iff.mp h.symm⟩
theorem WfVals.no_credit_zero {U Δ : Finset Var} :
    ∀ {Γ : Ctx} {vs : List Val}, WfVals U Δ Γ vs → Res.credit 0 ∉ Γ
  | _, _, .nil => by simp
  | _, _, .cons Γ₁ Γ₂ v vs hv hvs => by
    simp only [Multiset.mem_add, not_or]
    exact ⟨WfVal.no_credit_zero hv, WfVals.no_credit_zero hvs⟩
end

/-! ## Locations of a substituted expression -/

theorem locs_subst {cfg : Cfg} {U Δ : Finset Var} {Γ : Ctx} {e : Expr} (h : Wf cfg U Δ Γ e)
    (hU : U = ∅) {ρ : Subst} {D : Var → Prop}
    (hΔ : ∀ x ∈ Δ, ∀ l, Var.loc l ∈ Val.fv (Val.subst ρ (.var x)) → D (.loc l))
    (hΓ : ∀ x, Res.var x ∈ Γ → ∀ l, Var.loc l ∈ Val.fv (Val.subst ρ (.var x)) → D (.loc l))
    (l : Nat) (hl : Var.loc l ∈ (e.subst ρ).fv) : D (.loc l) := by
  obtain ⟨x, hx, hl'⟩ := Expr.fv_subst ρ (.loc l) (by simp) e hl
  rcases Wf.fv_subset h x hx with h1 | h1 | h1
  · subst hU; simp at h1
  · exact hΔ x h1 l hl'
  · exact hΓ x h1 l hl'

end FIP
