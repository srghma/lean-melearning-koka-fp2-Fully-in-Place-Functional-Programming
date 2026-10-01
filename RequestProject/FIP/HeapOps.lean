module

public import RequestProject.FIP.HeapInv

@[expose] public section

/-!
# The heap operations preserve the invariant (Theorem 6)

`dup`, `drop` (with the cascade of `dcon`/`dlam` freeing whole subtrees, Lemma 62),
`dropru`, `free` and `alloc` preserve the invariant `HInv`, as does the allocation of a
new cell.
-/

namespace FIP.Lam

variable {sig : LSig} {funs : List FName} {H : Heap} {R : Multiset Var} {RC : Multiset Nat}
  {Γ Γ₀ : Ctx} {σ : Nat → Option LVal}

/-! ## Objects -/

theorem dfvList_of_isLoc {vs : List LVal} (h : ∀ v ∈ vs, v.IsLoc) :
    LVal.dfvList vs = LVal.fvList vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    obtain ⟨l, rfl⟩ := h v (by simp)
    simp [LVal.dfvList, LVal.fvList, LVal.dfv, LVal.fv, ih (fun w hw => h w (by simp [hw]))]

theorem fvList_locs (ls : List Nat) :
    LVal.fvList (ls.map fun l => LVal.var (.loc l)) = ls.map .loc := by
  induction ls with
  | nil => rfl
  | cons l ls ih => simp [LVal.fvList, LVal.fv, ih]

theorem isLoc_locs (ls : List Nat) : ∀ v ∈ ls.map (fun l => LVal.var (.loc l)), v.IsLoc := by
  intro v hv
  obtain ⟨l, -, rfl⟩ := List.mem_map.mp hv
  exact ⟨l, rfl⟩

/-- The atoms of an object. -/
def HObj.atoms : HObj → List LVal
  | .con _ args => args
  | .clo zs _ _ => zs

theorem HObj.fv_eq_atoms (o : HObj) : o.fv = LVal.fvList o.atoms := by
  cases o <;> rfl

theorem HObj.Ok.atoms_isLoc {o : HObj} (h : o.Ok funs) : ∀ v ∈ o.atoms, v.IsLoc := by
  cases o with
  | con c args => exact h
  | clo zs xs body =>
    obtain ⟨ls, rfl, -, -, -⟩ := h
    exact isLoc_locs ls

theorem HObj.Ok.dfv_sub {o : HObj} (h : o.Ok funs) : ∀ y ∈ o.toVal.dfv, y ∈ o.fv := by
  cases o with
  | con c args =>
    intro y hy
    simp only [HObj.toVal, LVal.dfv] at hy
    rw [dfvList_of_isLoc h] at hy
    exact hy
  | clo zs xs body =>
    obtain ⟨ls, rfl, hwf, -, -⟩ := h
    intro y hy
    simp only [HObj.toVal, LVal.dfv, List.mem_append, List.mem_filter,
      decide_eq_true_eq] at hy
    simp only [HObj.fv]
    rcases hy with hy | ⟨hy, hx⟩
    · rwa [dfvList_of_isLoc (isLoc_locs ls)] at hy
    · rw [fvList_locs]
      rcases LWf.dfv_sub hwf y hy with h' | h'
      · simp at h'
      · rcases Multiset.mem_add.mp h' with h' | h'
        · simpa [varCtx] using h'
        · exact absurd h' (not_mem_ctx hx)

theorem HObj.Ok.fv_loc {o : HObj} (h : o.Ok funs) : ∀ y ∈ o.fv, ∃ l, y = .loc l := by
  rw [HObj.fv_eq_atoms]; exact fvList_loc h.atoms_isLoc

theorem HObj.subst_congr {o : HObj} (h : o.Ok funs) {σ σ' : Nat → Option LVal}
    (hag : ∀ l, Var.loc l ∈ o.fv → σ l = σ' l) :
    o.toVal.subst (locS σ) = o.toVal.subst (locS σ') := by
  apply LVal.subst_congr
  intro y hy
  cases y with
  | name s => rfl
  | loc l => exact hag l (h.dfv_sub _ hy)

/-! ## Facts about the invariant -/

theorem Heap.Reads.defined {H : Heap} {σ : Nat → Option LVal} (h : H.Reads σ) {l n} {o : HObj}
    (hc : HCell.bind (.loc l) n o ∈ H) : ∃ v, σ l = some v ∧ v.dfv = [] :=
  ⟨_, h.cell l n o hc, h.closed l _ (h.cell l n o hc)⟩

theorem locS_closedLoc {σ : Nat → Option LVal} (h : ∀ l v, σ l = some v → v.dfv = []) :
    (locS σ).ClosedLoc :=
  ⟨fun _ => rfl, fun y v hy => by
    cases y with
    | name s => cases hy
    | loc l => exact h l v hy⟩

theorem locS_remove (σ : Nat → Option LVal) (xs : List Binder) : (locS σ).remove xs = locS σ := by
  funext y
  by_cases h : y ∈ Binder.vars xs
  · rw [LSubst.remove_of_mem h]
    simp only [Binder.vars, List.mem_map] at h
    obtain ⟨b, -, rfl⟩ := h
    rfl
  · rw [LSubst.remove_of_not_mem h]

namespace HInv

theorem _root_.FIP.Lam.Heap.mem_dom_of_cntM {x : Var} (hx : x ∈ H.cntM) :
    x ∈ H.dom := by
  obtain ⟨n, o, hc, -⟩ := Heap.mem_cntM.mp hx
  exact Heap.mem_dom.mpr ⟨n, o, hc⟩

theorem loc_of_cntM (h : HInv funs H R RC Γ σ) {x : Var} (hx : x ∈ H.cntM) :
    ∃ l n o, x = .loc l ∧ HCell.bind (.loc l) n o ∈ H := by
  obtain ⟨n, o, hc, -⟩ := Heap.mem_cntM.mp hx
  obtain ⟨⟨l, rfl⟩, -, -⟩ := h.cell_ok hc
  exact ⟨l, n, o, rfl, hc⟩

theorem defined (h : HInv funs H R RC Γ σ) {x : Var} (hx : x ∈ H.cntM) :
    ∃ l v, x = .loc l ∧ σ l = some v ∧ v.dfv = [] := by
  obtain ⟨l, n, o, rfl, hc⟩ := h.loc_of_cntM hx
  obtain ⟨v, hv, hv'⟩ := h.reads.defined hc
  exact ⟨l, v, rfl, hv, hv'⟩

theorem rngFv_cntM (h : HInv funs H R RC Γ σ) {x : Var} (hx : x ∈ H.rngFv) : x ∈ H.cntM := by
  rw [h.cnt]; exact Multiset.mem_add.mpr (.inr hx)

theorem vars_cntM (h : HInv funs H R RC Γ σ) {x : Var} (hx : x ∈ Ctx.vars Γ) : x ∈ H.cntM := by
  rw [h.cnt]; exact Multiset.mem_add.mpr (.inl (Multiset.mem_add.mpr (.inr hx)))

theorem R_cntM (h : HInv funs H R RC Γ σ) {x : Var} (hx : x ∈ R) : x ∈ H.cntM := by
  rw [h.cnt]; exact Multiset.mem_add.mpr (.inl (Multiset.mem_add.mpr (.inl hx)))

theorem obj_fv_cntM (h : HInv funs H R RC Γ σ) {x : Var} {n : Nat} {o : HObj}
    (hc : HCell.bind x n o ∈ H) {y : Var} (hy : y ∈ o.fv) : y ∈ H.cntM :=
  h.rngFv_cntM (Heap.mem_rngFv.mpr ⟨x, n, o, hc, hy⟩)

/-- The readback `σ` is closed on locations. -/
theorem closedLoc (h : HInv funs H R RC Γ σ) : (locS σ).ClosedLoc := locS_closedLoc h.reads.closed

/-- The objects of the heap are unchanged when reference counts change. -/
theorem of_sameObj {H' : Heap} {Γ' : Ctx} {R' : Multiset Var} {RC' : Multiset Nat}
    (h : HInv funs H R RC Γ σ)
    (hobj : ∀ x n o, HCell.bind x n o ∈ H' → ∃ m, HCell.bind x m o ∈ H)
    (hok : ∀ c ∈ H', c.Ok funs) (hdom : H'.dom.Nodup)
    (hcnt : H'.cntM = R' + Ctx.vars Γ' + H'.rngFv) (hcred : nz H'.creditsM = RC' + Ctx.cr Γ')
    (hctx : Ctx.LocOnly Γ') : HInv funs H' R' RC' Γ' σ :=
  ⟨hok, hdom, hcnt, hcred, hctx, h.reads.mono fun _ n o hc => hobj _ n o hc⟩

end HInv

/-! ## Allocating a cell -/

theorem exists_fresh (H : Heap) : ∃ l, Var.loc l ∉ H.dom := by
  classical
  let S : Finset Nat := (H.dom.toFinset).biUnion fun x => match x with
    | .loc l => {l}
    | .name _ => ∅
  obtain ⟨l, hl⟩ := Infinite.exists_notMem_finset S
  refine ⟨l, fun h => hl ?_⟩
  simp only [S, Finset.mem_biUnion, Multiset.mem_toFinset]
  exact ⟨_, h, by simp⟩

theorem HInv.addCell (h : HInv funs H R RC (Γ₀ + locCtx as) σ) {o : HObj} (ho : o.Ok funs)
    (has : o.fv = LVal.fvList as) {l : Nat} (hl : Var.loc l ∉ H.dom) :
    HInv funs ({HCell.bind (.loc l) 1 o} + H) R RC (Γ₀ + {Res.var (.loc l)})
      (Function.update σ l (some (o.toVal.subst (locS σ)))) := by
  have hfv : ∀ y ∈ o.fv, y ∈ H.cntM := by
    intro y hy
    apply h.vars_cntM
    rw [Ctx.vars_add, locCtx_vars, ← has]
    exact Multiset.mem_add.mpr (.inr (by simpa using hy))
  have hfvl : ∀ m, Var.loc m ∈ o.fv → m ≠ l := by
    rintro m hm rfl
    exact hl (Heap.mem_dom_of_cntM (hfv _ hm))
  have hag : ∀ m, Var.loc m ∈ o.fv →
      σ m = Function.update σ l (some (o.toVal.subst (locS σ))) m := by
    intro m hm; rw [Function.update_of_ne (hfvl m hm)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩⟩
  · intro c hc
    rcases Multiset.mem_add.mp hc with hc | hc
    · rw [Multiset.mem_singleton] at hc; subst hc; exact ⟨⟨l, rfl⟩, le_refl _, ho⟩
    · exact h.ok c hc
  · rw [Heap.dom_add, Heap.dom_bind, Multiset.singleton_add, Multiset.nodup_cons]
    exact ⟨hl, h.nodup⟩
  · rw [Heap.cntM_add, Heap.cntM_bind, h.cnt, Heap.rngFv_add, Heap.rngFv_bind, has,
      Ctx.vars_add, Ctx.vars_add, locCtx_vars, Ctx.vars_var, Multiset.replicate_one]
    abel
  · rw [Heap.creditsM_add, Heap.creditsM_bind, zero_add, h.cred, Ctx.cr_add, Ctx.cr_add,
      locCtx_cr, Ctx.cr_var]
  · exact h.ctx.left.add (by intro r hr; simp at hr; exact .inl ⟨l, hr⟩)
  · intro m v hm
    by_cases hml : m = l
    · subst hml
      rw [Function.update_self, Option.some.injEq] at hm
      subst hm
      apply LVal.dfv_subst_closed
      intro z hz
      obtain ⟨m', w, rfl, hw, hw'⟩ := h.defined (hfv z (ho.dfv_sub z hz))
      exact ⟨w, hw, hw'⟩
    · rw [Function.update_of_ne hml] at hm
      exact h.reads.closed m v hm
  · intro m n p hc
    rcases Multiset.mem_add.mp hc with hc1 | hc1
    · rw [Multiset.mem_singleton, HCell.bind.injEq, Var.loc.injEq] at hc1
      obtain ⟨rfl, -, rfl⟩ := hc1
      rw [Function.update_self]
      congr 1
      exact HObj.subst_congr ho hag
    · have hml : m ≠ l := by
        intro hml; subst hml; exact hl (Heap.mem_dom.mpr ⟨n, p, hc1⟩)
      rw [Function.update_of_ne hml, h.reads.cell m n p hc1]
      congr 1
      apply HObj.subst_congr (h.cell_ok hc1).2.2
      intro m' hm'
      have hm'l : m' ≠ l := by
        intro hm'l; subst hm'l; exact hl (Heap.mem_dom_of_cntM (h.obj_fv_cntM hc1 hm'))
      rw [Function.update_of_ne hm'l]

/-! ## Reuse credits -/

theorem HInv.takeCredit (h : HInv funs H R RC (Γ₀ + {Res.credit k}) σ) (hk : 1 ≤ k) :
    ∃ H₀, H = {HCell.credit k} + H₀ ∧ HInv funs H₀ R RC Γ₀ σ := by
  have hmem : HCell.credit k ∈ H := by
    rw [← Heap.mem_creditsM]
    have : k ∈ nz H.creditsM := by
      rw [h.cred, Ctx.cr_add, Ctx.cr_credit]
      simp [nz]; omega
    exact Multiset.mem_of_mem_filter this
  obtain ⟨H₀, rfl⟩ := Heap.eq_add_of_mem hmem
  refine ⟨H₀, rfl, ⟨fun c hc => h.ok c (Multiset.mem_add.mpr (.inr hc)), ?_, ?_, ?_,
    h.ctx.left, h.reads.mono fun l n o hc => ⟨n, Multiset.mem_add.mpr (.inr hc)⟩⟩⟩
  · have := h.nodup; rwa [Heap.dom_add, Heap.dom_credit, zero_add] at this
  · have := h.cnt
    rwa [Heap.cntM_add, Heap.cntM_credit, zero_add, Heap.rngFv_add, Heap.rngFv_credit, zero_add,
      Ctx.vars_add, Ctx.vars_credit, add_zero] at this
  · have := h.cred
    rw [Heap.creditsM_add, Heap.creditsM_credit, nz_add, Ctx.cr_add, Ctx.cr_credit] at this
    rw [add_comm, ← add_assoc] at this
    exact add_right_cancel this

theorem HInv.putCredit (h : HInv funs H R RC Γ σ) (k : Nat) :
    HInv funs ({HCell.credit k} + H) R RC (Γ + {Res.credit k}) σ := by
  refine ⟨fun c hc => ?_, ?_, ?_, ?_, h.ctx.add (Ctx.LocOnly.credit k),
    h.reads.mono fun l n o hc => ?_⟩
  · rcases Multiset.mem_add.mp hc with hc | hc
    · rw [Multiset.mem_singleton] at hc; subst hc; trivial
    · exact h.ok c hc
  · rw [Heap.dom_add, Heap.dom_credit, zero_add]; exact h.nodup
  · rw [Heap.cntM_add, Heap.cntM_credit, zero_add, Heap.rngFv_add, Heap.rngFv_credit, zero_add,
      Ctx.vars_add, Ctx.vars_credit, add_zero]; exact h.cnt
  · rw [Heap.creditsM_add, Heap.creditsM_credit, nz_add, h.cred, Ctx.cr_add, Ctx.cr_credit]
    abel
  · rcases Multiset.mem_add.mp hc with hc | hc
    · simp at hc
    · exact ⟨n, hc⟩

/-! ## `dup` -/

theorem HInv.dup (h : HInv funs H R RC Γ σ) {x : Var} (hx : x ∈ H.cntM) (e : LExpr) :
    ∃ H', HSteps sig H (.dup (.var x) e) H' e ∧ HInv funs H' R RC (Γ + {Res.var x}) σ ∧
      (∀ y n o, HCell.bind y n o ∈ H → ∃ m, HCell.bind y m o ∈ H') ∧ H'.dom = H.dom ∧
      H'.cntM = H.cntM + {x} := by
  obtain ⟨n, o, hc, hn⟩ := Heap.mem_cntM.mp hx
  obtain ⟨H₀, rfl⟩ := Heap.eq_add_of_mem hc
  refine ⟨{HCell.bind x (n + 1) o} + H₀, HSteps.head (.dup H₀ x n o e), ?_, ?_, by simp, ?_⟩
  · refine h.of_sameObj (fun y m p hm => ?_) (fun c hc' => ?_) (by simpa using h.nodup) ?_ ?_ ?_
    · rcases Multiset.mem_add.mp hm with hm | hm
      · rw [Multiset.mem_singleton, HCell.bind.injEq] at hm
        obtain ⟨rfl, -, rfl⟩ := hm
        exact ⟨n, by simp⟩
      · exact ⟨m, Multiset.mem_add.mpr (.inr hm)⟩
    · rcases Multiset.mem_add.mp hc' with hc' | hc'
      · rw [Multiset.mem_singleton] at hc'; subst hc'
        obtain ⟨hl, -, ho⟩ := h.cell_ok hc
        exact ⟨hl, by omega, ho⟩
      · exact h.ok c (Multiset.mem_add.mpr (.inr hc'))
    · have := h.cnt
      simp only [Heap.cntM_add, Heap.cntM_bind, Heap.rngFv_add, Heap.rngFv_bind,
        Ctx.vars_add, Ctx.vars_var] at this ⊢
      rw [Multiset.replicate_succ, ← Multiset.singleton_add, add_assoc, this]
      abel
    · have := h.cred
      simpa [Ctx.cr_add] using this
    · refine h.ctx.add ?_
      obtain ⟨⟨l, rfl⟩, -, -⟩ := h.cell_ok hc
      intro r hr; simp at hr; exact .inl ⟨l, hr⟩
  · intro y m p hm
    rcases Multiset.mem_add.mp hm with hm | hm
    · rw [Multiset.mem_singleton, HCell.bind.injEq] at hm
      obtain ⟨rfl, rfl, rfl⟩ := hm
      exact ⟨_, Multiset.mem_add.mpr (.inl (Multiset.mem_singleton_self _))⟩
    · exact ⟨m, Multiset.mem_add.mpr (.inr hm)⟩
  · simp only [Heap.cntM_add, Heap.cntM_bind]
    rw [Multiset.replicate_succ, ← Multiset.singleton_add]
    abel

theorem HInv.dups : ∀ {H : Heap} {Γ : Ctx}, HInv funs H R RC Γ σ →
    ∀ (zs : List LVal), (∀ z ∈ zs, z.IsLoc) → (∀ y ∈ LVal.fvList zs, y ∈ H.cntM) →
    ∀ (e : LExpr), ∃ H', HSteps sig H (FIP.Lam.dups zs e) H' e ∧
      HInv funs H' R RC (Γ + locCtx zs) σ ∧
      (∀ y n o, HCell.bind y n o ∈ H → ∃ m, HCell.bind y m o ∈ H') ∧ H'.dom = H.dom
  | H, Γ, h, [], _, _, e => ⟨H, .refl _ _, by simpa [locCtx, LVal.fvList] using h,
      fun y n o hc => ⟨n, hc⟩, rfl⟩
  | H, Γ, h, z :: zs, hz, hm, e => by
    obtain ⟨l, rfl⟩ := hz z (by simp)
    have hx : Var.loc l ∈ H.cntM := hm _ (by simp [LVal.fvList, LVal.fv])
    obtain ⟨H₁, hs1, h1, hobj1, hdom1, hcnt1⟩ := h.dup (sig := sig) hx (FIP.Lam.dups zs e)
    have hm' : ∀ y ∈ LVal.fvList zs, y ∈ H₁.cntM := by
      intro y hy
      rw [hcnt1]
      exact Multiset.mem_add.mpr (.inl (hm y (by simp [LVal.fvList, hy])))
    obtain ⟨H₂, hs2, h2, hobj2, hdom2⟩ :=
      HInv.dups h1 zs (fun w hw => hz w (by simp [hw])) hm' e
    refine ⟨H₂, hs1.trans hs2, ?_, ?_, by rw [hdom2, hdom1]⟩
    · rw [locCtx_cons, ← add_assoc]; exact h2
    · intro y n o hc
      obtain ⟨m, hm1⟩ := hobj1 y n o hc
      exact hobj2 y m o hm1

/-! ## `drop` and `dropru` -/

theorem HInv.removeCell {H₀ : Heap} {x : Var} {o : HObj}
    (h : HInv funs ({HCell.bind x 1 o} + H₀) R RC (Γ₀ + {Res.var x}) σ) :
    HInv funs H₀ R RC (Γ₀ + locCtx o.atoms) σ := by
  have hc : HCell.bind x 1 o ∈ ({HCell.bind x 1 o} + H₀ : Heap) := by simp
  have ho := (h.cell_ok hc).2.2
  refine ⟨fun c hc' => h.ok c (Multiset.mem_add.mpr (.inr hc')), ?_, ?_, ?_, ?_,
    h.reads.mono fun l n o hc' => ⟨n, Multiset.mem_add.mpr (.inr hc')⟩⟩
  · have := h.nodup
    rw [Heap.dom_add, Heap.dom_bind, Multiset.singleton_add, Multiset.nodup_cons] at this
    exact this.2
  · have := h.cnt
    rw [Heap.cntM_add, Heap.cntM_bind, Multiset.replicate_one, Heap.rngFv_add, Heap.rngFv_bind,
      Ctx.vars_add, Ctx.vars_var, HObj.fv_eq_atoms] at this
    rw [Ctx.vars_add, locCtx_vars]
    have : {x} + H₀.cntM = {x} + (R + (Ctx.vars Γ₀ + ↑(LVal.fvList o.atoms)) + H₀.rngFv) := by
      rw [this]; abel
    exact add_left_cancel this
  · have := h.cred
    rw [Heap.creditsM_add, Heap.creditsM_bind, zero_add, Ctx.cr_add, Ctx.cr_var, add_zero] at this
    rw [this, Ctx.cr_add, locCtx_cr, add_zero]
  · exact h.ctx.left.add (locCtx_locOnly ho.atoms_isLoc)

theorem HInv.decCell {H₀ : Heap} {x : Var} {m : Nat} {o : HObj}
    (h : HInv funs ({HCell.bind x (m + 2) o} + H₀) R RC (Γ₀ + {Res.var x}) σ) :
    HInv funs ({HCell.bind x (m + 1) o} + H₀) R RC Γ₀ σ := by
  have hc : HCell.bind x (m + 2) o ∈ ({HCell.bind x (m + 2) o} + H₀ : Heap) := by simp
  refine ⟨fun c hc' => ?_, ?_, ?_, ?_, h.ctx.left, h.reads.mono fun l n p hc' => ?_⟩
  · rcases Multiset.mem_add.mp hc' with hc' | hc'
    · rw [Multiset.mem_singleton] at hc'; subst hc'
      obtain ⟨hl, -, ho⟩ := h.cell_ok hc
      exact ⟨hl, by omega, ho⟩
    · exact h.ok c (Multiset.mem_add.mpr (.inr hc'))
  · have := h.nodup
    rw [Heap.dom_add, Heap.dom_bind] at this ⊢; exact this
  · have := h.cnt
    rw [Heap.cntM_add, Heap.cntM_bind, Heap.rngFv_add, Heap.rngFv_bind, Ctx.vars_add,
      Ctx.vars_var, Multiset.replicate_succ, ← Multiset.singleton_add] at this
    rw [Heap.cntM_add, Heap.cntM_bind, Heap.rngFv_add, Heap.rngFv_bind]
    have : {x} + (Multiset.replicate (m + 1) x + H₀.cntM) =
        {x} + (R + Ctx.vars Γ₀ + (↑o.fv + H₀.rngFv)) := by
      rw [← add_assoc, this]; abel
    exact add_left_cancel this
  · have := h.cred
    rw [Heap.creditsM_add, Heap.creditsM_bind, Ctx.cr_add, Ctx.cr_var, add_zero] at this
    rw [Heap.creditsM_add, Heap.creditsM_bind]; exact this
  · rcases Multiset.mem_add.mp hc' with hc' | hc'
    · rw [Multiset.mem_singleton, HCell.bind.injEq] at hc'
      obtain ⟨rfl, -, rfl⟩ := hc'
      exact ⟨m + 2, hc⟩
    · exact ⟨n, Multiset.mem_add.mpr (.inr hc')⟩

theorem HInv.cell_of_var (h : HInv funs H R RC (Γ₀ + {Res.var x}) σ) :
    ∃ n o H₀, H = {HCell.bind x n o} + H₀ ∧ 1 ≤ n := by
  obtain ⟨n, o, hc, -⟩ := Heap.mem_cntM.mp (h.vars_cntM (x := x) (by simp [Ctx.vars_add]))
  obtain ⟨H₀, rfl⟩ := Heap.eq_add_of_mem hc
  exact ⟨n, o, H₀, rfl, (h.cell_ok hc).2.1⟩

/-- One `drop` step: decrement the reference count, or free the cell and drop its
    children. -/
theorem HInv.drop1 (h : HInv funs H R RC (Γ₀ + {Res.var x}) σ) (e : LExpr) :
    (∃ H', HHead sig H (.drop (.var x) e) H' e ∧ HInv funs H' R RC Γ₀ σ ∧
      Multiset.card H' = Multiset.card H) ∨
    (∃ H' fs, HHead sig H (.drop (.var x) e) H' (drops fs e) ∧ (∀ f ∈ fs, f.IsLoc) ∧
      HInv funs H' R RC (Γ₀ + locCtx fs) σ ∧ Multiset.card H' < Multiset.card H) := by
  obtain ⟨n, o, H₀, rfl, hn⟩ := h.cell_of_var
  have hc : HCell.bind x n o ∈ ({HCell.bind x n o} + H₀ : Heap) := by simp
  have ho := (h.cell_ok hc).2.2
  match n, hn, h, hc with
  | 1, _, h, hc =>
    refine .inr ⟨H₀, o.atoms, ?_, ho.atoms_isLoc, h.removeCell, by simp⟩
    cases o with
    | con c fs => exact .dcon H₀ x c fs e
    | clo zs xs b => exact .dlam H₀ x zs xs b e
  | m + 2, _, h, hc =>
    exact .inl ⟨_, .drop H₀ x m o e, h.decCell, by simp⟩

theorem drops_append (fs gs : List LVal) (e : LExpr) :
    drops (fs ++ gs) e = drops fs (drops gs e) := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    cases f with
    | var x => simp [drops, ih]
    | _ => simp [drops, ih]

/-- **Lemma 62** (dropping a tree): `drop`ping owned locations frees exactly the cells that
    are no longer referenced. -/
theorem HInv.drops : ∀ (c : Nat) (fs : List LVal) {H : Heap} {Γ₀ : Ctx},
    Multiset.card H ≤ c → (∀ f ∈ fs, f.IsLoc) → HInv funs H R RC (Γ₀ + locCtx fs) σ →
    ∀ e, ∃ H', HSteps sig H (FIP.Lam.drops fs e) H' e ∧ HInv funs H' R RC Γ₀ σ := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c IH =>
  intro fs
  induction fs with
  | nil =>
    intro H Γ₀ _ _ h e
    exact ⟨H, .refl _ _, by simpa [locCtx, LVal.fvList] using h⟩
  | cons f rest ihf =>
    intro H Γ₀ hcard hf h e
    obtain ⟨l, rfl⟩ := hf f (by simp)
    have h' : HInv funs H R RC (Γ₀ + locCtx rest + {Res.var (.loc l)}) σ := by
      rw [locCtx_cons] at h
      have : Γ₀ + ({Res.var (.loc l)} + locCtx rest) = Γ₀ + locCtx rest + {Res.var (.loc l)} := by
        abel
      rwa [this] at h
    have hfr : ∀ g ∈ rest, g.IsLoc := fun g hg => hf g (by simp [hg])
    show ∃ H', HSteps sig H (.drop (.var (.loc l)) (FIP.Lam.drops rest e)) H' e ∧ _
    rcases h'.drop1 (sig := sig) (FIP.Lam.drops rest e) with
      ⟨H₁, hs, h1, hc1⟩ | ⟨H₁, gs, hs, hgs, h1, hc1⟩
    · obtain ⟨H₂, hs2, h2⟩ := ihf (by omega) hfr h1 e
      exact ⟨H₂, (HSteps.head hs).trans hs2, h2⟩
    · have h1' : HInv funs H₁ R RC (Γ₀ + locCtx (gs ++ rest)) σ := by
        rw [locCtx_append]
        have : Γ₀ + locCtx rest + locCtx gs = Γ₀ + (locCtx gs + locCtx rest) := by abel
        rwa [this] at h1
      obtain ⟨H₂, hs2, h2⟩ := IH (Multiset.card H₁) (by omega) (gs ++ rest) (le_refl _)
        (fun g hg => by
          rcases List.mem_append.mp hg with hg | hg
          · exact hgs g hg
          · exact hfr g hg) h1' e
      rw [drops_append] at hs2
      exact ⟨H₂, (HSteps.head hs).trans hs2, h2⟩

theorem HInv.drop (h : HInv funs H R RC (Γ₀ + {Res.var x}) σ) (hx : ∃ l, x = .loc l)
    (e : LExpr) :
    ∃ H', HSteps sig H (.drop (.var x) e) H' e ∧ HInv funs H' R RC Γ₀ σ := by
  obtain ⟨l, rfl⟩ := hx
  have h' : HInv funs H R RC (Γ₀ + locCtx [.var (.loc l)]) σ := by
    simpa [locCtx, LVal.fvList, LVal.fv] using h
  have := HInv.drops (sig := sig) _ [.var (.loc l)] (le_refl _)
    (fun f hf => by simp at hf; exact ⟨l, hf⟩) h' e
  simpa [FIP.Lam.drops] using this

/-- `dropru x` on a constructor cell of size `k`: decrement the reference count and
    allocate a reuse credit, or turn the unique cell into a reuse credit and drop its
    children. -/
theorem HInv.dropru (h : HInv funs H R RC (Γ₀ + {Res.var x}) σ) {n : Nat} {c : CName}
    {fs : List LVal} (hc : HCell.bind x n (.con c fs) ∈ H) (e : LExpr) :
    ∃ H', HSteps sig H (.dropru (.var x) fs.length e) H' e ∧
      HInv funs H' R RC (Γ₀ + {Res.credit fs.length}) σ := by
  obtain ⟨n', o, H₀, rfl, hn⟩ := h.cell_of_var
  have hc' : HCell.bind x n' o ∈ ({HCell.bind x n' o} + H₀ : Heap) := by simp
  obtain ⟨rfl, rfl⟩ := h.cell_unique hc hc'
  match n, hn, h, hc with
  | 1, _, h, hc =>
    have h1 := h.removeCell.putCredit fs.length
    have h1' : HInv funs ({HCell.credit fs.length} + H₀) R RC
        (Γ₀ + {Res.credit fs.length} + locCtx fs) σ := by
      have : Γ₀ + locCtx (HObj.con c fs).atoms + {Res.credit fs.length} =
          Γ₀ + {Res.credit fs.length} + locCtx fs := by simp [HObj.atoms]; abel
      rw [this] at h1
      rwa [add_comm] at h1 ⊢
    have hfs : ∀ f ∈ fs, f.IsLoc := (h.cell_ok hc).2.2
    obtain ⟨H₂, hs2, h2⟩ := HInv.drops (sig := sig) _ fs (le_refl _) hfs h1' e
    exact ⟨H₂, (HSteps.head (.dconru H₀ x c fs e)).trans hs2, h2⟩
  | m + 2, _, h, hc =>
    have h1 := h.decCell.putCredit fs.length
    refine ⟨_, HSteps.head (.dropru H₀ x m c fs e), ?_⟩
    have : ({HCell.bind x (m + 1) (.con c fs)} + {HCell.credit fs.length} + H₀ : Heap) =
        {HCell.credit fs.length} + ({HCell.bind x (m + 1) (.con c fs)} + H₀) := by abel
    rw [this]; exact h1

end FIP.Lam
