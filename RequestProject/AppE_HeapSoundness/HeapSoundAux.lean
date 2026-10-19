module

public import RequestProject.AppE_HeapSoundness.HeapAlloc

@[expose] public section

/-!
# The statement of the main lemma of Theorem 6, and its bookkeeping

The proof of Theorem 6 (`HeapSound.lean`) is a big-step simulation: if the functional
semantics evaluates an expression to a value in `n` steps, then the heap semantics evaluates
it to locations denoting that value.  An expression `e : LExpr m` of a scope `m` is run with
its variables replaced by locations (`ρ : Fin m → Nat`); the functional semantics runs the
same expression with the locations replaced by the closed values `σ = [H]` they denote.

* `SzOk sz ρ σ`: the sizes recorded in the size environment are those of the constructors
  the variables denote;
* `HeapResult`: the conclusion — the heap semantics reaches a tuple of locations, which are
  the new roots beside the frame `R`, denoting the values of the functional run;
* `ExprClaim` / `MainClaim`: the main lemma for `n` functional steps.
-/

namespace FIP.Lam

variable {sig : LSig}

/-- The sizes of `sz` are those of the constructors denoted by the variables. -/
def SzOk {m : Nat} (sz : Fin m → Option Nat) (ρ : Fin m → Nat) (σ : Nat → Option (LVal 0)) :
    Prop :=
  ∀ i k, sz i = some k → ∃ (c : CName) (ws : LVals 0), σ (ρ i) = some (.ctor c ws) ∧ ws.length = k

/-- The conclusion of the main lemma: `H | e` evaluates in the heap semantics to a tuple of
    locations `xs`, which are the new roots beside the frame `R`, and which denote the
    values `vs`. -/
def HeapResult (sig : LSig) (H : Heap) (e : LExpr 0) (R : Ctx 0) (σ : Nat → Option (LVal 0))
    (vs : LVals 0) : Prop :=
  ∃ (H' : Heap) (xs : List Nat) (σ' : Nat → Option (LVal 0)),
    HSteps sig H e H' (.ret (LVals.ofList (xs.map locV))) ∧ HInv sig.funs H' σ' ∧
      SubstExt σ σ' ∧ H'.roots = locsCtx xs + R ∧
      xs.map (fun l => (locV l).substLoc σ') = vs.toList

/-- The main lemma for an expression and at most `n` functional steps. -/
def ExprClaim (sig : LSig) (n : Nat) {m : Nat} (Δ : Finset (Var m)) (Γ : Ctx m) (e : LExpr m) :
    Prop :=
  ∀ n', n' ≤ n → ∀ (sz : Fin m → Option Nat), e.Adm sz →
    ∀ (ρ : Fin m → Nat) (H : Heap) (R : Ctx 0) (σ : Nat → Option (LVal 0)) (vs : LVals 0),
      SzOk sz ρ σ → HInv sig.funs H σ → (∀ y ∈ Δ, Res.var (y.ren ρ) ∈ R) →
      H.roots = nzCtx (Ctx.ren ρ Γ) + R →
      LStepsN sig n' ((e.subst (LSubst.locs ρ)).substLoc σ) (.ret vs) →
      HeapResult sig H (e.subst (LSubst.locs ρ)) R σ vs

/-- The main lemma for `n` functional steps. -/
def MainClaim (sig : LSig) (n : Nat) : Prop :=
  ∀ {m : Nat} {Δ : Finset (Var m)} {Γ : Ctx m} {e : LExpr m}, LWf sig.funs Δ Γ e →
    ExprClaim sig n Δ Γ e

/-! ## Bookkeeping -/

theorem SzOk.mono {m : Nat} {sz : Fin m → Option Nat} {ρ : Fin m → Nat}
    {σ σ' : Nat → Option (LVal 0)} (h : SzOk sz ρ σ) (he : SubstExt σ σ') : SzOk sz ρ σ' := by
  intro i k hi
  obtain ⟨c, ws, h1, h2⟩ := h i k hi
  exact ⟨c, ws, he _ _ h1, h2⟩

theorem SzOk.none {m : Nat} (ρ : Fin m → Nat) (σ : Nat → Option (LVal 0)) :
    SzOk (fun _ => none) ρ σ := by
  intro i k hi; simp at hi

theorem HeapResult.prepend {H H₁ : Heap} {e e₁ : LExpr 0} {R : Ctx 0}
    {σ σ₁ : Nat → Option (LVal 0)} {vs : LVals 0} (hs : HSteps sig H e H₁ e₁)
    (he : SubstExt σ σ₁) (h : HeapResult sig H₁ e₁ R σ₁ vs) : HeapResult sig H e R σ vs := by
  obtain ⟨H', xs, σ', h1, h2, h3, h4, h5⟩ := h
  exact ⟨H', xs, σ', hs.trans h1, h2, he.trans h3, h4, h5⟩

theorem nzCtx_le (Γ : Ctx 0) : nzCtx Γ ≤ Γ := Multiset.filter_le _ _

theorem mem_nzCtx_var {Γ : Ctx 0} {x : Var 0} (h : Res.var x ∈ Γ) : Res.var x ∈ nzCtx Γ := by
  simp only [nzCtx, Multiset.mem_filter]; exact ⟨h, by simp⟩

theorem mem_ren_var {m : Nat} {ρ : Fin m → Nat} {Γ : Ctx m} {x : Var m}
    (h : Res.var x ∈ Γ) : Res.var (x.ren ρ) ∈ Ctx.ren ρ Γ :=
  Multiset.mem_map.mpr ⟨_, h, rfl⟩

/-- A variable available to an expression (borrowed or owned) is a root of the heap. -/
theorem alive_var {m : Nat} {Δ : Finset (Var m)} {Γ : Ctx m} {ρ : Fin m → Nat} {H : Heap}
    {R : Ctx 0} (hΔ : ∀ y ∈ Δ, Res.var (y.ren ρ) ∈ R) (hR : H.roots = nzCtx (Ctx.ren ρ Γ) + R)
    {x : Var m} (hx : x ∈ Δ ∨ Res.var x ∈ Γ) : Res.var (x.ren ρ) ∈ H.roots := by
  rw [hR, Multiset.mem_add]
  rcases hx with hx | hx
  · exact .inr (hΔ x hx)
  · exact .inl (mem_nzCtx_var (mem_ren_var hx))

/-- The locations of a well-formed expression are bound in the heap. -/
theorem locs_defined {funs : List FName} {m : Nat} {Δ : Finset (Var m)} {Γ : Ctx m}
    {e : LExpr m} (hwf : LWf funs Δ Γ e) {ρ : Fin m → Nat} {H : Heap} {R : Ctx 0}
    {σ : Nat → Option (LVal 0)} (hH : HInv funs H σ) (hΔ : ∀ y ∈ Δ, Res.var (y.ren ρ) ∈ R)
    (hR : H.roots = nzCtx (Ctx.ren ρ Γ) + R) :
    ∀ l ∈ (e.subst (LSubst.locs ρ)).locs, ∃ v, σ l = some v := by
  intro l hl
  obtain ⟨x, hx, hxl⟩ := hwf.locs_ren ρ hl
  have := alive_var hΔ hR hx
  rw [hxl] at this
  exact hH.some_of_root this

theorem substLoc_ext {n : Nat} {e : LExpr n} {σ σ' : Nat → Option (LVal 0)}
    (h : ∀ l ∈ e.locs, ∃ v, σ l = some v) (he : SubstExt σ σ') : e.substLoc σ = e.substLoc σ' := by
  apply LExpr.substLoc_congr
  intro l hl
  obtain ⟨v, hv⟩ := h l hl
  rw [hv, he _ _ hv]

theorem substLoc_ext_val {n : Nat} {v : LVal n} {σ σ' : Nat → Option (LVal 0)}
    (h : ∀ l ∈ v.locs, ∃ w, σ l = some w) (he : SubstExt σ σ') : v.substLoc σ = v.substLoc σ' := by
  apply LVal.substLoc_congr
  intro l hl
  obtain ⟨w, hw⟩ := h l hl
  rw [hw, he _ _ hw]

theorem LExpr.inst0_substLoc {k : Nat} (σ : Nat → Option (LVal 0)) (e : LExpr (0 + k))
    (ls : List (LVal 0)) : (e.inst0 ls).substLoc σ = (e.substLoc σ).inst0 (ls.map (LVal.substLoc σ)) := by
  unfold LExpr.inst0
  rw [LExpr.substLoc_subst]
  apply LExpr.subst_congr
  intro i
  rw [LSubst.inst_substLoc]
  congr 1
  funext j; exact j.elim0

theorem LVal.subst_locs_var' {m : Nat} (ρ : Fin m → Nat) (x : Var m) :
    (LVal.var x).subst (LSubst.locs ρ) = locV (x.ren ρ).toLoc := by
  rw [LVal.subst_locs_var]; simp

/-- Substituting locations into an expression without locations, then values for them. -/
theorem LExpr.subst_locs_substLoc {n : Nat} {e : LExpr n} (he : e.locs = []) (ρ : Fin n → Nat)
    (σ : Nat → Option (LVal 0)) :
    (e.subst (LSubst.locs ρ)).substLoc σ = e.subst (fun i => (locV (ρ i)).substLoc σ) := by
  rw [LExpr.substLoc_subst, LExpr.substLoc_of_locs_nil σ he]; rfl

theorem instN_ofListN {k c : Nat} (xs zs : List Nat) (hl : xs.length = k) (i : Fin (c + k)) :
    instN k xs (ofListN c zs) i = ofListN (c + k) (xs ++ zs) i := by
  simp only [instN, ofListN]
  split
  · rename_i h
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by omega)]
  · rename_i h
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by omega), hl]

theorem inst_ofList_locs {k c : Nat} (xs zs : List Nat) (hk : xs.length = k)
    (hc : zs.length = c) (i : Fin (c + k)) :
    LSubst.inst k (xs.map locV) (LSubst.ofList c (zs.map locV)) i =
      LSubst.locs (instN k xs (ofListN c zs)) i := by
  simp only [LSubst.inst, LSubst.ofList, LSubst.locs, instN, ofListN]
  split
  · rename_i h
    rw [List.getD_eq_getElem _ _ (by simpa [hk] using h), List.getD_eq_getElem _ _ (by omega)]
    simp
  · rename_i h
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ (by omega)]
    simp

theorem Ctx.ren_allCtx_inst {k c : Nat} (xs zs : List Nat) (hk : xs.length = k)
    (hc : zs.length = c) :
    Ctx.ren (instN k xs (ofListN c zs)) (allCtx (c + k)) = locsCtx xs + locsCtx zs := by
  have : instN k xs (ofListN c zs) = ofListN (c + k) (xs ++ zs) :=
    funext (instN_ofListN xs zs hk)
  rw [this, Ctx.ren_allCtx _ _ (by simp; omega), locsCtx_append]

/-- The borrowed variables under a binder. -/
theorem delta_shift {m k : Nat} {Δ : Finset (Var m)} {ρ : Fin m → Nat} {R : Ctx 0}
    (xs : List Nat) (hΔ : ∀ y ∈ Δ, Res.var (y.ren ρ) ∈ R) :
    ∀ y ∈ Vars.shift k Δ, Res.var (y.ren (instN k xs ρ)) ∈ R := by
  intro y hy
  simp only [Vars.shift, Finset.mem_map] at hy
  obtain ⟨y, hy, rfl⟩ := hy
  simp only [Var.shiftEmb, Function.Embedding.coeFn_mk]
  rw [Var.ren_shift]; exact hΔ y hy

theorem SzOk.up {m k : Nat} {sz : Fin m → Option Nat} {ρ : Fin m → Nat}
    {σ : Nat → Option (LVal 0)} (h : SzOk sz ρ σ) (xs : List Nat) :
    SzOk (SzEnv.up k sz) (instN k xs ρ) σ := by
  intro i j hi
  simp only [SzEnv.up] at hi
  split at hi
  · simp at hi
  · rename_i hlt
    obtain ⟨c, ws, h1, h2⟩ := h _ _ hi
    refine ⟨c, ws, ?_, h2⟩
    simp only [instN, hlt, dite_false]; exact h1

/-- The roots of a binder's environment. -/
theorem roots_binder {m k : Nat} (ρ : Fin m → Nat) (xs : List Nat) (hl : xs.length = k)
    (Γ : Ctx m) :
    nzCtx (Ctx.ren (instN k xs ρ) (Ctx.shift k Γ + bCtx m k)) =
      nzCtx (Ctx.ren ρ Γ) + locsCtx xs := by
  rw [Ctx.ren_add, Ctx.ren_shift, Ctx.ren_bCtx _ _ _ hl, nzCtx_add, nzCtx_locsCtx]

/-- The branch of the functional match. -/
def LBranch.substLoc (σ : Nat → Option (LVal 0)) {n : Nat} (b : LBranch n) : LBranch n :=
  ⟨b.ctor, b.k, b.body.substLoc σ⟩

theorem LBranches.toList_substLoc {n : Nat} (σ : Nat → Option (LVal 0)) :
    ∀ bs : LBranches n, (bs.substLoc σ).toList = bs.toList.map (LBranch.substLoc σ)
  | .nil => rfl
  | .cons c k e bs => by
    simp [LBranches.substLoc, LBranches.toList_substLoc σ bs, LBranch.substLoc]

theorem LBranches.find_substLoc {n : Nat} (σ : Nat → Option (LVal 0)) (bs : LBranches n)
    (c : CName) (k : Nat) :
    (bs.substLoc σ).find c k = (bs.find c k).map (LBranch.substLoc σ) := by
  simp only [LBranches.find, LBranches.toList_substLoc, List.find?_map]
  rfl

theorem LExpr.substLoc_dups {n : Nat} (σ : Nat → Option (LVal 0)) :
    ∀ (vs : List (LVal n)) (e : LExpr n),
      (dups vs e).substLoc σ = dups (vs.map (LVal.substLoc σ)) (e.substLoc σ)
  | [], e => rfl
  | v :: vs, e => by
    simp only [dups, LExpr.substLoc, List.map_cons]; rw [LExpr.substLoc_dups σ vs e]

/-- The value denoted by a bound location. -/
theorem HInv.locV_substLoc {funs : List FName} {H : Heap} {σ : Nat → Option (LVal 0)}
    (h : HInv funs H σ) {l n : Nat} {o : HObj} (hc : HCell.bind (.loc l) n o ∈ H) :
    (locV l).substLoc σ = o.toVal σ := by
  simp [h.reads l n o hc]

/-- The fields of a cell are bound. -/
theorem HInv.fields_dom {funs : List FName} {H : Heap} {σ : Nat → Option (LVal 0)}
    (h : HInv funs H σ) {x : Var 0} {n : Nat} {o : HObj} (hc : HCell.bind x n o ∈ H) :
    ∃ ls : List Nat, o.fields = ls.map locV ∧ ∀ l ∈ ls, Var.loc l ∈ H.dom := by
  obtain ⟨ls, hls⟩ := (h.ok x n o hc).fields_locs
  refine ⟨ls, hls, fun l hl => h.linear.1.2.2 _ ?_⟩
  obtain ⟨H₀, rfl⟩ := Multiset.exists_cons_of_mem hc
  rw [Heap.rngFv_cons_bind, Multiset.mem_add]
  left
  rw [HObj.fv_eq_fields, hls, LVal.fvList_locs]
  simp [hl]

end FIP.Lam
