module

public import RequestProject.Named.AppE_HeapSoundness.HeapApp

@[expose] public section

/-!
# The main invariant of Theorem 6: matches

The matched location is bound to a constructor cell `C z̄`; the heap semantics selects the
branch `C x̄ ↦ dup x̄; e`, substitutes the fields `z̄` for `x̄` and duplicates them.  In a
reusing branch `e` is `dropru x; e'`, which turns the matched cell (or a fresh cell, if the
matched one is shared) into a reuse credit of the right size.
-/

namespace FIPNamed.Lam

variable {sig : LSig} {n : Nat} {Δ : Finset Var} {Γ : Ctx} {H : Heap} {R : Multiset Var}
  {RC : Multiset Nat} {σ : Nat → Option LVal} {vs : List LVal}

theorem lfindBranch_spec {bs : List LBranch} {c : CName} {k : Nat} {b : LBranch}
    (h : lfindBranch bs c k = some b) : b ∈ bs ∧ b.ctor = c ∧ b.binders.length = k := by
  unfold lfindBranch at h
  have h1 := List.mem_of_find?_eq_some h
  have h2 := List.find?_some h
  simp only [Bool.and_eq_true, beq_iff_eq] at h2
  exact ⟨h1, h2.1, h2.2⟩

theorem HInv.of_empties {funs : List FName} : ∀ (j : Nat) {Γ₀ : Ctx},
    HInv funs H R RC (Γ₀ + Multiset.replicate j (Res.credit 0)) σ → HInv funs H R RC Γ₀ σ
  | 0, Γ₀, h => by simpa using h
  | j + 1, Γ₀, h => by
    have heq : Γ₀ + Multiset.replicate (j + 1) (Res.credit 0) =
        (Γ₀ + Multiset.replicate j (Res.credit 0)) + {Res.credit 0} := by
      rw [Multiset.replicate_succ, ← Multiset.singleton_add]; abel
    rw [heq] at h
    exact HInv.of_empties j h.of_empty

theorem vals_subst_locS (σ : Nat → Option LVal) (xs : List Binder) :
    LVal.substList (locS σ) (Binder.vals xs) = Binder.vals xs := by
  have := substList_vals_remove (locS σ) xs
  rwa [locS_remove] at this

theorem case_match (IH : ∀ m < n, HMainClaim sig m) {x : Var} {bs : List LBranch}
    (hx : x ∈ Δ ∨ Res.var x ∈ Γ) (hfr : ∀ b ∈ bs, Binder.LFresh b.binders Δ Γ)
    (es : LBranch → LExpr) (hes : ∀ b ∈ bs, b.body = dups (Binder.vals b.binders) (es b))
    (hwf : ∀ b ∈ bs, LWf sig.funs Δ (Γ + Binder.ctx b.binders) (es b))
    (hadm : (LExpr.match (.var x) bs).Adm) (h : HInv sig.funs H R RC Γ σ)
    (hΔ : ∀ x ∈ Δ, x ∈ R)
    (hev : LStepsN sig n ((LExpr.match (.var x) bs).subst (locS σ)) (.ret vs)) :
    HeapResult sig H R RC (.match (.var x) bs) σ vs := by
  have hadmb : ∀ b ∈ bs, LBranch.Adm x b := by cases hadm; assumption
  have hxc : x ∈ H.cntM := by
    rcases hx with hx | hx
    · exact h.R_cntM (hΔ x hx)
    · exact h.vars_cntM (Ctx.mem_vars.mpr hx)
  obtain ⟨l, nc, o, rfl, hc, hrdx⟩ := h.cell_rd hxc
  simp only [LExpr.subst] at hev
  obtain ⟨m, t, rfl, hh, hrest⟩ :=
    LStepsN.head_of (fun _ hs => LStep.of_noCtx (by simp [LExpr.NoCtx]) hs)
      (by simp [LExpr.IsRet]) hev
  have hrdx' : (LVal.var (.loc l)).subst (locS σ) = o.toVal.subst (locS σ) := hrdx
  rw [hrdx'] at hh
  obtain ⟨-, -, hok⟩ := h.cell_ok hc
  cases o with
  | clo zs xs body => cases hh
  | con c fs =>
  simp only [HObj.toVal, LVal.subst] at hh
  cases hh with
  | «match» _ _ _ xs e hfind =>
  rw [lfindBranch_substB, Option.map_eq_some_iff] at hfind
  obtain ⟨b, hfind, hbe⟩ := hfind
  obtain ⟨hb, hbc, hbl⟩ := lfindBranch_spec hfind
  obtain ⟨c', xs', body⟩ := b
  simp only [LBranch.ctor, LBranch.binders, LBranch.body, LBranch.mk.injEq] at hbe hbc hbl
  obtain ⟨-, hx', he'⟩ := hbe
  subst xs e c'
  have hfr' := hfr _ hb
  have hwfb := hwf _ hb
  have hes' := hes _ hb
  have hab := hadmb _ hb
  simp only [LBranch.body, LBranch.binders] at hes' hwfb hfr'
  generalize es (.mk c xs' body) = eb at hes' hwfb
  have hnd := hfr'.1
  have hfsl : ∀ f ∈ fs, f.IsLoc := hok
  obtain ⟨ys, rfl⟩ := exists_map_var hfsl
  have hlenv : xs'.length = (LVal.substList (locS σ) (ys.map LVal.var)).length := hbl
  have hlen' : xs'.length = (ys.map LVal.var).length := by
    rw [hbl, LVal.substList_eq_map, List.length_map]
  have hlen : xs'.length = ys.length := by rw [hlen', List.length_map]
  -- the functional reduction
  rw [locS_remove, hes', subst_dups, vals_subst_locS, subst_dups,
    vals_subst_lzip xs' _ hnd hlenv] at hrest
  obtain ⟨-, hrest'⟩ := LStepsN.dups_inv _ hrest
  -- the heap reduction
  have hfind' : lfindBranch bs c (ys.map LVal.var).length = some (.mk c xs' body) := by
    rwa [LVal.substList_eq_map, List.length_map] at hfind
  have hstep0 := HSteps.head (sig := sig) (HHead.match H (.loc l) nc c (ys.map .var) bs xs' body hc hfind')
  rw [hes', subst_dups, vals_subst_lzip xs' _ hnd hlen'] at hstep0
  obtain ⟨H₁, hs1, hinv1, hobj1, -⟩ := h.dups (sig := sig) (ys.map .var) hfsl
    (fun y hy => h.obj_fv_cntM hc (by simpa [HObj.fv] using hy))
    (eb.subst (lzip xs' (ys.map .var)))
  have hren : (Γ + Binder.ctx xs').map (Res.ren (lzip xs' (ys.map .var))) =
      Γ + locCtx (ys.map .var) := by
    rw [Multiset.map_add, Res.ren_locOnly (lzip_locRen _ _ hfsl) h.ctx,
      ctx_ren_lzip xs' ys hnd hlen]
  have himg : Δ.image (lzip xs' (ys.map .var)).ren = Δ :=
    image_ren_locs (lzip_locRen _ _ hfsl) (h.locs_of_R hΔ)
  cases hab with
  | plain _ _ _ _ hadmbody =>
    have hadm_eb : eb.Adm := LExpr.Adm.of_dups _ (hes' ▸ hadmbody)
    have hres := cont IH (m := m - (LVal.substList (locS σ) (ys.map LVal.var)).length)
      (by omega) hfsl hwfb hadm_eb (by rw [hren]; exact hinv1)
      (by rw [himg]; exact hΔ) (by rw [← LVal.substList_eq_map]; exact hrest')
    exact HeapResult.prepend (hstep0.trans hs1) hres (fun _ _ => rfl)
  | reuse _ _ e _ he hxn =>
    have heb := dups_inj _ hes'
    subst heb
    have hwfr := hwfb.rename (lzip_locRen xs' (ys.map .var) hfsl)
    rw [hren, himg] at hwfr
    have hdr : (LExpr.dropru (.var (.loc l)) xs'.length e).subst (lzip xs' (ys.map .var)) =
        .dropru (.var (.loc l)) xs'.length (e.subst (lzip xs' (ys.map .var))) := by
      simp [LExpr.subst, LVal.subst, lzip_loc]
    rw [hdr] at hwfr hs1 hstep0
    obtain ⟨Γ₀, j, hΓeq, hwf0⟩ := hwfr.dropru_inv rfl
    have hinv1' : HInv sig.funs H₁ R RC (Γ₀ + {Res.var (.loc l)}) σ :=
      HInv.of_empties j (hΓeq ▸ hinv1)
    obtain ⟨mc, hc1⟩ := hobj1 _ _ _ hc
    obtain ⟨H₂, hs2, hinv2⟩ := hinv1'.dropru (sig := sig) hc1 (e.subst (lzip xs' (ys.map .var)))
    rw [← hlen'] at hs2 hinv2
    simp only [LExpr.subst] at hrest'
    obtain ⟨m2, t2, hm2, hh2, hrest2⟩ :=
      LStepsN.head_of (fun _ hs => LStep.of_noCtx (by simp [LExpr.NoCtx]) hs)
        (by simp [LExpr.IsRet]) hrest'
    cases hh2
    have hres := IH m2 (by omega) hwf0 (he.rename (lzip_locRen _ _ hfsl)) hinv2 hΔ
      (by
        rw [LExpr.subst_commute _ (lzip_nameOnly _ _ hfsl) h.closedLoc, lzip_post,
          ← LVal.substList_eq_map]
        exact hrest2)
    exact HeapResult.prepend ((hstep0.trans hs1).trans hs2) hres (fun _ _ => rfl)

end FIPNamed.Lam
