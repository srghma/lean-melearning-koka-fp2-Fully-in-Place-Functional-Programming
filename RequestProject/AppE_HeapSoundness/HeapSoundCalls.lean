module

public import RequestProject.AppE_HeapSoundness.HeapSoundCases

@[expose] public section

/-!
# Theorem 6: calls and applications

The main lemma for a call `f(ȳ; e)` of a top-level function and for an application
`e₁ e₂` of a closure.  The body of the function (or of the closure) is not a subterm of
the expression, so these cases use the main lemma for fewer functional steps.
-/

namespace FIP.Lam

variable {sig : LSig}

/-- The borrowed arguments of an admissible call are borrowed variables. -/
theorem borrow_locs {m : Nat} {funs : List FName} {Δ : Finset (Var m)} {ρ : Fin m → Nat}
    {R : Ctx 0} (hΔ : ∀ y ∈ Δ, Res.var (y.ren ρ) ∈ R) :
    ∀ (ys : List (LVal m)), (∀ y ∈ ys, LBorrowArg funs Δ y) → (∀ y ∈ ys, y.Adm) →
      ∃ yls : List Nat, ys.map (LVal.subst (LSubst.locs ρ)) = yls.map locV ∧
        ∀ l ∈ yls, Res.var (.loc l) ∈ R
  | [], _, _ => ⟨[], rfl, by simp⟩
  | y :: ys, hb, ha => by
    obtain ⟨yls, h1, h2⟩ := borrow_locs hΔ ys (fun z hz => hb z (by simp [hz]))
      (fun z hz => ha z (by simp [hz]))
    have hby := hb y (by simp)
    have hay := ha y (by simp)
    cases y with
    | var x =>
      refine ⟨(x.ren ρ).toLoc :: yls, by simp [h1, LVal.subst_locs_var'], ?_⟩
      intro l hl
      simp only [List.mem_cons] at hl
      rcases hl with rfl | hl
      · simpa using hΔ x hby
      · exact h2 l hl
    | fn g => exact absurd hay (by simp [LVal.Adm])
    | ctor c vs => exact absurd hby (by simp [LBorrowArg])
    | lam zs c k b => exact absurd hby (by simp [LBorrowArg])

theorem LSig.mem_of_lookup {sig : LSig} {f : FName} {fd : LFunDef} (h : sig.lookup f = some fd) :
    fd ∈ sig := List.mem_of_find?_eq_some h

variable {n m : Nat} {Δ : Finset (Var m)}

theorem exprClaim_call (hsig : sig.Wf) (hadmS : sig.Adm) (IHs : ∀ n'' < n, MainClaim sig n'')
    {Γ : Ctx m} (f : FName) (ys : LVals m) (e : LExpr m)
    (hys : ∀ y ∈ ys.toList, LBorrowArg sig.funs Δ y) (ih : ExprClaim sig n Δ Γ e) :
    ExprClaim sig n Δ Γ (.call f (.ret ys) e) := by
  intro n' hn sz hadm ρ H R σ vs hsz hH hΔ hR hst
  obtain ⟨yls, hyls, hylR⟩ := borrow_locs hΔ ys.toList hys ((LVals.adm_iff ys).mp hadm.1)
  have hY : ys.subst (LSubst.locs ρ) = LVals.ofList (yls.map locV) := by
    rw [← hyls, ← LVals.toList_subst, LVals.ofList_toList]
  have hsub : (LExpr.call f (.ret ys) e).subst (LSubst.locs ρ) =
      .call f (.ret (LVals.ofList (yls.map locV))) (e.subst (LSubst.locs ρ)) := by
    simp only [LExpr.subst, hY]
  rw [hsub] at hst ⊢
  simp only [LExpr.substLoc] at hst
  set Y := (LVals.ofList (yls.map locV)).substLoc σ with hYdef
  obtain ⟨n₁, ws, hn₁, hst₁, hst₂⟩ := LStepsN.plug_inv (E := .callO f Y .hole)
    (e := (e.subst (LSubst.locs ρ)).substLoc σ) hst
  -- the argument
  obtain ⟨H₁, xs, σ₁, hs₁, hI₁, hE₁, hr₁, hv₁⟩ :=
    ih n₁ (by omega) sz hadm.2 ρ H R σ ws hsz hH hΔ hR hst₁
  -- the call
  obtain ⟨n₃, e', hn₃, hh, hst₃⟩ := LStepsN.head_inv (LExpr.ready_call f Y ws) (by simp) hst₂
  cases hh with
  | call _ fd _ _ hlook hb ho =>
  have hfd := LSig.mem_of_lookup hlook
  have hwfb := hsig fd hfd
  have hnil := hwfb.locs_nil_fun
  have hyl : yls.length = fd.borrowed := by
    rw [hb, hYdef]; simp [LVals.length]
  have hxl : xs.length = fd.owned := by
    rw [ho, LVals.length, ← hv₁, List.length_map]
  have hstep := HHead.call (sig := sig) H₁ f fd (LVals.ofList (yls.map locV))
    (LVals.ofList (xs.map locV)) hlook
    (by simpa using fun a ha => (List.mem_append.mp ha).elim (locs_atomic yls a) (locs_atomic xs a))
    (by simp [LVals.length, hyl]) (by simp [LVals.length, hxl])
  rw [LVals.toList_ofList, LVals.toList_ofList] at hstep
  set ρ' := instN fd.borrowed yls (ofListN fd.owned xs) with hρ'
  have hbody : fd.instBody (yls.map locV) (xs.map locV) = fd.body.subst (LSubst.locs ρ') :=
    LExpr.subst_congr (inst_ofList_locs yls xs hyl hxl) _
  rw [hbody] at hstep
  refine HeapResult.prepend ((hs₁.ctx (.callO f _ .hole)).trans (HSteps.single hstep.step))
    hE₁ ?_
  -- the body
  refine IHs n₃ (by omega) hwfb n₃ le_rfl _ (hadmS fd hfd) ρ' H₁ R σ₁ vs (SzOk.none _ _) hI₁
    ?_ ?_ ?_
  · intro y hy
    simp only [bSet, List.mem_toFinset, List.mem_map, List.mem_finRange, true_and] at hy
    obtain ⟨j, rfl⟩ := hy
    rw [hρ', Var.ren_newB, List.getD_eq_getElem _ _ (by omega)]
    exact hylR _ (List.getElem_mem _)
  · rw [hr₁, hρ', Ctx.ren_shift, Ctx.ren_allCtx _ _ hxl, nzCtx_locsCtx]
  · rw [LExpr.subst_locs_substLoc hnil]
    unfold LFunDef.instBody at hst₃
    convert hst₃ using 2
    funext i
    rw [show locV (ρ' i) = LSubst.locs ρ' i from rfl, ← inst_ofList_locs yls xs hyl hxl,
      LSubst.inst_substLoc]
    congr 1
    · rw [hYdef, LVals.toList_substLoc, LVals.toList_ofList]
      apply List.map_congr_left
      intro v hv
      simp only [List.mem_map] at hv
      obtain ⟨l, hl, rfl⟩ := hv
      obtain ⟨w, hw⟩ := hH.some_of_root (hR ▸ Multiset.mem_add.mpr (.inr (hylR l hl)))
      exact (substLoc_ext_val (v := locV l)
        (fun l' hl' => by simp [LVal.locs] at hl'; subst hl'; exact ⟨w, hw⟩) hE₁).symm
    · funext j
      rw [LSubst.ofList_substLoc, List.map_map, Function.comp_def, hv₁]

theorem exprClaim_app (IHs : ∀ n'' < n, MainClaim sig n'') {Γ₁ Γ₂ : Ctx m} (e₁ e₂ : LExpr m)
    (h₂ : LWf sig.funs Δ Γ₂ e₂) (ih₁ : ExprClaim sig n Δ Γ₁ e₁)
    (ih₂ : ExprClaim sig n Δ Γ₂ e₂) : ExprClaim sig n Δ (Γ₁ + Γ₂) (.app e₁ e₂) := by
  intro n' hn sz hadm ρ H R σ vs hsz hH hΔ hR hst
  simp only [LExpr.subst, LExpr.substLoc] at hst ⊢
  obtain ⟨n₁, ws₁, hn₁, hst₁, hst₂⟩ :=
    LStepsN.plug_inv (E := .appL .hole ((e₂.subst (LSubst.locs ρ)).substLoc σ))
      (e := (e₁.subst (LSubst.locs ρ)).substLoc σ) hst
  -- the function
  obtain ⟨H₁, xs₁, σ₁, hs₁, hI₁, hE₁, hr₁, hv₁⟩ :=
    ih₁ n₁ (by omega) sz hadm.1 ρ H (nzCtx (Ctx.ren ρ Γ₂) + R) σ ws₁ hsz hH
      (fun y hy => Multiset.mem_add.mpr (.inr (hΔ y hy)))
      (by rw [hR]; simp only [Ctx.ren_add, nzCtx_add]; abel) hst₁
  have hdef₂ := locs_defined h₂ hH (R := nzCtx (Ctx.ren ρ Γ₁) + R)
    (fun y hy => Multiset.mem_add.mpr (.inr (hΔ y hy)))
    (by rw [hR]; simp only [Ctx.ren_add, nzCtx_add]; abel)
  change LStepsN sig (n' - n₁) (LExpr.app (.ret ws₁) ((e₂.subst (LSubst.locs ρ)).substLoc σ))
    (.ret vs) at hst₂
  rw [substLoc_ext hdef₂ hE₁] at hst₂
  obtain ⟨n₂, ws₂, hn₂, hst₃, hst₄⟩ :=
    LStepsN.plug_inv (E := .appR ws₁ .hole) (e := (e₂.subst (LSubst.locs ρ)).substLoc σ₁) hst₂
  -- the argument
  obtain ⟨H₂, xs₂, σ₂, hs₂, hI₂, hE₂, hr₂, hv₂⟩ :=
    ih₂ n₂ (by omega) sz hadm.2 ρ H₁ (locsCtx xs₁ + R) σ₁ ws₂ (hsz.mono hE₁) hI₁
      (fun y hy => Multiset.mem_add.mpr (.inr (hΔ y hy)))
      (by rw [hr₁]; abel) hst₃
  have hsteps₁₂ := (hs₁.ctx (.appL .hole (e₂.subst (LSubst.locs ρ)))).trans
    (hs₂.ctx (.appR (LVals.ofList (xs₁.map locV)) .hole))
  -- the application
  obtain ⟨n₄, e', hn₄, hh, hst₅⟩ := LStepsN.head_inv (LExpr.ready_app ws₁ ws₂) (by simp) hst₄
  -- the function is a single location, whose cell is still in the heap
  have hcell : ∀ v : LVal 0, ws₁ = .cons v .nil → ∃ y cnt o, xs₁ = [y] ∧
      HCell.bind (.loc y) cnt o ∈ H₂ ∧ v = o.toVal σ₂ := by
    intro v hv
    rw [hv] at hv₁
    obtain ⟨y, rfl, hy⟩ := List.map_eq_singleton_iff.mp hv₁
    have hroot : Res.var (.loc y) ∈ H₂.roots := by rw [hr₂]; simp
    obtain ⟨cnt, o, hc⟩ := Heap.mem_dom_iff.mp (hI₂.linear.mem_dom_of_root hroot)
    have hroot₁ : Res.var (.loc y) ∈ H₁.roots := by rw [hr₁]; simp
    obtain ⟨w, hw⟩ := hI₁.some_of_root hroot₁
    refine ⟨y, cnt, o, rfl, hc, ?_⟩
    rw [← hy, ← hI₂.locV_substLoc hc]
    exact substLoc_ext_val (v := locV y)
      (fun l' hl' => by simp [LVal.locs] at hl'; subst hl'; exact ⟨w, hw⟩) hE₂
  cases hh with
  | appFn f fd _ _ _ _ =>
    obtain ⟨y, cnt, o, -, -, hv⟩ := hcell _ rfl
    cases o <;> simp [HObj.toVal] at hv
  | beta zs c k b _ hlen =>
  obtain ⟨y, cnt, o, rfl, hc, hv⟩ := hcell _ rfl
  obtain ⟨c', args⟩ | ⟨zs₀, c', k', b'⟩ := o
  · simp [HObj.toVal] at hv
  simp only [HObj.toVal, LVal.lam.injEq] at hv
  obtain ⟨hzs, rfl, rfl, hb⟩ := hv
  cases eq_of_heq hb
  obtain ⟨hzloc, hzlen, hwfb, hadmb⟩ := hI₂.ok _ _ _ hc
  obtain ⟨zls, hzls, hzdom⟩ := hI₂.fields_dom hc
  simp only [HObj.fields] at hzls
  subst hzls
  have hzl : zls.length = c := by simpa using hzlen
  have hxl : xs₂.length = k := by rw [← hlen, LVals.length, ← hv₂, List.length_map]
  have hstep := HHead.app (sig := sig) H₂ (.loc y) cnt (zls.map locV) c k b
    (LVals.ofList (xs₂.map locV)) hc (by simpa using locs_atomic xs₂) (by simp [LVals.length, hxl])
  rw [LVals.toList_ofList] at hstep
  set ρ' := instN k xs₂ (ofListN c zls) with hρ'
  have hbody : b.beta (zls.map locV) (xs₂.map locV) = b.subst (LSubst.locs ρ') :=
    LExpr.subst_congr (inst_ofList_locs xs₂ zls hxl hzl) _
  rw [hbody] at hstep
  -- duplicate the captured values, then drop the closure
  obtain ⟨H₃, hs₃, hI₃, hr₃, hd₃⟩ := heap_dups (sig := sig) zls
    (.drop (locV y) (b.subst (LSubst.locs ρ'))) hI₂ hzdom
  have hroot₃ : Res.var (.loc y) ∈ H₃.roots := by rw [hr₃, hr₂]; simp
  obtain ⟨H₄, hs₄, hI₄, hr₄⟩ := heap_drop (sig := sig) hI₃ y (b.subst (LSubst.locs ρ')) hroot₃
  refine HeapResult.prepend
    (hsteps₁₂.trans ((HSteps.single hstep.step).trans (hs₃.trans hs₄))) (hE₁.trans hE₂) ?_
  -- the body
  refine IHs n₄ (by omega) hwfb n₄ le_rfl _ hadmb ρ' H₄ R σ₂ vs (SzOk.none _ _) hI₄
    (by simp) ?_ ?_
  · apply add_right_cancel (b := {Res.var (Var.loc y)})
    rw [hr₄, hr₃, hr₂, hρ', Ctx.ren_allCtx_inst xs₂ zls hxl hzl, nzCtx_add, nzCtx_locsCtx,
      nzCtx_locsCtx]
    simp only [locsCtx_cons, locsCtx_nil, add_zero]
    abel
  · rw [LExpr.subst_locs_substLoc hwfb.locs_nil_clo]
    unfold LExpr.beta at hst₅
    convert hst₅ using 2
    funext i
    rw [show locV (ρ' i) = LSubst.locs ρ' i from rfl, ← inst_ofList_locs xs₂ zls hxl hzl,
      LSubst.inst_substLoc]
    congr 1
    · rw [List.map_map, Function.comp_def, hv₂]
    · funext j
      rw [LSubst.ofList_substLoc, hzs, LVals.toList_ofList]

end FIP.Lam
