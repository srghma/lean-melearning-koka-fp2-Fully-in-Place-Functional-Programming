module

public import RequestProject.AppE_HeapSoundness.HeapSoundSimple

@[expose] public section

/-!
# Theorem 6: `let` and `match`

The main lemma for `let x̄ = e₁ in e₂` (the bound expression is evaluated with the
environment `Γ₂, Γ₃` of the body kept in the frame, and the body with the resulting
locations for `x̄`) and for the non-destructive `match x {Cᵢ x̄ᵢ ↦ dup x̄ᵢ; eᵢ}` (the
fields of the cell of `x` are duplicated, and the branch is evaluated with them for `x̄ᵢ`).
-/

namespace FIP.Lam

variable {sig : LSig}

theorem Ctx.res_of_mem_vars_toFinset {n : Nat} {Γ : Ctx n} {x : Var n}
    (h : x ∈ Γ.vars.toFinset) : Res.var x ∈ Γ := by
  simp only [Multiset.mem_toFinset, Ctx.vars, Multiset.mem_filterMap] at h
  obtain ⟨r, hr, hx⟩ := h
  cases r <;> simp_all

theorem bvals_subst_locs {m k : Nat} (ρ : Fin m → Nat) (xs : List Nat) (hl : xs.length = k) :
    (bvals m k).map (LVal.subst (LSubst.locs (instN k xs ρ))) = xs.map locV := by
  subst hl
  apply List.ext_getElem (by simp [bvals])
  intro i h1 h2
  simp only [bvals, List.map_map, List.getElem_map, List.getElem_finRange, Function.comp_apply]
  rw [LVal.subst_locs_var, Var.ren_newB]
  simp only [Fin.cast_mk, List.getD_eq_getElem _ _ (by simpa using h2)]

variable {n m : Nat} {Δ : Finset (Var m)}

theorem exprClaim_letIn {Γ₁ Γ₂ Γ₃ : Ctx m} {k : Nat} {e₁ : LExpr m} {e₂ : LExpr (m + k)}
    (hΓ₂ : Γ₂.OnlyVars) (h₁ : LWf sig.funs (Δ ∪ Γ₂.vars.toFinset) Γ₁ e₁)
    (h₂ : LWf sig.funs (Vars.shift k Δ) (Ctx.shift k (Γ₂ + Γ₃) + bCtx m k) e₂)
    (ih₁ : ExprClaim sig n (Δ ∪ Γ₂.vars.toFinset) Γ₁ e₁)
    (ih₂ : ExprClaim sig n (Vars.shift k Δ) (Ctx.shift k (Γ₂ + Γ₃) + bCtx m k) e₂) :
    ExprClaim sig n Δ (Γ₁ + Γ₂ + Γ₃) (.letIn k e₁ e₂) := by
  intro n' hn sz hadm ρ H R σ vs hsz hH hΔ hR hst
  have hwf := LWf.letIn Γ₁ Γ₂ Γ₃ k e₁ e₂ hΓ₂ h₁ h₂
  have hdef := locs_defined hwf hH hΔ hR
  set E2 := e₂.subst (LSubst.up k (LSubst.locs ρ)) with hE2
  have hsub : (LExpr.letIn k e₁ e₂).subst (LSubst.locs ρ) =
      .letIn k (e₁.subst (LSubst.locs ρ)) E2 := rfl
  rw [hsub] at hst hdef ⊢
  simp only [LExpr.substLoc] at hst
  obtain ⟨n₁, ws, hn₁, hst₁, hst₂⟩ := LStepsN.plug_inv (E := .letIn k .hole (E2.substLoc σ))
    (e := (e₁.subst (LSubst.locs ρ)).substLoc σ) hst
  -- the bound expression
  obtain ⟨H₁, xs, σ₁, hs₁, hI₁, hE₁, hr₁, hv₁⟩ :=
    ih₁ n₁ (by omega) sz hadm.1 ρ H (nzCtx (Ctx.ren ρ (Γ₂ + Γ₃)) + R) σ ws hsz hH
      (by
        intro y hy
        rcases Finset.mem_union.mp hy with hy | hy
        · exact Multiset.mem_add.mpr (.inr (hΔ y hy))
        · refine Multiset.mem_add.mpr (.inl (mem_nzCtx_var (mem_ren_var ?_)))
          exact Multiset.mem_add.mpr (.inl (Ctx.res_of_mem_vars_toFinset hy)))
      (by rw [hR]; simp only [Ctx.ren_add, nzCtx_add]; abel) hst₁
  -- the `let` step
  obtain ⟨n₃, e', hn₃, hh, hst₃⟩ := LStepsN.head_inv (LExpr.ready_letIn k ws _) (by simp) hst₂
  cases hh with
  | letIn _ _ _ hlen =>
  have hxs : xs.length = k := by
    rw [← hlen, LVals.length, ← hv₁, List.length_map]
  have hstep := HHead.letIn (sig := sig) H₁ k (LVals.ofList (xs.map locV)) E2
    (by simpa using locs_atomic xs) (by simp [LVals.length, hxs])
  rw [LVals.toList_ofList] at hstep
  unfold LExpr.inst0 at hstep
  rw [hE2, LExpr.subst_up_inst0 ρ xs hxs] at hstep
  refine HeapResult.prepend ((hs₁.ctx (.letIn k .hole E2)).trans (HSteps.single hstep.step))
    hE₁ ?_
  -- the body
  refine ih₂ n₃ (by omega) _ hadm.2 (instN k xs ρ) H₁ R σ₁ vs ((hsz.mono hE₁).up xs) hI₁
    (delta_shift xs hΔ) ?_ ?_
  · rw [hr₁, roots_binder ρ xs hxs]; abel
  · have : (e₂.subst (LSubst.locs (instN k xs ρ))).substLoc σ₁ =
        (E2.substLoc σ).inst0 ws.toList := by
      rw [← LExpr.subst_up_inst0 ρ xs hxs, ← hE2]
      change (E2.inst0 (xs.map locV)).substLoc σ₁ = _
      rw [LExpr.inst0_substLoc, List.map_map, Function.comp_def, hv₁,
        ← substLoc_ext (fun l hl => hdef l (by simp [LExpr.locs, hl])) hE₁]
    rw [this]; exact hst₃

theorem SzOk.branch {m k : Nat} {sz : Fin m → Option Nat} {ρ : Fin m → Nat}
    {σ : Nat → Option (LVal 0)} (h : SzOk sz ρ σ) (xs : List Nat) (x : Var m) {l : Nat}
    (hxl : x.ren ρ = .loc l) {c : CName} {ws : LVals 0} (hσ : σ l = some (.ctor c ws))
    (hws : ws.length = k) :
    SzOk (SzEnv.branch sz (.var x) k) (instN k xs ρ) σ := by
  cases x with
  | loc l' => exact h.up xs
  | bvar j =>
    intro i k' hi
    simp only [SzEnv.branch] at hi
    split at hi
    · rename_i hij
      cases hi
      refine ⟨c, ws, ?_, hws⟩
      simp only [Var.ren, Var.loc.injEq] at hxl
      have : instN k xs ρ i = ρ j := by
        simp only [instN, show ¬ (i.val < k) by omega, dite_false]
        exact congrArg ρ (Fin.ext (by simp; omega))
      rw [this, hxl]; exact hσ
    · exact h.up xs i k' hi

theorem exprClaim_match {Γ : Ctx m} (x : Var m) (bs : LBranches m)
    (hx : x ∈ Δ ∨ Res.var x ∈ Γ) (es : (b : LBranch m) → LExpr (m + b.k))
    (hes : ∀ b ∈ bs.toList, b.body = dups (bvals m b.k) (es b))
    (ih : ∀ b ∈ bs.toList,
      ExprClaim sig n (Vars.shift b.k Δ) (Ctx.shift b.k Γ + bCtx m b.k) (es b)) :
    ExprClaim sig n Δ Γ (.match (.var x) bs) := by
  intro n' hn sz hadm ρ H R σ vs hsz hH hΔ hR hst
  obtain ⟨l, hl⟩ := Var.zero_eq_loc (x.ren ρ)
  have hroot := alive_var hΔ hR hx
  rw [hl] at hroot
  obtain ⟨cnt, o, hc⟩ := Heap.mem_dom_iff.mp (hH.linear.mem_dom_of_root hroot)
  have hsub : (LExpr.match (.var x) bs).subst (LSubst.locs ρ) =
      .match (locV l) (bs.subst (LSubst.locs ρ)) := by
    simp only [LExpr.subst, LVal.subst_locs_var, hl]
  rw [hsub] at hst ⊢
  simp only [LExpr.substLoc] at hst
  rw [hH.locV_substLoc hc] at hst
  obtain ⟨n₂, e', rfl, hh, hst₂⟩ := LStepsN.head_inv
    (LExpr.ready_other ⟨by simp, by simp, by simp, by simp⟩) (by simp) hst
  obtain ⟨zls, hzls, hzdom⟩ := hH.fields_dom hc
  obtain ⟨c, zs⟩ | ⟨zs, c', k', b⟩ := o
  swap
  · cases hh
  simp only [HObj.fields] at hzls
  subst hzls
  simp only [HObj.toVal] at hh
  cases hh with
  | «match» _ _ _ b' hfind =>
  rw [LBranches.find_substLoc, LBranches.find_subst] at hfind
  cases hb : bs.find c (LVals.ofList ((zls.map locV).map (LVal.substLoc σ))).length with
  | none => rw [hb] at hfind; simp at hfind
  | some b =>
  rw [hb] at hfind
  simp only [Option.map_some, Option.some.injEq] at hfind
  subst hfind
  have hbmem := LBranches.find_mem hb
  have hbk : b.k = zls.length := by
    have := (LBranches.find_spec hb).2; rw [this]; simp [LVals.length]
  -- the heap `match` step
  have hfind' : (bs.subst (LSubst.locs ρ)).find c (zls.map locV).length =
      some (LBranch.subst (LSubst.locs ρ) b) := by
    rw [LBranches.find_subst]
    have : (zls.map locV).length =
        (LVals.ofList ((zls.map locV).map (LVal.substLoc σ))).length := by simp [LVals.length]
    rw [this, hb]; rfl
  have hstep := HHead.match (sig := sig) H (.loc l) cnt c (zls.map locV) _ _ hc hfind'
  have hbody : (LBranch.subst (LSubst.locs ρ) b).body.inst0 (zls.map locV) =
      dups (zls.map locV) ((es b).subst (LSubst.locs (instN b.k zls ρ))) := by
    simp only [LBranch.subst]
    unfold LExpr.inst0
    rw [LExpr.subst_up_inst0 ρ zls hbk.symm, hes b hbmem, subst_dups,
      bvals_subst_locs ρ zls hbk.symm]
  rw [hbody] at hstep
  obtain ⟨H₁, hs₁, hI₁, hr₁, -⟩ := heap_dups (sig := sig) zls
    ((es b).subst (LSubst.locs (instN b.k zls ρ))) hH hzdom
  refine HeapResult.prepend ((HSteps.single hstep.step).trans hs₁) (SubstExt.refl σ) ?_
  -- the functional continuation
  have hcont : (LBranch.substLoc σ (LBranch.subst (LSubst.locs ρ) b)).body.inst0
      (LVals.ofList ((zls.map locV).map (LVal.substLoc σ))).toList =
      dups ((zls.map locV).map (LVal.substLoc σ))
        (((es b).subst (LSubst.locs (instN b.k zls ρ))).substLoc σ) := by
    rw [LVals.toList_ofList, ← LExpr.substLoc_dups, ← hbody]
    simp only [LBranch.substLoc]
    rw [LExpr.inst0_substLoc]
  rw [hcont] at hst₂
  obtain ⟨n₃, rfl, hst₃⟩ := LStepsN.dups_inv _ hst₂
  have hadmb : (es b).Adm (SzEnv.branch sz (.var x) b.k) := by
    have := LBranches.adm_mem hadm.2 b hbmem
    rw [hes b hbmem] at this
    exact LExpr.adm_dups _ this
  refine ih b hbmem n₃ (by omega) _ hadmb (instN b.k zls ρ) H₁ R σ vs
    (hsz.branch zls x hl (hH.reads l cnt _ hc) (by simp [LVals.length, hbk])) hI₁
    (delta_shift zls hΔ) ?_ hst₃
  rw [hr₁, roots_binder ρ zls hbk.symm, hR]; abel

end FIP.Lam
