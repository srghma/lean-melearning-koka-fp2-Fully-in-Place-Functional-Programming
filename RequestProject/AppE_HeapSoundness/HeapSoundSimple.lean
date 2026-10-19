module

public import RequestProject.AppE_HeapSoundness.HeapSoundAux

@[expose] public section

/-!
# Theorem 6: the cases without control flow

The main lemma for tuples, `dup`, `drop`, `dropru`, `free`, `alloc` and the `empty` rule.
-/

namespace FIP.Lam

variable {sig : LSig}

/-! ## Inversion of the functional semantics on administrative instructions -/

theorem LStepsN.drop_inv {n : Nat} {v : LVal 0} {e : LExpr 0} {vs : LVals 0}
    (h : LStepsN sig n (.drop v e) (.ret vs)) : ∃ n', n = n' + 1 ∧ LStepsN sig n' e (.ret vs) := by
  obtain ⟨n', e', rfl, hh, hr⟩ := LStepsN.head_inv
    (LExpr.ready_other ⟨by simp, by simp, by simp, by simp⟩) (by simp) h
  cases hh
  exact ⟨n', rfl, hr⟩

theorem LStepsN.dropru_inv {n k : Nat} {v : LVal 0} {e : LExpr 0} {vs : LVals 0}
    (h : LStepsN sig n (.dropru v k e) (.ret vs)) :
    ∃ n', n = n' + 1 ∧ LStepsN sig n' e (.ret vs) := by
  obtain ⟨n', e', rfl, hh, hr⟩ := LStepsN.head_inv
    (LExpr.ready_other ⟨by simp, by simp, by simp, by simp⟩) (by simp) h
  cases hh
  exact ⟨n', rfl, hr⟩

theorem LStepsN.free_inv {n k : Nat} {e : LExpr 0} {vs : LVals 0}
    (h : LStepsN sig n (.free k e) (.ret vs)) : ∃ n', n = n' + 1 ∧ LStepsN sig n' e (.ret vs) := by
  obtain ⟨n', e', rfl, hh, hr⟩ := LStepsN.head_inv
    (LExpr.ready_other ⟨by simp, by simp, by simp, by simp⟩) (by simp) h
  cases hh
  exact ⟨n', rfl, hr⟩

theorem LStepsN.alloc_inv {n k : Nat} {e : LExpr 0} {vs : LVals 0}
    (h : LStepsN sig n (.alloc k e) (.ret vs)) : ∃ n', n = n' + 1 ∧ LStepsN sig n' e (.ret vs) := by
  obtain ⟨n', e', rfl, hh, hr⟩ := LStepsN.head_inv
    (LExpr.ready_other ⟨by simp, by simp, by simp, by simp⟩) (by simp) h
  cases hh
  exact ⟨n', rfl, hr⟩

theorem HObj.fvCtx_of_fields {o : HObj} {ls : List Nat} (h : o.fields = ls.map locV) :
    o.fvCtx = locsCtx ls := by
  simp [HObj.fvCtx, HObj.fv_eq_fields, h, LVal.fvList_locs, locsCtx, List.map_map,
    Function.comp_def]

@[simp] theorem Res.ren_credit {m : Nat} (ρ : Fin m → Nat) (k : Nat) :
    (Res.credit k : Res m).ren ρ = .credit k := rfl

@[simp] theorem Res.ren_var {m : Nat} (ρ : Fin m → Nat) (x : Var m) :
    (Res.var x).ren ρ = .var (x.ren ρ) := rfl

/-! ## The cases -/

variable {n m : Nat} {Δ : Finset (Var m)}

theorem exprClaim_tuple {Γ : Ctx m} (vs₀ : LVals m) (h : LWfVals sig.funs Δ Γ vs₀.toList) :
    ExprClaim sig n Δ Γ (.ret vs₀) := by
  intro n' _ sz hadm ρ H R σ vs _ hH _ hR hst
  simp only [LExpr.subst, LExpr.substLoc] at hst
  obtain ⟨-, hv⟩ := hst.ret_inv
  cases hv
  obtain ⟨H', ls, σ', hs, hI, hE, hr, hval⟩ := h.alloc ρ (ListPos.ret .hole) [] [] (by simp)
    ((LVals.adm_iff vs₀).mp hadm) hH hR
  refine ⟨H', ls, σ', ?_, hI, hE, hr, ?_⟩
  · simp only [LExpr.subst, List.nil_append, List.append_nil, LECtx.plug] at hs ⊢
    rw [← LVals.ofList_toList (vs₀.subst _), LVals.toList_subst]; exact hs
  · rw [hval]; simp

theorem exprClaim_dup {Γ : Ctx m} {e : LExpr m} (x : Var m) (hx : x ∈ Δ ∨ Res.var x ∈ Γ)
    (ih : ExprClaim sig n Δ (Γ + {Res.var x}) e) : ExprClaim sig n Δ Γ (.dup (.var x) e) := by
  intro n' hn sz hadm ρ H R σ vs hsz hH hΔ hR hst
  obtain ⟨l, hl⟩ := Var.zero_eq_loc (x.ren ρ)
  have hroot := alive_var hΔ hR hx
  rw [hl] at hroot
  have hsub : (LExpr.dup (.var x) e).subst (LSubst.locs ρ) =
      dups ([l].map locV) (e.subst (LSubst.locs ρ)) := by
    simp only [LExpr.subst, LVal.subst_locs_var, hl]; rfl
  rw [hsub] at hst ⊢
  obtain ⟨n'', rfl, hst'⟩ := LStepsN.dups_inv _ (by simpa [LExpr.substLoc_dups] using hst)
  obtain ⟨H₁, hs, hI, hr, -⟩ := heap_dups (sig := sig) [l] (e.subst (LSubst.locs ρ)) hH
    (by simpa using hH.linear.mem_dom_of_root hroot)
  refine HeapResult.prepend hs (SubstExt.refl σ) ?_
  refine ih n'' (by simp at hn ⊢; omega) sz hadm.2 ρ H₁ R σ vs hsz hI hΔ ?_ hst'
  rw [hr, hR]; simp [hl]; abel

theorem exprClaim_drop {Γ : Ctx m} {e : LExpr m} (x : Var m)
    (ih : ExprClaim sig n Δ Γ e) : ExprClaim sig n Δ (Γ + {Res.var x}) (.drop (.var x) e) := by
  intro n' hn sz hadm ρ H R σ vs hsz hH hΔ hR hst
  obtain ⟨l, hl⟩ := Var.zero_eq_loc (x.ren ρ)
  have hroot := alive_var hΔ hR (x := x) (.inr (by simp))
  rw [hl] at hroot
  have hsub : (LExpr.drop (.var x) e).subst (LSubst.locs ρ) =
      .drop (locV l) (e.subst (LSubst.locs ρ)) := by
    simp only [LExpr.subst, LVal.subst_locs_var, hl]
  rw [hsub] at hst ⊢
  obtain ⟨n'', rfl, hst'⟩ := LStepsN.drop_inv hst
  obtain ⟨H₁, hs, hI, hr⟩ := heap_drop (sig := sig) hH l (e.subst (LSubst.locs ρ)) hroot
  refine HeapResult.prepend hs (SubstExt.refl σ) ?_
  refine ih n'' (by omega) sz hadm.2 ρ H₁ R σ vs hsz hI hΔ ?_ hst'
  apply add_right_cancel (b := {Res.var (Var.loc l)})
  rw [hr, hR]; simp [hl]; abel

theorem exprClaim_dropru {Γ : Ctx m} {e : LExpr m} (x : Var m) (k : Nat)
    (ih : ExprClaim sig n Δ (Γ + {Res.credit k}) e) :
    ExprClaim sig n Δ (Γ + {Res.var x}) (.dropru (.var x) k e) := by
  intro n' hn sz hadm ρ H R σ vs hsz hH hΔ hR hst
  obtain ⟨⟨i, hi, hk⟩, hadm⟩ := hadm
  cases hi
  set l := ρ i with hl
  have hroot := alive_var hΔ hR (x := .bvar i) (.inr (by simp))
  simp only [Var.ren] at hroot
  have hsub : (LExpr.dropru (.var (.bvar i)) k e).subst (LSubst.locs ρ) =
      .dropru (locV l) k (e.subst (LSubst.locs ρ)) := by
    simp only [LExpr.subst, LVal.subst_locs_var, Var.ren]; rfl
  rw [hsub] at hst ⊢
  obtain ⟨n'', rfl, hst'⟩ := LStepsN.dropru_inv hst
  obtain ⟨c, ws, hσl, hws⟩ := hsz i k hk
  obtain ⟨cnt, o, hc⟩ := Heap.mem_dom_iff.mp (hH.linear.mem_dom_of_root hroot)
  have hread := hH.reads l cnt o hc
  rw [hσl] at hread
  obtain ⟨zls, hzls, -⟩ := hH.fields_dom hc
  obtain ⟨c', zs⟩ | ⟨zs, c', k', b⟩ := o
  swap
  · simp [HObj.toVal] at hread
  simp only [HObj.toVal, Option.some.injEq, LVal.ctor.injEq] at hread
  obtain ⟨rfl, rfl⟩ := hread
  simp only [HObj.fields] at hzls
  subst hzls
  have hk' : k = (zls.map locV).length := by
    rw [← hws]; simp [LVals.length]
  subst hk'
  obtain ⟨H₀, rfl⟩ := Multiset.exists_cons_of_mem hc
  rw [← Multiset.singleton_add] at hH hroot hR ⊢
  have hpos : 1 ≤ cnt :=
    hH.linear.1.2.1 _ _ _ (Multiset.mem_add.mpr (.inl (Multiset.mem_singleton_self _)))
  have hih := fun H₁ (hI : HInv sig.funs H₁ σ)
      (hr : H₁.roots = nzCtx (Ctx.ren ρ (Γ + {Res.credit (zls.map locV).length})) + R) =>
    ih n'' (by omega) sz hadm ρ H₁ R σ vs hsz hI hΔ hr hst'
  obtain _ | _ | cnt := cnt
  · omega
  · -- the cell is unique: it becomes a reuse credit
    have hstep := HHead.dconru (sig := sig) H₀ (.loc l) c (zls.map locV)
      (e.subst (LSubst.locs ρ))
    have hI₁ := (hH.free hroot).add_credit (zls.map locV).length
    have hlin₀ := Heap.free_linear hH.linear hroot
    have hle := free_fvCtx_le hH.linear hroot
    rw [HObj.fvCtx_of_fields (ls := zls) rfl] at hle
    have hr₁ := Heap.roots_credit hlin₀ (zls.map locV).length
    obtain ⟨H₂, hs, hI₂, hr₂⟩ := heap_drops (sig := sig) hI₁ zls (e.subst (LSubst.locs ρ))
      (by rw [hr₁]; exact le_add_left hle)
    refine HeapResult.prepend ((HSteps.single hstep.step).trans hs) (SubstExt.refl σ) ?_
    refine hih H₂ hI₂ ?_
    have hfree := Heap.roots_free hH.linear hroot
    rw [HObj.fvCtx_of_fields (ls := zls) rfl] at hfree
    apply add_right_cancel (b := locsCtx zls + {Res.var (Var.loc l)})
    rw [← add_assoc, hr₂, hr₁, add_assoc, hfree, hR]
    simp only [Ctx.ren_add, Ctx.ren_singleton, nzCtx_add, Res.ren_var, Res.ren_credit, Var.ren,
      nzCtx_var]
    abel
  · -- the cell is shared: a fresh reuse credit is allocated
    have hstep := HHead.dropru (sig := sig) H₀ (.loc l) cnt c (zls.map locV)
      (e.subst (LSubst.locs ρ))
    have hI₁ := (hH.dec hroot).add_credit (zls.map locV).length
    have hlin₁ := Heap.dec_linear hH.linear hroot
    have hr₁ := Heap.roots_credit hlin₁ (zls.map locV).length
    have hdec := Heap.roots_dec hH.linear hroot
    have heq : ({HCell.bind (.loc l) (cnt + 1) (.con c (zls.map locV))} +
        {HCell.credit (zls.map locV).length} + H₀ : Heap) =
        {HCell.credit (zls.map locV).length} +
          ({HCell.bind (.loc l) (cnt + 1) (.con c (zls.map locV))} + H₀) := by
      abel
    refine HeapResult.prepend (HSteps.single hstep.step) (SubstExt.refl σ) ?_
    rw [heq]
    refine hih _ hI₁ ?_
    apply add_right_cancel (b := {Res.var (Var.loc l)})
    rw [hr₁, add_assoc, hdec, hR]
    simp only [Ctx.ren_add, Ctx.ren_singleton, nzCtx_add, Res.ren_var, Res.ren_credit, Var.ren,
      nzCtx_var]
    abel

theorem exprClaim_free {Γ : Ctx m} {e : LExpr m} (k : Nat) (hk : 1 ≤ k)
    (ih : ExprClaim sig n Δ Γ e) : ExprClaim sig n Δ (Γ + {Res.credit k}) (.free k e) := by
  intro n' hn sz hadm ρ H R σ vs hsz hH hΔ hR hst
  simp only [LExpr.subst, LExpr.substLoc] at hst ⊢
  obtain ⟨n'', rfl, hst'⟩ := LStepsN.free_inv hst
  have hnz : nzCtx {Res.credit k} = {Res.credit k} := nzCtx_credit (by omega)
  have hroot : Res.credit k ∈ H.roots := by
    rw [hR]; simp [hnz]
  obtain ⟨H₀, rfl⟩ := Multiset.exists_cons_of_mem (Heap.credit_mem_of_root hroot)
  rw [← Multiset.singleton_add] at hH hR ⊢
  have hr₁ := Heap.roots_credit (Heap.linear_of_credit hH.linear) k
  refine HeapResult.prepend (HSteps.single (HHead.free (sig := sig) H₀ k _).step)
    (SubstExt.refl σ) ?_
  refine ih n'' (by omega) sz hadm ρ H₀ R σ vs hsz hH.remove_credit hΔ ?_ hst'
  apply add_left_cancel (a := nzCtx {Res.credit k})
  rw [← hr₁, hR]
  simp only [Ctx.ren_add, Ctx.ren_singleton, nzCtx_add, Res.ren_credit]
  abel

theorem exprClaim_alloc {Γ : Ctx m} {e : LExpr m} (k : Nat)
    (ih : ExprClaim sig n Δ (Γ + {Res.credit k}) e) : ExprClaim sig n Δ Γ (.alloc k e) := by
  intro n' hn sz hadm ρ H R σ vs hsz hH hΔ hR hst
  simp only [LExpr.subst, LExpr.substLoc] at hst ⊢
  obtain ⟨n'', rfl, hst'⟩ := LStepsN.alloc_inv hst
  refine HeapResult.prepend (HSteps.single (HHead.alloc (sig := sig) H k _).step)
    (SubstExt.refl σ) ?_
  refine ih n'' (by omega) sz hadm ρ _ R σ vs hsz (hH.add_credit k) hΔ ?_ hst'
  rw [Heap.roots_credit hH.linear, hR]
  simp only [Ctx.ren_add, Ctx.ren_singleton, nzCtx_add, Res.ren_credit]
  abel

theorem exprClaim_empty {Γ : Ctx m} {e : LExpr m} (ih : ExprClaim sig n Δ Γ e) :
    ExprClaim sig n Δ (Γ + {Res.credit 0}) e := by
  intro n' hn sz hadm ρ H R σ vs hsz hH hΔ hR hst
  refine ih n' hn sz hadm ρ H R σ vs hsz hH hΔ ?_ hst
  rw [hR]; simp

end FIP.Lam
