module

public import RequestProject.Named.AppE_HeapSoundness.HeapCases

@[expose] public section

/-!
# The main invariant of Theorem 6: `let`, calls, applications and matches

Each of these cases ends by substituting locations for the binders of an expression
(the body of a `let`, of a function, of a closure or of a match branch) and continuing
with the induction hypothesis on the renamed expression (`cont`).
-/

namespace FIPNamed.Lam

variable {sig : LSig} {n : Nat} {Δ : Finset Var} {Γ : Ctx} {H : Heap} {R : Multiset Var}
  {RC : Multiset Nat} {σ : Nat → Option LVal} {vs : List LVal}

theorem isLoc_of_locOnly {ys : List Var} (h : Ctx.LocOnly (locCtx (ys.map .var))) :
    ∀ v ∈ ys.map LVal.var, v.IsLoc := by
  intro v hv
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hv
  rw [locCtx_map] at h
  rcases h (.var y) (Multiset.mem_map_of_mem _ (by simpa using hy)) with ⟨l, hl⟩ | ⟨k, hk⟩
  · injection hl with hl; exact ⟨l, by rw [hl]⟩
  · cases hk

theorem exists_map_var {fs : List LVal} (h : ∀ f ∈ fs, f.IsLoc) :
    ∃ ys : List Var, fs = ys.map .var := by
  induction fs with
  | nil => exact ⟨[], rfl⟩
  | cons f fs ih =>
    obtain ⟨l, rfl⟩ := h f (by simp)
    obtain ⟨ys, rfl⟩ := ih fun g hg => h g (by simp [hg])
    exact ⟨.loc l :: ys, rfl⟩

theorem loc_not_mem_ctx (xs : List Binder) (l : Nat) : Res.var (.loc l) ∉ Binder.ctx xs :=
  not_mem_ctx (loc_not_mem_vars xs l)

/-- Continue with the induction hypothesis after substituting the locations `as` for the
    binders `bs` of a well-formed expression. -/
theorem cont (IH : ∀ m < n, HMainClaim sig m) {m : Nat} (hm : m < n) {Δ₀ : Finset Var}
    {Γ₀ : Ctx} {e₀ : LExpr} {bs : List Binder} {as : List LVal} (has : ∀ a ∈ as, a.IsLoc)
    (hwf : LWf sig.funs Δ₀ Γ₀ e₀) (hadm : e₀.Adm)
    (h : HInv sig.funs H R RC (Γ₀.map (Res.ren (lzip bs as))) σ)
    (hΔ : ∀ x ∈ Δ₀.image (lzip bs as).ren, x ∈ R)
    (hev : LStepsN sig m ((e₀.subst (locS σ)).subst
      (lzip bs (as.map (LVal.subst (locS σ))))) (.ret vs)) :
    HeapResult sig H R RC (e₀.subst (lzip bs as)) σ vs := by
  refine IH m hm (hwf.rename (lzip_locRen bs as has)) (hadm.rename (lzip_locRen bs as has)) h
    hΔ ?_
  rw [LExpr.subst_commute _ (lzip_nameOnly bs as has) h.closedLoc, lzip_post]
  exact hev

theorem map_var_subst (σ : Nat → Option LVal) (ys : List Var) :
    (ys.map LVal.var).map (LVal.subst (locS σ)) = ys.map (rd σ) := by
  simp [List.map_map, Function.comp_def]

/-! ## `let` -/

theorem case_letIn (IH : ∀ m < n, HMainClaim sig m) {Γ₁ Γ₂ Γ₃ : Ctx} {xs : List Binder}
    {e₁ e₂ : LExpr}
    (he₁ : LWf sig.funs (Δ ∪ (Ctx.vars Γ₂).toFinset) Γ₁ e₁)
    (he₂ : LWf sig.funs Δ (Γ₂ + Γ₃ + Binder.ctx xs) e₂) (hfr : Binder.LFresh xs Δ (Γ₂ + Γ₃))
    (hadm : (LExpr.letIn xs e₁ e₂).Adm) (h : HInv sig.funs H R RC (Γ₁ + Γ₂ + Γ₃) σ)
    (hΔ : ∀ x ∈ Δ, x ∈ R)
    (hev : LStepsN sig n ((LExpr.letIn xs e₁ e₂).subst (locS σ)) (.ret vs)) :
    HeapResult sig H R RC (.letIn xs e₁ e₂) σ vs := by
  have hadm1 : e₁.Adm := by cases hadm; assumption
  have hadm2 : e₂.Adm := by cases hadm; assumption
  simp only [LExpr.subst, locS_remove] at hev
  obtain ⟨k, vs₁, hk, hev1, hev2⟩ := LStepsN.plug (.letIn xs .hole _) hev
  simp only [LECtx.plug] at hev2
  obtain ⟨m, t, hm, hh, hrest⟩ :=
    LStepsN.head_of (fun _ hs => LStep.letIn_ret hs) (by simp [LExpr.IsRet]) hev2
  cases hh with
  | letIn _ _ _ hlen =>
  have h1 : HInv sig.funs H (R + Ctx.vars Γ₂ + Ctx.vars Γ₃) (RC + Ctx.cr Γ₂ + Ctx.cr Γ₃) Γ₁ σ :=
    h.shift (by simp only [Ctx.vars_add]; abel) (by simp only [Ctx.cr_add]; abel) h.ctx.left.left
  have hS : ∀ x ∈ Δ ∪ (Ctx.vars Γ₂).toFinset, x ∈ R + Ctx.vars Γ₂ + Ctx.vars Γ₃ := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact Multiset.mem_add.mpr (.inl (Multiset.mem_add.mpr (.inl (hΔ x hx))))
    · exact Multiset.mem_add.mpr (.inl (Multiset.mem_add.mpr (.inr (Multiset.mem_toFinset.mp hx))))
  obtain ⟨H₁, ys, σ₁, hs1, hinv1, hag1, hrd1⟩ := IH k (by omega) he₁ hadm1 h1 hS hev1
  have hys := isLoc_of_locOnly hinv1.ctx
  have hlen' : xs.length = ys.length := by rw [hlen, ← hrd1, List.length_map]
  have hΓloc : Ctx.LocOnly (Γ₂ + Γ₃) := by
    have := h.ctx; rw [add_assoc] at this; exact this.right
  have h2 : HInv sig.funs H₁ R RC
      ((Γ₂ + Γ₃ + Binder.ctx xs).map (Res.ren (lzip xs (ys.map .var)))) σ₁ := by
    rw [Multiset.map_add, Res.ren_locOnly (lzip_locRen _ _ hys) hΓloc,
      ctx_ren_lzip xs ys hfr.1 hlen']
    exact hinv1.shift (by simp only [Ctx.vars_add]; abel) (by simp only [Ctx.cr_add, locCtx_cr]; abel)
      (hΓloc.add hinv1.ctx)
  have hagR : ∀ l, Var.loc l ∈ R → σ₁ l = σ l := fun l hl =>
    hag1 l (Multiset.mem_add.mpr (.inl (Multiset.mem_add.mpr (.inl hl))))
  have he₂σ : e₂.subst (locS σ₁) = e₂.subst (locS σ) := by
    refine subst_agree hag1 fun l hl => ?_
    rcases LWf.dfv_sub he₂ _ hl with hl | hl
    · exact Multiset.mem_add.mpr (.inl (Multiset.mem_add.mpr (.inl (hΔ _ hl))))
    · rcases Multiset.mem_add.mp hl with hl | hl
      · rw [add_assoc]
        exact Multiset.mem_add.mpr (.inr (by rw [← Ctx.vars_add]; exact Ctx.mem_vars.mpr hl))
      · exact absurd hl (loc_not_mem_ctx xs l)
  have hres := cont IH (m := m) (by omega) hys he₂ hadm2 h2
    (by rw [image_ren_locs (lzip_locRen _ _ hys) (h.locs_of_R hΔ)]; exact hΔ)
    (by rw [map_var_subst, hrd1, he₂σ]; exact hrest)
  have hs1' : HSteps sig H (.letIn xs e₁ e₂) H₁ (.letIn xs (.ret (ys.map .var)) e₂) :=
    hs1.ctx (.letIn xs .hole e₂)
  exact HeapResult.prepend (hs1'.trans (HSteps.head (HHead.letIn H₁ xs _ e₂
    (fun a ha => by obtain ⟨y, -, rfl⟩ := List.mem_map.mp ha; trivial)
    (by rw [hlen', List.length_map])))) hres hagR

/-! ## Calls -/

theorem LSubst.ren_congr {σ τ : LSubst} {y : Var} (h : σ y = τ y) : σ.ren y = τ.ren y := by
  simp only [LSubst.ren, h]

theorem ctx_ren_lzip_append (bs os : List Binder) (as1 : List LVal) (ys : List Var)
    (hnd : ((bs ++ os).map (·.name)).Nodup) (hl1 : bs.length = as1.length)
    (hl2 : os.length = ys.length) :
    (Binder.ctx os).map (Res.ren (lzip (bs ++ os) (as1 ++ ys.map .var))) =
      locCtx (ys.map .var) := by
  rw [List.map_append, List.nodup_append] at hnd
  rw [← ctx_ren_lzip os ys hnd.2.1 hl2]
  apply Multiset.map_congr rfl
  intro r hr
  simp only [Binder.ctx, Multiset.mem_coe, List.mem_map] at hr
  obtain ⟨b, hb, rfl⟩ := hr
  simp only [Res.ren]
  congr 1
  apply LSubst.ren_congr
  have hnm : Var.name b.name ∉ Binder.vars bs := by
    intro hm
    simp only [Binder.vars, List.mem_map] at hm
    obtain ⟨b', hb', he⟩ := hm
    injection he with he
    exact hnd.2.2 _ (List.mem_map_of_mem hb') _ (List.mem_map_of_mem hb) he
  have := lzip_append bs os as1 (ys.map .var) hl1 (.name b.name)
  rw [lzip_none_of_not_mem hnm] at this
  exact this

theorem borrow_vars {funs : List FName} {ys : List LVal} (hb : ∀ y ∈ ys, LBorrowArg funs Δ y)
    (ha : ∀ y ∈ ys, y.Adm) : ∃ bys : List Var, ys = bys.map .var ∧ ∀ y ∈ bys, y ∈ Δ := by
  induction ys with
  | nil => exact ⟨[], rfl, by simp⟩
  | cons y ys ih =>
    obtain ⟨bys, rfl, hbys⟩ :=
      ih (fun z hz => hb z (by simp [hz])) (fun z hz => ha z (by simp [hz]))
    have h1 := hb y (by simp)
    have h2 := ha y (by simp)
    cases y with
    | var z =>
      refine ⟨z :: bys, rfl, fun w hw => ?_⟩
      rcases List.mem_cons.mp hw with rfl | hw
      · exact h1
      · exact hbys w hw
    | fn g => cases h2
    | _ => exact h1.elim

theorem case_call (IH : ∀ m < n, HMainClaim sig m) (hsig : sig.Wf) (hsigA : sig.Adm)
    {f : FName} {ys : List LVal} {e : LExpr}
    (hys : ∀ y ∈ ys, LBorrowArg sig.funs Δ y) (he : LWf sig.funs Δ Γ e)
    (hadm : (LExpr.call f (.ret ys) e).Adm) (h : HInv sig.funs H R RC Γ σ)
    (hΔ : ∀ x ∈ Δ, x ∈ R)
    (hev : LStepsN sig n ((LExpr.call f (.ret ys) e).subst (locS σ)) (.ret vs)) :
    HeapResult sig H R RC (.call f (.ret ys) e) σ vs := by
  have hadmys : ∀ v ∈ ys, v.Adm := by
    cases hadm with | call _ _ _ h1 _ => cases h1; assumption
  have hadme : e.Adm := by cases hadm; assumption
  obtain ⟨bys, rfl, hbys⟩ := borrow_vars hys hadmys
  have hbloc : ∀ v ∈ bys.map LVal.var, v.IsLoc := by
    intro v hv
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hv
    obtain ⟨l, rfl⟩ := h.locs_of_R hΔ z (hbys z hz)
    exact ⟨l, rfl⟩
  simp only [LExpr.subst] at hev
  obtain ⟨k, w₂, hk, hev1, hev2⟩ := LStepsN.plug (.callO f _ .hole) hev
  simp only [LECtx.plug] at hev2
  obtain ⟨m, t, hm, hh, hrest⟩ :=
    LStepsN.head_of (fun _ hs => LStep.call_ret_ret hs) (by simp [LExpr.IsRet]) hev2
  cases hh with
  | call _ fd _ _ hlook hl1 hl2 =>
  obtain ⟨H₁, as, σ₁, hs1, hinv1, hag1, hrd1⟩ := IH k (by omega) he hadme h hΔ hev1
  have has := isLoc_of_locOnly hinv1.ctx
  have hfd := hsig fd (LSig.lookup_mem hlook)
  have hl1' : fd.borrowed.length = (bys.map LVal.var).length := by
    rw [hl1, LVal.substList_eq_map, List.length_map]
  have hl2' : fd.owned.length = as.length := by rw [hl2, ← hrd1, List.length_map]
  have hall : ∀ a ∈ bys.map LVal.var ++ as.map LVal.var, a.IsLoc := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hbloc a ha
    · exact has a ha
  have hbody : fd.body.subst (locS σ₁) = fd.body := by
    refine LExpr.subst_of_dfv _ fun y hy => ?_
    cases y with
    | name s => rfl
    | loc l =>
      rcases LWf.dfv_sub hfd.2 _ hy with hy | hy
      · exact absurd (List.mem_toFinset.mp hy) (loc_not_mem_vars _ l)
      · exact absurd hy (loc_not_mem_ctx _ l)
  have hargs : (bys.map LVal.var ++ as.map LVal.var).map (LVal.subst (locS σ₁)) =
      LVal.substList (locS σ) (bys.map LVal.var) ++ w₂ := by
    rw [List.map_append, map_var_subst, map_var_subst, hrd1, LVal.substList_eq_map,
      map_var_subst]
    congr 1
    apply List.map_congr_left
    intro z hz
    obtain ⟨l, rfl⟩ := h.locs_of_R hΔ z (hbys z hz)
    simp only [rd, LVal.subst, locS]
    rw [hag1 l (hΔ _ (hbys _ hz))]
  have hres := cont IH (m := m) (by omega) hall hfd.2 (hsigA fd (LSig.lookup_mem hlook))
    (by rw [ctx_ren_lzip_append _ _ _ _ hfd.1 hl1' hl2']; exact hinv1)
    (by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨v, hv, hlz⟩ := lzip_some_of_mem _ _ hl1' y (List.mem_toFinset.mp hy)
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hv
      have : lzip (fd.borrowed ++ fd.owned) (bys.map LVal.var ++ as.map LVal.var) y =
          some (.var z) := by
        rw [lzip_append _ _ _ _ hl1', hlz]
      simp only [LSubst.ren, this]
      exact hΔ z (hbys z hz))
    (by rw [hbody, hargs]; exact hrest)
  have hs1' : HSteps sig H (.call f (.ret (bys.map LVal.var)) e) H₁
      (.call f (.ret (bys.map LVal.var)) (.ret (as.map .var))) := hs1.ctx (.callO f _ .hole)
  exact HeapResult.prepend (hs1'.trans (HSteps.head (HHead.call H₁ f fd _ _ hlook
    (fun a ha => by obtain ⟨l, rfl⟩ := hall a ha; trivial) hl1'
    (by rw [hl2', List.length_map])))) hres hag1

end FIPNamed.Lam
