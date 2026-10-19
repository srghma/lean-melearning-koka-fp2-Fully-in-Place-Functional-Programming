module

public import RequestProject.AppE_HeapSoundness.HeapLocs

@[expose] public section

/-!
# Allocating values in the heap semantics

A well-formed tuple of values `(v₁, …, vₖ)` is evaluated by the heap semantics to a tuple of
locations, allocating its constructors (reusing their credits) and its lambdas from the
inside out and from left to right (`LWfVals.alloc`).  Each value consumes its owned
resources and becomes a single root, and denotes the same closed value as before.
-/

namespace FIP.Lam

variable {sig : LSig}

/-- The location of a variable of scope `0`. -/
def _root_.FIP.Var.toLoc : Var 0 → Nat
  | .loc l => l
  | .bvar i => i.elim0

@[simp] theorem Var.loc_toLoc (x : Var 0) : Var.loc x.toLoc = x := by
  cases x with
  | loc l => rfl
  | bvar i => exact i.elim0

/-- The borrowed environment of a value is irrelevant. -/
theorem LWfVals.anyΔ {funs : List FName} {n : Nat} {Δ : Finset (Var n)} {Γ : Ctx n}
    {vs : List (LVal n)} (h : LWfVals funs Δ Γ vs) (Δ' : Finset (Var n)) :
    LWfVals funs Δ' Γ vs := by
  induction h using LWfVals.rec
    (motive_1 := @fun n Δ Γ v _ => ∀ Δ' : Finset (Var n), LWfVal funs Δ' Γ v)
    (motive_3 := @fun _ _ _ _ _ => True) with
  | var x => exact .var x
  | atom c => exact .atom c
  | reuse c vs Γ hne hvs ih => exact .reuse c vs Γ hne (ih _)
  | lam zs c k e hc he _ => exact .lam zs c k e hc he
  | nil => exact .nil
  | cons Γ₁ Γ₂ v vs hv hvs ih₁ ih₂ => exact .cons Γ₁ Γ₂ v vs (ih₁ _) (ih₂ _)
  | _ => trivial

/-- The locations of well-formed values, after a substitution of locations, are owned. -/
theorem LWfVals.locs_ren {funs : List FName} {m : Nat} {Δ : Finset (Var m)} {Γ : Ctx m}
    {vs : List (LVal m)} (h : LWfVals funs Δ Γ vs) (ρ : Fin m → Nat) :
    ∀ v ∈ vs, ∀ l ∈ (v.subst (LSubst.locs ρ)).locs, Res.var (.loc l) ∈ Ctx.ren ρ Γ := by
  intro v hv l hl
  have ht : LWf funs ∅ Γ (.ret (LVals.ofList vs)) :=
    LWf.tuple _ (by simpa using h.anyΔ ∅)
  have : l ∈ ((LExpr.ret (LVals.ofList vs)).subst (LSubst.locs ρ)).locs := by
    simp only [LExpr.subst, LExpr.locs, LVals.locs_eq, LVals.toList_subst, LVals.toList_ofList,
      List.mem_flatMap, List.mem_map]
    exact ⟨_, ⟨v, hv, rfl⟩, hl⟩
  obtain ⟨x, hx, hxe⟩ := ht.locs_ren ρ this
  rcases hx with hx | hx
  · simp at hx
  · rw [← hxe]
    exact Multiset.mem_map.mpr ⟨_, hx, rfl⟩

/-- A position for a list of values, in which the heap semantics allocates values. -/
def ListPos (sig : LSig) (L : List (LVal 0) → LExpr 0) : Prop :=
  ∀ (pre rest : List (LVal 0)), (∀ a ∈ pre, a.Atomic) → ∀ (V : LVCtx), V.Ok →
    ∀ {H H' : Heap} {v v' : LVal 0}, HValHead H v H' v' →
      HStep sig H (L (pre ++ V.plug v :: rest)) H' (L (pre ++ V.plug v' :: rest))

theorem ListPos.ret (E : LECtx) : ListPos sig (fun ws => E.plug (.ret (LVals.ofList ws))) :=
  fun pre rest hpre V hV _ _ _ _ h => HStep.val E pre V rest hpre hV h

theorem ListPos.ctor {L : List (LVal 0) → LExpr 0} (hL : ListPos sig L) (pre rest : List (LVal 0))
    (hpre : ∀ a ∈ pre, a.Atomic) (c : CName) :
    ListPos sig (fun ws => L (pre ++ .ctor c (LVals.ofList ws) :: rest)) :=
  fun pre' rest' hpre' V hV _ _ _ _ h => hL pre rest hpre (.ctor c pre' V rest') ⟨hpre', hV⟩ h

theorem ListPos.step {L : List (LVal 0) → LExpr 0} (hL : ListPos sig L) {pre rest : List (LVal 0)}
    (hpre : ∀ a ∈ pre, a.Atomic) {H H' : Heap} {v v' : LVal 0} (h : HValHead H v H' v') :
    HStep sig H (L (pre ++ v :: rest)) H' (L (pre ++ v' :: rest)) :=
  hL pre rest hpre .hole trivial h

theorem locV_atomic (l : Nat) : (locV l).Atomic := trivial

theorem locs_atomic (ls : List Nat) : ∀ a ∈ ls.map locV, a.Atomic := by
  intro a ha; simp only [List.mem_map] at ha; obtain ⟨l, -, rfl⟩ := ha; trivial

theorem nzCtx_ren_varCtx {m : Nat} (ρ : Fin m → Nat) (zs : List (Var m)) :
    nzCtx (Ctx.ren ρ (varCtx zs)) = locsCtx (zs.map fun z => (z.ren ρ).toLoc) := by
  simp only [varCtx, Ctx.ren, Multiset.map_coe, List.map_map, locsCtx]
  rw [nzCtx]
  rw [Multiset.filter_eq_self.mpr (by
    intro a ha; simp only [Multiset.mem_coe, List.mem_map] at ha
    obtain ⟨_, _, rfl⟩ := ha; simp [Res.ren])]
  congr 1
  apply List.map_congr_left
  intro z _
  simp [Res.ren]

/-- **Allocation of well-formed values** (from left to right, inside out). -/
theorem LWfVals.alloc {n : Nat} {Δ : Finset (Var n)} {Γ : Ctx n} {vs : List (LVal n)}
    (h : LWfVals sig.funs Δ Γ vs) :
    ∀ (ρ : Fin n → Nat) {L : List (LVal 0) → LExpr 0}, ListPos sig L →
    ∀ (pre rest : List (LVal 0)), (∀ a ∈ pre, a.Atomic) →
    ∀ {H : Heap} {σ : Nat → Option (LVal 0)} {A : Ctx 0},
      (∀ v ∈ vs, v.Adm) → HInv sig.funs H σ → H.roots = nzCtx (Ctx.ren ρ Γ) + A →
      ∃ (H' : Heap) (ls : List Nat) (σ' : Nat → Option (LVal 0)),
        HSteps sig H (L (pre ++ vs.map (LVal.subst (LSubst.locs ρ)) ++ rest)) H'
          (L (pre ++ ls.map locV ++ rest)) ∧
        HInv sig.funs H' σ' ∧ SubstExt σ σ' ∧ H'.roots = locsCtx ls + A ∧
        ls.map (fun l => (locV l).substLoc σ') =
          vs.map (fun v => (v.subst (LSubst.locs ρ)).substLoc σ) := by
  induction h using LWfVals.rec
    (motive_1 := @fun n Δ Γ v _ =>
      ∀ (ρ : Fin n → Nat) {L : List (LVal 0) → LExpr 0}, ListPos sig L →
      ∀ (pre rest : List (LVal 0)), (∀ a ∈ pre, a.Atomic) →
      ∀ {H : Heap} {σ : Nat → Option (LVal 0)} {A : Ctx 0},
        v.Adm → HInv sig.funs H σ → H.roots = nzCtx (Ctx.ren ρ Γ) + A →
        ∃ (H' : Heap) (l : Nat) (σ' : Nat → Option (LVal 0)),
          HSteps sig H (L (pre ++ v.subst (LSubst.locs ρ) :: rest)) H'
            (L (pre ++ locV l :: rest)) ∧
          HInv sig.funs H' σ' ∧ SubstExt σ σ' ∧ H'.roots = {Res.var (.loc l)} + A ∧
          (locV l).substLoc σ' = (v.subst (LSubst.locs ρ)).substLoc σ)
    (motive_3 := @fun _ _ _ _ _ => True) with
  | var x =>
    rename_i ρ L hL pre rest hpre H σ A hadm hH hroots
    obtain ⟨l, hl⟩ := Var.zero_eq_loc (x.ren ρ)
    refine ⟨H, l, σ, ?_, hH, SubstExt.refl σ, ?_, ?_⟩
    · rw [LVal.subst_locs_var, hl]; exact .refl _ _
    · rw [hroots]; simp [Res.ren, hl]
    · rw [LVal.subst_locs_var, hl]
  | atom c =>
    rename_i ρ L hL pre rest hpre H σ A hadm hH hroots
    obtain ⟨N, hN, hNd⟩ := hH.exists_fresh
    have hok : (HObj.con c []).Ok sig.funs := by simp [HObj.Ok]
    have hfv : (HObj.con c []).fvCtx = 0 := rfl
    obtain ⟨hH', hext⟩ := hH.alloc hN hok (by rw [hfv]; exact Multiset.zero_le _)
    refine ⟨_, N, _, HSteps.single (hL.step hpre (HValHead.atom H c N hNd)), hH', hext, ?_, ?_⟩
    · have := Heap.roots_alloc hH.linear hNd (o := HObj.con c []) (by rw [hfv]; exact Multiset.zero_le _)
      rw [hfv, add_zero] at this
      rw [this, hroots]; simp [add_comm]
    · rw [locV_substLoc _ N _ (Function.update_self _ _ _)]
      simp [HObj.toVal, LVal.subst, LVals.subst, LVal.substLoc, LVals.substLoc, LVals.ofList]
  | reuse c vs Γ hne hvs ih =>
    rename_i ρ L hL pre rest hpre H σ A hadm hH hroots
    have hk : vs.length ≠ 0 := by
      intro h0; apply hne
      cases vs with
      | nil => rfl
      | cons v vs => simp at h0
    have hroots' : H.roots = nzCtx (Ctx.ren ρ Γ) + ({Res.credit vs.length} + A) := by
      rw [hroots, Ctx.ren_add, Ctx.ren_singleton, nzCtx_add]
      simp only [Res.ren]; rw [nzCtx_credit hk]; abel
    obtain ⟨H₁, ls, σ₁, hs₁, hH₁, hext₁, hr₁, hv₁⟩ :=
      ih ρ (hL.ctor pre rest hpre c) [] [] (by simp) (LVals.adm_iff vs |>.mp hadm) hH hroots'
    simp only [List.nil_append, List.append_nil] at hs₁
    have hlen : ls.length = vs.length := by
      have := congrArg List.length hv₁; simpa using this
    -- the credit is in the heap
    have hcr : HCell.credit vs.length ∈ H₁ :=
      Heap.credit_mem_of_root (by rw [hr₁]; simp)
    obtain ⟨H₁', rfl⟩ := Multiset.exists_cons_of_mem hcr
    rw [← Multiset.singleton_add] at hH₁ hr₁ hs₁
    have hH₁' := hH₁.remove_credit
    have hr₁' : Heap.roots H₁' = locsCtx ls + A := by
      have := Heap.roots_credit hH₁'.linear vs.length
      rw [nzCtx_credit hk, hr₁] at this
      have : locsCtx ls + A + {Res.credit vs.length} = Heap.roots H₁' + {Res.credit vs.length} := by
        rw [add_comm (Heap.roots H₁'), ← this]; abel
      exact (add_right_cancel this).symm
    obtain ⟨N, hN, hNd⟩ := hH₁'.exists_fresh
    have hok : (HObj.con c (ls.map locV)).Ok sig.funs := by
      simp only [HObj.Ok, List.mem_map]; rintro a ⟨l, -, rfl⟩; exact ⟨l, rfl⟩
    have hfv : (HObj.con c (ls.map locV)).fvCtx = locsCtx ls := by
      simp [HObj.fvCtx, HObj.fv, LVal.fvList_locs, locsCtx, List.map_map]; rfl
    have hle : (HObj.con c (ls.map locV)).fvCtx ≤ Heap.roots H₁' := by
      rw [hfv, hr₁']; exact Multiset.le_add_right _ _
    obtain ⟨hH₂, hext₂⟩ := hH₁'.alloc hN hok hle
    have hne' : LVals.ofList (ls.map locV) ≠ .nil := by
      intro h0
      have := congrArg LVals.toList h0
      simp only [LVals.toList_ofList, LVals.toList_nil, List.map_eq_nil_iff] at this
      subst this; exact hk (by simp at hlen; omega)
    have hlen' : (LVals.ofList (ls.map locV)).length = vs.length := by
      unfold LVals.length; simp only [LVals.toList_ofList, List.length_map]; exact hlen
    have hsubst : (LVal.ctor c vs).subst (LSubst.locs ρ) =
        .ctor c (LVals.ofList (vs.toList.map (LVal.subst (LSubst.locs ρ)))) := by
      rw [← LVals.toList_subst, LVals.ofList_toList]; rfl
    have hstep := hL.step (pre := pre) (rest := rest) hpre
      (HValHead.reuse H₁' c (LVals.ofList (ls.map locV)) N hne'
        (by simpa using locs_atomic ls) hNd)
    rw [hlen'] at hstep
    simp only [LVals.toList_ofList] at hstep
    rw [hsubst]
    refine ⟨_, N, _, hs₁.tail hstep, hH₂, hext₁.trans hext₂, ?_, ?_⟩
    · have h2 := Heap.roots_alloc hH₁'.linear hNd hle
      rw [hfv, hr₁'] at h2
      exact add_right_cancel (b := locsCtx ls) (h2.trans (by abel))
    · rw [locV_substLoc _ N _ (Function.update_self _ _ _)]
      simp only [HObj.toVal, LVal.substLoc, LVals.substLoc_ofList, List.map_map]
      congr 2
  | lam zs c k e hc he _ =>
    rename_i ρ L hL pre rest hpre H σ A hadm hH hroots
    set ls := zs.map fun z => (z.ren ρ).toLoc with hls
    have hzs : (LVals.ofList (zs.map LVal.var)).subst (LSubst.locs ρ) =
        LVals.ofList (ls.map locV) := by
      simp only [LVals.subst_ofList, List.map_map, hls]
      congr 1
      apply List.map_congr_left
      intro z _
      simp [LVal.subst_locs_var]
    have hsub : (LVal.lam (LVals.ofList (zs.map LVal.var)) c k e).subst (LSubst.locs ρ) =
        .lam (LVals.ofList (ls.map locV)) c k e := by
      rw [← hzs]; rfl
    rw [nzCtx_ren_varCtx, ← hls] at hroots
    obtain ⟨N, hN, hNd⟩ := hH.exists_fresh
    have hok : (HObj.clo (ls.map locV) c k e).Ok sig.funs := by
      refine ⟨?_, by simp [hls, hc], he, hadm.2⟩
      simp only [List.mem_map]; rintro a ⟨l, -, rfl⟩; exact ⟨l, rfl⟩
    have hfv : (HObj.clo (ls.map locV) c k e).fvCtx = locsCtx ls := by
      simp [HObj.fvCtx, HObj.fv, LVal.fvList_locs, locsCtx, List.map_map]; rfl
    have hle : (HObj.clo (ls.map locV) c k e).fvCtx ≤ H.roots := by
      rw [hfv, hroots]; exact Multiset.le_add_right _ _
    obtain ⟨hH', hext⟩ := hH.alloc hN hok hle
    have hstep := hL.step (pre := pre) (rest := rest) hpre
      (HValHead.lam H (LVals.ofList (ls.map locV)) c k e N
        (by simpa using locs_atomic ls) hNd)
    simp only [LVals.toList_ofList] at hstep
    rw [hsub]
    refine ⟨_, N, _, HSteps.single hstep, hH', hext, ?_, ?_⟩
    · have h2 := Heap.roots_alloc hH.linear hNd hle
      rw [hfv, hroots] at h2
      exact add_right_cancel (b := locsCtx ls) (h2.trans (by abel))
    · rw [locV_substLoc _ N _ (Function.update_self _ _ _)]
      simp [HObj.toVal, LVal.substLoc, LVals.substLoc_ofList]
  | nil =>
    intro ρ L hL pre rest hpre H σ A hadm hH hroots
    exact ⟨H, [], σ, by simpa using HSteps.refl H _, hH, SubstExt.refl σ, by simpa using hroots, rfl⟩
  | cons Γ₁ Γ₂ v vs hv hvs ih₁ ih₂ =>
    intro ρ L hL pre rest hpre H σ A hadm hH hroots
    have hroots₁ : H.roots = nzCtx (Ctx.ren ρ Γ₁) + (nzCtx (Ctx.ren ρ Γ₂) + A) := by
      rw [hroots]; simp; abel
    obtain ⟨H₁, l, σ₁, hs₁, hH₁, hext₁, hr₁, hv₁⟩ :=
      ih₁ ρ hL pre (vs.map (LVal.subst (LSubst.locs ρ)) ++ rest) hpre (hadm v (by simp)) hH hroots₁
    have hr₁' : H₁.roots = nzCtx (Ctx.ren ρ Γ₂) + ({Res.var (.loc l)} + A) := by
      rw [hr₁]; abel
    obtain ⟨H₂, ls, σ₂, hs₂, hH₂, hext₂, hr₂, hv₂⟩ :=
      ih₂ ρ hL (pre ++ [locV l]) rest (by
        intro a ha; simp only [List.mem_append, List.mem_singleton] at ha
        rcases ha with ha | rfl
        · exact hpre a ha
        · trivial) (fun w hw => hadm w (by simp [hw])) hH₁ hr₁'
    refine ⟨H₂, l :: ls, σ₂, ?_, hH₂, hext₁.trans hext₂, ?_, ?_⟩
    · simp only [List.map_cons, List.append_assoc, List.cons_append]
        at hs₁ hs₂ ⊢
      exact hs₁.trans hs₂
    · rw [hr₂]; simp
    · simp only [List.map_cons, List.cons.injEq]
      obtain ⟨w, hw⟩ := hH₁.some_of_root (l := l) (by rw [hr₁]; simp)
      refine ⟨?_, ?_⟩
      · rw [← hv₁, locV_substLoc _ l w hw, locV_substLoc _ l w (hext₂ l w hw)]
      · rw [hv₂]
        apply List.map_congr_left
        intro u hu
        apply LVal.substLoc_congr
        intro l' hl'
        have hmem := hvs.locs_ren ρ u hu l' hl'
        have : Res.var (.loc l') ∈ H.roots := by
          rw [hroots]
          refine Multiset.mem_add.mpr (.inl ?_)
          simp only [Ctx.ren_add, nzCtx_add]
          refine Multiset.mem_add.mpr (.inr ?_)
          exact Multiset.mem_filter.mpr ⟨hmem, by simp⟩
        obtain ⟨w', hw'⟩ := hH.some_of_root this
        rw [hext₁ l' w' hw', hw']
  | _ => trivial

end FIP.Lam
