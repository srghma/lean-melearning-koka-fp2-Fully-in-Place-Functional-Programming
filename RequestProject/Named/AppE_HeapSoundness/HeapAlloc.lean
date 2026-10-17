module

public import RequestProject.Named.AppE_HeapSoundness.HeapOps

@[expose] public section

/-!
# Allocating values in the heap (Theorem 6)

A well-formed tuple of values is evaluated by the heap semantics into a tuple of locations,
allocating a cell for every constructor (reusing a credit, or for free for an atom) and
for every lambda (*lam_h*); the invariant is preserved and the new locations denote the
values.
-/

namespace FIPNamed.Lam

variable {sig : LSig} {funs : List FName} {R : Multiset Var} {RC : Multiset Nat}

/-! ## Value contexts -/

/-- Composition of value contexts. -/
def LVCtx.comp : LVCtx → LVCtx → LVCtx
  | .hole, W => W
  | .ctor c done V rest, W => .ctor c done (V.comp W) rest

theorem LVCtx.plug_comp : ∀ (V W : LVCtx) (v : LVal), (V.comp W).plug v = V.plug (W.plug v)
  | .hole, _, _ => rfl
  | .ctor c done V rest, W, v => by simp [LVCtx.comp, LVCtx.plug, LVCtx.plug_comp V W v]

theorem LVCtx.Ok.comp : ∀ {V W : LVCtx}, V.Ok → W.Ok → (V.comp W).Ok
  | .hole, _, _, hW => hW
  | .ctor _ _ _ _, _, ⟨hd, hV⟩, hW => ⟨hd, LVCtx.Ok.comp hV hW⟩

/-- `L` places a list of values at a position where the heap semantics evaluates them from
    left to right. -/
def PosOK (L : List LVal → LExpr) : Prop :=
  ∀ (pre post : List LVal), (∀ a ∈ pre, a.Atomic) → ∃ (E : LECtx) (done : List LVal)
    (V : LVCtx) (rest : List LVal), (∀ a ∈ done, a.Atomic) ∧ V.Ok ∧
    ∀ w, L (pre ++ w :: post) = E.plug (.ret (done ++ V.plug w :: rest))

theorem PosOK.ret (E : LECtx) (done : List LVal) (hd : ∀ a ∈ done, a.Atomic) :
    PosOK fun xs => E.plug (.ret (done ++ xs)) := by
  unfold PosOK
  intro pre post hpre
  refine ⟨E, done ++ pre, .hole, post, ?_, trivial, fun w => by simp [LVCtx.plug]⟩
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · exact hd a ha
  · exact hpre a ha

theorem PosOK.ctor (E : LECtx) (done : List LVal) (V : LVCtx) (rest : List LVal) (c : CName)
    (hd : ∀ a ∈ done, a.Atomic) (hV : V.Ok) :
    PosOK fun xs => E.plug (.ret (done ++ V.plug (.ctor c xs) :: rest)) := by
  unfold PosOK
  intro pre post hpre
  refine ⟨E, done, V.comp (.ctor c pre .hole post), rest, hd, hV.comp ⟨hpre, trivial⟩,
    fun w => ?_⟩
  rw [LVCtx.plug_comp]; rfl

theorem PosOK.cons {L : List LVal → LExpr} (h : PosOK L) (y : Var) :
    PosOK fun xs => L (.var y :: xs) := by
  unfold PosOK
  intro pre post hpre
  obtain ⟨E, done, V, rest, hd, hV, hL⟩ := h (.var y :: pre) post (by
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · trivial
    · exact hpre a ha)
  exact ⟨E, done, V, rest, hd, hV, fun w => by rw [← hL w]; rfl⟩

/-! ## Free variables of values -/

mutual
theorem LWfVal.dfv_ctx : ∀ {Δ : Finset Var} {Γ : Ctx} {v : LVal},
    LWfVal funs Δ Γ v → ∀ y ∈ v.dfv, Res.var y ∈ Γ
  | _, _, _, .var x, y, hy => by simp [LVal.dfv] at hy; subst hy; simp
  | _, _, _, .atom c, y, hy => by simp [LVal.dfv, LVal.dfvList] at hy
  | _, _, _, .reuse c vs Γ _ hvs, y, hy => by
    simp only [LVal.dfv] at hy
    exact Multiset.mem_add.mpr (.inl (LWfVals.dfv_ctx hvs y hy))
  | _, _, _, .lam zs xs e hwf hzs, y, hy => by
    rcases LWfVal.dfv_sub (LWfVal.lam (funs := funs) (Δ := ∅) zs xs e hwf hzs) y hy with h | h
    · simp at h
    · exact h
theorem LWfVals.dfv_ctx : ∀ {Δ : Finset Var} {Γ : Ctx} {vs : List LVal},
    LWfVals funs Δ Γ vs → ∀ y ∈ LVal.dfvList vs, Res.var y ∈ Γ
  | _, _, _, .nil, y, hy => by simp [LVal.dfvList] at hy
  | _, _, _, .cons Γ₁ Γ₂ v vs hv hvs, y, hy => by
    simp only [LVal.dfvList, List.mem_append] at hy
    rcases hy with hy | hy
    · exact Multiset.mem_add.mpr (.inl (LWfVal.dfv_ctx hv y hy))
    · exact Multiset.mem_add.mpr (.inr (LWfVals.dfv_ctx hvs y hy))
end

theorem LVal.fvList_map_var (ys : List Var) : LVal.fvList (ys.map .var) = ys := by
  induction ys with
  | nil => rfl
  | cons y ys ih => simp [LVal.fvList, LVal.fv, ih]

theorem locCtx_cons_var (y : Var) (vs : List LVal) :
    locCtx (.var y :: vs) = {Res.var y} + locCtx vs := by
  simp [locCtx, LVal.fvList, LVal.fv]

theorem varCtx_eq_locCtx (zs : List Var) : varCtx zs = locCtx (zs.map .var) := by
  rw [locCtx_map]; simp [varCtx]

theorem exists_locs {zs : List Var} (h : ∀ z ∈ zs, ∃ l, z = .loc l) :
    ∃ ls : List Nat, zs = ls.map .loc := by
  induction zs with
  | nil => exact ⟨[], rfl⟩
  | cons z zs ih =>
    obtain ⟨l, rfl⟩ := h z (by simp)
    obtain ⟨ls, rfl⟩ := ih (fun w hw => h w (by simp [hw]))
    exact ⟨l :: ls, rfl⟩

/-- The readback of a variable. -/
abbrev rd (σ : Nat → Option LVal) (y : Var) : LVal := (LVal.var y).subst (locS σ)

/-! ## Allocation -/

mutual
theorem allocVal : ∀ {Δ : Finset Var} {Γv : Ctx} {v : LVal}, LWfVal funs Δ Γv v → v.Adm →
    ∀ {H : Heap} {Γ₀ : Ctx} {σ : Nat → Option LVal}, HInv funs H R RC (Γ₀ + Γv) σ →
    ∃ (H' : Heap) (y : Var) (σ' : Nat → Option LVal), (∀ (E : LECtx) (done : List LVal) (V : LVCtx) (rest : List LVal),
        (∀ a ∈ done, a.Atomic) → V.Ok →
        HSteps sig H (E.plug (.ret (done ++ V.plug v :: rest))) H'
          (E.plug (.ret (done ++ V.plug (.var y) :: rest)))) ∧
      HInv funs H' R RC (Γ₀ + {Res.var y}) σ' ∧ (∀ x ∈ H.dom, x ∈ H'.dom) ∧
      (∀ l, Var.loc l ∈ H.dom → σ' l = σ l) ∧ rd σ' y = v.subst (locS σ)
  | _, _, _, .var x, _, H, Γ₀, σ, h =>
    ⟨H, x, σ, fun _ _ _ _ _ _ => .refl _ _, h, fun _ hx => hx, fun _ _ => rfl, rfl⟩
  | _, _, _, .atom c, _, H, Γ₀, σ, h => by
    obtain ⟨l, hl⟩ := exists_fresh H
    have h0 : HInv funs H R RC (Γ₀ + locCtx []) σ := by simpa [locCtx, LVal.fvList] using h
    have h1 := h0.addCell (o := .con c []) (fun a ha => by simp at ha) rfl hl
    refine ⟨_, .loc l, _, fun E done V rest hd hV => .single (.val E done V rest hd hV
      (HValHead.atom H c l hl)), h1, fun x hx => by simp [hx], fun m hm => ?_, ?_⟩
    · rw [Function.update_of_ne]; rintro rfl; exact hl hm
    · simp [rd, LVal.subst, locS, HObj.toVal, LVal.substList]
  | _, _, _, .reuse c vs Γa hne hvs, hadm, H, Γ₀, σ, h => by
    have hadm' : ∀ v ∈ vs, v.Adm := by cases hadm; assumption
    have h0 : HInv funs H R RC (Γ₀ + {Res.credit vs.length} + Γa) σ := by
      have : Γ₀ + (Γa + {Res.credit vs.length}) = Γ₀ + {Res.credit vs.length} + Γa := by abel
      rwa [this] at h
    obtain ⟨H₁, ys, σ₁, hs1, h1, hdom1, hag1, hrd1⟩ := allocVals hvs hadm' h0
    have hlen : ys.length = vs.length := by
      have := congrArg List.length hrd1; simpa using this
    have h1' : HInv funs H₁ R RC (Γ₀ + locCtx (ys.map .var) + {Res.credit vs.length}) σ₁ := by
      have : Γ₀ + {Res.credit vs.length} + locCtx (ys.map .var) =
          Γ₀ + locCtx (ys.map .var) + {Res.credit vs.length} := by abel
      rwa [this] at h1
    have hk : 1 ≤ vs.length := by
      cases vs with
      | nil => exact absurd rfl hne
      | cons _ _ => simp
    obtain ⟨H₂, rfl, h2⟩ := h1'.takeCredit hk
    obtain ⟨l, hl⟩ := exists_fresh H₂
    have hok : (HObj.con c (ys.map .var)).Ok funs := by
      intro a ha
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ha
      have : y ∈ H₂.cntM := h2.vars_cntM (x := y) (by
        rw [Ctx.vars_add, locCtx_vars, LVal.fvList_map_var]
        simp [hy])
      obtain ⟨l', -, -, rfl, -⟩ := h2.loc_of_cntM this
      exact ⟨l', rfl⟩
    have h3 := h2.addCell hok rfl hl
    have hne' : ys.map LVal.var ≠ [] := by
      intro h'; apply hne; rw [← List.length_eq_zero_iff, ← hlen, ← List.length_map (f := LVal.var), h']
      rfl
    refine ⟨_, .loc l, _, fun E done V rest hd hV => ?_, h3, ?_, ?_, ?_⟩
    · refine (hs1 _ (PosOK.ctor E done V rest c hd hV)).trans (.single ?_)
      have := HStep.val (sig := sig) E done V rest hd hV
        (HValHead.reuse H₂ c (ys.map .var) l hne' (fun a ha => by
          obtain ⟨y, -, rfl⟩ := List.mem_map.mp ha; trivial) hl)
      rw [List.length_map, hlen] at this
      exact this
    · intro x hx
      have := hdom1 x hx
      simp only [Heap.dom_add, Heap.dom_credit, zero_add] at this
      simp [this]
    · intro m hm
      have hml : m ≠ l := by
        rintro rfl; apply hl
        have := hdom1 _ hm
        simpa using this
      rw [Function.update_of_ne hml, hag1 m hm]
    · simp only [rd, LVal.subst, locS, Function.update_self, Option.getD_some, HObj.toVal]
      rw [LVal.substList_eq_map, LVal.substList_eq_map, List.map_map]
      congr 1
  | _, _, _, .lam zs xs e hwf hzs, hadm, H, Γ₀, σ, h => by
    have hadm' : e.Adm := by cases hadm; assumption
    have hnd : (xs.map (·.name)).Nodup := by cases hadm; assumption
    have hz : ∀ z ∈ zs, ∃ l, z = .loc l := by
      intro z hz
      rcases h.ctx (.var z) (Multiset.mem_add.mpr (.inr (by simp [varCtx, hz]))) with
        ⟨l, hl⟩ | ⟨k, hk⟩
      · exact ⟨l, by injection hl⟩
      · cases hk
    obtain ⟨ls, rfl⟩ := exists_locs hz
    obtain ⟨l, hl⟩ := exists_fresh H
    have h0 : HInv funs H R RC (Γ₀ + locCtx ((ls.map Var.loc).map .var)) σ := by
      rwa [← varCtx_eq_locCtx]
    have hok : (HObj.clo ((ls.map Var.loc).map .var) xs e).Ok funs :=
      ⟨ls, by simp, hwf, hadm', hnd⟩
    have h1 := h0.addCell hok rfl hl
    refine ⟨_, .loc l, _, fun E done V rest hd hV => .single (.val E done V rest hd hV
      (HValHead.lam H _ xs e l (fun a ha => by
        obtain ⟨y, -, rfl⟩ := List.mem_map.mp ha; trivial) hl)), h1,
      fun x hx => by simp [hx], fun m hm => ?_, ?_⟩
    · rw [Function.update_of_ne]; rintro rfl; exact hl hm
    · simp [rd, LVal.subst, locS, HObj.toVal]
theorem allocVals : ∀ {Δ : Finset Var} {Γv : Ctx} {vs : List LVal}, LWfVals funs Δ Γv vs →
    (∀ v ∈ vs, v.Adm) →
    ∀ {H : Heap} {Γ₀ : Ctx} {σ : Nat → Option LVal}, HInv funs H R RC (Γ₀ + Γv) σ →
    ∃ (H' : Heap) (ys : List Var) (σ' : Nat → Option LVal), (∀ L, PosOK L → HSteps sig H (L vs) H' (L (ys.map .var))) ∧
      HInv funs H' R RC (Γ₀ + locCtx (ys.map .var)) σ' ∧ (∀ x ∈ H.dom, x ∈ H'.dom) ∧
      (∀ l, Var.loc l ∈ H.dom → σ' l = σ l) ∧ ys.map (rd σ') = vs.map (LVal.subst (locS σ))
  | _, _, _, .nil, _, H, Γ₀, σ, h =>
    ⟨H, [], σ, fun _ _ => .refl _ _, by simpa [locCtx, LVal.fvList] using h,
      fun _ hx => hx, fun _ _ => rfl, rfl⟩
  | _, _, _, .cons Γ₁ Γ₂ v vs hv hvs, hadm, H, Γ₀, σ, h => by
    have h0 : HInv funs H R RC (Γ₀ + Γ₂ + Γ₁) σ := by
      have : Γ₀ + (Γ₁ + Γ₂) = Γ₀ + Γ₂ + Γ₁ := by abel
      rwa [this] at h
    obtain ⟨H₁, y, σ₁, hs1, h1, hdom1, hag1, hrd1⟩ := allocVal hv (hadm v (by simp)) h0
    have h1' : HInv funs H₁ R RC (Γ₀ + {Res.var y} + Γ₂) σ₁ := by
      have : Γ₀ + Γ₂ + {Res.var y} = Γ₀ + {Res.var y} + Γ₂ := by abel
      rwa [this] at h1
    obtain ⟨H₂, ys, σ₂, hs2, h2, hdom2, hag2, hrd2⟩ :=
      allocVals hvs (fun w hw => hadm w (by simp [hw])) h1'
    have hyc : y ∈ H₁.cntM := h1.vars_cntM (x := y) (by simp [Ctx.vars_add])
    have hy : y ∈ H₁.dom := Heap.mem_dom_of_cntM hyc
    obtain ⟨ly, -, -, rfl, -⟩ := h1.loc_of_cntM hyc
    refine ⟨H₂, .loc ly :: ys, σ₂, fun L hL => ?_, ?_, fun x hx => hdom2 x (hdom1 x hx),
      fun m hm => by rw [hag2 m (hdom1 _ hm), hag1 m hm], ?_⟩
    · obtain ⟨E, done, V, rest, hd, hV, hLw⟩ := hL [] vs (by simp)
      have e1 := hs1 E done V rest hd hV
      rw [← hLw, ← hLw] at e1
      exact e1.trans (hs2 _ (hL.cons (.loc ly)))
    · rw [List.map_cons, locCtx_cons_var, ← add_assoc]; exact h2
    · rw [List.map_cons, List.map_cons, hrd2]
      congr 1
      · rw [← hrd1]; simp only [rd, LVal.subst, locS]; rw [hag2 ly hy]
      · apply List.map_congr_left
        intro w hw
        apply LVal.subst_congr
        intro z hz
        have hz' : Res.var z ∈ Γ₂ := LWfVals.dfv_ctx hvs z
          (LVal.mem_dfvList.mpr ⟨w, hw, hz⟩)
        have hzc : z ∈ H.cntM := h.vars_cntM (by
          rw [Ctx.vars_add, Ctx.vars_add]
          exact Multiset.mem_add.mpr (.inr (Multiset.mem_add.mpr (.inr (Ctx.mem_vars.mpr hz')))))
        obtain ⟨lz, -, -, rfl, -⟩ := h.loc_of_cntM hzc
        exact hag1 lz (Heap.mem_dom_of_cntM hzc)
end

end FIPNamed.Lam
