module

public import RequestProject.AppB_StoreSoundness.StoreSoundCases

@[expose] public section

/-!
# The cases of the proof of Theorem 1 that bind variables, and deallocation

`let`, `match` and `match!` extend the substitution `ρ` by the locations bound by their
binders (`Subst.inst`); `drop` and `free` release memory.
-/

namespace FIP

variable {sig : Sig} {fbip : Bool}

theorem Vars.shift_empty {m : Nat} (k : Nat) : Vars.shift k (∅ : Finset (Var m)) = ∅ := by
  simp [Vars.shift]

theorem scalars_empty {m : Nat} {xs : List Bool} (hall : xs.all (!·) = true) :
    Vars.shift xs.length (∅ : Finset (Var m)) ∪ Binder.scalars xs = ∅ := by
  simp [Vars.shift_empty, Binder.scalars_of_all hall]

/-- Matching a substituted, location-substituted list of branches. -/
theorem Branches.find_subst_inv {m : Nat} {σ : Nat → Option (Val 0)} {ρ : Fin m → Val 0}
    {bs : Branches m} {c : CName} {k : Nat} {b : Branch 0}
    (h : ((bs.subst ρ).substLoc σ).find c k = some b) :
    ∃ b0, bs.find c k = some b0 ∧ b = (b0.subst ρ).substLoc σ := by
  rw [Branches.find_substLoc, Branches.find_subst] at h
  cases hb : bs.find c k with
  | none => rw [hb] at h; simp at h
  | some b0 =>
    rw [hb] at h
    simp only [Option.map_some, Option.some.injEq] at h
    exact ⟨b0, rfl, h.symm⟩

theorem Borrowed.loc_mem {m : Nat} {S₁ : Store} {ρ : Fin m → Val 0} {x : Var m}
    (h : Borrowed sig S₁ ρ x) {l : Nat} (hl : Var.loc l ∈ Val.fv (Val.subst ρ (.var x))) :
    Var.loc l ∈ S₁.dom := by
  rcases h with ⟨l', hl', hlS⟩ | ⟨g, fd, hg, -⟩
  · rw [hl'] at hl; simp [Val.fv] at hl; subst hl; exact hlS
  · rw [hg] at hl; simp [Val.fv] at hl

theorem Owned.loc_mem {m : Nat} {ρ : Fin m → Val 0} {Γ : Ctx m} {S : Store} (h : Owned ρ Γ S)
    {x : Var m} (hx : Res.var x ∈ Γ) {l : Nat} (hl : Var.loc l ∈ Val.fv (Val.subst ρ (.var x))) :
    Var.loc l ∈ S.dom := by
  obtain ⟨l', hl', hlr⟩ := h.mem_roots hx
  rw [hl'] at hl; simp [Val.fv] at hl; subst hl
  exact (Store.mem_roots_var.mp hlr).1

theorem case_letIn {n : Nat} (IH : ∀ m < n, MainClaim sig fbip m) {cfg : Cfg}
    (hcfg : cfg.Compatible sig fbip) {m : Nat} {U Δ : Finset (Var m)} {Γ₁ Γ₂ Γ₃ : Ctx m}
    {xs : List Bool} {e₁ : Expr m} {e₂ : Expr (m + xs.length)} (hU : U = ∅)
    (hsf : (Expr.letIn xs e₁ e₂).scalarFree = true)
    (h₁ : Wf cfg U (Δ ∪ Γ₂.vars.toFinset) Γ₁ e₁)
    (h₂ : Wf cfg (Vars.shift xs.length U ∪ Binder.scalars xs) (Vars.shift xs.length Δ)
      ((Γ₂ + Γ₃).shift xs.length + Binder.owned xs) e₂)
    {ρ : Fin m → Val 0} {S₁ S₂ : Store} {σ : Nat → Option (Val 0)} {vs : List (Val 0)}
    (hρ : Subst.Atomic ρ)
    (hΔ : ∀ x ∈ Δ, Borrowed sig S₁ ρ x) (hΓ : Owned ρ (Γ₁ + Γ₂ + Γ₃) S₂)
    (hS₁ : S₁.Sound) (hinv : OwnedInv S₁ S₂ σ)
    (hev : StepsN sig n (((Expr.letIn xs e₁ e₂).subst ρ).substLoc σ) (.ret vs)) :
    StoreResult sig fbip S₁ S₂ ((Expr.letIn xs e₁ e₂).subst ρ) σ vs := by
  subst hU
  simp only [Expr.subst, Expr.substLoc] at hev ⊢
  obtain ⟨n1, n2, ws, hle, hev1, hlen, hev2⟩ := hev.letIn_inv
  simp only [Expr.scalarFree, Bool.and_eq_true] at hsf
  obtain ⟨⟨hall, hsf1⟩, hsf2⟩ := hsf
  -- split the owned store into the part used by `e₁` and the rest
  have hr : S₂.roots =
      Ctx.nz (Γ₁.map (Res.substR ρ)) + Ctx.nz ((Γ₂ + Γ₃).map (Res.substR ρ)) := by
    rw [← hΓ.roots, add_assoc, Multiset.map_add, Ctx.nz_add]
  obtain ⟨Ta, Tb, rfl, hTa, hTb, hla, hlb⟩ := Store.split hinv.lin hr
  have hdab : Ta.Disjoint Tb := by
    intro x hx hx'
    have := hinv.lin.1.1
    rw [Store.dom_add] at this
    exact Multiset.disjoint_left.mp (Multiset.nodup_add.mp this).2.2 hx hx'
  have hd1b : S₁.Disjoint Tb := fun x hx hx' => hinv.disj x hx (by simp [hx'])
  have hd1a : S₁.Disjoint Ta := fun x hx hx' => hinv.disj x hx (by simp [hx'])
  have hS₁' : (S₁ + Tb).Sound := Store.join_sound hS₁ hlb.1 hd1b
  have heq : S₁ + Tb + Ta = S₁ + (Ta + Tb) := by abel
  have hinv1 : OwnedInv (S₁ + Tb) Ta σ :=
    { disj := fun x hx hx' => by
        rw [Store.dom_add, Multiset.mem_add] at hx
        rcases hx with hx | hx
        · exact hd1a x hx hx'
        · exact hdab x hx' hx
      lin := hla
      ptr := by rw [heq]; exact hinv.ptr
      reads := by rw [heq]; exact hinv.reads }
  have hΓa : Owned ρ Γ₁ Ta :=
    ⟨fun y hy => hΓ.var y (Multiset.mem_add.mpr (.inl (Multiset.mem_add.mpr (.inl hy)))),
      hTa.symm⟩
  have hΓb : Owned ρ (Γ₂ + Γ₃) Tb :=
    ⟨fun y hy => hΓ.var y (by rw [add_assoc]; exact Multiset.mem_add.mpr (.inr hy)), hTb.symm⟩
  have hΔ1 : ∀ x ∈ Δ ∪ Γ₂.vars.toFinset, Borrowed sig (S₁ + Tb) ρ x := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · rcases hΔ x hx with ⟨l, hl, hlS⟩ | h
      · exact .inl ⟨l, hl, by simp [hlS]⟩
      · exact .inr h
    · have hx' : Res.var x ∈ Γ₂ := Ctx.mem_vars.mp (Multiset.mem_toFinset.mp hx)
      obtain ⟨l, hl, hlr⟩ := hΓb.mem_roots (Multiset.mem_add.mpr (.inl hx'))
      exact .inl ⟨l, hl, by simp [(Store.mem_roots_var.mp hlr).1]⟩
  -- evaluate `e₁`
  obtain ⟨S₃, xs₁, σ₃, hs1, hr3, hinv3, hag3, hden3⟩ :=
    IH n1 (by omega) hcfg rfl hsf1 h₁ hρ hΔ1 hΓa hS₁' hinv1 hev1
  have hd3 : (S₁ + Tb).Disjoint S₃ := hinv3.disj
  have hdb3 : Tb.Disjoint S₃ := fun x hx hx' => hd3 x (by simp [hx]) hx'
  have hlin4 : (Tb + S₃).Linear := Store.join_linear hlb hinv3.lin hdb3
  have hinv4 : OwnedInv S₁ (Tb + S₃) σ₃ :=
    { disj := fun x hx hx' => by
        rw [Store.dom_add, Multiset.mem_add] at hx'
        rcases hx' with h | h
        · exact hd1b x hx h
        · exact hd3 x (by simp [hx]) h
      lin := hlin4
      ptr := by rw [← add_assoc]; exact hinv3.ptr
      reads := by rw [← add_assoc]; exact hinv3.reads }
  have has : ∀ y ∈ xs₁, ∃ k, y = .loc k := by
    intro y hy
    obtain ⟨k, rfl, -⟩ := hinv3.root_loc (x := y) (by rw [hr3]; simp [hy])
    exact ⟨k, rfl⟩
  have hlen₁ : xs.length = xs₁.length := by rw [hlen, ← hden3]; simp
  have hlen' : xs.length = (xs₁.map Val.var).length := by simp [hlen₁]
  have hρ₂ := hρ.inst_locs hlen₁.symm has
  have hΔ₂ := Borrowed.shift_set hΔ xs.length (xs₁.map Val.var)
  have hΓ₂' : Owned (Subst.inst xs.length (xs₁.map Val.var) ρ)
      ((Γ₂ + Γ₃).shift xs.length + Binder.owned xs) (Tb + S₃) :=
    hΓb.inst hall hlen₁ has (by rw [Store.roots_add hlb.1 hinv3.lin.1 hdb3, hr3])
  have hU₂ := scalars_empty (m := m) hall
  have hcongr : (e₂.subst (Subst.up xs.length ρ)).substLoc σ₃ =
      (e₂.subst (Subst.up xs.length ρ)).substLoc σ := by
    refine Expr.substLoc_congr _ fun k hk => hag3 k ?_
    refine locs_subst_up (D := fun l => Var.loc l ∈ (S₁ + Tb).dom) h₂ hU₂ ?_ ?_ k hk
    · intro y hy l hl
      have := (hΔ y (Vars.mem_shift.mp hy)).loc_mem hl
      simp [this]
    · intro y hy l hl
      rcases Multiset.mem_add.mp hy with hy | hy
      · have := hΓb.loc_mem (Ctx.mem_shift_var.mp hy) hl
        simp [this]
      · exact absurd hy (Binder.shift_not_mem_owned xs y)
  have hev2' : StepsN sig n2
      ((e₂.subst (Subst.inst xs.length (xs₁.map Val.var) ρ)).substLoc σ₃) (.ret vs) := by
    rw [← body_subst_eq, den_eq hden3, hcongr]
    exact hev2
  have hres := IH n2 (by omega) hcfg hU₂ hsf2 h₂ hρ₂ hΔ₂ hΓ₂' hS₁ hinv4 hev2'
  refine StoreResult.prepend (S₂' := Tb + S₃) (σ' := σ₃) ?_
    (fun k hk => hag3 k (by simp [hk])) hres
  have h1 := SSteps.ctx (.letIn xs .hole (e₂.subst (Subst.up xs.length ρ))) hs1
  simp only [ECtx.plug] at h1
  have h2 := SHead.letIn (sig := sig) (fbip := fbip) (S₁ + Tb + S₃) xs (xs₁.map Val.var)
    (e₂.subst (Subst.up xs.length ρ))
    (fun a ha => by obtain ⟨y, -, rfl⟩ := List.mem_map.mp ha; trivial) hlen'
  rw [Expr.subst_up_inst] at h2
  exact (h1.trans (SSteps.single (SStep.ofHead h2))).cast heq (by abel)

theorem case_bmatch {n : Nat} (IH : ∀ m < n, MainClaim sig fbip m) {cfg : Cfg}
    (hcfg : cfg.Compatible sig fbip) {m : Nat} {U Δ : Finset (Var m)} {Γ : Ctx m} {y : Var m}
    {bs : Branches m}
    (hU : U = ∅) (hsf : (Expr.bmatch (.var y) bs).scalarFree = true) (hy : y ∈ Δ ∨ y ∈ U)
    (hbs : ∀ b ∈ bs.toList,
      Wf cfg (Vars.shift b.binders.length U ∪ Binder.scalars b.binders)
        (Vars.shift b.binders.length Δ ∪ Binder.ownedSet b.binders)
        (Γ.shift b.binders.length) b.body)
    {ρ : Fin m → Val 0} {S₁ S₂ : Store} {σ : Nat → Option (Val 0)} {vs : List (Val 0)}
    (hρ : Subst.Atomic ρ)
    (hΔ : ∀ x ∈ Δ, Borrowed sig S₁ ρ x) (hΓ : Owned ρ Γ S₂)
    (hS₁ : S₁.Sound) (hinv : OwnedInv S₁ S₂ σ)
    (hev : StepsN sig n (((Expr.bmatch (.var y) bs).subst ρ).substLoc σ) (.ret vs)) :
    StoreResult sig fbip S₁ S₂ ((Expr.bmatch (.var y) bs).subst ρ) σ vs := by
  subst hU
  have hy' : y ∈ Δ := hy.resolve_right (by simp)
  simp only [Expr.subst, Expr.substLoc, Val.substList, Val.substLocList] at hev ⊢
  obtain ⟨k, c, ws, b, hm, hv, hf, hev'⟩ := hev.bmatch_inv
  rcases hΔ y hy' with ⟨l, hl, hlS⟩ | ⟨g, fd, hg, -, -⟩
  swap
  · rw [hg] at hv; simp [Val.substLoc] at hv
  rw [hl] at hv ⊢
  obtain ⟨c', as, hcell⟩ := Store.mem_dom.mp hlS
  have hcell' : Cell.bind (.loc l) c' as ∈ S₁ + S₂ := Multiset.mem_add.mpr (.inl hcell)
  obtain ⟨ls, rfl⟩ : ∃ ls : List (Var 0), as = ls.map Val.var :=
    ⟨_, hinv.ptr.args_vars hcell'⟩
  have hls : ∀ z ∈ ls, ∃ k, z = .loc k := by
    intro z hz
    obtain ⟨k, hk⟩ := hinv.ptr.args hcell' (.var z) (List.mem_map_of_mem hz)
    exact ⟨k, by simpa using hk⟩
  have hread := hinv.reads.2 l c' _ hcell'
  simp only [Val.substLoc_loc0, hread, Option.getD_some, Val.ctor.injEq] at hv
  obtain ⟨rfl, rfl⟩ := hv
  obtain ⟨b0, hfb, rfl⟩ := Branches.find_subst_inv hf
  obtain ⟨hbmem, -, hlen⟩ := Branches.find_mem hfb
  simp only [List.length_map] at hlen
  have hbs' := hbs _ hbmem
  obtain ⟨hall, hsfb⟩ := Branches.scalarFree_mem
    (by simp [Expr.scalarFree] at hsf; exact hsf.2) hbmem
  have hρ' := hρ.inst_locs hlen.symm hls
  have hΔ' : ∀ x ∈ Vars.shift b0.binders.length Δ ∪ Binder.ownedSet b0.binders,
      Borrowed sig S₁ (Subst.inst b0.binders.length (ls.map Val.var) ρ) x := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact Borrowed.shift_set hΔ _ _ x hx
    · obtain ⟨w, hw, hw'⟩ := Binder.subst_ownedSet (ρ := ρ) (ws := ls.map Val.var)
        (by rw [List.length_map]; exact hlen) hx
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hw
      obtain ⟨k, rfl⟩ := hls z hz
      refine .inl ⟨k, hw', hS₁.2 _ ?_⟩
      exact Store.mem_rngFv.mpr ⟨_, _, _, hcell, by simp [Val.fvList_map_var, hz]⟩
  have hΓ' := hΓ.shift b0.binders.length (ls.map Val.var)
  have hev'' : StepsN sig k
      ((b0.body.subst (Subst.inst b0.binders.length (ls.map Val.var) ρ)).substLoc σ)
      (.ret vs) := by
    rw [← body_subst_eq]; exact hev'
  have hres := IH k (by omega) hcfg (scalars_empty hall) hsfb hbs' hρ' hΔ' hΓ' hS₁ hinv hev''
  refine StoreResult.prepend (S₂' := S₂) ?_ (fun _ _ => rfl) hres
  have hstep := SHead.bmatch (sig := sig) (fbip := fbip) (S₁ + S₂) (.loc l) _ (ls.map Val.var)
    (bs.subst ρ) (b0.subst ρ) hcell'
    (by rw [Branches.find_subst]; simp only [List.length_map] at hfb ⊢; rw [hfb]; rfl)
  have he : (b0.subst ρ).body.inst (ls.map Val.var) =
      b0.body.subst (Subst.inst b0.binders.length (ls.map Val.var) ρ) :=
    Expr.subst_up_inst ρ b0.body _
  rw [he] at hstep
  exact SSteps.single (SStep.ofHead hstep)

theorem case_dmatch {n : Nat} (IH : ∀ m < n, MainClaim sig fbip m) {cfg : Cfg}
    (hcfg : cfg.Compatible sig fbip) {m : Nat} {U Δ : Finset (Var m)} {Γ : Ctx m} {x : Var m}
    {bs : Branches m}
    (hU : U = ∅) (hsf : (Expr.dmatch (.var x) bs).scalarFree = true)
    (hbs : ∀ b ∈ bs.toList,
      Wf cfg (Vars.shift b.binders.length U ∪ Binder.scalars b.binders)
        (Vars.shift b.binders.length Δ)
        (Γ.shift b.binders.length + Binder.owned b.binders + {Res.credit b.binders.length})
        b.body)
    {ρ : Fin m → Val 0} {S₁ S₂ : Store} {σ : Nat → Option (Val 0)} {vs : List (Val 0)}
    (hρ : Subst.Atomic ρ)
    (hΔ : ∀ x ∈ Δ, Borrowed sig S₁ ρ x) (hΓ : Owned ρ (Γ + {Res.var x}) S₂)
    (hS₁ : S₁.Sound) (hinv : OwnedInv S₁ S₂ σ)
    (hev : StepsN sig n (((Expr.dmatch (.var x) bs).subst ρ).substLoc σ) (.ret vs)) :
    StoreResult sig fbip S₁ S₂ ((Expr.dmatch (.var x) bs).subst ρ) σ vs := by
  subst hU
  simp only [Expr.subst, Expr.substLoc, Val.substList, Val.substLocList] at hev ⊢
  obtain ⟨k, c, ws, b, hm, hv, hf, hev'⟩ := hev.dmatch_inv
  obtain ⟨l, hl, hr⟩ := hΓ.split_var
  rw [hl] at hv ⊢
  have hroot : Res.var (.loc l) ∈ S₂.roots := by rw [hr]; simp
  obtain ⟨c', as, R, rfl⟩ := Store.exists_cell_of_root hroot
  have hzr := (Store.mem_roots_var.mp hroot).2
  obtain ⟨hR, -, -, -, -⟩ := Store.remove_root hinv.lin hzr
  have hroots := Store.roots_remove_root hinv.lin hzr
  have hcell' : Cell.bind (.loc l) c' as ∈ S₁ + ({Cell.bind (.loc l) c' as} + R) := by simp
  obtain ⟨ls, rfl⟩ : ∃ ls : List (Var 0), as = ls.map Val.var :=
    ⟨_, hinv.ptr.args_vars hcell'⟩
  have hls : ∀ z ∈ ls, ∃ k, z = .loc k := by
    intro z hz
    obtain ⟨k, hk⟩ := hinv.ptr.args hcell' (.var z) (List.mem_map_of_mem hz)
    exact ⟨k, by simpa using hk⟩
  have hread := hinv.reads.2 l c' _ hcell'
  simp only [Val.substLoc_loc0, hread, Option.getD_some, Val.ctor.injEq] at hv
  obtain ⟨rfl, rfl⟩ := hv
  obtain ⟨b0, hfb, rfl⟩ := Branches.find_subst_inv hf
  obtain ⟨hbmem, -, hlen⟩ := Branches.find_mem hfb
  simp only [List.length_map] at hlen
  have hbs' := hbs _ hbmem
  obtain ⟨hall, hsfb⟩ := Branches.scalarFree_mem
    (by simp [Expr.scalarFree] at hsf; exact hsf.2) hbmem
  have hρ' := hρ.inst_locs hlen.symm hls
  have hΔ' := Borrowed.shift_set hΔ b0.binders.length (ls.map Val.var)
  have hRr : R.roots = Ctx.nz (Γ.map (Res.substR ρ)) +
      ((ls.map Res.var : List (Res 0)) : Multiset (Res 0)) := by
    rw [hr, Val.fvList_map_var] at hroots
    have : R.roots + {Res.var (.loc l)} = Ctx.nz (Γ.map (Res.substR ρ)) +
        ((ls.map Res.var : List (Res 0)) : Multiset (Res 0)) + {Res.var (.loc l)} := by
      rw [← hroots]
      simp only [List.map_cons, List.map_nil, Multiset.map_coe, Multiset.coe_singleton]
      abel
    exact add_right_cancel this
  have hΓ' : Owned (Subst.inst b0.binders.length (ls.map Val.var) ρ)
      (Γ.shift b0.binders.length + Binder.owned b0.binders + {Res.credit b0.binders.length})
      ({Cell.credit (ls.map Val.var).length} + R) := by
    refine ⟨fun y hy => ?_, ?_⟩
    · rcases Multiset.mem_add.mp hy with hy | hy
      · rcases Multiset.mem_add.mp hy with hy | hy
        · obtain ⟨y0, hy0, rfl⟩ := Ctx.exists_of_mem_shift_var hy
          rw [Val.subst_inst_shift]
          exact hΓ.var y0 (Multiset.mem_add.mpr (.inl hy0))
        · obtain ⟨j, -, rfl⟩ := Binder.mem_select.mp (Binder.mem_ownedAt_var.mp hy)
          rw [Val.subst_inst_newB ρ (by simp [hlen])]
          simp only [List.getElem_map]
          obtain ⟨k, hk⟩ := hls _ (List.getElem_mem _)
          exact ⟨k, by rw [hk]⟩
      · simp at hy
    · rw [Multiset.map_add, Multiset.map_add, Ctx.nz_add, Ctx.nz_add, Ctx.nz_credit,
        Store.roots_credit, hRr, Ctx.shift_substR, Binder.owned_substR hall hlen, Ctx.nz_vars,
        List.length_map, ← hlen]
  have hinv' := hinv.swap_credit hR (ls.map Val.var).length
  have hev'' : StepsN sig k
      ((b0.body.subst (Subst.inst b0.binders.length (ls.map Val.var) ρ)).substLoc σ)
      (.ret vs) := by
    rw [← body_subst_eq]; exact hev'
  have hres := IH k (by omega) hcfg (scalars_empty hall) hsfb hbs' hρ' hΔ' hΓ' hS₁ hinv' hev''
  refine StoreResult.prepend ?_ (fun _ _ => rfl) hres
  have hstep := SHead.dmatch (sig := sig) (fbip := fbip) (S₁ + R) (.loc l) _ (ls.map Val.var)
    (bs.subst ρ) (b0.subst ρ)
    (by rw [Branches.find_subst]; simp only [List.length_map] at hfb ⊢; rw [hfb]; rfl)
  have he : (b0.subst ρ).body.inst (ls.map Val.var) =
      b0.body.subst (Subst.inst b0.binders.length (ls.map Val.var) ρ) :=
    Expr.subst_up_inst ρ b0.body _
  rw [he] at hstep
  refine SSteps.single (SStep.ofHead ?_)
  simpa [add_left_comm] using hstep

theorem case_drop
    (hfb' : ∀ (cfg : Cfg), cfg.Compatible sig fbip → cfg.fbip = true → fbip = true)
    {n : Nat} (IH : ∀ m < n, MainClaim sig fbip m) {cfg : Cfg}
    (hcfg : cfg.Compatible sig fbip) {m : Nat} {U Δ : Finset (Var m)} {Γ : Ctx m} {x : Var m}
    {e : Expr m}
    (hU : U = ∅) (hsf : (Expr.drop (.var x) e).scalarFree = true) (hf : cfg.fbip = true)
    (he : Wf cfg U Δ Γ e)
    {ρ : Fin m → Val 0} {S₁ S₂ : Store} {σ : Nat → Option (Val 0)} {vs : List (Val 0)}
    (hρ : Subst.Atomic ρ)
    (hΔ : ∀ x ∈ Δ, Borrowed sig S₁ ρ x) (hΓ : Owned ρ (Γ + {Res.var x}) S₂)
    (hS₁ : S₁.Sound) (hinv : OwnedInv S₁ S₂ σ)
    (hev : StepsN sig n (((Expr.drop (.var x) e).subst ρ).substLoc σ) (.ret vs)) :
    StoreResult sig fbip S₁ S₂ ((Expr.drop (.var x) e).subst ρ) σ vs := by
  simp only [Expr.subst, Expr.substLoc] at hev ⊢
  obtain ⟨m, hm, hev'⟩ := hev.drop_inv
  obtain ⟨l, hl, hr⟩ := hΓ.split_var
  obtain ⟨T', hs, hle, hlin, hr'⟩ :=
    drop_tree (sig := sig) (e.subst ρ) _ S₂ rfl [Var.loc l] σ _ hinv hr
  have hfb : fbip = true := hfb' cfg hcfg hf
  subst hfb
  have hinvT := hinv.mono hlin hle
  have hT : Owned ρ Γ T' := ⟨fun y hy => hΓ.var y (Multiset.mem_add.mpr (.inl hy)), hr'.symm⟩
  have hsf' : e.scalarFree = true := by simp [Expr.scalarFree] at hsf; exact hsf.2
  rw [hl]
  exact StoreResult.prepend (by simpa [drops] using hs) (fun _ _ => rfl)
    (IH m (by omega) hcfg hU hsf' he hρ hΔ hT hS₁ hinvT hev')

theorem case_free {n : Nat} (IH : ∀ m < n, MainClaim sig fbip m) {cfg : Cfg}
    (hcfg : cfg.Compatible sig fbip) {m : Nat} {U Δ : Finset (Var m)} {Γ : Ctx m} {k : Nat}
    {e : Expr m}
    (hU : U = ∅) (hsf : (Expr.free k e).scalarFree = true) (hf : cfg.fbip = true) (hk : 1 ≤ k)
    (he : Wf cfg U Δ Γ e)
    {ρ : Fin m → Val 0} {S₁ S₂ : Store} {σ : Nat → Option (Val 0)} {vs : List (Val 0)}
    (hρ : Subst.Atomic ρ)
    (hΔ : ∀ x ∈ Δ, Borrowed sig S₁ ρ x) (hΓ : Owned ρ (Γ + {Res.credit k}) S₂)
    (hS₁ : S₁.Sound) (hinv : OwnedInv S₁ S₂ σ)
    (hev : StepsN sig n (((Expr.free k e).subst ρ).substLoc σ) (.ret vs)) :
    StoreResult sig fbip S₁ S₂ ((Expr.free k e).subst ρ) σ vs := by
  simp only [Expr.subst, Expr.substLoc] at hev ⊢
  obtain ⟨m, hm, hev'⟩ := hev.free_inv
  obtain ⟨R, rfl, hR⟩ := hΓ.split_credit hk
  have hinvR := hinv.mono (Store.linear_of_credit hinv.lin) (Multiset.le_add_left _ _)
  have hsf' : e.scalarFree = true := by simpa [Expr.scalarFree] using hsf
  exact StoreResult.prepend (case_free_aux (hcfg.2.2.1 hf) k _) (fun _ _ => rfl)
    (IH m (by omega) hcfg hU hsf' he hρ hΔ hR hS₁ hinvR hev')

end FIP
