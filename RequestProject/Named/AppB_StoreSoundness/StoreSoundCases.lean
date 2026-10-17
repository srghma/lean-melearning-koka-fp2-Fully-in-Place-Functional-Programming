module

public import RequestProject.Named.AppB_StoreSoundness.StoreSoundCall

@[expose] public section

/-!
# The cases of the proof of Theorem 1
-/

namespace FIPNamed

variable {sig : Sig} {fbip : Bool}

mutual
theorem Val.scalarFree_subst {ρ : Subst} (hρ : ρ.Atomic) :
    ∀ v : Val, v.scalarFree = true → (v.subst ρ).scalarFree = true
  | .var x, _ => by
    rcases hρ.subst_var x with h | ⟨l, h⟩ | ⟨g, h⟩ <;> rw [h] <;> rfl
  | .fn _, _ => rfl
  | .lit _, h => h
  | .ctor c vs, h => by
    simp only [Val.subst, Val.scalarFree] at h ⊢
    exact Val.scalarFreeList_subst hρ vs h
theorem Val.scalarFreeList_subst {ρ : Subst} (hρ : ρ.Atomic) :
    ∀ vs : List Val, Val.scalarFreeList vs = true → Val.scalarFreeList (Val.substList ρ vs) = true
  | [], _ => rfl
  | v :: vs, h => by
    simp only [Val.scalarFreeList, Val.substList, Bool.and_eq_true] at h ⊢
    exact ⟨Val.scalarFree_subst hρ v h.1, Val.scalarFreeList_subst hρ vs h.2⟩
end

theorem Owned.roots_eq {ρ : Subst} {Γ : Ctx} {S₂ : Store} (h : Owned ρ Γ S₂)
    (h0 : Res.credit 0 ∉ Γ) : S₂.roots = Γ.map (Res.substR ρ) := by
  rw [← h.roots, Ctx.nz, Multiset.filter_eq_self]
  intro r hr
  obtain ⟨r0, hr0, rfl⟩ := Multiset.mem_map.mp hr
  cases r0 with
  | var x =>
    simp only [Res.substR]
    split <;> simp
  | credit k =>
    simp only [Res.substR, ne_eq, Res.credit.injEq]
    rintro rfl; exact h0 hr0
  | alloc => simp [Res.substR]

theorem Owned.ex_var {ρ : Subst} {Γ : Ctx} {S₂ : Store} (h : Owned ρ Γ S₂) :
    ∀ x, Res.var x ∈ Γ → ∃ y, Val.subst ρ (.var x) = .var y := fun x hx =>
  let ⟨_, hl⟩ := h.var x hx; ⟨_, hl⟩

theorem StoreResult.prepend {S₁ S₂ S₂' : Store} {e e' : Expr} {σ σ' : Nat → Option Val}
    {vs : List Val} (hs : SSteps sig fbip (S₁ + S₂) e (S₁ + S₂') e')
    (hag : ∀ n, Var.loc n ∈ S₁.dom → σ' n = σ n) (h : StoreResult sig fbip S₁ S₂' e' σ' vs) :
    StoreResult sig fbip S₁ S₂ e σ vs := by
  obtain ⟨S₃, xs, σ₃, hs', hr, hinv, hag', hden⟩ := h
  exact ⟨S₃, xs, σ₃, hs.trans hs', hr, hinv, fun n hn => (hag' n hn).trans (hag n hn), hden⟩

theorem Owned.split_credit {ρ : Subst} {Γ : Ctx} {S₂ : Store} {k : Nat} (hk : 1 ≤ k)
    (h : Owned ρ (Γ + {Res.credit k}) S₂) : ∃ R, S₂ = {Cell.credit k} + R ∧ Owned ρ Γ R := by
  have hk0 : k ≠ 0 := by omega
  have hr := h.roots
  rw [Multiset.map_add, Ctx.nz_add, Ctx.nz_credit] at hr
  have hk' : Res.credit k ∈ S₂.roots := by rw [← hr]; simp [Cell.credits, hk0]
  obtain ⟨R, rfl⟩ := Store.exists_credit_of_root hk'
  refine ⟨R, rfl, fun x hx => h.var x (Multiset.mem_add.mpr (.inl hx)), ?_⟩
  rw [Store.roots_credit] at hr
  exact add_right_cancel hr

theorem Owned.split_var {ρ : Subst} {Γ : Ctx} {S₂ : Store} {x : Var}
    (h : Owned ρ (Γ + {Res.var x}) S₂) : ∃ l, Val.subst ρ (.var x) = .var (.loc l) ∧
      S₂.roots = ([Var.loc l].map Res.var : Multiset Res) + Ctx.nz (Γ.map (Res.substR ρ)) := by
  obtain ⟨l, hl⟩ := h.var x (Multiset.mem_add.mpr (.inr (Multiset.mem_singleton_self _)))
  refine ⟨l, hl, ?_⟩
  rw [← h.roots, Multiset.map_add, Ctx.nz_add, add_comm]
  simp [Ctx.nz, Res.substR_var hl, Multiset.filter_singleton, Multiset.singleton_add]

theorem case_free_aux {S₁ R : Store} (hf : fbip = true) (k : Nat) (e : Expr) :
    SSteps sig fbip (S₁ + ({Cell.credit k} + R)) (.free k e) (S₁ + R) e := by
  refine SSteps.single (SStep.ofHead ?_)
  have := SHead.free (sig := sig) (S₁ + R) k e hf
  simpa [add_left_comm] using this


theorem Cfg.Compatible.sum_budget {cfg : Cfg} (h : cfg.Compatible sig fbip) (f : FName)
    (ys : List Val) : cfg.budget f + (ys.map (fnBudget cfg)).sum = 0 := by
  have h0 : ∀ y ∈ ys, fnBudget cfg y = 0 := by
    intro y _
    cases y <;> simp [fnBudget, h.2.1]
  rw [h.2.1 f, zero_add, List.sum_eq_zero]
  intro a ha
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ha
  exact h0 y hy

theorem StepsN.appR_loc {S : Store} {σ : Nat → Option Val} (hσ : S.Reads σ) {l : Nat}
    (hl : Var.loc l ∈ S.dom) {f : FName} (h : Val.substLoc σ (.var (.loc l)) = .fn f) : False := by
  obtain ⟨c, as, hc⟩ := Store.mem_dom.mp hl
  simp [Val.substLoc, hσ.2 l c as hc] at h

theorem call_args {cfg : Cfg} (hcfg : cfg.Compatible sig fbip) {Δ : Finset Var} {ρ : Subst}
    {S₁ : Store} (hΔ : ∀ x ∈ Δ, Borrowed sig S₁ ρ x) {ys : List Val}
    (hys : ∀ y ∈ ys, BorrowArg cfg ∅ Δ y) : ∀ a ∈ Val.substList ρ ys, BorrowedVal sig S₁ a := by
  intro a ha
  rw [Val.substList_eq_map] at ha
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ha
  have := hys y hy
  cases y with
  | var x =>
    simp only [BorrowArg, Finset.notMem_empty, or_false] at this
    rcases hΔ x this with ⟨l, hl, hlS⟩ | ⟨g, fd, hg, hl, hann⟩
    · exact .inl ⟨l, hl, hlS⟩
    · exact .inr ⟨g, fd, hg, hl, hann⟩
  | fn g =>
    obtain ⟨fd, hl, hann⟩ := hcfg.1 g this
    exact .inr ⟨g, fd, rfl, hl, hann⟩
  | _ => simp [BorrowArg] at this

/-- The common part of `bapp` and `fapp`: applying an annotated top-level function. -/
theorem case_app_fn (hsig : sig.PaperFragment)
    (hfb : ∀ fd ∈ sig, fd.annot.isFbip = true → fbip = true)
    {n : Nat} (IH : ∀ m < n, MainClaim sig fbip m) {cfg : Cfg} (hcfg : cfg.Compatible sig fbip)
    {Δ : Finset Var} {Γ : Ctx} {g : FName} {fd₀ : FunDef} {e : Expr}
    (hg₀ : sig.lookup g = some fd₀) (hann : fd₀.annot ≠ .plain)
    (hsf : e.scalarFree = true) (he : Wf cfg ∅ Δ Γ e)
    {ρ : Subst} {S₁ S₂ : Store} {σ : Nat → Option Val} {vs : List Val} (hρ : ρ.Atomic)
    (hΔ : ∀ x ∈ Δ, Borrowed sig S₁ ρ x) (hΓ : Owned ρ Γ S₂)
    (hS₁ : S₁.Sound) (hinv : OwnedInv S₁ S₂ σ)
    (hev : StepsN sig n (.app (.ret [.fn g]) ((e.subst ρ).substLoc σ)) (.ret vs)) :
    StoreResult sig fbip S₁ S₂ (.app (.val (.fn g)) (e.subst ρ)) σ vs := by
  obtain ⟨n1, n2, f', fd, ws, hle, hv, hev1, hg, hb, hl, hev2⟩ := hev.appR_inv
  cases hv
  rw [hg₀] at hg; cases hg
  have hfd := (Sig.lookup_mem hg₀).1
  obtain ⟨S₃, xs₁, σ₃, hs1, hr3, hinv3, hag3, hden3⟩ :=
    IH n1 (by omega) hcfg rfl hsf he hρ hΔ hΓ hS₁ hinv hev1
  have hl2' : fd₀.owned.length = xs₁.length := by rw [hl, ← hden3]; simp
  have hz : ∀ τ : Subst, zipSubst fd₀.borrowed [] ++ τ = τ := by
    intro τ; rw [hb]; rfl
  have hev2' : StepsN sig n2 ((fd₀.body.subst (zipSubst fd₀.borrowed [] ++
      zipSubst fd₀.owned (xs₁.map .var))).substLoc σ₃) (.ret vs) := by
    rw [hz, body_substLoc hinv3.reads.1 (body_noLoc hsig hfd hann), zipSubst_mapLoc]
    convert hev2 using 3
    rw [← hden3]; simp
  have hres := call_body hsig hfb (IH n2 (by omega)) hg₀ hann (as1 := []) (by simp) hr3 hinv3 hS₁
    (by simp [hb]) hl2' hev2'
  rw [hz] at hres
  refine StoreResult.prepend (S₂' := S₃) (σ' := σ₃) ?_ hag3 hres
  have h1 := SSteps.ctx (.appR [.fn g] .hole) hs1
  simp only [ECtx.plug] at h1
  have h2 := SHead.app (sig := sig) (fbip := fbip) (S₁ + S₃) g fd₀ (xs₁.map .var) hg₀ hb
    (fun a ha => by obtain ⟨y, -, rfl⟩ := List.mem_map.mp ha; trivial) (by simp [hl2'])
  exact h1.trans (SSteps.single (SStep.ofHead h2))

theorem case_tuple {U Δ : Finset Var} {Γ : Ctx} {vs₀ : List Val} (hU : U = ∅)
    (hsf : (Expr.ret vs₀).scalarFree = true) (hvs : WfVals U Δ Γ vs₀)
    {ρ : Subst} {S₁ S₂ : Store} {σ : Nat → Option Val} {vs : List Val} (hρ : ρ.Atomic)
    (hΓ : Owned ρ Γ S₂) (hS₁ : S₁.Sound) (hinv : OwnedInv S₁ S₂ σ) {n : Nat}
    (hev : StepsN sig n (((Expr.ret vs₀).subst ρ).substLoc σ) (.ret vs)) :
    StoreResult sig fbip S₁ S₂ ((Expr.ret vs₀).subst ρ) σ vs := by
  subst hU
  simp only [Expr.subst, Expr.substLoc] at hev ⊢
  obtain ⟨-, hvs'⟩ := hev.ret_ret
  have hw := WfVals.substR (Δ' := ∅) hvs hΓ.ex_var
  have hroots := hΓ.roots_eq (WfVals.no_credit_zero hvs)
  obtain ⟨ls, S₂', σ', hs, hinv', hr', -, hag, hden⟩ :=
    alloc_tuple (sig := sig) (fbip := fbip) hS₁ hw
      (Val.scalarFreeList_subst hρ _ (by simpa [Expr.scalarFree] using hsf)) [] S₂ σ 0 hinv
      (by rw [hroots, add_zero])
  refine ⟨S₂', ls, σ', by simpa using hs, by simpa using hr', hinv',
    fun n hn => hag n (by simp [hn]), ?_⟩
  rw [hden, ← hvs']
  simp

theorem case_call (hsig : sig.PaperFragment) (hfb : ∀ fd ∈ sig, fd.annot.isFbip = true → fbip = true)
    {n : Nat} (IH : ∀ m < n, MainClaim sig fbip m) {cfg : Cfg} (hcfg : cfg.Compatible sig fbip)
    {U Δ : Finset Var} {Γ : Ctx} {f : FName} {ys : List Val} {e : Expr} (hU : U = ∅)
    (hsf : (Expr.call f (.ret ys) e).scalarFree = true) (hf : f ∈ cfg.funs)
    (hys : ∀ y ∈ ys, BorrowArg cfg U Δ y) (he : Wf cfg U Δ Γ e)
    {ρ : Subst} {S₁ S₂ : Store} {σ : Nat → Option Val} {vs : List Val} (hρ : ρ.Atomic)
    (hΔ : ∀ x ∈ Δ, Borrowed sig S₁ ρ x)
    (hΓ : Owned ρ (Γ + Multiset.replicate (cfg.budget f + (ys.map (fnBudget cfg)).sum) Res.alloc) S₂)
    (hS₁ : S₁.Sound) (hinv : OwnedInv S₁ S₂ σ)
    (hev : StepsN sig n (((Expr.call f (.ret ys) e).subst ρ).substLoc σ) (.ret vs)) :
    StoreResult sig fbip S₁ S₂ ((Expr.call f (.ret ys) e).subst ρ) σ vs := by
  subst hU
  rw [hcfg.sum_budget, Multiset.replicate_zero, add_zero] at hΓ
  simp only [Expr.subst, Expr.substLoc] at hev ⊢
  obtain ⟨n1, n2, vs2, fd, hle, hev1, hg, hl1, hl2, hev2⟩ := hev.callO_inv
  simp only [Expr.scalarFree, Bool.and_eq_true] at hsf
  obtain ⟨S₃, xs₁, σ₃, hs1, hr3, hinv3, hag3, hden3⟩ :=
    IH n1 (by omega) hcfg rfl hsf.2 he hρ hΔ hΓ hS₁ hinv hev1
  have has1 := call_args hcfg hΔ hys
  obtain ⟨fd', hg', hann⟩ := hcfg.1 f hf
  rw [hg] at hg'; cases hg'
  have hfd := (Sig.lookup_mem hg).1
  have hl1' : fd.borrowed.length = (Val.substList ρ ys).length := by simpa using hl1
  have hl2' : fd.owned.length = xs₁.length := by rw [hl2, ← hden3]; simp
  have hvs1 : (Val.substList ρ ys).map (Val.substLoc σ₃) = (Val.substList ρ ys).map (Val.substLoc σ) :=
    List.map_congr_left fun a ha => (has1 a ha).substLoc hag3
  have hev2' : StepsN sig n2 ((fd.body.subst (zipSubst fd.borrowed (Val.substList ρ ys) ++
      zipSubst fd.owned (xs₁.map .var))).substLoc σ₃) (.ret vs) := by
    rw [body_substLoc hinv3.reads.1 (body_noLoc hsig hfd hann), Subst.mapLoc_append,
      zipSubst_mapLoc, zipSubst_mapLoc, hvs1]
    convert hev2 using 4
    · simp
    · rw [← hden3]; simp
  have hres := call_body hsig hfb (IH n2 (by omega)) hg hann has1 hr3 hinv3 hS₁ hl1' hl2' hev2'
  refine StoreResult.prepend (S₂' := S₃) (σ' := σ₃) ?_ hag3 hres
  have h1 := SSteps.ctx (.callO f (Val.substList ρ ys) .hole) hs1
  simp only [ECtx.plug] at h1
  have h2 := SHead.call (sig := sig) (fbip := fbip) (S₁ + S₃) f fd (Val.substList ρ ys)
    (xs₁.map .var) hg (fun a ha => (has1 a ha).atomic)
    (fun a ha => by obtain ⟨y, -, rfl⟩ := List.mem_map.mp ha; trivial) hl1' (by simp [hl2'])
  exact h1.trans (SSteps.single (SStep.ofHead h2))

theorem case_bapp (hsig : sig.PaperFragment) (hfb : ∀ fd ∈ sig, fd.annot.isFbip = true → fbip = true)
    {n : Nat} (IH : ∀ m < n, MainClaim sig fbip m) {cfg : Cfg} (hcfg : cfg.Compatible sig fbip)
    {U Δ : Finset Var} {Γ : Ctx} {y : Var} {e : Expr} (hU : U = ∅)
    (hsf : (Expr.app (.var y) e).scalarFree = true) (hy : y ∈ Δ) (he : Wf cfg U Δ Γ e)
    {ρ : Subst} {S₁ S₂ : Store} {σ : Nat → Option Val} {vs : List Val} (hρ : ρ.Atomic)
    (hΔ : ∀ x ∈ Δ, Borrowed sig S₁ ρ x) (hΓ : Owned ρ Γ S₂)
    (hS₁ : S₁.Sound) (hinv : OwnedInv S₁ S₂ σ)
    (hev : StepsN sig n (((Expr.app (.var y) e).subst ρ).substLoc σ) (.ret vs)) :
    StoreResult sig fbip S₁ S₂ ((Expr.app (.var y) e).subst ρ) σ vs := by
  subst hU
  simp only [Expr.subst, Expr.substLoc, Val.substList, Val.substLocList] at hev ⊢
  have hsf' : e.scalarFree = true := by simp [Expr.scalarFree] at hsf; exact hsf.2
  rcases hΔ y hy with ⟨l, hl, hlS⟩ | ⟨g, fd, hg, hgl, hann⟩
  · rw [hl] at hev
    obtain ⟨_, _, f', _, _, _, hv, _⟩ := hev.appR_inv
    exact (StepsN.appR_loc (hinv.reads.mono (Multiset.le_add_right _ _)) hlS hv).elim
  · rw [hg] at hev ⊢
    exact case_app_fn hsig hfb IH hcfg hgl hann hsf' he hρ hΔ hΓ hS₁ hinv hev

theorem case_fapp (hsig : sig.PaperFragment) (hfb : ∀ fd ∈ sig, fd.annot.isFbip = true → fbip = true)
    {n : Nat} (IH : ∀ m < n, MainClaim sig fbip m) {cfg : Cfg} (hcfg : cfg.Compatible sig fbip)
    {U Δ : Finset Var} {Γ : Ctx} {f : FName} {e : Expr} (hU : U = ∅)
    (hsf : (Expr.app (.val (.fn f)) e).scalarFree = true) (hf : f ∈ cfg.funs)
    (he : Wf cfg U Δ Γ e)
    {ρ : Subst} {S₁ S₂ : Store} {σ : Nat → Option Val} {vs : List Val} (hρ : ρ.Atomic)
    (hΔ : ∀ x ∈ Δ, Borrowed sig S₁ ρ x)
    (hΓ : Owned ρ (Γ + Multiset.replicate (cfg.budget f) Res.alloc) S₂)
    (hS₁ : S₁.Sound) (hinv : OwnedInv S₁ S₂ σ)
    (hev : StepsN sig n (((Expr.app (.val (.fn f)) e).subst ρ).substLoc σ) (.ret vs)) :
    StoreResult sig fbip S₁ S₂ ((Expr.app (.val (.fn f)) e).subst ρ) σ vs := by
  subst hU
  rw [hcfg.2.1 f, Multiset.replicate_zero, add_zero] at hΓ
  simp only [Expr.subst, Expr.substLoc, Val.substList, Val.substLocList, Val.subst,
    Val.substLoc] at hev ⊢
  have hsf' : e.scalarFree = true := by simp [Expr.scalarFree] at hsf; exact hsf.2
  obtain ⟨fd, hg, hann⟩ := hcfg.1 f hf
  exact case_app_fn hsig hfb IH hcfg hg hann hsf' he hρ hΔ hΓ hS₁ hinv hev

theorem case_letIn {n : Nat} (IH : ∀ m < n, MainClaim sig fbip m) {cfg : Cfg}
    (hcfg : cfg.Compatible sig fbip) {U Δ : Finset Var} {Γ₁ Γ₂ Γ₃ : Ctx} {xs : List Binder}
    {e₁ e₂ : Expr} (hU : U = ∅) (hsf : (Expr.letIn xs e₁ e₂).scalarFree = true)
    (h₁ : Wf cfg U (Δ ∪ Γ₂.vars.toFinset) Γ₁ e₁)
    (h₂ : Wf cfg (U ∪ Binder.scalars xs) Δ (Γ₂ + Γ₃ + Binder.owned xs) e₂)
    (hfr : Binder.Fresh xs U Δ (Γ₂ + Γ₃))
    {ρ : Subst} {S₁ S₂ : Store} {σ : Nat → Option Val} {vs : List Val} (hρ : ρ.Atomic)
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
  have hr : S₂.roots = Ctx.nz (Γ₁.map (Res.substR ρ)) + Ctx.nz ((Γ₂ + Γ₃).map (Res.substR ρ)) := by
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
    ⟨fun y hy => hΓ.var y (Multiset.mem_add.mpr (.inl (Multiset.mem_add.mpr (.inl hy)))), hTa.symm⟩
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
  have hroots4 : (Tb + S₃).roots =
      Ctx.nz ((Γ₂ + Γ₃).map (Res.substR ρ)) + (xs₁.map Res.var : Multiset Res) := by
    rw [Store.roots_add hlb.1 hinv3.lin.1 hdb3, hTb, hr3]
  have hinv4 : OwnedInv S₁ (Tb + S₃) σ₃ :=
    { disj := fun x hx hx' => by
        rw [Store.dom_add, Multiset.mem_add] at hx'
        rcases hx' with h | h
        · exact hd1b x hx h
        · exact hd3 x (by simp [hx]) h
      lin := hlin4
      ptr := by rw [← add_assoc]; exact hinv3.ptr
      reads := by rw [← add_assoc]; exact hinv3.reads }
  have has : ∀ v ∈ xs₁.map Val.var, ∃ k, v = .var (.loc k) := by
    intro v hv
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hv
    obtain ⟨k, rfl, -⟩ := hinv3.root_loc (x := y) (by rw [hr3]; simp [hy])
    exact ⟨k, rfl⟩
  have hlen₁ : xs.length = xs₁.length := by rw [hlen, ← hden3]; simp
  have hlen' : xs.length = (xs₁.map Val.var).length := by simp [hlen₁]
  have hρ₂ : (ρ.remove xs ++ zipSubst xs (xs₁.map Val.var)).Atomic :=
    (hρ.remove xs).append (Subst.atomic_zipSubst xs _ fun v hv => .inl (has v hv))
  have hΔ₂ : ∀ y ∈ Δ, Borrowed sig S₁ (ρ.remove xs ++ zipSubst xs (xs₁.map Val.var)) y := by
    intro y hy
    unfold Borrowed
    rw [Val.subst_ext_not_mem ρ xs _ (hfr.not_mem_borrowed hy)]
    exact hΔ y hy
  have hΓ₂' : Owned (ρ.remove xs ++ zipSubst xs (xs₁.map Val.var)) (Γ₂ + Γ₃ + Binder.owned xs)
      (Tb + S₃) := by
    refine ⟨fun y hy => ?_, ?_⟩
    · rcases Multiset.mem_add.mp hy with hy | hy
      · rw [Val.subst_ext_not_mem ρ xs _ (hfr.not_mem_ctx hy)]
        exact hΓb.var y hy
      · obtain ⟨v, hv, hv'⟩ := Val.subst_ext_vars ρ hfr.1 hlen' (Binder.mem_vars_of_owned hy)
        obtain ⟨k, rfl⟩ := has v hv
        exact ⟨k, hv'⟩
    · rw [Multiset.map_add, Ctx.nz_add,
        Ctx.map_substR_congr (fun y hy => Val.subst_ext_not_mem ρ xs _ (hfr.not_mem_ctx hy)),
        Binder.owned_substR hall hfr.1 hlen₁, Ctx.nz_vars, hroots4]
  have hU₂ : (∅ : Finset Var) ∪ Binder.scalars xs = ∅ := by simp [Binder.scalars_of_all hall]
  have hcongr : (e₂.subst (ρ.remove xs)).substLoc σ₃ = (e₂.subst (ρ.remove xs)).substLoc σ := by
    refine Expr.substLoc_congr _ fun k hk => hag3 k ?_
    refine locs_subst (D := fun v => v ∈ (S₁ + Tb).dom) h₂ hU₂ ?_ ?_ k hk
    · intro y hy l hl
      rw [Val.subst_var_remove ρ xs y (hfr.not_mem_borrowed hy)] at hl
      rcases hΔ y hy with ⟨l', hl', hlS⟩ | ⟨g, fd, hg, -⟩
      · rw [hl'] at hl; simp [Val.fv] at hl; subst hl; simp [hlS]
      · rw [hg] at hl; simp [Val.fv] at hl
    · intro y hy l hl
      by_cases hyx : y ∈ Binder.vars xs
      · rw [Val.subst_var_remove_mem ρ xs y hyx] at hl
        simp [Val.fv] at hl; subst hl; simp [Binder.vars] at hyx
      · rw [Val.subst_var_remove ρ xs y hyx] at hl
        have hy' : Res.var y ∈ Γ₂ + Γ₃ := by
          rcases Multiset.mem_add.mp hy with hy | hy
          · exact hy
          · exact absurd (Binder.mem_vars_of_owned hy) hyx
        obtain ⟨l', hl', hlr⟩ := hΓb.mem_roots hy'
        rw [hl'] at hl; simp [Val.fv] at hl; subst hl
        simp [(Store.mem_roots_var.mp hlr).1]
  have hws : (xs₁.map Val.var).map (Val.substLoc σ₃) = ws := by rw [← hden3]; simp
  have hev2' : StepsN sig n2
      ((e₂.subst (ρ.remove xs ++ zipSubst xs (xs₁.map Val.var))).substLoc σ₃) (.ret vs) := by
    rw [← body_subst_eq hinv3.reads.1 hρ xs _ e₂, hws, hcongr]
    exact hev2
  have hres := IH n2 (by omega) hcfg hU₂ hsf2 h₂ hρ₂ hΔ₂ hΓ₂' hS₁ hinv4 hev2'
  refine StoreResult.prepend (S₂' := Tb + S₃) (σ' := σ₃) ?_ (fun k hk => hag3 k (by simp [hk])) hres
  have h1 := SSteps.ctx (.letIn xs .hole (e₂.subst (ρ.remove xs))) hs1
  simp only [ECtx.plug] at h1
  have h2 := SHead.letIn (sig := sig) (fbip := fbip) (S₁ + Tb + S₃) xs (xs₁.map Val.var)
    (e₂.subst (ρ.remove xs)) (fun a ha => by obtain ⟨k, rfl⟩ := has a ha; trivial) hlen'
  rw [Expr.subst_append (hρ.remove xs).noName] at h2
  exact (h1.trans (SSteps.single (SStep.ofHead h2))).cast heq (by abel)

theorem case_bmatch {n : Nat} (IH : ∀ m < n, MainClaim sig fbip m) {cfg : Cfg}
    (hcfg : cfg.Compatible sig fbip) {U Δ : Finset Var} {Γ : Ctx} {y : Var} {bs : List Branch}
    (hU : U = ∅) (hsf : (Expr.bmatch (.var y) bs).scalarFree = true) (hy : y ∈ Δ ∨ y ∈ U)
    (hfr : ∀ b ∈ bs, Binder.Fresh b.binders U Δ Γ)
    (hbs : ∀ b ∈ bs,
      Wf cfg (U ∪ Binder.scalars b.binders) (Δ ∪ Binder.ownedSet b.binders) Γ b.body)
    {ρ : Subst} {S₁ S₂ : Store} {σ : Nat → Option Val} {vs : List Val} (hρ : ρ.Atomic)
    (hΔ : ∀ x ∈ Δ, Borrowed sig S₁ ρ x) (hΓ : Owned ρ Γ S₂)
    (hS₁ : S₁.Sound) (hinv : OwnedInv S₁ S₂ σ)
    (hev : StepsN sig n (((Expr.bmatch (.var y) bs).subst ρ).substLoc σ) (.ret vs)) :
    StoreResult sig fbip S₁ S₂ ((Expr.bmatch (.var y) bs).subst ρ) σ vs := by
  subst hU
  have hy' : y ∈ Δ := hy.resolve_right (by simp)
  simp only [Expr.subst, Expr.substLoc, Val.substList, Val.substLocList] at hev ⊢
  obtain ⟨m, c, ws, xs, e', hm, hv, hf, hev'⟩ := hev.bmatch_inv
  rcases hΔ y hy' with ⟨l, hl, hlS⟩ | ⟨g, fd, hg, -, -⟩
  swap
  · rw [hg] at hv; simp [Val.substLoc] at hv
  rw [hl] at hv ⊢
  obtain ⟨c', as, hcell⟩ := Store.mem_dom.mp hlS
  have hcell' : Cell.bind (.loc l) c' as ∈ S₁ + S₂ := Multiset.mem_add.mpr (.inl hcell)
  have hread := hinv.reads.2 l c' as hcell'
  simp only [Val.substLoc, hread, Option.getD_some, Val.ctor.injEq] at hv
  obtain ⟨rfl, rfl⟩ := hv
  obtain ⟨body, hfb, rfl⟩ := findBranch_subst_inv hf
  obtain ⟨hbmem, -, hlen⟩ := findBranch_mem hfb
  simp only [Branch.binders, List.length_map] at hlen
  have hfr' := hfr _ hbmem
  have hbs' := hbs _ hbmem
  obtain ⟨hall, hsfb⟩ := Expr.scalarFreeB_mem (by simp [Expr.scalarFree] at hsf; exact hsf.2) hbmem
  simp only [Branch.binders, Branch.body] at hfr' hbs' hall hsfb
  have hρ' : (ρ.remove xs ++ zipSubst xs as).Atomic :=
    (hρ.remove xs).append (Subst.atomic_zipSubst xs as fun v hv => .inl (hinv.ptr.args hcell' v hv))
  have hΔ' : ∀ x ∈ Δ ∪ Binder.ownedSet xs, Borrowed sig S₁ (ρ.remove xs ++ zipSubst xs as) x := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · unfold Borrowed
      rw [Val.subst_ext_not_mem ρ xs as (hfr'.not_mem_borrowed hx)]
      exact hΔ x hx
    · obtain ⟨v, hv, hv'⟩ := Val.subst_ext_vars ρ hfr'.1 hlen (Binder.mem_vars_of_ownedSet hx)
      obtain ⟨k, rfl⟩ := hinv.ptr.args hcell' v hv
      refine .inl ⟨k, hv', hS₁.2 _ ?_⟩
      exact Store.mem_rngFv.mpr ⟨_, _, _, hcell, Val.mem_fvList.mpr ⟨_, hv, by simp [Val.fv]⟩⟩
  have hΓ' : Owned (ρ.remove xs ++ zipSubst xs as) Γ S₂ :=
    hΓ.congr fun x hx => Val.subst_ext_not_mem ρ xs as (hfr'.not_mem_ctx hx)
  have hres := IH m (by omega) hcfg (by simp [Binder.scalars_of_all hall]) hsfb hbs' hρ' hΔ' hΓ'
    hS₁ hinv (by rw [← body_subst_eq hinv.reads.1 hρ]; exact hev')
  refine StoreResult.prepend (S₂' := S₂) ?_ (fun _ _ => rfl) hres
  have hstep := SHead.bmatch (sig := sig) (fbip := fbip) (S₁ + S₂) (.loc l) _ as
    (Expr.substBranches ρ bs) xs (body.subst (ρ.remove xs)) hcell'
    (findBranch_subst_some (by simpa using hfb))
  rw [Expr.subst_append (hρ.remove xs).noName] at hstep
  exact SSteps.single (SStep.ofHead hstep)

theorem case_dmatch {n : Nat} (IH : ∀ m < n, MainClaim sig fbip m) {cfg : Cfg}
    (hcfg : cfg.Compatible sig fbip) {U Δ : Finset Var} {Γ : Ctx} {x : Var} {bs : List Branch}
    (hU : U = ∅) (hsf : (Expr.dmatch (.var x) bs).scalarFree = true)
    (hfr : ∀ b ∈ bs, Binder.Fresh b.binders U Δ Γ)
    (hbs : ∀ b ∈ bs, Wf cfg (U ∪ Binder.scalars b.binders) Δ
          (Γ + Binder.owned b.binders + {Res.credit b.binders.length}) b.body)
    {ρ : Subst} {S₁ S₂ : Store} {σ : Nat → Option Val} {vs : List Val} (hρ : ρ.Atomic)
    (hΔ : ∀ x ∈ Δ, Borrowed sig S₁ ρ x) (hΓ : Owned ρ (Γ + {Res.var x}) S₂)
    (hS₁ : S₁.Sound) (hinv : OwnedInv S₁ S₂ σ)
    (hev : StepsN sig n (((Expr.dmatch (.var x) bs).subst ρ).substLoc σ) (.ret vs)) :
    StoreResult sig fbip S₁ S₂ ((Expr.dmatch (.var x) bs).subst ρ) σ vs := by
  subst hU
  simp only [Expr.subst, Expr.substLoc, Val.substList, Val.substLocList] at hev ⊢
  obtain ⟨m, c, ws, xs, e', hm, hv, hf, hev'⟩ := hev.dmatch_inv
  obtain ⟨l, hl, hr⟩ := hΓ.split_var
  rw [hl] at hv ⊢
  have hroot : Res.var (.loc l) ∈ S₂.roots := by rw [hr]; simp
  obtain ⟨c', as, R, rfl⟩ := Store.exists_cell_of_root hroot
  have hzr := (Store.mem_roots_var.mp hroot).2
  obtain ⟨hR, -, -, -, -⟩ := Store.remove_root hinv.lin hzr
  have hroots := Store.roots_remove_root hinv.lin hzr
  have hcell' : Cell.bind (.loc l) c' as ∈ S₁ + ({Cell.bind (.loc l) c' as} + R) := by simp
  have hread := hinv.reads.2 l c' as hcell'
  simp only [Val.substLoc, hread, Option.getD_some, Val.ctor.injEq] at hv
  obtain ⟨rfl, rfl⟩ := hv
  obtain ⟨body, hfb, rfl⟩ := findBranch_subst_inv hf
  obtain ⟨hbmem, -, hlen⟩ := findBranch_mem hfb
  simp only [Branch.binders, List.length_map] at hlen
  have hfr' := hfr _ hbmem
  have hbs' := hbs _ hbmem
  obtain ⟨hall, hsfb⟩ := Expr.scalarFreeB_mem (by simp [Expr.scalarFree] at hsf; exact hsf.2) hbmem
  simp only [Branch.binders, Branch.body] at hfr' hbs' hall hsfb
  have hasv := hinv.ptr.args_vars hcell'
  set ls := Val.fvList as with hls
  have hρ' : (ρ.remove xs ++ zipSubst xs as).Atomic :=
    (hρ.remove xs).append (Subst.atomic_zipSubst xs as fun v hv => .inl (hinv.ptr.args hcell' v hv))
  have hΔ' : ∀ y ∈ Δ, Borrowed sig S₁ (ρ.remove xs ++ zipSubst xs as) y := by
    intro y hy
    unfold Borrowed
    rw [Val.subst_ext_not_mem ρ xs as (hfr'.not_mem_borrowed hy)]
    exact hΔ y hy
  have hRr : R.roots = Ctx.nz (Γ.map (Res.substR ρ)) + (ls.map Res.var : Multiset Res) := by
    rw [hr] at hroots
    have : R.roots + {Res.var (.loc l)} =
        Ctx.nz (Γ.map (Res.substR ρ)) + (ls.map Res.var : Multiset Res) + {Res.var (.loc l)} := by
      rw [← hroots]
      simp only [List.map_cons, List.map_nil, Multiset.map_coe, Multiset.coe_singleton]
      abel
    exact add_right_cancel this
  have hΓ' : Owned (ρ.remove xs ++ zipSubst xs as)
      (Γ + Binder.owned xs + {Res.credit xs.length}) ({Cell.credit as.length} + R) := by
    refine ⟨fun y hy => ?_, ?_⟩
    · rcases Multiset.mem_add.mp hy with hy | hy
      · rcases Multiset.mem_add.mp hy with hy | hy
        · rw [Val.subst_ext_not_mem ρ xs as (hfr'.not_mem_ctx hy)]
          exact hΓ.var y (Multiset.mem_add.mpr (.inl hy))
        · obtain ⟨v, hv, hv'⟩ := Val.subst_ext_vars ρ hfr'.1 hlen (Binder.mem_vars_of_owned hy)
          obtain ⟨k, rfl⟩ := hinv.ptr.args hcell' v hv
          exact ⟨k, hv'⟩
      · simp at hy
    · rw [Multiset.map_add, Multiset.map_add, Ctx.nz_add, Ctx.nz_add, Ctx.nz_credit,
        Store.roots_credit, hRr, hlen,
        Ctx.map_substR_congr (fun y hy => Val.subst_ext_not_mem ρ xs as (hfr'.not_mem_ctx hy))]
      congr 2
      rw [hasv, Binder.owned_substR hall hfr'.1 (by rw [hlen, hasv]; simp), Ctx.nz_vars]
  have hinv' : OwnedInv S₁ ({Cell.credit as.length} + R) σ := hinv.swap_credit hR _
  have hU' : (∅ : Finset Var) ∪ Binder.scalars xs = ∅ := by simp [Binder.scalars_of_all hall]
  have hres := IH m (by omega) hcfg hU' hsfb hbs' hρ' hΔ' hΓ'
    hS₁ hinv' (by rw [← body_subst_eq hinv.reads.1 hρ]; exact hev')
  refine StoreResult.prepend ?_ (fun _ _ => rfl) hres
  have hstep := SHead.dmatch (sig := sig) (fbip := fbip) (S₁ + R) (.loc l) _ as
    (Expr.substBranches ρ bs) xs (body.subst (ρ.remove xs))
    (findBranch_subst_some (by simpa using hfb))
  rw [Expr.subst_append (hρ.remove xs).noName] at hstep
  refine SSteps.single (SStep.ofHead ?_)
  simpa [add_left_comm] using hstep

theorem case_drop (hfb' : ∀ (cfg : Cfg), cfg.Compatible sig fbip → cfg.fbip = true → fbip = true)
    {n : Nat} (IH : ∀ m < n, MainClaim sig fbip m) {cfg : Cfg}
    (hcfg : cfg.Compatible sig fbip) {U Δ : Finset Var} {Γ : Ctx} {x : Var} {e : Expr}
    (hU : U = ∅) (hsf : (Expr.drop (.var x) e).scalarFree = true) (hf : cfg.fbip = true)
    (he : Wf cfg U Δ Γ e)
    {ρ : Subst} {S₁ S₂ : Store} {σ : Nat → Option Val} {vs : List Val} (hρ : ρ.Atomic)
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
    (hcfg : cfg.Compatible sig fbip) {U Δ : Finset Var} {Γ : Ctx} {k : Nat} {e : Expr}
    (hU : U = ∅) (hsf : (Expr.free k e).scalarFree = true) (hf : cfg.fbip = true) (hk : 1 ≤ k)
    (he : Wf cfg U Δ Γ e)
    {ρ : Subst} {S₁ S₂ : Store} {σ : Nat → Option Val} {vs : List Val} (hρ : ρ.Atomic)
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

end FIPNamed
