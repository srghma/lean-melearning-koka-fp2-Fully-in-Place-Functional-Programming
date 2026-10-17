module

public import RequestProject.AppB_StoreSoundness.StoreSoundCall

@[expose] public section

/-!
# The cases of the proof of Theorem 1
-/

namespace FIP

variable {sig : Sig} {fbip : Bool}

mutual
theorem Val.scalarFree_subst {m : Nat} {ρ : Fin m → Val 0} (hρ : Subst.Atomic ρ) :
    ∀ v : Val m, v.scalarFree = true → (v.subst ρ).scalarFree = true
  | .var x, _ => by
    rcases hρ.subst_var x with ⟨l, h⟩ | ⟨g, h⟩ <;> rw [h] <;> rfl
  | .fn _, _ => rfl
  | .lit _, h => h
  | .ctor c vs, h => by
    simp only [Val.subst, Val.scalarFree] at h ⊢
    exact Val.scalarFreeList_subst hρ vs h
theorem Val.scalarFreeList_subst {m : Nat} {ρ : Fin m → Val 0} (hρ : Subst.Atomic ρ) :
    ∀ vs : List (Val m), Val.scalarFreeList vs = true →
      Val.scalarFreeList (Val.substList ρ vs) = true
  | [], _ => rfl
  | v :: vs, h => by
    simp only [Val.scalarFreeList, Val.substList, Bool.and_eq_true] at h ⊢
    exact ⟨Val.scalarFree_subst hρ v h.1, Val.scalarFreeList_subst hρ vs h.2⟩
end

theorem Owned.roots_eq {m : Nat} {ρ : Fin m → Val 0} {Γ : Ctx m} {S₂ : Store} (h : Owned ρ Γ S₂)
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

theorem Owned.ex_var {m : Nat} {ρ : Fin m → Val 0} {Γ : Ctx m} {S₂ : Store} (h : Owned ρ Γ S₂) :
    ∀ x, Res.var x ∈ Γ → ∃ y, Val.subst ρ (.var x) = .var y := fun x hx =>
  let ⟨_, hl⟩ := h.var x hx; ⟨_, hl⟩

theorem StoreResult.prepend {S₁ S₂ S₂' : Store} {e e' : Expr 0} {σ σ' : Nat → Option (Val 0)}
    {vs : List (Val 0)} (hs : SSteps sig fbip (S₁ + S₂) e (S₁ + S₂') e')
    (hag : ∀ n, Var.loc n ∈ S₁.dom → σ' n = σ n) (h : StoreResult sig fbip S₁ S₂' e' σ' vs) :
    StoreResult sig fbip S₁ S₂ e σ vs := by
  obtain ⟨S₃, xs, σ₃, hs', hr, hinv, hag', hden⟩ := h
  exact ⟨S₃, xs, σ₃, hs.trans hs', hr, hinv, fun n hn => (hag' n hn).trans (hag n hn), hden⟩

theorem Owned.split_credit {m : Nat} {ρ : Fin m → Val 0} {Γ : Ctx m} {S₂ : Store} {k : Nat}
    (hk : 1 ≤ k) (h : Owned ρ (Γ + {Res.credit k}) S₂) :
    ∃ R, S₂ = {Cell.credit k} + R ∧ Owned ρ Γ R := by
  have hk0 : k ≠ 0 := by omega
  have hr := h.roots
  rw [Multiset.map_add, Ctx.nz_add, Ctx.nz_credit] at hr
  have hk' : Res.credit k ∈ S₂.roots := by rw [← hr]; simp [Cell.credits, hk0]
  obtain ⟨R, rfl⟩ := Store.exists_credit_of_root hk'
  refine ⟨R, rfl, fun x hx => h.var x (Multiset.mem_add.mpr (.inl hx)), ?_⟩
  rw [Store.roots_credit] at hr
  exact add_right_cancel hr

theorem Owned.split_var {m : Nat} {ρ : Fin m → Val 0} {Γ : Ctx m} {S₂ : Store} {x : Var m}
    (h : Owned ρ (Γ + {Res.var x}) S₂) : ∃ l, Val.subst ρ (.var x) = .var (.loc l) ∧
      S₂.roots = (([Var.loc l].map Res.var : List (Res 0)) : Multiset (Res 0)) + Ctx.nz (Γ.map (Res.substR ρ)) := by
  obtain ⟨l, hl⟩ := h.var x (Multiset.mem_add.mpr (.inr (Multiset.mem_singleton_self _)))
  refine ⟨l, hl, ?_⟩
  rw [← h.roots, Multiset.map_add, Ctx.nz_add, add_comm]
  simp [Ctx.nz, Res.substR_var hl, Multiset.filter_singleton, Multiset.singleton_add]

theorem case_free_aux {S₁ R : Store} (hf : fbip = true) (k : Nat) (e : Expr 0) :
    SSteps sig fbip (S₁ + ({Cell.credit k} + R)) (.free k e) (S₁ + R) e := by
  refine SSteps.single (SStep.ofHead ?_)
  have := SHead.free (sig := sig) (S₁ + R) k e hf
  simpa [add_left_comm] using this

theorem Cfg.Compatible.sum_budget {cfg : Cfg} (h : cfg.Compatible sig fbip) (f : FName)
    {m : Nat} (ys : List (Val m)) : cfg.budget f + (ys.map (fnBudget cfg)).sum = 0 := by
  have h0 : ∀ y ∈ ys, fnBudget cfg y = 0 := by
    intro y _
    cases y <;> simp [fnBudget, h.2.1]
  rw [h.2.1 f, zero_add, List.sum_eq_zero]
  intro a ha
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ha
  exact h0 y hy

theorem StepsN.appR_loc {S : Store} {σ : Nat → Option (Val 0)} (hσ : S.Reads σ) {l : Nat}
    (hl : Var.loc l ∈ S.dom) {f : FName} (h : Val.substLoc σ (.var (.loc l) : Val 0) = .fn f) : False := by
  obtain ⟨c, as, hc⟩ := Store.mem_dom.mp hl
  simp [hσ.2 l c as hc] at h

theorem call_args {cfg : Cfg} (hcfg : cfg.Compatible sig fbip) {m : Nat} {Δ : Finset (Var m)}
    {ρ : Fin m → Val 0} {S₁ : Store} (hΔ : ∀ x ∈ Δ, Borrowed sig S₁ ρ x) {ys : List (Val m)}
    (hys : ∀ y ∈ ys, BorrowArg cfg ∅ Δ y) : ∀ a ∈ ys.map (Val.subst ρ), BorrowedVal sig S₁ a := by
  intro a ha
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

theorem den_eq {xs₁ : List (Var 0)} {σ : Nat → Option (Val 0)} {ws : List (Val 0)}
    (h : xs₁.map (fun x => Val.substLoc σ (.var x)) = ws) :
    (xs₁.map Val.var).map (Val.substLoc σ) = ws := by
  rw [← h, List.map_map]; rfl

/-- The common part of `bapp` and `fapp`: applying an annotated top-level function. -/
theorem case_app_fn (hsig : sig.PaperFragment)
    (hfb : ∀ fd ∈ sig, fd.annot.isFbip = true → fbip = true)
    {n : Nat} (IH : ∀ m < n, MainClaim sig fbip m) {cfg : Cfg} (hcfg : cfg.Compatible sig fbip)
    {m : Nat} {Δ : Finset (Var m)} {Γ : Ctx m} {g : FName} {fd₀ : FunDef} {e : Expr m}
    (hg₀ : sig.lookup g = some fd₀) (hann : fd₀.annot ≠ .plain)
    (hsf : e.scalarFree = true) (he : Wf cfg ∅ Δ Γ e)
    {ρ : Fin m → Val 0} {S₁ S₂ : Store} {σ : Nat → Option (Val 0)} {vs : List (Val 0)}
    (hρ : Subst.Atomic ρ)
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
  have hev2' : StepsN sig n2 ((fd₀.instBody [] (xs₁.map .var)).substLoc σ₃) (.ret vs) := by
    rw [FunDef.instBody_substLoc hsig hfd hann, den_eq hden3]
    exact hev2
  have hres := call_body hsig hfb (IH n2 (by omega)) hg₀ hann (as1 := []) (by simp) hr3 hinv3 hS₁
    (by simp [hb]) hl2' hev2'
  refine StoreResult.prepend (S₂' := S₃) (σ' := σ₃) ?_ hag3 hres
  have h1 := SSteps.ctx (.appR [.fn g] .hole) hs1
  simp only [ECtx.plug] at h1
  have h2 := SHead.app (sig := sig) (fbip := fbip) (S₁ + S₃) g fd₀ (xs₁.map .var) hg₀ hb
    (fun a ha => by obtain ⟨y, -, rfl⟩ := List.mem_map.mp ha; trivial) (by simp [hl2'])
  exact h1.trans (SSteps.single (SStep.ofHead h2))

theorem case_tuple {m : Nat} {U Δ : Finset (Var m)} {Γ : Ctx m} {vs₀ : List (Val m)} (hU : U = ∅)
    (hsf : (Expr.ret vs₀).scalarFree = true) (hvs : WfVals U Δ Γ vs₀)
    {ρ : Fin m → Val 0} {S₁ S₂ : Store} {σ : Nat → Option (Val 0)} {vs : List (Val 0)}
    (hρ : Subst.Atomic ρ)
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

theorem case_call (hsig : sig.PaperFragment)
    (hfb : ∀ fd ∈ sig, fd.annot.isFbip = true → fbip = true)
    {n : Nat} (IH : ∀ m < n, MainClaim sig fbip m) {cfg : Cfg} (hcfg : cfg.Compatible sig fbip)
    {m : Nat} {U Δ : Finset (Var m)} {Γ : Ctx m} {f : FName} {ys : List (Val m)} {e : Expr m}
    (hU : U = ∅)
    (hsf : (Expr.call f (.ret ys) e).scalarFree = true) (hf : f ∈ cfg.funs)
    (hys : ∀ y ∈ ys, BorrowArg cfg U Δ y) (he : Wf cfg U Δ Γ e)
    {ρ : Fin m → Val 0} {S₁ S₂ : Store} {σ : Nat → Option (Val 0)} {vs : List (Val 0)}
    (hρ : Subst.Atomic ρ)
    (hΔ : ∀ x ∈ Δ, Borrowed sig S₁ ρ x)
    (hΓ : Owned ρ (Γ + Multiset.replicate (cfg.budget f + (ys.map (fnBudget cfg)).sum) Res.alloc)
      S₂)
    (hS₁ : S₁.Sound) (hinv : OwnedInv S₁ S₂ σ)
    (hev : StepsN sig n (((Expr.call f (.ret ys) e).subst ρ).substLoc σ) (.ret vs)) :
    StoreResult sig fbip S₁ S₂ ((Expr.call f (.ret ys) e).subst ρ) σ vs := by
  subst hU
  rw [hcfg.sum_budget, Multiset.replicate_zero, add_zero] at hΓ
  simp only [Expr.subst, Expr.substLoc, Val.substList_eq_map, Val.substLocList_eq_map] at hev ⊢
  obtain ⟨n1, n2, vs2, fd, hle, hev1, hg, hl1, hl2, hev2⟩ := hev.callO_inv
  simp only [Expr.scalarFree, Bool.and_eq_true] at hsf
  obtain ⟨S₃, xs₁, σ₃, hs1, hr3, hinv3, hag3, hden3⟩ :=
    IH n1 (by omega) hcfg rfl hsf.2 he hρ hΔ hΓ hS₁ hinv hev1
  have has1 := call_args hcfg hΔ hys
  obtain ⟨fd', hg', hann⟩ := hcfg.1 f hf
  rw [hg] at hg'; cases hg'
  have hfd := (Sig.lookup_mem hg).1
  have hl1' : fd.borrowed.length = (ys.map (Val.subst ρ)).length := by simpa using hl1
  have hl2' : fd.owned.length = xs₁.length := by rw [hl2, ← hden3]; simp
  have hvs1 : (ys.map (Val.subst ρ)).map (Val.substLoc σ₃) =
      (ys.map (Val.subst ρ)).map (Val.substLoc σ) :=
    List.map_congr_left fun a ha => (has1 a ha).substLoc hag3
  have hev2' : StepsN sig n2
      ((fd.instBody (ys.map (Val.subst ρ)) (xs₁.map .var)).substLoc σ₃) (.ret vs) := by
    rw [FunDef.instBody_substLoc hsig hfd hann, den_eq hden3, hvs1]
    exact hev2
  have hres := call_body hsig hfb (IH n2 (by omega)) hg hann has1 hr3 hinv3 hS₁ hl1' hl2' hev2'
  refine StoreResult.prepend (S₂' := S₃) (σ' := σ₃) ?_ hag3 hres
  have h1 := SSteps.ctx (.callO f (ys.map (Val.subst ρ)) .hole) hs1
  simp only [ECtx.plug] at h1
  have h2 := SHead.call (sig := sig) (fbip := fbip) (S₁ + S₃) f fd (ys.map (Val.subst ρ))
    (xs₁.map .var) hg (fun a ha => (has1 a ha).atomic)
    (fun a ha => by obtain ⟨y, -, rfl⟩ := List.mem_map.mp ha; trivial) hl1' (by simp [hl2'])
  exact h1.trans (SSteps.single (SStep.ofHead h2))

theorem case_bapp (hsig : sig.PaperFragment)
    (hfb : ∀ fd ∈ sig, fd.annot.isFbip = true → fbip = true)
    {n : Nat} (IH : ∀ m < n, MainClaim sig fbip m) {cfg : Cfg} (hcfg : cfg.Compatible sig fbip)
    {m : Nat} {U Δ : Finset (Var m)} {Γ : Ctx m} {y : Var m} {e : Expr m} (hU : U = ∅)
    (hsf : (Expr.app (.var y) e).scalarFree = true) (hy : y ∈ Δ) (he : Wf cfg U Δ Γ e)
    {ρ : Fin m → Val 0} {S₁ S₂ : Store} {σ : Nat → Option (Val 0)} {vs : List (Val 0)}
    (hρ : Subst.Atomic ρ)
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

theorem case_fapp (hsig : sig.PaperFragment)
    (hfb : ∀ fd ∈ sig, fd.annot.isFbip = true → fbip = true)
    {n : Nat} (IH : ∀ m < n, MainClaim sig fbip m) {cfg : Cfg} (hcfg : cfg.Compatible sig fbip)
    {m : Nat} {U Δ : Finset (Var m)} {Γ : Ctx m} {f : FName} {e : Expr m} (hU : U = ∅)
    (hsf : (Expr.app (.val (.fn f)) e).scalarFree = true) (hf : f ∈ cfg.funs)
    (he : Wf cfg U Δ Γ e)
    {ρ : Fin m → Val 0} {S₁ S₂ : Store} {σ : Nat → Option (Val 0)} {vs : List (Val 0)}
    (hρ : Subst.Atomic ρ)
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

end FIP
