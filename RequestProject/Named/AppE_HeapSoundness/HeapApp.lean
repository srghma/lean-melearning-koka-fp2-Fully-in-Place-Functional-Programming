module

public import RequestProject.Named.AppE_HeapSoundness.HeapCasesB

@[expose] public section

/-!
# The main invariant of Theorem 6: applications

The function position evaluates to a location bound to a closure `λ^z̄ x̄. e`; the heap
semantics duplicates the captured locations `z̄`, drops the closure and continues with the
body, in which the locations of the arguments are substituted for `x̄`.
-/

namespace FIPNamed.Lam

variable {sig : LSig} {n : Nat} {Δ : Finset Var} {Γ : Ctx} {H : Heap} {R : Multiset Var}
  {RC : Multiset Nat} {σ : Nat → Option LVal} {vs : List LVal}

/-- A location of the heap is read back as a constructor or a lambda. -/
theorem HInv.rd_cases {funs : List FName} (h : HInv funs H R RC Γ σ) {y : Var} (hy : y ∈ H.cntM) :
    (∃ c fs, rd σ y = .ctor c fs) ∨ (∃ zs xs b, rd σ y = .lam zs xs b) := by
  obtain ⟨l, n, o, rfl, hc, hrd⟩ := h.cell_rd hy
  rw [hrd]
  cases o with
  | con c fs => exact .inl ⟨c, _, rfl⟩
  | clo zs xs b => exact .inr ⟨_, xs, _, rfl⟩

@[simp] theorem Ctx.vars_single_var (x : Var) : Ctx.vars {Res.var x} = {x} := rfl

@[simp] theorem Ctx.cr_single_var (x : Var) : Ctx.cr {Res.var x} = 0 := by
  simp [Ctx.cr]

theorem locCtx_single (y : Var) : locCtx [.var y] = {Res.var y} := by
  rw [locCtx_cons_var]; simp [locCtx, LVal.fvList]

theorem mem_locCtx_single (y : Var) : y ∈ Ctx.vars (locCtx [.var y]) := by
  rw [locCtx_vars]; simp [LVal.fvList, LVal.fv]

theorem single_of_map_eq {ys : List Var} {f : Var → LVal} {w : LVal} (h : ys.map f = [w]) :
    ∃ y, ys = [y] ∧ f y = w := by
  rcases ys with _ | ⟨y, _ | ⟨_, _⟩⟩ <;> simp at h
  exact ⟨y, rfl, h⟩

theorem case_app (IH : ∀ m < n, HMainClaim sig m) {Γ₁ Γ₂ : Ctx} {e₁ e₂ : LExpr}
    (he₁ : LWf sig.funs Δ Γ₁ e₁) (he₂ : LWf sig.funs Δ Γ₂ e₂)
    (hadm : (LExpr.app e₁ e₂).Adm) (h : HInv sig.funs H R RC (Γ₁ + Γ₂) σ)
    (hΔ : ∀ x ∈ Δ, x ∈ R)
    (hev : LStepsN sig n ((LExpr.app e₁ e₂).subst (locS σ)) (.ret vs)) :
    HeapResult sig H R RC (.app e₁ e₂) σ vs := by
  have hadm1 : e₁.Adm := by cases hadm; assumption
  have hadm2 : e₂.Adm := by cases hadm; assumption
  simp only [LExpr.subst] at hev
  obtain ⟨k₁, w₁, hk₁, hev1, hev'⟩ := LStepsN.plug (.appL .hole _) hev
  simp only [LECtx.plug] at hev'
  obtain ⟨k₂, w₂, hk₂, hev2, hev''⟩ := LStepsN.plug (.appR w₁ .hole) hev'
  simp only [LECtx.plug] at hev''
  obtain ⟨m, t, hm, hh, hrest⟩ :=
    LStepsN.head_of (fun _ hs => LStep.app_ret_ret hs) (by simp [LExpr.IsRet]) hev''
  -- evaluate the function position
  have h1 : HInv sig.funs H (R + Ctx.vars Γ₂) (RC + Ctx.cr Γ₂) Γ₁ σ :=
    h.shift (by simp only [Ctx.vars_add]; abel) (by simp only [Ctx.cr_add]; abel) h.ctx.left
  obtain ⟨H₁, ys₁, σ₁, hs1, hinv1, hag1, hrd1⟩ :=
    IH k₁ (by omega) he₁ hadm1 h1 (fun x hx => Multiset.mem_add.mpr (.inl (hΔ x hx))) hev1
  cases hh with
  | appFn f fd _ _ _ _ =>
    obtain ⟨y, rfl, hy⟩ := single_of_map_eq hrd1
    rcases hinv1.rd_cases (hinv1.vars_cntM (mem_locCtx_single y)) with
      ⟨c, fs, hc⟩ | ⟨zs, xs, b, hc⟩ <;> rw [hc] at hy <;> cases hy
  | beta zs xs body _ hl =>
  obtain ⟨y, rfl, hy⟩ := single_of_map_eq hrd1
  obtain ⟨ly, rfl⟩ : ∃ l, y = .loc l := by
    obtain ⟨l, hl⟩ := isLoc_of_locOnly hinv1.ctx (.var y) (by simp)
    injection hl with hl
    exact ⟨l, hl⟩
  -- evaluate the argument
  have h1' : HInv sig.funs H₁ (R + {Var.loc ly}) RC Γ₂ σ₁ :=
    hinv1.shift (by simp only [List.map_cons, List.map_nil, locCtx_single, Ctx.vars_single_var]; abel)
      (by simp only [List.map_cons, List.map_nil, locCtx_single, Ctx.cr_single_var, add_zero])
      h.ctx.right
  have hagR1 : ∀ l, Var.loc l ∈ R → σ₁ l = σ l := fun l hl =>
    hag1 l (Multiset.mem_add.mpr (.inl hl))
  have he₂σ : e₂.subst (locS σ₁) = e₂.subst (locS σ) := by
    refine subst_agree hag1 fun l hl => ?_
    rcases LWf.dfv_sub he₂ _ hl with hl | hl
    · exact Multiset.mem_add.mpr (.inl (hΔ _ hl))
    · exact Multiset.mem_add.mpr (.inr (Ctx.mem_vars.mpr hl))
  obtain ⟨H₂, as, σ₂, hs2, hinv2, hag2, hrd2⟩ :=
    IH k₂ (by omega) he₂ hadm2 h1' (fun x hx => Multiset.mem_add.mpr (.inl (hΔ x hx)))
      (by rw [he₂σ]; exact hev2)
  have has := isLoc_of_locOnly hinv2.ctx
  have hσy : σ₂ ly = σ₁ ly := hag2 ly (Multiset.mem_add.mpr (.inr (Multiset.mem_singleton_self _)))
  have hrdy : rd σ₂ (.loc ly) = rd σ₁ (.loc ly) := by simp only [rd, LVal.subst, locS, hσy]
  -- the closure
  obtain ⟨l', nc, o, hl', hc, hrdo⟩ :=
    hinv2.cell_rd (hinv2.R_cntM (Multiset.mem_add.mpr (.inr (Multiset.mem_singleton_self _))))
  injection hl' with hl'
  subst hl'
  rw [hrdy, hy] at hrdo
  cases o with
  | con c fs => simp [HObj.toVal, LVal.subst] at hrdo
  | clo zs₂ xs₂ body₂ =>
  simp only [HObj.toVal, LVal.subst, LVal.lam.injEq] at hrdo
  obtain ⟨-, hxs, hb⟩ := hrdo
  subst xs body
  rw [locS_remove] at hrest
  obtain ⟨-, -, ls, rfl, hwfb, hadmb, hnd⟩ := hinv2.cell_ok hc
  have hlen : xs₂.length = (as.map LVal.var).length := by
    rw [hl, ← hrd2, List.length_map, List.length_map]
  -- duplicate the captured locations, drop the closure
  have h2 : HInv sig.funs H₂ R RC ({Res.var (.loc ly)} + locCtx (as.map .var)) σ₂ :=
    hinv2.shift (by simp only [Ctx.vars_add, Ctx.vars_single_var, add_assoc])
      (by simp only [Ctx.cr_add, locCtx_cr, Ctx.cr_single_var, add_zero])
      ((show Ctx.LocOnly {Res.var (.loc ly)} by
        intro r hr; rw [Multiset.mem_singleton] at hr; exact .inl ⟨ly, hr⟩).add hinv2.ctx)
  obtain ⟨H₃, hs3, hinv3, -, -⟩ := h2.dups (sig := sig) _ (isLoc_locs ls)
    (fun y hy => hinv2.obj_fv_cntM hc (by simpa [HObj.fv] using hy))
    (.drop (.var (.loc ly)) (body₂.subst (lzip xs₂ (as.map .var))))
  have hinv3' : HInv sig.funs H₃ R RC
      (locCtx (as.map .var) + locCtx (ls.map fun l => LVal.var (.loc l)) + {Res.var (.loc ly)})
      σ₂ := by
    convert hinv3 using 1; abel
  obtain ⟨H₄, hs4, hinv4⟩ := hinv3'.drop (sig := sig) ⟨ly, rfl⟩
    (body₂.subst (lzip xs₂ (as.map .var)))
  have hloc : Ctx.LocOnly (varCtx (ls.map Var.loc)) := by
    rw [varCtx_eq_locCtx, List.map_map]; exact locCtx_locOnly (isLoc_locs ls)
  have hres := cont IH (m := m) (by omega) has hwfb hadmb
    (by
      rw [Multiset.map_add, Res.ren_locOnly (lzip_locRen _ _ has) hloc,
        ctx_ren_lzip xs₂ as hnd (by simpa using hlen), varCtx_eq_locCtx, List.map_map]
      convert hinv4 using 1; rw [add_comm]; rfl)
    (by simp)
    (by rw [map_var_subst, hrd2]; exact hrest)
  have hs1' : HSteps sig H (.app e₁ e₂) H₁ (.app (.ret [.var (.loc ly)]) e₂) :=
    hs1.ctx (.appL .hole e₂)
  have hs2' : HSteps sig H₁ (.app (.ret [.var (.loc ly)]) e₂) H₂
      (.app (.ret [.var (.loc ly)]) (.ret (as.map .var))) := hs2.ctx (.appR _ .hole)
  refine HeapResult.prepend ((hs1'.trans hs2').trans ((HSteps.head (HHead.app H₂ _ nc _ xs₂
    body₂ _ hc (fun a ha => by obtain ⟨l, rfl⟩ := has a ha; trivial) hlen)).trans
    (hs3.trans hs4))) hres fun l hl => ?_
  rw [hag2 l (Multiset.mem_add.mpr (.inl hl)), hagR1 l hl]

end FIPNamed.Lam
