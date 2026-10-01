module

public import RequestProject.FIP.HeapMainAux

@[expose] public section

/-!
# The main invariant of Theorem 6: the simple cases

The proof proceeds by induction on the length of the functional reduction and on the
derivation of `Δ | Γ ⊢ e`.  The expression evaluated by the heap semantics is a
well-formed expression whose free variables are locations: borrowed locations, which hold
a reference of the rest of the computation (`R`), and owned locations (`Γ`).
-/

namespace FIP.Lam

/-- The names of the functions of a signature. -/
abbrev LSig.funs (sig : LSig) : List FName := sig.map (·.name)

/-- The conclusion of Theorem 6 for `H | e`: the heap semantics evaluates `e` to locations
    `ȳ` denoting the values `v̄`, the result heap is linear with roots `R, ȳ`, and the
    locations held by the rest of the computation denote the same values as before. -/
def HeapResult (sig : LSig) (H : Heap) (R : Multiset Var) (RC : Multiset Nat) (e : LExpr)
    (σ : Nat → Option LVal) (vs : List LVal) : Prop :=
  ∃ (H' : Heap) (ys : List Var) (σ' : Nat → Option LVal),
    HSteps sig H e H' (.ret (ys.map .var)) ∧
    HInv sig.funs H' R RC (locCtx (ys.map .var)) σ' ∧ (∀ l, Var.loc l ∈ R → σ' l = σ l) ∧
    ys.map (rd σ') = vs

/-- The statement proved by induction on the length `n` of the functional reduction. -/
def HMainClaim (sig : LSig) (n : Nat) : Prop :=
  ∀ {Δ : Finset Var} {Γ : Ctx} {e : LExpr}, LWf sig.funs Δ Γ e → e.Adm →
  ∀ {H : Heap} {R : Multiset Var} {RC : Multiset Nat} {σ : Nat → Option LVal}
    {vs : List LVal}, HInv sig.funs H R RC Γ σ → (∀ x ∈ Δ, x ∈ R) →
    LStepsN sig n (e.subst (locS σ)) (.ret vs) → HeapResult sig H R RC e σ vs

variable {sig : LSig} {n : Nat} {Δ : Finset Var} {Γ : Ctx} {H : Heap} {R : Multiset Var}
  {RC : Multiset Nat} {σ : Nat → Option LVal} {vs : List LVal}

theorem HeapResult.prepend {H₁ : Heap} {e e₁ : LExpr} {σ₁ : Nat → Option LVal}
    (hs : HSteps sig H e H₁ e₁) (hr : HeapResult sig H₁ R RC e₁ σ₁ vs)
    (hag : ∀ l, Var.loc l ∈ R → σ₁ l = σ l) : HeapResult sig H R RC e σ vs := by
  obtain ⟨H', ys, σ', hs', h', hag', hrd⟩ := hr
  exact ⟨H', ys, σ', hs.trans hs', h', fun l hl => by rw [hag' l hl, hag l hl], hrd⟩

/-! ## Values -/

theorem case_tuple {vs0 : List LVal} (hvs : LWfVals sig.funs Δ Γ vs0) (hadm : (LExpr.ret vs0).Adm)
    (h : HInv sig.funs H R RC Γ σ)
    (hev : LStepsN sig n ((LExpr.ret vs0).subst (locS σ)) (.ret vs)) :
    HeapResult sig H R RC (.ret vs0) σ vs := by
  have hadm' : ∀ v ∈ vs0, v.Adm := by cases hadm; assumption
  simp only [LExpr.subst] at hev
  obtain ⟨-, hvs'⟩ := hev.ret_ret
  obtain ⟨H', ys, σ', hs, h', -, hag, hrd⟩ :=
    allocVals (sig := sig) hvs hadm' (Γ₀ := 0) (by simpa using h)
  refine ⟨H', ys, σ', ?_, by simpa using h', fun l hl => hag l (h.dom_of_R hl), ?_⟩
  · simpa [LECtx.plug] using hs _ (PosOK.ret .hole [] (by simp))
  · rw [hrd, ← hvs', LVal.substList_eq_map]

/-! ## `dup`, `drop`, `free`, `alloc` -/

theorem case_dup (IH : ∀ m < n, HMainClaim sig m) {x : Var} {e : LExpr}
    (hx : x ∈ Δ ∨ Res.var x ∈ Γ) (he : LWf sig.funs Δ (Γ + {Res.var x}) e)
    (hadm : (LExpr.dup (.var x) e).Adm) (h : HInv sig.funs H R RC Γ σ) (hΔ : ∀ x ∈ Δ, x ∈ R)
    (hev : LStepsN sig n ((LExpr.dup (.var x) e).subst (locS σ)) (.ret vs)) :
    HeapResult sig H R RC (.dup (.var x) e) σ vs := by
  have hadm' : e.Adm := by cases hadm; assumption
  simp only [LExpr.subst] at hev
  obtain ⟨m, t, rfl, hh, hrest⟩ :=
    LStepsN.head_of (fun _ hs => LStep.of_noCtx (by simp [LExpr.NoCtx]) hs) (by simp [LExpr.IsRet]) hev
  cases hh
  have hxc : x ∈ H.cntM := by
    rcases hx with hx | hx
    · exact h.R_cntM (hΔ x hx)
    · exact h.vars_cntM (Ctx.mem_vars.mpr hx)
  obtain ⟨H₁, hs, h1, -, -, -⟩ := h.dup (sig := sig) hxc e
  exact HeapResult.prepend hs (IH m (by omega) he hadm' h1 hΔ hrest) (fun _ _ => rfl)

theorem case_drop (IH : ∀ m < n, HMainClaim sig m) {x : Var} {e : LExpr}
    (he : LWf sig.funs Δ Γ e) (hadm : (LExpr.drop (.var x) e).Adm)
    (h : HInv sig.funs H R RC (Γ + {Res.var x}) σ) (hΔ : ∀ x ∈ Δ, x ∈ R)
    (hev : LStepsN sig n ((LExpr.drop (.var x) e).subst (locS σ)) (.ret vs)) :
    HeapResult sig H R RC (.drop (.var x) e) σ vs := by
  have hadm' : e.Adm := by cases hadm; assumption
  simp only [LExpr.subst] at hev
  obtain ⟨m, t, rfl, hh, hrest⟩ :=
    LStepsN.head_of (fun _ hs => LStep.of_noCtx (by simp [LExpr.NoCtx]) hs) (by simp [LExpr.IsRet]) hev
  cases hh
  have hxl : ∃ l, x = .loc l := by
    rcases h.ctx (.var x) (by simp) with ⟨l, hl⟩ | ⟨k, hk⟩
    · exact ⟨l, by injection hl⟩
    · cases hk
  obtain ⟨H₁, hs, h1⟩ := h.drop (sig := sig) hxl e
  exact HeapResult.prepend hs (IH m (by omega) he hadm' h1 hΔ hrest) (fun _ _ => rfl)

theorem case_free (IH : ∀ m < n, HMainClaim sig m) {k : Nat} {e : LExpr} (hk : 1 ≤ k)
    (he : LWf sig.funs Δ Γ e) (hadm : (LExpr.free k e).Adm)
    (h : HInv sig.funs H R RC (Γ + {Res.credit k}) σ) (hΔ : ∀ x ∈ Δ, x ∈ R)
    (hev : LStepsN sig n ((LExpr.free k e).subst (locS σ)) (.ret vs)) :
    HeapResult sig H R RC (.free k e) σ vs := by
  have hadm' : e.Adm := by cases hadm; assumption
  simp only [LExpr.subst] at hev
  obtain ⟨m, t, rfl, hh, hrest⟩ :=
    LStepsN.head_of (fun _ hs => LStep.of_noCtx (by simp [LExpr.NoCtx]) hs) (by simp [LExpr.IsRet]) hev
  cases hh
  obtain ⟨H₀, rfl, h0⟩ := h.takeCredit hk
  exact HeapResult.prepend (HSteps.head (.free H₀ k e)) (IH m (by omega) he hadm' h0 hΔ hrest)
    (fun _ _ => rfl)

theorem case_alloc (IH : ∀ m < n, HMainClaim sig m) {k : Nat} {e : LExpr}
    (he : LWf sig.funs Δ (Γ + {Res.credit k}) e) (hadm : (LExpr.alloc k e).Adm)
    (h : HInv sig.funs H R RC Γ σ) (hΔ : ∀ x ∈ Δ, x ∈ R)
    (hev : LStepsN sig n ((LExpr.alloc k e).subst (locS σ)) (.ret vs)) :
    HeapResult sig H R RC (.alloc k e) σ vs := by
  have hadm' : e.Adm := by cases hadm; assumption
  simp only [LExpr.subst] at hev
  obtain ⟨m, t, rfl, hh, hrest⟩ :=
    LStepsN.head_of (fun _ hs => LStep.of_noCtx (by simp [LExpr.NoCtx]) hs) (by simp [LExpr.IsRet]) hev
  cases hh
  exact HeapResult.prepend (HSteps.head (.alloc H k e)) (IH m (by omega) he hadm' (h.putCredit k) hΔ hrest)
    (fun _ _ => rfl)

theorem HInv.of_empty {funs : List FName} (h : HInv funs H R RC (Γ + {Res.credit 0}) σ) :
    HInv funs H R RC Γ σ :=
  h.shift (by simp [Ctx.vars_add]) (by simp [Ctx.cr_add, nz]) h.ctx.left

end FIP.Lam
