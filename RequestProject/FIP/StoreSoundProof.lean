module

public import RequestProject.FIP.StoreSoundCases

@[expose] public section

/-!
# Soundness of the store semantics (Theorem 1, Corollary 1; Appendix B.6)

**Theorem 1** (`store_sound`).  Let `Δ | Γ ⊢ e` be a well-formed FIP expression of the
paper's calculus, and let `S₁, S₂` be disjoint stores of the paper's shape (locations bound
to constructors applied to locations) with `Δ ⊆ dom(S₁)`, `S₁` sound, `Γ = roots(S₂)` and
`S₂` linear.  If `[S₁, S₂]e ⟼* v̄` in the functional semantics, then
`S₁, S₂ | e ⟼*ₛ S₁, S₃ | x̄` in the store semantics, where `[S₁, S₃]x̄ = v̄`,
`x̄ = roots(S₃)` and `S₃` is linear.

The substitution `[S]` is given by a location substitution `σ` with `S.Reads σ`: `σ` maps
every location bound in `S` to the closed value it denotes.  (Such a `σ` exists exactly
when no cycle of `S` is reachable; `[S]` is not defined otherwise.)
-/

namespace FIP

variable {sig : Sig} {fbip : Bool}

theorem Owned.of_empty {ρ : Subst} {Γ : Ctx} {S₂ : Store} (h : Owned ρ (Γ + {Res.credit 0}) S₂) :
    Owned ρ Γ S₂ := by
  refine ⟨fun x hx => h.var x (Multiset.mem_add.mpr (.inl hx)), ?_⟩
  rw [← h.roots]
  simp [Ctx.nz, Multiset.filter_add, Res.substR]

theorem Owned.not_alloc {ρ : Subst} {Γ : Ctx} {S₂ : Store} (h : Owned ρ (Γ + {Res.alloc}) S₂) :
    False := by
  apply Store.alloc_not_mem_roots S₂
  rw [← h.roots]
  simp [Ctx.nz, Res.substR]

/-- The main invariant (Appendix B.5), by induction on the length of the functional
    reduction and on the derivation of `Δ | Γ ⊢ e`. -/
theorem mainClaim (hsig : sig.PaperFragment)
    (hfb : ∀ fd ∈ sig, fd.annot.isFbip = true → fbip = true) : ∀ n, MainClaim sig fbip n := by
  have hfb' : ∀ (cfg : Cfg), cfg.Compatible sig fbip → cfg.fbip = true → fbip = true :=
    fun cfg hc h => hc.2.2.1 h
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro cfg U Δ Γ e hcfg hU hsf hwf
  revert hU hsf
  induction hwf with
  | tuple hvs =>
    intro hU hsf ρ S₁ S₂ σ vs hρ hΔ hΓ hS₁ hinv hev
    exact case_tuple hU hsf hvs hρ hΓ hS₁ hinv hev
  | call f ys e hf hys he _ =>
    intro hU hsf ρ S₁ S₂ σ vs hρ hΔ hΓ hS₁ hinv hev
    exact case_call hsig hfb IH hcfg hU hsf hf hys he hρ hΔ hΓ hS₁ hinv hev
  | bapp y e hy he _ =>
    intro hU hsf ρ S₁ S₂ σ vs hρ hΔ hΓ hS₁ hinv hev
    exact case_bapp hsig hfb IH hcfg hU hsf hy he hρ hΔ hΓ hS₁ hinv hev
  | fapp f e hf he _ =>
    intro hU hsf ρ S₁ S₂ σ vs hρ hΔ hΓ hS₁ hinv hev
    exact case_fapp hsig hfb IH hcfg hU hsf hf he hρ hΔ hΓ hS₁ hinv hev
  | letIn Γ₁ Γ₂ Γ₃ xs e₁ e₂ _ h₁ h₂ hfr _ _ =>
    intro hU hsf ρ S₁ S₂ σ vs hρ hΔ hΓ hS₁ hinv hev
    exact case_letIn IH hcfg hU hsf h₁ h₂ hfr hρ hΔ hΓ hS₁ hinv hev
  | bmatch y bs hy hfr hbs _ =>
    intro hU hsf ρ S₁ S₂ σ vs hρ hΔ hΓ hS₁ hinv hev
    exact case_bmatch IH hcfg hU hsf hy hfr hbs hρ hΔ hΓ hS₁ hinv hev
  | dmatch x bs hfr hbs _ =>
    intro hU hsf ρ S₁ S₂ σ vs hρ hΔ hΓ hS₁ hinv hev
    exact case_dmatch IH hcfg hU hsf hfr hbs hρ hΔ hΓ hS₁ hinv hev
  | empty _ ih =>
    intro hU hsf ρ S₁ S₂ σ vs hρ hΔ hΓ hS₁ hinv hev
    exact ih hU hsf hρ hΔ hΓ.of_empty hS₁ hinv hev
  | drop x hf he _ =>
    intro hU hsf ρ S₁ S₂ σ vs hρ hΔ hΓ hS₁ hinv hev
    exact case_drop hfb' IH hcfg hU hsf hf he hρ hΔ hΓ hS₁ hinv hev
  | free k hf hk he _ =>
    intro hU hsf ρ S₁ S₂ σ vs hρ hΔ hΓ hS₁ hinv hev
    exact case_free IH hcfg hU hsf hf hk he hρ hΔ hΓ hS₁ hinv hev
  | inst k hk _ _ =>
    intro hU hsf ρ S₁ S₂ σ vs hρ hΔ hΓ hS₁ hinv hev
    exact hΓ.not_alloc.elim
  | weaken _ _ =>
    intro hU hsf ρ S₁ S₂ σ vs hρ hΔ hΓ hS₁ hinv hev
    exact hΓ.not_alloc.elim
  | prim op vs hv =>
    intro hU hsf
    simp [Expr.scalarFree] at hsf

theorem Res.substR_nil (r : Res) : r.substR [] = r := by
  cases r with
  | var x => simp [Res.substR, Val.subst_nil]
  | _ => rfl

/-- **Theorem 1** (the store semantics is sound for well-formed FIP programs).
    If `Δ | Γ ⊢ e`, and `S₁, S₂` are disjoint stores of the paper's shape with
    `Δ ⊆ dom(S₁)`, `S₁` sound, `Γ = roots(S₂)` and `S₂` linear, then `[S₁, S₂]e ⟼* v̄`
    implies `S₁, S₂ | e ⟼*ₛ S₁, S₃ | x̄` where `[S₁, S₃]x̄ = v̄`, `x̄ = roots(S₃)` and `S₃`
    is linear.  Here `σ` is `[S₁, S₂]` and `σ₃` is `[S₁, S₃]`, which agrees with `σ` on
    the borrowed store `S₁`. -/
theorem store_sound {sig : Sig} (hsig : sig.PaperFragment) {fbip : Bool} {cfg : Cfg}
    (hcfg : cfg.Compatible sig fbip) {Δ : Finset Var} {Γ : Ctx} {e : Expr}
    (hsf : e.scalarFree = true) (h : Wf cfg ∅ Δ Γ e)
    {S₁ S₂ : Store} (hd : S₁.Disjoint S₂) (hΔ : ∀ x ∈ Δ, x ∈ S₁.dom) (hS₁ : S₁.Sound)
    (hΓ : Γ = S₂.roots) (hS₂ : S₂.Linear) (hptr : (S₁ + S₂).Ptr)
    {σ : Nat → Option Val} (hσ : (S₁ + S₂).Reads σ)
    {vs : List Val} (hev : Steps sig (e.substLoc σ) (.ret vs)) :
    ∃ (S₃ : Store) (xs : List Var),
      SSteps sig fbip (S₁ + S₂) e (S₁ + S₃) (.ret (xs.map .var)) ∧
      (∃ σ₃, (S₁ + S₃).Reads σ₃ ∧ (∀ n, Var.loc n ∈ S₁.dom → σ₃ n = σ n) ∧
        xs.map (fun x => Val.substLoc σ₃ (.var x)) = vs) ∧
      S₃.roots = (xs : Multiset Var).map Res.var ∧ S₃.Linear := by
  obtain ⟨n, hn⟩ := StepsN.of_steps hev
  have hinv : OwnedInv S₁ S₂ σ := ⟨hd, hS₂, hptr, hσ⟩
  have hρ : Subst.Atomic [] := by simp [Subst.Atomic]
  have hB : ∀ x ∈ Δ, Borrowed sig S₁ [] x := by
    intro x hx
    obtain ⟨l, rfl⟩ := (hptr.mono (Multiset.le_add_right _ _)).dom_loc (hΔ x hx)
    exact .inl ⟨l, Val.subst_nil _, hΔ _ hx⟩
  have hO : Owned [] Γ S₂ := by
    refine ⟨fun x hx => ?_, ?_⟩
    · rw [hΓ] at hx
      obtain ⟨l, rfl, -⟩ := hinv.root_loc hx
      exact ⟨l, Val.subst_nil _⟩
    · have : Γ.map (Res.substR []) = Γ := by
        conv_rhs => rw [← Multiset.map_id Γ]
        exact Multiset.map_congr rfl fun r _ => Res.substR_nil r
      rw [this, hΓ, Ctx.nz, Multiset.filter_eq_self]
      intro r hr h'
      subst h'
      exact Store.credit_zero_not_mem_roots S₂ hr
  have hn' : StepsN sig n ((e.subst []).substLoc σ) (.ret vs) := by rw [Expr.subst_nil]; exact hn
  obtain ⟨S₃, xs, σ₃, hs, hr, hinv₃, hag, hden⟩ :=
    mainClaim hsig hcfg.2.2.2 n hcfg rfl hsf h hρ hB hO hS₁ hinv hn'
  rw [Expr.subst_nil] at hs
  exact ⟨S₃, xs, hs, ⟨σ₃, hinv₃.reads, hag, hden⟩, by rw [hr]; simp, hinv₃.lin⟩

/-- **Corollary 1.** If `e ⟼* v̄` and `∅ | ⋄k ⊢ e` (with `k ≥ 1`), then `⋄k | e ⟼*ₛ S | x̄`
    with `[S]x̄ = v̄`: a FIP expression runs in a store containing just the reuse credit it
    needs. -/
theorem store_sound_closed {sig : Sig} (hsig : sig.PaperFragment) {fbip : Bool}
    {cfg : Cfg} (hcfg : cfg.Compatible sig fbip) {e : Expr} {k : Nat} (hk : 0 < k)
    (hsf : e.scalarFree = true) (h : Wf cfg ∅ ∅ {Res.credit k} e)
    {vs : List Val} (hev : Steps sig e (.ret vs)) :
    ∃ (S : Store) (xs : List Var),
      SSteps sig fbip {Cell.credit k} e S (.ret (xs.map .var)) ∧
      ∃ σ, S.Reads σ ∧ xs.map (fun x => Val.substLoc σ (.var x)) = vs := by
  have hfv : e.fv = [] := by
    rcases hx : e.fv with _ | ⟨x, _⟩
    · rfl
    · have := Wf.fv_subset h x (by simp [hx])
      simp [Avail] at this
  have hsub : e.substLoc (fun _ => none) = e :=
    Expr.substLoc_of_noLoc _ e (by simp [NoLoc, hfv])
  have hroots : ({Res.credit k} : Ctx) = Store.roots {Cell.credit k} := by
    simp [Store.roots, Cell.dom, Cell.credits, Nat.pos_iff_ne_zero.mp hk]
  have hlin : Store.Linear {Cell.credit k} := by
    refine ⟨⟨?_, ?_⟩, ?_⟩ <;> simp [Cell.dom, Cell.fv]
  obtain ⟨S₃, xs, hs, ⟨σ₃, hσ₃, -, hden⟩, -, -⟩ :=
    store_sound hsig hcfg hsf h (S₁ := 0) (S₂ := {Cell.credit k}) (by simp [Store.Disjoint])
      (by simp) (by simp [Store.Sound]) hroots hlin
      (by intro c hc; simp at hc; subst hc; trivial)
      (σ := fun _ => none) ⟨by simp [LocClosed], by simp⟩ (hsub.symm ▸ hev)
  exact ⟨S₃, xs, by simpa using hs, σ₃, by simpa using hσ₃, hden⟩

end FIP
