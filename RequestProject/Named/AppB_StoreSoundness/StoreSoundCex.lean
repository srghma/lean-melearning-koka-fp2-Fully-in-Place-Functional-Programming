module

public import RequestProject.Named.AppB_StoreSoundness.StoreSound

@[expose] public section

/- ══════════════════ PAPER sec. 2.3, App. B START: Store Semantics: Theorem 1 and Corollary 1; Soundness of Store Semantics (PDF p. 12; App. B.2-B.6 on pp. 40-54) ══════════════════
   `not_storeSoundOriginalClaim`: the original wording fails when a store may bind a
   program name. -/

/-!
# The originally stated form of Theorem 1 is false

The first formal statement of Theorem 1 (kept below as `StoreSoundOriginalClaim`) allowed
the stores to bind *program names* (`Var.name`) and not only locations.  The substitution
`[S]e` only replaces locations, so a store binding a name gives a counterexample: with
`S₂ = {x ↦ C}` for the name `x`, the expression `x` is well-formed with `Γ = {x} = roots(S₂)`,
the functional semantics returns the (unsubstituted) variable `x`, but `[S₂]x = C`.

The corrected statement (`store_sound` in `RequestProject/AppB_StoreSoundness/StoreSoundProof.lean`)
requires the stores to bind locations to constructors applied to locations (the paper's
grammar `S ::= S, x ↦ Cᵏ x₁ … xₖ | S, ⋄k`).
-/

namespace FIPNamed

theorem SStep.not_ret_var {sig : Sig} {fbip : Bool} {S S' : Store} {x : Var} {e0 e' : Expr}
    (he : e0 = .ret [.var x]) : ¬ SStep sig fbip S e0 S' e' := by
  intro h
  cases h with
  | head E hh =>
    cases E <;> simp [ECtx.plug] at he
    subst he
    cases hh
  | val E done V rest hd hV hv =>
    cases E <;> simp only [ECtx.plug, reduceCtorEq, Expr.ret.injEq] at he
    rcases done with _ | ⟨d, done⟩
    · simp only [List.nil_append, List.cons.injEq] at he
      obtain ⟨hV', -⟩ := he
      cases V <;> simp [VCtx.plug] at hV'
      subst hV'
      cases hv
    · simp at he

theorem SSteps.ret_var {sig : Sig} {fbip : Bool} {S S' : Store} {x : Var} {e0 e' : Expr}
    (h : SSteps sig fbip S e0 S' e') (he : e0 = .ret [.var x]) : S' = S ∧ e' = e0 := by
  induction h with
  | refl => exact ⟨rfl, rfl⟩
  | tail _ hs ih =>
    obtain ⟨rfl, rfl⟩ := ih he
    exact absurd hs (SStep.not_ret_var he)

/-- The first formal statement of Theorem 1 (which allowed stores to bind names). -/
def StoreSoundOriginalClaim : Prop :=
  ∀ {sig : Sig} (_hsig : sig.PaperFragment) {fbip : Bool} {cfg : Cfg}
    (_hcfg : cfg.Compatible sig fbip) {Δ : Finset Var} {Γ : Ctx} {e : Expr}
    (_hsf : e.scalarFree = true) (_h : Wf cfg ∅ Δ Γ e)
    {S₁ S₂ : Store} (_hd : S₁.Disjoint S₂) (_hΔ : ∀ x ∈ Δ, x ∈ S₁.dom) (_hS₁ : S₁.Sound)
    (_hΓ : Γ = S₂.roots) (_hS₂ : S₂.Linear)
    {vs : List Val} (_hev : Steps sig ((S₁ + S₂).substE e) (.ret vs)),
    ∃ (S₃ : Store) (xs : List Var),
      SSteps sig fbip (S₁ + S₂) e (S₁ + S₃) (.ret (xs.map .var)) ∧
      xs.map (fun x => S₃.read (.var x)) = vs ∧
      S₃.roots = (xs : Multiset Var).map Res.var ∧ S₃.Linear

/-- The first formal statement of Theorem 1 is false: a store binding a program name is a
    counterexample. -/
theorem not_storeSoundOriginalClaim : ¬ StoreSoundOriginalClaim := by
  intro H
  let x : Var := .name "x"
  let S₂ : Store := {Cell.bind x "C" []}
  have hroots : ({Res.var x} : Ctx) = S₂.roots := by
    simp [S₂, Store.roots, Cell.dom, Cell.fv, Cell.credits, Val.fvList]
  have hwf : Wf { funs := [] } ∅ ∅ {Res.var x} (.ret [.var x]) := by
    have := WfVals.cons (U := ∅) (Δ := ∅) _ _ _ _ (WfVal.var x) WfVals.nil
    simp only [add_zero] at this
    exact .tuple this
  have hsub : ((0 : Store) + S₂).substE (.ret [.var x]) = .ret [.var x] := by
    simp [Store.substE, Expr.substLoc, Val.substLocList, Val.substLoc, x]
  obtain ⟨S₃, xs, hs, hr, -, -⟩ := H (sig := []) (fbip := false)
    ⟨by simp, by simp [Sig.Wf], by simp, by simp⟩ (cfg := { funs := [] })
    ⟨by simp, by simp, by simp, by simp⟩
    (by simp [Expr.scalarFree, Val.scalarFreeList, Val.scalarFree])
    hwf (S₁ := 0) (S₂ := S₂) (by simp [Store.Disjoint]) (by simp) (by simp [Store.Sound])
    hroots (by refine ⟨⟨?_, ?_⟩, ?_⟩ <;> simp [S₂, Cell.dom, Cell.fv, Val.fvList])
    (vs := [.var x]) (by rw [hsub])
  obtain ⟨h1, h2⟩ := hs.ret_var rfl
  simp only [zero_add] at h1
  subst h1
  cases xs with
  | nil => simp at h2
  | cons y ys =>
    cases ys with
    | cons => simp at h2
    | nil =>
      simp only [List.map_cons, List.map_nil, Expr.ret.injEq, List.cons.injEq, Val.var.injEq,
        and_true] at h2
      subst h2
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hr
      have hl : S₂.lookup x = some ("C", []) := by
        have hex : ∃ p : CName × List Val, Cell.bind x p.1 p.2 ∈ S₂ :=
          ⟨("C", []), by simp [S₂]⟩
        unfold Store.lookup
        rw [dif_pos hex, Option.some_inj]
        have := hex.choose_spec
        generalize hex.choose = p at this
        change Cell.bind x p.1 p.2 ∈ ({Cell.bind x "C" []} : Store) at this
        simp only [Multiset.mem_singleton, Cell.bind.injEq, true_and] at this
        exact Prod.ext this.1 this.2
      unfold Store.read at hr
      rw [show Multiset.card S₂ + 1 = 1 + 1 from rfl, Store.readN, hl] at hr
      simp at hr

end FIPNamed

/- ══════════════════ PAPER sec. 2.3, App. B END: Store Semantics: Theorem 1 and Corollary 1; Soundness of Store Semantics ══════════════════ -/
