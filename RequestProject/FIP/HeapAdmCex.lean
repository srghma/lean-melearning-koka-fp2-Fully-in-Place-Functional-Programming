module

public import RequestProject.FIP.HeapTheorem

@[expose] public section

/-!
# Theorem 6 needs the reuse-drop restriction

The typing rule for `dropru x; e` does not check that the size `k` recorded in
`dropru x k` is the size of the cell bound to `x`, while the heap semantics only reduces
`dropru x k` when it is.  So without the admissibility hypothesis `e.Adm` of
`heap_sound_corrected` (which only allows `dropru` as the reuse-drop of a match branch on
`x`), a well-formed expression can evaluate functionally while the heap semantics is stuck:
with `x ↦¹ C` (a cell with no fields), `dropru x 1; free 1; ()` is well-formed with owned
environment `x`, reduces functionally to `()`, and has no heap reduction at all
(`heap_sound_needs_adm`).

Function values are excluded for a similar reason: a top-level function may be passed as a
borrowed argument, and borrowed arguments may be duplicated and dropped, but the heap
semantics has no rule for `dup f` or `drop f`.  With `f(y;) = dup y; drop y; ()` and
`g() = ()`, the closed expression `f(g; )` reduces functionally to `()`, while the heap
semantics gets stuck at `dup g; drop g; ()` (`heap_sound_needs_no_fn`).
-/

namespace FIP.Lam

theorem HStep.stuck_dropru {sig : LSig} {H H' : Heap} {e0 e' e1 : LExpr} {y : Var}
    (hH : ∀ x n c zs, HCell.bind x n (.con c zs) ∈ H → zs = [])
    (he : e0 = .dropru (.var y) 1 e1) : ¬ HStep sig H e0 H' e' := by
  intro h
  cases h with
  | head E hh =>
    cases E <;> simp only [LECtx.plug, reduceCtorEq] at he
    cases hh with
    | dropru H₀ x n c zs e =>
      simp only [LExpr.dropru.injEq] at he
      have := hH x (n + 2) c zs (by simp)
      subst this
      simp at he
    | dconru H₀ x c zs e =>
      simp only [LExpr.dropru.injEq] at he
      have := hH x 1 c zs (by simp)
      subst this
      simp at he
    | _ => simp at he
  | val E done V rest hd hV hv =>
    cases E <;> simp [LECtx.plug] at he

theorem HSteps.stuck_dropru {sig : LSig} {H H' : Heap} {e0 e' e1 : LExpr} {y : Var}
    (hH : ∀ x n c zs, HCell.bind x n (.con c zs) ∈ H → zs = [])
    (h : HSteps sig H e0 H' e') (he : e0 = .dropru (.var y) 1 e1) : H' = H ∧ e' = e0 := by
  induction h with
  | refl => exact ⟨rfl, rfl⟩
  | tail _ hs ih =>
    obtain ⟨rfl, rfl⟩ := ih he
    exact (HStep.stuck_dropru hH he hs).elim

/-- Without `e.Adm`, the conclusion of `heap_sound_corrected` can fail: all other hypotheses
    hold, the expression evaluates functionally, and the heap semantics never reaches a
    value. -/
theorem heap_sound_needs_adm : ∃ (sig : LSig) (Γ : Ctx) (e : LExpr) (H : Heap)
    (σ : Nat → Option LVal) (vs : List LVal),
    sig.Wf ∧ sig.Adm ∧ LWf sig.funs ∅ Γ e ∧ HInv sig.funs H 0 0 Γ σ ∧
    LSteps sig (e.subst (locS σ)) (.ret vs) ∧ ¬ e.Adm ∧
    ∀ (H' : Heap) (ys : List Var), ¬ HSteps sig H e H' (.ret (ys.map .var)) := by
  refine ⟨[], {Res.var (.loc 0)}, .dropru (.var (.loc 0)) 1 (.free 1 (.ret [])),
    {HCell.bind (.loc 0) 1 (.con "C" [])}, fun l => if l = 0 then some (.ctor "C" []) else none,
    [], by simp [LSig.Wf], by simp [LSig.Adm], ?_, ?_, ?_, (by intro h; cases h), ?_⟩
  · simpa using LWf.dropru (funs := LSig.funs []) (Δ := ∅) (Γ := 0) (.loc 0) 1
      (by simpa using LWf.free (funs := LSig.funs []) (Δ := ∅) (Γ := 0) 1 le_rfl (.tuple .nil))
  · refine ⟨?_, by simp [Heap.dom],
      by rw [Ctx.vars_single_var]; simp [Heap.cntM, Heap.rngFv, HObj.fv, LVal.fvList],
      by simp [nz, Heap.creditsM, Ctx.cr], ?_, ⟨?_, ?_⟩⟩
    · intro c hc
      rw [Multiset.mem_singleton] at hc
      subst hc
      exact ⟨⟨0, rfl⟩, le_rfl, by simp [HObj.Ok]⟩
    · intro r hr
      rw [Multiset.mem_singleton] at hr
      exact .inl ⟨0, hr⟩
    · intro l v hv
      split_ifs at hv
      cases hv
      simp [LVal.dfv, LVal.dfvList]
    · intro l n o hc
      rw [Multiset.mem_singleton] at hc
      simp only [HCell.bind.injEq, Var.loc.injEq] at hc
      obtain ⟨rfl, rfl, rfl⟩ := hc
      simp [HObj.toVal, LVal.subst, LVal.substList]
  · simp only [LExpr.subst, LVal.subst, LVal.substList]
    refine Relation.ReflTransGen.head (LStep.step .hole (LHead.dropru _ _ _)) ?_
    exact Relation.ReflTransGen.head (LStep.step .hole (LHead.free _ _)) .refl
  · intro H' ys hs
    have := (HSteps.stuck_dropru (fun x n c zs hc => by
      rw [Multiset.mem_singleton] at hc
      simp only [HCell.bind.injEq, HObj.con.injEq] at hc
      exact hc.2.2.2) hs rfl).2
    cases this

/-! ## Function values passed as borrowed arguments -/

/-- `f(y;) = dup y; drop y; ()`. -/
def cexFnF : LFunDef :=
  { name := "f", borrowed := [⟨"y", false⟩], owned := [],
    body := .dup (.var (.name "y")) (.drop (.var (.name "y")) (.ret [])) }

/-- `g() = ()`. -/
def cexFnG : LFunDef := { name := "g", borrowed := [], owned := [], body := .ret [] }

/-- The signature `f, g`. -/
def cexFnSig : LSig := [cexFnF, cexFnG]

/-- The body of `f` with `g` substituted for `y`. -/
def cexFnStuck : LExpr := .dup (.fn "g") (.drop (.fn "g") (.ret []))

theorem cexFn_lookup : cexFnSig.lookup "f" = some cexFnF := rfl

theorem cexFn_body :
    cexFnF.body.subst (lzip (cexFnF.borrowed ++ cexFnF.owned) ([LVal.fn "g"] ++ [])) =
      cexFnStuck := rfl

theorem HStep.cexFn_call {H H' : Heap} {e0 e' : LExpr}
    (he : e0 = .call "f" (.ret [.fn "g"]) (.ret [])) (h : HStep cexFnSig H e0 H' e') :
    H' = H ∧ e' = cexFnStuck := by
  cases h with
  | head E hh =>
    cases E with
    | hole =>
      simp only [LECtx.plug] at he ⊢
      subst he
      cases hh with
      | call _ _ fd _ _ hlook _ _ _ =>
        rw [cexFn_lookup] at hlook
        cases hlook
        exact ⟨rfl, cexFn_body⟩
    | callB f E e =>
      simp only [LECtx.plug, LExpr.call.injEq] at he
      obtain ⟨rfl, rfl⟩ := LECtx.plug_eq_ret he.2.1
      cases hh
    | callO f vs E =>
      simp only [LECtx.plug, LExpr.call.injEq] at he
      obtain ⟨rfl, rfl⟩ := LECtx.plug_eq_ret he.2.2
      cases hh
    | _ => simp [LECtx.plug] at he
  | val E done V rest hd hV hv =>
    cases E with
    | callB f E e =>
      simp only [LECtx.plug, LExpr.call.injEq] at he
      obtain ⟨rfl, he'⟩ := LECtx.plug_eq_ret he.2.1
      simp only [LExpr.ret.injEq] at he'
      rcases done with _ | ⟨d, done⟩
      · simp only [List.nil_append, List.cons.injEq] at he'
        obtain ⟨hV', -⟩ := he'
        cases V <;> simp [LVCtx.plug] at hV'
        subst hV'
        cases hv
      · simp at he'
    | callO f vs E =>
      simp only [LECtx.plug, LExpr.call.injEq] at he
      obtain ⟨rfl, he'⟩ := LECtx.plug_eq_ret he.2.2
      simp at he'
    | _ => simp [LECtx.plug] at he

theorem HStep.cexFn_stuck {H H' : Heap} {e0 e' : LExpr} (he : e0 = cexFnStuck) :
    ¬ HStep cexFnSig H e0 H' e' := by
  intro h
  cases h with
  | head E hh =>
    cases E <;> simp only [LECtx.plug, cexFnStuck, reduceCtorEq] at he
    subst he
    cases hh
  | val E done V rest hd hV hv =>
    cases E <;> simp [LECtx.plug, cexFnStuck] at he

theorem HSteps.cexFn {H H' : Heap} {e0 e' : LExpr} (h : HSteps cexFnSig H e0 H' e')
    (he : e0 = .call "f" (.ret [.fn "g"]) (.ret [])) :
    H' = H ∧ (e' = .call "f" (.ret [.fn "g"]) (.ret []) ∨ e' = cexFnStuck) := by
  induction h with
  | refl => exact ⟨rfl, .inl he⟩
  | tail _ hs ih =>
    obtain ⟨rfl, h1 | h1⟩ := ih he
    · obtain ⟨rfl, rfl⟩ := HStep.cexFn_call h1 hs
      exact ⟨rfl, .inr rfl⟩
    · exact (HStep.cexFn_stuck h1 hs).elim

/-- Without `e.Adm`, the conclusion of `heap_sound_corrected` can fail because of function
    values, even for a closed expression evaluated from the empty heap. -/
theorem heap_sound_needs_no_fn : ∃ (sig : LSig) (e : LExpr) (vs : List LVal),
    sig.Wf ∧ sig.Adm ∧ LWf sig.funs ∅ 0 e ∧ LSteps sig e (.ret vs) ∧ ¬ e.Adm ∧
    ∀ (H' : Heap) (ys : List Var), ¬ HSteps sig 0 e H' (.ret (ys.map .var)) := by
  refine ⟨cexFnSig, .call "f" (.ret [.fn "g"]) (.ret []), [], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro fd hfd
    simp only [cexFnSig, List.mem_cons, List.not_mem_nil, or_false] at hfd
    rcases hfd with rfl | rfl
    · refine ⟨by decide, ?_⟩
      simp only [cexFnF, Binder.ctx, Binder.vars, List.map_cons, List.map_nil]
      refine LWf.dup (Γ := 0) _ (.inl (by simp)) ?_
      simpa using LWf.drop (funs := LSig.funs cexFnSig)
        (Δ := ({Var.name "y"} : List Var).toFinset) (Γ := 0) (.name "y") (.tuple .nil)
    · exact ⟨by decide, by simpa [cexFnG, Binder.ctx] using
        (LWf.tuple (funs := LSig.funs cexFnSig) (Δ := ∅) .nil)⟩
  · intro fd hfd
    simp only [cexFnSig, List.mem_cons, List.not_mem_nil, or_false] at hfd
    rcases hfd with rfl | rfl
    · exact .dup _ _ (.var _) (.drop _ _ (.var _) (.ret _ (by simp)))
    · exact .ret _ (by simp)
  · exact LWf.call _ _ _ (by decide) (by simp [LBorrowArg, cexFnSig, cexFnF, cexFnG])
      (.tuple .nil)
  · refine Relation.ReflTransGen.head (LStep.step .hole (LHead.call _ cexFnF [.fn "g"] []
      cexFn_lookup rfl rfl)) ?_
    simp only [LECtx.plug]
    rw [cexFn_body]
    refine Relation.ReflTransGen.head (LStep.step .hole (LHead.dup _ _)) ?_
    exact Relation.ReflTransGen.head (LStep.step .hole (LHead.drop _ _)) .refl
  · intro h
    cases h with
    | call _ _ _ h1 _ => cases h1 with | ret _ h => exact absurd (h (.fn "g") (by simp)) (by intro h; cases h)
  · intro H' ys hs
    obtain ⟨-, h | h⟩ := HSteps.cexFn hs rfl
    · cases h
    · cases h

end FIP.Lam
