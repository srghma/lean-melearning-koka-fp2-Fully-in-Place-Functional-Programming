module

public import RequestProject.AppE_HeapSoundness.LamSubst

@[expose] public section

/- ══════════════════ PAPER sec. 5.3, App. E START: Soundness of the Heap Semantics: Theorem 6 (PDF pp. 25-26; App. E.2-E.6 on pp. 75-85) ══════════════════
   Two counterexamples to Theorem 6 as stated: `heap_sound_needs_adm` and
   `heap_sound_needs_no_fn`. -/

/-!
# Theorem 6 as stated needs extra hypotheses

Theorem 6 states that for a well-formed expression `∅ | Γ ⊢ e`, evaluated in a linear heap
`H` whose roots are `Γ`, if `[H]e` evaluates (functionally) to values, then the heap
semantics evaluates `e` to values as well.  Two features of `λfip` break this.

* **The size in `dropru`.**  The typing rule for `dropru x; e` does not check that the size
  `k` recorded in `dropru x k` is the size of the cell bound to `x`, while the heap semantics
  only reduces `dropru x k` when it is.  With `x ↦¹ C` (a cell with no fields),
  `dropru x 1; free 1; ()` is well-formed with owned environment `x`, reduces functionally to
  `()` whatever `x` denotes, and has no heap reduction at all (`heap_sound_needs_adm`).
* **Function values.**  A top-level function may be passed as a borrowed argument, and a
  borrowed argument may be duplicated and dropped, but the heap semantics has no rule for
  `dup f` or `drop f`.  With `f(y;) = dup y; drop y; ()` and `g() = ()`, the closed
  expression `f(g;)` reduces functionally to `()`, while the heap semantics gets stuck at
  `dup g; drop g; ()` (`heap_sound_needs_no_fn`).

So a correct version of Theorem 6 must restrict `dropru` to the reuse-drop of a match on
`x` (where the size is right) and exclude function values from the heap semantics.
-/

namespace FIP.Lam

/-! ## The size in `dropru` -/

/-- The heap `x ↦¹ C` for the location `x = 0`. -/
def cexHeap : Heap := {HCell.bind (.loc 0) 1 (.con "C" [])}

/-- `dropru x 1; free 1; ()` for the location `x = 0`. -/
def cexDropru : LExpr 0 := .dropru (.var (.loc 0)) 1 (.free 1 (.ret .nil))

/-- `dropru y 1; e` is stuck in a heap whose constructor cells have no fields. -/
theorem HStep.stuck_dropru {sig : LSig} {H H' : Heap} {e0 e' e1 : LExpr 0} {y : Var 0}
    (hH : ∀ x n c zs, HCell.bind x n (.con c zs) ∈ H → zs = [])
    (he : e0 = .dropru (.var y) 1 e1) : ¬ HStep sig H e0 H' e' := by
  intro h
  cases h with
  | head E hh =>
    cases E <;> simp only [LECtx.plug, reduceCtorEq] at he
    cases hh with
    | dropru H₀ x n c zs e =>
      have := hH x (n + 2) c zs (by simp)
      subst this
      simp at he
    | dconru H₀ x c zs e =>
      have := hH x 1 c zs (by simp)
      subst this
      simp at he
    | _ => simp at he
  | val E done V rest hd hV hv =>
    cases E <;> simp [LECtx.plug] at he

theorem HSteps.stuck_dropru {sig : LSig} {H H' : Heap} {e0 e' e1 : LExpr 0} {y : Var 0}
    (hH : ∀ x n c zs, HCell.bind x n (.con c zs) ∈ H → zs = [])
    (h : HSteps sig H e0 H' e') (he : e0 = .dropru (.var y) 1 e1) : H' = H ∧ e' = e0 := by
  induction h with
  | refl => exact ⟨rfl, rfl⟩
  | tail _ hs ih =>
    obtain ⟨rfl, rfl⟩ := ih he
    exact (HStep.stuck_dropru hH he hs).elim

/-- Without a restriction on `dropru`, Theorem 6 fails: the expression is well-formed, the
    heap is linear with the right roots, the expression evaluates functionally whatever
    the location denotes, and the heap semantics never takes a step. -/
theorem heap_sound_needs_adm :
    LSig.Wf [] ∧ LWf (LSig.funs []) ∅ {Res.var (.loc 0)} cexDropru ∧ cexHeap.Linear ∧
    ({Res.var (.loc 0)} : Ctx 0) = cexHeap.roots ∧
    (∀ σ, LSteps [] (cexDropru.substLoc σ) (.ret .nil)) ∧
    ∀ H' e', HSteps [] cexHeap cexDropru H' e' → H' = cexHeap ∧ e' = cexDropru := by
  refine ⟨by simp [LSig.Wf], ?_, ?_, ?_, ?_, fun H' e' h => ?_⟩
  · have h0 : LWf (LSig.funs []) ∅ (0 : Ctx 0) (.ret .nil) := LWf.tuple LVals.nil LWfVals.nil
    have h1 := LWf.free 1 le_rfl h0
    have h2 := LWf.dropru (Γ := 0) (Var.loc 0) 1 h1
    rwa [zero_add] at h2
  · refine ⟨⟨by simp [cexHeap, Heap.dom], ?_, ?_⟩, ?_⟩
    · intro x n o h; simp [cexHeap] at h; omega
    · simp [cexHeap, Heap.rngFv, HObj.fv, LVal.fvList]
    · intro x n o h; simp [cexHeap, Heap.rngFv, HObj.fv, LVal.fvList]
  · simp [cexHeap, Heap.roots, Heap.rngFv, HObj.fv, LVal.fvList]
  · intro σ
    refine Relation.ReflTransGen.head (LStep.step .hole (LHead.dropru _ _ _)) ?_
    exact Relation.ReflTransGen.head (LStep.step .hole (LHead.free _ _)) .refl
  · exact HSteps.stuck_dropru (fun x n c zs hc => by
      simp only [cexHeap, Multiset.mem_singleton, HCell.bind.injEq, HObj.con.injEq] at hc
      exact hc.2.2.2) h rfl

/-! ## Function values passed as borrowed arguments -/

/-- `f(y;) = dup y; drop y; ()`. -/
def cexFnF : LFunDef :=
  { name := "f", borrowed := 1, owned := 0,
    body := .dup (.var (.bvar 0)) (.drop (.var (.bvar 0)) (.ret .nil)) }

/-- `g() = ()`. -/
def cexFnG : LFunDef := { name := "g", borrowed := 0, owned := 0, body := .ret .nil }

/-- The signature `f, g`. -/
def cexFnSig : LSig := [cexFnF, cexFnG]

/-- The call `f(g;)`. -/
def cexFnCall : LExpr 0 := .call "f" (.ret (.cons (.fn "g") .nil)) (.ret .nil)

/-- The body of `f` with `g` substituted for `y`: `dup g; drop g; ()`. -/
def cexFnStuck : LExpr 0 := .dup (.fn "g") (.drop (.fn "g") (.ret .nil))

theorem cexFn_instBody : cexFnF.instBody [.fn "g"] [] = cexFnStuck := rfl

theorem cexFnCall_step {H H' : Heap} {e0 e' : LExpr 0} (h : HStep cexFnSig H e0 H' e')
    (he : e0 = cexFnCall) : H' = H ∧ e' = cexFnStuck := by
  cases h with
  | head E hh =>
    cases E with
    | hole =>
      simp only [LECtx.plug] at he ⊢
      subst he
      cases hh with
      | call _ _ fd as1 as2 hl _ _ _ =>
        obtain rfl : cexFnF = fd := by simpa [cexFnF, cexFnSig, LSig.lookup] using hl
        exact ⟨rfl, rfl⟩
    | callB f E e2 =>
      cases E <;> simp only [LECtx.plug, cexFnCall, LExpr.call.injEq, reduceCtorEq, false_and,
        and_false] at he
      obtain ⟨-, rfl, -⟩ := he
      cases hh
    | callO f vs E =>
      cases E <;> simp only [LECtx.plug, cexFnCall, LExpr.call.injEq, reduceCtorEq,
        and_false] at he
      obtain ⟨-, -, rfl⟩ := he
      cases hh
    | _ => simp [LECtx.plug, cexFnCall] at he
  | val E done V rest hd hV hv =>
    exfalso
    cases E with
    | callB f E e2 =>
      cases E <;> simp only [LECtx.plug, cexFnCall, LExpr.call.injEq, reduceCtorEq, false_and,
        and_false, LExpr.ret.injEq] at he
      obtain ⟨-, h1, -⟩ := he
      have h2 := congrArg LVals.toList h1
      simp only [LVals.toList_ofList, LVals.toList_cons, LVals.toList_nil] at h2
      rcases done with _ | ⟨d, done⟩
      · simp only [List.nil_append, List.cons.injEq] at h2
        obtain ⟨h3, -⟩ := h2
        cases V <;> simp only [LVCtx.plug, reduceCtorEq] at h3
        subst h3
        cases hv
      · simp at h2
    | callO f vs E =>
      cases E <;> simp only [LECtx.plug, cexFnCall, LExpr.call.injEq, reduceCtorEq,
        and_false, LExpr.ret.injEq] at he
      have h2 := congrArg LVals.toList he.2.2
      simp at h2
    | _ => simp [LECtx.plug, cexFnCall] at he

theorem cexFnStuck_stuck {H H' : Heap} {e0 e' : LExpr 0} (he : e0 = cexFnStuck) :
    ¬ HStep cexFnSig H e0 H' e' := by
  intro h
  cases h with
  | head E hh =>
    cases E <;> simp only [LECtx.plug, cexFnStuck, reduceCtorEq] at he
    subst he
    cases hh
  | val E done V rest hd hV hv =>
    cases E <;> simp [LECtx.plug, cexFnStuck] at he

theorem cexFn_steps {H H' : Heap} {e0 e' : LExpr 0} (h : HSteps cexFnSig H e0 H' e')
    (he : e0 = cexFnCall) : H' = H ∧ (e' = cexFnCall ∨ e' = cexFnStuck) := by
  induction h with
  | refl => exact ⟨rfl, .inl he⟩
  | tail _ hs ih =>
    obtain ⟨rfl, rfl | rfl⟩ := ih he
    · exact ⟨(cexFnCall_step hs rfl).1, .inr (cexFnCall_step hs rfl).2⟩
    · exact (cexFnStuck_stuck rfl hs).elim

/-- Function values break Theorem 6: `f(g;)` is well-formed in a well-formed signature and
    reduces functionally to `()`, but the heap semantics (from the empty heap) never
    reaches a value: it gets stuck at `dup g; drop g; ()`. -/
theorem heap_sound_needs_no_fn :
    cexFnSig.Wf ∧ LWf cexFnSig.funs ∅ 0 cexFnCall ∧ LSteps cexFnSig cexFnCall (.ret .nil) ∧
    ∀ H' vs, ¬ HSteps cexFnSig 0 cexFnCall H' (.ret vs) := by
  refine ⟨?_, ?_, ?_, fun H' vs h => ?_⟩
  · intro fd hfd
    simp only [cexFnSig, List.mem_cons, List.not_mem_nil, or_false] at hfd
    rcases hfd with rfl | rfl
    · have h0 : LWf cexFnSig.funs (bSet 0 1) (0 : Ctx (0 + 1)) (.ret .nil) :=
        LWf.tuple LVals.nil LWfVals.nil
      have h1 := LWf.drop (Var.bvar 0) h0
      have h2 := LWf.dup (Γ := 0) (Var.bvar 0) (by simp [bSet, Var.newB]) h1
      simpa [cexFnF, allCtx, Ctx.shift] using h2
    · simpa [cexFnG, allCtx, Ctx.shift] using
        (LWf.tuple (funs := cexFnSig.funs) (Δ := bSet 0 0) LVals.nil LWfVals.nil)
  · exact LWf.call "f" _ _ (by simp [cexFnSig, LSig.funs, cexFnF])
      (by simp [LBorrowArg, cexFnSig, LSig.funs, cexFnG]) (LWf.tuple LVals.nil LWfVals.nil)
  · refine Relation.ReflTransGen.head (LStep.step .hole (LHead.call "f" cexFnF _ _ rfl rfl rfl)) ?_
    refine Relation.ReflTransGen.head (LStep.step .hole (LHead.dup _ _)) ?_
    exact Relation.ReflTransGen.head (LStep.step .hole (LHead.drop _ _)) .refl
  · rcases (cexFn_steps h rfl).2 with h' | h' <;> simp [cexFnCall, cexFnStuck] at h' 

end FIP.Lam

/- ══════════════════ PAPER sec. 5.3, App. E END: Soundness of the Heap Semantics: Theorem 6 ══════════════════ -/
