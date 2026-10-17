module

public import RequestProject.AppC_StackBound.Stack

@[expose] public section

/- ══════════════════ PAPER sec. 2.6, App. C START: Stack Safe FIP: Theorem 4; Stack Bound (PDF p. 14; App. C on pp. 54-67) ══════════════════
   `not_stackBoundClaim`: `|E| <= |e_max| * |Sigma|^2` already fails for the identity function. -/

/-!
# The stated bound of Theorem 4 is false

The paper's Theorem 4 states `|E| ≤ |e_max| · |Σ|²` for every decomposition `E[e']` of every
expression reached from a call `f(ȳ; x̄)`.  Already the initial expression is a
counterexample when `|e_max| = 0`: for the identity function `f(; x) = x` (whose body `x`
has depth `0`), the call `f(; l)` itself decomposes as `E[l]` with `E = f(; □)` of depth `1`,
while `|e_max| · |Σ|² = 0`.
-/

namespace FIP

/-- The statement of Theorem 4 with the paper's bound. -/
def StackBoundClaim : Prop :=
  ∀ {sig : Sig} (_hsig : sig.PaperFragment) {groups : List (List FName)}
    (_hss : sig.StackSafe groups) {fbip : Bool} {f : FName} {fd : FunDef}
    (_hf : sig.lookup f = some fd) (_hfip : fd.annot ≠ .plain) {ys xs : List (Var 0)}
    {S₁ S₂ : Store} (_hd : S₁.Disjoint S₂) (_hy : ∀ y ∈ ys, y ∈ S₁.dom) (_hS₁ : S₁.Sound)
    (_hx : S₂.roots = (xs : Multiset (Var 0)).map Res.var) (_hS₂ : S₂.Linear)
    (_hnofn : ∀ x c as, Cell.bind x c as ∈ S₁ + S₂ → ∀ a ∈ as, ∀ g, a ≠ .fn g)
    {S' : Store} {e : Expr 0}
    (_h : SSteps sig fbip (S₁ + S₂) (.call f (.ret (ys.map .var)) (.ret (xs.map .var))) S' e)
    (E : ECtx 0) (e' : Expr 0) (_he : e = E.plug e'),
    E.depth ≤ sig.maxDepth * sig.length ^ 2

/-- The identity function `f(; x) = x`, annotated `fip`. -/
def idFun : FunDef where
  name := "f"
  borrowed := []
  owned := [false]
  body := .ret [.var (.bvar 0)]
  annot := .fip 0

/-- The statement of Theorem 4 with the paper's bound is false. -/
theorem not_stackBoundClaim : ¬ StackBoundClaim := by
  intro H
  let S₂ : Store := {Cell.bind (.loc 0) "C" []}
  have hctx : idFun.ownedCtx = {Res.var (.bvar ⟨0, by simp [idFun]⟩)} := by decide
  have hsc : idFun.scalars = ∅ := by decide
  have hwf : idFun.Wf [idFun] := by
    unfold FunDef.Wf
    rw [hctx, hsc]
    have := WfVals.cons (U := ∅) (Δ := idFun.borrowedSet) _ _ _ _ (WfVal.var (.bvar ⟨0, by simp [idFun]⟩))
      WfVals.nil
    simp only [add_zero] at this
    exact Wf.tuple this
  have hsig : Sig.PaperFragment [idFun] :=
    ⟨by simp, by
      intro fd hfd _
      simp only [List.mem_singleton] at hfd
      subst hfd; exact hwf,
     by simp [idFun, Expr.scalarFree, Val.scalarFreeList, Val.scalarFree],
     by simp [idFun, Annot.budget]⟩
  have hss : Sig.StackSafe [idFun] [["f"]] := by
    refine ⟨by simp [idFun], ?_⟩
    intro i hi g hg fd hfd
    simp only [List.length_singleton, Nat.lt_one_iff] at hi
    subst hi
    simp only [List.getElem_singleton, List.mem_singleton] at hg
    subst hg
    simp only [Sig.lookup, List.find?, idFun, beq_self_eq_true, Option.some.injEq] at hfd
    subst hfd
    refine ⟨.base _ ?_, ?_⟩
    · simp [Expr.Avoids, Expr.funs, Val.funsList, Val.funs]
    · simp [Expr.funs, Val.funsList, Val.funs]
  have := H hsig hss (fbip := false) (f := "f") (fd := idFun) (by simp [Sig.lookup, idFun])
    (by simp [idFun]) (ys := []) (xs := [.loc 0]) (S₁ := 0) (S₂ := S₂)
    (by simp [Store.Disjoint]) (by simp) (by simp [Store.Sound])
    (by simp [S₂, Store.roots, Cell.dom, Cell.fv, Cell.credits, Val.fvList])
    (by refine ⟨⟨?_, ?_⟩, ?_⟩ <;> simp [S₂, Cell.dom, Cell.fv, Val.fvList])
    (by intro x c as hc a ha; simp only [S₂, zero_add, Multiset.mem_singleton, Cell.bind.injEq] at hc
        rw [hc.2.2] at ha; simp at ha)
    (.refl _ _) (.callO "f" [] .hole) (.ret [.var (.loc 0)]) rfl
  simp [ECtx.depth, Sig.maxDepth, idFun, Expr.depth, Val.depth] at this

end FIP

/- ══════════════════ PAPER sec. 2.6, App. C END: Stack Safe FIP: Theorem 4; Stack Bound ══════════════════ -/
