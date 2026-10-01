module

public import RequestProject.FIP.Stack

@[expose] public section

/-!
# The stated bound of Theorem 4 is false

`stack_bound` states `|E| ≤ |e_max| · |Σ|²` for every decomposition `E[e']` of every
expression reached from a call `f(ȳ; x̄)`.  Already the initial expression is a
counterexample when `|e_max| = 0`: for the identity function `f(; x) = x` (whose body `x`
has depth `0`), the call `f(; l)` itself decomposes as `E[l]` with `E = f(; □)` of depth `1`,
while `|e_max| · |Σ|² = 0`.
-/

namespace FIP

/-- The statement of Theorem 4 as formalized in `stack_bound`. -/
def StackBoundClaim : Prop :=
  ∀ {sig : Sig} (_hsig : sig.PaperFragment) {groups : List (List FName)}
    (_hss : sig.StackSafe groups) {fbip : Bool} {f : FName} {fd : FunDef}
    (_hf : sig.lookup f = some fd) (_hfip : fd.annot ≠ .plain) {ys xs : List Var}
    {S₁ S₂ : Store} (_hd : S₁.Disjoint S₂) (_hy : ∀ y ∈ ys, y ∈ S₁.dom) (_hS₁ : S₁.Sound)
    (_hx : S₂.roots = (xs : Multiset Var).map Res.var) (_hS₂ : S₂.Linear)
    (_hnofn : ∀ x c as, Cell.bind x c as ∈ S₁ + S₂ → ∀ a ∈ as, ∀ g, a ≠ .fn g)
    {S' : Store} {e : Expr}
    (_h : SSteps sig fbip (S₁ + S₂) (.call f (.ret (ys.map .var)) (.ret (xs.map .var))) S' e)
    (E : ECtx) (e' : Expr) (_he : e = E.plug e'),
    E.depth ≤ sig.maxDepth * sig.length ^ 2

/-- The identity function `f(; x) = x`, annotated `fip`. -/
def idFun : FunDef where
  name := "f"
  borrowed := []
  owned := [{ name := "x" }]
  body := .ret [.var (.name "x")]
  annot := .fip 0

/-- The statement of Theorem 4 in `stack_bound` is false. -/
theorem not_stackBoundClaim : ¬ StackBoundClaim := by
  intro H
  let S₂ : Store := {Cell.bind (.loc 0) "C" []}
  have hwf : idFun.Wf [idFun] := by
    refine ⟨by decide, ?_⟩
    have := WfVals.cons (U := ∅) (Δ := ∅) _ _ _ _ (WfVal.var (.name "x")) WfVals.nil
    simp only [add_zero] at this
    have h := Wf.tuple (cfg := Sig.cfg [idFun] idFun.annot) this
    simpa [idFun, FunDef.ownedCtx, FunDef.scalars, Binder.owned, Binder.scalars,
      Binder.ownedSet, Annot.budget] using h
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
