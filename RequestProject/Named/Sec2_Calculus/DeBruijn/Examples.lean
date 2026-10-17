module

public import RequestProject.Named.Sec2_Calculus.DeBruijn.Simulation
public import RequestProject.Named.Sec1_Overview.Intro
public import RequestProject.Named.Sec3_Traversals.Plain
public import RequestProject.Named.AppA_Examples.RedBlack
public import RequestProject.Named.AppA_Examples.MergeSort
public import RequestProject.Named.AppA_Examples.QuickSort
public import RequestProject.Named.AppA_Examples.FingerTree

@[expose] public section

/-!
# The paper's programs as well-scoped de Bruijn terms

Every KokaNamed module of the paper, compiled by `[NKOKA| … ]` / `[NKOKA_FIP| … ]`, is well
scoped: each function body becomes a `Term (|x̄| + |ȳ|)` whose only free variables are
the parameters (`…_scoped`).  By the simulation theorem
(`RequestProject/Sec2_Calculus/DeBruijn/Simulation.lean`), the evaluations proved for the
named programs carry over to their de Bruijn representations; `reverse_db` does this for
`reverse([1,2,3,4,5]) = [5,4,3,2,1]` of §1.
-/

namespace ExamplesNamed.DeBruijn

open KokaNamed FIPNamed

theorem intro_scoped : ExamplesNamed.Intro.intro.sig.toTSig.isSome := by decide
theorem plain_scoped : ExamplesNamed.Plain.plain.sig.toTSig.isSome := by decide
theorem tmapZipper_scoped : ExamplesNamed.Plain.tmapZipper.sig.toTSig.isSome := by decide
theorem rbtree_scoped : ExamplesNamed.RedBlack.rbtree.sig.toTSig.isSome := by decide
theorem mergesort_scoped : ExamplesNamed.MergeSort.mergesort.sig.toTSig.isSome := by decide
theorem quicksort_scoped : ExamplesNamed.QuickSort.quicksort.sig.toTSig.isSome := by decide
theorem fbipQuicksort_scoped : ExamplesNamed.QuickSort.fbipQuicksort.sig.toTSig.isSome := by decide
theorem fingertree_scoped : ExamplesNamed.FingerTree.fingertree.sig.toTSig.isSome := by decide

/-- `reverse([1,2,3,4,5]) = [5,4,3,2,1]` (§1), in the de Bruijn semantics: the call is a
    closed term `t : Term 0`, and it reduces in the well-scoped signature to the closed
    tuple representing `[5,4,3,2,1]`. -/
theorem reverse_db :
    ∃ tsig, ExamplesNamed.Intro.intro.sig.toTSig = some tsig ∧
      ∃ t : Term 0,
        (ExamplesNamed.Intro.intro.callE "reverse" [] [listV [1, 2, 3, 4, 5]]).toClosed = some t ∧
      ∃ ts : List (TVal 0),
        Val.toTVals Scope.empty [listV [5, 4, 3, 2, 1]] = some ts ∧ TSteps tsig t (.ret ts) := by
  obtain ⟨tsig, hsig⟩ := Option.isSome_iff_exists.mp intro_scoped
  have hc : (ExamplesNamed.Intro.intro.callE "reverse" [] [listV [1, 2, 3, 4, 5]]).toClosed.isSome := by
    decide
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hc
  have hs := Module.run_sound ExamplesNamed.Intro.reverse_example
  obtain ⟨t', ht', hts⟩ := Steps.toClosed hsig hs ht
  have hr : (Val.toTVals Scope.empty [listV [5, 4, 3, 2, 1]]).isSome := by decide
  obtain ⟨ts, hts'⟩ := Option.isSome_iff_exists.mp hr
  refine ⟨tsig, hsig, t, ht, ts, hts', ?_⟩
  simp only [Expr.toClosed, Expr.toTerm, hts', Option.map_some, Option.some.injEq] at ht'
  exact ht' ▸ hts

end ExamplesNamed.DeBruijn
