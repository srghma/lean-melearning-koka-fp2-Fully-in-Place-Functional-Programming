module

public import RequestProject.Frontend.Util

@[expose] public section

/-!
# Why the evaluator needs a proof of termination

`Koka.Module.eval` has no fuel, but asks for a proof that the call terminates
(`FIP.Expr.Halts`).  This premise cannot be dropped: the calculus has general recursion,
and even a *fully in-place* function may loop.  `loop` below is accepted by the FIP check,
its call `loop(0)` steps to itself forever, and therefore no function `Sig → Expr 0 →
List (Val 0)` can be a sound evaluator for every expression (`no_sound_total_eval`).
-/

namespace Examples.Divergence

open Koka FIP

/-- A fully in-place function that never returns. -/
def loopM := [KOKA_FIP|
fip fun loop( x : int ) : int
  loop(x)
]

/-- `loop` is fully in-place. -/
theorem loop_wf : loopM.sig.Wf := loopM.wf

/-- The call `loop(0)` does not terminate. -/
theorem loop_diverges : ¬ (loopM.callE "loop" (by decide) [] [.lit 0]).Halts loopM.sig :=
  Expr.not_halts_of_step_self rfl

/-- There is no sound evaluator that is total without a termination premise: no function
    `ev` gives, for every signature and closed expression, values that the expression
    reduces to. -/
theorem no_sound_total_eval :
    ¬ ∃ ev : Sig → FIP.Expr 0 → List (Val 0), ∀ sig e, Steps sig e (.ret (ev sig e)) := by
  rintro ⟨ev, hev⟩
  exact loop_diverges (Expr.halts_iff.mpr ⟨_, hev _ _⟩)

end Examples.Divergence
