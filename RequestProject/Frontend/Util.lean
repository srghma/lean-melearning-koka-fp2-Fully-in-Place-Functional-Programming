module

public import RequestProject.Frontend.Elab

@[expose] public section

/-!
# Helpers for running compiled Koka code

Values of Koka lists as core values, a chain of calls threading an accumulator, and the
tactic `koka_eval` that computes the result of `Koka.Module.eval` (or `evalExpr`,
`evalFold`) by running the interpreter in the kernel.
-/

namespace Koka

open FIP

/-- A Koka `list<int>` as a core value (`Nil` and `Cons` are built-in constructors, in
    scope in every module). -/
def listV : List Int → Val 0
  | [] => .ctor "Nil" []
  | x :: xs => .ctor "Cons" [.lit x, listV xs]

/-- The integers of a `list<int>` value of length less than `n`. -/
def ofListVN : Nat → Val 0 → Option (List Int)
  | _ + 1, .ctor "Nil" [] => some []
  | n + 1, .ctor "Cons" [.lit x, xs] => (ofListVN n xs).map (x :: ·)
  | _, _ => none

/-- The integers of a `list<int>` value (of length less than 1000). -/
def ofListV : Val 0 → Option (List Int) := ofListVN 1000

/-- Thread a value through successive calls `f(; acc, args₁)`, `f(; acc, args₂)`, …,
    starting from `acc = init`, as a chain of `let`s. -/
def foldCalls (f : FName) (init : Val 0) (argss : List (List (Val 0))) : FIP.Expr 0 :=
  go (.ret [init]) argss
where
  go (acc : FIP.Expr 0) : List (List (Val 0)) → FIP.Expr 0
    | [] => acc
    | args :: rest =>
      go (.letIn [false] acc
        (.call f (.ret []) (.ret (.var (.bvar ⟨0, by simp⟩) :: args.map (Val.shift 1))))) rest

/-- The result of `foldCalls` for a function `f` of the module. -/
def Module.evalFold {F : Finset FName} {C : Finset CName} (m : Module F C) (f : FName)
    (init : Val 0) (argss : List (List (Val 0))) (hf : f ∈ F := by decide)
    (h : (foldCalls (m.fn f hf).name init argss).Halts m.sig := by fip_halts) : List (Val 0) :=
  m.evalExpr _ h

/-- `koka_eval` proves a statement about the results of `Module.eval`, `Module.evalExpr`
    or `Module.evalFold` by running the interpreter in the kernel: the result of the total
    evaluator is the one found with enough fuel (`FIP.Expr.evalTotal_eq_run`). -/
macro "koka_eval" : tactic =>
  `(tactic| (simp only [Koka.Module.eval, Koka.Module.evalFold, Koka.Module.evalExpr]
             repeat' rw [FIP.Expr.evalTotal_eq_run (k := 1000000)]
             all_goals decide +kernel))

end Koka
