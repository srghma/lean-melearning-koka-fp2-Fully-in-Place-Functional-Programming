module

public import RequestProject.Named.Frontend.Elab

@[expose] public section

/-!
# Helpers for running compiled KokaNamed code

Values of KokaNamed data types as core values, and a function to run a call of a compiled
function with the interpreter of the functional semantics (`FIPNamed.Expr.eval`), whose
result is justified by `FIPNamed.Expr.eval_sound`.
-/

namespace KokaNamed

open FIPNamed

/-- A KokaNamed `list<int>` as a core value. -/
def listV : List Int → Val
  | [] => .ctor "Nil" []
  | x :: xs => .ctor "Cons" [.lit x, listV xs]

/-- An atom (a constructor without fields). -/
def atom (c : String) : Val := .ctor c []

/-- The call `f(borrowed; owned)` of a function of the module. -/
def Module.callE (_m : Module) (f : String) (borrowed owned : List Val) : FIPNamed.Expr :=
  .call f (.ret borrowed) (.ret owned)

/-- Run the call `f(borrowed; owned)` for at most `fuel` steps. -/
def Module.run (m : Module) (f : String) (borrowed owned : List Val) (fuel : Nat := 10000) :
    Option (List Val) :=
  (m.callE f borrowed owned).eval m.sig fuel

/-- A successful run is a reduction sequence of the functional semantics. -/
theorem Module.run_sound {m : Module} {f : String} {b o vs : List Val} {fuel : Nat}
    (h : m.run f b o fuel = some vs) : Steps m.sig (m.callE f b o) (.ret vs) :=
  Expr.eval_sound h

/-- Thread a value through successive calls `f(; acc, args₁)`, `f(; acc, args₂)`, …,
    starting from `acc = init`, as a chain of `let`s. -/
def foldCalls (f : String) (init : Val) (argss : List (List Val)) : FIPNamed.Expr :=
  go "acc#" (.ret [init]) argss
where
  go (x : String) (acc : FIPNamed.Expr) : List (List Val) → FIPNamed.Expr
    | [] => acc
    | args :: rest =>
      go (x ++ "'") (.letIn [{ name := x }] acc (.call f (.ret []) (.ret (.var (.name x) :: args))))
        rest

/-- Run `foldCalls` with the interpreter. -/
def Module.runFold (m : Module) (f : String) (init : Val) (argss : List (List Val))
    (fuel : Nat := 100000) : Option (List Val) :=
  (foldCalls f init argss).eval m.sig fuel

/-- A successful `runFold` is a reduction sequence of the functional semantics. -/
theorem Module.runFold_sound {m : Module} {f : String} {init : Val} {argss : List (List Val)}
    {vs : List Val} {fuel : Nat} (h : m.runFold f init argss fuel = some vs) :
    Steps m.sig (foldCalls f init argss) (.ret vs) :=
  Expr.eval_sound h

/-- The integers of a `list<int>` value of length less than `n`. -/
def ofListVN : Nat → Val → Option (List Int)
  | _ + 1, .ctor "Nil" [] => some []
  | n + 1, .ctor "Cons" [.lit x, xs] => (ofListVN n xs).map (x :: ·)
  | _, _ => none

/-- The integers of a `list<int>` value (of length less than 1000). -/
def ofListV : Val → Option (List Int) := ofListVN 1000

end KokaNamed
