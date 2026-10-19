module

public import RequestProject.Frontend.Compile
meta import RequestProject.Frontend.Compile

@[expose] public section

/-!
# The front end terminates on every input

The lexer, the parser and the compiler are total functions (no `partial`, no fuel), so
`[KOKA| … ]` cannot loop.  Inputs that used to make the compiler unfold a definition
forever are now handled: a recursive value type is reported as an error, and a recursive
type alias is left folded inside its own expansion.
-/

namespace Koka.Robustness

/-- A value type that contains itself cannot be unboxed: the compiler reports it. -/
def recursiveValueType : String := "value type v { V(x : v, y : int) }
fun f(a : int) : v
  f(a)
fun g(a : int) : int
  match f(a)
    V(_, y) -> y
"

#guard match compileSource recursiveValueType with
  | .error e => e == "in function 'g': recursive value type 'v'"
  | .ok _ => false

/-- A recursive type alias is expanded once and then left folded. -/
def recursiveAlias : String := "alias a = list<a>
fun f(xs : a) : a
  xs
"

#guard (compileSource recursiveAlias).toBool

-- An unterminated comment is a lexer error, not a loop.
#guard !(compileSource "fun f(x : int) : int /* x").toBool

end Koka.Robustness
