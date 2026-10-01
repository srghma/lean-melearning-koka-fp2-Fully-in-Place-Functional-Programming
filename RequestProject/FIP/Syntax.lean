module

public import Mathlib

@[expose] public section

/-!
# The syntax of the FIP calculus (Fig. 2, Fig. 6 of the paper)

This file formalizes the grammar of the *fully in-place* (FIP) calculus of
Lorenzen, Leijen and Swierstra, "FP²: Fully in-Place Functional Programming"
(ICFP 2023), together with the FBIP extension (`drop x; e` and `free k; e`, Fig. 6).

```
e ::= v | e e | f(e; e) | let x̄ = e in e | match e { p ↦ e } | match! e { p ↦ e }
    | (v, ..., v) | drop x; e | free k; e
v ::= x | C^k v1 ... vk | f
p ::= C^k x1 ... xk
Σ ::= ∅ | Σ, f(ȳ; x̄) = e
```

## Representation choices

* **Variables.** A variable `Var` is either a *name* (`Var.name s`), which is what a
  program binds, or a store *location* (`Var.loc n`), which is what the store semantics
  (Fig. 5) allocates.  Binders are always names, so substituting locations for names
  can never capture.
* **Unboxed tuples.** `Expr.ret vs` is the unboxed tuple `(v1, ..., vn)`; a value `v`
  used as an expression is the singleton tuple `(v)`, written `Expr.val v`.
* **Top-level functions as values.** `Val.fn f` is a top-level function `f ∈ dom(Σ)`
  passed as a (borrowed) argument; `(f) v̄` is `Expr.app (Expr.val (Val.fn f)) e`.

## Extension: unboxed scalars

The examples of Appendix A use Koka *value types* (`int32`, `bool`, enumerations such
as `color`), whose values need no heap cell and may be freely duplicated and discarded
by the Koka implementation.  To express these examples we add, **beyond the paper's
Fig. 2**,

* scalar literals `Val.lit n`,
* primitive operations on scalars `Expr.prim op v̄` (comparisons returning the atoms
  `True`/`False`),
* a flag `Binder.scalar` on binders: a binder whose type is a value type binds a
  *scalar* variable, which the FIP rules treat as unrestricted (see
  `RequestProject/FIP/Rules.lean`).

The paper's calculus is exactly the fragment without literals, primitives and scalar
binders.
-/

namespace FIP

/-- Names of top-level functions. -/
abbrev FName := String
/-- Names of constructors. -/
abbrev CName := String

/-- A variable: either a program name, or a location of the store semantics. -/
inductive Var where
  | name (s : String)
  | loc (n : Nat)
  deriving DecidableEq, Repr, Inhabited, Hashable, Lean.ToExpr

instance : Coe String Var := ⟨Var.name⟩

/-- A binder: a variable name together with a flag saying whether it binds an unboxed
    scalar (a Koka value type).  In the paper's calculus every binder has
    `scalar = false`. -/
structure Binder where
  name : String
  scalar : Bool := false
  deriving DecidableEq, Repr, Inhabited, Lean.ToExpr

/-- Values `v ::= x | C^k v1 ... vk | f` (and scalar literals, an extension). -/
inductive Val where
  /-- a variable `x` -/
  | var (x : Var)
  /-- a top-level function `f ∈ dom(Σ)` used as a value -/
  | fn (f : FName)
  /-- a constructor of arity `k = args.length`; an *atom* when `k = 0` -/
  | ctor (c : CName) (args : List Val)
  /-- an unboxed scalar literal (extension, e.g. an `int32`) -/
  | lit (n : Int)
  deriving Repr, Inhabited, Lean.ToExpr

mutual
/-- Decidable equality of values. -/
def Val.decEq : (a b : Val) → Decidable (a = b)
  | .var x, .var y => if h : x = y then isTrue (by rw [h]) else isFalse (by grind)
  | .fn f, .fn g => if h : f = g then isTrue (by rw [h]) else isFalse (by grind)
  | .lit n, .lit m => if h : n = m then isTrue (by rw [h]) else isFalse (by grind)
  | .ctor c as, .ctor d bs =>
    if h : c = d then
      match Val.decEqList as bs with
      | isTrue h' => isTrue (by rw [h, h'])
      | isFalse h' => isFalse (by grind)
    else isFalse (by grind)
  | .var _, .fn _ | .var _, .ctor _ _ | .var _, .lit _
  | .fn _, .var _ | .fn _, .ctor _ _ | .fn _, .lit _
  | .ctor _ _, .var _ | .ctor _ _, .fn _ | .ctor _ _, .lit _
  | .lit _, .var _ | .lit _, .fn _ | .lit _, .ctor _ _ => isFalse (by grind)
/-- Decidable equality of lists of values. -/
def Val.decEqList : (a b : List Val) → Decidable (a = b)
  | [], [] => isTrue rfl
  | [], _ :: _ | _ :: _, [] => isFalse (by grind)
  | a :: as, b :: bs =>
    match Val.decEq a b, Val.decEqList as bs with
    | isTrue h, isTrue h' => isTrue (by rw [h, h'])
    | isFalse h, _ => isFalse (by grind)
    | _, isFalse h' => isFalse (by grind)
end

instance : DecidableEq Val := Val.decEq

/-- Primitive operations on scalars (extension). The comparisons return the atoms
    `True` or `False`. -/
inductive PrimOp where
  | lt | le | gt | ge | eq | ne
  deriving DecidableEq, Repr, Inhabited, Lean.ToExpr

mutual
/-- Expressions of the FIP / FBIP calculus. -/
inductive Expr where
  /-- the unboxed tuple `(v1, ..., vn)`; a value `v` is the singleton tuple `(v)` -/
  | ret (vs : List Val)
  /-- application `e1 e2` of a function passed as a (borrowed) argument -/
  | app (e1 e2 : Expr)
  /-- the call `f(e1; e2)`, with `e1` the borrowed and `e2` the owned arguments -/
  | call (f : FName) (e1 e2 : Expr)
  /-- `let x̄ = e1 in e2`, binding all components of the unboxed tuple `e1` -/
  | letIn (xs : List Binder) (e1 e2 : Expr)
  /-- the (borrowing) `match e { p ↦ e }` -/
  | bmatch (e : Expr) (bs : List Branch)
  /-- the destructive `match! e { p ↦ e }` -/
  | dmatch (e : Expr) (bs : List Branch)
  /-- `drop x; e` (FBIP, Fig. 6) -/
  | drop (x : Val) (e : Expr)
  /-- `free k; e` (FBIP, Fig. 6) -/
  | free (k : Nat) (e : Expr)
  /-- a primitive operation on scalars (extension) -/
  | prim (op : PrimOp) (args : List Val)
  deriving Repr, Inhabited, Lean.ToExpr

/-- A branch `C^k x1 ... xk ↦ e` of a match. -/
inductive Branch where
  | mk (c : CName) (xs : List Binder) (body : Expr)
  deriving Repr, Inhabited, Lean.ToExpr
end

namespace Expr
/-- A value used as an expression: the singleton unboxed tuple `(v)`. -/
@[match_pattern] abbrev val (v : Val) : Expr := .ret [v]
/-- A variable used as an expression. -/
@[match_pattern] abbrev var (x : Var) : Expr := .ret [.var x]
end Expr

namespace Branch
def ctor : Branch → CName | mk c _ _ => c
def binders : Branch → List Binder | mk _ xs _ => xs
def body : Branch → Expr | mk _ _ e => e
end Branch

/-- Allocation annotations of a top-level function: `fip`, `fip(n)`, `fbip`, `fbip(n)`,
    or none (a plain Koka `fun`). -/
inductive Annot where
  | plain
  | fip (n : Nat)
  | fbip (n : Nat)
  deriving DecidableEq, Repr, Inhabited, Lean.ToExpr

/-- The allocation budget `n` of a function annotated `fip(n)` or `fbip(n)`. -/
def Annot.budget : Annot → Nat
  | .plain => 0
  | .fip n => n
  | .fbip n => n

/-- A top-level function `f(ȳ; x̄) = e` with borrowed parameters `ȳ` and owned
    parameters `x̄`. -/
structure FunDef where
  name : FName
  borrowed : List Binder
  owned : List Binder
  body : Expr
  annot : Annot := .plain
  deriving Repr, Inhabited, Lean.ToExpr

/-- A signature `Σ`: the (mutually recursive) top-level functions. -/
abbrev Sig := List FunDef

/-- Look up a function in the signature. -/
def Sig.lookup (sig : Sig) (f : FName) : Option FunDef := sig.find? (·.name == f)

end FIP
