module

public import RequestProject.Named.Sec2_Calculus.Syntax

@[expose] public section

/-!
# The KokaNamed surface language

The abstract syntax of the fragment of KokaNamed used in the paper's examples: type
declarations (with their field types), function declarations annotated `fip`,
`fip(n)`, `fbip`, `fbip(n)` or nothing, and expressions with nested patterns, guards,
`if`/`elif`/`else`, `val` bindings, tuples and method-call syntax.

`KokaNamed.Ty` is the tree of KokaNamed types: like the rest of the language it holds no names
tables and no proofs; a type is built out of its parts.
-/

namespace KokaNamed

/-- A KokaNamed type: a type constructor applied to arguments (`list<a>`, `int32`, `a`),
    a function type `(a, b) -> c`, or an (unboxed) tuple `(a, b)`. -/
inductive Ty where
  | con (name : String) (args : List Ty)
  | fn (args : List Ty) (res : Ty)
  | tuple (ts : List Ty)
  deriving Repr, Inhabited, BEq, Lean.ToExpr

/-- A constructor declaration `C(f₁ : τ₁, ..., fₖ : τₖ)`. -/
structure CtorDecl where
  name : String
  fields : List (String × Ty)
  deriving Repr, Inhabited, Lean.ToExpr

/-- The kind of a type declaration: `type`, `ref type` or `value type`. -/
inductive TypeKind where
  | normal | ref | value
  deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr

/-- A type declaration `type T<a, ...> { C₁(...); ...; Cₙ(...) }`. -/
structure TypeDecl where
  name : String
  params : List String
  ctors : List CtorDecl
  kind : TypeKind := .normal
  deriving Repr, Inhabited, Lean.ToExpr

/-- Patterns: variables, wildcards, constructor patterns (with possibly fewer
    sub-patterns than fields, the rest being wildcards) and tuple patterns. -/
inductive Pat where
  | var (x : String)
  | wild
  | ctor (c : String) (args : List Pat)
  | tuple (ps : List Pat)
  deriving Repr, Inhabited

/-- Binary operators. -/
inductive BinOp where
  | lt | le | gt | ge | eq | ne | and | or
  deriving Repr, Inhabited, BEq

mutual
/-- KokaNamed expressions. -/
inductive Expr where
  | var (x : String)
  | lit (n : Int)
  /-- application `f(e₁, ..., eₙ)` of a function, a constructor or a parameter -/
  | app (f : String) (args : List Expr)
  | tuple (es : List Expr)
  | binop (op : BinOp) (a b : Expr)
  | ite (c t e : Expr)
  /-- `match e { clauses }`; `destr` records an explicit `match!` -/
  | «match» (destr : Bool) (scrut : Expr) (clauses : List Clause)
  /-- `val p = e₁; e₂` -/
  | valIn (p : Pat) (e1 e2 : Expr)
  deriving Repr, Inhabited
/-- A clause `p | guard -> body` of a match. -/
inductive Clause where
  | mk (p : Pat) (guard : Option Expr) (body : Expr)
  deriving Repr, Inhabited
end

/-- A function parameter `[^]x [: τ]`. -/
structure Param where
  name : String
  borrowed : Bool := false
  ty : Option Ty := none
  deriving Repr, Inhabited

/-- A function declaration. -/
structure FunDecl where
  annot : FIPNamed.Annot
  name : String
  params : List Param
  ret : Option Ty
  body : Expr
  deriving Repr, Inhabited

/-- A top-level declaration. -/
inductive Decl where
  | type (d : TypeDecl)
  | alias (name : String) (ty : Ty)
  | fn (d : FunDecl)
  deriving Repr, Inhabited

/-- A KokaNamed program: a list of declarations. -/
abbrev Program := List Decl

end KokaNamed
