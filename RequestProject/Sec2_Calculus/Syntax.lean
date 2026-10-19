module

public import Mathlib

@[expose] public section

/- ══════════════════ PAPER sec. 2 START: A Language for Fully In-Place Update: the grammar (PDF pp. 7-8, Fig. 2; Fig. 6 on p. 13) ══════════════════
   Values, expressions, branches, function annotations (`fip`, `fbip`, `fip(n)`) and
   signatures `Sigma`, with well-scoped de Bruijn indices (`Expr 0` = closed expressions). -/

/-!
# The syntax of the FIP calculus (Fig. 2, Fig. 6 of the paper), with de Bruijn indices

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

## Well-scoped de Bruijn representation

Bound variables are **de Bruijn indices** of type `Fin n`, and the number `n` of variables
in scope is an index of every syntactic category:

* `Var n`, `Val n` — a variable / value whose bound variables are among `0, …, n-1`;
* `Expr n` — an expression with at most `n` free variables;
* **`Expr 0` is the type of closed expressions.**  A closed expression may still mention
  store *locations* (`Var.loc l`), which are allocated by the store semantics (Fig. 5) and
  are never bound by a binder.

Binders carry no names.  A binder only records whether it binds an unboxed scalar
(see below), so `let x̄ = e₁ in e₂` is `Expr.letIn xs e₁ e₂` with `xs : List Bool` and
`e₂ : Expr (n + xs.length)`, and a branch `C x̄ ↦ e` has a body of scope `n + xs.length`.
A top-level function `f(ȳ; x̄) = e` has a body `Expr (x̄.length + ȳ.length)`: its only free
variables are its parameters.

**Index convention.**  Under `k` new binders the scope `n` becomes `n + k`; the index
`j < k` is the `j`-th new binder (in the order written) and `k + i` is the variable `i`
of the enclosing scope.  In a function body the borrowed parameters `ȳ` are the inner
binders: index `j < |ȳ|` is `yⱼ` and `|ȳ| + i` is `xᵢ`.

Because a de Bruijn binder is always fresh, the paper's implicit convention that bound
variables are distinct (Barendregt's convention) holds by construction.

## Other representation choices

* **Unboxed tuples.** `Expr.ret vs` is the unboxed tuple `(v1, ..., vn)`; a value `v`
  used as an expression is the singleton tuple `(v)`, written `Expr.val v`.
* **Top-level functions as values.** `Val.fn f` is a top-level function `f ∈ dom(Σ)`
  passed as a (borrowed) argument; `(f) v̄` is `Expr.app (Expr.val (Val.fn f)) e`.
* **Branches.** The branches of a match form their own inductive type `Branches n`
  (a list whose entries live in different scopes); `Branches.toList` views it as a list
  of `Branch n`.

## Extension: unboxed scalars

The examples of Appendix A use Koka *value types* (`int32`, `bool`, enumerations such
as `color`), whose values need no heap cell and may be freely duplicated and discarded
by the Koka implementation.  To express these examples we add, **beyond the paper's
Fig. 2**,

* scalar literals `Val.lit n`,
* primitive operations on scalars `Expr.prim op v̄` (comparisons returning the atoms
  `True`/`False`),
* a flag on binders: a binder whose type is a value type binds a *scalar* variable
  (flag `true`), which the FIP rules treat as unrestricted (see
  `RequestProject/Sec2_Calculus/Rules.lean`).

The paper's calculus is exactly the fragment without literals, primitives and scalar
binders.
-/

namespace FIP

/-- Names of top-level functions. -/
abbrev FName := String
/-- Names of constructors. -/
abbrev CName := String

/-- A variable of scope `n`: a bound variable (de Bruijn index), or a location of the
    store semantics (locations are never bound). -/
inductive Var (n : Nat) where
  | bvar (i : Fin n)
  | loc (l : Nat)
  deriving DecidableEq, Repr, Hashable

/-- Values `v ::= x | C^k v1 ... vk | f` (and scalar literals, an extension). -/
inductive Val (n : Nat) where
  /-- a variable `x` -/
  | var (x : Var n)
  /-- a top-level function `f ∈ dom(Σ)` used as a value -/
  | fn (f : FName)
  /-- a constructor of arity `k = args.length`; an *atom* when `k = 0` -/
  | ctor (c : CName) (args : List (Val n))
  /-- an unboxed scalar literal (extension, e.g. an `int32`) -/
  | lit (k : Int)
  deriving Repr

instance {n : Nat} : Inhabited (Val n) := ⟨.lit 0⟩

mutual
/-- Decidable equality of values. -/
def Val.decEq {n : Nat} : (a b : Val n) → Decidable (a = b)
  | .var x, .var y => if h : x = y then isTrue (by rw [h]) else isFalse (by grind)
  | .fn f, .fn g => if h : f = g then isTrue (by rw [h]) else isFalse (by grind)
  | .lit a, .lit b => if h : a = b then isTrue (by rw [h]) else isFalse (by grind)
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
def Val.decEqList {n : Nat} : (a b : List (Val n)) → Decidable (a = b)
  | [], [] => isTrue rfl
  | [], _ :: _ | _ :: _, [] => isFalse (by grind)
  | a :: as, b :: bs =>
    match Val.decEq a b, Val.decEqList as bs with
    | isTrue h, isTrue h' => isTrue (by rw [h, h'])
    | isFalse h, _ => isFalse (by grind)
    | _, isFalse h' => isFalse (by grind)
end

instance {n : Nat} : DecidableEq (Val n) := Val.decEq

/-- Primitive operations on scalars (extension). The comparisons return the atoms
    `True` or `False`. -/
inductive PrimOp where
  | lt | le | gt | ge | eq | ne
  deriving DecidableEq, Repr, Inhabited, Lean.ToExpr

mutual
/-- Expressions of the FIP / FBIP calculus with at most `n` free variables.
    `Expr 0` is the type of closed expressions. -/
inductive Expr : Nat → Type where
  /-- the unboxed tuple `(v1, ..., vn)`; a value `v` is the singleton tuple `(v)` -/
  | ret {n : Nat} (vs : List (Val n)) : Expr n
  /-- application `e1 e2` of a function passed as a (borrowed) argument -/
  | app {n : Nat} (e1 e2 : Expr n) : Expr n
  /-- the call `f(e1; e2)`, with `e1` the borrowed and `e2` the owned arguments -/
  | call {n : Nat} (f : FName) (e1 e2 : Expr n) : Expr n
  /-- `let x̄ = e1 in e2`, binding all components of the unboxed tuple `e1`; the binders
      are nameless, `xs` records which of them bind scalars, and `e2` lives in the scope
      extended by `xs.length` variables -/
  | letIn {n : Nat} (xs : List Bool) (e1 : Expr n) (e2 : Expr (n + xs.length)) : Expr n
  /-- the (borrowing) `match e { p ↦ e }` -/
  | bmatch {n : Nat} (e : Expr n) (bs : Branches n) : Expr n
  /-- the destructive `match! e { p ↦ e }` -/
  | dmatch {n : Nat} (e : Expr n) (bs : Branches n) : Expr n
  /-- `drop x; e` (FBIP, Fig. 6) -/
  | drop {n : Nat} (x : Val n) (e : Expr n) : Expr n
  /-- `free k; e` (FBIP, Fig. 6) -/
  | free {n : Nat} (k : Nat) (e : Expr n) : Expr n
  /-- a primitive operation on scalars (extension) -/
  | prim {n : Nat} (op : PrimOp) (args : List (Val n)) : Expr n
/-- The branches of a match: a list of branches `C x̄ ↦ e`, where the body of each branch
    lives in the scope extended by its pattern variables. -/
inductive Branches : Nat → Type where
  | nil {n : Nat} : Branches n
  /-- the branch `C x̄ ↦ body`, followed by the other branches -/
  | cons {n : Nat} (c : CName) (xs : List Bool) (body : Expr (n + xs.length))
      (rest : Branches n) : Branches n
end

instance {n : Nat} : Inhabited (Expr n) := ⟨.ret []⟩

namespace Expr
/-- A value used as an expression: the singleton unboxed tuple `(v)`. -/
@[match_pattern] abbrev val {n : Nat} (v : Val n) : Expr n := .ret [v]
/-- A variable used as an expression. -/
@[match_pattern] abbrev var {n : Nat} (x : Var n) : Expr n := .ret [.var x]
end Expr

/-- A single branch `C x̄ ↦ e` of a match in scope `n`: the constructor, the scalar flags
    of the pattern variables, and the body. -/
structure Branch (n : Nat) where
  ctor : CName
  binders : List Bool
  body : Expr (n + binders.length)

/-- The branches of a match, as a list. -/
def Branches.toList {n : Nat} : Branches n → List (Branch n)
  | .nil => []
  | .cons c xs e bs => ⟨c, xs, e⟩ :: bs.toList

@[simp] theorem Branches.toList_nil {n : Nat} : (Branches.nil : Branches n).toList = [] := rfl
@[simp] theorem Branches.toList_cons {n : Nat} (c : CName) (xs : List Bool)
    (e : Expr (n + xs.length)) (bs : Branches n) :
    (Branches.cons c xs e bs).toList = ⟨c, xs, e⟩ :: bs.toList := rfl

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
    parameters `x̄` (given by their scalar flags).  The body may mention the parameters
    only: the index `j < |ȳ|` is `yⱼ` and `|ȳ| + i` is `xᵢ`. -/
structure FunDef where
  name : FName
  borrowed : List Bool
  owned : List Bool
  body : Expr (owned.length + borrowed.length)
  annot : Annot := .plain

instance : Inhabited FunDef := ⟨{ name := "", borrowed := [], owned := [], body := .ret [] }⟩

/-- A signature `Σ`: the (mutually recursive) top-level functions. -/
abbrev Sig := List FunDef

/-- Look up a function in the signature. -/
def Sig.lookup (sig : Sig) (f : FName) : Option FunDef := sig.find? (·.name == f)

/-- The names of the functions of a signature, in order. -/
abbrev Sig.names (sig : Sig) : List FName := sig.map (·.name)

theorem Sig.lookup_mem {sig : Sig} {g : FName} {fd : FunDef} (h : sig.lookup g = some fd) :
    fd ∈ sig ∧ fd.name = g := by
  unfold Sig.lookup at h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

theorem Sig.lookup_of_mem {sig : Sig} (hn : sig.names.Nodup) {fd : FunDef} (h : fd ∈ sig) :
    sig.lookup fd.name = some fd := by
  induction sig with
  | nil => simp at h
  | cons fd' sig ih =>
    simp only [Sig.names, List.map_cons, List.nodup_cons] at hn
    unfold Sig.lookup at ih ⊢
    rw [List.find?_cons]
    by_cases heq : fd'.name = fd.name
    · simp only [heq, beq_self_eq_true]
      rcases List.mem_cons.mp h with rfl | h
      · rfl
      · exact absurd (heq ▸ List.mem_map_of_mem h) hn.1
    · have : (fd'.name == fd.name) = false := by simpa using heq
      simp only [this]
      rcases List.mem_cons.mp h with rfl | h
      · exact absurd rfl heq
      · exact ih hn.2 h

theorem Sig.lookup_isSome_of_mem_names {sig : Sig} {f : FName} (h : f ∈ sig.names) :
    (sig.lookup f).isSome := by
  obtain ⟨fd, hfd, rfl⟩ := List.mem_map.mp h
  exact List.find?_isSome.mpr ⟨fd, hfd, by simp⟩

end FIP

/- ══════════════════ PAPER sec. 2 END: A Language for Fully In-Place Update: the grammar ══════════════════ -/
