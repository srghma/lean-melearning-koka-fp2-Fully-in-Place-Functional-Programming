module

public import RequestProject.Frontend.Ast

@[expose] public section

/-!
# The compiler's intermediate representation, and scope resolution

The Koka compiler (`RequestProject/Frontend/Compile.lean`) works on source names: it
invents fresh names for intermediate results, splits variables by the names they mention,
and so on.  It therefore first produces terms of a small *intermediate representation*
`Koka.IR.Expr`, which has the shape of the FIP grammar but refers to variables by name.
This representation is internal to the front end and nothing is proved about it.

The last pass of the compiler, `IR.Expr.resolve`, resolves every name to a de Bruijn
index and produces a well-scoped term `FIP.Expr n` of the calculus
(`RequestProject/Sec2_Calculus/Syntax.lean`); it fails if a name is not in scope.  A
function body is resolved in the scope of the function's parameters, so a compiled
function is an `FIP.FunDef` whose body mentions its parameters only.
-/

namespace Koka.IR

/-- A binder of the intermediate representation: a name and its scalar flag. -/
structure Binder where
  name : String
  scalar : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- Values of the intermediate representation. -/
inductive Val where
  | var (x : String)
  | fn (f : FIP.FName)
  | ctor (c : FIP.CName) (args : List Val)
  | lit (n : Int)
  deriving Repr, Inhabited, BEq

mutual
/-- Expressions of the intermediate representation (the FIP grammar, with names). -/
inductive Expr where
  | ret (vs : List Val)
  | app (e1 e2 : Expr)
  | call (f : FIP.FName) (e1 e2 : Expr)
  | letIn (xs : List Binder) (e1 e2 : Expr)
  | bmatch (e : Expr) (bs : List Branch)
  | dmatch (e : Expr) (bs : List Branch)
  | drop (x : Val) (e : Expr)
  | free (k : Nat) (e : Expr)
  | prim (op : FIP.PrimOp) (args : List Val)
  deriving Repr, Inhabited
/-- A branch `C x̄ ↦ e`. -/
inductive Branch where
  | mk (c : FIP.CName) (xs : List Binder) (body : Expr)
  deriving Repr, Inhabited
end

/-- A variable used as an expression. -/
abbrev Expr.var (x : String) : Expr := .ret [.var x]

mutual
/-- The names a value mentions. -/
def Val.fv : Val → List String
  | .var x => [x]
  | .fn _ => []
  | .ctor _ vs => Val.fvList vs
  | .lit _ => []
/-- The names a list of values mentions. -/
def Val.fvList : List Val → List String
  | [] => []
  | v :: vs => Val.fv v ++ Val.fvList vs
end

mutual
/-- The free names of an expression. -/
def Expr.fv : Expr → List String
  | .ret vs => Val.fvList vs
  | .app e1 e2 => Expr.fv e1 ++ Expr.fv e2
  | .call _ e1 e2 => Expr.fv e1 ++ Expr.fv e2
  | .letIn xs e1 e2 => Expr.fv e1 ++ (Expr.fv e2).filter (fun v => v ∉ xs.map (·.name))
  | .bmatch e bs => Expr.fv e ++ Expr.fvBranches bs
  | .dmatch e bs => Expr.fv e ++ Expr.fvBranches bs
  | .drop x e => Val.fv x ++ Expr.fv e
  | .free _ e => Expr.fv e
  | .prim _ vs => Val.fvList vs
/-- The free names of the branches of a match. -/
def Expr.fvBranches : List Branch → List String
  | [] => []
  | .mk _ xs e :: bs => (Expr.fv e).filter (fun v => v ∉ xs.map (·.name)) ++ Expr.fvBranches bs
end

/-! ## Scope resolution -/

/-- A *scope* of `n` variables: which de Bruijn index (if any) a name refers to. -/
abbrev Scope (n : Nat) := String → Option (Fin n)

/-- The empty scope. -/
def Scope.empty : Scope 0 := fun _ => none

/-- Extend a scope by the binders `xs`: the `j`-th binder becomes the index `j`, a name
    bound in `Γ` to `i` becomes `|xs| + i`, and an earlier binder shadows a later one. -/
def Scope.extend {n : Nat} : (xs : List Binder) → Scope n → Scope (n + xs.length)
  | [], Γ => Γ
  | x :: xs, Γ => fun s =>
      if x.name = s then some ⟨0, by simp⟩
      else (Scope.extend xs Γ s).map Fin.succ

/-- The scalar flags of binders. -/
def Binder.flags (xs : List Binder) : List Bool := xs.map (·.scalar)

@[simp] theorem Binder.length_flags (xs : List Binder) : (Binder.flags xs).length = xs.length := by
  simp [Binder.flags]

/-- Resolve a name. -/
def resolveVar {n : Nat} (Γ : Scope n) (x : String) : Except String (FIP.Var n) :=
  match Γ x with
  | some i => pure (.bvar i)
  | none => throw s!"variable '{x}' is not in scope"

mutual
/-- Resolve the names of a value. -/
def Val.resolve {n : Nat} (Γ : Scope n) : Val → Except String (FIP.Val n)
  | .var x => return .var (← resolveVar Γ x)
  | .fn f => pure (.fn f)
  | .ctor c vs => return .ctor c (← Val.resolveList Γ vs)
  | .lit k => pure (.lit k)
/-- Resolve the names of a list of values. -/
def Val.resolveList {n : Nat} (Γ : Scope n) : List Val → Except String (List (FIP.Val n))
  | [] => pure []
  | v :: vs => return (← Val.resolve Γ v) :: (← Val.resolveList Γ vs)
end

/-- Cast an expression along an equation of scopes. -/
def castE {n m : Nat} (h : n = m) (e : FIP.Expr n) : FIP.Expr m := h ▸ e

mutual
/-- Resolve the names of an expression in a scope, producing a well-scoped term of the
    FIP calculus. -/
def Expr.resolve {n : Nat} (Γ : Scope n) : Expr → Except String (FIP.Expr n)
  | .ret vs => return .ret (← Val.resolveList Γ vs)
  | .app e1 e2 => return .app (← Expr.resolve Γ e1) (← Expr.resolve Γ e2)
  | .call f e1 e2 => return .call f (← Expr.resolve Γ e1) (← Expr.resolve Γ e2)
  | .letIn xs e1 e2 => do
      let b ← Expr.resolve (Γ.extend xs) e2
      return .letIn (Binder.flags xs) (← Expr.resolve Γ e1) (castE (by simp) b)
  | .bmatch e bs => return .bmatch (← Expr.resolve Γ e) (← Expr.resolveBranches Γ bs)
  | .dmatch e bs => return .dmatch (← Expr.resolve Γ e) (← Expr.resolveBranches Γ bs)
  | .drop x e => return .drop (← Val.resolve Γ x) (← Expr.resolve Γ e)
  | .free k e => return .free k (← Expr.resolve Γ e)
  | .prim op vs => return .prim op (← Val.resolveList Γ vs)
/-- Resolve the names of the branches of a match. -/
def Expr.resolveBranches {n : Nat} (Γ : Scope n) : List Branch → Except String (FIP.Branches n)
  | [] => pure .nil
  | .mk c xs e :: bs => do
      let b ← Expr.resolve (Γ.extend xs) e
      return .cons c (Binder.flags xs) (castE (by simp) b) (← Expr.resolveBranches Γ bs)
end

/-- Resolve a function body: the owned parameters `x̄` are bound first, the borrowed
    parameters `ȳ` are the inner binders. -/
def resolveFun (name : FIP.FName) (borrowed owned : List Binder) (body : Expr) (annot : FIP.Annot) :
    Except String FIP.FunDef := do
  let Γ : Scope (owned.length + borrowed.length) :=
    Scope.extend borrowed (fun s => (Scope.extend owned Scope.empty s).map
      (Fin.cast (by simp)))
  let b ← body.resolve Γ
  return { name, borrowed := Binder.flags borrowed, owned := Binder.flags owned,
           body := castE (by simp) b, annot }

end Koka.IR
