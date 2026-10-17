module

public import RequestProject.Named.Sec2_Calculus.Semantics

@[expose] public section

/-!
# Well-scoped de Bruijn syntax: `Term n` (Fig. 2, Fig. 6, nameless)

This file gives a second, *intrinsically scoped* representation of the grammar of
`RequestProject/Sec2_Calculus/Syntax.lean`.  Bound variables are de Bruijn indices of
type `Fin n`, and the number `n` of variables in scope is an index of the type:

* `TVal n` — a value whose variables are among `0, …, n-1`;
* `Term n` — an expression with at most `n` free (bound-variable) indices;
* `Term 0` — a **closed** expression: it mentions no program variable at all.  It may
  still mention store locations (`TVal.loc`), which are not bound by any binder.

A binder no longer carries a name: `let x̄ = e₁ in e₂` becomes `Term.letIn sc t₁ t₂` with
`sc : List Bool` the scalar flags of the binders (see `Binder.scalar`) and
`t₂ : Term (n + sc.length)`.  A branch `C x̄ ↦ e` of a match is
`TBranches.cons C sc body rest` with `body : Term (n + sc.length)`.  A top-level function
`f(ȳ; x̄) = e` has a body `Term (x̄.length + ȳ.length)`: its only free variables are its
parameters.

## Index convention

Under `k` new binders the scope `n` becomes `n + k`, and

* the index `j < k` is the `j`-th of the new binders (in the order they are written);
* the index `k + i` is the variable `i` of the enclosing scope.

For a function body the borrowed parameters `ȳ` are the inner binders and the owned
parameters `x̄` the outer ones, so the index `j < |ȳ|` is `yⱼ` and `|ȳ| + i` is `xᵢ`.

## From names to indices

`Expr.toTerm Γ e` resolves the names of `e` in a *scope* `Γ : Scope n` (a partial map from
names to indices) and fails exactly when `e` has a free name that `Γ` does not bind
(`Expr.toTerm_isSome_iff` in `RequestProject/Sec2_Calculus/DeBruijn/Closed.lean`).  With
the empty scope it turns a closed named expression into a `Term 0`.  Shadowing is resolved
as by the named substitution `Expr.subst`: a name refers to its innermost binder.
-/

namespace FIPNamed

/-! ## Values and terms -/

/-- Values `v ::= x | C^k v1 ... vk | f` (plus locations and scalar literals) whose
    variables are de Bruijn indices among `0, …, n-1`. -/
inductive TVal (n : Nat) where
  /-- a bound variable, as a de Bruijn index -/
  | bvar (i : Fin n)
  /-- a location of the store semantics (never bound) -/
  | loc (l : Nat)
  /-- a top-level function used as a value -/
  | fn (f : FName)
  /-- a constructor applied to values -/
  | ctor (c : CName) (args : List (TVal n))
  /-- a scalar literal (extension) -/
  | lit (k : Int)
  deriving Repr, Inhabited

mutual
/-- Expressions of the FIPNamed / FBIP calculus with at most `n` free de Bruijn indices.
    `Term 0` is the type of closed expressions. -/
inductive Term : Nat → Type where
  /-- the unboxed tuple `(v1, ..., vn)` -/
  | ret {n : Nat} (vs : List (TVal n)) : Term n
  /-- application `e1 e2` of a function passed as an argument -/
  | app {n : Nat} (e1 e2 : Term n) : Term n
  /-- the call `f(e1; e2)` -/
  | call {n : Nat} (f : FName) (e1 e2 : Term n) : Term n
  /-- `let x̄ = e1 in e2`: the binders are nameless, `sc` records their scalar flags and
      `e2` lives in the scope extended by `sc.length` variables -/
  | letIn {n : Nat} (sc : List Bool) (e1 : Term n) (e2 : Term (n + sc.length)) : Term n
  /-- the borrowing `match e { p ↦ e }` -/
  | bmatch {n : Nat} (e : Term n) (bs : TBranches n) : Term n
  /-- the destructive `match! e { p ↦ e }` -/
  | dmatch {n : Nat} (e : Term n) (bs : TBranches n) : Term n
  /-- `drop x; e` -/
  | drop {n : Nat} (x : TVal n) (e : Term n) : Term n
  /-- `free k; e` -/
  | free {n : Nat} (k : Nat) (e : Term n) : Term n
  /-- a primitive operation on scalars (extension) -/
  | prim {n : Nat} (op : PrimOp) (args : List (TVal n)) : Term n
/-- The branches of a match.  (A list of branches is its own inductive type because the
    scope of a body, `n + sc.length`, differs from branch to branch.) -/
inductive TBranches : Nat → Type where
  | nil {n : Nat} : TBranches n
  /-- the branch `C x̄ ↦ body`, followed by the other branches -/
  | cons {n : Nat} (c : CName) (sc : List Bool) (body : Term (n + sc.length))
      (rest : TBranches n) : TBranches n
end

instance {n : Nat} : Inhabited (Term n) := ⟨.ret []⟩

/-- A top-level function `f(ȳ; x̄) = e`: `borrowed` and `owned` are the scalar flags of
    `ȳ` and `x̄`, and the body may mention the parameters only. -/
structure TFunDef where
  name : FName
  borrowed : List Bool
  owned : List Bool
  body : Term (owned.length + borrowed.length)
  annot : Annot := .plain

/-- A signature of well-scoped functions. -/
abbrev TSig := List TFunDef

/-- Look up a function in a signature. -/
def TSig.lookup (sig : TSig) (f : FName) : Option TFunDef := sig.find? (·.name == f)

/-! ## Substitution

A substitution `σ : Fin n → TVal m` maps every variable of scope `n` to a value of scope
`m`.  Values contain no binders, so a renaming is the substitution `TVal.bvar ∘ ρ`. -/

mutual
/-- Apply a substitution to a value. -/
def TVal.subst {n m : Nat} (σ : Fin n → TVal m) : TVal n → TVal m
  | .bvar i => σ i
  | .loc l => .loc l
  | .fn f => .fn f
  | .ctor c vs => .ctor c (TVal.substList σ vs)
  | .lit k => .lit k
/-- Apply a substitution to a list of values. -/
def TVal.substList {n m : Nat} (σ : Fin n → TVal m) : List (TVal n) → List (TVal m)
  | [] => []
  | v :: vs => TVal.subst σ v :: TVal.substList σ vs
end

@[simp] theorem TVal.substList_eq_map {n m : Nat} (σ : Fin n → TVal m) (vs : List (TVal n)) :
    TVal.substList σ vs = vs.map (TVal.subst σ) := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp [TVal.substList, ih]

/-- Weakening: a value of scope `m` seen in the scope `m + k`, where the `k` new variables
    are the innermost ones (indices `< k`). -/
def TVal.shift {m : Nat} (k : Nat) (v : TVal m) : TVal (m + k) :=
  v.subst fun i => .bvar ⟨k + i, by omega⟩

/-- Push a substitution under `k` binders: the new variables are left alone, and the
    values substituted for the old ones are weakened. -/
def Subst.up {n m : Nat} (k : Nat) (σ : Fin n → TVal m) : Fin (n + k) → TVal (m + k) :=
  fun i => if h : i.val < k then .bvar ⟨i, by omega⟩ else (σ ⟨i - k, by omega⟩).shift k

mutual
/-- Apply a substitution to a term. -/
def Term.subst {n m : Nat} (σ : Fin n → TVal m) : Term n → Term m
  | .ret vs => .ret (TVal.substList σ vs)
  | .app e1 e2 => .app (Term.subst σ e1) (Term.subst σ e2)
  | .call f e1 e2 => .call f (Term.subst σ e1) (Term.subst σ e2)
  | .letIn sc e1 e2 => .letIn sc (Term.subst σ e1) (Term.subst (Subst.up sc.length σ) e2)
  | .bmatch e bs => .bmatch (Term.subst σ e) (TBranches.subst σ bs)
  | .dmatch e bs => .dmatch (Term.subst σ e) (TBranches.subst σ bs)
  | .drop x e => .drop (TVal.subst σ x) (Term.subst σ e)
  | .free k e => .free k (Term.subst σ e)
  | .prim op vs => .prim op (TVal.substList σ vs)
/-- Apply a substitution to the branches of a match. -/
def TBranches.subst {n m : Nat} (σ : Fin n → TVal m) : TBranches n → TBranches m
  | .nil => .nil
  | .cons c sc e bs =>
      .cons c sc (Term.subst (Subst.up sc.length σ) e) (TBranches.subst σ bs)
end

/-- The substitution `[x̄ := v̄]` for the `k = |v̄|` innermost variables of the scope
    `n + k`, the other variables being sent to `σ`. -/
def Subst.inst {n m k : Nat} (vs : List (TVal m)) (h : vs.length = k) (σ : Fin n → TVal m) :
    Fin (n + k) → TVal m :=
  fun i => if hi : i.val < k then vs[i.val]'(by omega) else σ ⟨i - k, by omega⟩

/-- The substitution of the arguments for the parameters of a function body:
    `ȳ := v̄₁` (the inner, borrowed parameters) and `x̄ := v̄₂` (the owned ones). -/
def Subst.args {m kb ko : Nat} (vs1 vs2 : List (TVal m)) (h1 : vs1.length = kb)
    (h2 : vs2.length = ko) : Fin (ko + kb) → TVal m :=
  Subst.inst vs1 h1 fun i => vs2[i.val]'(by omega)

/-! ## From named to nameless syntax -/

/-- A *scope* of `n` variables: which de Bruijn index (if any) a name refers to. -/
abbrev Scope (n : Nat) := String → Option (Fin n)

/-- The empty scope: no name is bound. -/
def Scope.empty : Scope 0 := fun _ => none

/-- The scalar flags of a list of binders: all that remains of the binders in a `Term`. -/
abbrev Binder.flags (xs : List Binder) : List Bool := xs.map (·.scalar)

/-- Extend a scope by the binders `xs`: the `j`-th binder becomes the index `j`, a name
    bound by `Γ` to `i` becomes `|xs| + i`, and an earlier binder shadows a later one
    with the same name (as in `zipSubst`). -/
def Scope.extend {n : Nat} : (xs : List Binder) → Scope n → Scope (n + (Binder.flags xs).length)
  | [], Γ => Γ
  | x :: xs, Γ => fun s =>
      if x.name = s then some ⟨0, by simp⟩ else (Scope.extend xs Γ s).map Fin.succ

/-- The scope of a list of binders alone. -/
def Scope.ofBinders (xs : List Binder) : Scope (Binder.flags xs).length :=
  fun s => (Scope.extend xs Scope.empty s).map (Fin.cast (by simp))

mutual
/-- Resolve the names of a value in a scope; `none` if a free name is not in scope. -/
def Val.toTVal {n : Nat} (Γ : Scope n) : Val → Option (TVal n)
  | .var (.name s) => (Γ s).map .bvar
  | .var (.loc l) => some (.loc l)
  | .fn f => some (.fn f)
  | .ctor c vs => (Val.toTVals Γ vs).map (.ctor c)
  | .lit k => some (.lit k)
/-- Resolve the names of a list of values. -/
def Val.toTVals {n : Nat} (Γ : Scope n) : List Val → Option (List (TVal n))
  | [] => some []
  | v :: vs => do
      let t ← Val.toTVal Γ v
      let ts ← Val.toTVals Γ vs
      pure (t :: ts)
end

mutual
/-- Resolve the names of an expression in a scope, producing a well-scoped de Bruijn
    term; `none` if the expression has a free name that is not in scope.  With
    `Scope.empty` this maps closed expressions to `Term 0`. -/
def Expr.toTerm {n : Nat} (Γ : Scope n) : Expr → Option (Term n)
  | .ret vs => (Val.toTVals Γ vs).map .ret
  | .app e1 e2 => do pure (.app (← Expr.toTerm Γ e1) (← Expr.toTerm Γ e2))
  | .call f e1 e2 => do pure (.call f (← Expr.toTerm Γ e1) (← Expr.toTerm Γ e2))
  | .letIn xs e1 e2 => do
      pure (.letIn (Binder.flags xs) (← Expr.toTerm Γ e1) (← Expr.toTerm (Γ.extend xs) e2))
  | .bmatch e bs => do pure (.bmatch (← Expr.toTerm Γ e) (← Expr.toBranches Γ bs))
  | .dmatch e bs => do pure (.dmatch (← Expr.toTerm Γ e) (← Expr.toBranches Γ bs))
  | .drop x e => do pure (.drop (← Val.toTVal Γ x) (← Expr.toTerm Γ e))
  | .free k e => (Expr.toTerm Γ e).map (.free k)
  | .prim op vs => (Val.toTVals Γ vs).map (.prim op)
/-- Resolve the names of the branches of a match. -/
def Expr.toBranches {n : Nat} (Γ : Scope n) : List Branch → Option (TBranches n)
  | [] => some .nil
  | .mk c xs e :: bs => do
      pure (.cons c (Binder.flags xs) (← Expr.toTerm (Γ.extend xs) e) (← Expr.toBranches Γ bs))
end

/-- A closed expression as a closed term (`none` if the expression has a free name). -/
def Expr.toClosed (e : Expr) : Option (Term 0) := e.toTerm Scope.empty

/-- A function definition as a well-scoped one: its body may only mention its
    parameters. -/
def FunDef.toTFunDef (fd : FunDef) : Option TFunDef :=
  (fd.body.toTerm ((Scope.ofBinders fd.owned).extend fd.borrowed)).map fun b =>
    { name := fd.name, borrowed := Binder.flags fd.borrowed, owned := Binder.flags fd.owned,
      body := b, annot := fd.annot }

/-- A signature as a well-scoped one (`none` if some body mentions a name that is not a
    parameter). -/
def Sig.toTSig (sig : Sig) : Option TSig := sig.mapM FunDef.toTFunDef

end FIPNamed
