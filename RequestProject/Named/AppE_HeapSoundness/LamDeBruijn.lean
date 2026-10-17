module

public import RequestProject.Named.AppE_HeapSoundness.Heap
public import RequestProject.Named.Sec2_Calculus.DeBruijn.Closed

@[expose] public section

/-!
# Well-scoped de Bruijn syntax for `λfip`: `LTerm n` (Fig. 9, nameless)

The `λfip` analogue of `RequestProject/Sec2_Calculus/DeBruijn/Syntax.lean`.  Variables are
de Bruijn indices `Fin n` and the scope `n` is an index of the types:

* `LTVal n`, `LTerm n`, `LTBranches n` — values, expressions and branches with at most `n`
  free indices; `LTerm 0` is the type of closed `λfip` expressions;
* `LTVals n k` — a list of exactly `k` values (the arity of a tuple, of a constructor, or
  the number of captured variables of a lambda is part of its type).

## Lambdas are closure-converted by construction

In `λfip` a lambda `λ^z̄ x̄. e` records the free variables `z̄` of its body
(rule `lam` of Fig. 9 types `e` in `∅ | z̄, x̄`).  Here this is a property of the type:

`LTVal.lam (zs : LTVals n k) (sc : List Bool) (body : LTerm (k + sc.length))`

The captured values `zs` live in the enclosing scope `n`, but the body lives in its own
scope of `k + |x̄|` variables — the index `j < |x̄|` is the parameter `xⱼ`, and `|x̄| + i`
is the captured value `zᵢ`.  The body of a lambda cannot mention any other variable of
the enclosing scope.  The plain substitution `LTVal.subst` never enters it; the
substitution of the semantics, `LTVal.isubst`, reaches it only through the captured
values, exactly as the named substitution of Fig. 9 does (see "Substitution into
closures" below).  β-reduction instantiates the body with the arguments and the captured
values (`LTHead.beta`).

`LExpr.toLTerm Γ e` resolves the names of a named `λfip` expression.  It succeeds exactly
when the free names of `e` are in scope and the body of every lambda only mentions its
parameters and its recorded variables `z̄` (`LExpr.toLTerm_isSome_iff`): in particular a
named lambda whose annotation `z̄` is wrong has no de Bruijn representation.
-/

namespace FIPNamed.Lam

mutual
/-- Values of `λfip` with at most `n` free de Bruijn indices. -/
inductive LTVal : Nat → Type where
  | bvar {n : Nat} (i : Fin n) : LTVal n
  | loc {n : Nat} (l : Nat) : LTVal n
  | fn {n : Nat} (f : FName) : LTVal n
  | ctor {n : Nat} (c : CName) {k : Nat} (args : LTVals n k) : LTVal n
  /-- `λ^z̄ x̄. e`: the captured values `z̄` (in the enclosing scope) and a body whose only
      variables are the parameters `x̄` (indices `< |x̄|`) and the captured values. -/
  | lam {n : Nat} {k : Nat} (zs : LTVals n k) (sc : List Bool) (body : LTerm (k + sc.length)) :
      LTVal n
/-- A list of exactly `k` values. -/
inductive LTVals : Nat → Nat → Type where
  | nil {n : Nat} : LTVals n 0
  | cons {n k : Nat} (v : LTVal n) (vs : LTVals n k) : LTVals n (k + 1)
/-- Expressions of `λfip` with at most `n` free de Bruijn indices. -/
inductive LTerm : Nat → Type where
  | ret {n k : Nat} (vs : LTVals n k) : LTerm n
  | app {n : Nat} (e1 e2 : LTerm n) : LTerm n
  | call {n : Nat} (f : FName) (e1 e2 : LTerm n) : LTerm n
  | letIn {n : Nat} (sc : List Bool) (e1 : LTerm n) (e2 : LTerm (n + sc.length)) : LTerm n
  | «match» {n : Nat} (x : LTVal n) (bs : LTBranches n) : LTerm n
  | dup {n : Nat} (x : LTVal n) (e : LTerm n) : LTerm n
  | drop {n : Nat} (x : LTVal n) (e : LTerm n) : LTerm n
  | dropru {n : Nat} (x : LTVal n) (k : Nat) (e : LTerm n) : LTerm n
  | free {n : Nat} (k : Nat) (e : LTerm n) : LTerm n
  | alloc {n : Nat} (k : Nat) (e : LTerm n) : LTerm n
/-- Branches `C x̄ ↦ e` of a match. -/
inductive LTBranches : Nat → Type where
  | nil {n : Nat} : LTBranches n
  | cons {n : Nat} (c : CName) (sc : List Bool) (body : LTerm (n + sc.length))
      (rest : LTBranches n) : LTBranches n
end

/-- The `i`-th value of a list of `k` values. -/
def LTVals.get {n : Nat} : {k : Nat} → LTVals n k → Fin k → LTVal n
  | _, .cons v _, ⟨0, _⟩ => v
  | _, .cons _ vs, ⟨i + 1, h⟩ => vs.get ⟨i, by omega⟩

/-- A top-level `λfip` function whose body only mentions its parameters. -/
structure LTFunDef where
  name : FName
  borrowed : List Bool
  owned : List Bool
  body : LTerm (owned.length + borrowed.length)

/-- A well-scoped `λfip` signature. -/
abbrev LTSig := List LTFunDef

/-- Look up a function. -/
def LTSig.lookup (sig : LTSig) (f : FName) : Option LTFunDef := sig.find? (·.name == f)

/-! ## Substitution

Substitution acts on the captured values of a lambda and **not** on its body, which has
its own scope. -/

mutual
/-- Apply a substitution to a value. -/
def LTVal.subst {n m : Nat} (σ : Fin n → LTVal m) : LTVal n → LTVal m
  | .bvar i => σ i
  | .loc l => .loc l
  | .fn f => .fn f
  | .ctor c vs => .ctor c (LTVals.subst σ vs)
  | .lam zs sc body => .lam (LTVals.subst σ zs) sc body
/-- Apply a substitution to a list of values. -/
def LTVals.subst {n m : Nat} (σ : Fin n → LTVal m) : {k : Nat} → LTVals n k → LTVals m k
  | _, .nil => .nil
  | _, .cons v vs => .cons (LTVal.subst σ v) (LTVals.subst σ vs)
end

/-- Weakening past `k` new innermost variables. -/
def LTVal.shift {m : Nat} (k : Nat) (v : LTVal m) : LTVal (m + k) :=
  v.subst fun i => .bvar ⟨k + i, by omega⟩

/-- Push a substitution under `k` binders. -/
def LSubst'.up {n m : Nat} (k : Nat) (σ : Fin n → LTVal m) : Fin (n + k) → LTVal (m + k) :=
  fun i => if h : i.val < k then .bvar ⟨i, by omega⟩ else (σ ⟨i - k, by omega⟩).shift k

mutual
/-- Apply a substitution to an expression. -/
def LTerm.subst {n m : Nat} (σ : Fin n → LTVal m) : LTerm n → LTerm m
  | .ret vs => .ret (LTVals.subst σ vs)
  | .app e1 e2 => .app (LTerm.subst σ e1) (LTerm.subst σ e2)
  | .call f e1 e2 => .call f (LTerm.subst σ e1) (LTerm.subst σ e2)
  | .letIn sc e1 e2 => .letIn sc (LTerm.subst σ e1) (LTerm.subst (LSubst'.up sc.length σ) e2)
  | .match x bs => .match (LTVal.subst σ x) (LTBranches.subst σ bs)
  | .dup x e => .dup (LTVal.subst σ x) (LTerm.subst σ e)
  | .drop x e => .drop (LTVal.subst σ x) (LTerm.subst σ e)
  | .dropru x k e => .dropru (LTVal.subst σ x) k (LTerm.subst σ e)
  | .free k e => .free k (LTerm.subst σ e)
  | .alloc k e => .alloc k (LTerm.subst σ e)
/-- Apply a substitution to branches. -/
def LTBranches.subst {n m : Nat} (σ : Fin n → LTVal m) : LTBranches n → LTBranches m
  | .nil => .nil
  | .cons c sc e bs => .cons c sc (LTerm.subst (LSubst'.up sc.length σ) e) (LTBranches.subst σ bs)
end

/-- `[x̄ := v̄]` for the `k` innermost variables of the scope `n + k`, the others being sent
    to `σ`. -/
def LSubst'.inst {n m k k' : Nat} (vs : LTVals m k') (h : k' = k) (σ : Fin n → LTVal m) :
    Fin (n + k) → LTVal m :=
  fun i => if hi : i.val < k then vs.get ⟨i.val, by omega⟩ else σ ⟨i - k, by omega⟩

/-! ## Substitution into closures

The named substitution `LExpr.subst` of Fig. 9 enters the body of a lambda: substituting
`z := v` in `λ^z̄ x̄. e` gives `λ^(z̄[z := v]) x̄. e[z := v]`.  A de Bruijn body cannot mention
the enclosing scope, so the only way a substitution can reach it is through the captured
values: when a captured value is a variable `zᵢ = bvar j` that the substitution sends to a
**closed** value `c`, the body's index for `zᵢ` is instantiated with `c` as well.
`LTerm.isubst` is this *closure-instantiating* substitution, and the functional semantics
`LTHead` below uses it.  It agrees with the plain `LTerm.subst` except at such captured
positions (in particular for renamings, which never produce closed values), and it is what
makes name resolution commute with substitution exactly
(`LExpr.toLTerm_subst` in `RequestProject/AppE_HeapSoundness/LamDeBruijnSubst.lean`). -/

mutual
/-- The closed value `v` denotes, if `v` mentions no index. -/
def LTVal.lower {n : Nat} : LTVal n → Option (LTVal 0)
  | .bvar _ => none
  | .loc l => some (.loc l)
  | .fn f => some (.fn f)
  | .ctor c vs => (LTVals.lower vs).map (.ctor c)
  | .lam zs sc body => (LTVals.lower zs).map fun zs' => .lam zs' sc body
/-- `LTVal.lower` for a list of values. -/
def LTVals.lower {n : Nat} : {k : Nat} → LTVals n k → Option (LTVals 0 k)
  | _, .nil => some .nil
  | _, .cons v vs => do pure (.cons (← LTVal.lower v) (← LTVals.lower vs))
end

/-- A closed value, seen in any scope. -/
def LTVal.weaken {m : Nat} (c : LTVal 0) : LTVal m := c.subst Fin.elim0

/-- The closed value a captured value becomes under `σ`, when it is a variable that `σ`
    sends to a closed value. -/
def LTVal.capOf {n m : Nat} (σ : Fin n → LTVal m) : LTVal n → Option (LTVal 0)
  | .bvar j => (σ j).lower
  | _ => none

/-- How a substitution `σ` acts on the body of `λ^z̄ x̄. e` (scope `|z̄| + p`, `p = |x̄|`):
    parameters are kept, and the index of a captured value is instantiated with the closed
    value `σ` turns it into, if any. -/
def LSubst'.cap {n m k : Nat} (σ : Fin n → LTVal m) (zs : LTVals n k) (p : Nat) :
    Fin (k + p) → LTVal (k + p) :=
  fun i => if h : i.val < p then .bvar i else
    match (zs.get ⟨i.val - p, by omega⟩).capOf σ with
    | some c => c.weaken
    | none => .bvar i

mutual
/-- Closure-instantiating substitution of a value. -/
def LTVal.isubst {n m : Nat} (σ : Fin n → LTVal m) : LTVal n → LTVal m
  | .bvar i => σ i
  | .loc l => .loc l
  | .fn f => .fn f
  | .ctor c vs => .ctor c (LTVals.isubst σ vs)
  | .lam zs sc body =>
      .lam (LTVals.isubst σ zs) sc (LTerm.isubst (LSubst'.cap σ zs sc.length) body)
/-- Closure-instantiating substitution of a list of values. -/
def LTVals.isubst {n m : Nat} (σ : Fin n → LTVal m) : {k : Nat} → LTVals n k → LTVals m k
  | _, .nil => .nil
  | _, .cons v vs => .cons (LTVal.isubst σ v) (LTVals.isubst σ vs)
/-- Closure-instantiating substitution of an expression. -/
def LTerm.isubst {n m : Nat} (σ : Fin n → LTVal m) : LTerm n → LTerm m
  | .ret vs => .ret (LTVals.isubst σ vs)
  | .app e1 e2 => .app (LTerm.isubst σ e1) (LTerm.isubst σ e2)
  | .call f e1 e2 => .call f (LTerm.isubst σ e1) (LTerm.isubst σ e2)
  | .letIn sc e1 e2 =>
      .letIn sc (LTerm.isubst σ e1) (LTerm.isubst (LSubst'.up sc.length σ) e2)
  | .match x bs => .match (LTVal.isubst σ x) (LTBranches.isubst σ bs)
  | .dup x e => .dup (LTVal.isubst σ x) (LTerm.isubst σ e)
  | .drop x e => .drop (LTVal.isubst σ x) (LTerm.isubst σ e)
  | .dropru x k e => .dropru (LTVal.isubst σ x) k (LTerm.isubst σ e)
  | .free k e => .free k (LTerm.isubst σ e)
  | .alloc k e => .alloc k (LTerm.isubst σ e)
/-- Closure-instantiating substitution of branches. -/
def LTBranches.isubst {n m : Nat} (σ : Fin n → LTVal m) : LTBranches n → LTBranches m
  | .nil => .nil
  | .cons c sc e bs =>
      .cons c sc (LTerm.isubst (LSubst'.up sc.length σ) e) (LTBranches.isubst σ bs)
end

/-! ## Functional semantics -/

/-- Evaluation contexts. -/
inductive LTECtx (n : Nat) where
  | hole
  | appL (E : LTECtx n) (e : LTerm n)
  | appR {k : Nat} (vs : LTVals n k) (E : LTECtx n)
  | callB (f : FName) (E : LTECtx n) (e : LTerm n)
  | callO (f : FName) {k : Nat} (vs : LTVals n k) (E : LTECtx n)
  | letIn (sc : List Bool) (E : LTECtx n) (e : LTerm (n + sc.length))

/-- `E[e]`. -/
def LTECtx.plug {n : Nat} : LTECtx n → LTerm n → LTerm n
  | .hole, e => e
  | .appL E e2, e => .app (E.plug e) e2
  | .appR vs E, e => .app (.ret vs) (E.plug e)
  | .callB f E e2, e => .call f (E.plug e) e2
  | .callO f vs E, e => .call f (.ret vs) (E.plug e)
  | .letIn sc E e2, e => .letIn sc (E.plug e) e2

/-- The first branch for constructor `c` with `k` fields. -/
def LTBranches.find {n : Nat} : LTBranches n → CName → Nat →
    Option (Σ sc : List Bool, LTerm (n + sc.length))
  | .nil, _, _ => none
  | .cons c' sc e bs, c, k =>
      if c' = c ∧ sc.length = k then some ⟨sc, e⟩ else LTBranches.find bs c k

/-- A singleton tuple. -/
abbrev LTVals.one {n : Nat} (v : LTVal n) : LTVals n 1 := .cons v .nil

/-- Head reductions of `λfip` on well-scoped terms. -/
inductive LTHead (sig : LTSig) {n : Nat} : LTerm n → LTerm n → Prop where
  | letIn (sc : List Bool) {k : Nat} (vs : LTVals n k) (e : LTerm (n + sc.length))
      (h : k = sc.length) :
      LTHead sig (.letIn sc (.ret vs) e) (e.isubst (LSubst'.inst vs h .bvar))
  | call (f : FName) (fd : LTFunDef) {k1 k2 : Nat} (vs1 : LTVals n k1) (vs2 : LTVals n k2)
      (h1 : k1 = fd.borrowed.length) (h2 : k2 = fd.owned.length) :
      sig.lookup f = some fd →
      LTHead sig (.call f (.ret vs1) (.ret vs2))
        (fd.body.isubst (LSubst'.inst vs1 h1 fun i => vs2.get ⟨i.val, by omega⟩))
  | appFn (f : FName) (fd : LTFunDef) {k : Nat} (vs : LTVals n k)
      (h1 : 0 = fd.borrowed.length) (h2 : k = fd.owned.length) :
      sig.lookup f = some fd →
      LTHead sig (.app (.ret (.one (.fn f))) (.ret vs))
        (fd.body.isubst (LSubst'.inst (LTVals.nil (n := n)) h1 fun i => vs.get ⟨i.val, by omega⟩))
  /-- (*beta*) `(λ^z̄ x̄. e) v̄ ⟶ e[x̄ := v̄, z̄ := z̄]`: the body is instantiated with the
      arguments (inner indices) and the captured values (outer indices). -/
  | beta {kz : Nat} (zs : LTVals n kz) (sc : List Bool) (body : LTerm (kz + sc.length))
      {k : Nat} (vs : LTVals n k) (h : k = sc.length) :
      LTHead sig (.app (.ret (.one (.lam zs sc body))) (.ret vs))
        (body.isubst (LSubst'.inst vs h zs.get))
  | «match» (c : CName) {k : Nat} (vs : LTVals n k) (bs : LTBranches n) (sc : List Bool)
      (e : LTerm (n + sc.length)) (h : k = sc.length) :
      bs.find c k = some ⟨sc, e⟩ →
      LTHead sig (.match (.ctor c vs) bs) (e.isubst (LSubst'.inst vs h .bvar))
  | dup (v : LTVal n) (e : LTerm n) : LTHead sig (.dup v e) e
  | drop (v : LTVal n) (e : LTerm n) : LTHead sig (.drop v e) e
  | dropru (v : LTVal n) (k : Nat) (e : LTerm n) : LTHead sig (.dropru v k e) e
  | free (k : Nat) (e : LTerm n) : LTHead sig (.free k e) e
  | alloc (k : Nat) (e : LTerm n) : LTHead sig (.alloc k e) e

/-- The functional semantics of well-scoped `λfip` terms; closed terms step to closed
    terms by construction. -/
inductive LTStep (sig : LTSig) {n : Nat} : LTerm n → LTerm n → Prop where
  | step (E : LTECtx n) {e e' : LTerm n} : LTHead sig e e' → LTStep sig (E.plug e) (E.plug e')

/-- `⟼*` on well-scoped `λfip` terms. -/
abbrev LTSteps (sig : LTSig) {n : Nat} := Relation.ReflTransGen (LTStep sig (n := n))

/-! ## From names to indices -/

/-- The scope of the recorded variables `z̄` of a lambda: the name of the `i`-th recorded
    variable resolves to `i` (the first occurrence wins). -/
def Scope.ofCaptured : (zs : List LVal) → Scope zs.length
  | [] => fun _ => none
  | z :: zs => fun s =>
      match z with
      | .var (.name s') => if s' = s then some ⟨0, by simp⟩ else (Scope.ofCaptured zs s).map Fin.succ
      | _ => (Scope.ofCaptured zs s).map Fin.succ

mutual
/-- Resolve the names of a value; the body of a lambda is resolved in the scope of its
    parameters and recorded variables. -/
def LVal.toLTVal {n : Nat} (Γ : Scope n) : LVal → Option (LTVal n)
  | .var (.name s) => (Γ s).map .bvar
  | .var (.loc l) => some (.loc l)
  | .fn f => some (.fn f)
  | .ctor c vs => (LVal.toLTVals Γ vs).map (.ctor c)
  | .lam zs xs e => do
      pure (.lam (← LVal.toLTVals Γ zs) (Binder.flags xs)
        (← LExpr.toLTerm ((Scope.ofCaptured zs).extend xs) e))
/-- Resolve the names of a list of values. -/
def LVal.toLTVals {n : Nat} (Γ : Scope n) : (vs : List LVal) → Option (LTVals n vs.length)
  | [] => some .nil
  | v :: vs => do pure (.cons (← LVal.toLTVal Γ v) (← LVal.toLTVals Γ vs))
/-- Resolve the names of an expression. -/
def LExpr.toLTerm {n : Nat} (Γ : Scope n) : LExpr → Option (LTerm n)
  | .ret vs => (LVal.toLTVals Γ vs).map .ret
  | .app e1 e2 => do pure (.app (← LExpr.toLTerm Γ e1) (← LExpr.toLTerm Γ e2))
  | .call f e1 e2 => do pure (.call f (← LExpr.toLTerm Γ e1) (← LExpr.toLTerm Γ e2))
  | .letIn xs e1 e2 => do
      pure (.letIn (Binder.flags xs) (← LExpr.toLTerm Γ e1) (← LExpr.toLTerm (Γ.extend xs) e2))
  | .match x bs => do pure (.match (← LVal.toLTVal Γ x) (← LExpr.toLBranches Γ bs))
  | .dup x e => do pure (.dup (← LVal.toLTVal Γ x) (← LExpr.toLTerm Γ e))
  | .drop x e => do pure (.drop (← LVal.toLTVal Γ x) (← LExpr.toLTerm Γ e))
  | .dropru x k e => do pure (.dropru (← LVal.toLTVal Γ x) k (← LExpr.toLTerm Γ e))
  | .free k e => (LExpr.toLTerm Γ e).map (.free k)
  | .alloc k e => (LExpr.toLTerm Γ e).map (.alloc k)
/-- Resolve the names of branches. -/
def LExpr.toLBranches {n : Nat} (Γ : Scope n) : List LBranch → Option (LTBranches n)
  | [] => some .nil
  | .mk c xs e :: bs => do
      pure (.cons c (Binder.flags xs) (← LExpr.toLTerm (Γ.extend xs) e) (← LExpr.toLBranches Γ bs))
end

/-- A `λfip` function as a well-scoped one. -/
def LFunDef.toLTFunDef (fd : LFunDef) : Option LTFunDef :=
  (fd.body.toLTerm ((Scope.ofBinders fd.owned).extend fd.borrowed)).map fun b =>
    { name := fd.name, borrowed := Binder.flags fd.borrowed, owned := Binder.flags fd.owned,
      body := b }

/-- A `λfip` signature as a well-scoped one. -/
def LSig.toLTSig (sig : LSig) : Option LTSig := sig.mapM LFunDef.toLTFunDef

/-! ## Which named expressions are well scoped -/

/-- The names among the recorded variables `z̄` of a lambda. -/
def capturedNames : List LVal → List String
  | [] => []
  | .var (.name s) :: zs => s :: capturedNames zs
  | _ :: zs => capturedNames zs

mutual
/-- `LVal.Scoped P v`: every free name of `v` satisfies `P`, and the body of every lambda
    in `v` only mentions its parameters and its recorded variables. -/
def LVal.Scoped (P : String → Prop) : LVal → Prop
  | .var (.name s) => P s
  | .var (.loc _) => True
  | .fn _ => True
  | .ctor _ vs => LVal.ScopedList P vs
  | .lam zs xs e =>
      LVal.ScopedList P zs ∧
        LExpr.Scoped (fun s => s ∈ xs.map (·.name) ∨ s ∈ capturedNames zs) e
/-- `LVal.Scoped` for every value of a list. -/
def LVal.ScopedList (P : String → Prop) : List LVal → Prop
  | [] => True
  | v :: vs => LVal.Scoped P v ∧ LVal.ScopedList P vs
/-- `LExpr.Scoped P e`: every free name of `e` satisfies `P` (names bound in `e` being
    excepted), and the body of every lambda only mentions its parameters and its
    recorded variables. -/
def LExpr.Scoped (P : String → Prop) : LExpr → Prop
  | .ret vs => LVal.ScopedList P vs
  | .app e1 e2 => LExpr.Scoped P e1 ∧ LExpr.Scoped P e2
  | .call _ e1 e2 => LExpr.Scoped P e1 ∧ LExpr.Scoped P e2
  | .letIn xs e1 e2 =>
      LExpr.Scoped P e1 ∧ LExpr.Scoped (fun s => s ∈ xs.map (·.name) ∨ P s) e2
  | .match x bs => LVal.Scoped P x ∧ LExpr.ScopedB P bs
  | .dup x e => LVal.Scoped P x ∧ LExpr.Scoped P e
  | .drop x e => LVal.Scoped P x ∧ LExpr.Scoped P e
  | .dropru x _ e => LVal.Scoped P x ∧ LExpr.Scoped P e
  | .free _ e => LExpr.Scoped P e
  | .alloc _ e => LExpr.Scoped P e
/-- `LExpr.Scoped` for branches. -/
def LExpr.ScopedB (P : String → Prop) : List LBranch → Prop
  | [] => True
  | .mk _ xs e :: bs =>
      LExpr.Scoped (fun s => s ∈ xs.map (·.name) ∨ P s) e ∧ LExpr.ScopedB P bs
end

end FIPNamed.Lam
