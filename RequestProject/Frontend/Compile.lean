module

public import RequestProject.Frontend.Parse
public import RequestProject.Frontend.IR

@[expose] public section

/-!
# Compiling Koka to the FIP calculus

This file translates the Koka surface language (`RequestProject/Frontend/Ast.lean`) into the
core FIP calculus (`FIP.Sig`), doing what the paper's implementation does implicitly
("these examples do not use `match!`, `drop` or `free` as they are automatically
inferred by our implementation", Appendix A):

* **A-normal form.** Nested calls and matches in argument position are bound by `let`;
  a variable that is still needed after a `let` is *borrowed* in its bound expression,
  exactly as in rule `let` of Fig. 4.
* **Matches.** Nested patterns, guards and catch-all clauses are compiled by a
  pattern-matching matrix.  A match on an *owned* variable becomes a destructive
  `match!` (yielding a reuse credit), a match on a *borrowed* or *scalar* variable a
  borrowing `match`.  A catch-all clause `x -> e` that uses the scrutinee `x` after it
  was destructed *reconstructs* it from its fields (reusing the credit); a constructor no
  clause covers gets no branch (evaluation is stuck, which models Koka's `exn` effect).
* **Unused owned variables.** In a `fip` function an owned variable that is not used and
  whose type has a single constructor (such as the `unit2` and `reuse3` *reuse
  tokens* of Appendix A) is destructed to provide its reuse credit; in a `fbip`
  function unused owned variables are `drop`ped.
* **Value types.** Enumerations (`color`, `bool`, `pad`), `int`, `int32`, … are *scalars*
  (see the extension described in `RequestProject/Sec2_Calculus/Syntax.lean`); `value type`s such
  as `bseq` and `tuple4`, and tuples, are unboxed: a variable of such a type is
  represented by one core variable per field.
* `if c then e₁ else e₂` is a match on the atoms `True`/`False`; `&&`, `||` are
  desugared; comparisons become primitive operations.

The compiler is an (unverified) front end: every property of the resulting code is
established afterwards, on the core calculus — the FIP check by `FIP.Sig.check_sound`,
the results of evaluation by `FIP.Expr.evalTotal_sound`.
-/

namespace Koka

open IR (Val Binder Branch)

/-! ## Types -/

/-- The unknown type (for untyped parameters and type variables). -/
def unk : Ty := .con "?" []

/-- Built-in types: `list`, `bool` and `maybe`. -/
def builtinTypes : List TypeDecl :=
  [ { name := "list", params := ["a"],
      ctors := [ { name := "Nil", fields := [] },
                 { name := "Cons", fields := [("head", .con "a" []),
                                              ("tail", .con "list" [.con "a" []])] } ] },
    { name := "bool", params := [],
      ctors := [ { name := "False", fields := [] }, { name := "True", fields := [] } ] },
    { name := "maybe", params := ["a"],
      ctors := [ { name := "Nothing", fields := [] },
                 { name := "Just", fields := [("value", .con "a" [])] } ] } ]

/-- Built-in scalar (value) types. -/
def primTypes : List String :=
  ["int", "int8", "int16", "int32", "int64", "char", "float64", "ssize_t"]

/-- Substitute types for type variables. -/
def Ty.subst (σ : List (String × Ty)) : Ty → Ty
  | .con n [] => (σ.lookup n).getD (.con n [])
  | .con n args => .con n (args.map (Ty.subst σ))
  | .fn as r => .fn (as.map (Ty.subst σ)) (Ty.subst σ r)
  | .tuple ts => .tuple (ts.map (Ty.subst σ))

/-! ## Termination

Every function of the compiler is total: there is no `partial` and no fuel.  Most
functions recurse on the structure of their argument.  Unfolding definitions (type
aliases, value types, destructed variables) recurses on a list of definitions from which
the unfolded one is removed (`eraseKey`, `length_eraseKey_lt`), so that a recursive alias
or value type is reported or left folded instead of being unfolded forever.  The
compiler proper is well-founded on the size of the Koka code it compiles (`Expr.size`)
and, for the pattern-matching matrix, on the size of its patterns and columns; where a
measure is only known at run time it is checked (`noProgress`). -/

/-- Remove the entries for the key `k` from an association list. -/
def eraseKey {β : Type} (l : List (String × β)) (k : String) : List (String × β) :=
  l.filter (·.1 != k)

theorem length_eraseKey_lt {β : Type} {l : List (String × β)} {k : String} {v : β}
    (h : l.lookup k = some v) : (eraseKey l k).length < l.length := by
  unfold eraseKey
  induction l with
  | nil => simp at h
  | cons p l ih =>
    obtain ⟨a, b⟩ := p
    have hle := List.length_filter_le (fun x : String × β => x.1 != k) l
    by_cases hk : k = a
    · subst hk
      simp [List.filter]
      omega
    · have hka : (k == a) = false := by simpa using hk
      simp only [List.lookup, hka] at h
      have := ih h
      simp only [List.filter_cons]
      split <;> simp only [List.length_cons] <;> omega

/-- How a core variable is held. -/
inductive Kind where
  | owned | borrowed | scalar
  deriving BEq, Repr, Inhabited

/-- The core representation of a Koka variable: one core variable, or (for tuples and
    value types) one representation per component. -/
inductive Rep where
  | atom (x : String) (k : Kind)
  | flat (rs : List Rep)
  deriving Repr, Inhabited

/-- The core values of a representation. -/
def Rep.vals : Rep → List Val
  | .atom x _ => [.var x]
  | .flat rs => rs.flatMap Rep.vals

/-- The core binders of a representation. -/
def Rep.binders : Rep → List Binder
  | .atom x k => [{ name := x, scalar := k == .scalar }]
  | .flat rs => rs.flatMap Rep.binders

/-- Owned variables that are used later become borrowed. -/
def Rep.demote (used : List String) : Rep → Rep
  | .atom x .owned => if used.contains x then .atom x .borrowed else .atom x .owned
  | .atom x k => .atom x k
  | .flat rs => .flat (rs.map (Rep.demote used))

/-- The owned core variables of a representation. -/
def Rep.ownedNames : Rep → List String
  | .atom x .owned => [x]
  | .atom _ _ => []
  | .flat rs => rs.flatMap Rep.ownedNames

/-- The size of a representation (a measure for the pattern-matching matrix). -/
def Rep.size : Rep → Nat
  | .atom _ _ => 1
  | .flat rs => (rs.map Rep.size).sum + 1

/-- The compilation environment. -/
structure Env where
  types : List TypeDecl
  aliases : List (String × Ty)
  funs : List FunDecl
  vars : List (String × Ty × Rep) := []
  deriving Inhabited

/-- Expand type aliases.  An alias is not expanded inside its own expansion, so a
    recursive alias is left folded there. -/
def normWith : List (String × Ty) → Ty → Ty
  | as, .con n args =>
    match _h : as.lookup n with
    | some t => normWith (eraseKey as n) t
    | none => .con n (args.map (normWith as))
  | as, .fn ts r => .fn (ts.map (normWith as)) (normWith as r)
  | as, .tuple ts => .tuple (ts.map (normWith as))
termination_by as t => (as.length, sizeOf t)
decreasing_by
  all_goals simp_wf
  · exact Prod.Lex.left _ _ (length_eraseKey_lt ‹_›)
  all_goals (apply Prod.Lex.right; first | omega | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega))

namespace Env

def findType (env : Env) (n : String) : Option TypeDecl := env.types.find? (·.name == n)

def findCtor (env : Env) (c : String) : Option (TypeDecl × CtorDecl) :=
  env.types.findSome? fun d => (d.ctors.find? (·.name == c)).map (d, ·)

def findFun (env : Env) (f : String) : Option FunDecl := env.funs.find? (·.name == f)

def lookupVar (env : Env) (x : String) : Option (Ty × Rep) :=
  (env.vars.find? (·.1 == x)).map (·.2)

def bind (env : Env) (x : String) (t : Ty) (r : Rep) : Env :=
  { env with vars := (x, t, r) :: env.vars }

def demote (env : Env) (used : List String) : Env :=
  { env with vars := env.vars.map fun (x, t, r) => (x, t, r.demote used) }

/-- Expand type aliases. -/
def norm (env : Env) : Ty → Ty := normWith env.aliases

/-- Is this a declaration of a value type (unboxed, single constructor)? -/
def isValueDecl (d : TypeDecl) : Bool :=
  d.kind == .value && d.ctors.length == 1 && d.ctors.all (!·.fields.isEmpty)

/-- Is this an enumeration (all constructors are atoms)? -/
def isEnumDecl (d : TypeDecl) : Bool := d.ctors.all (·.fields.isEmpty)

/-- The field types of a constructor at a given instance of its type. -/
def fieldTys (d : TypeDecl) (c : CtorDecl) (args : List Ty) : List Ty :=
  let σ := d.params.zip (args ++ List.replicate d.params.length unk)
  c.fields.map fun (_, t) => Ty.subst σ t

/-- The shape of a type. -/
inductive Cls where
  | scalar | boxed | fn
  /-- an unboxed tuple, or a value type `name` -/
  | flat (comps : List Ty) (name : Option String)

/-- The shape of a type whose aliases are expanded. -/
def clsNorm (env : Env) : Ty → Cls
  | .con n args =>
    if primTypes.contains n then .scalar
    else match env.findType n with
      | some d =>
        if isEnumDecl d then .scalar
        else if isValueDecl d then
          match d.ctors with
          | [c] => .flat (fieldTys d c args) (some n)
          | _ => .boxed
        else .boxed
      | none => .boxed
  | .tuple ts => .flat ts none
  | .fn _ _ => .fn

/-- The shape of a type. -/
def cls (env : Env) (t : Ty) : Cls := env.clsNorm (env.norm t)

/-- The components of an unboxed type (`[]` for any other type). -/
def comps (env : Env) (t : Ty) : List Ty :=
  match env.cls t with
  | .flat cs _ => cs
  | _ => []

/-- The kind of a variable of type `t`: scalar, or the given kind `mode`. -/
def kindOf (env : Env) (t : Ty) (mode : Kind) : Kind :=
  match env.cls t with
  | .scalar => .scalar
  | _ => mode

end Env

/-! ## Type inference (just enough to know how variables are represented) -/

mutual
/-- One-way matching of a declared field type against an inferred argument type. -/
def matchTy (params : List String) : Ty → Ty → List (String × Ty) → List (String × Ty)
  | .con p [], t, σ => if params.contains p && !(t == unk) && (σ.lookup p).isNone then (p, t) :: σ else σ
  | .con _ as, .con _ bs, σ => matchTys params as bs σ
  | .tuple as, .tuple bs, σ => matchTys params as bs σ
  | _, _, σ => σ
/-- `matchTy`, componentwise. -/
def matchTys (params : List String) : List Ty → List Ty → List (String × Ty) → List (String × Ty)
  | a :: as, b :: bs, σ => matchTys params as bs (matchTy params a b σ)
  | _, _, σ => σ
end

mutual
/-- The (approximate) type of an expression. -/
def inferTy (env : Env) : Expr → Ty
  | .var x =>
    match env.lookupVar x with
    | some (t, _) => t
    | none => match env.findFun x with
      | some fd => .fn (fd.params.map (·.ty.getD unk)) (fd.ret.getD unk)
      | none => unk
  | .lit _ => .con "int" []
  | .app f args =>
    match env.findCtor f with
    | some (d, c) =>
      let σ := inferArgTys env d.params c.fields args []
      .con d.name (d.params.map fun p => (σ.lookup p).getD unk)
    | none =>
      match env.lookupVar f with
      | some (t, _) => match env.norm t with
        | .fn _ r => r
        | _ => unk
      | none => match env.findFun f with
        | some fd => fd.ret.getD unk
        | none => unk
  | .tuple es => .tuple (inferTys env es)
  | .binop _ _ _ => .con "bool" []
  | .ite _ t e =>
    let a := inferTy env t
    if a == unk then inferTy env e else a
  | .match _ _ cls => inferClauses env cls
  | .valIn _ _ e2 => inferTy env e2
/-- The types of a list of expressions. -/
def inferTys (env : Env) : List Expr → List Ty
  | [] => []
  | e :: es => inferTy env e :: inferTys env es
/-- Instantiate the type parameters `params` of a constructor with fields `fields` from
    the types of its arguments. -/
def inferArgTys (env : Env) (params : List String) :
    List (String × Ty) → List Expr → List (String × Ty) → List (String × Ty)
  | (_, ft) :: fs, a :: as, σ =>
    inferArgTys env params fs as (matchTy params ft (env.norm (inferTy env a)) σ)
  | _, _, σ => σ
/-- The type of the first clause whose type is known. -/
def inferClauses (env : Env) : List Clause → Ty
  | [] => unk
  | .mk _ _ b :: cs =>
    let a := inferTy env b
    if a == unk then inferClauses env cs else a
end

/-! ## Surface free variables and sizes -/

def Pat.binds (x : String) : Pat → Bool
  | .var y => x == y
  | .wild => false
  | .ctor _ ps => ps.attach.any fun ⟨p, _⟩ => Pat.binds x p
  | .tuple ps => ps.attach.any fun ⟨p, _⟩ => Pat.binds x p

mutual
def Expr.mentions (x : String) : Expr → Bool
  | .var y => x == y
  | .lit _ => false
  | .app f args => f == x || Expr.mentionsList x args
  | .tuple es => Expr.mentionsList x es
  | .binop _ a b => a.mentions x || b.mentions x
  | .ite c t e => c.mentions x || t.mentions x || e.mentions x
  | .match _ s cls => s.mentions x || Clause.mentionsList x cls
  | .valIn p e1 e2 => e1.mentions x || (!p.binds x && e2.mentions x)
def Expr.mentionsList (x : String) : List Expr → Bool
  | [] => false
  | e :: es => e.mentions x || Expr.mentionsList x es
def Expr.mentionsOpt (x : String) : Option Expr → Bool
  | none => false
  | some e => e.mentions x
def Clause.mentions (x : String) : Clause → Bool
  | .mk p g b => !p.binds x && (Expr.mentionsOpt x g || b.mentions x)
def Clause.mentionsList (x : String) : List Clause → Bool
  | [] => false
  | c :: cs => c.mentions x || Clause.mentionsList x cs
end

mutual
/-- The size of an expression: the measure on which the compiler recurses. -/
def Expr.size : Expr → Nat
  | .var _ | .lit _ => 1
  | .app _ args => Expr.sizeList args + 1
  | .tuple es => Expr.sizeList es + 1
  | .binop _ a b => a.size + b.size + 3
  | .ite c t e => c.size + t.size + e.size + 1
  | .match _ s cls => s.size + Clause.sizeList cls + 2
  | .valIn _ e1 e2 => e1.size + e2.size + 3
def Expr.sizeList : List Expr → Nat
  | [] => 0
  | e :: es => e.size + Expr.sizeList es + 1
def Expr.sizeOpt : Option Expr → Nat
  | none => 0
  | some e => e.size
def Clause.size : Clause → Nat
  | .mk _ g b => b.size + Expr.sizeOpt g + 1
def Clause.sizeList : List Clause → Nat
  | [] => 0
  | c :: cs => c.size + Clause.sizeList cs
end

/-- The size of a pattern: the number of constructor and tuple patterns in it. -/
def Pat.size : Pat → Nat
  | .var _ | .wild => 0
  | .ctor _ ps => (ps.map Pat.size).sum + 1
  | .tuple ps => (ps.map Pat.size).sum + 1

/-! ## The compiler -/

structure CState where
  next : Nat := 0
  /-- the Koka type of every core variable introduced -/
  tys : List (String × Ty) := []

abbrev CM := StateT CState (Except String)

def fresh (hint : String) : CM String := do
  let s ← get
  set { s with next := s.next + 1 }
  return s!"{hint}#{s.next}"

def recordTy (x : String) (t : Ty) : CM Unit :=
  modify fun s => { s with tys := (x, t) :: s.tys }

/-- A fresh core variable of type `t`, a scalar or of kind `mode`. -/
def freshAtom (env : Env) (hint : String) (t : Ty) (mode : Kind) : CM Rep := do
  let x ← fresh hint
  recordTy x t
  return .atom x (env.kindOf t mode)

/-- A fresh representation for a value of the type `t` (whose aliases are expanded);
    boxed components get kind `mode`.  `visited` are the value types being unboxed: a
    recursive value type is an error. -/
def freshRepN (env : Env) (hint : String) (mode : Kind) (visited : List String) (t : Ty) :
    CM Rep := do
  match t with
  | .tuple ts => return .flat (← ts.attach.mapM fun ⟨c, _⟩ => freshRepN env hint mode visited c)
  | _ =>
    match env.clsNorm t with
    | .flat comps (some n) =>
      if visited.length < env.types.length ∧ n ∉ visited then
        return .flat (← comps.mapM fun c => freshRepN env hint mode (n :: visited) (env.norm c))
      else throw s!"recursive value type '{n}'"
    | _ => freshAtom env hint t mode
termination_by (env.types.length - visited.length, sizeOf t)
decreasing_by
  all_goals simp_wf
  · apply Prod.Lex.right; have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega
  · apply Prod.Lex.left; have := (‹_ ∧ _›).1; omega

/-- A fresh representation for a value of type `t`; boxed components get kind `mode`. -/
def freshRep (env : Env) (hint : String) (t : Ty) (mode : Kind) : CM Rep :=
  freshRepN env hint mode [] (env.norm t)

def primOp : BinOp → FIP.PrimOp
  | .lt => .lt | .le => .le | .gt => .gt | .ge => .ge | .eq => .eq | .ne => .ne
  | _ => .eq

def hintOf : Expr → String
  | .app f _ => f
  | _ => "t"

/-- A row of the pattern-matching matrix. -/
structure Row where
  pats : List Pat
  binds : List (String × Ty × Rep)
  guard : Option Expr
  body : Expr
  deriving Inhabited

/-- The size of the code of a row. -/
def Row.size (r : Row) : Nat := r.body.size + Expr.sizeOpt r.guard + 1

/-- The rows of the clauses of a match. -/
def rowsOf (cls : List Clause) : List Row :=
  cls.map fun (.mk p g b) => { pats := [p], binds := [], guard := g, body := b }

theorem rowsOf_size (cls : List Clause) :
    ((rowsOf cls).map Row.size).sum = Clause.sizeList cls := by
  induction cls with
  | nil => rfl
  | cons c cs ih =>
    cases c
    simp only [rowsOf, List.map_cons, List.sum_cons, Clause.sizeList, Clause.size,
      Row.size] at ih ⊢
    omega

/-- A column of the matrix: the core representation of the value matched, and its type. -/
structure Occ where
  rep : Rep
  ty : Ty
  deriving Inhabited

/-- The measure of a matrix: the size of its code, of its patterns and of its columns, and
    its number of rows. -/
def matrixMeasure (occs : List Occ) (rows : List Row) : Nat × Nat × Nat × Nat :=
  ((rows.map Row.size).sum, (rows.map fun r => (r.pats.map Pat.size).sum).sum,
   (occs.map (·.rep.size)).sum, rows.length)

def isRefutable : Pat → Bool
  | .ctor _ _ => true
  | .tuple _ => true
  | _ => false

def Rep.isFlat : Rep → Bool
  | .flat _ => true
  | _ => false

/-- The destructed occurrences on the current path: variable ↦ constructor, fields. -/
abbrev DMap := List (String × String × List Rep)

/-- The value of an occurrence, rebuilding destructed cells. -/
def recon (dm : DMap) : Rep → List Val
  | .atom x _ =>
    match _h : dm.lookup x with
    | some (c, subs) => [.ctor c (subs.flatMap (recon (eraseKey dm x)))]
    | none => [.var x]
  | .flat rs => rs.flatMap (recon dm)
termination_by r => (dm.length, sizeOf r)
decreasing_by
  all_goals simp_wf
  · exact Prod.Lex.left _ _ (length_eraseKey_lt ‹_›)
  · apply Prod.Lex.right; have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega

/-- Is this expression compiled by binding it to fresh variables (rather than to values
    directly)? -/
def valTag (env : Env) : Expr → Nat
  | .var _ | .lit _ | .tuple _ => 0
  | .app c _ => if (env.findCtor c).isSome then 0 else 3
  | _ => 3

theorem lex_of_matrix {a b : Nat × Nat × Nat × Nat} {t : Nat}
    (h : Prod.Lex (· < ·) (Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·))) a b) :
    Prod.Lex (· < ·) (Prod.Lex (· < ·) (Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·))))
      (a.1, t, a.2) (b.1, t, b.2) := by
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  cases h with
  | left _ _ h => exact Prod.Lex.left _ _ h
  | right _ h => exact Prod.Lex.right _ (Prod.Lex.right _ h)

theorem valTag_le (env : Env) (e : Expr) : valTag env e ≤ 3 := by
  unfold valTag; split <;> (try split) <;> omega

/-- Discharge the termination goals of the compiler. -/
macro "compile_decreasing" : tactic =>
  `(tactic| all_goals (simp_wf <;> first
      | (apply Prod.Lex.left
         (try simp only [Expr.size, Expr.sizeList, Expr.sizeOpt, rowsOf_size,
           List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at *)
         omega)
      | (apply lex_lt_of_le (Nat.le_refl _)
         apply Prod.Lex.left
         (try simp only [valTag, *, Option.isSome_some, Option.isSome_none, if_true, if_false,
           Bool.false_eq_true])
         omega)
      | (apply lex_lt_of_le (Nat.le_refl _)
         apply Prod.Lex.left
         exact Nat.lt_of_le_of_lt (valTag_le _ _) (by decide))
      | (apply lex_lt_of_le
         · (try simp only [Expr.size, Expr.sizeList, Expr.sizeOpt, Row.size,
             List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at *)
           omega
         · exact Prod.Lex.left _ _ (by decide))))

mutual

/-- Compile an expression to values, passing them to the continuation `k`. -/
def compileVal (env : Env) (e : Expr) (k : List Val → CM IR.Expr) : CM IR.Expr :=
  match e with
  | .var x =>
    match env.lookupVar x with
    | some (_, r) => k r.vals
    | none =>
      if (env.findFun x).isSome then k [.fn x] else throw s!"unknown variable '{x}'"
  | .lit n => k [.lit n]
  | .app c args =>
    match _h : env.findCtor c with
    | some (d, cd) => do
      unless cd.fields.length == args.length || args.isEmpty && cd.fields.isEmpty do
        throw s!"constructor '{c}' expects {cd.fields.length} arguments"
      compileArgs env args fun vss => do
        if Env.isValueDecl d then k vss.flatten
        else
          let vs ← vss.mapM fun vs => match vs with
            | [v] => pure v
            | _ => throw s!"constructor '{c}': an unboxed value cannot be a field"
          k [.ctor c vs]
    | none => bindTo env (.app c args) k
  | .tuple es => compileArgs env es fun vss => k vss.flatten
  | .binop op a b => bindTo env (.binop op a b) k
  | .ite c t f => bindTo env (.ite c t f) k
  | .match d s cls => bindTo env (.match d s cls) k
  | .valIn p e1 e2 => bindTo env (.valIn p e1 e2) k
termination_by (e.size, valTag env e, 0, 0, 0)
decreasing_by compile_decreasing

/-- Compile a list of arguments from left to right. -/
def compileArgs (env : Env) (es : List Expr) (k : List (List Val) → CM IR.Expr) :
    CM IR.Expr :=
  match es with
  | [] => k []
  | e :: es => compileVal env e fun vs => compileArgs env es fun vss => k (vs :: vss)
termination_by (Expr.sizeList es, 0, 0, 0, 0)
decreasing_by compile_decreasing

/-- `let x̄ = e in k x̄`: variables used in the continuation are borrowed in `e`. -/
def bindTo (env : Env) (e : Expr) (k : List Val → CM IR.Expr) : CM IR.Expr := do
  let ty := inferTy env e
  let r ← freshRep env (hintOf e) ty .owned
  let body ← k r.vals
  let e1 ← compileTail (env.demote body.fv) e
  return .letIn r.binders e1 body
termination_by (e.size, 2, 0, 0, 0)
decreasing_by compile_decreasing

/-- Compile an expression in tail position. -/
def compileTail (env : Env) (e : Expr) : CM IR.Expr :=
  match e with
  | .app f args =>
    if (env.findCtor f).isSome then compileVal env (.app f args) fun vs => pure (.ret vs)
    else match env.lookupVar f with
      | some (_, .atom x _) =>
        compileArgs env args fun vss => pure (.app (.var x) (.ret vss.flatten))
      | some _ => throw s!"'{f}' is not a function"
      | none => match env.findFun f with
        | some fd => do
          unless fd.params.length == args.length do
            throw s!"function '{f}' expects {fd.params.length} arguments"
          compileArgs env args fun vss => do
            let pairs := fd.params.zip vss
            let b := (pairs.filter (·.1.borrowed)).flatMap (·.2)
            let o := (pairs.filter (!·.1.borrowed)).flatMap (·.2)
            pure (.call f (.ret b) (.ret o))
        | none => throw s!"unknown function '{f}'"
  | .binop .and a b => compileCond env a (compileTail env b) (pure (.ret [.ctor "False" []]))
  | .binop .or a b => compileCond env a (pure (.ret [.ctor "True" []])) (compileTail env b)
  | .binop op a b =>
    compileArgs env [a, b] fun vss => match vss with
      | [[va], [vb]] => pure (.prim (primOp op) [va, vb])
      | _ => throw "a comparison expects scalar arguments"
  | .ite c t f =>
    compileCond env c (compileTail env t) (compileTail env f)
  | .match _ scrut cls => compileMatchOn env scrut (rowsOf cls)
  | .valIn p e1 e2 =>
    compileMatchOn env e1 [{ pats := [p], binds := [], guard := none, body := e2 }]
  | .var x => compileVal env (.var x) fun vs => pure (.ret vs)
  | .lit n => compileVal env (.lit n) fun vs => pure (.ret vs)
  | .tuple es => compileVal env (.tuple es) fun vs => pure (.ret vs)
termination_by (e.size, 1, 0, 0, 0)
decreasing_by compile_decreasing

/-- Compile a match of `scrut` against the rows `rows`. -/
def compileMatchOn (env : Env) (scrut : Expr) (rows : List Row) : CM IR.Expr :=
  match scrut with
  | .var x =>
    match env.lookupVar x with
    | some (t, r) => compileMatch env [] [⟨r, t⟩] rows
    | none => throw s!"unknown variable '{x}'"
  | s => do
    let ty := inferTy env s
    let r ← freshRep env (hintOf s) ty .owned
    let body ← compileMatch env [] [⟨r, ty⟩] rows
    let e1 ← compileTail (env.demote body.fv) s
    return .letIn r.binders e1 body
termination_by (scrut.size + (rows.map Row.size).sum + 1, 0, 0, 0, 0)
decreasing_by compile_decreasing

/-- `if c then t else f`, with the branches given as core computations. -/
def compileCond (env : Env) (c : Expr) (t f : CM IR.Expr) : CM IR.Expr :=
  compileVal env c fun vs => match vs with
    | [.ctor "True" []] => t
    | [.ctor "False" []] => f
    | [.var x] => do
      let t' ← t
      let f' ← f
      pure (.bmatch (.var x) [.mk "True" [] t', .mk "False" [] f'])
    | _ => throw "a condition must be a boolean"
termination_by (c.size, 4, 0, 0, 0)
decreasing_by compile_decreasing

/-- The pattern-matching matrix. -/
def compileMatch (env : Env) (dm : DMap) (occs : List Occ) (rows : List Row) :
    CM IR.Expr := do
  -- unboxed columns are expanded into their components
  match occs.findIdx? (·.rep.isFlat) with
  | some i =>
    let occ := occs[i]!
    let rs := match occ.rep with | .flat rs => rs | _ => []
    let tys : List Ty := match env.cls occ.ty with
      | .flat ts _ => ts
      | _ => List.replicate rs.length unk
    let subs : List Occ := (rs.zip (tys ++ List.replicate rs.length unk)).map fun (r, t) => ⟨r, t⟩
    let rows' ← rows.mapM fun row => do
      let p := row.pats[i]!
      let ps ← match p with
        | .tuple ps => pure ps
        | .ctor _ ps => pure ps
        | _ => pure []
      let ps := ps ++ List.replicate (rs.length - ps.length) Pat.wild
      unless ps.length == rs.length do throw "pattern arity mismatch"
      let binds := match p with
        | .var x => (x, occ.ty, occ.rep) :: row.binds
        | _ => row.binds
      pure { row with pats := row.pats.take i ++ ps ++ row.pats.drop (i + 1), binds }
    let occs' := occs.take i ++ subs ++ occs.drop (i + 1)
    if Prod.Lex (· < ·) (Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·)))
        (matrixMeasure occs' rows') (matrixMeasure occs rows) then
      compileMatch env dm occs' rows'
    else noProgress "compiler"
  | none =>
  match rows with
  | [] => throw "non-exhaustive match"
  | row :: rest =>
    match row.pats.findIdx? isRefutable with
    | none =>
      let binds := row.binds ++ (row.pats.zip occs).filterMap fun (p, o) =>
        match p with
        | .var x => some (x, o.ty, o.rep)
        | _ => none
      compileRow env dm binds row.guard row.body (compileMatch env dm occs rest)
    | some i =>
      let rows := row :: rest
      let occ := occs[i]!
      let cname := match row.pats[i]! with | .ctor c _ => c | _ => ""
      let some (d, _) := env.findCtor cname | throw s!"unknown constructor '{cname}'"
      let (x, kind) ← match occ.rep with
        | .atom x k => pure (x, k)
        | _ => throw "internal error: flat occurrence"
      let args := match env.norm occ.ty with
        | .con _ as => as
        | _ => []
      let hasDefault := rows.any fun r => !isRefutable r.pats[i]!
      let needed := d.ctors.filter fun c =>
        hasDefault || rows.any fun r => match r.pats[i]! with
          | .ctor c' _ => c' == c.name
          | _ => false
      let destr := kind == .owned
      let fmode := if destr then Kind.owned else Kind.borrowed
      let brs ← needed.mapM fun cd => do
        let ftys := Env.fieldTys d cd args
        let subs ← (cd.fields.zip ftys).mapM fun ((fname, _), ft) => freshAtom env fname ft fmode
        let k := cd.fields.length
        let rows' ← rows.filterMapM fun r => do
          let p := r.pats[i]!
          let spec (ps : List Pat) := r.pats.take i ++ ps ++ r.pats.drop (i + 1)
          match p with
          | .ctor c ps =>
            if c == cd.name then
              unless ps.length ≤ k do throw s!"too many arguments in pattern '{c}'"
              pure (some { r with pats := spec (ps ++ List.replicate (k - ps.length) .wild) })
            else pure none
          | .var y =>
            pure (some { r with pats := spec (List.replicate k .wild),
                                binds := r.binds ++ [(y, occ.ty, occ.rep)] })
          | _ => pure (some { r with pats := spec (List.replicate k .wild) })
        let dm' := if destr then (x, cd.name, subs) :: dm else dm
        let subOccs := (subs.zip ftys).map fun (r, t) => (⟨r, t⟩ : Occ)
        let occs' := occs.take i ++ subOccs ++ occs.drop (i + 1)
        if Prod.Lex (· < ·) (Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·)))
            (matrixMeasure occs' rows') (matrixMeasure occs (row :: rest)) then
          let body ← compileMatch env dm' occs' rows'
          pure (Branch.mk cd.name (subs.flatMap Rep.binders) body)
        else noProgress "compiler"
      if destr then return .dmatch (.var x) brs
      else return .bmatch (.var x) brs
termination_by ((rows.map Row.size).sum, 6, (matrixMeasure occs rows).2)
decreasing_by
  · exact lex_of_matrix ‹_›
  · simp_wf
    apply Prod.Lex.left
    simp only [Row.size]; omega
  · simp_wf
    apply lex_lt_of_le _ (Prod.Lex.left _ _ (by decide : 5 < 6))
    simp only [Row.size]; omega
  · exact lex_of_matrix ‹_›

/-- The body of a matched row: bind its variables (rebuilding destructed values), check
    the guard, and fall back to the remaining rows if it fails. -/
def compileRow (env : Env) (dm : DMap) (binds : List (String × Ty × Rep))
    (guard : Option Expr) (body : Expr) (fallback : CM IR.Expr) : CM IR.Expr := do
  -- aliases are bound directly; destructed values are rebuilt after the guard
  let mut envG := env
  let mut rebuildM : List (String × Ty × List Val) := []
  for (x, t, r) in binds do
    let vs := recon dm r
    if vs == r.vals then envG := envG.bind x t r
    else if body.mentions x then rebuildM := rebuildM ++ [(x, t, vs)]
  let rebuild := rebuildM
  let envG' := envG
  let tbody : CM IR.Expr := do
    let mut envB := envG'
    let mut lets : List (List Binder × List Val) := []
    for (x, t, vs) in rebuild do
      let r' ← freshRep env x t .owned
      envB := envB.bind x t r'
      lets := lets ++ [(r'.binders, vs)]
    let core ← compileTail envB body
    return lets.foldr (fun (bs, vs) acc => .letIn bs (.ret vs) acc) core
  match guard with
  | none => tbody
  | some g => compileCond envG' g tbody fallback
termination_by (body.size + Expr.sizeOpt guard + 1, 5, 0, 0, 0)
decreasing_by compile_decreasing

end

/-! ## Unused owned variables -/

/-- The owned (non-scalar) variables bound by binders. -/
def ownedBinders (xs : List Binder) : List String :=
  (xs.filter (!·.scalar)).map (·.name)

mutual
/-- Consume the unused owned variables `owned` of `e`: in a `fip` function destruct them
    (if their type has a single constructor), in a `fbip` function `drop` them.
    `visited` are the types being destructed: a field of a type that is being destructed
    is not destructed again. -/
def consume (env : Env) (fbip : Bool) (visited : List String) (owned : List String)
    (e : IR.Expr) : CM IR.Expr := do
  let fv := e.fv
  let used := owned.filter fun x => fv.contains x
  let unused := owned.filter fun x => !fv.contains x
  let e' ← consumeIn env fbip visited used e
  unused.foldlM (fun acc u => consumeVar env fbip visited u acc) e'
termination_by (env.types.length - visited.length, sizeOf e + 1, 2)

/-- Push the consumption of the variables `used` into `e`. -/
def consumeIn (env : Env) (fbip : Bool) (visited : List String) (used : List String)
    (e : IR.Expr) : CM IR.Expr := do
  match e with
  | .letIn xs e1 e2 =>
    let f1 := e1.fv
    let f2 := e2.fv
    let o1 := used.filter fun x => f1.contains x && !f2.contains x
    let o2 := used.filter (!o1.contains ·) ++ ownedBinders xs
    return .letIn xs (← consume env fbip visited o1 e1) (← consume env fbip visited o2 e2)
  | .dmatch (.var x) bs =>
    let bs' ← bs.attach.mapM fun ⟨.mk c xs b, _⟩ => do
      return Branch.mk c xs (← consume env fbip visited (used.erase x ++ ownedBinders xs) b)
    return .dmatch (.var x) bs'
  | .bmatch s bs =>
    let bs' ← bs.attach.mapM fun ⟨.mk c xs b, _⟩ => do
      return Branch.mk c xs (← consume env fbip visited used b)
    return .bmatch s bs'
  | .drop v b => return .drop v (← consumeIn env fbip visited used b)
  | .free k b => return .free k (← consumeIn env fbip visited used b)
  | _ => return e
termination_by (env.types.length - visited.length, sizeOf e + 1, 1)
decreasing_by
  all_goals simp_wf
  all_goals (apply Prod.Lex.right; apply Prod.Lex.left)
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; simp only [IR.Branch.mk.sizeOf_spec] at this; omega)

/-- Consume the unused owned variable `u` around `acc`. -/
def consumeVar (env : Env) (fbip : Bool) (visited : List String) (u : String)
    (acc : IR.Expr) : CM IR.Expr := do
  if fbip then return .drop (.var u) acc
  let t := ((← get).tys.lookup u).getD unk
  match env.norm t with
  | .con n args =>
    match env.findType n with
    | some d =>
      match d.ctors with
      | [cd] =>
        if cd.fields.isEmpty then return acc
        if visited.length < env.types.length ∧ n ∉ visited then
          let ftys := Env.fieldTys d cd args
          let subs ← (cd.fields.zip ftys).flatMapM fun ((fname, _), ft) => do
            return (← freshAtom env fname ft .owned).binders
          let body ← consume env fbip (n :: visited) (ownedBinders subs) acc
          return .dmatch (.var u) [.mk cd.name subs body]
        else return acc
      | _ => return acc
    | none => return acc
  | _ => return acc
termination_by (env.types.length - visited.length, 0, 0)
decreasing_by
  all_goals simp_wf
  apply Prod.Lex.left; have := (‹_ ∧ _›).1; omega
end

/-! ## Functions and programs -/

/-- The raw output of the compiler: the type declarations and the core signature of a
    Koka program.  `Koka.Module` (in `RequestProject/Frontend/Module.lean`) adds the names of
    its functions and constructors as indices, with the proofs that tie them together. -/
structure RawModule where
  types : List TypeDecl
  sig : FIP.Sig
  deriving Inhabited

/-- The representation of a parameter. -/
def paramRep (env : Env) (p : Param) : Rep :=
  let t := p.ty.getD unk
  let mode := if p.borrowed then Kind.borrowed else Kind.owned
  match env.cls t with
  | .flat comps _ =>
    .flat ((List.range comps.length).zip comps |>.map fun (i, c) =>
      .atom s!"{p.name}#{i}" (env.kindOf c mode))
  | _ => .atom p.name (env.kindOf t mode)

/-- Compile a function declaration. -/
def compileFun (env : Env) (fd : FunDecl) : Except String FIP.FunDef := do
  let reps := fd.params.map fun p => (p, paramRep env p)
  let env' := reps.foldl (fun env (p, r) => env.bind p.name (p.ty.getD unk) r) env
  let tys := reps.flatMap fun (p, r) => match r with
    | .atom x _ => [(x, p.ty.getD unk)]
    | .flat rs =>
      (rs.zip (env.comps (p.ty.getD unk))).filterMap fun (r, c) => match r with
        | .atom x _ => some (x, c)
        | _ => none
  let prog : CM IR.Expr := do
    let body ← compileTail env' fd.body
    match fd.annot with
    | .plain => return body
    | a =>
      let owned := (reps.filter (!·.1.borrowed)).flatMap (·.2.ownedNames)
      consume env (match a with | .fbip _ => true | _ => false) [] owned body
  match prog.run { tys } with
  | .ok (body, _) =>
    match IR.resolveFun fd.name ((reps.filter (·.1.borrowed)).flatMap (·.2.binders))
        ((reps.filter (!·.1.borrowed)).flatMap (·.2.binders)) body fd.annot with
    | .ok f => return f
    | .error msg => throw s!"in function '{fd.name}': {msg}"
  | .error msg => throw s!"in function '{fd.name}': {msg}"

/-- Compile a whole program. -/
def compileProgram (p : Program) : Except String RawModule := do
  let types := p.filterMap fun d => match d with | .type t => some t | _ => none
  let aliases := p.filterMap fun d => match d with | .alias x t => some (x, t) | _ => none
  let funs := p.filterMap fun d => match d with | .fn f => some f | _ => none
  let env : Env := { types := types ++ builtinTypes, aliases, funs }
  let sig ← funs.mapM (compileFun env)
  return { types, sig }

/-- Parse and compile Koka source code. -/
def compileSource (src : String) : Except String RawModule := do
  compileProgram (← parseProgram src)

end Koka
