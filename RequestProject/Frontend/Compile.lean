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
the results of evaluation by `IR.Expr.eval_sound`.
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
partial def Ty.subst (σ : List (String × Ty)) : Ty → Ty
  | .con n [] => (σ.lookup n).getD (.con n [])
  | .con n args => .con n (args.map (Ty.subst σ))
  | .fn as r => .fn (as.map (Ty.subst σ)) (Ty.subst σ r)
  | .tuple ts => .tuple (ts.map (Ty.subst σ))

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

partial def Rep.vals : Rep → List Val
  | .atom x _ => [.var x]
  | .flat rs => rs.flatMap Rep.vals

partial def Rep.binders : Rep → List Binder
  | .atom x k => [{ name := x, scalar := k == .scalar }]
  | .flat rs => rs.flatMap Rep.binders

/-- Owned variables that are used later become borrowed. -/
partial def Rep.demote (used : List String) : Rep → Rep
  | .atom x .owned => if used.contains x then .atom x .borrowed else .atom x .owned
  | .atom x k => .atom x k
  | .flat rs => .flat (rs.map (Rep.demote used))

partial def Rep.ownedNames : Rep → List String
  | .atom x .owned => [x]
  | .atom _ _ => []
  | .flat rs => rs.flatMap Rep.ownedNames

/-- The compilation environment. -/
structure Env where
  types : List TypeDecl
  aliases : List (String × Ty)
  funs : List FunDecl
  vars : List (String × Ty × Rep) := []
  deriving Inhabited

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
partial def norm (env : Env) : Ty → Ty
  | .con n args =>
    match env.aliases.lookup n with
    | some t => env.norm t
    | none => .con n (args.map env.norm)
  | .fn as r => .fn (as.map env.norm) (env.norm r)
  | .tuple ts => .tuple (ts.map env.norm)

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
  | flat (comps : List Ty)

def cls (env : Env) (t : Ty) : Cls :=
  match env.norm t with
  | .con n args =>
    if primTypes.contains n then .scalar
    else match env.findType n with
      | some d =>
        if isEnumDecl d then .scalar
        else if isValueDecl d then
          match d.ctors with
          | [c] => .flat (fieldTys d c (args.map env.norm))
          | _ => .boxed
        else .boxed
      | none => .boxed
  | .tuple ts => .flat ts
  | .fn _ _ => .fn

end Env

/-! ## Type inference (just enough to know how variables are represented) -/

/-- One-way matching of a declared field type against an inferred argument type. -/
partial def matchTy (params : List String) : Ty → Ty → List (String × Ty) → List (String × Ty)
  | .con p [], t, σ => if params.contains p && !(t == unk) && (σ.lookup p).isNone then (p, t) :: σ else σ
  | .con _ as, .con _ bs, σ => (as.zip bs).foldl (fun σ (a, b) => matchTy params a b σ) σ
  | .tuple as, .tuple bs, σ => (as.zip bs).foldl (fun σ (a, b) => matchTy params a b σ) σ
  | _, _, σ => σ

mutual
/-- The (approximate) type of an expression. -/
partial def inferTy (env : Env) : Expr → Ty
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
      let σ := (c.fields.zip args).foldl
        (fun σ ((_, ft), a) => matchTy d.params ft (env.norm (inferTy env a)) σ) []
      .con d.name (d.params.map fun p => (σ.lookup p).getD unk)
    | none =>
      match env.lookupVar f with
      | some (t, _) => match env.norm t with
        | .fn _ r => r
        | _ => unk
      | none => match env.findFun f with
        | some fd => fd.ret.getD unk
        | none => unk
  | .tuple es => .tuple (es.map (inferTy env))
  | .binop _ _ _ => .con "bool" []
  | .ite _ t e =>
    let a := inferTy env t
    if a == unk then inferTy env e else a
  | .match _ _ cls => inferClauses env cls
  | .valIn _ _ e2 => inferTy env e2
partial def inferClauses (env : Env) : List Clause → Ty
  | [] => unk
  | .mk _ _ b :: cs =>
    let a := inferTy env b
    if a == unk then inferClauses env cs else a
end

/-! ## Surface free variables -/

partial def Pat.binds (x : String) : Pat → Bool
  | .var y => x == y
  | .wild => false
  | .ctor _ ps => ps.any (Pat.binds x)
  | .tuple ps => ps.any (Pat.binds x)

mutual
partial def Expr.mentions (x : String) : Expr → Bool
  | .var y => x == y
  | .lit _ => false
  | .app f args => f == x || args.any (Expr.mentions x)
  | .tuple es => es.any (Expr.mentions x)
  | .binop _ a b => a.mentions x || b.mentions x
  | .ite c t e => c.mentions x || t.mentions x || e.mentions x
  | .match _ s cls => s.mentions x || cls.any (Clause.mentions x)
  | .valIn p e1 e2 => e1.mentions x || (!p.binds x && e2.mentions x)
partial def Clause.mentions (x : String) : Clause → Bool
  | .mk p g b => !p.binds x && (g.any (Expr.mentions x) || b.mentions x)
end

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

/-- A fresh representation for a value of type `t`; boxed components get kind `mode`. -/
partial def freshRep (env : Env) (hint : String) (t : Ty) (mode : Kind) : CM Rep := do
  match env.cls t with
  | .flat comps => return .flat (← comps.mapM fun c => freshRep env hint c mode)
  | .scalar => let x ← fresh hint; recordTy x t; return .atom x .scalar
  | _ => let x ← fresh hint; recordTy x t; return .atom x mode

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

/-- A column of the matrix: the core representation of the value matched, and its type. -/
structure Occ where
  rep : Rep
  ty : Ty
  deriving Inhabited

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
partial def recon (dm : DMap) : Rep → List Val
  | .atom x _ =>
    match dm.lookup x with
    | some (c, subs) => [.ctor c (subs.flatMap (recon dm))]
    | none => [.var x]
  | .flat rs => rs.flatMap (recon dm)

mutual

/-- Compile an expression to values, passing them to the continuation `k`. -/
partial def compileVal (env : Env) (e : Expr) (k : List Val → CM IR.Expr) : CM IR.Expr := do
  match e with
  | .var x =>
    match env.lookupVar x with
    | some (_, r) => k r.vals
    | none =>
      if (env.findFun x).isSome then k [.fn x] else throw s!"unknown variable '{x}'"
  | .lit n => k [.lit n]
  | .app c args =>
    match env.findCtor c with
    | some (d, cd) =>
      unless cd.fields.length == args.length || args.isEmpty && cd.fields.isEmpty do
        throw s!"constructor '{c}' expects {cd.fields.length} arguments"
      compileArgs env args fun vss => do
        if Env.isValueDecl d then k vss.flatten
        else
          let vs ← vss.mapM fun vs => match vs with
            | [v] => pure v
            | _ => throw s!"constructor '{c}': an unboxed value cannot be a field"
          k [.ctor c vs]
    | none => bindTo env e k
  | .tuple es => compileArgs env es fun vss => k vss.flatten
  | _ => bindTo env e k

/-- Compile a list of arguments from left to right. -/
partial def compileArgs (env : Env) : List Expr → (List (List Val) → CM IR.Expr) → CM IR.Expr
  | [], k => k []
  | e :: es, k => compileVal env e fun vs => compileArgs env es fun vss => k (vs :: vss)

/-- `let x̄ = e in k x̄`: variables used in the continuation are borrowed in `e`. -/
partial def bindTo (env : Env) (e : Expr) (k : List Val → CM IR.Expr) : CM IR.Expr := do
  let ty := inferTy env e
  let r ← freshRep env (hintOf e) ty .owned
  let body ← k r.vals
  let e1 ← compileTail (env.demote body.fv) e
  return .letIn r.binders e1 body

/-- Compile an expression in tail position. -/
partial def compileTail (env : Env) (e : Expr) : CM IR.Expr := do
  match e with
  | .app f args =>
    if (env.findCtor f).isSome then compileVal env e fun vs => pure (.ret vs)
    else match env.lookupVar f with
      | some (_, .atom x _) =>
        compileArgs env args fun vss => pure (.app (.var x) (.ret vss.flatten))
      | some _ => throw s!"'{f}' is not a function"
      | none => match env.findFun f with
        | some fd =>
          unless fd.params.length == args.length do
            throw s!"function '{f}' expects {fd.params.length} arguments"
          compileArgs env args fun vss => do
            let pairs := fd.params.zip vss
            let b := (pairs.filter (·.1.borrowed)).flatMap (·.2)
            let o := (pairs.filter (!·.1.borrowed)).flatMap (·.2)
            pure (.call f (.ret b) (.ret o))
        | none => throw s!"unknown function '{f}'"
  | .binop .and a b => compileTail env (.ite a b (.app "False" []))
  | .binop .or a b => compileTail env (.ite a (.app "True" []) b)
  | .binop op a b =>
    compileArgs env [a, b] fun vss => match vss with
      | [[va], [vb]] => pure (.prim (primOp op) [va, vb])
      | _ => throw "a comparison expects scalar arguments"
  | .ite c t f =>
    compileCond env c (compileTail env t) (compileTail env f)
  | .match _ scrut cls =>
    let rows := cls.map fun (.mk p g b) => { pats := [p], binds := [], guard := g, body := b }
    let ty := inferTy env scrut
    match scrut with
    | .var x =>
      match env.lookupVar x with
      | some (t, r) => compileMatch env [] [⟨r, t⟩] rows
      | none => throw s!"unknown variable '{x}'"
    | _ =>
      let r ← freshRep env (hintOf scrut) ty .owned
      let body ← compileMatch env [] [⟨r, ty⟩] rows
      let e1 ← compileTail (env.demote body.fv) scrut
      return .letIn r.binders e1 body
  | .valIn p e1 e2 => compileTail env (.match false e1 [.mk p none e2])
  | _ => compileVal env e fun vs => pure (.ret vs)

/-- `if c then t else f`, with the branches given as core computations. -/
partial def compileCond (env : Env) (c : Expr) (t f : CM IR.Expr) : CM IR.Expr :=
  compileVal env c fun vs => match vs with
    | [.ctor "True" []] => t
    | [.ctor "False" []] => f
    | [.var x] => do
      let t' ← t
      let f' ← f
      pure (.bmatch (.var x) [.mk "True" [] t', .mk "False" [] f'])
    | _ => throw "a condition must be a boolean"

/-- The pattern-matching matrix. -/
partial def compileMatch (env : Env) (dm : DMap) (occs : List Occ) (rows : List Row) :
    CM IR.Expr := do
  -- unboxed columns are expanded into their components
  match occs.findIdx? (·.rep.isFlat) with
  | some i =>
    let occ := occs[i]!
    let rs := match occ.rep with | .flat rs => rs | _ => []
    let tys : List Ty := match env.cls occ.ty with
      | .flat ts => ts
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
    compileMatch env dm (occs.take i ++ subs ++ occs.drop (i + 1)) rows'
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
        let subs ← (cd.fields.zip ftys).mapM fun ((fname, _), ft) => do
          match env.cls ft with
          | .scalar => let y ← fresh fname; recordTy y ft; pure (Rep.atom y .scalar)
          | _ => let y ← fresh fname; recordTy y ft; pure (Rep.atom y fmode)
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
        let body ← compileMatch env dm' (occs.take i ++ subOccs ++ occs.drop (i + 1)) rows'
        pure (Branch.mk cd.name (subs.flatMap Rep.binders) body)
      if destr then return .dmatch (.var x) brs
      else return .bmatch (.var x) brs

/-- The body of a matched row: bind its variables (rebuilding destructed values), check
    the guard, and fall back to the remaining rows if it fails. -/
partial def compileRow (env : Env) (dm : DMap) (binds : List (String × Ty × Rep))
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

end

/-! ## Unused owned variables -/

/-- The owned (non-scalar) variables bound by binders. -/
def ownedBinders (xs : List Binder) : List String :=
  (xs.filter (!·.scalar)).map (·.name)

/-- Consume the unused owned variables: in a `fip` function destruct them (if their type
    has a single constructor), in a `fbip` function `drop` them. -/
partial def consume (env : Env) (fbip : Bool) (owned : List String) (e : IR.Expr) :
    CM IR.Expr := do
  let fv := e.fv
  let used := owned.filter fun x => fv.contains x
  let unused := owned.filter fun x => !fv.contains x
  let e' ← go used e
  unused.foldlM (fun acc u => wrap u acc) e'
where
  go (used : List String) (e : IR.Expr) : CM IR.Expr := do
    match e with
    | .letIn xs e1 e2 =>
      let f1 := e1.fv
      let f2 := e2.fv
      let o1 := used.filter fun x => f1.contains x && !f2.contains x
      let o2 := used.filter (!o1.contains ·) ++ ownedBinders xs
      return .letIn xs (← consume env fbip o1 e1) (← consume env fbip o2 e2)
    | .dmatch (.var x) bs =>
      let bs' ← bs.mapM fun (.mk c xs b) => do
        return Branch.mk c xs (← consume env fbip (used.erase x ++ ownedBinders xs) b)
      return .dmatch (.var x) bs'
    | .bmatch s bs =>
      let bs' ← bs.mapM fun (.mk c xs b) => do
        return Branch.mk c xs (← consume env fbip used b)
      return .bmatch s bs'
    | .drop v b => return .drop v (← go used b)
    | .free k b => return .free k (← go used b)
    | _ => return e
  wrap (u : String) (acc : IR.Expr) : CM IR.Expr := do
    if fbip then return .drop (.var u) acc
    let t := ((← get).tys.lookup u).getD unk
    match env.norm t with
    | .con n args =>
      match env.findType n with
      | some d =>
        match d.ctors with
        | [cd] =>
          if cd.fields.isEmpty then return acc
          let ftys := Env.fieldTys d cd args
          let subs ← (cd.fields.zip ftys).mapM fun ((fname, _), ft) => do
            let y ← fresh fname
            recordTy y ft
            match env.cls ft with
            | .scalar => pure (Binder.mk y true)
            | _ => pure (Binder.mk y false)
          let body ← consume env fbip (ownedBinders subs) acc
          return .dmatch (.var u) [.mk cd.name subs body]
        | _ => return acc
      | none => return acc
    | _ => return acc

/-! ## Functions and programs -/

/-- A compiled Koka module: its type declarations and the core signature. -/
structure Module where
  types : List TypeDecl
  sig : FIP.Sig
  deriving Inhabited

/-- The representation of a parameter. -/
def paramRep (env : Env) (p : Param) : Rep :=
  let t := p.ty.getD unk
  let mode := if p.borrowed then Kind.borrowed else Kind.owned
  match env.cls t with
  | .scalar => .atom p.name .scalar
  | .flat comps =>
    .flat ((List.range comps.length).zip comps |>.map fun (i, c) =>
      match env.cls c with
      | .scalar => .atom s!"{p.name}#{i}" .scalar
      | _ => .atom s!"{p.name}#{i}" mode)
  | _ => .atom p.name mode

/-- Compile a function declaration. -/
def compileFun (env : Env) (fd : FunDecl) : Except String FIP.FunDef := do
  let reps := fd.params.map fun p => (p, paramRep env p)
  let env' := reps.foldl (fun env (p, r) => env.bind p.name (p.ty.getD unk) r) env
  let tys := reps.flatMap fun (p, r) => match r with
    | .atom x _ => [(x, p.ty.getD unk)]
    | .flat rs =>
      let comps := match env.cls (p.ty.getD unk) with | .flat cs => cs | _ => []
      (rs.zip comps).filterMap fun (r, c) => match r with
        | .atom x _ => some (x, c)
        | _ => none
  let prog : CM IR.Expr := do
    let body ← compileTail env' fd.body
    match fd.annot with
    | .plain => return body
    | a =>
      let owned := (reps.filter (!·.1.borrowed)).flatMap (·.2.ownedNames)
      consume env (match a with | .fbip _ => true | _ => false) owned body
  match prog.run { tys } with
  | .ok (body, _) =>
    match IR.resolveFun fd.name ((reps.filter (·.1.borrowed)).flatMap (·.2.binders))
        ((reps.filter (!·.1.borrowed)).flatMap (·.2.binders)) body fd.annot with
    | .ok f => return f
    | .error msg => throw s!"in function '{fd.name}': {msg}"
  | .error msg => throw s!"in function '{fd.name}': {msg}"

/-- Compile a whole program. -/
def compileProgram (p : Program) : Except String Module := do
  let types := p.filterMap fun d => match d with | .type t => some t | _ => none
  let aliases := p.filterMap fun d => match d with | .alias x t => some (x, t) | _ => none
  let funs := p.filterMap fun d => match d with | .fn f => some f | _ => none
  let env : Env := { types := types ++ builtinTypes, aliases, funs }
  let sig ← funs.mapM (compileFun env)
  return { types, sig }

/-- Parse and compile Koka source code. -/
def compileSource (src : String) : Except String Module := do
  compileProgram (← parseProgram src)

end Koka
