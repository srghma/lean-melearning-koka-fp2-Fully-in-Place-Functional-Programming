module

public import RequestProject.Koka.Ast

@[expose] public section

/-!
# A parser for the Koka surface language

A hand-written lexer and layout-sensitive recursive-descent parser, so that the code of
the paper can be written essentially verbatim inside `[KOKA| ... ]`:

* identifiers may contain dashes (`reverse-acc`, `set-black`) and primes (`xs'`),
* `//` and `/* */` comments,
* blocks are delimited by indentation (or by `{ ... ; ... }`),
* `x.f(args)` is method-call syntax for `f(x, args)`.

Layout: a block opened on a new line has the column of its first token; a later line
starting at that column begins a new item, a line starting left of it closes the block,
and a line starting right of it continues the current item.  The keywords `then`,
`elif` and `else` always continue the current item.
-/

namespace Koka

/-- Tokens. -/
inductive Tok where
  | ident (s : String)
  | ctor (s : String)
  | int (n : Int)
  | sym (s : String)
  | kw (s : String)
  deriving Repr, Inhabited, BEq

/-- A token with its position. -/
structure Token where
  tok : Tok
  line : Nat
  col : Nat
  deriving Repr, Inhabited

def keywords : List String :=
  ["fun", "fip", "fbip", "match", "if", "then", "elif", "else", "val", "alias", "import",
   "fn"]

def symbols : List String :=
  ["->", "<=", ">=", "==", "!=", "&&", "||", "(", ")", "{", "}", ",", ";", ":", "=",
   "<", ">", "|", "^", ".", "_", "[", "]"]

def isIdStart (c : Char) : Bool := c.isAlpha
def isIdChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '\''

/-- Split a string into tokens. -/
partial def lex (s : String) : Except String (Array Token) :=
  go s.toList 1 0 #[]
where
  go : List Char → Nat → Nat → Array Token → Except String (Array Token)
  | [], _, _, acc => .ok acc
  | '\n' :: cs, line, _, acc => go cs (line + 1) 0 acc
  | '/' :: '/' :: cs, line, col, acc =>
    let rest := cs.dropWhile (· != '\n')
    go rest line col acc
  | '/' :: '*' :: cs, line, col, acc => skipComment cs line (col + 2) acc
  | c :: cs, line, col, acc =>
    if c == ' ' || c == '\t' || c == '\r' then go cs line (col + 1) acc
    else if c.isDigit then
      let ds := (c :: cs).takeWhile Char.isDigit
      let rest := (c :: cs).dropWhile Char.isDigit
      go rest line (col + ds.length)
        (acc.push ⟨.int (String.ofList ds).toNat!, line, col⟩)
    else if isIdStart c then
      let (idc, rest) := ident (c :: cs) []
      let name := String.ofList idc
      let (tok, rest, len) :=
        if name == "match" then
          match rest with
          | '!' :: r => (Tok.kw "match!", r, idc.length + 1)
          | _ => (Tok.kw "match", rest, idc.length)
        else if keywords.contains name then (Tok.kw name, rest, idc.length)
        else if c.isUpper then (Tok.ctor name, rest, idc.length)
        else (Tok.ident name, rest, idc.length)
      go rest line (col + len) (acc.push ⟨tok, line, col⟩)
    else
      let two := String.ofList ((c :: cs).take 2)
      if symbols.contains two && two.length == 2 then
        go (cs.drop 1) line (col + 2) (acc.push ⟨.sym two, line, col⟩)
      else if symbols.contains (String.singleton c) then
        go cs line (col + 1) (acc.push ⟨.sym (String.singleton c), line, col⟩)
      else .error s!"unexpected character '{c}' at line {line}, column {col}"
  ident : List Char → List Char → List Char × List Char
  | c :: cs, acc =>
    if isIdChar c then ident cs (acc ++ [c])
    else if c == '-' then
      match cs with
      | d :: _ => if d.isAlpha && !acc.isEmpty then ident cs (acc ++ [c]) else (acc, c :: cs)
      | [] => (acc, [c])
    else (acc, c :: cs)
  | [], acc => (acc, [])
  skipComment : List Char → Nat → Nat → Array Token → Except String (Array Token)
  | '*' :: '/' :: cs, line, col, acc => go cs line (col + 2) acc
  | '\n' :: cs, line, _, acc => skipComment cs (line + 1) 0 acc
  | _ :: cs, line, col, acc => skipComment cs line (col + 1) acc
  | [], _, _, _ => .error "unterminated comment"

/-! ## Parser state and layout -/

structure PState where
  toks : Array Token
  pos : Nat := 0
  /-- stack of layout block columns -/
  ctx : List Nat := []
  /-- line of the last consumed token -/
  lastLine : Nat := 0

abbrev P := StateT PState (Except String)

def rawPeek : P (Option Token) := do
  let s ← get
  return s.toks[s.pos]?

def isContKw (t : Tok) : Bool :=
  t == .kw "then" || t == .kw "elif" || t == .kw "else"

/-- The next token, if it belongs to the current item (layout-aware). -/
def peek : P (Option Token) := do
  let s ← get
  match s.toks[s.pos]? with
  | none => return none
  | some t =>
    if t.line > s.lastLine then
      let c := s.ctx.headD 0
      if t.col < c then return none
      if t.col == c && !isContKw t.tok then return none
      return some t
    else return some t

def peekTok : P (Option Tok) := return (← peek).map (·.tok)

def advance : P Token := do
  match ← peek with
  | none => throw "unexpected end of input"
  | some t =>
    modify fun s => { s with pos := s.pos + 1, lastLine := t.line }
    return t

def errAt (msg : String) : P α := do
  match ← rawPeek with
  | some t => throw s!"{msg} at line {t.line}, column {t.col} (found {repr t.tok})"
  | none => throw s!"{msg} at end of input"

def expectSym (s : String) : P Unit := do
  match ← peekTok with
  | some (.sym s') => if s == s' then discard advance else errAt s!"expected '{s}'"
  | _ => errAt s!"expected '{s}'"

def isSym (s : String) : P Bool := do
  return (← peekTok) == some (.sym s)

def isKw (s : String) : P Bool := do
  return (← peekTok) == some (.kw s)

def trySym (s : String) : P Bool := do
  if ← isSym s then discard advance; return true else return false

def ident : P String := do
  match ← peekTok with
  | some (.ident x) => discard advance; return x
  | _ => errAt "expected an identifier"

def anyName : P String := do
  match ← peekTok with
  | some (.ident x) => discard advance; return x
  | some (.ctor x) => discard advance; return x
  | _ => errAt "expected a name"

/-- Parse a comma separated list up to the closing symbol. -/
partial def sepBy (p : P α) (close : String) : P (List α) := do
  if ← trySym close then return []
  let rec loop (acc : Array α) : P (List α) := do
    let a ← p
    if ← trySym "," then loop (acc.push a)
    else expectSym close; return (acc.push a).toList
  loop #[]

/-- Parse the items of a block: either in braces separated by `;`, on the same line
    separated by `;`, or as a layout block opened on a new line. -/
partial def block (item : P α) : P (List α) := do
  let s ← get
  if ← trySym "{" then
    let saved := (← get).ctx
    modify fun s => { s with ctx := 0 :: s.ctx }
    let rec loopB (acc : Array α) : P (List α) := do
      if ← trySym "}" then return acc.toList
      if ← trySym ";" then return (← loopB acc)
      let a ← item
      loopB (acc.push a)
    let r ← loopB #[]
    modify fun s => { s with ctx := saved }
    return r
  match s.toks[s.pos]? with
  | none => errAt "expected a block"
  | some t =>
    if t.line > s.lastLine then
      if (s.ctx.head?.map (fun c => decide (t.col ≤ c))).getD false then errAt "expected an indented block"
      let saved := s.ctx
      modify fun s => { s with ctx := t.col :: s.ctx }
      let rec loopL (acc : Array α) : P (List α) := do
        let a ← item
        let acc := acc.push a
        discard <| trySym ";"
        let s ← get
        match s.toks[s.pos]? with
        | some t' =>
          if (t'.line > s.lastLine && t'.col == t.col) then
            modify fun s => { s with lastLine := t'.line }
            loopL acc
          else return acc.toList
        | none => return acc.toList
      modify fun s => { s with lastLine := t.line }
      let r ← loopL #[]
      modify fun s => { s with ctx := saved }
      return r
    else
      -- a single item on the same line
      return [← item]

/-! ## Types -/

mutual
partial def pType : P Ty := do
  let t ← pBType
  if ← trySym "->" then
    let r ← pType
    match t with
    | .tuple ts => return .fn ts r
    | _ => return .fn [t] r
  return t
partial def pBType : P Ty := do
  match ← peekTok with
  | some (.sym "(") =>
    discard advance
    let ts ← sepBy pType ")"
    match ts with
    | [t] => return t
    | _ => return .tuple ts
  | some (.sym "<") =>
    -- an effect row `<exn, div>` preceding a type
    discard advance
    discard <| sepBy anyName ">"
    pBType
  | some (.ident x) =>
    discard advance
    if ← trySym "<" then
      let args ← sepBy pType ">"
      return .con x args
    return .con x []
  | _ => errAt "expected a type"
end

/-- A result type, possibly preceded by an effect (`exn tree`, `<div> list<a>`). -/
partial def pResultType : P Ty := do
  let startLine := (← get).lastLine
  let t ← pBType
  -- if another type follows on the same line, the first was an effect
  match ← rawPeek with
  | some tk =>
    let s ← get
    if tk.line == s.lastLine && tk.line ≥ startLine then
      match tk.tok with
      | .ident _ | .sym "(" => pType
      | _ => return t
    else return t
  | none => return t

/-! ## Patterns -/

partial def pPat : P Pat := do
  match ← peekTok with
  | some (.sym "_") => discard advance; return .wild
  | some (.ident x) => discard advance; return .var x
  | some (.ctor c) =>
    discard advance
    if ← trySym "(" then
      let ps ← sepBy pPat ")"
      return .ctor c ps
    return .ctor c []
  | some (.sym "(") =>
    discard advance
    let ps ← sepBy pPat ")"
    match ps with
    | [p] => return p
    | _ => return .tuple ps
  | _ => errAt "expected a pattern"

/-! ## Expressions -/

def binop? : Tok → Option (BinOp × Nat)
  | .sym "<" => some (.lt, 4)
  | .sym "<=" => some (.le, 4)
  | .sym ">" => some (.gt, 4)
  | .sym ">=" => some (.ge, 4)
  | .sym "==" => some (.eq, 4)
  | .sym "!=" => some (.ne, 4)
  | .sym "&&" => some (.and, 3)
  | .sym "||" => some (.or, 2)
  | _ => none

mutual
/-- A block of statements `val p = e` ending in an expression. -/
partial def pBlockExpr : P Expr := do
  let items ← block pStmt
  match items.reverse with
  | [] => errAt "empty block"
  | (none, e) :: rest =>
    rest.foldlM (fun acc it => match it with
      | (some p, e1) => return Expr.valIn p e1 acc
      | (none, _) => errAt "a block may only end with an expression") e
  | (some _, _) :: _ => errAt "a block must end with an expression"

partial def pStmt : P (Option Pat × Expr) := do
  if ← isKw "val" then
    discard advance
    let p ← pPat
    expectSym "="
    let e ← pBlockExpr
    return (some p, e)
  return (none, ← pExpr)

partial def pExpr : P Expr := do
  match ← peekTok with
  | some (.kw "if") => pIf
  | some (.kw "match") => discard advance; pMatch false
  | some (.kw "match!") => discard advance; pMatch true
  | _ => pOp 0

partial def pIf : P Expr := do
  discard advance
  let c ← pExpr
  unless ← isKw "then" do errAt "expected 'then'"
  discard advance
  let t ← pBlockExpr
  if ← isKw "elif" then
    let e ← pIf
    return .ite c t e
  unless ← isKw "else" do errAt "expected 'else'"
  discard advance
  let e ← pBlockExpr
  return .ite c t e

partial def pMatch (destr : Bool) : P Expr := do
  let scrut ← pPostfix
  let clauses ← block pClause
  return .match destr scrut clauses.flatten

/-- A clause `p -> e` or `p | g₁ -> e₁ | g₂ -> e₂ ...` (one clause per alternative). -/
partial def pClause : P (List Clause) := do
  let p ← pPat
  if ← isSym "->" then
    discard advance
    return [.mk p none (← pBlockExpr)]
  let rec alts (acc : Array Clause) : P (List Clause) := do
    if ← trySym "|" then
      let g ← if ← trySym "_" then pure none else some <$> pExpr
      expectSym "->"
      let b ← pBlockExpr
      alts (acc.push (.mk p g b))
    else return acc.toList
  let cs ← alts #[]
  if cs.isEmpty then errAt "expected '->' or a guard"
  return cs

partial def pOp (minPrec : Nat) : P Expr := do
  let lhs ← pPostfix
  let rec loop (lhs : Expr) : P Expr := do
    match (← peekTok).bind binop? with
    | some (op, prec) =>
      if prec < minPrec then return lhs
      discard advance
      let rhs ← pOp (prec + 1)
      loop (.binop op lhs rhs)
    | none => return lhs
  loop lhs

partial def pPostfix : P Expr := do
  let e ← pAtom
  let rec loop (e : Expr) : P Expr := do
    if ← isSym "." then
      discard advance
      let f ← ident
      if ← isSym "(" then
        discard advance
        let args ← sepBy pExpr ")"
        loop (.app f (e :: args))
      else loop (.app f [e])
    else return e
  loop e

partial def pAtom : P Expr := do
  match ← peekTok with
  | some (.int n) => discard advance; return .lit n
  | some (.ident x) =>
    discard advance
    if ← isSym "(" then
      discard advance
      return .app x (← sepBy pExpr ")")
    return .var x
  | some (.ctor c) =>
    discard advance
    if ← isSym "(" then
      discard advance
      return .app c (← sepBy pExpr ")")
    return .app c []
  | some (.sym "(") =>
    discard advance
    let es ← sepBy pBlockExpr ")"
    match es with
    | [e] => return e
    | _ => return .tuple es
  | some (.kw "if") => pIf
  | some (.kw "match") => discard advance; pMatch false
  | some (.kw "match!") => discard advance; pMatch true
  | _ => errAt "expected an expression"
end

/-! ## Declarations -/

partial def pParam : P Param := do
  let b ← trySym "^"
  let x ← ident
  if ← trySym ":" then
    return { name := x, borrowed := b, ty := some (← pType) }
  return { name := x, borrowed := b }

partial def pCtor : P CtorDecl := do
  match ← peekTok with
  | some (.ctor c) =>
    discard advance
    if ← trySym "(" then
      let fs ← sepBy (do
        let f ← ident
        expectSym ":"
        let t ← pType
        return (f, t)) ")"
      return { name := c, fields := fs }
    return { name := c, fields := [] }
  | _ => errAt "expected a constructor"

/-- Skip the remaining tokens of the current line. -/
partial def skipLine : P Unit := do
  let s ← get
  match s.toks[s.pos]? with
  | some t => if t.line == s.lastLine then discard advance; skipLine else pure ()
  | none => pure ()

partial def pAnnot : P (Option FIP.Annot) := do
  let num : P Nat := do
    if ← trySym "(" then
      match ← peekTok with
      | some (.int n) =>
        discard advance; expectSym ")"; return n.toNat
      | _ => errAt "expected a number"
    return 0
  match ← peekTok with
  | some (.kw "fip") => discard advance; return some (.fip (← num))
  | some (.kw "fbip") => discard advance; return some (.fbip (← num))
  | _ => return none

partial def pDecl : P (Option Decl) := do
  if (← peekTok) == some (.ident "pub") then discard advance
  match ← peekTok with
  | some (.kw "import") => discard advance; skipLine; return none
  | some (.kw "alias") =>
    discard advance
    let x ← ident
    expectSym "="
    return some (.alias x (← pType))
  | some (.ident "type") | some (.ident "ref") | some (.ident "value") =>
    let kind ← match ← peekTok with
      | some (.ident "ref") => discard advance; pure TypeKind.ref
      | some (.ident "value") => discard advance; pure TypeKind.value
      | _ => pure TypeKind.normal
    unless (← peekTok) == some (.ident "type") do errAt "expected 'type'"
    discard advance
    let x ← ident
    let ps ← if ← trySym "<" then sepBy ident ">" else pure []
    let cs ← block pCtor
    return some (.type { name := x, params := ps, ctors := cs, kind := kind })
  | _ =>
    let annot ← pAnnot
    unless ← isKw "fun" do errAt "expected a declaration"
    discard advance
    let f ← ident
    expectSym "("
    let params ← sepBy pParam ")"
    let ret ← if ← trySym ":" then some <$> pResultType else pure none
    let body ← pBlockExpr
    return some (.fn { annot := annot.getD .plain, name := f, params, ret, body })

/-- Parse a whole program. -/
def parseProgram (src : String) : Except String Program := do
  -- `import` lines are ignored (they are blanked, keeping the line numbers)
  let src := "\n".intercalate <| (src.splitOn "\n").map fun l =>
    if (l.dropWhile (· == ' ')).startsWith "import " then "" else l
  let toks ← lex src
  let p : P Program := do
    let ds ← block pDecl
    if let some t ← rawPeek then
      throw s!"unexpected token {repr t.tok} at line {t.line}, column {t.col}"
    return ds.filterMap id
  let (r, _) ← p.run { toks }
  return r

end Koka
