module

public import RequestProject.Frontend.Ast

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

/-- Read an identifier (letters, digits, `_`, primes, and dashes followed by a letter):
    the characters read so far (`acc`) and the rest of the input. -/
def lexIdent : List Char → List Char → List Char × List Char
  | c :: cs, acc =>
    if isIdChar c then lexIdent cs (acc ++ [c])
    else if c == '-' then
      match cs with
      | d :: _ => if d.isAlpha && !acc.isEmpty then lexIdent cs (acc ++ [c]) else (acc, c :: cs)
      | [] => (acc, [c])
    else (acc, c :: cs)
  | [], acc => (acc, [])

/-- The error reported if a recursive call would not make progress.  Termination of the
    lexer, the parser and the compiler is proved by well-founded recursion on a measure of
    the input; where the measure of the argument of a recursive call is only known at run
    time, it is checked, and this error is reported instead of looping.  It is never
    reported for the code of the paper. -/
def noProgress {m : Type → Type} [MonadExcept String m] {α : Type} (what : String) : m α :=
  throw s!"Koka {what}: no progress (internal error)"

mutual
/-- Split a list of characters into tokens (line `line`, column `col`). -/
def lexGo (l : List Char) (line col : Nat) (acc : Array Token) : Except String (Array Token) :=
  match l with
  | [] => .ok acc
  | '\n' :: cs => lexGo cs (line + 1) 0 acc
  | '/' :: '/' :: cs =>
    lexGo (cs.dropWhile (· != '\n')) line col acc
  | '/' :: '*' :: cs => lexSkipComment cs line (col + 2) acc
  | c :: cs =>
    if c == ' ' || c == '\t' || c == '\r' then lexGo cs line (col + 1) acc
    else if c.isDigit then
      let ds := cs.takeWhile Char.isDigit
      lexGo (cs.dropWhile Char.isDigit) line (col + ds.length + 1)
        (acc.push ⟨.int (String.ofList (c :: ds)).toNat!, line, col⟩)
    else if isIdStart c then
      let (idc, rest) := lexIdent (c :: cs) []
      let name := String.ofList idc
      let (tok, rest, len) :=
        if name == "match" then
          match rest with
          | '!' :: r => (Tok.kw "match!", r, idc.length + 1)
          | _ => (Tok.kw "match", rest, idc.length)
        else if keywords.contains name then (Tok.kw name, rest, idc.length)
        else if c.isUpper then (Tok.ctor name, rest, idc.length)
        else (Tok.ident name, rest, idc.length)
      if rest.length ≤ cs.length then lexGo rest line (col + len) (acc.push ⟨tok, line, col⟩)
      else noProgress "lexer"
    else
      let two := String.ofList ((c :: cs).take 2)
      if symbols.contains two && two.length == 2 then
        lexGo (cs.drop 1) line (col + 2) (acc.push ⟨.sym two, line, col⟩)
      else if symbols.contains (String.singleton c) then
        lexGo cs line (col + 1) (acc.push ⟨.sym (String.singleton c), line, col⟩)
      else .error s!"unexpected character '{c}' at line {line}, column {col}"
termination_by l.length
decreasing_by all_goals (simp_wf <;> first | omega | (have := List.length_dropWhile_le (p := (· != '\n')) cs; omega) | (have := List.length_dropWhile_le (p := Char.isDigit) cs; omega))
/-- Skip a `/* … */` comment. -/
def lexSkipComment (l : List Char) (line col : Nat) (acc : Array Token) :
    Except String (Array Token) :=
  match l with
  | '*' :: '/' :: cs => lexGo cs line (col + 2) acc
  | '\n' :: cs => lexSkipComment cs (line + 1) 0 acc
  | _ :: cs => lexSkipComment cs line (col + 1) acc
  | [] => .error "unterminated comment"
termination_by l.length
end

/-- Split a string into tokens. -/
def lex (s : String) : Except String (Array Token) := lexGo s.toList 1 0 #[]

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

/-! ## Termination of the parser

The parser is a recursive-descent parser, so its functions call each other on the same
input (an expression starts with an operand, an operand with an atom, …) as well as on
the rest of the input.  Every recursive function therefore takes, as its first argument,
the number `n` of tokens that were left when it was called, and recursion is
well-founded on the pair `(n, level)`, where `level` is the position of the function in
the grammar: a call on the same input goes to a function of a lower level, and any other
call is made on fewer tokens.  The number of tokens left after a sub-parser has run is
read from the state and checked (`remaining`, `noProgress`), so no fuel is involved. -/

/-- The number of tokens that have not been consumed. -/
def remaining : P Nat := do
  let s ← get
  return s.toks.size - s.pos

/-- A lexicographic decrease whose first component does not increase. -/
theorem lex_lt_of_le {β : Type} {r : β → β → Prop} {a b : Nat} {x y : β} (h₁ : a ≤ b)
    (h₂ : r x y) : Prod.Lex (· < ·) r (a, x) (b, y) := by
  rcases Nat.lt_or_eq_of_le h₁ with h | rfl
  · exact Prod.Lex.left _ _ h
  · exact Prod.Lex.right _ h₂

/-- Discharge the termination goals of the parser: either fewer tokens are left, or as
    many and the callee is lower in the grammar. -/
macro "koka_decreasing" : tactic =>
  `(tactic| all_goals (simp_wf <;> first
      | omega
      | (apply Prod.Lex.left; omega)
      | (apply lex_lt_of_le <;> omega)))

/-- Parse a comma separated list up to the closing symbol, with the items parsed by `p`,
    which is called when at most `n` tokens are left. -/
def sepBy (n : Nat) (p : (m : Nat) → m ≤ n → P α) (close : String) : P (List α) := do
  if ← trySym close then return []
  loop n (Nat.le_refl n) #[]
where
  loop (m : Nat) (hm : m ≤ n) (acc : Array α) : P (List α) := do
    let r ← remaining
    if h : r ≤ m then
      let a ← p r (Nat.le_trans h hm)
      if ← trySym "," then
        let r' ← remaining
        if h' : r' < m then loop r' (by omega) (acc.push a) else noProgress "parser"
      else expectSym close; return (acc.push a).toList
    else noProgress "parser"
  termination_by m

/-- `sepBy` for an item parser that does not take part in a recursion. -/
def sepBy' (p : P α) (close : String) : P (List α) := do
  sepBy (← remaining) (fun _ _ => p) close

/-- Parse the items of a block: either in braces separated by `;`, on the same line
    separated by `;`, or as a layout block opened on a new line.  The items are parsed
    by `item`, which is called when at most `n` tokens are left. -/
def block (n : Nat) (item : (m : Nat) → m ≤ n → P α) : P (List α) := do
  let s ← get
  if ← trySym "{" then
    let saved := (← get).ctx
    modify fun s => { s with ctx := 0 :: s.ctx }
    let r ← loopB n (Nat.le_refl n) #[]
    modify fun s => { s with ctx := saved }
    return r
  match s.toks[s.pos]? with
  | none => errAt "expected a block"
  | some t =>
    if t.line > s.lastLine then
      if (s.ctx.head?.map (fun c => decide (t.col ≤ c))).getD false then
        errAt "expected an indented block"
      let saved := s.ctx
      modify fun s => { s with ctx := t.col :: s.ctx }
      modify fun s => { s with lastLine := t.line }
      let r ← loopL t.col n (Nat.le_refl n) #[]
      modify fun s => { s with ctx := saved }
      return r
    else
      -- a single item on the same line
      let r ← remaining
      if h : r ≤ n then return [← item r h] else noProgress "parser"
where
  /-- The items of a block in braces. -/
  loopB (m : Nat) (hm : m ≤ n) (acc : Array α) : P (List α) := do
    if ← trySym "}" then return acc.toList
    if ← trySym ";" then
      let r ← remaining
      if h : r < m then return (← loopB r (by omega) acc) else noProgress "parser"
    let r ← remaining
    if h : r ≤ m then
      let a ← item r (Nat.le_trans h hm)
      let r' ← remaining
      if h' : r' < m then loopB r' (by omega) (acc.push a) else noProgress "parser"
    else noProgress "parser"
  termination_by m
  /-- The items of a layout block at column `col`. -/
  loopL (col : Nat) (m : Nat) (hm : m ≤ n) (acc : Array α) : P (List α) := do
    let r ← remaining
    if h : r ≤ m then
      let a ← item r (Nat.le_trans h hm)
      let acc := acc.push a
      discard <| trySym ";"
      let s ← get
      match s.toks[s.pos]? with
      | some t' =>
        if (t'.line > s.lastLine && t'.col == col) then
          modify fun s => { s with lastLine := t'.line }
          let r' ← remaining
          if h' : r' < m then loopL col r' (by omega) acc else noProgress "parser"
        else return acc.toList
      | none => return acc.toList
    else noProgress "parser"
  termination_by m

/-! ## Types -/

mutual
/-- A type, possibly a function type `τ -> τ'`. -/
def pType (n : Nat) : P Ty := do
  let t ← pBType n
  if ← trySym "->" then
    let r ← remaining
    if r < n then
      let res ← pType r
      match t with
      | .tuple ts => return .fn ts res
      | _ => return .fn [t] res
    else noProgress "parser"
  else return t
termination_by (n, 1)
decreasing_by koka_decreasing
/-- A type that is not a function type. -/
def pBType (n : Nat) : P Ty := do
  match ← peekTok with
  | some (.sym "(") =>
    discard advance
    let r ← remaining
    if r < n then
      let ts ← sepBy r (fun m _ => pType m) ")"
      match ts with
      | [t] => return t
      | _ => return .tuple ts
    else noProgress "parser"
  | some (.sym "<") =>
    -- an effect row `<exn, div>` preceding a type
    discard advance
    discard <| sepBy' anyName ">"
    let r ← remaining
    if r < n then pBType r else noProgress "parser"
  | some (.ident x) =>
    discard advance
    if ← trySym "<" then
      let r ← remaining
      if r < n then
        let args ← sepBy r (fun m _ => pType m) ">"
        return .con x args
      else noProgress "parser"
    else return .con x []
  | _ => errAt "expected a type"
termination_by (n, 0)
decreasing_by koka_decreasing
end

/-- A type (not part of a recursion). -/
def pType' : P Ty := do pType (← remaining)

/-- A result type, possibly preceded by an effect (`exn tree`, `<div> list<a>`). -/
def pResultType : P Ty := do
  let startLine := (← get).lastLine
  let t ← pBType (← remaining)
  -- if another type follows on the same line, the first was an effect
  match ← rawPeek with
  | some tk =>
    let s ← get
    if tk.line == s.lastLine && tk.line ≥ startLine then
      match tk.tok with
      | .ident _ | .sym "(" => pType'
      | _ => return t
    else return t
  | none => return t

/-! ## Patterns -/

/-- A pattern. -/
def pPat (n : Nat) : P Pat := do
  match ← peekTok with
  | some (.sym "_") => discard advance; return .wild
  | some (.ident x) => discard advance; return .var x
  | some (.ctor c) =>
    discard advance
    if ← trySym "(" then
      let r ← remaining
      if r < n then return .ctor c (← sepBy r (fun m _ => pPat m) ")")
      else noProgress "parser"
    else return .ctor c []
  | some (.sym "(") =>
    discard advance
    let r ← remaining
    if r < n then
      let ps ← sepBy r (fun m _ => pPat m) ")"
      match ps with
      | [p] => return p
      | _ => return .tuple ps
    else noProgress "parser"
  | _ => errAt "expected a pattern"
termination_by n
decreasing_by all_goals omega

/-- A pattern (not part of a recursion). -/
def pPat' : P Pat := do pPat (← remaining)

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

/-- Turn the statements of a block into nested `val` bindings. -/
def blockToExpr (items : List (Option Pat × Expr)) : P Expr :=
  match items.reverse with
  | [] => errAt "empty block"
  | (none, e) :: rest =>
    rest.foldlM (fun acc it => match it with
      | (some p, e1) => return Expr.valIn p e1 acc
      | (none, _) => errAt "a block may only end with an expression") e
  | (some _, _) :: _ => errAt "a block must end with an expression"

mutual
/-- A block of statements `val p = e` ending in an expression. -/
def pBlockExpr (n : Nat) : P Expr := do
  blockToExpr (← block n (fun m _ => pStmt m))
termination_by (n, 6)
decreasing_by koka_decreasing

/-- A statement: `val p = e` or an expression. -/
def pStmt (n : Nat) : P (Option Pat × Expr) := do
  if ← isKw "val" then
    discard advance
    let p ← pPat'
    expectSym "="
    let r ← remaining
    if r < n then return (some p, ← pBlockExpr r) else noProgress "parser"
  else return (none, ← pExpr n)
termination_by (n, 5)
decreasing_by koka_decreasing

/-- An expression. -/
def pExpr (n : Nat) : P Expr := do
  match ← peekTok with
  | some (.kw "if") | some (.kw "match") | some (.kw "match!") => pAtom n
  | _ => pOp n 0
termination_by (n, 4)
decreasing_by koka_decreasing

/-- `if c then e₁ elif … else e₂`. -/
def pIf (n : Nat) : P Expr := do
  discard advance
  let r ← remaining
  if r < n then
    let c ← pExpr r
    unless ← isKw "then" do errAt "expected 'then'"
    discard advance
    let r ← remaining
    if r < n then
      let t ← pBlockExpr r
      if ← isKw "elif" then
        let r ← remaining
        if r < n then return .ite c t (← pIf r) else noProgress "parser"
      else
        unless ← isKw "else" do errAt "expected 'else'"
        discard advance
        let r ← remaining
        if r < n then return .ite c t (← pBlockExpr r) else noProgress "parser"
    else noProgress "parser"
  else noProgress "parser"
termination_by (n, 0)
decreasing_by koka_decreasing

/-- The scrutinee and the clauses of a `match` (after the keyword). -/
def pMatch (n : Nat) (destr : Bool) : P Expr := do
  let scrut ← pPostfix n
  let r ← remaining
  if r ≤ n then
    let clauses ← block r (fun m _ => pClause m)
    return .match destr scrut clauses.flatten
  else noProgress "parser"
termination_by (n, 3)
decreasing_by koka_decreasing

/-- A clause `p -> e` or `p | g₁ -> e₁ | g₂ -> e₂ ...` (one clause per alternative). -/
def pClause (n : Nat) : P (List Clause) := do
  let p ← pPat'
  if ← isSym "->" then
    discard advance
    let r ← remaining
    if r < n then return [.mk p none (← pBlockExpr r)] else noProgress "parser"
  else
    let r ← remaining
    if r < n then
      let cs ← pAlts r p #[]
      if cs.isEmpty then errAt "expected '->' or a guard"
      return cs
    else noProgress "parser"
termination_by (n, 0)
decreasing_by koka_decreasing

/-- The guarded alternatives `| g -> e` of a clause with pattern `p`. -/
def pAlts (n : Nat) (p : Pat) (acc : Array Clause) : P (List Clause) := do
  if ← trySym "|" then
    let g ← if ← trySym "_" then pure none else
      let r ← remaining
      if r < n then some <$> pExpr r else noProgress "parser"
    expectSym "->"
    let r ← remaining
    if r < n then
      let b ← pBlockExpr r
      let r ← remaining
      if r < n then pAlts r p (acc.push (.mk p g b)) else noProgress "parser"
    else noProgress "parser"
  else return acc.toList
termination_by (n, 0)
decreasing_by koka_decreasing

/-- Binary operators of precedence at least `minPrec`. -/
def pOp (n : Nat) (minPrec : Nat) : P Expr := do
  let lhs ← pPostfix n
  let r ← remaining
  if r < n then pOpLoop r minPrec lhs else noProgress "parser"
termination_by (n, 3)
decreasing_by koka_decreasing

/-- The operators following the left operand `lhs`. -/
def pOpLoop (n : Nat) (minPrec : Nat) (lhs : Expr) : P Expr := do
  match (← peekTok).bind binop? with
  | some (op, prec) =>
    if prec < minPrec then return lhs
    discard advance
    let r ← remaining
    if h : r < n then
      let rhs ← pOp r (prec + 1)
      let r ← remaining
      if r < n then pOpLoop r minPrec (.binop op lhs rhs) else noProgress "parser"
    else noProgress "parser"
  | none => return lhs
termination_by (n, 3)
decreasing_by koka_decreasing

/-- An atom followed by method calls `.f(args)`. -/
def pPostfix (n : Nat) : P Expr := do
  let e ← pAtom n
  let r ← remaining
  if r < n then pPostfixLoop r e else noProgress "parser"
termination_by (n, 2)
decreasing_by koka_decreasing

/-- The method calls following `e`. -/
def pPostfixLoop (n : Nat) (e : Expr) : P Expr := do
  if ← isSym "." then
    discard advance
    let f ← ident
    let args ← if ← isSym "(" then
        discard advance
        let r ← remaining
        if r < n then sepBy r (fun m _ => pExpr m) ")" else noProgress "parser"
      else pure []
    let r ← remaining
    if r < n then pPostfixLoop r (.app f (e :: args)) else noProgress "parser"
  else return e
termination_by (n, 2)
decreasing_by koka_decreasing

/-- An atom: a literal, a variable, an application, a tuple, an `if` or a `match`. -/
def pAtom (n : Nat) : P Expr := do
  match ← peekTok with
  | some (.int k) => discard advance; return .lit k
  | some (.ident x) | some (.ctor x) =>
    let isCtor := match ← peekTok with | some (.ctor _) => true | _ => false
    discard advance
    if ← isSym "(" then
      discard advance
      let r ← remaining
      if r < n then return .app x (← sepBy r (fun m _ => pExpr m) ")")
      else noProgress "parser"
    else return if isCtor then .app x [] else .var x
  | some (.sym "(") =>
    discard advance
    let r ← remaining
    if r < n then
      let es ← sepBy r (fun m _ => pBlockExpr m) ")"
      match es with
      | [e] => return e
      | _ => return .tuple es
    else noProgress "parser"
  | some (.kw "if") => pIf n
  | some (.kw "match") | some (.kw "match!") =>
    let destr := (← peekTok) == some (.kw "match!")
    discard advance
    let r ← remaining
    if r < n then pMatch r destr else noProgress "parser"
  | _ => errAt "expected an expression"
termination_by (n, 1)
decreasing_by koka_decreasing
end

/-! ## Declarations -/

def pParam : P Param := do
  let b ← trySym "^"
  let x ← ident
  if ← trySym ":" then
    return { name := x, borrowed := b, ty := some (← pType') }
  return { name := x, borrowed := b }

def pCtor : P CtorDecl := do
  match ← peekTok with
  | some (.ctor c) =>
    discard advance
    if ← trySym "(" then
      let fs ← sepBy' (do
        let f ← ident
        expectSym ":"
        let t ← pType'
        return (f, t)) ")"
      return { name := c, fields := fs }
    return { name := c, fields := [] }
  | _ => errAt "expected a constructor"

/-- Skip the remaining tokens of the current line. -/
def skipLine (n : Nat) : P Unit := do
  let s ← get
  match s.toks[s.pos]? with
  | some t =>
    if t.line == s.lastLine then
      discard advance
      let r ← remaining
      if r < n then skipLine r else noProgress "parser"
    else pure ()
  | none => pure ()
termination_by n

def pAnnot : P (Option FIP.Annot) := do
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

def pDecl : P (Option Decl) := do
  if (← peekTok) == some (.ident "pub") then discard advance
  match ← peekTok with
  | some (.kw "import") => discard advance; skipLine (← remaining); return none
  | some (.kw "alias") =>
    discard advance
    let x ← ident
    expectSym "="
    return some (.alias x (← pType'))
  | some (.ident "type") | some (.ident "ref") | some (.ident "value") =>
    let kind ← match ← peekTok with
      | some (.ident "ref") => discard advance; pure TypeKind.ref
      | some (.ident "value") => discard advance; pure TypeKind.value
      | _ => pure TypeKind.normal
    unless (← peekTok) == some (.ident "type") do errAt "expected 'type'"
    discard advance
    let x ← ident
    let ps ← if ← trySym "<" then sepBy' ident ">" else pure []
    let cs ← block (← remaining) (fun _ _ => pCtor)
    return some (.type { name := x, params := ps, ctors := cs, kind := kind })
  | _ =>
    let annot ← pAnnot
    unless ← isKw "fun" do errAt "expected a declaration"
    discard advance
    let f ← ident
    expectSym "("
    let params ← sepBy' pParam ")"
    let ret ← if ← trySym ":" then some <$> pResultType else pure none
    let body ← pBlockExpr (← remaining)
    return some (.fn { annot := annot.getD .plain, name := f, params, ret, body })

/-- Parse a whole program. -/
def parseProgram (src : String) : Except String Program := do
  -- `import` lines are ignored (they are blanked, keeping the line numbers)
  let src := "\n".intercalate <| (src.splitOn "\n").map fun l =>
    if (l.dropWhile (· == ' ')).startsWith "import " then "" else l
  let toks ← lex src
  let p : P Program := do
    let ds ← block (← remaining) (fun _ _ => pDecl)
    if let some t ← rawPeek then
      throw s!"unexpected token {repr t.tok} at line {t.line}, column {t.col}"
    return ds.filterMap id
  let (r, _) ← p.run { toks }
  return r

end Koka
