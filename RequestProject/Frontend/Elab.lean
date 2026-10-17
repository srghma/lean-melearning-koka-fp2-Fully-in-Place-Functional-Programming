module

public import RequestProject.Frontend.Compile
public import RequestProject.Sec2_Calculus.CheckSound
public meta import RequestProject.Frontend.Compile
public meta import RequestProject.Sec2_Calculus.CheckSound

@[expose] public section

/- ══════════════════ NOT IN PAPER START: Lean support code: the KOKA and KOKA_FIP notations that hold the paper's Koka (used by the code of sec. 1, 3, 4 and App. A) ══════════════════
   `[KOKA| ... ]` parses (`Frontend/Parse.lean`) and compiles (`Frontend/Compile.lean`) a Koka
   module into the calculus of Section 2; `[KOKA_FIP| ... ]` additionally runs the checker and,
   through `Sig.check_sound`, returns a `FipModule` carrying a proof that every `fip`/`fbip`
   function is well formed.  A function that is not fully in-place is a compile-time error. -/

/-!
# `[KOKA| ... ]` and `[KOKA_FIP| ... ]`

Two term elaborators that let the Koka code of the paper be written verbatim in Lean:

* `[KOKA| src ]` parses and compiles the Koka program `src` (types and functions, with
  or without `fip`/`fbip` annotations) to a `Koka.Module`: its type declarations and the
  core FIP signature `Σ` of its functions.
* `[KOKA_FIP| src ]` does the same, then runs the FIP checker on every annotated
  function (reporting the functions that fail) and produces a `Koka.FipModule`, which
  carries a proof of `⊩ Σ` (`FIP.Sig.Wf`) obtained from the checker's soundness theorem
  `FIP.Sig.check_sound` by kernel evaluation of the checker.

The Koka source is taken verbatim up to the closing `]`; layout (indentation) is
significant, as in Koka, so it is best to start the program on a new line.
-/

namespace Koka

/-- A Koka module whose annotated functions are proved fully in-place (`fip`) or
    functional but in-place (`fbip`): `⊩ Σ`. -/
structure FipModule extends Module where
  wf : sig.Wf

open Lean Parser Elab Term Meta

/-- Consume raw text up to (not including) the `]` closing the quotation, allowing
    nested brackets. -/
meta partial def kokaRawFn (depth : Nat := 0) : ParserFn := fun c s =>
  let i := s.pos
  if h : c.atEnd i then s.mkEOIError
  else
    let ch := c.get' i h
    if ch == ']' then
      if depth == 0 then s else kokaRawFn (depth - 1) c (s.next' c i h)
    else if ch == '[' then kokaRawFn (depth + 1) c (s.next' c i h)
    else kokaRawFn depth c (s.next' c i h)

/-- The raw Koka source of a quotation, as a single atom. -/
meta def kokaRaw : Parser where
  fn := rawFn (kokaRawFn 0) (trailingWs := false)

@[combinator_formatter kokaRaw]
meta def kokaRaw.formatter : PrettyPrinter.Formatter :=
  PrettyPrinter.Formatter.visitAtom Name.anonymous

@[combinator_parenthesizer kokaRaw]
meta def kokaRaw.parenthesizer : PrettyPrinter.Parenthesizer :=
  PrettyPrinter.Parenthesizer.visitToken

/-- `[KOKA| src ]`: a compiled Koka module. -/
syntax (name := kokaQuot) "[KOKA|" kokaRaw "]" : term

/-- `[KOKA_FIP| src ]`: a compiled Koka module with a proof that its annotated functions
    are fully in-place. -/
syntax (name := kokaFipQuot) "[KOKA_FIP|" kokaRaw "]" : term

/-! ## Quoting compiled modules

A compiled module is turned into a Lean term by hand: the terms of the calculus are
indexed by their scope, so each node is built at its (literal) scope, and a de Bruijn
index `i : Fin n` is `⟨i, of_decide_eq_true rfl⟩`. -/

/-- The term `⟨i, _⟩ : Fin n`. -/
meta def quoteFin (n i : Nat) : Lean.Expr :=
  let prop := mkApp4 (mkConst ``LT.lt [0]) (mkConst ``Nat) (mkConst ``instLTNat) (toExpr i)
    (toExpr n)
  let inst := mkApp2 (mkConst ``Nat.decLt) (toExpr i) (toExpr n)
  let pf := mkApp3 (mkConst ``of_decide_eq_true) prop inst
    (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true))
  mkApp3 (mkConst ``Fin.mk) (toExpr n) (toExpr i) pf

/-- A list literal of the given element type. -/
meta def quoteList (ty : Lean.Expr) : List Lean.Expr → Lean.Expr
  | [] => mkApp (mkConst ``List.nil [0]) ty
  | x :: xs => mkApp3 (mkConst ``List.cons [0]) ty x (quoteList ty xs)

/-- Quote a variable of scope `n`. -/
meta def quoteVar (n : Nat) : FIP.Var n → Lean.Expr
  | .bvar i => mkApp2 (mkConst ``FIP.Var.bvar) (toExpr n) (quoteFin n i.val)
  | .loc l => mkApp2 (mkConst ``FIP.Var.loc) (toExpr n) (toExpr l)

/-- Quote a value of scope `n`. -/
meta partial def quoteVal (n : Nat) : FIP.Val n → Lean.Expr
  | .var x => mkApp2 (mkConst ``FIP.Val.var) (toExpr n) (quoteVar n x)
  | .fn f => mkApp2 (mkConst ``FIP.Val.fn) (toExpr n) (toExpr f)
  | .ctor c vs => mkApp3 (mkConst ``FIP.Val.ctor) (toExpr n) (toExpr c)
      (quoteList (mkApp (mkConst ``FIP.Val) (toExpr n)) (vs.map (quoteVal n)))
  | .lit k => mkApp2 (mkConst ``FIP.Val.lit) (toExpr n) (toExpr k)

/-- Quote a list of values of scope `n`. -/
meta def quoteVals (n : Nat) (vs : List (FIP.Val n)) : Lean.Expr :=
  quoteList (mkApp (mkConst ``FIP.Val) (toExpr n)) (vs.map (quoteVal n))

mutual
/-- Quote an expression of scope `n`. -/
meta partial def quoteExpr : (n : Nat) → FIP.Expr n → Lean.Expr
  | n, .ret vs => mkApp2 (mkConst ``FIP.Expr.ret) (toExpr n) (quoteVals n vs)
  | n, .app e1 e2 => mkApp3 (mkConst ``FIP.Expr.app) (toExpr n) (quoteExpr n e1) (quoteExpr n e2)
  | n, .call f e1 e2 =>
    mkApp4 (mkConst ``FIP.Expr.call) (toExpr n) (toExpr f) (quoteExpr n e1) (quoteExpr n e2)
  | n, .letIn xs e1 e2 =>
    mkApp4 (mkConst ``FIP.Expr.letIn) (toExpr n) (toExpr xs) (quoteExpr n e1)
      (quoteExpr (n + xs.length) e2)
  | n, .bmatch e bs =>
    mkApp3 (mkConst ``FIP.Expr.bmatch) (toExpr n) (quoteExpr n e) (quoteBranches n bs)
  | n, .dmatch e bs =>
    mkApp3 (mkConst ``FIP.Expr.dmatch) (toExpr n) (quoteExpr n e) (quoteBranches n bs)
  | n, .drop x e => mkApp3 (mkConst ``FIP.Expr.drop) (toExpr n) (quoteVal n x) (quoteExpr n e)
  | n, .free k e => mkApp3 (mkConst ``FIP.Expr.free) (toExpr n) (toExpr k) (quoteExpr n e)
  | n, .prim op vs => mkApp3 (mkConst ``FIP.Expr.prim) (toExpr n) (toExpr op) (quoteVals n vs)
/-- Quote the branches of a match of scope `n`. -/
meta partial def quoteBranches : (n : Nat) → FIP.Branches n → Lean.Expr
  | n, .nil => mkApp (mkConst ``FIP.Branches.nil) (toExpr n)
  | n, .cons c xs e bs =>
    mkApp5 (mkConst ``FIP.Branches.cons) (toExpr n) (toExpr c) (toExpr xs)
      (quoteExpr (n + xs.length) e) (quoteBranches n bs)
end

/-- Quote a function definition. -/
meta def quoteFunDef (fd : FIP.FunDef) : Lean.Expr :=
  mkApp5 (mkConst ``FIP.FunDef.mk) (toExpr fd.name) (toExpr fd.borrowed) (toExpr fd.owned)
    (quoteExpr _ fd.body) (toExpr fd.annot)

/-- Quote a compiled module. -/
meta def quoteModule (m : Module) : Lean.Expr :=
  mkApp2 (mkConst ``Module.mk) (toExpr m.types)
    (quoteList (mkConst ``FIP.FunDef) (m.sig.map quoteFunDef))

/-- Parse and compile the source of a quotation. -/
meta def compileQuot (stx : Syntax) : TermElabM Module := do
  let src := stx[1].getAtomVal
  match compileSource src with
  | .ok m => return m
  | .error e => throwErrorAt stx "Koka: {e}"

@[term_elab kokaQuot]
meta def elabKoka : TermElab := fun stx _ => do
  let m ← compileQuot stx
  return quoteModule m

@[term_elab kokaFipQuot]
meta def elabKokaFip : TermElab := fun stx _ => do
  let m ← compileQuot stx
  let bad := m.sig.filter fun fd => !(fd.annot == .plain || fd.check m.sig)
  unless bad.isEmpty do
    throwErrorAt stx "Koka: the FIP check fails for {bad.map (·.name)}"
  let mE := quoteModule m
  let sigE := mkApp (mkConst ``Module.sig) mE
  let checkE := mkApp (mkConst ``FIP.Sig.check) sigE
  let eqT ← mkEq checkE (mkConst ``Bool.true)
  let h ← mkExpectedTypeHint (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)) eqT
  let wf := mkApp2 (mkConst ``FIP.Sig.check_sound) sigE h
  return mkApp2 (mkConst ``FipModule.mk) mE wf

end Koka

/- ══════════════════ NOT IN PAPER END: Lean support code: the KOKA and KOKA_FIP notations that hold the paper's Koka ══════════════════ -/
