module

public import RequestProject.Frontend.Module
public meta import RequestProject.Frontend.Module

@[expose] public section

/- ══════════════════ NOT IN PAPER START: Lean support code: the KOKA and KOKA_FIP notations that hold the paper's Koka (used by the code of sec. 1, 3, 4 and App. A) ══════════════════
   `[KOKA| ... ]` parses (`Frontend/Parse.lean`) and compiles (`Frontend/Compile.lean`) a Koka
   module into the calculus of Section 2; `[KOKA_FIP| ... ]` additionally runs the checker and,
   through `Sig.check_sound`, returns a `FipModule F C` carrying a proof that every `fip`/`fbip`
   function is well formed.  A function that is not fully in-place is a compile-time error. -/

/-!
# `[KOKA| ... ]` and `[KOKA_FIP| ... ]`

Two term elaborators that let the Koka code of the paper be written verbatim in Lean:

* `[KOKA| src ]` parses and compiles the Koka program `src` (types and functions, with
  or without `fip`/`fbip` annotations) to a `Koka.Module F C`: its type declarations and
  the core FIP signature `Σ` of its functions, indexed by the set `F` of its functions and
  the set `C` of its constructors.  Both sets are computed here, and the proofs that tie
  them to the code (exact names, distinct function names, closedness) are checked by the
  kernel; an unknown function or constructor, or a function defined twice, is reported as
  an error.
* `[KOKA_FIP| src ]` does the same, then runs the FIP checker on every annotated
  function (reporting the functions that fail) and produces a `Koka.FipModule F C`, which
  carries a proof of `⊩ Σ` (`FIP.Sig.Wf`) obtained from the checker's soundness theorem
  `FIP.Sig.check_sound` by kernel evaluation of the checker.

The indices appear in the type of the result, so a module is best declared without a
type ascription: `def m := [KOKA_FIP| … ]`.

The Koka source is taken verbatim up to the closing `]`; layout (indentation) is
significant, as in Koka, so it is best to start the program on a new line.
-/

namespace Koka

open Lean Parser Elab Term Meta

/-- The number of bytes of `cs` before the `]` that closes the quotation, where `depth`
    brackets are open and `acc` bytes have been read; `none` if the quotation is not
    closed.  Structural recursion on the input: no fuel, and it terminates. -/
meta def kokaRawLen : List Char → Nat → Nat → Option Nat
  | [], _, _ => none
  | ']' :: _, 0, acc => some acc
  | ']' :: cs, d + 1, acc => kokaRawLen cs d (acc + 1)
  | '[' :: cs, d, acc => kokaRawLen cs (d + 1) (acc + 1)
  | ch :: cs, d, acc => kokaRawLen cs d (acc + ch.utf8Size)

/-- Consume raw text up to (not including) the `]` closing the quotation, allowing
    nested brackets. -/
meta def kokaRawFn : ParserFn := fun c s =>
  let i := s.pos
  match kokaRawLen (String.Pos.Raw.extract c.inputString i c.endPos).toList 0 0 with
  | some len => s.setPos ⟨i.byteIdx + len⟩
  | none => s.mkEOIError

/-- The raw Koka source of a quotation, as a single atom. -/
meta def kokaRaw : Parser where
  fn := rawFn kokaRawFn (trailingWs := false)

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

mutual
/-- Quote a value of scope `n`. -/
meta def quoteVal (n : Nat) : FIP.Val n → Lean.Expr
  | .var x => mkApp2 (mkConst ``FIP.Val.var) (toExpr n) (quoteVar n x)
  | .fn f => mkApp2 (mkConst ``FIP.Val.fn) (toExpr n) (toExpr f)
  | .ctor c vs => mkApp3 (mkConst ``FIP.Val.ctor) (toExpr n) (toExpr c) (quoteVals n vs)
  | .lit k => mkApp2 (mkConst ``FIP.Val.lit) (toExpr n) (toExpr k)
/-- Quote a list of values of scope `n`. -/
meta def quoteVals (n : Nat) : List (FIP.Val n) → Lean.Expr
  | [] => mkApp (mkConst ``List.nil [0]) (mkApp (mkConst ``FIP.Val) (toExpr n))
  | v :: vs => mkApp3 (mkConst ``List.cons [0]) (mkApp (mkConst ``FIP.Val) (toExpr n))
      (quoteVal n v) (quoteVals n vs)
end

mutual
/-- Quote an expression of scope `n`. -/
meta def quoteExpr : (n : Nat) → FIP.Expr n → Lean.Expr
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
meta def quoteBranches : (n : Nat) → FIP.Branches n → Lean.Expr
  | n, .nil => mkApp (mkConst ``FIP.Branches.nil) (toExpr n)
  | n, .cons c xs e bs =>
    mkApp5 (mkConst ``FIP.Branches.cons) (toExpr n) (toExpr c) (toExpr xs)
      (quoteExpr (n + xs.length) e) (quoteBranches n bs)
end

/-- Quote a function definition. -/
meta def quoteFunDef (fd : FIP.FunDef) : Lean.Expr :=
  mkApp5 (mkConst ``FIP.FunDef.mk) (toExpr fd.name) (toExpr fd.borrowed) (toExpr fd.owned)
    (quoteExpr _ fd.body) (toExpr fd.annot)

/-- Quote a signature. -/
meta def quoteSig (sig : FIP.Sig) : Lean.Expr :=
  quoteList (mkConst ``FIP.FunDef) (sig.map quoteFunDef)

/-- The literal `{s₁, …, sₙ} : Finset String`. -/
meta def quoteFinset (ss : List String) : TermElabM Lean.Expr := do
  let t ← match ss.eraseDups.reverse with
    | [] => `((∅ : Finset String))
    | s :: rest =>
      rest.foldlM (fun acc x => `(insert $(Syntax.mkStrLit x) $acc))
        (← `((singleton $(Syntax.mkStrLit s) : Finset String)))
  elabTerm t (some (mkApp (mkConst ``Finset [0]) (mkConst ``String)))

/-- Apply a constructor to its remaining arguments, all of which are decidable
    propositions, proving each by `decide` (checked by the kernel). -/
meta def applyDecideProofs (f : Lean.Expr) : Nat → MetaM Lean.Expr
  | 0 => pure f
  | k + 1 => do
    let .forallE _ d _ _ ← whnf (← inferType f) | throwError "Koka: unexpected field"
    applyDecideProofs (mkApp f (← mkDecideProof d)) k

/-- Parse and compile the source of a quotation, check that the result is a closed module
    with distinct function names, and build the `Koka.Module F C` with the proofs. -/
meta def elabModule (stx : Syntax) : TermElabM (Lean.Expr × Lean.Expr × Lean.Expr × RawModule) := do
  let src := stx[1].getAtomVal
  let m ← match compileSource src with
    | .ok m => pure m
    | .error e => throwErrorAt stx "Koka: {e}"
  let names := m.sig.names
  let dups := names.filter fun f => names.count f > 1
  unless dups.isEmpty do
    throwErrorAt stx "Koka: functions defined more than once: {dups.eraseDups}"
  let ctors := ctorNames m.types
  let fS : Finset String := names.toFinset
  let cS : Finset String := ctors.toFinset
  let bad := (FIP.Sig.refs m.sig).filter fun r => !r.valid fS cS m.sig m.types
  unless bad.isEmpty do
    let showRef : FIP.Ref → String := fun
      | .fn f | .call f none => if names.contains f then s!"function '{f}'" else
          s!"unknown function '{f}'"
      | .call f (some (b, o)) => if names.contains f then
          s!"call of '{f}' with {b} borrowed and {o} owned arguments"
        else s!"unknown function '{f}'"
      | .ctor c k => if ctors.contains c then s!"constructor '{c}' with {k} fields"
        else s!"unknown constructor '{c}'"
    throwErrorAt stx "Koka: invalid references: {bad.eraseDups.map showRef}"
  let fE ← quoteFinset names
  let cE ← quoteFinset ctors
  let sigE := quoteSig m.sig
  let mk := mkAppN (mkConst ``Module.mk) #[fE, cE, toExpr m.types, sigE]
  return (fE, cE, ← applyDecideProofs mk 4, m)

@[term_elab kokaQuot]
meta def elabKoka : TermElab := fun stx _ => do
  let (_, _, mE, _) ← elabModule stx
  return mE

@[term_elab kokaFipQuot]
meta def elabKokaFip : TermElab := fun stx _ => do
  let (fE, cE, mE, m) ← elabModule stx
  let bad := m.sig.filter fun fd => !(fd.annot == .plain || fd.check m.sig)
  unless bad.isEmpty do
    throwErrorAt stx "Koka: the FIP check fails for {bad.map (·.name)}"
  let sigE := quoteSig m.sig
  let checkE := mkApp (mkConst ``FIP.Sig.check) sigE
  let eqT ← mkEq checkE (mkConst ``Bool.true)
  let h ← mkExpectedTypeHint (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)) eqT
  let wf := mkApp2 (mkConst ``FIP.Sig.check_sound) sigE h
  return mkApp4 (mkConst ``FipModule.mk) fE cE mE wf

end Koka

/- ══════════════════ NOT IN PAPER END: Lean support code: the KOKA and KOKA_FIP notations that hold the paper's Koka ══════════════════ -/
