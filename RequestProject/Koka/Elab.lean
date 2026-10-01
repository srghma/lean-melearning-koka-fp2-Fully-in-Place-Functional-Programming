module

public import RequestProject.Koka.Compile
public import RequestProject.FIP.CheckSound
public meta import RequestProject.Koka.Compile
public meta import RequestProject.FIP.CheckSound

@[expose] public section

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

/-- Parse and compile the source of a quotation. -/
meta def compileQuot (stx : Syntax) : TermElabM Module := do
  let src := stx[1].getAtomVal
  match compileSource src with
  | .ok m => return m
  | .error e => throwErrorAt stx "Koka: {e}"

@[term_elab kokaQuot]
meta def elabKoka : TermElab := fun stx _ => do
  let m ← compileQuot stx
  return toExpr m

@[term_elab kokaFipQuot]
meta def elabKokaFip : TermElab := fun stx _ => do
  let m ← compileQuot stx
  let bad := m.sig.filter fun fd => !(fd.annot == .plain || fd.check m.sig)
  unless bad.isEmpty do
    throwErrorAt stx "Koka: the FIP check fails for {bad.map (·.name)}"
  let mE := toExpr m
  let sigE := mkApp (mkConst ``Module.sig) mE
  let checkE := mkApp (mkConst ``FIP.Sig.check) sigE
  let eqT ← mkEq checkE (mkConst ``Bool.true)
  let h ← mkExpectedTypeHint (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)) eqT
  let wf := mkApp2 (mkConst ``FIP.Sig.check_sound) sigE h
  return mkApp2 (mkConst ``FipModule.mk) mE wf

end Koka
