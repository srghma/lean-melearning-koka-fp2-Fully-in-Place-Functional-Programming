module

public import RequestProject.Named.Frontend.Compile
public import RequestProject.Named.Sec2_Calculus.CheckSound
public meta import RequestProject.Named.Frontend.Compile
public meta import RequestProject.Named.Sec2_Calculus.CheckSound

@[expose] public section

/-!
# `[NKOKA| ... ]` and `[NKOKA_FIP| ... ]`

Two term elaborators that let the KokaNamed code of the paper be written verbatim in Lean:

* `[NKOKA| src ]` parses and compiles the KokaNamed program `src` (types and functions, with
  or without `fip`/`fbip` annotations) to a `KokaNamed.Module`: its type declarations and the
  core FIPNamed signature `Σ` of its functions.
* `[NKOKA_FIP| src ]` does the same, then runs the FIPNamed checker on every annotated
  function (reporting the functions that fail) and produces a `KokaNamed.FipModule`, which
  carries a proof of `⊩ Σ` (`FIPNamed.Sig.Wf`) obtained from the checker's soundness theorem
  `FIPNamed.Sig.check_sound` by kernel evaluation of the checker.

The KokaNamed source is taken verbatim up to the closing `]`; layout (indentation) is
significant, as in KokaNamed, so it is best to start the program on a new line.
-/

namespace KokaNamed

/-- A KokaNamed module whose annotated functions are proved fully in-place (`fip`) or
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

/-- The raw KokaNamed source of a quotation, as a single atom. -/
meta def kokaRaw : Parser where
  fn := rawFn (kokaRawFn 0) (trailingWs := false)

@[combinator_formatter kokaRaw]
meta def kokaRaw.formatter : PrettyPrinter.Formatter :=
  PrettyPrinter.Formatter.visitAtom Name.anonymous

@[combinator_parenthesizer kokaRaw]
meta def kokaRaw.parenthesizer : PrettyPrinter.Parenthesizer :=
  PrettyPrinter.Parenthesizer.visitToken

/-- `[NKOKA| src ]`: a compiled KokaNamed module. -/
syntax (name := kokaQuot) "[NKOKA|" kokaRaw "]" : term

/-- `[NKOKA_FIP| src ]`: a compiled KokaNamed module with a proof that its annotated functions
    are fully in-place. -/
syntax (name := kokaFipQuot) "[NKOKA_FIP|" kokaRaw "]" : term

/-- Parse and compile the source of a quotation. -/
meta def compileQuot (stx : Syntax) : TermElabM Module := do
  let src := stx[1].getAtomVal
  match compileSource src with
  | .ok m => return m
  | .error e => throwErrorAt stx "KokaNamed: {e}"

@[term_elab kokaQuot]
meta def elabKoka : TermElab := fun stx _ => do
  let m ← compileQuot stx
  return toExpr m

@[term_elab kokaFipQuot]
meta def elabKokaFip : TermElab := fun stx _ => do
  let m ← compileQuot stx
  let bad := m.sig.filter fun fd => !(fd.annot == .plain || fd.check m.sig)
  unless bad.isEmpty do
    throwErrorAt stx "KokaNamed: the FIPNamed check fails for {bad.map (·.name)}"
  let mE := toExpr m
  let sigE := mkApp (mkConst ``Module.sig) mE
  let checkE := mkApp (mkConst ``FIPNamed.Sig.check) sigE
  let eqT ← mkEq checkE (mkConst ``Bool.true)
  let h ← mkExpectedTypeHint (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)) eqT
  let wf := mkApp2 (mkConst ``FIPNamed.Sig.check_sound) sigE h
  return mkApp2 (mkConst ``FipModule.mk) mE wf

end KokaNamed
