# How to read this formalization of *FP²: Fully in-Place Functional Programming*

This project formalizes, in Lean 4 with Mathlib, the paper by Lorenzen, Leijen and Swierstra
(ICFP 2023, <https://doi.org/10.1145/3607840>). The technical-report text is in
`fip-tr-v2.latex`. The Lean sources in `RequestProject/` are grouped into one directory per
section or appendix of the paper:

```
RequestProject/
├── Frontend/              Koka surface syntax, the [KOKA| … ] / [KOKA_FIP| … ] notation,
│                          and `Koka.Module F C` (modules indexed by their names)
├── Sec1_Overview/         §1   introductory examples (reverse, splay-tree zipper, smap)
├── Sec2_Calculus/         §2   the FIP calculus: grammar, semantics, typing rules, checker,
│                               and a fuel-free evaluator
├── Sec3_Traversals/       §3   tree map with zippers; plain (non-FIP) Koka code
├── AppA_Examples/         §4 / App. A  red-black trees, merge sort, quicksort, finger trees
├── AppB_StoreSoundness/   §2.3–2.4 / App. B  store semantics, Theorems 1–3, Corollary 1
├── AppC_StackBound/       §2.6 / App. C  stack safety, Theorem 4
├── AppD_TRMC/             §5 / App. D  TRMC with reuse (Lemmas 41, 43, 45)
├── AppE_HeapSoundness/    §5 / App. E  λfip, heap semantics, Theorem 6 and counterexamples
└── Main.lean              shared options (not imported by the other files)
```

Every file begins with a `/-! … -/` header that says which part of the paper it covers and
which definitions or theorems it contains. Read that header before the code.

Lean namespaces are unchanged by the directory layout. The core calculus lives in
`namespace FIP`, `λfip` and the heap in `namespace FIP.Lam`, and the Koka front end in
`namespace Koka`.

## Where each part of the paper starts and ends

`RequestProject/PaperMap.lean` maps every section, figure and theorem of the paper (with its
page numbers in `fip-tr-v2.pdf`) to the Lean files that formalize it. Inside those files,
`PAPER <section> START: <title>` / `PAPER <section> END: <title>` comments (as `// …` lines
inside `[KOKA| … ]` blocks) mark where the code for that part of the paper starts and ends.
`grep -rn "PAPER sec. 1.2 " RequestProject` lists the code of §1.2, and
`grep -rn "PAPER.*App. B" RequestProject` the code of Appendix B.

---

## Suggested reading order

### 1. The grammar and the rules (§2): `Sec2_Calculus/`

There is a single representation of the calculus: bound variables are **de Bruijn indices**
`Fin n`, and the number `n` of variables in scope is an index of the type. `Expr n` has at
most `n` free variables, and **`Expr 0` is exactly the type of closed expressions** (store
locations, which are never bound, may still occur). A function body is an
`Expr (|x̄| + |ȳ|)`: it can only mention its parameters. Binders carry no names, so the
paper's convention that bound variables are distinct holds by construction.

Read these files in this order. Each one imports the previous one.

| File | Paper | Contents |
|---|---|---|
| `Syntax.lean` | Fig. 2, Fig. 6 | `Var n` (bound variables and store locations), `Val n`, `Expr n`, `Branches n`, function annotations `Annot` (`fip`, `fbip`, with optional allocation budgets from §2.5), `FunDef`, signatures `Sig`, `Sig.names`, `Sig.lookup` |
| `Semantics.lean` | Fig. 3 (§2.1) | substitution, evaluation contexts `ECtx`, head reduction `Head`, `Step`/`Steps` (`e ⟼* e'`), and a bounded interpreter `Expr.run`/`Expr.eval` proved sound |
| `Eval.lean` | — | the **fuel-free, terminating evaluator** `Expr.evalTotal`. It takes a proof `Expr.Halts` that the expression reduces to values (`∃ vs, e ⟼* (vs)`, no fuel in the definition) and performs one step of the semantics after the other, by well-founded recursion on the reduction (`acc_of_halts`). Also `halts_iff_run`, `evalTotal_sound`, `evalTotal_unique`, `evalTotal_eq_run`, completeness of the interpreter and `Step.deterministic` |
| `Rules.lean` | Fig. 4, 6, 7 (§2.2–2.5) | the judgment `Wf cfg U Δ Γ e`, i.e. `Δ \| Γ ⊢ e`: borrowed environment `Δ`, owned multiset `Γ` of variables and reuse credits `⋄k`; `FunDef.Wf`, `Sig.Wf` (`⊩ Σ`) |
| `Check.lean` | remark in §2.2 | an executable checker `check` / `Sig.check` |
| `CheckSound.lean` | — | `Sig.check_sound`: if the checker accepts, then `⊩ Σ` holds |
| `SubstLemmas.lean` | — | substitution lemmas used by the proofs |

### 2. Writing the paper's code verbatim: `Frontend/`

You only need these files to see how the Koka listings become Lean terms.

* `Ast.lean`, `Parse.lean`: the Koka fragment used in the paper and a layout-sensitive parser.
* `IR.lean`, `Compile.lean`: translation of Koka into the calculus of `Sec2_Calculus/`
  (the compiler works with names internally and resolves them to de Bruijn indices at the end).
* `Module.lean`: **`Koka.Module F C`**, a compiled module indexed by the set `F` of its
  top-level functions and the set `C` of its constructors (both `Finset String`). The
  structure carries proofs that `F` and `C` are exactly the names of the module, that
  function names are distinct, and that the module is closed with consistent arities:
  every function called or passed and every constructor built or matched belongs to `F`
  resp. `C`, every call passes as many borrowed and owned arguments as the function has
  parameters, and every constructor is used with its declared number of fields (lemmas
  `Module.fn_mem_of_refs`, `Module.call_arity`, `Module.ctor_arity`). Its operations
  ask for membership proofs, discharged by `decide`:
  * `m.fn f hf` — the definition of `f ∈ F` (no `Option`);
  * `m.eval f b o` — the result of the call `f(b; o)`: needs `f ∈ F` and a proof that the
    call terminates (found by running the interpreter, `fip_halts`), and **no fuel**;
    `eval_sound`, `eval_unique`;
  * `m.evalExpr e`, `m.evalFold f init args` — the same for other closed expressions;
  * `m.con c args`, `m.atom c` — constructor values, checked against `C` and the arity of `c`;
    `m.fnVal f` — a function of the module as a value; `m.call f e₁ e₂` — a call of `f ∈ F`.

  `FipModule F C` extends `Module F C` with a proof of `⊩ Σ`.
* `Elab.lean`: the two elaborators.
  * `[KOKA| … ]` compiles any Koka module to a `Module F C`, computing `F` and `C`. An
    unknown function or constructor, an arity mismatch, or a function defined twice, is a
    compile-time error.
  * `[KOKA_FIP| … ]` also runs the checker. Through `Sig.check_sound` it produces a
    `FipModule F C`. A function that is not FIP is a compile-time error.

  Write `def m := [KOKA_FIP| … ]` without a type: the indices are inferred, e.g.
  `rev : FipModule {"reverse-acc", "reverse"} {"Nil", "Cons", …}`.
* `Util.lean`: `listV`, `foldCalls`, and the tactic `koka_eval`, which proves statements
  about `Module.eval` results by running the interpreter in the kernel.
* `Robustness.lean`: the lexer, the parser and the compiler are total functions (no
  `partial`, no fuel: well-founded recursion on the input, with run-time checked measures
  where the measure is only known at run time), so `[KOKA| … ]` cannot loop; a recursive
  value type is reported as an error.
* `Divergence.lean`: why `eval` needs a termination proof — a `fip` function that loops
  (`loop_diverges`), so no evaluator can be total and sound without that premise
  (`no_sound_total_eval`).

### 3. The examples: `Sec1_Overview/`, `Sec3_Traversals/`, `AppA_Examples/`

Each file is a Koka listing from the paper inside `[KOKA_FIP| … ]`. After the listing come a
theorem `…_wf` (the functions are fully in-place) and a few evaluation checks such as
`reverse_example : intro.eval "reverse" [] [listV [1, 2, 3, 4, 5]] = [listV [5, 4, 3, 2, 1]]`,
proved by `koka_eval`.

* `Sec1_Overview/Intro.lean`: §1 (list reversal, splay-tree zippers, `is-node`, `smap`).
* `Sec3_Traversals/Plain.lean`: the zipper-based `tmap` of §3. It also has plain `[KOKA| … ]`
  code, and shows that `palindrome` is rejected by `[KOKA_FIP| … ]`.
* `AppA_Examples/RedBlack.lean` (A.1), `MergeSort.lean` (A.2), `QuickSort.lean` (A.3, with
  the `fbip` variant of §4.2), `FingerTree.lean` (A.4).

### 4. Store semantics and Theorem 1 (§2.3–2.4, App. B): `AppB_StoreSoundness/`

Start with the definitions and statements:

| File | Paper | Contents |
|---|---|---|
| `Store.lean` | Fig. 5, 6; B.1–B.2 | stores `S`, `Sound`, `Linear`, `roots`, the store semantics `SStep`/`SSteps` (`S \| e ⟼*ₛ S' \| e'`); **Theorem 2** `SSteps.size_eq` and **Theorem 3** `SSteps.size_le` |
| `StoreSound.lean` | B.6 | `Sig.PaperFragment` (the setting of Theorem 1). Stores bind locations only (`Var 0`), so a store cannot bind a program variable |
| `StoreSoundProof.lean` | B.6 | **Theorem 1** `store_sound` (corrected) and **Corollary 1** `store_sound_closed` |

The proof is spread over these files, listed in import order:
`SubstFacts.lean` → `StoreInv.lean` (B.1–B.2, including `Store.Ptr` and `Store.Reads`) →
`StoreAlloc.lean` → `FunSteps.lean` → `StoreSoundAux.lean` (B.5 main invariant) →
`StoreSoundCall.lean` → `StoreSoundCases.lean` (one case per typing rule) →
`StoreSoundBinders.lean` → `StoreSoundProof.lean`. `Weaken.lean` proves Lemma 12 of B.4.

### 5. The stack bound (§2.6, App. C): `AppC_StackBound/`

* `Stack.lean`: depths `|e|`, `|E|`, `e_max` and stack safety `Sig.StackSafe`.
* `StackCex.lean`: `not_stackBoundClaim`. The bound `|E| ≤ |e_max|·|Σ|²` fails already for
  the identity function.
* `StackBound.lean`: **Theorem 4, corrected**: `stack_bound` proves
  `|E| ≤ (|Σ|+1)² · max(1, |e_max|)`.
* The proof files, in import order: `StackDefs.lean` → `StackBP.lean` (borrowed positions,
  C.2–C.3) → `StackSem.lean` → `StackRank.lean` (ranks and weights) → `StackLocal.lean`
  (frames, C.1).

### 6. TRMC with reuse (§5, App. D): `AppD_TRMC/`

`TRMC.lean` covers:

* accumulators `AccE` and **Lemma 41** `accE_wf`;
* the tail-context replacement **Lemma 43** `Wf.tailRepl`;
* typed evaluation contexts `ECtx.Wf` and the value replacement **Lemma 45**
  `ECtx.Wf.plug_val`.

### 7. Reference counting and Theorem 6 (§5, App. E): `AppE_HeapSoundness/`

| File | Paper | Contents |
|---|---|---|
| `LamSyntax.lean` | Fig. 9 | `λfip` syntax with de Bruijn indices (`LVal n`, `LVals n`, `LExpr n`); a lambda is closure-converted by construction |
| `LamSubst.lean` | — | substitution lemmas |
| `Heap.lean` | Fig. 9, 10; E.1 | the functional semantics and typing `LWf` of `λfip`, heaps with reference counts, the heap semantics `HSteps`, the join `H₁ ⊗ H₂`, the translation of destructive match (`LWf.dmatch_translation`) |
| `HeapCex.lean` | E.6 | Theorem 6 as stated needs two extra hypotheses: `heap_sound_needs_adm` (the size in `dropru`) and `heap_sound_needs_no_fn` (function values) |
| `HeapAdm.lean` | — | the admissible fragment `LExpr.Adm` (no function values, `dropru` with the matched size), substitutions of locations for variables |
| `HeapFunSteps.lean` | — | counted functional reductions `LStepsN` and their inversion in evaluation contexts |
| `HeapRoots.lean` | E.1 | reference counts, roots and linearity under `dup`, `drop`, freeing, allocation and credits |
| `HeapInv.lean` | E.2 | the heap invariant `HInv` (linear heap, well-formed objects, `σ = [H]`) |
| `HeapDrop.lean`, `HeapLocs.lean`, `HeapAlloc.lean` | E.4 | dropping (recursive freeing), locations of well-formed expressions, allocation of values |
| `HeapSoundAux.lean`, `HeapSoundSimple.lean`, `HeapSoundCases.lean`, `HeapSoundCalls.lean` | E.5 | the main lemma `MainClaim`, case by case |
| `HeapSound.lean` | E.6 | **Theorem 6** `heap_sound` and **Corollary 3** `heap_sound_empty` |

The corrected Theorem 6 (`heap_sound`) assumes an admissible signature and expression and a
heap satisfying `HInv`.  Instead of the paper's split `H₁ ⊗ H₂` it uses one heap whose roots
are the owned environment `Γ` plus a frame `R` containing the borrowed variables `Δ`.

---

## Where the formalization differs from the paper

The file headers and docstrings explain each of these points in detail.

* **Theorem 1.**
  * Stores must have the paper's shape: locations bound to constructors applied to
    locations (`Store.Ptr`).
  * `[S]` is expressed as a substitution of closed values for locations (`Store.Reads`).
  * Function names in a signature must be distinct.
* **Theorem 4.** The bound is `(|Σ|+1)² · max(1, |e_max|)`. The paper's
  `|e_max|·|Σ|²` is refuted.
* **Theorem 6.** As stated it is false: counterexamples show that `dropru` must be
  restricted to the reuse step of a match and that function values must be excluded
  (`HeapCex.lean`). The corrected theorem `heap_sound` (`HeapSound.lean`) adds these two
  restrictions (`LExpr.Adm`) and the heap invariant `HInv`, and uses a single heap with a
  frame of roots instead of the join `H₁ ⊗ H₂`.
* **Binders are de Bruijn indices** everywhere, so the paper's implicit convention that bound
  variables are distinct (Barendregt's convention) needs no side conditions.

## Building and checking

```
lake build
```

This builds every file in `RequestProject/`. There is no `sorry` in the sources. To see which
axioms a result depends on, run `#print axioms FIP.store_sound` (or the same for any other
theorem) in a file that imports the relevant module.

---

## Type safety of the front end: what is enforced, and what could be added

Enforced by the types or by the invariants of `Koka.Module F C` (checked by the kernel when
a `[KOKA| … ]` block is elaborated):

* bound variables are well scoped (de Bruijn indices `Fin n`; a function body only
  mentions its parameters);
* every function and constructor that the code mentions belongs to `F` resp. `C`, calls
  have the right numbers of borrowed and owned arguments, and constructors the right
  number of fields;
* the operations of a module (`fn`, `eval`, `evalExpr`, `con`, `atom`, `fnVal`, `call`)
  demand membership proofs (and, for `con`, the arity), so that a misspelt name is a type
  error at the use site;
* `eval` demands a proof of termination instead of fuel, and `FipModule` carries `⊩ Σ`.

Possible further steps (not done, because each changes the core calculus on which the
soundness proofs of Appendices B–E are stated):

* index the core syntax by the signature, `Expr F n`, so that `call f` carries `f ∈ F` and a
  closed module is closed by construction rather than by an invariant;
* give constructors their arity in the type (`Val.ctor c (args : Vector (Val n) k)` with
  `k` the declared arity of `c`);
* type the core values by Koka types (an intrinsically typed core), so that `Module.eval`
  could take and return typed Lean values (for example `List Int`) instead of `Val 0`, with
  the decoding (`listV`, `ofListV`) given by a type class;
* record the annotation (`fip`, `fbip`, `fip(n)`) of each function in the type of a
  `FipModule`, so that a lemma about a `fip` function cannot be applied to a `fbip` one.

