# How to read this formalization of *FP²: Fully in-Place Functional Programming*

This project formalizes, in Lean 4 with Mathlib, the paper by Lorenzen, Leijen and Swierstra
(ICFP 2023, <https://doi.org/10.1145/3607840>). The technical-report text is in
`fip-tr-v2.latex`. The Lean sources in `RequestProject/` are grouped into one directory per
section or appendix of the paper:

```
RequestProject/
├── Frontend/              Koka surface syntax and the [KOKA| … ] / [KOKA_FIP| … ] notation
├── Sec1_Overview/         §1   introductory examples (reverse, splay-tree zipper, smap)
├── Sec2_Calculus/         §2   the FIP calculus: grammar, semantics, typing rules, checker
│   └── DeBruijn/               the same calculus with well-scoped de Bruijn indices (`Term n`)
├── Sec3_Traversals/       §3   tree map with zippers; plain (non-FIP) Koka code
├── AppA_Examples/         §4 / App. A  red-black trees, merge sort, quicksort, finger trees
├── AppB_StoreSoundness/   §2.3–2.4 / App. B  store semantics, Theorems 1–3, Corollary 1
├── AppC_StackBound/       §2.6 / App. C  stack safety, Theorem 4
├── AppD_TRMC/             §5 / App. D  TRMC with reuse (Lemmas 41, 43, 45)
├── AppE_HeapSoundness/    §5 / App. E  λfip, heap semantics, Theorem 6
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

Read these files in this order. Each one imports the previous one.

| File | Paper | Contents |
|---|---|---|
| `Syntax.lean` | Fig. 2, Fig. 6 | `Var` (program names and store locations), `Val`, `Expr`, `Branch`, function annotations `Annot` (`fip`, `fbip`, with optional allocation budgets from §2.5), `FunDef`, signatures `Sig` |
| `Semantics.lean` | Fig. 3 (§2.1) | substitution, evaluation contexts `ECtx`, head reduction `Head`, `Step`/`Steps` (`e ⟼* e'`), and an executable interpreter `Expr.run` proved sound |
| `Rules.lean` | Fig. 4, 6, 7 (§2.2–2.5) | the judgment `Wf cfg U Δ Γ e`, i.e. `Δ \| Γ ⊢ e`: borrowed environment `Δ`, owned multiset `Γ` of variables and reuse credits `⋄k`; `FunDef.Wf`, `Sig.Wf` (`⊩ Σ`) |
| `Check.lean` | remark in §2.2 | an executable checker `check` / `Sig.check` |
| `CheckSound.lean` | — | `Sig.check_sound`: if the checker accepts, then `⊩ Σ` holds |

### 1b. Well-scoped de Bruijn syntax: `Sec2_Calculus/DeBruijn/` and `AppE_HeapSoundness/LamDeBruijn*.lean`

The calculus of `Syntax.lean` uses named binders. These files give a second representation in
which bound variables are de Bruijn indices `Fin n` and the number `n` of variables in scope is
an index of the type: `Term n` has at most `n` free variables, and **`Term 0` is exactly the type
of closed expressions** (store locations, which are never bound, may still occur). Under `k` new
binders the scope becomes `n + k`; the index `j < k` is the `j`-th new binder and `k + i` is the
outer variable `i`. A function body is a `Term (|x̄| + |ȳ|)`: it can only mention its parameters.

| File | Contents |
|---|---|
| `DeBruijn/Syntax.lean` | `TVal n`, `Term n`, `TBranches n`, `TFunDef`, `TSig`; substitution `Term.subst` (with `Subst.up`, `Subst.inst`, `Subst.args`); name resolution `Expr.toTerm : Scope n → Expr → Option (Term n)`, `Expr.toClosed`, `FunDef.toTFunDef`, `Sig.toTSig` |
| `DeBruijn/Semantics.lean` | Fig. 3 on `Term n`: `TECtx`, `THead`, `TStep`, `TSteps`. A step maps `Term n` to `Term n`, so closed terms stay closed by construction |
| `DeBruijn/Closed.lean` | `Expr.toTerm_isSome_iff` (resolution succeeds iff every free name is in scope), `Expr.toClosed_isSome_iff` (**a named expression is a `Term 0` iff it has no free name**), `FunDef.toTFunDef_isSome_iff` |
| `DeBruijn/ScopeLemmas.lean`, `SubstComm.lean`, `SimLemmas.lean`, `Beta.lean` | proof files; the key lemma is `Expr.toTerm_subst`: substituting closed values commutes with name resolution |
| `DeBruijn/Simulation.lean` | **the two semantics agree on closed programs**: `Step.toClosed`, `TStep.ofClosed` (lock-step simulation in both directions), `Steps.toClosed`, `TSteps.ofClosed`, and `Steps.ret_iff` (same results) |
| `DeBruijn/Print.lean` | `Term.toExpr` prints a term with names; `Term.toExpr_toTerm` / `Term.toExpr_toClosed`: resolving the printed term gives the term back (so `Expr.toTerm` is onto) |
| `DeBruijn/Wf.lean` | well-formed programs are well scoped: `Wf.fv_inEnv`, `Wf.toClosed_isSome`, `FunDef.Wf.toTFunDef_isSome` |
| `DeBruijn/Examples.lean` | every Koka module of the paper is well scoped (`…_scoped`); `reverse_db` runs `reverse` of §1 in the de Bruijn semantics |
| `AppE_HeapSoundness/LamDeBruijn.lean` | `λfip` with de Bruijn indices: `LTVal n`, `LTVals n k`, `LTerm n`; a lambda `λ^z̄ x̄. e` is `LTVal.lam zs sc body` with `body : LTerm (k + |x̄|)` for `k = |z̄|` captured values, so closures are closure-converted by construction; the plain substitution `LTerm.subst`, the closure-instantiating substitution `LTerm.isubst` used by the semantics (it reaches a lambda body through the captured values that become closed values, as the named substitution of Fig. 9 does), the functional semantics `LTStep`, and name resolution `LExpr.toLTerm` |
| `AppE_HeapSoundness/LamDeBruijnClosed.lean` | `LExpr.toLTerm_isSome_iff`, `LExpr.toLTerm_empty_isSome_iff` (**`LTerm 0` = closed expressions with correctly annotated lambdas**), `lam_wrong_annotation` |
| `AppE_HeapSoundness/LamDeBruijnWf.lean` | `LWf.scoped`, `LWf.toLTerm_closed` (every well-formed closed `λfip` program is an `LTerm 0`), `LSig.Wf.toLTSig` |
| `AppE_HeapSoundness/LamDeBruijnSubst.lean`, `LamDeBruijnBeta.lean`, `LamDeBruijnSimLemmas.lean` | proof files; the key lemma is `LExpr.toLTerm_subst`: substituting closed values commutes with name resolution, with `LTerm.isubst` on the de Bruijn side |
| `AppE_HeapSoundness/LamDeBruijnSim.lean` | **the two semantics of `λfip` agree on closed programs**: `LStep.toClosed`, `LTStep.ofClosed` (lock-step simulation in both directions), `LSteps.toClosed`, `LTSteps.ofClosed`, and `LSteps.ret_iff` (same results) |
| `AppE_HeapSoundness/LamDeBruijnExample.lean` | why the semantics needs `LTerm.isubst`: for `(λ^z x. z) D` and `z := C`, the plain substitution does not commute with name resolution (`plain_subst_does_not_commute`), the closure-instantiating one does (`isubst_commutes_example`) |

The proofs of Theorems 1, 4 and 6 are still carried out on the named syntax; the de Bruijn
layer is connected to it by the simulation theorems (for the core calculus and for `λfip`) and
by the scoping theorems.

### 2. Writing the paper's code verbatim: `Frontend/`

You only need these files to see how the Koka listings become Lean terms.

* `Ast.lean`, `Parse.lean`: the Koka fragment used in the paper and a layout-sensitive parser.
* `Compile.lean`: translation of Koka into the calculus of `Sec2_Calculus/`.
* `Elab.lean`: the two elaborators.
  * `[KOKA| … ]` compiles any Koka module.
  * `[KOKA_FIP| … ]` also runs the checker. Through `Sig.check_sound` it produces a
    `FipModule`, which carries a proof of `⊩ Σ`. A function that is not FIP is a
    compile-time error.
* `Util.lean`: helpers for running compiled functions in the examples.

### 3. The examples: `Sec1_Overview/`, `Sec3_Traversals/`, `AppA_Examples/`

Each file is a Koka listing from the paper inside `[KOKA_FIP| … ]`. After the listing come a
theorem `…_wf` (the functions are fully in-place) and a few evaluation checks such as
`reverse_example` and `sort_example`.

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
| `StoreSound.lean` | B.6 | `Sig.PaperFragment` (the setting of Theorem 1); the paper's original wording of Theorem 1, kept commented out |
| `StoreSoundCex.lean` | — | `not_storeSoundOriginalClaim`: the original wording is false when a store may bind a program name |
| `StoreSoundProof.lean` | B.6 | **Theorem 1** `store_sound` (corrected) and **Corollary 1** `store_sound_closed` |

The proof is spread over these files, listed in import order:
`SubstFacts.lean` → `StoreInv.lean` (B.1–B.2, including `Store.Ptr` and `Store.Reads`) →
`StoreAlloc.lean` → `FunSteps.lean` → `StoreSoundAux.lean` (B.5 main invariant) →
`StoreSoundCall.lean` → `StoreSoundCases.lean` (one case per typing rule) →
`StoreSoundProof.lean`. `Weaken.lean` proves Lemma 12 of B.4.

### 5. The stack bound (§2.6, App. C): `AppC_StackBound/`

* `Stack.lean`: depths `|e|`, `|E|`, `e_max` and stack safety `Sig.StackSafe`. It keeps the
  paper's original wording of Theorem 4, commented out.
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

Start with the definitions and statements:

| File | Paper | Contents |
|---|---|---|
| `Heap.lean` | Fig. 9, 10; E.1 | `λfip` syntax (`LVal`, `LExpr`), its typing `LWf`, heaps with reference counts, the heap semantics `HSteps`, the translation of destructive match (`LWf.dmatch_translation`). It keeps the paper's original wording of Theorem 6, commented out |
| `HeapCex.lean` | — | `not_heapSoundClaim`: the original wording is false |
| `HeapSyntax.lean` | — | admissible programs `LExpr.Adm` / `LSig.Adm` (an extra hypothesis) |
| `HeapInv.lean` | E.2, E.5 | the invariant `HInv` that replaces `H₁ ⊗ H₂` |
| `HeapLinear.lean` | E.4 | `HInv` implies that the heap is linear, and pins down its roots |
| `HeapTheorem.lean` | E.6 | **Theorem 6, corrected**: `heap_sound_corrected`, and the closed-program version `heap_sound_closed` |
| `HeapAdmCex.lean` | — | `heap_sound_needs_no_fn`, `heap_sound_needs_adm`: two of the admissibility conditions cannot be dropped |

The proof files, in import order:
`HeapRename.lean` → `HeapFun.lean` → `HeapInv.lean` → `HeapOps.lean` (dup/drop/free, E.1)
→ `HeapAlloc.lean` → `HeapMainAux.lean` → `HeapCases.lean` → `HeapCasesB.lean` (let, call)
→ `HeapApp.lean` → `HeapMatch.lean` → `HeapSound.lean`.

---

## Where the formalization differs from the paper

The file headers and docstrings explain each of these points in detail. Every original
wording that turned out to be false is kept in a block comment next to its counterexample.

* **Theorem 1.**
  * Stores must have the paper's shape: locations bound to constructors applied to
    locations (`Store.Ptr`).
  * `[S]` is expressed as a substitution of closed values for locations (`Store.Reads`).
  * Function names in a signature must be distinct.
* **Theorem 4.** The bound is `(|Σ|+1)² · max(1, |e_max|)`. The paper's
  `|e_max|·|Σ|²` is refuted.
* **Theorem 6.**
  * The two heaps `H₁ ⊗ H₂` are replaced by one heap with an invariant `HInv`.
  * Heaps bind only locations.
  * Programs must be admissible: no function values, `dropru` only as the reuse step of a
    match, and distinct lambda parameters.
  * Counterexamples show that the first two admissibility conditions are needed. No
    counterexample shows that the third one is needed.
* **Binders are named** in the syntax used for the proofs of Theorems 1, 4 and 6. The paper's
  implicit convention that bound variables are distinct (Barendregt's convention) becomes
  explicit freshness side conditions, for example in Lemmas 12 and 43. The nameless,
  well-scoped representation `Term n` (`Sec2_Calculus/DeBruijn/`) has no such conditions;
  on closed programs its semantics is in lock-step with the named one.

## Building and checking

```
lake build
```

This builds every file in `RequestProject/`, including `RequestProject/All.lean`, which imports
every module at once: if two files declared the same name, that file would fail to build. So
any combination of results (for instance Theorem 1 together with Theorem 4) can be imported
into one file. The only `sorry`s in the sources are inside the
commented-out original statements in `StoreSound.lean`, `Stack.lean` and `Heap.lean`. To
see which axioms a result depends on, run `#print axioms FIP.store_sound` (or the same for
any other theorem) in a file that imports the relevant module.
