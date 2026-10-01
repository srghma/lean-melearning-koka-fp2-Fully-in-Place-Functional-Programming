# Summary of changes for run 6014dad0-b9ba-4cd3-93b9-a9b2c1f8ca3c
Both items left open by the previous session are now done: there are corrected, proved versions of Theorem 4 and Theorem 6. The whole project builds (`lake build`) with no warnings. There is no `sorry` outside the commented-out original false statements, and the new results use only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

**Theorem 4 (stack bound), corrected.** `FIP.stack_bound` in `RequestProject/FIP/StackBound.lean` proves the bound `|E| ≤ (|Σ|+1)² · max(1, |e_max|)` for every evaluation context reached from a call. This replaces the paper's `|e_max| · |Σ|²`, which is false (`not_stackBoundClaim`). The hypotheses are:
- every function is FIP or FBIP,
- the signature is stack safe, with no empty recursive groups,
- the store has the paper's shape.

The proof tracks the stack of active calls: a non-tail call pushes a call of strictly smaller weight, and a tail call reuses its slot.

**Theorem 6 (heap soundness), corrected.** `FIP.Lam.heap_sound_corrected` is in `RequestProject/FIP/HeapTheorem.lean`. The paper's two heaps `H₁ ⊗ H₂` become one heap `H` satisfying an invariant `HInv H R RC Γ σ` (in `HeapInv.lean`):
- heaps bind locations only;
- each reference count equals the references held by the rest of the computation (`R`, which must contain `Δ`), plus those of the owned environment `Γ`, plus those from the heap itself;
- reuse credits are accounted the same way;
- `σ` is `[H]`.

The conclusion: if `[H]e ⟼* v̄`, then `H | e ⟼*ₕ H' | ȳ` with `[H']ȳ = v̄`. Also, `H'` is linear in the paper's sense, `roots(H')` as locations is `R, ȳ`, the invariant still holds, and the locations in `R` still denote the same values. `HeapLinear.lean` proves that the invariant implies `Heap.Linear` and pins down `roots`.

`heap_sound_closed` covers closed programs `∅ | ∅ ⊢ e` run from the empty heap: the final heap is linear, its roots are exactly the result locations, and every non-empty reuse credit has been used up.

**Extra hypotheses.** Beyond location-only heaps, the corrected theorem requires the program and signature to be *admissible* (`LExpr.Adm`, `LSig.Adm` in `HeapSyntax.lean`):
1. **No function used as a value.** This is needed: `heap_sound_needs_no_fn` gives `f(y;) = dup y; drop y; ()` and `g() = ()`. Then `f(g;)` evaluates to `()` functionally, but the heap semantics has no rule for `dup g` and gets stuck.
2. **`dropru x` only as the reuse step of a match branch on `x`.** This is needed: the typing rule does not check that the size written in `dropru` matches the cell. `heap_sound_needs_adm` shows a well-typed `dropru x 1; free 1; ()` with `x ↦¹ C` (a cell with no fields) that evaluates functionally but is stuck in the heap semantics.
3. **Lambda parameters are distinct.** The proof uses this, but I have not proved that it is necessary.

The proof is strong induction on the length of the functional reduction, then recursion on the typing derivation. It is split across `HeapCases.lean`, `HeapCasesB.lean` (let, call), `HeapApp.lean` (application) and `HeapMatch.lean` (match), and assembled in `HeapSound.lean`.

The comments in `Heap.lean` and `HeapCex.lean` now point to the corrected statement. The Properties table lists the corrected Theorem 6, the closed-program version and the two necessity counterexamples as proved. It also records the `HInv` and `LExpr.Adm` definitions, and the original false Theorem 6 entry now refers to the corrected version.

# Summary of changes for run 1e76a75a-b05f-4d01-b5cb-36afddd681c2
This session finished the proof of Theorem 1, the soundness of the store semantics (Appendix B), with no `sorry`. It also found that the formal statements of Theorem 4 and Theorem 6 left by the earlier session are false as written, and proved counterexamples to both. The full project builds, and no `sorry` is left outside commented-out code. All proved results use only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

**Theorem 1 (B.1–B.6)**
- `FIP.store_sound` and Corollary 1 (`FIP.store_sound_closed`) are in `RequestProject/FIP/StoreSoundProof.lean`. The proof works by strong induction on the length of the functional reduction, then on the typing derivation.
- The supporting lemmas are spread over `StoreInv.lean`, `StoreAlloc.lean`, `StoreSoundAux.lean`, `StoreSoundCall.lean` and `StoreSoundCases.lean`. They cover splitting and joining stores, building values in the store, dropping trees, and every typing rule: tuple, call, borrowed application, application of a named function, `let`, borrowed match, destructive match, `drop`, `free`, `empty`, `inst` and `weaken`.
- **The statement differs from the paper's in three ways:**
  - Stores must have the paper's shape: locations bound to constructors applied to locations (`Store.Ptr`).
  - The paper's `[S]` is expressed as a substitution of closed values for locations (`Store.Reads`).
  - I added a field `names` to `Sig.PaperFragment`, requiring distinct function names. Without it the theorem fails: an annotated function could call a name that resolves to an unannotated function with the same name, whose body allocates.
- The earlier version of Theorem 1, which let stores bind program names, is false. The counterexample is `not_storeSoundOriginalClaim` in `StoreSoundCex.lean`.

**Theorem 4 (Appendix C) is false as stated.** `not_stackBoundClaim` in `RequestProject/FIP/StackCex.lean` refutes the bound `|E| ≤ |e_max|·|Σ|²`. Take the identity function `f(; x) = x`, whose body has depth 0. The very first expression, the call itself, already has an evaluation context of depth 1, while the bound is 0.

**Theorem 6 (Appendix E) is false as stated.** `not_heapSoundClaim` in `RequestProject/FIP/HeapCex.lean` refutes it with the same kind of counterexample as the early Theorem 1: a heap that binds a program name.

The false statements of Theorems 4 and 6 are kept, commented out, in `Stack.lean` and `Heap.lean`, with notes explaining why they fail.

**Not done:** I have not written or proved corrected versions of Theorems 4 and 6. A fixed Theorem 4 needs a larger bound, and its proof needs an invariant on the stack of nested function calls. A fixed Theorem 6 needs heaps that bind only locations, and its proof would redo the Theorem 1 argument with reference counts and closures. Both are substantial pieces of work that remain open.

The Properties table lists Theorems 1, 2 and 3 and Corollary 1 as proved, and the original Theorem 1 statement and Theorems 4 and 6 as negated. It also records the two definitions the Theorem 1 statement relies on, `Sig.PaperFragment` and `Store.Reads`.