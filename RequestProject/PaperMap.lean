module

/-!
# Map from the paper *FP²: Fully in-Place Functional Programming* to the Lean code

Lorenzen, Leijen, Swierstra, ICFP 2023 (https://doi.org/10.1145/3607840).  Page numbers are
those of the technical report `fip-tr-v2.pdf` (85 pages) in the project root.

Every Lean file that formalizes part of the paper carries markers

```
/- ══════ PAPER <section> START: <section title>: <topic> (<pages, figures>) ══════ ... -/
/- ══════ PAPER <section> END: <section title>: <topic> ══════ -/
// ===== PAPER <section> START: ... =====          (inside a [KOKA| ... ] block)
// ===== PAPER <section> END: ... =====
```

so `grep -rn "PAPER sec. 1.2 " RequestProject` finds the code of §1.2 and
`grep -rn "PAPER.*App. B" RequestProject` the code of Appendix B.  The START and END of one region
carry the same text, and regions never nest.  When one region of the paper is split over
two places in the same file the second one is marked `(continued)`.  The one region that
is not part of the paper (the Lean notation for Koka code) is marked `NOT IN PAPER`.
Paths below are relative to `RequestProject/`.

| Paper | Title | PDF pages | Lean code |
|---|---|---|---|
| §1 | Introduction and Overview (`reverse`) | 1–3 | `Sec1_Overview/Intro.lean` |
| §1.1 | Zippers and Unboxed Tuples | 2–3 | `Sec1_Overview/Intro.lean` |
| §1.2 | Splay Tree Lookup and Atoms (Fig. 1) | 3–5 | `Sec1_Overview/Intro.lean` |
| §1.3 | Borrowing and Second-Order Functions | 5 | `Sec1_Overview/Intro.lean` |
| §1.4 | Fully in-Place in a Functional World | 5–7 | `Sec3_Traversals/Plain.lean` (first and last region) |
| §1.5 | Contributions | 7 | no code |
| §2 | A Language for Fully In-Place Update (grammar, Fig. 2, Fig. 6) | 7–8, 13 | `Sec2_Calculus/Syntax.lean` |
| §2.1 | Functional Operational Semantics (Fig. 3) | 8–9 | `Sec2_Calculus/Semantics.lean` |
| §2.2 | FIP: Fully In-Place (Fig. 4) | 9–11 | `Sec2_Calculus/Rules.lean`, `Check.lean`, `CheckSound.lean` |
| §2.3 | Store Semantics (Fig. 5), Theorems 1–2, Corollaries 1–2 | 11–12 | `AppB_StoreSoundness/Store.lean`, `StoreSound.lean`, `StoreSoundProof.lean` |
| §2.4 | FBIP: Allowing Deallocation (Fig. 6), Theorem 3 | 12–13 | `Sec2_Calculus/Rules.lean` (second region), `AppB_StoreSoundness/Store.lean` |
| §2.5 | FIP and FBIP with bounded allocation (Fig. 7) | 13–14 | `Sec2_Calculus/Rules.lean` (second region) |
| §2.6 | Stack Safe FIP, Theorem 4 | 14 | `AppC_StackBound/Stack.lean`, `StackCex.lean`, `StackBound.lean` |
| §3 | Fully In-Place Traversals over Polynomial Datatypes | 15 | `Sec3_Traversals/Plain.lean` (middle region) |
| §3.1 | Tail Recursion Modulo Reusable Defunctionalized CPS Contexts (Fig. 8), Theorem 5 | 15–18 | `Sec3_Traversals/Plain.lean`, `AppD_TRMC/TRMC.lean` |
| §4 | Further Examples of Fully In-Place Algorithms | 18 | see §4.1–4.3 |
| §4.1 | Imperative red-black tree insertion, functionally | 18–20 | `AppA_Examples/RedBlack.lean` |
| §4.2 | Sorting lists in-place | 20–21 | `AppA_Examples/MergeSort.lean`, `QuickSort.lean` |
| §4.3 | Finger trees | 21–22 | `AppA_Examples/FingerTree.lean` |
| §5 | Reference Counting with Borrowing and Unboxing (Fig. 9) | 22–24 | `AppE_HeapSoundness/LamSyntax.lean`, `Heap.lean` |
| §5.1 | Elaborating borrowing | 24 | `AppE_HeapSoundness/LamSyntax.lean`, `Heap.lean` |
| §5.2 | Heap semantics (Fig. 10) | 24–25 | `AppE_HeapSoundness/Heap.lean` |
| §5.3 | Soundness of the Heap Semantics, Theorem 6, Corollary 3 | 25–26 | `Named/AppE_HeapSoundness/HeapInv.lean`, `HeapTheorem.lean`, `HeapCex.lean`, `HeapAdmCex.lean` |
| §6 | Benchmarks (Fig. 11) | 26–28 | no code |
| §7 | Related Work | 28–29 | no code |
| §8 | Conclusion and Future Work | 29 | no code |
| App. A.1 | Red-Black Trees | 32–33 | `AppA_Examples/RedBlack.lean` |
| App. A.2 | Stable Merge Sort | 33–35 | `AppA_Examples/MergeSort.lean` |
| App. A.3 | Quick Sort | 35–36 | `AppA_Examples/QuickSort.lean` |
| App. A.4 | Finger Trees | 36–38 | `AppA_Examples/FingerTree.lean` |
| App. B.1 | Properties of Stores | 38–40 | `AppB_StoreSoundness/Store.lean` (first region) |
| App. B.2–B.6 | Simple Invariant, Progress, Linearity and roots, Main Invariant, Soundness (Theorem 7) | 40–54 | `AppB_StoreSoundness/Store.lean` (last region), `StoreSound.lean`, `StoreSoundProof.lean`, `Named/AppB_StoreSoundness/StoreSoundCex.lean` |
| App. C.1–C.3 | Stack Bound: within a function, first-order, second-order (Theorem 8) | 54–67 | `AppC_StackBound/Stack.lean`, `StackCex.lean`, `StackBound.lean` |
| App. D, D.1 | TRMC with Reuse Translation (Fig. 12), Soundness (Theorem 9) | 67–71 | `AppD_TRMC/TRMC.lean` |
| App. E.1 | Properties of Heaps | 71–75 | `AppE_HeapSoundness/Heap.lean` |
| App. E.2–E.6 | Simple Invariant, Progress, Linearity and roots, Main Invariant, Soundness (Theorem 10) | 75–85 | `Named/AppE_HeapSoundness/HeapInv.lean`, `HeapTheorem.lean`, `HeapCex.lean`, `HeapAdmCex.lean` |

## What is verified

* Every `fip`/`fbip` function of the paper (§1, §3, App. A) is accepted by the checker,
  and the checker is sound (`FIP.Sig.check_sound`), so each module carries a proof of
  `⊩ Σ` (`intro_wf`, `tmapZipper_wf`, `rbtree_wf`, `mergesort_wf`, `quicksort_wf`,
  `fbipQuicksort_wf`, `fingertree_wf`).
* Theorem 1 (store soundness) and Corollary 1: `FIP.store_sound`, `FIP.store_sound_closed`,
  with a corrected statement; the original wording is refuted by
  `FIPNamed.not_storeSoundOriginalClaim`.
* Theorems 2 and 3: `FIP.SSteps.size_eq`, `FIP.SSteps.size_le`.
* Theorem 4 (stack bound), corrected: `FIP.stack_bound`; the original bound is refuted by
  `FIP.not_stackBoundClaim`.
* TRMC with reuse: Lemmas 41, 43, 45 (`FIP.accE_wf`, `FIP.Wf.tailRepl`,
  `FIP.ECtx.Wf.plug_val`).
* Theorem 6 (heap soundness), corrected: `FIPNamed.Lam.heap_sound_corrected`,
  `FIPNamed.Lam.heap_sound_closed`; the original wording is refuted by
  `FIPNamed.Lam.not_heapSoundClaim`, and the extra hypotheses are shown necessary by
  `FIPNamed.Lam.heap_sound_needs_adm`, `FIPNamed.Lam.heap_sound_needs_no_fn`.
-/
