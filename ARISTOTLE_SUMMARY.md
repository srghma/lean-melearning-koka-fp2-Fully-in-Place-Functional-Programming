# Summary of changes for run 990f35c7-be69-4f3f-af3a-7b2ee67ccc5d
I worked through all five points of your request. The full project builds with `lake build`. It contains no `sorry`, `admit`, `partial def` or added axioms. I checked the main theorems with `#print axioms`: `FIP.store_sound`, `FIP.Lam.heap_sound`, `Examples.QuickSort.quicksort_example`, `Examples.Divergence.no_sound_total_eval` and `Koka.Module.call_arity` use only the standard axioms. Everything is committed and pushed.

1. **Named implementation removed.** `RequestProject/Named` and the named `[NKOKA| … ]` / `[NKOKA_FIP| … ]` front end were already gone when this session started. Only the de Bruijn implementation and `[KOKA| … ]` / `[KOKA_FIP| … ]` are left.

2. **Modules indexed by finsets.** `Koka.Module F C` (and `FipModule F C`) are indexed by the `Finset` of top-level functions `F` and of constructors `C`. The module carries proofs that:
   - `F` and `C` are exactly its names;
   - function names are distinct;
   - the code is closed: it only calls, builds or matches names in `F` / `C`.

   `Module.eval` requires a proof `f ∈ F`, found by `decide` by default.

3. **More type safety.**
   - The closedness field now also checks arities. Every call passes as many borrowed and owned arguments as the function declares, and every constructor is built or matched with its declared number of fields.
   - This is exposed as proved lemmas `fn_mem_of_refs`, `call_arity` and `ctor_arity`.
   - The elaborator rejects bad references with an error message.
   - Further ideas I did not implement are listed in a new "Type safety" section of `READING_GUIDE.md`.

4. **Fuel-less, terminating evaluation and elaboration.**
   - **Elaborator:** every `partial` definition is gone. The lexer, parser, compiler and elaborator are total, with termination measures that are checked at run time.
   - **Evaluator:** `FIP.Expr.evalTotal` uses no fuel. It is defined by well-founded recursion and takes a proof that the expression terminates in the paper's functional semantics (`Expr.Halts`, which `halts_iff` shows is exactly that). It is proved sound and its result is the only one (`evalTotal_sound`, `evalTotal_unique`); `Module.eval` is built on it.
   - **Why a termination proof is needed:** `no_sound_total_eval` proves that no evaluator can be both total and sound, because a FIP function `loop(x) = loop(x)` never terminates.
   - **Where fuel remains:** the default tactic `fip_halts` finds the termination proof by running the interpreter for a fixed number of steps, so fuel survives there only as a way to search for proofs.

5. **Less duplication.** I merged shared helpers in the compiler and parser (`freshAtom`, one lexicographic-measure lemma, `pExpr` reusing `pAtom`). I also merged the `Head.not_ret` lemma, which existed twice, into `Sec2_Calculus/Semantics.lean`, and fixed some deprecation warnings.

In the results table I updated the `Koka.Module` entry for the arity invariant and added `Koka.Module.call_arity` as proved.