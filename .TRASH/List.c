// Lean compiler output
// Module: RequestProject.List
// Imports: public import Init
#include <lean/lean.h>

#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
  #endif
  LEAN_EXPORT lean_object * l_myLength___redArg(lean_object * );
  LEAN_EXPORT lean_object * l_myLengthTRAux___redArg___boxed(lean_object * , lean_object * );
  LEAN_EXPORT lean_object * l_myLength___redArg___boxed(lean_object * );
  LEAN_EXPORT lean_object * l_myLength___boxed(lean_object * , lean_object * );
  LEAN_EXPORT lean_object * l_myLengthTRAux(lean_object * , lean_object * , lean_object * );
  LEAN_EXPORT lean_object * l_myLengthTRAux___redArg(lean_object * , lean_object * );
  LEAN_EXPORT lean_object * l_myLength(lean_object * , lean_object * );
  LEAN_EXPORT lean_object * l_myLengthTRAux___boxed(lean_object * , lean_object * , lean_object * );
  lean_object * lean_nat_add(lean_object * , lean_object * );

  /*
   * [1] NON-TAIL-RECURSIVE CORE (Specialized / Reduced-Arg)
   * Why: Type parameter 'α' is erased at runtime, leaving only the List argument x_1.
   * Implementation: NOT tail-recursive. Calls itself recursively, waits for the result,
   * then computes (+ 1). Uses O(N) call-stack frames; risks stack overflow on large lists.
   */
  LEAN_EXPORT lean_object * l_myLength___redArg(lean_object * x_1) {
    _start: {
      if (lean_obj_tag(x_1) == 0) {
        lean_object * x_2;
        x_2 = lean_unsigned_to_nat(0 u);
        return x_2;
      } else {
        lean_object * x_3;
        lean_object * x_4;
        lean_object * x_5;
        lean_object * x_6;
        x_3 = lean_ctor_get(x_1, 1);
        /* Recursive C function call: pushes a new stack frame */
        x_4 = l_myLength___redArg(x_3);
        x_5 = lean_unsigned_to_nat(1 u);
        /* Post-call work: cannot tail-call optimize because addition occurs after return */
        x_6 = lean_nat_add(x_4, x_5);
        lean_dec(x_4);
        return x_6;
      }
    }
  }

  /*
   * [2] BOXED WRAPPER for reduced-arg myLength
   * Why: ABI compatibility wrapper that handles reference-counting ownership.
   * Implementation: Forwards to l_myLength___redArg, then decrements (frees) input x_1.
   */
  LEAN_EXPORT lean_object * l_myLength___redArg___boxed(lean_object * x_1) {
    _start: {
      lean_object * x_2;
      x_2 = l_myLength___redArg(x_1);
      lean_dec(x_1);
      return x_2;
    }
  }

  /*
   * [3] FULL-ARITY ENTRY POINT for myLength
   * Why: Matches Lean's logical signature: (α : Type) -> List α -> Nat.
   * Implementation: Discards erased type 'x_1' and delegates to reduced-arg core.
   */
  LEAN_EXPORT lean_object * l_myLength(lean_object * x_1, lean_object * x_2) {
    _start: {
      lean_object * x_3;
      x_3 = l_myLength___redArg(x_2);
      return x_3;
    }
  }

  /*
   * [4] BOXED WRAPPER for full-arity myLength (OWNED!!!!! NOT BORROWED, l_myLength IS BORROWED!!!)
   * Why: Standard calling convention wrapper for dynamic/higher-order calls.
   * Implementation: Calls l_myLength, then decrements list argument x_2.
   */
  LEAN_EXPORT lean_object * l_myLength___boxed(lean_object * x_1, lean_object * x_2) {
    _start: {
      lean_object * x_3;
      x_3 = l_myLength(x_1, x_2);
      lean_dec(x_2);
      return x_3;
    }
  }

  /*
   * [5] TAIL-RECURSIVE CORE (Specialized / Reduced-Arg)
   * Why: Core implementation of tail-recursive length with erased type argument.
   * Implementation: TAIL-RECURSIVE. Updates accumulator (x_2 + 1), updates list pointer (x_1),
   * and jumps directly to `_start` via goto. Uses O(1) stack space (pure loop, stack-safe).
   */
  LEAN_EXPORT lean_object * l_myLengthTRAux___redArg(lean_object * x_1, lean_object * x_2) {
    _start: {
      if (lean_obj_tag(x_1) == 0) {
        return x_2;
      } else {
        lean_object * x_3;
        lean_object * x_4;
        lean_object * x_5;
        x_3 = lean_ctor_get(x_1, 1);
        x_4 = lean_unsigned_to_nat(1 u);
        /* Compute new accumulator first */
        x_5 = lean_nat_add(x_2, x_4);
        lean_dec(x_2);
        /* In-place argument update for loop iteration */
        x_1 = x_3;
        x_2 = x_5;
        /* Tail-call optimized: loop jump instead of a function call */
        goto _start;
      }
    }
  }

  /*
   * [6] BOXED WRAPPER for reduced-arg myLengthTRAux
   * Why: ABI reference-counting wrapper.
   * Implementation: Forwards to l_myLengthTRAux___redArg, then frees consumed list x_1.
   */
  LEAN_EXPORT lean_object * l_myLengthTRAux___redArg___boxed(lean_object * x_1, lean_object * x_2) {
    _start: {
      lean_object * x_3;
      x_3 = l_myLengthTRAux___redArg(x_1, x_2);
      lean_dec(x_1);
      return x_3;
    }
  }

  /*
   * [7] FULL-ARITY ENTRY POINT for myLengthTRAux
   * Why: Matches Lean signature: (α : Type) -> List α -> Nat -> Nat.
   * Implementation: Discards erased type x_1 and forwards list (x_2) and acc (x_3).
   */
  LEAN_EXPORT lean_object * l_myLengthTRAux(lean_object * x_1, lean_object * x_2, lean_object * x_3) {
    _start: {
      lean_object * x_4;
      x_4 = l_myLengthTRAux___redArg(x_2, x_3);
      return x_4;
    }
  }

  /*
   * [8] BOXED WRAPPER for full-arity myLengthTRAux
   * Why: ABI dynamic call wrapper with reference count cleanup.
   * Implementation: Calls l_myLengthTRAux, then decrements consumed list argument x_2.
   */
  LEAN_EXPORT lean_object * l_myLengthTRAux___boxed(lean_object * x_1, lean_object * x_2, lean_object * x_3) {
    _start: {
      lean_object * x_4;
      x_4 = l_myLengthTRAux(x_1, x_2, x_3);
      lean_dec(x_2);
      return x_4;
    }
  }

  /*
   * [9] MODULE INITIALIZER
   * Why: Registers and runs initialization code for this Lean module and its dependencies.
   */
  lean_object * initialize_Init(uint8_t builtin);
  static bool _G_initialized = false;
  LEAN_EXPORT lean_object * initialize_RequestProject_List(uint8_t builtin) {
    lean_object * res;
    if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
    _G_initialized = true;
    res = initialize_Init(builtin);
    if (lean_io_result_is_error(res)) return res;
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
  }
  #ifdef __cplusplus
}
#endif
