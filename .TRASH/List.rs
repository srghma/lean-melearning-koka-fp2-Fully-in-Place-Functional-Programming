// ============================================================================
// Minimal Mock of <lean/lean.h> Runtime Primitives
// ============================================================================

#[allow(non_camel_case_types)]
#[repr(C)]
pub struct lean_object {
    pub tag: u8,                        // 0 = Nil (or Nat), 1 = Cons
    pub fields: [*mut lean_object; 2],  // [head, tail]
    pub nat_val: usize,                 // Value if object is a Nat
}

#[inline(always)]
pub unsafe fn lean_obj_tag(o: *mut lean_object) -> u8 {
    (*o).tag
}

#[inline(always)]
pub unsafe fn lean_ctor_get(o: *mut lean_object, idx: usize) -> *mut lean_object {
    (*o).fields[idx]
}

pub unsafe fn lean_unsigned_to_nat(n: u32) -> *mut lean_object {
    Box::into_raw(Box::new(lean_object {
        tag: 0,
        fields: [std::ptr::null_mut(), std::ptr::null_mut()],
        nat_val: n as usize,
    }))
}

pub unsafe fn lean_nat_add(a: *mut lean_object, b: *mut lean_object) -> *mut lean_object {
    let sum = (*a).nat_val + (*b).nat_val;
    lean_unsigned_to_nat(sum as u32)
}

pub unsafe fn lean_dec(o: *mut lean_object) {
    if !o.is_null() {
        // In real Lean this decrements RC; here we free for illustration
        let _ = Box::from_raw(o);
    }
}

// ============================================================================
// Direct 1-to-1 Translation of Lean Compiler C Output
// ============================================================================

/* [1] Non-tail-recursive core: performs recursive call + post-addition */
pub unsafe fn l_myLength___redArg(x_1: *mut lean_object) -> *mut lean_object {
    // '_start:' block in C
    if lean_obj_tag(x_1) == 0 {
        let x_2: *mut lean_object = lean_unsigned_to_nat(0);
        return x_2;
    } else {
        let x_3: *mut lean_object = lean_ctor_get(x_1, 1);
        let x_4: *mut lean_object = l_myLength___redArg(x_3); // Recursive stack call
        let x_5: *mut lean_object = lean_unsigned_to_nat(1);
        let x_6: *mut lean_object = lean_nat_add(x_4, x_5);
        lean_dec(x_4);
        return x_6;
    }
}

/* [2] Boxed wrapper for reduced-arg myLength */
pub unsafe fn l_myLength___redArg___boxed(x_1: *mut lean_object) -> *mut lean_object {
    let x_2: *mut lean_object = l_myLength___redArg(x_1);
    lean_dec(x_1);
    return x_2;
}

/* [3] Full-arity entry point for myLength (discards erased type param x_1) */
pub unsafe fn l_myLength(_x_1: *mut lean_object, x_2: *mut lean_object) -> *mut lean_object {
    let x_3: *mut lean_object = l_myLength___redArg(x_2);
    return x_3;
}

/* [4] Boxed wrapper for full-arity myLength */
pub unsafe fn l_myLength___boxed(x_1: *mut lean_object, x_2: *mut lean_object) -> *mut lean_object {
    let x_3: *mut lean_object = l_myLength(x_1, x_2);
    lean_dec(x_2);
    return x_3;
}

/* [5] Tail-recursive core: transformed to a loop (mimics 'goto _start') */
pub unsafe fn l_myLengthTRAux___redArg(
    mut x_1: *mut lean_object,
    mut x_2: *mut lean_object,
) -> *mut lean_object {
    'start: loop {
        if lean_obj_tag(x_1) == 0 {
            return x_2;
        } else {
            let x_3: *mut lean_object = lean_ctor_get(x_1, 1);
            let x_4: *mut lean_object = lean_unsigned_to_nat(1);
            let x_5: *mut lean_object = lean_nat_add(x_2, x_4);
            lean_dec(x_2);
            x_1 = x_3;
            x_2 = x_5;
            continue 'start; // Exact equivalent of C's 'goto _start;'
        }
    }
}

/* [6] Boxed wrapper for reduced-arg myLengthTRAux */
pub unsafe fn l_myLengthTRAux___redArg___boxed(
    x_1: *mut lean_object,
    x_2: *mut lean_object,
) -> *mut lean_object {
    let x_3: *mut lean_object = l_myLengthTRAux___redArg(x_1, x_2);
    lean_dec(x_1);
    return x_3;
}

/* [7] Full-arity entry point for myLengthTRAux (discards erased type param x_1) */
pub unsafe fn l_myLengthTRAux(
    _x_1: *mut lean_object,
    x_2: *mut lean_object,
    x_3: *mut lean_object,
) -> *mut lean_object {
    let x_4: *mut lean_object = l_myLengthTRAux___redArg(x_2, x_3);
    return x_4;
}

/* [8] Boxed wrapper for full-arity myLengthTRAux */
pub unsafe fn l_myLengthTRAux___boxed(
    x_1: *mut lean_object,
    x_2: *mut lean_object,
    x_3: *mut lean_object,
) -> *mut lean_object {
    let x_4: *mut lean_object = l_myLengthTRAux(x_1, x_2, x_3);
    lean_dec(x_2);
    return x_4;
}

// ============================================================================
// Verification / Entry point
// ============================================================================

fn main() {
    unsafe {
        // Construct mock list: [(), ()] -> length 2
        let nil = Box::into_raw(Box::new(lean_object {
            tag: 0,
            fields: [std::ptr::null_mut(), std::ptr::null_mut()],
            nat_val: 0,
        }));

        let cons1 = Box::into_raw(Box::new(lean_object {
            tag: 1,
            fields: [std::ptr::null_mut(), nil],
            nat_val: 0,
        }));

        let list = Box::into_raw(Box::new(lean_object {
            tag: 1,
            fields: [std::ptr::null_mut(), cons1],
            nat_val: 0,
        }));

        // 1. Test non-tail-recursive version
        let res_non_tr = l_myLength___redArg(list);
        println!("Non-tail-rec length: {}", (*res_non_tr).nat_val);

        // 2. Test tail-recursive version
        let acc0 = lean_unsigned_to_nat(0);
        let res_tr = l_myLengthTRAux___redArg(list, acc0);
        println!("Tail-rec length:     {}", (*res_tr).nat_val);
    }
}
