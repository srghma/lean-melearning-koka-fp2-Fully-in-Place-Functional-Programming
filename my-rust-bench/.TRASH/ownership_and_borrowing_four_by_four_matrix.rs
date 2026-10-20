use crate::box_list::{BoxList, Node as BoxNode};
use crate::box_to_box::reverse_box_to_box_tail;
use crate::box_to_rc::reverse_box_to_rc_tail;
use crate::rc_list::{Node as RcNode, RcList};
use crate::rc_to_box::reverse_rc_to_box_tail;
use crate::rc_to_rc::reverse_rc_to_rc_tail;
use std::rc::Rc;

// =========================================================================
// ROW 1: INPUT IS Owned Unique (BoxList<T>)
// =========================================================================

// --- [1, 1] Owned Box -> Owned Box ---
// ==== ALREADY IMPLEMENTED IN src/box_to_box.rs ====
#[inline(always)]
pub fn row1_col1_owned_box_to_owned_box<T>(mut list: BoxList<T>) -> BoxList<T> {
    BoxList {
        head: reverse_box_to_box_tail(list.head.take()),
    }
}

// --- [1, 2] Owned Box -> Borrowed Unique (&mut BoxList<T>) ---
// Consumes an owned BoxList, reverses it in-place, and installs it into an existing &mut target.
#[inline(always)]
pub fn row1_col2_owned_box_to_mut_box<T>(
    list: BoxList<T>,
    target: &mut BoxList<T>,
) -> &mut BoxList<T> {
    *target = row1_col1_owned_box_to_owned_box(list);
    target
}

// --- [1, 3] Owned Box -> Owned Shared (RcList<T>) ---
// ==== ALREADY IMPLEMENTED IN src/box_to_rc.rs ====
#[inline(always)]
pub fn row1_col3_owned_box_to_owned_rc<T>(mut list: BoxList<T>) -> RcList<T> {
    RcList {
        head: reverse_box_to_rc_tail(list.head.take()),
    }
}

// --- [1, 4] Owned Box -> Borrowed Shared (&BoxList<T>) ---
// Consumes an owned BoxList, reverses it into an allocated slot, and yields an immutable view.
#[inline(always)]
pub fn row1_col4_owned_box_to_shared_ref<T>(
    list: BoxList<T>,
    slot: &mut BoxList<T>,
) -> &BoxList<T> {
    *slot = row1_col1_owned_box_to_owned_box(list);
    slot
}

// =========================================================================
// ROW 2: INPUT IS Borrowed Unique (&mut BoxList<T>)
// =========================================================================

// --- [2, 1] Borrowed Unique -> Owned Box ---
// Drains the &mut location using head.take(), tail-recursively reverses it,
// leaving the source empty and returning ownership to caller.
#[inline(always)]
pub fn row2_col1_mut_box_to_owned_box<T>(list: &mut BoxList<T>) -> BoxList<T> {
    let owned = list.head.take();
    BoxList {
        head: reverse_box_to_box_tail(owned),
    }
}

// --- [2, 2] Borrowed Unique -> Borrowed Unique (&mut BoxList<T>) ---
// Pure in-place pointer flip without reallocation or changing heap addresses.
#[inline(always)]
pub fn row2_col2_mut_box_to_mut_box<T>(list: &mut BoxList<T>) -> &mut BoxList<T> {
    let owned = list.head.take();
    list.head = reverse_box_to_box_tail(owned);
    list
}

// --- [2, 3] Borrowed Unique -> Owned Shared (RcList<T>) ---
// Drains the uniquely borrowed list and converts all nodes into Rc pointers.
#[inline(always)]
pub fn row2_col3_mut_box_to_owned_rc<T>(list: &mut BoxList<T>) -> RcList<T> {
    let owned = list.head.take();
    RcList {
        head: reverse_box_to_rc_tail(owned),
    }
}

// --- [2, 4] Borrowed Unique -> Borrowed Shared (&BoxList<T>) ---
// Mutates the list in-place and downgrades the exclusive borrow to a shared view.
#[inline(always)]
pub fn row2_col4_mut_box_to_shared_ref<T>(list: &mut BoxList<T>) -> &BoxList<T> {
    let owned = list.head.take();
    list.head = reverse_box_to_box_tail(owned);
    list
}

// =========================================================================
// ROW 3: INPUT IS Owned Shared (RcList<T>)
// =========================================================================

// --- [3, 1] Owned Shared -> Owned Box ---
// ==== ALREADY IMPLEMENTED IN src/rc_to_box.rs ====
#[inline(always)]
pub fn row3_col1_owned_rc_to_owned_box<T: Clone>(mut list: RcList<T>) -> BoxList<T> {
    BoxList {
        head: reverse_rc_to_box_tail(list.head.take()),
    }
}

// --- [3, 2] Owned Shared -> Borrowed Unique (&mut BoxList<T>) ---
// Converts owned shared list into box list and installs into an existing &mut target.
#[inline(always)]
pub fn row3_col2_owned_rc_to_mut_box<T: Clone>(
    list: RcList<T>,
    target: &mut BoxList<T>,
) -> &mut BoxList<T> {
    *target = row3_col1_owned_rc_to_owned_box(list);
    target
}

// --- [3, 3] Owned Shared -> Owned Shared (RcList<T>) ---
// ==== ALREADY IMPLEMENTED IN src/rc_to_rc.rs ====
#[inline(always)]
pub fn row3_col3_owned_rc_to_owned_rc<T: Clone>(mut list: RcList<T>) -> RcList<T> {
    RcList {
        head: reverse_rc_to_rc_tail(list.head.take()),
    }
}

// --- [3, 4] Owned Shared -> Borrowed Shared (&RcList<T>) ---
// Reverses RcList in-place/COW into slot and returns an immutable view.
#[inline(always)]
pub fn row3_col4_owned_rc_to_shared_ref<T: Clone>(
    list: RcList<T>,
    slot: &mut RcList<T>,
) -> &RcList<T> {
    *slot = row3_col3_owned_rc_to_owned_rc(list);
    slot
}

// =========================================================================
// ROW 4: INPUT IS Borrowed Shared (&BoxList<T>)
// =========================================================================

// --- [4, 1] Borrowed Shared -> Owned Box ---
// Must deep-clone elements because the source cannot be consumed or mutated.
#[inline(always)]
fn ref_to_box_acc<T: Clone>(
    cur: Option<&BoxNode<T>>,
    acc: Option<Box<BoxNode<T>>>,
) -> Option<Box<BoxNode<T>>> {
    match cur {
        Some(node) => {
            let new_box = Some(Box::new(BoxNode {
                val: node.val.clone(),
                next: acc,
            }));
            ref_to_box_acc(node.next.as_deref(), new_box)
        }
        None => acc,
    }
}

#[inline(always)]
pub fn row4_col1_shared_ref_to_owned_box<T: Clone>(list: &BoxList<T>) -> BoxList<T> {
    BoxList {
        head: ref_to_box_acc(list.head.as_deref(), None),
    }
}

// --- [4, 2] Borrowed Shared -> Borrowed Unique (&mut BoxList<T>) ---
// TYPE-THEORETIC NOTE:
// A direct signature `fn(&BoxList<T>) -> &mut BoxList<T>` is STATICALLY FORBIDDEN
// by Rust's Borrow Checker (Aliasing XOR Mutability theorem: &T cannot alias &mut T).
// The only valid implementation is writing a cloned reversal into a separate exclusive target.
#[inline(always)]
pub fn row4_col2_shared_ref_to_mut_box<'a, T: Clone>(
    src: &BoxList<T>,
    target: &'a mut BoxList<T>,
) -> &'a mut BoxList<T> {
    *target = row4_col1_shared_ref_to_owned_box(src);
    target
}

// --- [4, 3] Borrowed Shared -> Owned Shared (RcList<T>) ---
// Clones values from the borrowed list into reference-counted nodes.
#[inline(always)]
fn ref_to_rc_acc<T: Clone>(
    cur: Option<&BoxNode<T>>,
    acc: Option<Rc<RcNode<T>>>,
) -> Option<Rc<RcNode<T>>> {
    match cur {
        Some(node) => {
            let new_rc = Some(Rc::new(RcNode {
                val: node.val.clone(),
                next: acc,
            }));
            ref_to_rc_acc(node.next.as_deref(), new_rc)
        }
        None => acc,
    }
}

#[inline(always)]
pub fn row4_col3_shared_ref_to_owned_rc<T: Clone>(list: &BoxList<T>) -> RcList<T> {
    RcList {
        head: ref_to_rc_acc(list.head.as_deref(), None),
    }
}

// --- [4, 4] Borrowed Shared -> Borrowed Shared (Lazy Zero-Allocation View) ---
// Returns a stack of references that traverses the list backward without copying or allocating.
pub struct ReversedView<'a, T> {
    cursors: Vec<&'a T>,
}

#[inline(always)]
fn collect_refs_acc<'a, T>(cur: Option<&'a BoxNode<T>>, mut acc: Vec<&'a T>) -> Vec<&'a T> {
    match cur {
        Some(node) => {
            acc.push(&node.val);
            collect_refs_acc(node.next.as_deref(), acc)
        }
        None => acc,
    }
}

#[inline(always)]
pub fn row4_col4_shared_ref_to_reversed_view<'a, T>(list: &'a BoxList<T>) -> ReversedView<'a, T> {
    ReversedView {
        cursors: collect_refs_acc(list.head.as_deref(), Vec::new()),
    }
}

impl<'a, T> Iterator for ReversedView<'a, T> {
    type Item = &'a T;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        self.cursors.pop()
    }
}
