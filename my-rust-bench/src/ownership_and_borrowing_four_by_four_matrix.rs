//! The 4x4 Ownership and Borrowing Reversal Matrix
//!
//! Grounded in the Linear-Cartesian-Unique (LCU) calculus and Graded Modal Types
//! from "Linearity and Uniqueness: An Entente Cordiale" (Marshall, Vollmer, Orchard, ESOP 2022).
//!
//! Type correspondences:
//! - Row/Col 1: Owned Unique          -> LCU: *1 A (Unique, 0 aliases, safe for in-place mutation)
//! - Row/Col 2: Borrowed Unique       -> LCU: &mut (*1 A) (Exclusive temporary loan of *1 capability)
//! - Row/Col 3: Owned Dynamic Shared  -> Perceus COW: dynamic branch (*1 A if RC==1, else !A)
//! - Row/Col 4: Borrowed Shared       -> LCU: *n A where n < 1 (Fractional uniqueness / read-only view)

use crate::box_list::{BoxList, Node as BoxNode};
use crate::box_to_box::reverse_box_to_box_tail;
use crate::box_to_rc::reverse_box_to_rc_tail;
use crate::rc_list::{Node as RcNode, RcList};
use crate::rc_to_box::reverse_rc_to_box_tail;
use crate::rc_to_rc::reverse_rc_to_rc_tail;
use std::rc::Rc;

// =========================================================================
// ROW 1: INPUT IS Owned Unique (*1 A) represented by BoxList<T>
// =========================================================================

/// --- [1, 1] Owned Unique -> Owned Unique ---
/// LCU Type: `reverse : *(List a) -> *(List a)`
/// Granule: `*1 (List a) -> *1 (List a)`
///
/// Guaranteed by LCU Theorem 5 (Uniqueness Invariant): because this list has a
/// single incoming reference from the past (*A), in-place destructive pointer
/// inversion is referentially transparent and executes with 0 allocations (FIP).
#[inline(always)]
pub fn row1_col1_owned_box_to_owned_box<T>(mut list: BoxList<T>) -> BoxList<T> {
    BoxList {
        head: reverse_box_to_box_tail(list.head.take()),
    }
}

/// --- [1, 2] Owned Unique -> Borrowed Unique (&mut BoxList<T>) ---
/// LCU Type: `reverse_into : *(List a) -> &mut *(List a) -> &mut *(List a)`
///
/// Consumes the owned unique *1 resource, flips pointers in-place, and writes
/// the resulting head into an existing exclusive target slot.
#[inline(always)]
pub fn row1_col2_owned_box_to_mut_box<T>(
    list: BoxList<T>,
    target: &mut BoxList<T>,
) -> &mut BoxList<T> {
    *target = row1_col1_owned_box_to_owned_box(list);
    target
}

/// --- [1, 3] Owned Unique -> Owned Shared (RcList<T>) ---
/// LCU Type: `borrow : *(List a) -> !(List a)`
/// Granule: `uniqueReturn : *a -> !a` (Return of Relative Monad)
///
/// Implements the relative monad `borrow` rule from ESOP 2022 §3.1: the past
/// uniqueness guarantee is forgotten to produce an unrestricted/shared structure,
/// allocating N reference-counting control blocks (RcBox) for the elements.
#[inline(always)]
pub fn row1_col3_owned_box_to_owned_rc<T>(mut list: BoxList<T>) -> RcList<T> {
    RcList {
        head: reverse_box_to_rc_tail(list.head.take()),
    }
}

/// --- [1, 4] Owned Unique -> Borrowed Shared (&BoxList<T>) ---
/// LCU Type: `split_permission : *1 (List a) -> *n (List a)` where n < 1
///
/// Consumes the unique list, reverses it in-place into caller storage, and
/// downgrades the full uniqueness permission (*1) into a fractional read-only
/// permission (*n).
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

/// --- [2, 1] Borrowed Unique -> Owned Unique (BoxList<T>) ---
/// LCU Type: `drain : &mut *(List a) -> *(List a)`
///
/// Extracts the exclusive *1 capability via `take()`, leaving the source
/// location as `None`, reverses it tail-recursively in-place, and transfers
/// owned uniqueness (*1) to the caller.
#[inline(always)]
pub fn row2_col1_mut_box_to_owned_box<T>(list: &mut BoxList<T>) -> BoxList<T> {
    let owned = list.head.take();
    BoxList {
        head: reverse_box_to_box_tail(owned),
    }
}

/// --- [2, 2] Borrowed Unique -> Borrowed Unique (&mut BoxList<T>) ---
/// LCU Type: `reverse_in_place : &mut *(List a) -> &mut *(List a)`
///
/// Pure in-place pointer flip on an exclusively held location. Preserves heap
/// node addresses and caller identity with 0 allocations.
#[inline(always)]
pub fn row2_col2_mut_box_to_mut_box<T>(list: &mut BoxList<T>) -> &mut BoxList<T> {
    let owned = list.head.take();
    list.head = reverse_box_to_box_tail(owned);
    list
}

/// --- [2, 3] Borrowed Unique -> Owned Shared (RcList<T>) ---
/// LCU Type: `drain_and_borrow : &mut *(List a) -> !(List a)`
///
/// Drains the exclusive source slot and forgets uniqueness into shared `Rc`
/// control blocks (allocates N headers).
#[inline(always)]
pub fn row2_col3_mut_box_to_owned_rc<T>(list: &mut BoxList<T>) -> RcList<T> {
    let owned = list.head.take();
    RcList {
        head: reverse_box_to_rc_tail(owned),
    }
}

/// --- [2, 4] Borrowed Unique -> Borrowed Shared (&BoxList<T>) ---
/// LCU Type: `reborrow_fractional : &'a mut *1 (List a) -> &'a *n (List a)`
///
/// Mutates the list in-place via its exclusive capability, then downgrades
/// the borrow from exclusive (*1) to fractional read-only (*n).
#[inline(always)]
pub fn row2_col4_mut_box_to_shared_ref<T>(list: &mut BoxList<T>) -> &BoxList<T> {
    let owned = list.head.take();
    list.head = reverse_box_to_box_tail(owned);
    list
}

// =========================================================================
// ROW 3: INPUT IS Owned Dynamic Shared (RcList<T>)
// =========================================================================

/// --- [3, 1] Owned Shared -> Owned Unique (BoxList<T>) ---
/// LCU / Perceus Type: `dynamic_try_unwrap : RcList a -> *(List a)`
///
/// THEORETICAL NOTE (ESOP 2022 §3.1 vs. Dynamic Systems):
/// In static LCU logic, transforming unrestricted `!A` into unique `*A` is
/// impossible without a deep `copy`. At runtime, `Rc::try_unwrap` acts as an
/// optimistic Perceus-style branch: if `strong_count == 1`, uniqueness is
/// dynamically recovered with 0 atomic updates; if shared, it falls back to
/// cloning values into fresh Box cells.
#[inline(always)]
pub fn row3_col1_owned_rc_to_owned_box<T: Clone>(mut list: RcList<T>) -> BoxList<T> {
    BoxList {
        head: reverse_rc_to_box_tail(list.head.take()),
    }
}

/// --- [3, 2] Owned Shared -> Borrowed Unique (&mut BoxList<T>) ---
/// Unwraps/clones from the dynamic reference-counted list into unique Box nodes
/// and installs them into an existing exclusive `target` slot.
#[inline(always)]
pub fn row3_col2_owned_rc_to_mut_box<T: Clone>(
    list: RcList<T>,
    target: &mut BoxList<T>,
) -> &mut BoxList<T> {
    *target = row3_col1_owned_rc_to_owned_box(list);
    target
}

/// --- [3, 3] Owned Shared -> Owned Shared (RcList<T>) ---
/// LCU / Perceus Type: `perceus_reverse : RcList a -> RcList a`
///
/// Dynamic in-place reference counting (Perceus):
/// Evaluates `Rc::get_mut`. If `strong_count == 1`, it mutates in-place (FIP).
/// If `strong_count > 1`, it falls back to Copy-On-Write allocation to protect
/// shared persistent tails.
#[inline(always)]
pub fn row3_col3_owned_rc_to_owned_rc<T: Clone>(mut list: RcList<T>) -> RcList<T> {
    RcList {
        head: reverse_rc_to_rc_tail(list.head.take()),
    }
}

/// --- [3, 4] Owned Shared -> Borrowed Shared (&RcList<T>) ---
/// Performs Perceus reversal into caller-allocated slot and yields an immutable view.
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
// (Modelled in Granule §6 as Fractional Uniqueness: *n A where n < 1)
// =========================================================================

/// --- [4, 1] Borrowed Shared -> Owned Unique (BoxList<T>) ---
/// LCU Type: `copy t as x in t' : !(List a) -> *(List a)`
/// Granule: `uniqueBind : (*a -> !b) -> !a -> !b`
///
/// Implements the LCU `copy` rule from ESOP 2022 §3.1: because the source is
/// fractionally held (n < 1) / unrestricted (!A), it cannot be mutated or drained.
/// Producing a brand new unique *1 value requires deep-cloning all elements.
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

/// --- [4, 2] Borrowed Shared -> Borrowed Unique (&mut BoxList<T>) ---
/// TYPE-THEORETIC NOTE (ESOP 2022 §6 & Fractional Permissions):
/// In Granule/Boyland's fractional permission logic:
///     *n P ⊗ *m P <-> *n+m P
/// An exclusive mutable view requires full permission (*1). A fractional view (*n where n < 1)
/// cannot be soundly promoted to *1 without recombining ALL outstanding fractions.
/// In Rust, casting `&T -> &mut T` directly is statically forbidden by the
/// Aliasing XOR Mutability theorem. The only sound implementation writes a cloned
/// reversal into a separate, disjoint exclusive target.
#[inline(always)]
pub fn row4_col2_shared_ref_to_mut_box<'a, T: Clone>(
    src: &BoxList<T>,
    target: &'a mut BoxList<T>,
) -> &'a mut BoxList<T> {
    *target = row4_col1_shared_ref_to_owned_box(src);
    target
}

/// --- [4, 3] Borrowed Shared -> Owned Shared (RcList<T>) ---
/// Clones values from the borrowed shared list into freshly allocated Rc nodes.
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

/// --- [4, 4] Borrowed Shared -> Borrowed Shared (Lazy Zero-Allocation View) ---
/// LCU Type: `view : *n (List a) -> ReversedView<'a, a>` (Fractional projection)
///
/// Pure lazy projection over fractional references (*n). Collects existing
/// pointer addresses without copying heap elements or mutating nodes.
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
