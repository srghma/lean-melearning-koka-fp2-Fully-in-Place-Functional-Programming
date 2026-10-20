use crate::box_list::{BoxList, Link as BoxLink, Node as BoxNode};
use crate::rc_list::{Link as RcLink, Node as RcNode, RcList};
use std::rc::Rc;

// =========================================================================
// reverse : List a -> List a {Unique}
// (Rc-backed shared list -> Box-backed unique list)
// =========================================================================

/// Unwraps an Rc node: moves (val, next) with 0 atomic updates if unique,
/// or clones (val, next) when shared.
#[inline(always)]
fn unwrap_rc_node<T: Clone>(rc_node: Rc<RcNode<T>>) -> (T, RcLink<T>) {
    crate::dbg_rc!("rc_to_box: inspecting rc_node", rc_node);
    match Rc::try_unwrap(rc_node) {
        Ok(mut unique) => (unique.val, unique.next.take()),
        Err(shared) => (shared.val.clone(), shared.next.clone()),
    }
}

// 1. While-Based Reverse (Iterative)
#[inline(always)]
pub fn reverse_rc_to_box_while<T: Clone>(mut xs: RcLink<T>) -> BoxLink<T> {
    let mut acc: BoxLink<T> = None;
    while let Some(rc_node) = xs {
        let (val, next) = unwrap_rc_node(rc_node);
        xs = next;
        acc = Some(Box::new(BoxNode { val, next: acc }));
    }
    acc
}

// 2. Tail-Recursive Reverse (Functional FIP Style)
#[inline(always)]
pub fn reverse_rc_to_box_tail_acc<T: Clone>(xs: RcLink<T>, acc: BoxLink<T>) -> BoxLink<T> {
    match xs {
        Some(rc_node) => {
            let (val, next) = unwrap_rc_node(rc_node);
            reverse_rc_to_box_tail_acc(next, Some(Box::new(BoxNode { val, next: acc })))
        }
        None => acc,
    }
}

#[inline(always)]
pub fn reverse_rc_to_box_tail<T: Clone>(xs: RcLink<T>) -> BoxLink<T> {
    reverse_rc_to_box_tail_acc(xs, None)
}

#[inline(always)]
pub fn rc_to_box_reversed<T: Clone>(rc_list: &RcList<T>) -> BoxList<T> {
    BoxList {
        head: reverse_rc_to_box_tail(rc_list.head.clone()),
    }
}
