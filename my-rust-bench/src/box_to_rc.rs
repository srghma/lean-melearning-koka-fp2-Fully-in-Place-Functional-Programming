use crate::box_list::{BoxList, Link as BoxLink};
use crate::rc_list::{Link as RcLink, Node as RcNode, RcList};
use std::rc::Rc;

// =========================================================================
// reverse : List a {Unique} -> List a
// (Box-backed unique list -> Rc-backed shared list)
// =========================================================================

// 1. While-Based Reverse (Iterative)
#[inline(always)]
pub fn reverse_box_to_rc_while<T>(mut xs: BoxLink<T>) -> RcLink<T> {
    let mut acc: RcLink<T> = None;
    while let Some(mut box_node) = xs {
        xs = box_node.next.take();
        acc = Some(Rc::new(RcNode {
            val: box_node.val,
            next: acc,
        }));
    }
    acc
}

// 2. Tail-Recursive Reverse (Functional FIP Style)
#[inline(always)]
pub fn reverse_box_to_rc_tail_acc<T>(xs: BoxLink<T>, acc: RcLink<T>) -> RcLink<T> {
    match xs {
        Some(mut box_node) => {
            let next = box_node.next.take();
            let new_rc = Some(Rc::new(RcNode {
                val: box_node.val,
                next: acc,
            }));
            reverse_box_to_rc_tail_acc(next, new_rc)
        }
        None => acc,
    }
}

#[inline(always)]
pub fn reverse_box_to_rc_tail<T>(xs: BoxLink<T>) -> RcLink<T> {
    reverse_box_to_rc_tail_acc(xs, None)
}

#[inline(always)]
pub fn box_to_rc_reversed<T>(mut box_list: BoxList<T>) -> RcList<T> {
    RcList {
        head: reverse_box_to_rc_tail(box_list.head.take()),
    }
}
