use crate::box_list::Link;

// =========================================================================
// reverse : List a {Unique} -> List a {Unique}
// (Box-backed unique list -> Box-backed unique list)
// =========================================================================

// 1. Iterative while-let version
#[inline(always)]
pub fn reverse_box_to_box_while<T>(mut xs: Link<T>) -> Link<T> {
    let mut acc = None;
    while let Some(mut node) = xs {
        // // 1. Decouple next link from current node
        // xs = node.next.take();
        // // 2. Point current node backward to acc (mutate existing heap cell)
        // node.next = acc;
        //
        // or better just:
        xs = std::mem::replace(&mut node.next, acc);
        acc = Some(node);
    }
    acc
}

// 2. Tail-Recursive Reverse (Functional FIP Style)
#[inline(always)]
pub fn reverse_box_to_box_tail_acc<T>(xs: Link<T>, acc: Link<T>) -> Link<T> {
    match xs {
        Some(mut node) => {
            // // 1. Decouple next link from current node
            // let next = node.next.take();
            // // 2. Point current node backward to acc
            // node.next = acc;
            //
            // or better just:
            let next = std::mem::replace(&mut node.next, acc);
            reverse_box_to_box_tail_acc(next, Some(node))
        }
        None => acc,
    }
}

#[inline(always)]
pub fn reverse_box_to_box_tail<T>(xs: Link<T>) -> Link<T> {
    reverse_box_to_box_tail_acc(xs, None)
}
