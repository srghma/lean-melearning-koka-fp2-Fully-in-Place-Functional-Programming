use std::rc::Rc;

// =========================================================================
// Data Structure: Reference Counted Singly-Linked List
// =========================================================================
#[derive(Debug)]
pub struct Node<T> {
    pub val: T,
    pub next: Option<Rc<Node<T>>>,
}

pub type Link<T> = Option<Rc<Node<T>>>;

// Wrapper struct with iterative Drop to prevent stack overflow on deep drops
pub struct RcList<T> {
    pub head: Link<T>,
}

impl<T> Drop for RcList<T> {
    fn drop(&mut self) {
        let mut cur = self.head.take();
        while let Some(mut rc_node) = cur {
            dbg_rc!("RcList::drop - inspecting rc_node", rc_node);
            // If we are the sole owner of this Rc, sever 'next' iteratively
            // so recursive Drop does not blow the call stack.
            if let Some(node) = Rc::get_mut(&mut rc_node) {
                cur = node.next.take();
                // Borrow of `node` ends here, safe to inspect rc_node
                dbg_rc!("RcList::drop - sole owner (severed next)", rc_node);
                // Explicitly drop rc_node at the end of the iteration
                drop(rc_node);
            } else {
                dbg_rc!("RcList::drop - shared owner (leaving tail intact)", rc_node);
                // Explicitly drop rc_node before breaking
                drop(rc_node);
                break;
            }
        }
    }
}

impl<T: Clone> Clone for RcList<T> {
    fn clone(&self) -> Self {
        RcList {
            head: self.head.clone(),
        }
    }
}

impl<T> RcList<T> {
    pub fn from_iter(iter: impl IntoIterator<Item = T>) -> Self {
        let mut head = None;
        for val in iter {
            head = Some(Rc::new(Node { val, next: head }));
        }
        RcList { head }
    }
}

// =========================================================================
// 1. While-Based Reverse (Iterative)
// =========================================================================
#[inline(always)]
pub fn reverse_rc_while<T: Clone>(mut xs: Link<T>) -> Link<T> {
    let mut acc: Link<T> = None;

    while let Some(mut rc_node) = xs {
        dbg_rc!("while: rc_node before uniqueness check", rc_node);

        // Rc::get_mut returns Some(&mut Node) ONLY if strong_count == 1.
        // This is the direct equivalent of Koka Perceus 'is-unique(xs)'.
        match Rc::get_mut(&mut rc_node) {
            Some(node) => {
                // --- RC == 1: UNIQUE (IN-PLACE REUSE) ---
                //
                // // 1. Decouple next link from current node
                // xs = node.next.take();
                // // 2. Point current node backward to acc (mutate existing heap cell)
                // node.next = acc;
                //
                // or better just
                xs = std::mem::replace(&mut node.next, acc);
                // Borrow of `node` ends here, safe to inspect rc_node
                dbg_rc!("while: unique (in-place reuse)", rc_node);
                // 3. Accumulate reused Rc without allocating (moves rc_node)
                acc = Some(rc_node);
            }
            None => {
                // --- RC > 1: SHARED (COPY-ON-WRITE FALLBACK) ---
                dbg_rc!("while: shared (COW fallback)", rc_node);
                // 1. Advance xs by cloning pointer (increments next's RC)
                xs = rc_node.next.clone();
                // 2. Allocate a brand-new Rc node for the reversed list
                acc = Some(Rc::new(Node {
                    val: rc_node.val.clone(),
                    next: acc,
                }));
                // rc_node drops here, decrementing its RC back down
                dbg_rc!("while: rc_node before drop", rc_node);
                drop(rc_node);
            }
        }
    }

    acc
}

// =========================================================================
// 2. Tail-Recursive Reverse (Functional FIP Style)
// =========================================================================
#[inline(always)]
pub fn reverse_rc_tail_acc<T: Clone>(xs: Link<T>, acc: Link<T>) -> Link<T> {
    match xs {
        Some(mut rc_node) => {
            dbg_rc!("tail_rec: rc_node before uniqueness check", rc_node);

            // Test uniqueness: is-unique(rc_node)
            match Rc::get_mut(&mut rc_node) {
                Some(node) => {
                    // --- UNIQUE: IN-PLACE REUSE ---
                    //
                    // let next = node.next.take();
                    // node.next = acc;
                    //
                    // or better just
                    let next = std::mem::replace(&mut node.next, acc);
                    // Borrow of `node` ends here, safe to inspect rc_node
                    dbg_rc!("tail_rec: unique (in-place reuse)", rc_node);
                    // Tail call with the reused node (moves next and rc_node)
                    reverse_rc_tail_acc(next, Some(rc_node))
                }
                None => {
                    // --- SHARED: COPY-ON-WRITE ---
                    dbg_rc!("tail_rec: shared (COW fallback)", rc_node);
                    let next = rc_node.next.clone();
                    let val = rc_node.val.clone();

                    // CRITICAL FOR TCO:
                    // Explicitly drop rc_node BEFORE the tail call.
                    // If rc_node is not dropped here, its destructor must run after
                    // the recursive call returns, which would PREVENT tail-call elimination!
                    dbg_rc!("tail_rec: rc_node before explicit drop", rc_node);
                    drop(rc_node);

                    let new_node = Rc::new(Node { val, next: acc });
                    dbg_rc!("tail_rec: allocated new_node", new_node);
                    reverse_rc_tail_acc(next, Some(new_node))
                }
            }
        }
        None => acc,
    }
}

#[inline(always)]
pub fn reverse_rc_tail<T: Clone>(xs: Link<T>) -> Link<T> {
    reverse_rc_tail_acc(xs, None)
}
