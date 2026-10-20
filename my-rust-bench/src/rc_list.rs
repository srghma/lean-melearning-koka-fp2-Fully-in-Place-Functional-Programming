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

impl<T> FromIterator<T> for RcList<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut head = None;
        for val in iter {
            head = Some(Rc::new(Node { val, next: head }));
        }
        RcList { head }
    }
}
