use std::sync::Arc;

// =========================================================================
// Data Structure: Atomically Reference Counted Singly-Linked List (Thread-Safe)
// =========================================================================

#[derive(Debug)]
pub struct Node<T> {
    pub val: T,
    pub next: Option<Arc<Node<T>>>,
}

pub type Link<T> = Option<Arc<Node<T>>>;

/// Wrapper struct with an iterative Drop to prevent call-stack overflow on deep lists.
///
/// Automatically implements `Send` and `Sync` whenever `T: Send + Sync`.
#[derive(Debug)]
pub struct ArcList<T> {
    pub head: Link<T>,
}

impl<T> Default for ArcList<T> {
    #[inline]
    fn default() -> Self {
        ArcList { head: None }
    }
}

impl<T> Drop for ArcList<T> {
    fn drop(&mut self) {
        let mut cur = self.head.take();
        while let Some(mut arc_node) = cur {
            // Arc::get_mut returns Some(&mut Node) ONLY if:
            // strong_count == 1 AND weak_count == 0 (with Acquire memory ordering).
            //
            // If we are the sole owner of this Arc, sever 'next' iteratively
            // so recursive Drop does not blow the call stack.
            if let Some(node) = Arc::get_mut(&mut arc_node) {
                cur = node.next.take();
                // Borrow of `node` ends here
                drop(arc_node);
            } else {
                // If strong_count > 1, another thread or handle still references
                // this tail. Decrement the atomic count and break without recursing.
                drop(arc_node);
                break;
            }
        }
    }
}

impl<T> Clone for ArcList<T> {
    #[inline]
    fn clone(&self) -> Self {
        ArcList {
            head: self.head.clone(),
        }
    }
}

impl<T> FromIterator<T> for ArcList<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut head = None;
        for val in iter {
            head = Some(Arc::new(Node { val, next: head }));
        }
        ArcList { head }
    }
}
