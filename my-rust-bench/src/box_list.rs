// =========================================================================
// Data Structure: Box-Backed Unique Singly-Linked List
// =========================================================================

pub struct Node<T> {
    pub val: T,
    pub next: Option<Box<Node<T>>>,
}

pub struct BoxList<T> {
    pub head: Option<Box<Node<T>>>,
}

pub type Link<T> = Option<Box<Node<T>>>;

impl<T> Default for BoxList<T> {
    fn default() -> Self {
        BoxList { head: None }
    }
}

impl<T> FromIterator<T> for BoxList<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut head = None;
        for val in iter {
            head = Some(Box::new(Node { val, next: head }));
        }
        BoxList { head }
    }
}

impl<T: Clone> Clone for BoxList<T> {
    fn clone(&self) -> Self {
        let mut elems = Vec::new();
        let mut cur = &self.head;
        while let Some(node) = cur {
            elems.push(node.val.clone());
            cur = &node.next;
        }
        Self::from_iter(elems)
    }
}

// Custom iterative drop to prevent recursion stack overflow on large lists
impl<T> Drop for BoxList<T> {
    fn drop(&mut self) {
        let mut cur = self.head.take();
        while let Some(mut node) = cur {
            cur = node.next.take();
        }
    }
}

// // ==========================================
// // 2. Arena-Backed Linked List (Contiguous Memory)
// // ==========================================
// #[derive(Clone)]
// pub struct ArenaNode<T> {
//     pub val: T,
//     pub next: Option<usize>,
// }
//
// #[derive(Clone)]
// pub struct ArenaList<T> {
//     pub nodes: Vec<ArenaNode<T>>,
//     pub head: Option<usize>,
// }
//
// impl<T> ArenaList<T> {
//     pub fn from_iter(iter: impl IntoIterator<Item = T>) -> Self {
//         let mut nodes = Vec::new();
//         let mut head = None;
//         for (i, val) in iter.into_iter().enumerate() {
//             nodes.push(ArenaNode { val, next: head });
//             head = Some(i);
//         }
//         ArenaList { nodes, head }
//     }
//
//     #[inline(always)]
//     pub fn reverse(&mut self) {
//         let mut acc = None;
//         let mut curr = self.head;
//         while let Some(idx) = curr {
//             let node = unsafe { self.nodes.get_unchecked_mut(idx) };
//             let next = node.next;
//             node.next = acc;
//             acc = Some(idx);
//             curr = next;
//         }
//         self.head = acc;
//     }
// }
