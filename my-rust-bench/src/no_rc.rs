// ==========================================
// 1. Boxed Singly-Linked List
// ==========================================
pub struct Node<T> {
    pub val: T,
    pub next: Option<Box<Node<T>>>,
}

pub struct List<T> {
    pub head: Option<Box<Node<T>>>,
}

impl<T> Default for List<T> {
    fn default() -> Self {
        List { head: None }
    }
}

pub type Link<T> = Option<Box<Node<T>>>;

#[inline(always)]
fn reverse_acc<T>(xs: Link<T>, acc: Link<T>) -> Link<T> {
    match xs {
        Some(mut node) => {
            let next = node.next.take();
            node.next = acc;
            reverse_acc(next, Some(node))
        }
        None => acc,
    }
}

impl<T> List<T> {
    #[inline(always)]
    pub fn reverse_rec(mut self) -> Self {
        let xs = self.head.take();
        List {
            head: reverse_acc(xs, None),
        }
    }

    // 2. Iterative while-let version
    #[inline(always)]
    pub fn reverse_iter(mut self) -> Self {
        let mut acc = None;
        let mut xs = self.head.take();
        while let Some(mut node) = xs {
            xs = std::mem::replace(&mut node.next, acc);
            acc = Some(node);
        }
        List { head: acc }
    }

    #[inline(always)]
    pub fn from_iter(iter: impl IntoIterator<Item = T>) -> Self {
        let mut head = None;
        for val in iter {
            head = Some(Box::new(Node { val, next: head }));
        }
        List { head }
    }
}

impl<T: Clone> Clone for List<T> {
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
impl<T> Drop for List<T> {
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
