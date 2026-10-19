use easybench::bench_env;

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

type Link<T> = Option<Box<Node<T>>>;

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

// ==========================================
// Benchmark Harness
// ==========================================
fn main() {
    let sizes = [100, 1_000, 10_000];

    for &n in &sizes {
        println!("=== List Size: {n} ===");
        let list: List<i32> = List::from_iter(0..n);
        // let arena_list: ArenaList<i32> = ArenaList::from_iter(0..n);
        let vec: Vec<i32> = (0..n).collect();

        let rec_stat = bench_env(list.clone(), |l| {
            let owned = std::mem::take(l);
            *l = owned.reverse_rec();
            l.head.as_ref().map(|node| node.val)
        });

        let iter_stat = bench_env(list.clone(), |l| {
            let owned = std::mem::take(l);
            *l = owned.reverse_iter();
            l.head.as_ref().map(|node| node.val)
        });

        // let arena_stat = bench_env(arena_list.clone(), |al| {
        //     al.reverse();
        //     al.head.map(|idx| al.nodes[idx].val)
        // });

        let vec_stat = bench_env(vec.clone(), |v| {
            v.reverse();
            v.first().copied()
        });

        println!("tail-rec (inlined):   {rec_stat}");
        println!("iterative (while):    {iter_stat}");
        // println!("arena-linked-list:    {arena_stat}");
        println!("vec (slice::reverse): {vec_stat}\n");
    }
}
