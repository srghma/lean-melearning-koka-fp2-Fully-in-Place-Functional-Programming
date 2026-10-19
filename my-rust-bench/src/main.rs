use easybench::bench_env;

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

// 1. Inlined Tail-Recursive version
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

fn main() {
    let sizes = [100, 1_000, 10_000];

    for &n in &sizes {
        println!("=== List Size: {n} ===");
        let list: List<i32> = List::from_iter(0..n);

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

        println!("tail-rec (inlined): {rec_stat}");
        println!("iterative (while):  {iter_stat}\n");
    }
}


// #[no_mangle]
// pub fn bench_rec(xs: Link<i32>) -> Link<i32> {
//     reverse_acc(xs, None)
// }
//
// #[no_mangle]
// pub fn bench_iter(mut xs: Link<i32>) -> Link<i32> {
//     let mut acc = None;
//     while let Some(mut node) = xs {
//         xs = std::mem::replace(&mut node.next, acc);
//         acc = Some(node);
//     }
//     acc
// }
