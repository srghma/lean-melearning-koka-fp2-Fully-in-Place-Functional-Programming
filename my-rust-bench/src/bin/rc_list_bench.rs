use std::rc::Rc;
use easybench::bench_env;

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
            // If we are the sole owner of this Rc, sever 'next' iteratively
            // so recursive Drop does not blow the call stack.
            if let Some(node) = Rc::get_mut(&mut rc_node) {
                cur = node.next.take();
                // Explicitly drop rc_node at the end of the iteration
                // drop(rc_node);
            } else {
                // Explicitly drop rc_node before breaking
                // drop(rc_node);
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
        // Rc::get_mut returns Some(&mut Node) ONLY if strong_count == 1.
        // This is the direct equivalent of Koka Perceus 'is-unique(xs)'.
        match Rc::get_mut(&mut rc_node) {
            Some(node) => {
                // --- RC == 1: UNIQUE (IN-PLACE REUSE) ---
                // 1. Decouple next link from current node
                xs = node.next.take();
                // 2. Point current node backward to acc (mutate existing heap cell)
                node.next = acc;
                // 3. Accumulate reused Rc without allocating (moves rc_node)
                acc = Some(rc_node);
            }
            None => {
                // --- RC > 1: SHARED (COPY-ON-WRITE FALLBACK) ---
                // 1. Advance xs by cloning pointer (increments next's RC)
                xs = rc_node.next.clone();
                // 2. Allocate a brand-new Rc node for the reversed list
                acc = Some(Rc::new(Node {
                    val: rc_node.val.clone(),
                    next: acc,
                }));
                // rc_node drops here, decrementing its RC back down
                // drop(rc_node);
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
            // Test uniqueness: is-unique(rc_node)
            match Rc::get_mut(&mut rc_node) {
                Some(node) => {
                    // --- UNIQUE: IN-PLACE REUSE ---
                    let next = node.next.take();
                    node.next = acc;
                    // Tail call with the reused node (moves next and rc_node)
                    reverse_rc_tail_acc(next, Some(rc_node))
                }
                None => {
                    // --- SHARED: COPY-ON-WRITE ---
                    let next = rc_node.next.clone();
                    let val = rc_node.val.clone();

                    // CRITICAL FOR TCO:
                    // Explicitly drop rc_node BEFORE the tail call.
                    // If rc_node is not dropped here, its destructor must run after
                    // the recursive call returns, which would PREVENT tail-call elimination!
                    drop(rc_node);

                    let new_node = Rc::new(Node { val, next: acc });
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

// =========================================================================
// Verification & Benchmarking
// =========================================================================
fn main() {
    println!("=== 1. Memory Address Verification (Copy-on-Write Trace) ===");
    {
        // Construct shared tail: 2 -> 3 -> Nil
        let node3 = Rc::new(Node { val: 3, next: None });
        let node2 = Rc::new(Node { val: 2, next: Some(node3.clone()) });

        // list1 = 1 -> 2 -> 3
        let list1 = Some(Rc::new(Node { val: 1, next: Some(node2.clone()) }));
        // list2 = 11 -> 2 -> 3 (shares node2 and node3)
        let list2 = Some(Rc::new(Node { val: 11, next: Some(node2.clone()) }));

        println!("Before reverse:");
        println!("  list1 Node 1 address : {:p} (RC: 1)", list1.as_ref().unwrap());
        println!("  shared  Node 2 address : {:p} (RC: 2)", node2);
        println!("  shared  Node 3 address : {:p} (RC: 2)", node3);

        // list1 is moved here into reverse_rc_tail
        let reversed = reverse_rc_tail(list1);

        println!("\nAfter reverse (tail-rec):");
        let r3 = reversed.as_ref().unwrap();
        let r2 = r3.next.as_ref().unwrap();
        let r1 = r2.next.as_ref().unwrap();

        println!("  reversed Node 3' address: {:p} (NEW via COW)", r3);
        println!("  reversed Node 2' address: {:p} (NEW via COW)", r2);
        println!("  reversed Node 1  address: {:p} (REUSED IN-PLACE!)", r1);

        println!("\nPreserved list2:");
        println!("  list2 -> Node 2 address : {:p} (UNTOUCHED)",
            list2.as_ref().unwrap().next.as_ref().unwrap());

        // Explicit drops for remaining scope variables (in reverse declaration order)
        // drop(reversed);
        // drop(list2);
        // drop(node2);
        // drop(node3);
    }

    println!("\n=== 2. Benchmarks: 100% Unique (Pure In-Place) vs 100% Shared (Pure COW) ===");
    let sizes = [100, 1_000, 10_000];

    for &n in &sizes {
        println!("\n--- Size: {n} ---");

        // Scenario A: 100% Unique list (every node has RC == 1)
        let unique_list: RcList<i32> = RcList::from_iter(0..n);

        let unique_while = bench_env(unique_list.clone(), |l| {
            let owned = std::mem::replace(&mut l.head, None);
            l.head = reverse_rc_while(owned);
            l.head.as_ref().map(|node| node.val)
        });

        let unique_tail = bench_env(unique_list.clone(), |l| {
            let owned = std::mem::replace(&mut l.head, None);
            l.head = reverse_rc_tail(owned);
            l.head.as_ref().map(|node| node.val)
        });

        println!("Unique (In-Place) While   : {unique_while}");
        println!("Unique (In-Place) Tail-Rec: {unique_tail}");

        // Scenario B: 100% Shared list (keep an external clone alive so RC == 2 for all nodes)
        let shared_list_root = RcList::from_iter(0..n);
        // This persistent reference keeps all node RCs >= 2
        let _keep_alive = shared_list_root.clone();

        let cow_while = bench_env(shared_list_root.clone(), |l| {
            let owned = std::mem::replace(&mut l.head, None);
            l.head = reverse_rc_while(owned);
            l.head.as_ref().map(|node| node.val)
        });

        let cow_tail = bench_env(shared_list_root.clone(), |l| {
            let owned = std::mem::replace(&mut l.head, None);
            l.head = reverse_rc_tail(owned);
            l.head.as_ref().map(|node| node.val)
        });

        println!("Shared (COW Malloc) While : {cow_while}");
        println!("Shared (COW Malloc) Tail  : {cow_tail}");

        // Explicit drops at the end of each iteration
        // drop(cow_tail);
        // drop(cow_while);
        // drop(_keep_alive);
        // drop(shared_list_root);
        // drop(unique_tail);
        // drop(unique_while);
        // drop(unique_list);
    }
}
