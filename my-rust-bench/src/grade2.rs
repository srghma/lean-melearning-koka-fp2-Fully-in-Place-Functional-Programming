// -- This will FAIL to type-check
// broken : (List Int, List Int)
// broken =
//   let tail = Next 2 (Next 3 Empty)
//   in (Next 1 tail, Next 11 tail)
//
// shareJoin : (List Int, List Int)
// shareJoin =
//   let [tail] : (List Int) [2] = [Next 2 (Next 3 Empty)]
//   in (Next 1 tail, Next 11 tail)

use std::sync::atomic::{AtomicBool, Ordering};
use std::ptr::NonNull;
use std::ops::Deref;

// The shared heap node
struct SharedInner<T> {
    data: T,
    // false = both handles alive
    // true  = one handle has already been dropped
    other_dropped: AtomicBool,
}

// An affine handle.
// NOTE: We deliberately DO NOT implement `Clone`!
pub struct DualRc<T> {
    ptr: NonNull<SharedInner<T>>,
}

// Thread-safety bounds (like Arc)
unsafe impl<T: Send + Sync> Send for DualRc<T> {}
unsafe impl<T: Send + Sync> Sync for DualRc<T> {}

impl<T> DualRc<T> {
    /// Granule: [x] : [T] [2] -> (T, T)
    /// Construct the resource and produce exactly 2 handles.
    pub fn new_pair(data: T) -> (DualRc<T>, DualRc<T>) {
        let boxed = Box::new(SharedInner {
            data,
            other_dropped: AtomicBool::new(false),
        });

        let ptr = NonNull::new(Box::into_raw(boxed)).unwrap();

        (DualRc { ptr }, DualRc { ptr })
    }
}

impl<T> Deref for DualRc<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        unsafe { &self.ptr.as_ref().data }
    }
}

impl<T> Drop for DualRc<T> {
    fn drop(&mut self) {
        unsafe {
            // swap `true` into other_dropped.
            // If the old value was already `true`, it means we are the second
            // handle to drop -> free the memory.
            if self.ptr.as_ref().other_dropped.swap(true, Ordering::AcqRel) {
                drop(Box::from_raw(self.ptr.as_ptr()));
            }
        }
    }
}

enum List<T> {
    Empty,
    Next(T, ListTail<T>),
}

enum ListTail<T> {
    Owned(Box<List<T>>),
    Shared(DualRc<List<T>>), // Branching node
}

fn main() {
    // 1. Create the shared tail: 2 -> 3 -> Empty
    let tail = List::Next(
        2,
        ListTail::Owned(Box::new(List::Next(3, ListTail::Owned(Box::new(List::Empty)))))
    );

    // 2. Graded unbox: split into EXACTLY 2 handles
    let (tail_a, tail_b) = DualRc::new_pair(tail);

    // 3. Node 1 and Node 11 share Node 2
    let list_one    = List::Next(1,  ListTail::Shared(tail_a));
    let list_eleven = List::Next(11, ListTail::Shared(tail_b));

    // Neither list_one nor list_eleven can clone their pointer to node 2.
    // The reference count cannot exceed 2 at compile-time.
}

// pub struct GradedRc<T, const USES: usize> {
//     ptr: NonNull<SharedInner<T>>,
// }
//
// impl<T> GradedRc<T, 2> {
//     // Grade splitting: [2] -> [1] + [1]
//     pub fn split(self) -> (GradedRc<T, 1>, GradedRc<T, 1>) {
//         let p = self.ptr;
//         std::mem::forget(self); // don't run drop on the [2] capability
//         (GradedRc { ptr: p }, GradedRc { ptr: p })
//     }
// }
//
// impl<T> GradedRc<T, 1> {
//     // Terminal handle: cannot be split!
//     // Can only be read (&T) or dropped.
// }
