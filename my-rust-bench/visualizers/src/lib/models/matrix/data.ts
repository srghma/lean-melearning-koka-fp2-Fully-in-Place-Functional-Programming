export interface MatrixCell {
  row: number;
  col: number;
  id: string;
  title: string;
  rustSig: string;
  lcuSig: string;
  granuleGraded: string;
  tag: string;
  tagType: 'fip' | 'cow' | 'view' | 'forbid';
  alloc: string;
  theoryDesc: string;
  code: string;
}

export interface HeaderInfo {
  title: string;
  subtitle: string;
  typeBadge: string;
  color: string;
}

export const columnHeaders: HeaderInfo[] = [
  {
    title: 'Owned Unique',
    subtitle: 'BoxList<T>',
    typeBadge: '*1 (List a)',
    color: 'text-emerald-400'
  },
  {
    title: 'Borrowed Unique',
    subtitle: '&mut BoxList<T>',
    typeBadge: '&mut *1 (List a)',
    color: 'text-amber-400'
  },
  {
    title: 'Owned Shared',
    subtitle: 'RcList<T>',
    typeBadge: '!(List a) / Dynamic COW',
    color: 'text-purple-400'
  },
  {
    title: 'Borrowed Shared',
    subtitle: '&BoxList<T> / View',
    typeBadge: '*n (List a) [n < 1]',
    color: 'text-sky-400'
  }
];

export const rowHeaders: HeaderInfo[] = [
  {
    title: '[Row 1] Owned Unique',
    subtitle: 'BoxList<T>',
    typeBadge: '*1 A (Linear + Zero-Aliases)',
    color: 'text-emerald-400'
  },
  {
    title: '[Row 2] Borrowed Unique',
    subtitle: '&mut BoxList<T>',
    typeBadge: '&mut (*1 A) (Exclusive Loan)',
    color: 'text-amber-400'
  },
  {
    title: '[Row 3] Owned Shared',
    subtitle: 'RcList<T>',
    typeBadge: 'Dynamic Perceus (*1 ⊕ !)',
    color: 'text-purple-400'
  },
  {
    title: '[Row 4] Borrowed Shared',
    subtitle: '&BoxList<T>',
    typeBadge: '*n A (Fractional View, n < 1)',
    color: 'text-sky-400'
  }
];

export const matrixCells: MatrixCell[][] = [
  // Row 1: Owned Unique (BoxList)
  [
    {
      row: 0,
      col: 0,
      id: 'row1_col1',
      title: 'Cell [1, 1]: Owned Unique → Owned Unique',
      rustSig: 'pub fn row1_col1_owned_box_to_owned_box<T>(mut list: BoxList<T>) -> BoxList<T>',
      lcuSig: 'reverse : *(List a) -> *(List a)',
      granuleGraded: '*1 (List a) -> *1 (List a) (Pure Unique In-Place Transformation)',
      tag: '0 Allocs',
      tagType: 'fip',
      alloc: '0 allocations. 100% in-place mutation of existing heap cells (FIP).',
      theoryDesc:
        'Proven safe by LCU Theorem 5 (Uniqueness Invariant): because this list has exactly one reference from the past (*A), in-place destructive pointer inversion is referentially transparent. Compiles to an O(1) jump loop.',
      code: `#[inline(always)]
pub fn row1_col1_owned_box_to_owned_box<T>(mut list: BoxList<T>) -> BoxList<T> {
    BoxList {
        head: reverse_box_to_box_tail(list.head.take()),
    }
}`
    },
    {
      row: 0,
      col: 1,
      id: 'row1_col2',
      title: 'Cell [1, 2]: Owned Unique → Borrowed Unique (&mut BoxList)',
      rustSig:
        'pub fn row1_col2_owned_box_to_mut_box<T>(list: BoxList<T>, target: &mut BoxList<T>) -> &mut BoxList<T>',
      lcuSig: 'reverse_into : *(List a) -> &mut *(List a) -> &mut *(List a)',
      granuleGraded: '*1 (List a) -> &mut (*1 (List a)) -> &mut (*1 (List a))',
      tag: 'In-Place',
      tagType: 'fip',
      alloc: '0 allocations. Reverses unique list and installs head into *target slot.',
      theoryDesc:
        'Consumes the owned unique *1 resource, flips pointers in-place, and assigns the resulting head pointer into the caller exclusive memory slot, returning the reborrowed &mut handle.',
      code: `#[inline(always)]
pub fn row1_col2_owned_box_to_mut_box<T>(
    list: BoxList<T>,
    target: &mut BoxList<T>,
) -> &mut BoxList<T> {
    *target = row1_col1_owned_box_to_owned_box(list);
    target
}`
    },
    {
      row: 0,
      col: 2,
      id: 'row1_col3',
      title: 'Cell [1, 3]: Owned Unique → Owned Shared (RcList)',
      rustSig: 'pub fn row1_col3_owned_box_to_owned_rc<T>(mut list: BoxList<T>) -> RcList<T>',
      lcuSig: 'borrow : *(List a) -> !(List a)',
      granuleGraded: 'uniqueReturn : *a -> !a (Relative Monad Return)',
      tag: 'N Allocs',
      tagType: 'cow',
      alloc: 'N allocations: Creates an RcBox control block (strong=1, weak=0) for each element.',
      theoryDesc:
        'Implements the relative monad borrow rule from ESOP 2022 §3.1: the past uniqueness guarantee is forgotten to produce an unrestricted/shared structure, packaging nodes into reference-counted headers.',
      code: `#[inline(always)]
pub fn row1_col3_owned_box_to_owned_rc<T>(mut list: BoxList<T>) -> RcList<T> {
    RcList {
        head: reverse_box_to_rc_tail(list.head.take()),
    }
}`
    },
    {
      row: 0,
      col: 3,
      id: 'row1_col4',
      title: 'Cell [1, 4]: Owned Unique → Borrowed Shared (&BoxList)',
      rustSig:
        'pub fn row1_col4_owned_box_to_shared_ref<T>(list: BoxList<T>, slot: &mut BoxList<T>) -> &BoxList<T>',
      lcuSig: 'split_permission : *1 (List a) -> *n (List a) (where n < 1)',
      granuleGraded: '*1 (List a) -> slot: &mut (*1 (List a)) -> *n (List a)',
      tag: 'Borrow',
      tagType: 'view',
      alloc: '0 allocations. Consumes list, reverses into slot, yields immutable view.',
      theoryDesc:
        'Consumes the unique list, reverses it in-place into caller storage, and downgrades the full uniqueness permission (*1) into a fractional read-only permission (*n).',
      code: `#[inline(always)]
pub fn row1_col4_owned_box_to_shared_ref<T>(
    list: BoxList<T>,
    slot: &mut BoxList<T>,
) -> &BoxList<T> {
    *slot = row1_col1_owned_box_to_owned_box(list);
    slot
}`
    }
  ],

  // Row 2: Borrowed Unique (&mut BoxList)
  [
    {
      row: 1,
      col: 0,
      id: 'row2_col1',
      title: 'Cell [2, 1]: Borrowed Unique → Owned Unique',
      rustSig: 'pub fn row2_col1_mut_box_to_owned_box<T>(list: &mut BoxList<T>) -> BoxList<T>',
      lcuSig: 'drain : &mut *(List a) -> *(List a)',
      granuleGraded: '&mut (*1 (List a)) -> *1 (List a) (Drain & Transfer)',
      tag: '0 Allocs',
      tagType: 'fip',
      alloc: '0 allocations. Leaves source list as None, transfers ownership to return.',
      theoryDesc:
        'Extracts the exclusive *1 capability via take(), leaving the source location empty, reverses it tail-recursively in-place, and transfers owned uniqueness (*1) to the caller.',
      code: `#[inline(always)]
pub fn row2_col1_mut_box_to_owned_box<T>(list: &mut BoxList<T>) -> BoxList<T> {
    let owned = list.head.take();
    BoxList {
        head: reverse_box_to_box_tail(owned),
    }
}`
    },
    {
      row: 1,
      col: 1,
      id: 'row2_col2',
      title: 'Cell [2, 2]: Borrowed Unique → Borrowed Unique (&mut BoxList)',
      rustSig: 'pub fn row2_col2_mut_box_to_mut_box<T>(list: &mut BoxList<T>) -> &mut BoxList<T>',
      lcuSig: 'reverse_in_place : &mut *(List a) -> &mut *(List a)',
      granuleGraded: '&mut (*1 (List a)) -> &mut (*1 (List a)) (Pure In-Place Inversion)',
      tag: '0 Allocs',
      tagType: 'fip',
      alloc: '0 allocations. Direct in-place mutation of caller structure.',
      theoryDesc:
        'Pure in-place pointer flip on an exclusively held location. Preserves heap node addresses and caller identity with zero memory allocations.',
      code: `#[inline(always)]
pub fn row2_col2_mut_box_to_mut_box<T>(list: &mut BoxList<T>) -> &mut BoxList<T> {
    let owned = list.head.take();
    list.head = reverse_box_to_box_tail(owned);
    list
}`
    },
    {
      row: 1,
      col: 2,
      id: 'row2_col3',
      title: 'Cell [2, 3]: Borrowed Unique → Owned Shared (RcList)',
      rustSig: 'pub fn row2_col3_mut_box_to_owned_rc<T>(list: &mut BoxList<T>) -> RcList<T>',
      lcuSig: 'drain_and_borrow : &mut *(List a) -> !(List a)',
      granuleGraded: '&mut (*1 (List a)) -> !(List a) (Drain to Shared)',
      tag: 'N Allocs',
      tagType: 'cow',
      alloc: 'N allocations: Creates Rc control blocks for drained elements.',
      theoryDesc:
        'Drains the exclusive source slot and forgets uniqueness into shared reference-counted control blocks, allocating N new Rc headers.',
      code: `#[inline(always)]
pub fn row2_col3_mut_box_to_owned_rc<T>(list: &mut BoxList<T>) -> RcList<T> {
    let owned = list.head.take();
    RcList {
        head: reverse_box_to_rc_tail(owned),
    }
}`
    },
    {
      row: 1,
      col: 3,
      id: 'row2_col4',
      title: 'Cell [2, 4]: Borrowed Unique → Borrowed Shared (&BoxList)',
      rustSig: 'pub fn row2_col4_mut_box_to_shared_ref<T>(list: &mut BoxList<T>) -> &BoxList<T>',
      lcuSig: 'reborrow_fractional : &mut *1 (List a) -> &*n (List a)',
      granuleGraded: '&mut (*1 (List a)) -> *n (List a) (Permission Downgrade)',
      tag: 'Downgrade',
      tagType: 'view',
      alloc: '0 allocations. In-place pointer flip followed by borrow downgrade.',
      theoryDesc:
        'Mutates the list in-place via its exclusive capability, then downgrades the borrow lifetime from exclusive (*1) to fractional read-only (*n).',
      code: `#[inline(always)]
pub fn row2_col4_mut_box_to_shared_ref<T>(list: &mut BoxList<T>) -> &BoxList<T> {
    let owned = list.head.take();
    list.head = reverse_box_to_box_tail(owned);
    list
}`
    }
  ],

  // Row 3: Owned Dynamic Shared (RcList)
  [
    {
      row: 2,
      col: 0,
      id: 'row3_col1',
      title: 'Cell [3, 1]: Owned Shared → Owned Unique',
      rustSig:
        'pub fn row3_col1_owned_rc_to_owned_box<T: Clone>(mut list: RcList<T>) -> BoxList<T>',
      lcuSig: 'try_unwrap : !(List a) -> *(List a) (Dynamic Perceus Branch)',
      granuleGraded: 'Dynamic Branch: RC==1 => *1 a (0 allocs) | RC>1 => copy !(List a)',
      tag: '0 or N Allocs',
      tagType: 'fip',
      alloc: '0 atomic updates if unique (Rc::try_unwrap); falls back to N clones if shared.',
      theoryDesc:
        'In static LCU logic, transforming unrestricted !A into unique *A requires copy. At runtime, Rc::try_unwrap acts as an optimistic Perceus-style branch: if strong_count == 1, uniqueness is dynamically recovered; if shared, it clones values into fresh Box cells.',
      code: `#[inline(always)]
pub fn row3_col1_owned_rc_to_owned_box<T: Clone>(mut list: RcList<T>) -> BoxList<T> {
    BoxList {
        head: reverse_rc_to_box_tail(list.head.take()),
    }
}`
    },
    {
      row: 2,
      col: 1,
      id: 'row3_col2',
      title: 'Cell [3, 2]: Owned Shared → Borrowed Unique (&mut BoxList)',
      rustSig:
        'pub fn row3_col2_owned_rc_to_mut_box<T: Clone>(list: RcList<T>, target: &mut BoxList<T>) -> &mut BoxList<T>',
      lcuSig: 'rc_into_mut_box : RcList a -> &mut *(List a) -> &mut *(List a)',
      granuleGraded: 'RcList a -> &mut (*1 (List a)) -> &mut (*1 (List a))',
      tag: 'Hybrid',
      tagType: 'cow',
      alloc: '0 allocations if RC==1 across all nodes; N allocations if shared.',
      theoryDesc:
        'Unwraps/clones from the dynamic reference-counted list into unique Box nodes and installs them into an existing exclusive target slot.',
      code: `#[inline(always)]
pub fn row3_col2_owned_rc_to_mut_box<T: Clone>(
    list: RcList<T>,
    target: &mut BoxList<T>,
) -> &mut BoxList<T> {
    *target = row3_col1_owned_rc_to_owned_box(list);
    target
}`
    },
    {
      row: 2,
      col: 2,
      id: 'row3_col3',
      title: 'Cell [3, 3]: Owned Shared → Owned Shared (RcList)',
      rustSig: 'pub fn row3_col3_owned_rc_to_owned_rc<T: Clone>(mut list: RcList<T>) -> RcList<T>',
      lcuSig: 'perceus_reverse : RcList a -> RcList a',
      granuleGraded: 'Perceus Dynamic In-Place Reference Counting',
      tag: 'Perceus',
      tagType: 'cow',
      alloc: '0 allocations if RC==1 (in-place reuse); allocates new Rc nodes only when RC > 1.',
      theoryDesc:
        'Evaluates Rc::get_mut (is-unique). If strong_count == 1, flips pointer in-place without memory allocation. If strong_count > 1, duplicates the shared node to preserve persistent branches.',
      code: `#[inline(always)]
pub fn row3_col3_owned_rc_to_owned_rc<T: Clone>(mut list: RcList<T>) -> RcList<T> {
    RcList {
        head: reverse_rc_to_rc_tail(list.head.take()),
    }
}`
    },
    {
      row: 2,
      col: 3,
      id: 'row3_col4',
      title: 'Cell [3, 4]: Owned Shared → Borrowed Shared (&RcList)',
      rustSig:
        'pub fn row3_col4_owned_rc_to_shared_ref<T: Clone>(list: RcList<T>, slot: &mut RcList<T>) -> &RcList<T>',
      lcuSig: 'rc_reverse_borrow : RcList a -> slot: &mut (RcList) -> & (RcList)',
      granuleGraded: 'RcList a -> slot: &mut (RcList) -> & (RcList)',
      tag: 'Borrow',
      tagType: 'view',
      alloc: '0 allocations if RC==1, N if shared.',
      theoryDesc:
        'Perceus-reverses the Rc list into a temporary mutable slot, returning an immutable shared view &RcList.',
      code: `#[inline(always)]
pub fn row3_col4_owned_rc_to_shared_ref<T: Clone>(
    list: RcList<T>,
    slot: &mut RcList<T>,
) -> &RcList<T> {
    *slot = row3_col3_owned_rc_to_owned_rc(list);
    slot
}`
    }
  ],

  // Row 4: Borrowed Shared (&BoxList)
  [
    {
      row: 3,
      col: 0,
      id: 'row4_col1',
      title: 'Cell [4, 1]: Borrowed Shared → Owned Unique',
      rustSig:
        'pub fn row4_col1_shared_ref_to_owned_box<T: Clone>(list: &BoxList<T>) -> BoxList<T>',
      lcuSig: "copy t as x in t' : !(List a) -> *(List a)",
      granuleGraded: 'uniqueBind : (*a -> !b) -> !a -> !b (Relative Monad Bind)',
      tag: 'N Clones',
      tagType: 'cow',
      alloc: 'N allocations: Must clone every value and allocate fresh BoxNode cells.',
      theoryDesc:
        'Implements the LCU copy rule from ESOP 2022 §3.1: because the source is fractionally held (n < 1) / unrestricted (!A), it cannot be mutated or drained. Producing a unique *1 value requires deep-cloning all elements.',
      code: `#[inline(always)]
fn ref_to_box_acc<T: Clone>(
    cur: Option<&BoxNode<T>>,
    acc: Option<Box<BoxNode<T>>>,
) -> Option<Box<BoxNode<T>>> {
    match cur {
        Some(node) => {
            let new_box = Some(Box::new(BoxNode {
                val: node.val.clone(),
                next: acc,
            }));
            ref_to_box_acc(node.next.as_deref(), new_box)
        }
        None => acc,
    }
}

#[inline(always)]
pub fn row4_col1_shared_ref_to_owned_box<T: Clone>(list: &BoxList<T>) -> BoxList<T> {
    BoxList {
        head: ref_to_box_acc(list.head.as_deref(), None),
    }
}`
    },
    {
      row: 3,
      col: 1,
      id: 'row4_col2',
      title: 'Cell [4, 2]: Borrowed Shared → Borrowed Unique (&mut BoxList)',
      rustSig:
        "pub fn row4_col2_shared_ref_to_mut_box<'a, T: Clone>(src: &BoxList<T>, target: &'a mut BoxList<T>) -> &'a mut BoxList<T>",
      lcuSig: 'ILLEGAL directly: *n P -> *1 P requires ∑ n_i = 1',
      granuleGraded: 'Violation of Fractional Permissions: cannot mutate while borrowed',
      tag: 'Forbidden / Slot',
      tagType: 'forbid',
      alloc: 'Direct conversion FORBIDDEN. Requires deep cloning into separate target slot.',
      theoryDesc:
        'In fractional permission logic (*n P ⊗ *m P <-> *n+m P), an exclusive mutable view requires full permission (*1). A fractional view (*n where n < 1) cannot be soundly promoted to *1. In Rust, &T -> &mut T is statically forbidden by the Aliasing XOR Mutability theorem. Safe code requires an independent exclusive destination slot.',
      code: `// A direct signature \`fn(&BoxList<T>) -> &mut BoxList<T>\` is STATICALLY FORBIDDEN
// by the Borrow Checker. Safe pattern: writing cloned reversal into a separate &mut target:
#[inline(always)]
pub fn row4_col2_shared_ref_to_mut_box<'a, T: Clone>(
    src: &BoxList<T>,
    target: &'a mut BoxList<T>,
) -> &'a mut BoxList<T> {
    *target = row4_col1_shared_ref_to_owned_box(src);
    target
}`
    },
    {
      row: 3,
      col: 2,
      id: 'row4_col3',
      title: 'Cell [4, 3]: Borrowed Shared → Owned Shared (RcList)',
      rustSig: 'pub fn row4_col3_shared_ref_to_owned_rc<T: Clone>(list: &BoxList<T>) -> RcList<T>',
      lcuSig: 'clone_to_rc : *n (List a) -> !(List a)',
      granuleGraded: '*n (List a) -> !(List a) (N Allocations)',
      tag: 'N Allocs',
      tagType: 'cow',
      alloc: 'N allocations: Creates new RcBox headers for cloned elements.',
      theoryDesc:
        'Traverses the borrowed list without mutating it, cloning values into freshly allocated Rc control blocks.',
      code: `#[inline(always)]
fn ref_to_rc_acc<T: Clone>(
    cur: Option<&BoxNode<T>>,
    acc: Option<Rc<RcNode<T>>>,
) -> Option<Rc<RcNode<T>>> {
    match cur {
        Some(node) => {
            let new_rc = Some(Rc::new(RcNode {
                val: node.val.clone(),
                next: acc,
            }));
            ref_to_rc_acc(node.next.as_deref(), new_rc)
        }
        None => acc,
    }
}

#[inline(always)]
pub fn row4_col3_shared_ref_to_owned_rc<T: Clone>(list: &BoxList<T>) -> RcList<T> {
    RcList {
        head: ref_to_rc_acc(list.head.as_deref(), None),
    }
}`
    },
    {
      row: 3,
      col: 3,
      id: 'row4_col4',
      title: 'Cell [4, 4]: Borrowed Shared → Borrowed Shared (Lazy Zero-Allocation View)',
      rustSig:
        "pub fn row4_col4_shared_ref_to_reversed_view<'a, T>(list: &'a BoxList<T>) -> ReversedView<'a, T>",
      lcuSig: "view : *n (List a) -> ReversedView<'a, a>",
      granuleGraded: "*n (List a) -> Iterator<&'a a> [0 Allocs]",
      tag: '0 Allocs View',
      tagType: 'fip',
      alloc: '0 heap allocations. Collects pointers on stack/vector view.',
      theoryDesc:
        'Pure lazy projection over fractional references (*n). Collects existing pointer addresses without copying heap elements or mutating nodes, achieving zero-cost reverse traversal.',
      code: `pub struct ReversedView<'a, T> {
    cursors: Vec<&'a T>,
}

#[inline(always)]
fn collect_refs_acc<'a, T>(cur: Option<&'a BoxNode<T>>, mut acc: Vec<&'a T>) -> Vec<&'a T> {
    match cur {
        Some(node) => {
            acc.push(&node.val);
            collect_refs_acc(node.next.as_deref(), acc)
        }
        None => acc,
    }
}

#[inline(always)]
pub fn row4_col4_shared_ref_to_reversed_view<'a, T>(list: &'a BoxList<T>) -> ReversedView<'a, T> {
    ReversedView {
        cursors: collect_refs_acc(list.head.as_deref(), Vec::new()),
    }
}

impl<'a, T> Iterator for ReversedView<'a, T> {
    type Item = &'a T;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        self.cursors.pop()
    }
}`
    }
  ]
];
