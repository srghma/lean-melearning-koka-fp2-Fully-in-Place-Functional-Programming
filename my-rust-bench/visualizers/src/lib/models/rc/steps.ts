import type { RcStep } from '#lib/types/rc';

export const RC_STEPS: RcStep[] = [
  {
    lineWhile: 1,
    lineTail: 1,
    xs: '0x100',
    acc: 'null',
    rc_node: null,
    getMut: null,
    nodeRCs: { '0x100': 1, '0x110': 1, '0x200': 2, '0x300': 1 },
    arrows: [
      { from: '0x100', to: '0x200', type: 'forward' },
      { from: '0x110', to: '0x200', type: 'shared-root' },
      { from: '0x200', to: '0x300', type: 'forward' },
      { from: '0x300', to: 'null', type: 'forward' }
    ],
    visibleNodes: ['0x100', '0x110', '0x200', '0x300'],
    title: 'Initial State: Shared Tail (list1: 1->2->3, list2: 11->2->3)',
    desc: 'list1 starts at 0x100. list2 starts at 0x110. Both converge on Node 2 (0x200), giving it RC = 2.',
    badge: 'Shared Tail',
    badgeType: 'slate'
  },
  {
    lineWhile: 4,
    lineTail: 3,
    xs: '0x100',
    acc: 'null',
    rc_node: '0x100',
    getMut: 'Some(&mut node) [RC == 1] -> UNIQUE!',
    nodeRCs: { '0x100': 1, '0x110': 1, '0x200': 2, '0x300': 1 },
    arrows: [
      { from: '0x100', to: '0x200', type: 'forward' },
      { from: '0x110', to: '0x200', type: 'shared-root' },
      { from: '0x200', to: '0x300', type: 'forward' },
      { from: '0x300', to: 'null', type: 'forward' }
    ],
    visibleNodes: ['0x100', '0x110', '0x200', '0x300'],
    title: 'Node 1 (0x100): Rc::get_mut checks RC == 1',
    desc: 'Rc::get_mut(&mut rc_node) succeeds! Node 1 is uniquely owned by list1. Corresponds to Koka is-unique.',
    badge: 'RC == 1 Unique',
    badgeType: 'emerald'
  },
  {
    lineWhile: 6,
    lineTail: 5,
    xs: '0x200',
    acc: 'null',
    rc_node: '0x100',
    getMut: 'Some(&mut node) [RC == 1]',
    nodeRCs: { '0x100': 1, '0x110': 1, '0x200': 2, '0x300': 1 },
    arrows: [
      { from: '0x100', to: '0x200', type: 'severed' },
      { from: '0x110', to: '0x200', type: 'shared-root' },
      { from: '0x200', to: '0x300', type: 'forward' },
      { from: '0x300', to: 'null', type: 'forward' }
    ],
    visibleNodes: ['0x100', '0x110', '0x200', '0x300'],
    title: 'Node 1: xs = node.next.take()',
    desc: 'Forward pointer from 0x100 is severed. 0x200 moved into xs. Node 1 next is temporarily null.',
    badge: 'Link Severed',
    badgeType: 'amber'
  },
  {
    lineWhile: 7,
    lineTail: 6,
    xs: '0x200',
    acc: '0x100',
    rc_node: '0x100',
    getMut: 'Some(&mut node) [RC == 1]',
    nodeRCs: { '0x100': 1, '0x110': 1, '0x200': 2, '0x300': 1 },
    arrows: [
      { from: '0x100', to: 'null', type: 'backward' },
      { from: '0x110', to: '0x200', type: 'shared-root' },
      { from: '0x200', to: '0x300', type: 'forward' },
      { from: '0x300', to: 'null', type: 'forward' }
    ],
    visibleNodes: ['0x100', '0x110', '0x200', '0x300'],
    title: 'Node 1: node.next = acc (IN-PLACE REUSE)',
    desc: 'Node 1 (0x100) next is set to acc (null). 0 allocations! Existing Rc heap cell at 0x100 is reused.',
    badge: 'In-Place Reuse',
    badgeType: 'emerald'
  },
  {
    lineWhile: 4,
    lineTail: 3,
    xs: '0x200',
    acc: '0x100',
    rc_node: '0x200',
    getMut: 'None [RC == 2] -> SHARED (COW)!',
    nodeRCs: { '0x100': 1, '0x110': 1, '0x200': 2, '0x300': 1 },
    arrows: [
      { from: '0x100', to: 'null', type: 'backward' },
      { from: '0x110', to: '0x200', type: 'shared-root' },
      { from: '0x200', to: '0x300', type: 'forward' },
      { from: '0x300', to: 'null', type: 'forward' }
    ],
    visibleNodes: ['0x100', '0x110', '0x200', '0x300'],
    title: 'Node 2 (0x200): Rc::get_mut fails (RC = 2)',
    desc: 'Rc::get_mut returns None because list2 also holds Node 2! In-place mutation would corrupt list2, so Rust branches to Copy-on-Write.',
    badge: 'RC == 2 Shared',
    badgeType: 'amber'
  },
  {
    lineWhile: 11,
    lineTail: 10,
    xs: '0x300',
    acc: '0x100',
    rc_node: '0x200',
    getMut: 'None [RC == 2]',
    nodeRCs: { '0x100': 1, '0x110': 1, '0x200': 2, '0x300': 2 },
    arrows: [
      { from: '0x100', to: 'null', type: 'backward' },
      { from: '0x110', to: '0x200', type: 'shared-root' },
      { from: '0x200', to: '0x300', type: 'forward' },
      { from: '0x300', to: 'null', type: 'forward' }
    ],
    visibleNodes: ['0x100', '0x110', '0x200', '0x300'],
    title: 'Node 2: xs = rc_node.next.clone()',
    desc: "Cloning next advances xs to Node 3 (0x300) and increments Node 3's RC to 2.",
    badge: 'Clone Link',
    badgeType: 'amber'
  },
  {
    lineWhile: 12,
    lineTail: 13,
    xs: '0x300',
    acc: '0x220',
    rc_node: null,
    getMut: 'None [COW Alloc]',
    nodeRCs: { '0x100': 1, '0x110': 1, '0x200': 1, '0x300': 2, '0x220': 1 },
    arrows: [
      { from: '0x100', to: 'null', type: 'backward' },
      { from: '0x110', to: '0x200', type: 'shared-root' },
      { from: '0x200', to: '0x300', type: 'forward' },
      { from: '0x300', to: 'null', type: 'forward' },
      { from: '0x220', to: '0x100', type: 'cow-backward' }
    ],
    visibleNodes: ['0x100', '0x110', '0x200', '0x300', '0x220'],
    title: "Node 2: Allocate Fresh Node 2' (0x220) via COW",
    desc: "Rc::new allocates brand-new Node 2' (0x220) pointing to Node 1 (0x100). rc_node dropped, lowering original Node 2 RC back to 1!",
    badge: 'COW New Alloc',
    badgeType: 'purple'
  },
  {
    lineWhile: 4,
    lineTail: 3,
    xs: '0x300',
    acc: '0x220',
    rc_node: '0x300',
    getMut: 'None [RC == 2] -> SHARED (COW)!',
    nodeRCs: { '0x100': 1, '0x110': 1, '0x200': 1, '0x300': 2, '0x220': 1 },
    arrows: [
      { from: '0x100', to: 'null', type: 'backward' },
      { from: '0x110', to: '0x200', type: 'shared-root' },
      { from: '0x200', to: '0x300', type: 'forward' },
      { from: '0x300', to: 'null', type: 'forward' },
      { from: '0x220', to: '0x100', type: 'cow-backward' }
    ],
    visibleNodes: ['0x100', '0x110', '0x200', '0x300', '0x220'],
    title: 'Node 3 (0x300): Rc::get_mut fails (RC = 2)',
    desc: 'Node 3 is held by xs and original Node 2 (0x200). Rc::get_mut returns None -> Copy-on-Write triggers again.',
    badge: 'RC == 2 Shared',
    badgeType: 'amber'
  },
  {
    lineWhile: 12,
    lineTail: 13,
    xs: 'null',
    acc: '0x320',
    rc_node: null,
    getMut: 'None [COW Alloc]',
    nodeRCs: { '0x100': 1, '0x110': 1, '0x200': 1, '0x300': 1, '0x220': 1, '0x320': 1 },
    arrows: [
      { from: '0x100', to: 'null', type: 'backward' },
      { from: '0x110', to: '0x200', type: 'shared-root' },
      { from: '0x200', to: '0x300', type: 'forward' },
      { from: '0x300', to: 'null', type: 'forward' },
      { from: '0x220', to: '0x100', type: 'cow-backward' },
      { from: '0x320', to: '0x220', type: 'cow-backward' }
    ],
    visibleNodes: ['0x100', '0x110', '0x200', '0x300', '0x220', '0x320'],
    title: "Node 3: Allocate Fresh Node 3' (0x320) via COW",
    desc: "Fresh Node 3' (0x320) points to Node 2' (0x220). rc_node dropped, original Node 3 RC falls back to 1.",
    badge: 'COW New Alloc',
    badgeType: 'purple'
  },
  {
    lineWhile: 19,
    lineTail: 17,
    xs: 'null',
    acc: '0x320',
    rc_node: null,
    getMut: null,
    nodeRCs: { '0x100': 1, '0x110': 1, '0x200': 1, '0x300': 1, '0x220': 1, '0x320': 1 },
    arrows: [
      { from: '0x100', to: 'null', type: 'backward' },
      { from: '0x110', to: '0x200', type: 'shared-root' },
      { from: '0x200', to: '0x300', type: 'forward' },
      { from: '0x300', to: 'null', type: 'forward' },
      { from: '0x220', to: '0x100', type: 'cow-backward' },
      { from: '0x320', to: '0x220', type: 'cow-backward' }
    ],
    visibleNodes: ['0x100', '0x110', '0x200', '0x300', '0x220', '0x320'],
    title: 'Reversal Complete: Both Lists Valid & Safe',
    desc: "Reversed list1: [3' @ 0x320] -> [2' @ 0x220] -> [1 @ 0x100] (Node 1 reused in-place!). list2: [11 @ 0x110] -> [2 @ 0x200] -> [3 @ 0x300] is completely untouched!",
    badge: 'Safe Sharing Complete',
    badgeType: 'emerald'
  }
];
