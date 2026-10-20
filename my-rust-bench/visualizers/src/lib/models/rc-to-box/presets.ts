import type { RcPresetConfig } from '#lib/types/rc';

export const RC_TO_BOX_PRESETS: RcPresetConfig[] = [
  {
    id: 'unique-to-box',
    name: '100% Unique (Zero Atomic Overhead)',
    shortDesc: 'All Rc nodes have RC = 1 -> Rc::try_unwrap succeeds',
    longDesc:
      'Every node succeeds Rc::try_unwrap: inner val is moved without cloning and next is taken directly with 0 atomic refcount updates. New Box nodes are allocated in accumulator.',
    activeRoot: 'rc_list',
    canvasWidth: 840,
    canvasHeight: 380,
    roots: [{ name: 'rc_list', targetAddr: '0x100', color: '#38bdf8' }],
    nodes: [
      {
        id: 'r1',
        addr: '0x100',
        val: 10,
        label: 'Rc 10',
        next: '0x200',
        x: 40,
        y: 40,
        tag: 'RC UNIQUE'
      },
      {
        id: 'r2',
        addr: '0x200',
        val: 20,
        label: 'Rc 20',
        next: '0x300',
        x: 250,
        y: 40,
        tag: 'RC UNIQUE'
      },
      {
        id: 'r3',
        addr: '0x300',
        val: 30,
        label: 'Rc 30',
        next: null,
        x: 460,
        y: 40,
        tag: 'RC UNIQUE'
      }
    ]
  },
  {
    id: 'shared-tail-to-box',
    name: 'Shared Tail (Partial COW Clone)',
    shortDesc: 'Node 1 is unique; Nodes 2 & 3 are shared with keep-alive',
    longDesc:
      'Node 1 is unique (try_unwrap Ok -> 0 atomic updates). Nodes 2 & 3 have RC > 1, so try_unwrap returns Err: shared_rc.val.clone() and .next.clone() are performed.',
    activeRoot: 'rc_list',
    canvasWidth: 840,
    canvasHeight: 460,
    roots: [
      { name: 'rc_list', targetAddr: '0x100', color: '#38bdf8' },
      { name: 'keep_alive', targetAddr: '0x200', color: '#f59e0b' }
    ],
    nodes: [
      {
        id: 'r1',
        addr: '0x100',
        val: 1,
        label: 'Rc 1',
        next: '0x200',
        x: 40,
        y: 40,
        tag: 'RC UNIQUE'
      },
      {
        id: 'r2',
        addr: '0x200',
        val: 2,
        label: 'Rc 2 (shared)',
        next: '0x300',
        x: 250,
        y: 40,
        tag: 'RC SHARED'
      },
      {
        id: 'r3',
        addr: '0x300',
        val: 3,
        label: 'Rc 3 (shared)',
        next: null,
        x: 460,
        y: 40,
        tag: 'RC SHARED'
      }
    ]
  }
];
