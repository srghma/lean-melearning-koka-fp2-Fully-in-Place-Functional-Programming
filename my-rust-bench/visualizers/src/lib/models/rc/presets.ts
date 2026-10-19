import type { RcPresetConfig } from '#lib/types/rc';

export const RC_PRESETS: RcPresetConfig[] = [
  // Preset 1: 3-Way Sharing (Requested: 1->2->3->4, 11->22->3->4, 13->23->3->4)
  {
    id: 'three-way',
    name: '3-Way Sharing (RC = 3)',
    shortDesc: '3 lists converge on Node 3 -> RC = 3',
    longDesc:
      'list1 (1->2), list2 (11->22), and list3 (13->23) all point into Node 3. Nodes 1 & 2 reuse in-place, while Nodes 3 & 4 trigger Copy-on-Write.',
    activeRoot: 'list1',
    canvasWidth: 840,
    canvasHeight: 460,
    roots: [
      { name: 'list1', targetAddr: '0x100', color: '#38bdf8' },
      { name: 'list2', targetAddr: '0x110', color: '#f59e0b' },
      { name: 'list3', targetAddr: '0x130', color: '#ec4899' }
    ],
    nodes: [
      // Branch 1
      {
        id: 'n1',
        addr: '0x100',
        val: 1,
        label: 'Node 1',
        next: '0x200',
        x: 40,
        y: 40,
        tag: 'REUSED IN-PLACE'
      },
      {
        id: 'n2',
        addr: '0x200',
        val: 2,
        label: 'Node 2',
        next: '0x300',
        x: 230,
        y: 40,
        tag: 'REUSED IN-PLACE'
      },
      // Branch 2
      {
        id: 'n11',
        addr: '0x110',
        val: 11,
        label: 'Node 11',
        next: '0x210',
        x: 40,
        y: 140,
        tag: 'list2 ROOT'
      },
      {
        id: 'n22',
        addr: '0x210',
        val: 22,
        label: 'Node 22',
        next: '0x300',
        x: 230,
        y: 140,
        tag: 'list2 NODE'
      },
      // Branch 3
      {
        id: 'n13',
        addr: '0x130',
        val: 13,
        label: 'Node 13',
        next: '0x230',
        x: 40,
        y: 240,
        tag: 'list3 ROOT'
      },
      {
        id: 'n23',
        addr: '0x230',
        val: 23,
        label: 'Node 23',
        next: '0x300',
        x: 230,
        y: 240,
        tag: 'list3 NODE'
      },
      // Shared tail (centered at y = 140)
      {
        id: 'n3',
        addr: '0x300',
        val: 3,
        label: 'Node 3 (shared 3x)',
        next: '0x400',
        x: 440,
        y: 140,
        tag: 'SHARED (RC=3)'
      },
      {
        id: 'n4',
        addr: '0x400',
        val: 4,
        label: 'Node 4 (shared)',
        next: null,
        x: 650,
        y: 140,
        tag: 'SHARED (RC=1)'
      }
    ]
  },

  // Preset 2: Head Shared (Requested: 1->2->3 and 1 has RC=2)
  {
    id: 'root-shared',
    name: 'Head Shared (RC = 2 on Node 1)',
    shortDesc: 'Persistent clone on list head -> Full COW cascade',
    longDesc:
      'An external reference holds Node 1. Every single node triggers Copy-on-Write because the original list is preserved intact.',
    activeRoot: 'list1',
    canvasWidth: 740,
    canvasHeight: 380,
    roots: [
      { name: 'list1', targetAddr: '0x100', color: '#38bdf8' },
      { name: 'clone', targetAddr: '0x100', color: '#f59e0b' }
    ],
    nodes: [
      {
        id: 'n1',
        addr: '0x100',
        val: 1,
        label: 'Node 1',
        next: '0x200',
        x: 40,
        y: 60,
        tag: 'SHARED HEAD'
      },
      {
        id: 'n2',
        addr: '0x200',
        val: 2,
        label: 'Node 2',
        next: '0x300',
        x: 270,
        y: 60,
        tag: 'SHARED VIA PARENT'
      },
      {
        id: 'n3',
        addr: '0x300',
        val: 3,
        label: 'Node 3',
        next: null,
        x: 500,
        y: 60,
        tag: 'SHARED VIA PARENT'
      }
    ]
  },

  // Preset 3: Classic Shared Tail (2-Way)
  {
    id: 'shared-tail',
    name: 'Classic Shared Tail (2-Way)',
    shortDesc: 'list1 (1->2->3) and list2 (11->2->3)',
    longDesc:
      'Node 1 is unique (RC=1) and flips in-place. Nodes 2 & 3 are shared with list2 (RC=2) and allocate fresh COW blocks.',
    activeRoot: 'list1',
    canvasWidth: 740,
    canvasHeight: 380,
    roots: [
      { name: 'list1', targetAddr: '0x100', color: '#38bdf8' },
      { name: 'list2', targetAddr: '0x110', color: '#f59e0b' }
    ],
    nodes: [
      {
        id: 'n1',
        addr: '0x100',
        val: 1,
        label: 'Node 1',
        next: '0x200',
        x: 40,
        y: 50,
        tag: 'REUSED IN-PLACE'
      },
      {
        id: 'n11',
        addr: '0x110',
        val: 11,
        label: 'Node 11 (list2)',
        next: '0x200',
        x: 40,
        y: 175,
        tag: 'list2 ROOT'
      },
      {
        id: 'n2',
        addr: '0x200',
        val: 2,
        label: 'Node 2 (shared)',
        next: '0x300',
        x: 270,
        y: 110,
        tag: 'SHARED ORIGINAL'
      },
      {
        id: 'n3',
        addr: '0x300',
        val: 3,
        label: 'Node 3 (shared)',
        next: null,
        x: 500,
        y: 110,
        tag: 'SHARED ORIGINAL'
      }
    ]
  },

  // Preset 4: 100% Unique List (0 Allocations)
  {
    id: 'all-unique',
    name: '100% Unique List (FIP In-Place)',
    shortDesc: 'All nodes have RC = 1 -> 0 allocations',
    longDesc:
      'Every node satisfies Rc::get_mut. 100% in-place mutation, identical to Box<Node> in mechanical efficiency.',
    activeRoot: 'list1',
    canvasWidth: 840,
    canvasHeight: 280,
    roots: [{ name: 'list1', targetAddr: '0x100', color: '#38bdf8' }],
    nodes: [
      {
        id: 'n1',
        addr: '0x100',
        val: 1,
        label: 'Node 1',
        next: '0x200',
        x: 40,
        y: 70,
        tag: 'REUSED IN-PLACE'
      },
      {
        id: 'n2',
        addr: '0x200',
        val: 2,
        label: 'Node 2',
        next: '0x300',
        x: 230,
        y: 70,
        tag: 'REUSED IN-PLACE'
      },
      {
        id: 'n3',
        addr: '0x300',
        val: 3,
        label: 'Node 3',
        next: '0x400',
        x: 430,
        y: 70,
        tag: 'REUSED IN-PLACE'
      },
      {
        id: 'n4',
        addr: '0x400',
        val: 4,
        label: 'Node 4',
        next: null,
        x: 630,
        y: 70,
        tag: 'REUSED IN-PLACE'
      }
    ]
  },

  // Preset 5: Middle Shared Node
  {
    id: 'middle-shared',
    name: 'Middle Shared (External Handle)',
    shortDesc: 'Only Node 2 is held externally',
    longDesc:
      'Node 1 reuses in-place. Node 2 has an extra reference and branches to COW, protecting the external handle.',
    activeRoot: 'list1',
    canvasWidth: 840,
    canvasHeight: 380,
    roots: [
      { name: 'list1', targetAddr: '0x100', color: '#38bdf8' },
      { name: 'handle', targetAddr: '0x200', color: '#f59e0b' }
    ],
    nodes: [
      {
        id: 'n1',
        addr: '0x100',
        val: 1,
        label: 'Node 1',
        next: '0x200',
        x: 40,
        y: 60,
        tag: 'REUSED IN-PLACE'
      },
      {
        id: 'n2',
        addr: '0x200',
        val: 2,
        label: 'Node 2',
        next: '0x300',
        x: 230,
        y: 60,
        tag: 'SHARED (HANDLE)'
      },
      {
        id: 'n3',
        addr: '0x300',
        val: 3,
        label: 'Node 3',
        next: '0x400',
        x: 430,
        y: 60,
        tag: 'SHARED VIA PARENT'
      },
      {
        id: 'n4',
        addr: '0x400',
        val: 4,
        label: 'Node 4',
        next: null,
        x: 630,
        y: 60,
        tag: 'SHARED VIA PARENT'
      }
    ]
  }
];
