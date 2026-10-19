import type { NodeMeta } from '#lib/types/rc';

export const RC_NODE_META: Record<string, NodeMeta> = {
  '0x100': {
    id: 'n1',
    addr: '0x100',
    val: 1,
    label: 'Node 1',
    x: 40,
    y: 50,
    tag: 'REUSED IN-PLACE'
  },
  '0x110': {
    id: 'n11',
    addr: '0x110',
    val: 11,
    label: 'Node 11 (list2)',
    x: 40,
    y: 175,
    tag: 'list2 ROOT'
  },
  '0x200': {
    id: 'n2',
    addr: '0x200',
    val: 2,
    label: 'Node 2 (shared)',
    x: 270,
    y: 110,
    tag: 'SHARED ORIGINAL'
  },
  '0x300': {
    id: 'n3',
    addr: '0x300',
    val: 3,
    label: 'Node 3 (shared)',
    x: 500,
    y: 110,
    tag: 'SHARED ORIGINAL'
  },
  '0x220': {
    id: 'n2_cow',
    addr: '0x220',
    val: 2,
    label: "Node 2' (COW)",
    x: 270,
    y: 260,
    tag: 'NEW COW ALLOC'
  },
  '0x320': {
    id: 'n3_cow',
    addr: '0x320',
    val: 3,
    label: "Node 3' (COW)",
    x: 500,
    y: 260,
    tag: 'NEW COW ALLOC'
  }
};
