import type { BaseStep } from '#lib/types/common';
import type { RcArrow, NodeMeta } from '#lib/types/rc';

export interface BoxToRcStep extends BaseStep {
  xs: string;
  acc: string;
  box_node: string | null;
  boxNodes: string[];
  rcNodes: string[];
  arrows: RcArrow[];
}

export function generateBoxToRcSteps(values: number[]): {
  steps: BoxToRcStep[];
  nodeMeta: Record<string, NodeMeta>;
} {
  const n = values.length;
  const nodeMeta: Record<string, NodeMeta> = {};
  const heap: Record<string, string | null> = {};

  const addresses = values.map((_, i) => `0x${(0x100 + i * 0x10).toString(16).toUpperCase()}`);

  for (let i = 0; i < n; i++) {
    const bAddr = addresses[i];
    const nextB = i < n - 1 ? addresses[i + 1] : null;
    nodeMeta[bAddr] = {
      id: `box_${i}`,
      addr: bAddr,
      val: values[i],
      label: `Box(${values[i]})`,
      x: 40 + i * 210,
      y: 40,
      tag: 'UNIQUE BOX'
    };
    heap[bAddr] = nextB;
  }

  const boxNodes = new Set<string>(addresses);
  const rcNodes = new Set<string>();

  function buildArrows(severed: { from: string; to: string } | null): RcArrow[] {
    const arrows: RcArrow[] = [];
    for (const b of boxNodes) {
      if (severed && severed.from === b) {
        arrows.push({ from: b, to: severed.to, type: 'severed' });
        continue;
      }
      const to = heap[b];
      if (to && boxNodes.has(to)) {
        arrows.push({ from: b, to, type: 'forward' });
      } else {
        arrows.push({ from: b, to: 'null', type: 'forward' });
      }
    }
    for (const r of rcNodes) {
      const to = heap[r];
      if (to && rcNodes.has(to)) {
        arrows.push({ from: r, to, type: 'backward' });
      } else {
        arrows.push({ from: r, to: 'null', type: 'forward' });
      }
    }
    return arrows;
  }

  const steps: BoxToRcStep[] = [];
  let xs: string | null = addresses[0] ?? null;
  let acc: string = 'null';

  steps.push({
    lineWhile: 1,
    lineTail: 1,
    xs,
    acc,
    box_node: null,
    boxNodes: Array.from(boxNodes),
    rcNodes: Array.from(rcNodes),
    arrows: buildArrows(null),
    title: 'Initial Call: List a {Unique} -> List a',
    desc: 'Starting with a unique Boxed singly-linked list. Each node will be wrapped into an Rc control block.',
    badge: 'Unique Input',
    badgeType: 'slate'
  });

  while (xs && xs !== 'null') {
    const currAddr: string = xs;
    const nextAddr: string | null = heap[currAddr] ?? null;

    // Sever next
    heap[currAddr] = null;
    xs = nextAddr;

    steps.push({
      lineWhile: 4,
      lineTail: 4,
      xs: xs || 'null',
      acc,
      box_node: currAddr,
      boxNodes: Array.from(boxNodes),
      rcNodes: Array.from(rcNodes),
      arrows: buildArrows(nextAddr ? { from: currAddr, to: nextAddr } : null),
      title: `${currAddr}: xs = box_node.next.take()`,
      desc: `Severed link to rest of list. Ownership of inner value ${nodeMeta[currAddr].val} retained.`,
      badge: 'Link Severed',
      badgeType: 'amber'
    });

    // Create RcNode
    const rcAddr = `rc_${currAddr}`;
    const origMeta = nodeMeta[currAddr];
    nodeMeta[rcAddr] = {
      id: `rc_${origMeta.id}`,
      addr: rcAddr,
      val: origMeta.val,
      label: `RcNode(${origMeta.val})`,
      x: origMeta.x,
      y: 220,
      tag: 'NEW RC CELL (RC=1)'
    };
    rcNodes.add(rcAddr);
    boxNodes.delete(currAddr);
    heap[rcAddr] = acc === 'null' ? null : acc;
    acc = rcAddr;

    steps.push({
      lineWhile: 5,
      lineTail: 5,
      xs: xs || 'null',
      acc,
      box_node: null,
      boxNodes: Array.from(boxNodes),
      rcNodes: Array.from(rcNodes),
      arrows: buildArrows(null),
      title: `Allocate Rc<Node> at ${rcAddr}`,
      desc: `Rc::new allocates an RcBox with strong=1, weak=0, pointing backward to accumulator ${heap[rcAddr] || 'null'}.`,
      badge: 'Rc Control Block Created',
      badgeType: 'purple'
    });
  }

  steps.push({
    lineWhile: 10,
    lineTail: 11,
    xs: 'null',
    acc,
    box_node: null,
    boxNodes: Array.from(boxNodes),
    rcNodes: Array.from(rcNodes),
    arrows: buildArrows(null),
    title: 'Conversion Complete: List a {Unique} -> List a',
    desc: `All elements are now packaged into reference-counted nodes. The returned Rc list supports shared persistent usage.`,
    badge: 'Rc List Ready',
    badgeType: 'emerald'
  });

  return { steps, nodeMeta };
}
