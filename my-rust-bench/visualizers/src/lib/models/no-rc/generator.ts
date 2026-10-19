import type { NoRcStep } from '#lib/types/no-rc';

export function generateNoRcSteps(values: number[]): { steps: NoRcStep[]; addresses: string[] } {
  const n = values.length;
  const addresses = values.map((_, i) => '0x' + (100 + i * 16).toString(16).toUpperCase());
  const steps: NoRcStep[] = [];
  let heapPointers: (number | null)[] = values.map((_, i) => (i < n - 1 ? i + 1 : null));
  let xs: number | null = 0;
  let acc: number | null = null;

  steps.push({
    lineWhile: 1,
    lineTail: 1,
    xs,
    acc,
    node: null,
    next: null,
    heap: [...heapPointers],
    severed: null,
    title: 'Initial Call: reverse_acc(xs, None)',
    desc: `List head starts at ${addresses[0]}. Accumulator is initialized to None (null / 0x0).`,
    badge: 'Stack Depth: 1',
    badgeType: 'slate'
  });

  for (let i = 0; i < n; i++) {
    const currNode = i;
    const nextTarget = heapPointers[currNode];

    steps.push({
      lineWhile: 4,
      lineTail: 3,
      xs: currNode,
      acc,
      node: currNode,
      next: null,
      heap: [...heapPointers],
      severed: null,
      title: `Match Node: Cons(${values[currNode]}, ...) @ ${addresses[currNode]}`,
      desc: `Ownership of heap block ${addresses[currNode]} acquired. Corresponds to Koka reuse credit (◇₂).`,
      badge: 'Ownership Acquired',
      badgeType: 'emerald'
    });

    const heapAfterTake = [...heapPointers];
    heapAfterTake[currNode] = null;
    steps.push({
      lineWhile: 5,
      lineTail: 4,
      xs: currNode,
      acc,
      node: currNode,
      next: nextTarget,
      heap: heapAfterTake,
      severed: { from: currNode, to: nextTarget },
      title: 'take(): Sever forward pointer',
      desc: `node.next.take() sets ${addresses[currNode]}->next to null and moves rest of list into local variable next.`,
      badge: 'Link Severed',
      badgeType: 'amber'
    });
    heapPointers = heapAfterTake;

    const heapAfterRewire = [...heapPointers];
    heapAfterRewire[currNode] = acc;
    steps.push({
      lineWhile: 6,
      lineTail: 5,
      xs: currNode,
      acc,
      node: currNode,
      next: nextTarget,
      heap: heapAfterRewire,
      severed: null,
      title: 'node.next = acc: IN-PLACE POINTER FLIP',
      desc: `Heap cell ${addresses[currNode]} is mutated in-place to point backwards to ${acc !== null ? addresses[acc] : 'null'}. 0 allocations!`,
      badge: '0 Allocations',
      badgeType: 'emerald'
    });
    heapPointers = heapAfterRewire;

    acc = currNode;
    xs = nextTarget;
    steps.push({
      lineWhile: 8,
      lineTail: 6,
      xs,
      acc,
      node: null,
      next: null,
      heap: [...heapPointers],
      severed: null,
      title: 'Advance: reverse_acc(next, Some(node))',
      desc: `In-place argument swap. Stack depth stays O(1) (TCO). acc is now ${addresses[acc]}.`,
      badge: 'TCO Constant Stack',
      badgeType: 'slate'
    });
  }

  steps.push({
    lineWhile: 10,
    lineTail: 8,
    xs: null,
    acc,
    node: null,
    next: null,
    heap: [...heapPointers],
    severed: null,
    title: 'Base Case: match None => acc',
    desc: `xs is None (null). The accumulated reversed list starting at ${acc !== null ? addresses[acc] : 'null'} is returned. Total allocations: 0.`,
    badge: 'Reversal Done',
    badgeType: 'emerald'
  });

  return { steps, addresses };
}
