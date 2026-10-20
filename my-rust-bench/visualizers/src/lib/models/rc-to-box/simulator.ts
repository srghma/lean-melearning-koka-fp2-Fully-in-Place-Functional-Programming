import type { RcPresetConfig, RcArrow, NodeMeta } from '#lib/types/rc';
import type { BaseStep } from '#lib/types/common';

export interface RcToBoxStep extends BaseStep {
  xs: string;
  acc: string;
  rc_node: string | null;
  unwrapResult: string | null;
  nodeRCs: Record<string, number>;
  arrows: RcArrow[];
  rcNodes: string[];
  boxNodes: string[];
}

export function simulateRcToBox(preset: RcPresetConfig): {
  steps: RcToBoxStep[];
  nodeMeta: Record<string, NodeMeta>;
} {
  const nodeMeta: Record<string, NodeMeta> = {};
  for (const n of preset.nodes) {
    nodeMeta[n.addr] = { ...n };
  }

  const heap: Record<string, string | null> = {};
  for (const n of preset.nodes) {
    heap[n.addr] = n.next;
  }

  const rcNodes = new Set<string>(preset.nodes.map((n) => n.addr));
  const boxNodes = new Set<string>();

  function computeRCs(
    currentXs: string | null,
    currentRcNode: string | null
  ): Record<string, number> {
    const rcs: Record<string, number> = {};
    for (const addr of rcNodes) {
      rcs[addr] = 0;
    }
    for (const r of preset.roots) {
      if (r.name !== preset.activeRoot && rcs[r.targetAddr] !== undefined) {
        rcs[r.targetAddr] += 1;
      }
    }
    for (const fromAddr of rcNodes) {
      const toAddr = heap[fromAddr];
      if (toAddr && rcs[toAddr] !== undefined) {
        rcs[toAddr] += 1;
      }
    }
    if (currentXs && currentXs !== 'null' && rcs[currentXs] !== undefined) {
      rcs[currentXs] += 1;
    }
    if (currentRcNode && currentRcNode !== 'null' && rcs[currentRcNode] !== undefined) {
      rcs[currentRcNode] += 1;
    }
    return rcs;
  }

  function buildArrows(): RcArrow[] {
    const arrows: RcArrow[] = [];
    for (const r of preset.roots) {
      if (r.name !== preset.activeRoot) {
        arrows.push({
          from: r.name,
          to: r.targetAddr,
          type: 'shared-root',
          color: r.color,
          label: r.name
        });
      }
    }
    for (const fromAddr of rcNodes) {
      const toAddr = heap[fromAddr];
      if (toAddr && rcNodes.has(toAddr)) {
        arrows.push({ from: fromAddr, to: toAddr, type: 'forward' });
      } else if (!toAddr) {
        arrows.push({ from: fromAddr, to: 'null', type: 'forward' });
      }
    }
    for (const fromAddr of boxNodes) {
      const toAddr = heap[fromAddr];
      if (toAddr && boxNodes.has(toAddr)) {
        arrows.push({ from: fromAddr, to: toAddr, type: 'backward' });
      } else {
        arrows.push({ from: fromAddr, to: 'null', type: 'forward' });
      }
    }
    return arrows;
  }

  const steps: RcToBoxStep[] = [];
  let xs: string | null = preset.roots.find((r) => r.name === preset.activeRoot)!.targetAddr;
  let acc: string = 'null';

  // Step 0: Init
  steps.push({
    lineWhile: 1,
    lineTail: 1,
    xs,
    acc,
    rc_node: null,
    unwrapResult: null,
    nodeRCs: computeRCs(xs, null),
    arrows: buildArrows(),
    rcNodes: Array.from(rcNodes),
    boxNodes: Array.from(boxNodes),
    title: `Initial State: ${preset.name}`,
    desc: preset.longDesc,
    badge: 'Graph Initialized',
    badgeType: 'slate'
  });

  while (xs && xs !== 'null') {
    const currAddr: string = xs;
    const nextAddr: string | null = heap[currAddr] ?? null;

    // Substep 1: xs moves into rc_node
    steps.push({
      lineWhile: 3,
      lineTail: 3,
      xs: 'null',
      acc,
      rc_node: currAddr,
      unwrapResult: 'evaluating try_unwrap...',
      nodeRCs: computeRCs(null, currAddr),
      arrows: buildArrows(),
      rcNodes: Array.from(rcNodes),
      boxNodes: Array.from(boxNodes),
      title: `Fetch rc_node = ${currAddr}`,
      desc: `xs is popped into local rc_node variable. Next step tests uniqueness.`,
      badge: `Fetch ${currAddr}`,
      badgeType: 'slate'
    });

    const initialRC = computeRCs(null, currAddr)[currAddr] || 1;
    const isUnique = initialRC === 1;

    // Substep 2: Match on Rc::try_unwrap(rc_node)
    if (isUnique) {
      // Ok(unique_node): take next directly, 0 atomic refcount updates
      heap[currAddr] = null;
      xs = nextAddr;

      steps.push({
        lineWhile: 7,
        lineTail: 5,
        xs: xs || 'null',
        acc,
        rc_node: currAddr,
        unwrapResult: 'Ok(unique_node) [RC == 1] -> 0 atomic updates!',
        nodeRCs: computeRCs(xs, currAddr),
        arrows: buildArrows(),
        rcNodes: Array.from(rcNodes),
        boxNodes: Array.from(boxNodes),
        title: `Rc::try_unwrap(${currAddr}) SUCCEEDED: Zero Atomic Updates`,
        desc: `Because RC == 1, ownership of the inner Node is acquired without atomic reference counting. unique_node.next.take() moves next without cloning!`,
        badge: '0 Atomic Updates (Unique)',
        badgeType: 'emerald'
      });
    } else {
      // Err(shared_rc): clone next and clone val
      xs = nextAddr;

      steps.push({
        lineWhile: 11,
        lineTail: 6,
        xs: xs || 'null',
        acc,
        rc_node: currAddr,
        unwrapResult: `Err(shared_rc) [RC == ${initialRC}] -> clone val & next`,
        nodeRCs: computeRCs(xs, currAddr),
        arrows: buildArrows(),
        rcNodes: Array.from(rcNodes),
        boxNodes: Array.from(boxNodes),
        title: `Rc::try_unwrap(${currAddr}) FAILED (RC = ${initialRC}): Shared Fallback`,
        desc: `RC > 1. try_unwrap safely returns Err(shared_rc). val.clone() and next.clone() copy the data while keeping original shared graph intact.`,
        badge: `RC == ${initialRC} Shared`,
        badgeType: 'amber'
      });
    }

    // Substep 3: acc = Some(Box::new(BoxNode { val, next: acc }))
    const boxAddr = `box_${currAddr}`;
    const origMeta = nodeMeta[currAddr];
    nodeMeta[boxAddr] = {
      id: `box_${origMeta.id}`,
      addr: boxAddr,
      val: origMeta.val,
      label: `Box(${origMeta.val})`,
      x: origMeta.x,
      y: 240,
      tag: isUnique ? 'BOX (FROM UNIQUE)' : 'BOX (FROM SHARED)'
    };
    boxNodes.add(boxAddr);
    heap[boxAddr] = acc === 'null' ? null : acc;
    acc = boxAddr;

    // rc_node dropped here:
    // Only dissolve the Rc cell if it was unique.
    // If shared, other roots (like keep_alive) preserve it in memory!
    if (isUnique) {
      rcNodes.delete(currAddr);
    }

    steps.push({
      lineWhile: 15,
      lineTail: 8,
      xs: xs || 'null',
      acc,
      rc_node: null,
      unwrapResult: isUnique ? 'Ok -> Box Allocated' : 'Err -> Box Allocated',
      nodeRCs: computeRCs(xs, null),
      arrows: buildArrows(),
      rcNodes: Array.from(rcNodes),
      boxNodes: Array.from(boxNodes),
      title: `Allocate Box<BoxNode> at ${boxAddr} for Accumulator`,
      desc: `Box::new encapsulates the unwrapped/cloned value and points backward to ${heap[boxAddr] || 'null'}. Input rc_node is dropped.`,
      badge: 'Box Cell Created',
      badgeType: 'purple'
    });
  }

  // Base Case
  steps.push({
    lineWhile: 17,
    lineTail: 11,
    xs: 'null',
    acc,
    rc_node: null,
    unwrapResult: null,
    nodeRCs: computeRCs(null, null),
    arrows: buildArrows(),
    rcNodes: Array.from(rcNodes),
    boxNodes: Array.from(boxNodes),
    title: 'Conversion Complete: Reversing List a -> List a {Unique}',
    desc: `Unique Boxed list starting at ${acc} is returned. 100% linear ownership with zero remaining Rc headers.`,
    badge: 'Linear Box List Ready',
    badgeType: 'emerald'
  });

  return { steps, nodeMeta };
}
