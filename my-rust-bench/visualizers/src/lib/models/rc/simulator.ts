import type { RcPresetConfig, RcStep, RcArrow, NodeMeta } from '#lib/types/rc';

export function simulateRcGraph(preset: RcPresetConfig): {
  steps: RcStep[];
  nodeMeta: Record<string, NodeMeta>;
} {
  const nodeMeta: Record<string, NodeMeta> = {};
  for (const n of preset.nodes) {
    nodeMeta[n.addr] = {
      id: n.id,
      addr: n.addr,
      val: n.val,
      label: n.label,
      x: n.x,
      y: n.y,
      tag: n.tag
    };
  }

  // Active heap pointers: addr -> nextAddr
  const heap: Record<string, string | null> = {};
  for (const n of preset.nodes) {
    heap[n.addr] = n.next;
  }

  // Visible nodes in the graph
  const visibleNodes = new Set<string>(preset.nodes.map((n) => n.addr));

  // Compute dynamic reference count for every visible node
  function computeRCs(
    currentXs: string | null,
    currentRcNode: string | null
  ): Record<string, number> {
    const rcs: Record<string, number> = {};
    for (const addr of visibleNodes) {
      rcs[addr] = 0;
    }

    // 1. External roots
    for (const r of preset.roots) {
      if (rcs[r.targetAddr] !== undefined) {
        rcs[r.targetAddr] += 1;
      }
    }

    // 2. Heap next pointers
    for (const fromAddr of visibleNodes) {
      const toAddr = heap[fromAddr];
      if (toAddr && rcs[toAddr] !== undefined) {
        rcs[toAddr] += 1;
      }
    }

    // 3. Stack variables
    if (currentXs && currentXs !== 'null' && rcs[currentXs] !== undefined) {
      rcs[currentXs] += 1;
    }
    if (currentRcNode && rcs[currentRcNode] !== undefined) {
      rcs[currentRcNode] += 1;
    }

    return rcs;
  }

  function buildArrows(severed: { from: string; to: string } | null): RcArrow[] {
    const arrows: RcArrow[] = [];

    // Root pointer arrows
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

    // Heap arrows
    for (const fromAddr of visibleNodes) {
      if (severed && severed.from === fromAddr) {
        arrows.push({ from: fromAddr, to: severed.to, type: 'severed' });
        continue;
      }

      const toAddr = heap[fromAddr];
      if (!toAddr) {
        arrows.push({ from: fromAddr, to: 'null', type: 'forward' });
      } else if (
        fromAddr.includes("'") ||
        fromAddr.includes('220') ||
        fromAddr.includes('320') ||
        fromAddr.includes('420')
      ) {
        arrows.push({ from: fromAddr, to: toAddr, type: 'cow-backward' });
      } else if (heap[toAddr] === fromAddr || nodeMeta[fromAddr]?.x > (nodeMeta[toAddr]?.x ?? 0)) {
        arrows.push({ from: fromAddr, to: toAddr, type: 'backward' });
      } else {
        arrows.push({ from: fromAddr, to: toAddr, type: 'forward' });
      }
    }

    return arrows;
  }

  const steps: RcStep[] = [];
  const activeRootDef = preset.roots.find((r) => r.name === preset.activeRoot)!;
  let xs: string | null = activeRootDef.targetAddr;
  let acc: string = 'null';

  // Step 0: Initial state
  steps.push({
    lineWhile: 1,
    lineTail: 1,
    xs,
    acc,
    rc_node: null,
    getMut: null,
    nodeRCs: computeRCs(null, null),
    arrows: buildArrows(null),
    visibleNodes: Array.from(visibleNodes),
    title: `Initial State: ${preset.name}`,
    desc: preset.longDesc,
    badge: 'Graph Initialized',
    badgeType: 'slate'
  });

  while (xs && xs !== 'null') {
    const currAddr: string = xs;
    const nextAddr: string | null = heap[currAddr] ?? null;

    // Compute RC to simulate Rc::get_mut(&mut rc_node)
    // Note: In Rust, xs moves into rc_node, decrementing xs and incrementing rc_node (net 0)
    const initialRCs = computeRCs(null, currAddr);
    const currRC = initialRCs[currAddr] || 1;
    const isUnique = currRC === 1;

    // Substep 1: while let Some(mut rc_node) = xs
    steps.push({
      lineWhile: 4,
      lineTail: 3,
      xs: currAddr,
      acc,
      rc_node: currAddr,
      getMut: isUnique
        ? `Some(&mut node) [RC == 1] -> UNIQUE!`
        : `None [RC == ${currRC}] -> SHARED (COW)!`,
      nodeRCs: computeRCs(null, currAddr),
      arrows: buildArrows(null),
      visibleNodes: Array.from(visibleNodes),
      title: `Inspect ${currAddr} (${nodeMeta[currAddr]?.label}): RC = ${currRC}`,
      desc: isUnique
        ? `Rc::get_mut(&mut rc_node) succeeds! Sole owner detected. Proceeding to in-place pointer flip.`
        : `Rc::get_mut(&mut rc_node) fails because RC = ${currRC} > 1. In-place mutation would corrupt other roots. Branching to Copy-on-Write.`,
      badge: isUnique ? 'RC == 1 Unique' : `RC == ${currRC} Shared`,
      badgeType: isUnique ? 'emerald' : 'amber'
    });

    if (isUnique) {
      // --- RC == 1: IN-PLACE REUSE ---
      // Substep 2: let next = node.next.take()
      const severedTarget = nextAddr || 'null';
      heap[currAddr] = null;
      xs = nextAddr;

      steps.push({
        lineWhile: 6,
        lineTail: 5,
        xs: xs || 'null',
        acc,
        rc_node: currAddr,
        getMut: 'Some(&mut node) [RC == 1]',
        nodeRCs: computeRCs(xs, currAddr),
        arrows: buildArrows({ from: currAddr, to: severedTarget }),
        visibleNodes: Array.from(visibleNodes),
        title: `${currAddr}: xs = node.next.take() (Sever Link)`,
        desc: `Forward pointer severed. Next target ${xs || 'null'} moved into xs. ${currAddr} next is temporarily null.`,
        badge: 'Link Severed',
        badgeType: 'amber'
      });

      // Substep 3: node.next = acc
      heap[currAddr] = acc === 'null' ? null : acc;
      acc = currAddr;

      steps.push({
        lineWhile: 7,
        lineTail: 6,
        xs: xs || 'null',
        acc,
        rc_node: currAddr,
        getMut: 'Some(&mut node) [RC == 1]',
        nodeRCs: computeRCs(xs, currAddr),
        arrows: buildArrows(null),
        visibleNodes: Array.from(visibleNodes),
        title: `${currAddr}: node.next = acc (IN-PLACE REUSE)`,
        desc: `${currAddr} is mutated in-place to point backwards to ${acc}. Zero allocations performed! Existing heap block reused.`,
        badge: '0 Allocations',
        badgeType: 'emerald'
      });
    } else {
      // --- RC > 1: COPY-ON-WRITE FALLBACK ---
      // Substep 2: xs = rc_node.next.clone()
      xs = nextAddr;

      steps.push({
        lineWhile: 11,
        lineTail: 10,
        xs: xs || 'null',
        acc,
        rc_node: currAddr,
        getMut: `None [RC == ${currRC}]`,
        nodeRCs: computeRCs(xs, currAddr),
        arrows: buildArrows(null),
        visibleNodes: Array.from(visibleNodes),
        title: `${currAddr}: xs = rc_node.next.clone() (Clone Link)`,
        desc: `Cloning next pointer advances xs to ${xs || 'null'}. If target exists, its reference count increases.`,
        badge: 'Link Cloned',
        badgeType: 'amber'
      });

      // Substep 3: Allocate fresh COW node
      const cowAddr = `${currAddr}'`;
      const originalMeta = nodeMeta[currAddr];
      nodeMeta[cowAddr] = {
        id: `${originalMeta.id}_cow`,
        addr: cowAddr,
        val: originalMeta.val,
        label: `${originalMeta.label}' (COW)`,
        x: originalMeta.x,
        y: originalMeta.y + 150, // Placed on lower COW row
        tag: 'NEW COW ALLOC'
      };
      visibleNodes.add(cowAddr);
      heap[cowAddr] = acc === 'null' ? null : acc;
      acc = cowAddr;

      steps.push({
        lineWhile: 12,
        lineTail: 13,
        xs: xs || 'null',
        acc,
        rc_node: null,
        getMut: 'None [COW Alloc]',
        nodeRCs: computeRCs(xs, null), // rc_node is dropped at end of body!
        arrows: buildArrows(null),
        visibleNodes: Array.from(visibleNodes),
        title: `Allocate Fresh Node ${cowAddr} via Copy-on-Write`,
        desc: `Rc::new allocates brand-new heap cell ${cowAddr} pointing backward to ${heap[cowAddr] || 'null'}. rc_node drops, lowering ${currAddr} RC back down.`,
        badge: 'COW New Alloc',
        badgeType: 'purple'
      });
    }
  }

  // Base Case
  steps.push({
    lineWhile: 19,
    lineTail: 17,
    xs: 'null',
    acc,
    rc_node: null,
    getMut: null,
    nodeRCs: computeRCs(null, null),
    arrows: buildArrows(null),
    visibleNodes: Array.from(visibleNodes),
    title: 'Reversal Complete: Safe & Valid',
    desc: `Reversed list head starting at ${acc} is returned. All shared branches remain 100% intact with zero memory corruption.`,
    badge: 'Reversal Done',
    badgeType: 'emerald'
  });

  return { steps, nodeMeta };
}
