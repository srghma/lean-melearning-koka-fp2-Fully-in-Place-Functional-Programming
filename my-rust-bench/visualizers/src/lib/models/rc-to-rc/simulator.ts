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

  const heap: Record<string, string | null> = {};
  for (const n of preset.nodes) {
    heap[n.addr] = n.next;
  }

  const visibleNodes = new Set<string>(preset.nodes.map((n) => n.addr));

  function computeRCs(
    currentXs: string | null,
    currentRcNode: string | null,
    currentAcc: string | null
  ): Record<string, number> {
    const rcs: Record<string, number> = {};
    for (const addr of visibleNodes) {
      rcs[addr] = 0;
    }

    // 1. External roots (exclude activeRoot: it's on stack via xs/rc_node/acc)
    for (const r of preset.roots) {
      if (r.name !== preset.activeRoot && rcs[r.targetAddr] !== undefined) {
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

    // 3. Stack variables (xs, rc_node, acc)
    if (currentXs && currentXs !== 'null' && rcs[currentXs] !== undefined) {
      rcs[currentXs] += 1;
    }
    if (currentRcNode && currentRcNode !== 'null' && rcs[currentRcNode] !== undefined) {
      rcs[currentRcNode] += 1;
    }
    if (currentAcc && currentAcc !== 'null' && rcs[currentAcc] !== undefined) {
      rcs[currentAcc] += 1;
    }

    return rcs;
  }

  function buildArrows(severed: { from: string; to: string } | null): RcArrow[] {
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

    for (const fromAddr of visibleNodes) {
      if (severed && severed.from === fromAddr) {
        arrows.push({ from: fromAddr, to: severed.to, type: 'severed' });
        continue;
      }

      const toAddr = heap[fromAddr];
      if (!toAddr) {
        arrows.push({ from: fromAddr, to: 'null', type: 'forward' });
      } else if (fromAddr.includes("'")) {
        arrows.push({ from: fromAddr, to: toAddr, type: 'cow-backward' });
      } else if (nodeMeta[fromAddr]?.x > (nodeMeta[toAddr]?.x ?? 0)) {
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
    nodeRCs: computeRCs(xs, null, null),
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

    // Substep 1: xs moves into rc_node (While: line 3, Tail: line 3)
    steps.push({
      lineWhile: 3,
      lineTail: 3,
      xs: 'null',
      acc,
      rc_node: currAddr,
      getMut: 'evaluating...',
      nodeRCs: computeRCs(null, currAddr, acc),
      arrows: buildArrows(null),
      visibleNodes: Array.from(visibleNodes),
      title: `Fetch: Some(mut rc_node) = ${currAddr}`,
      desc: `Input head ${currAddr} is matched into local variable rc_node. xs register is now None.`,
      badge: `Fetch ${currAddr}`,
      badgeType: 'slate'
    });

    // Substep 2: Test Uniqueness via Rc::get_mut (While: line 4, Tail: line 4)
    const initialRCs = computeRCs(null, currAddr, acc);
    const currRC = initialRCs[currAddr] || 1;
    const isUnique = currRC === 1;

    steps.push({
      lineWhile: 4,
      lineTail: 4,
      xs: 'null',
      acc,
      rc_node: currAddr,
      getMut: isUnique
        ? `Some(&mut node) [RC == 1] -> UNIQUE!`
        : `None [RC == ${currRC}] -> SHARED (COW)!`,
      nodeRCs: computeRCs(null, currAddr, acc),
      arrows: buildArrows(null),
      visibleNodes: Array.from(visibleNodes),
      title: `Inspect ${currAddr} (${nodeMeta[currAddr]?.label}): RC = ${currRC}`,
      desc: isUnique
        ? `Rc::get_mut(&mut rc_node) succeeds (RC == 1). In-place pointer flip without allocation.`
        : `Rc::get_mut(&mut rc_node) returns None (RC = ${currRC} > 1). Branching to Copy-on-Write.`,
      badge: isUnique ? 'RC == 1 Unique' : `RC == ${currRC} Shared`,
      badgeType: isUnique ? 'emerald' : 'amber'
    });

    if (isUnique) {
      // --- RC == 1: IN-PLACE REUSE ---
      // Substep 3: xs = node.next.take() (While: line 6, Tail: line 6)
      const severedTarget = nextAddr;
      heap[currAddr] = null;
      xs = nextAddr;

      steps.push({
        lineWhile: 6,
        lineTail: 6,
        xs: xs || 'null',
        acc,
        rc_node: currAddr,
        getMut: 'Some(&mut node) [RC == 1]',
        nodeRCs: computeRCs(xs, currAddr, acc),
        arrows: buildArrows(severedTarget ? { from: currAddr, to: severedTarget } : null),
        visibleNodes: Array.from(visibleNodes),
        title: `${currAddr}: xs = node.next.take() (Sever Link)`,
        desc: `Forward link severed. Next target ${xs || 'null'} moved into xs. ${currAddr} next is temporarily null.`,
        badge: 'Link Severed',
        badgeType: 'amber'
      });

      // Substep 4: node.next = acc (While: line 7, Tail: line 7)
      heap[currAddr] = acc === 'null' ? null : acc;

      steps.push({
        lineWhile: 7,
        lineTail: 7,
        xs: xs || 'null',
        acc, // acc still holds previous accumulator head
        rc_node: currAddr,
        getMut: 'Some(&mut node) [RC == 1]',
        nodeRCs: computeRCs(xs, currAddr, acc),
        arrows: buildArrows(null),
        visibleNodes: Array.from(visibleNodes),
        title: `${currAddr}: node.next = acc (Pointer Flip)`,
        desc: `Existing heap cell ${currAddr} is flipped backwards to point to ${heap[currAddr] || 'null'}.`,
        badge: 'Pointer Flipped',
        badgeType: 'emerald'
      });

      // Substep 5: acc = Some(rc_node) / Tail call (While: line 8, Tail: line 8)
      acc = currAddr;

      steps.push({
        lineWhile: 8,
        lineTail: 8,
        xs: xs || 'null',
        acc, // NOW acc updates to currAddr
        rc_node: null, // rc_node moved into acc
        getMut: 'Some(&mut node) [RC == 1]',
        nodeRCs: computeRCs(xs, null, acc),
        arrows: buildArrows(null),
        visibleNodes: Array.from(visibleNodes),
        title: `acc = Some(rc_node): Advance Accumulator`,
        desc: `Reused node ${acc} is pushed as the new head of accumulator. 0 allocations!`,
        badge: '0 Allocations',
        badgeType: 'emerald'
      });
    } else {
      // --- RC > 1: COPY-ON-WRITE FALLBACK ---
      // Substep 3: xs = rc_node.next.clone() (While: line 11, Tail: line 11)
      xs = nextAddr;

      steps.push({
        lineWhile: 11,
        lineTail: 11,
        xs: xs || 'null',
        acc,
        rc_node: currAddr,
        getMut: `None [RC == ${currRC}]`,
        nodeRCs: computeRCs(xs, currAddr, acc),
        arrows: buildArrows(null),
        visibleNodes: Array.from(visibleNodes),
        title: `${currAddr}: xs = rc_node.next.clone() (Clone Link)`,
        desc: `Cloned next pointer. xs advances to ${xs || 'null'}. Target's reference count increases to 2.`,
        badge: 'Link Cloned',
        badgeType: 'amber'
      });

      // Substep 4: Allocate fresh COW node & drop rc_node (While: line 12, Tail: line 14)
      const cowAddr = `${currAddr}'`;
      const originalMeta = nodeMeta[currAddr];
      const cowY =
        preset.id === 'three-way' ? 365 : preset.id === 'shared-tail' ? 260 : originalMeta.y + 140;

      nodeMeta[cowAddr] = {
        id: `${originalMeta.id}_cow`,
        addr: cowAddr,
        val: originalMeta.val,
        label: `${originalMeta.label}' (COW)`,
        x: originalMeta.x,
        y: cowY,
        tag: 'NEW COW ALLOC'
      };
      visibleNodes.add(cowAddr);
      heap[cowAddr] = acc === 'null' ? null : acc;
      acc = cowAddr;

      steps.push({
        lineWhile: 12,
        lineTail: 14,
        xs: xs || 'null',
        acc,
        rc_node: null, // explicitly dropped before tail call
        getMut: 'None [COW Alloc]',
        nodeRCs: computeRCs(xs, null, acc),
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
    lineTail: 18,
    xs: 'null',
    acc,
    rc_node: null,
    getMut: null,
    nodeRCs: computeRCs(null, null, acc),
    arrows: buildArrows(null),
    visibleNodes: Array.from(visibleNodes),
    title: 'Reversal Complete: Safe & Valid',
    desc: `Reversed list starting at ${acc} is returned. All shared branches remain 100% intact with zero memory corruption.`,
    badge: 'Reversal Done',
    badgeType: 'emerald'
  });

  return { steps, nodeMeta };
}
