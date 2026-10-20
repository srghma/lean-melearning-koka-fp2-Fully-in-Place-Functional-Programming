<script lang="ts">
  import type { AlgoMode, RegisterItem } from '#lib/types/common';
  import { BOX_TO_BOX_WHILE_CODE, BOX_TO_BOX_TAIL_CODE } from '#lib/models/box-to-box/code';
  import { generateNoRcSteps } from '#lib/models/box-to-box/generator';
  import NarrativeBox from '#lib/components/execution/NarrativeBox.svelte';
  import CodePanel from '#lib/components/execution/CodePanel.svelte';
  import RegistersPanel from '#lib/components/execution/RegistersPanel.svelte';
  import ControlsBar from '#lib/components/ui/ControlsBar.svelte';
  import AlgoToggle from '#lib/components/ui/AlgoToggle.svelte';
  import HeapBox from '#lib/components/heap/HeapBox.svelte';
  import ForwardArrow from '#lib/components/heap/ForwardArrow.svelte';
  import CurvedArrow from '#lib/components/heap/CurvedArrow.svelte';
  import SeveredArrow from '#lib/components/heap/SeveredArrow.svelte';

  let values = $state([1, 2, 3]);
  let inputStr = $state('1, 2, 3');
  let stepIdx = $state(0);
  let isPlaying = $state(false);
  let speed = $state(1500);
  let algoMode = $state<AlgoMode>('while');

  const { steps, addresses } = $derived(generateNoRcSteps(values));
  const current = $derived(steps[stepIdx] || steps[0]);
  const codeLines = $derived(algoMode === 'while' ? BOX_TO_BOX_WHILE_CODE : BOX_TO_BOX_TAIL_CODE);
  const activeLine = $derived(algoMode === 'while' ? current.lineWhile : current.lineTail);

  $effect(() => {
    if (!isPlaying) return;
    const timer = setTimeout(() => {
      if (stepIdx < steps.length - 1) {
        stepIdx += 1;
      } else {
        isPlaying = false;
      }
    }, speed);
    return () => clearTimeout(timer);
  });

  const registers = $derived<RegisterItem[]>([
    {
      label: 'xs (input head)',
      val: current.xs !== null ? addresses[current.xs] : 'null (None)',
      color: 'border-sky-500 text-sky-400'
    },
    {
      label: 'acc (accumulator)',
      val: current.acc !== null ? addresses[current.acc] : 'null (None)',
      color: 'border-emerald-500 text-emerald-400'
    },
    {
      label: 'node (owned box)',
      val: current.node !== null ? addresses[current.node] : '—',
      color: 'border-amber-500 text-amber-400'
    },
    {
      label: 'next (rest of list)',
      val:
        current.next !== null
          ? addresses[current.next]
          : current.node !== null
            ? 'null (0x0)'
            : '—',
      color: 'border-purple-500 text-purple-400'
    }
  ]);

  function handleUpdateList() {
    const parsed = inputStr
      .split(',')
      .map((s) => parseInt(s.trim(), 10))
      .filter((n) => !isNaN(n));
    if (parsed.length >= 2 && parsed.length <= 6) {
      values = parsed;
      stepIdx = 0;
      isPlaying = false;
    }
  }

  const nodeW = 140;
  const nodeH = 85;
  const gap = 80;
  const startX = 40;
  const heapY = 60;
</script>

<div class="mx-auto max-w-6xl space-y-6 px-6">
  <div class="flex items-center justify-between border-b border-slate-800 pb-4">
    <div>
      <h1 class="flex items-center gap-3 text-2xl font-bold tracking-tight text-white">
        No-RC List Reversal (Box&lt;Node&gt;)
        <span
          class="rounded border border-emerald-500/30 bg-emerald-500/20 px-2 py-0.5 font-mono text-xs text-emerald-300"
        >
          Zero Allocation O(1) Stack
        </span>
      </h1>
      <p class="mt-1 text-sm text-slate-400">
        Unique ownership enables in-place mutation of existing heap cells.
      </p>
    </div>

    <div class="flex items-center gap-3">
      <AlgoToggle bind:algoMode accentColor="emerald" />
      <div class="flex items-center gap-2">
        <input
          class="w-32 rounded border border-slate-700 bg-slate-900 px-2 py-1.5 font-mono text-xs text-slate-200 focus:border-emerald-500 focus:outline-none"
          bind:value={inputStr}
        />
        <button
          class="rounded border border-slate-700 bg-slate-800 px-3 py-1.5 text-xs text-slate-200 hover:bg-slate-700"
          onclick={handleUpdateList}
        >
          Set List
        </button>
      </div>
    </div>
  </div>

  <NarrativeBox
    title={current.title}
    desc={current.desc}
    stepNum={stepIdx + 1}
    totalSteps={steps.length}
    badge={current.badge}
    badgeType={current.badgeType}
  />

  <div class="grid grid-cols-1 gap-6 md:grid-cols-12">
    <div class="md:col-span-7">
      <CodePanel
        lines={codeLines}
        {activeLine}
        modeTitle={algoMode === 'while' ? 'Iterative while let' : 'Tail-Recursive inlined'}
        accentColor="emerald"
      />
    </div>
    <div class="md:col-span-5">
      <RegistersPanel {registers} />
    </div>
  </div>

  <!-- Heap Canvas -->
  <div class="rounded-xl border border-slate-800 bg-slate-900 p-5">
    <div
      class="mb-2 flex justify-between font-mono text-xs font-semibold tracking-wider text-slate-400 uppercase"
    >
      <span>Physical Heap Memory (Nodes Never Move)</span>
      <span class="text-slate-500">64-bit Pointer | In-Place Overwrite</span>
    </div>

    <div class="overflow-x-auto py-4">
      <svg
        width={Math.max(760, values.length * (nodeW + gap) + 120)}
        height="240"
        class="select-none"
      >
        <defs>
          <marker
            id="arrow-forward"
            markerWidth="8"
            markerHeight="8"
            refX="6"
            refY="4"
            orient="auto"
          >
            <path d="M0,1 L7,4 L0,7 Z" fill="#38bdf8" />
          </marker>
          <marker
            id="arrow-backward"
            markerWidth="8"
            markerHeight="8"
            refX="6"
            refY="4"
            orient="auto"
          >
            <path d="M0,1 L7,4 L0,7 Z" fill="#10b981" />
          </marker>
        </defs>

        {#each current.heap as targetIdx, srcIdx (srcIdx)}
          {@const x1 = startX + srcIdx * (nodeW + gap)}
          {#if targetIdx === null}
            <g>
              <line
                x1={x1 + nodeW}
                y1={heapY + 42}
                x2={x1 + nodeW + 30}
                y2={heapY + 42}
                stroke="#64748b"
                stroke-width="2"
              />
              <text
                x={x1 + nodeW + 36}
                y={heapY + 46}
                fill="#64748b"
                font-size="10"
                font-family="monospace">null</text
              >
            </g>
          {:else if targetIdx > srcIdx}
            <ForwardArrow
              x1={x1 + nodeW}
              y1={heapY + 42}
              x2={startX + targetIdx * (nodeW + gap)}
              y2={heapY + 42}
            />
          {:else}
            {@const x2 = startX + targetIdx * (nodeW + gap)}
            {@const startPtX = x1 + nodeW / 2}
            {@const endPtX = x2 + nodeW / 2}
            {@const arcY = heapY + nodeH + 45}
            {@const d = `M ${startPtX} ${heapY + nodeH} Q ${(startPtX + endPtX) / 2} ${arcY + 30} ${endPtX} ${heapY + nodeH}`}
            <CurvedArrow {d} />
          {/if}
        {/each}

        {#if current.severed && current.severed.to !== null}
          <SeveredArrow
            x1={startX + current.severed.from * (nodeW + gap) + nodeW}
            y1={heapY + 42}
            x2={startX + current.severed.to * (nodeW + gap)}
            y2={heapY + 42}
          />
        {/if}

        {#each values as val, idx (idx)}
          {@const x = startX + idx * (nodeW + gap)}
          <HeapBox
            {x}
            y={heapY}
            width={nodeW}
            height={nodeH}
            address={addresses[idx]}
            {val}
            nextText={current.heap[idx] !== null ? addresses[current.heap[idx]!] : 'null'}
            isCurrent={current.node === idx}
            isAcc={current.acc === idx}
            isXs={current.xs === idx}
          />
        {/each}
      </svg>
    </div>
  </div>

  <ControlsBar
    bind:stepIdx
    totalSteps={steps.length}
    bind:isPlaying
    bind:speed
    accentColor="emerald"
  />
</div>
