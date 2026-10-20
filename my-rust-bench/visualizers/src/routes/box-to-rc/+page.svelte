<script lang="ts">
  import type { AlgoMode, RegisterItem } from '#lib/types/common';
  import { BOX_TO_RC_WHILE_CODE, BOX_TO_RC_TAIL_CODE } from '#lib/models/box-to-rc/code';
  import { generateBoxToRcSteps } from '#lib/models/box-to-rc/generator';
  import NarrativeBox from '#lib/components/execution/NarrativeBox.svelte';
  import CodePanel from '#lib/components/execution/CodePanel.svelte';
  import RegistersPanel from '#lib/components/execution/RegistersPanel.svelte';
  import ControlsBar from '#lib/components/ui/ControlsBar.svelte';
  import AlgoToggle from '#lib/components/ui/AlgoToggle.svelte';
  import HeapBox from '#lib/components/heap/HeapBox.svelte';
  import ForwardArrow from '#lib/components/heap/ForwardArrow.svelte';
  import SeveredArrow from '#lib/components/heap/SeveredArrow.svelte';

  let values = $state([1, 2, 3]);
  let algoMode = $state<AlgoMode>('while');
  let stepIdx = $state(0);
  let isPlaying = $state(false);
  let speed = $state(1500);

  const { steps, nodeMeta } = $derived(generateBoxToRcSteps(values));
  const current = $derived(steps[stepIdx] || steps[0]);
  const codeLines = $derived(algoMode === 'while' ? BOX_TO_RC_WHILE_CODE : BOX_TO_RC_TAIL_CODE);
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
    { label: 'xs (input Box)', val: current.xs, color: 'border-sky-500 text-sky-400' },
    { label: 'acc (Rc accumulator)', val: current.acc, color: 'border-purple-500 text-purple-400' },
    {
      label: 'box_node (unwrapped)',
      val: current.box_node || '—',
      color: 'border-amber-500 text-amber-400'
    }
  ]);
</script>

<div class="mx-auto max-w-6xl space-y-6 px-6">
  <div class="flex items-center justify-between border-b border-slate-800 pb-4">
    <div>
      <h1 class="flex items-center gap-3 text-2xl font-bold tracking-tight text-white">
        Box &rarr; Rc Reversal (Unique &rarr; Shared)
        <span
          class="rounded border border-purple-500/30 bg-purple-500/20 px-2 py-0.5 font-mono text-xs text-purple-300"
        >
          List a &lcub;Unique&rcub; &rarr; List a
        </span>
      </h1>
      <p class="mt-1 text-sm text-slate-400">
        Takes linear unique Box cells and encapsulates them into Rc reference-counted control
        blocks.
      </p>
    </div>
    <AlgoToggle bind:algoMode accentColor="purple" />
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
        accentColor="purple"
      />
    </div>
    <div class="flex flex-col gap-4 md:col-span-5">
      <RegistersPanel title="CPU Registers & Acc" {registers} />
      <ControlsBar
        bind:stepIdx
        totalSteps={steps.length}
        bind:isPlaying
        bind:speed
        accentColor="purple"
      />
    </div>
  </div>

  <!-- Heap Canvas -->
  <div class="rounded-xl border border-slate-800 bg-slate-900 p-5">
    <div
      class="mb-2 flex justify-between font-mono text-xs font-semibold tracking-wider text-slate-400 uppercase"
    >
      <span>Dual Memory Canvas: Top (Unique Box) &rarr; Bottom (Shared Rc Control Blocks)</span>
      <span class="text-slate-500">Rc::new Allocates Strong=1, Weak=0 Headers</span>
    </div>

    <div class="overflow-x-auto py-2">
      <svg width={Math.max(760, values.length * 220 + 80)} height="360" class="select-none">
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
            <path d="M0,1 L7,4 L0,7 Z" fill="#c084fc" />
          </marker>
        </defs>

        <!-- Arrows -->
        {#each current.arrows as ar, i (i)}
          {@const src = nodeMeta[ar.from]}
          {#if src}
            {#if ar.to === 'null'}
              <g>
                <line
                  x1={src.x + 140}
                  y1={src.y + 40}
                  x2={src.x + 175}
                  y2={src.y + 40}
                  stroke="#64748b"
                  stroke-width="2"
                />
                <text
                  x={src.x + 182}
                  y={src.y + 44}
                  fill="#64748b"
                  font-size="11"
                  font-family="monospace">null</text
                >
              </g>
            {:else}
              {@const dst = nodeMeta[ar.to]}
              {#if dst}
                {#if ar.type === 'forward'}
                  <ForwardArrow x1={src.x + 140} y1={src.y + 40} x2={dst.x} y2={dst.y + 40} />
                {:else if ar.type === 'severed'}
                  <SeveredArrow x1={src.x + 140} y1={src.y + 40} x2={dst.x} y2={dst.y + 40} />
                {:else if ar.type === 'backward'}
                  <ForwardArrow
                    x1={src.x}
                    y1={src.y + 40}
                    x2={dst.x + 140}
                    y2={dst.y + 40}
                    color="#c084fc"
                    markerId="arrow-backward"
                  />
                {/if}
              {/if}
            {/if}
          {/if}
        {/each}

        <!-- Top Row: Box Nodes -->
        {#each current.boxNodes as addr (addr)}
          {@const meta = nodeMeta[addr]}
          {#if meta}
            <HeapBox
              x={meta.x}
              y={meta.y}
              width={140}
              height={80}
              address={meta.addr}
              val={meta.val}
              kind="box"
              tag={meta.tag}
              isCurrent={current.box_node === addr}
            />
          {/if}
        {/each}

        <!-- Bottom Row: Rc Accumulator Nodes -->
        {#each current.rcNodes as addr (addr)}
          {@const meta = nodeMeta[addr]}
          {#if meta}
            <HeapBox
              x={meta.x}
              y={meta.y}
              width={140}
              height={80}
              address={meta.addr}
              val={meta.val}
              rc={1}
              kind="rc"
              tag={meta.tag}
              isAcc={current.acc === addr}
            />
          {/if}
        {/each}
      </svg>
    </div>
  </div>
</div>
