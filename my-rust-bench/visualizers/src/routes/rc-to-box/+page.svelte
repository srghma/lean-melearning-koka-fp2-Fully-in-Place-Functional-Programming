<script lang="ts">
  import type { AlgoMode, RegisterItem } from '#lib/types/common';
  import { RC_TO_BOX_WHILE_CODE, RC_TO_BOX_TAIL_CODE } from '#lib/models/rc-to-box/code';
  import { RC_TO_BOX_PRESETS } from '#lib/models/rc-to-box/presets';
  import { simulateRcToBox } from '#lib/models/rc-to-box/simulator';
  import NarrativeBox from '#lib/components/execution/NarrativeBox.svelte';
  import CodePanel from '#lib/components/execution/CodePanel.svelte';
  import RegistersPanel from '#lib/components/execution/RegistersPanel.svelte';
  import ControlsBar from '#lib/components/ui/ControlsBar.svelte';
  import AlgoToggle from '#lib/components/ui/AlgoToggle.svelte';
  import HeapBox from '#lib/components/heap/HeapBox.svelte';
  import ForwardArrow from '#lib/components/heap/ForwardArrow.svelte';
  import RcPresetTabs from '#lib/components/rc/RcPresetTabs.svelte';

  let selectedPresetId = $state(RC_TO_BOX_PRESETS[0].id);
  let algoMode = $state<AlgoMode>('while');
  let stepIdx = $state(0);
  let isPlaying = $state(false);
  let speed = $state(1600);

  const activePreset = $derived(
    RC_TO_BOX_PRESETS.find((p) => p.id === selectedPresetId) || RC_TO_BOX_PRESETS[0]
  );
  const { steps, nodeMeta } = $derived(simulateRcToBox(activePreset));
  const current = $derived(steps[stepIdx] || steps[0]);
  const codeLines = $derived(algoMode === 'while' ? RC_TO_BOX_WHILE_CODE : RC_TO_BOX_TAIL_CODE);
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
    { label: 'xs (input Rc)', val: current.xs, color: 'border-sky-500 text-sky-400' },
    {
      label: 'acc (Box accumulator)',
      val: current.acc,
      color: 'border-emerald-500 text-emerald-400'
    },
    {
      label: 'rc_node (under test)',
      val: current.rc_node || '—',
      color: 'border-amber-500 text-amber-400'
    },
    {
      label: 'Rc::try_unwrap(rc_node)',
      val: current.unwrapResult || 'idle',
      color:
        current.unwrapResult && current.unwrapResult.includes('Ok')
          ? 'border-emerald-500 text-emerald-400'
          : current.unwrapResult
            ? 'border-amber-500 text-amber-400'
            : 'border-slate-700 text-slate-500'
    }
  ]);
</script>

<div class="mx-auto max-w-6xl space-y-6 px-6">
  <div class="flex items-center justify-between border-b border-slate-800 pb-4">
    <div>
      <h1 class="flex items-center gap-3 text-2xl font-bold tracking-tight text-white">
        Rc &rarr; Box Reversal (Shared &rarr; Unique)
        <span
          class="rounded border border-emerald-500/30 bg-emerald-500/20 px-2 py-0.5 font-mono text-xs text-emerald-300"
        >
          List a &rarr; List a &lcub;Unique&rcub;
        </span>
      </h1>
      <p class="mt-1 text-sm text-slate-400">{activePreset.shortDesc}</p>
    </div>
    <AlgoToggle bind:algoMode accentColor="emerald" />
  </div>

  <div class="space-y-3">
    <div class="font-mono text-xs font-semibold tracking-wider text-slate-400 uppercase">
      Select Scenario Preset:
    </div>
    <RcPresetTabs
      presets={RC_TO_BOX_PRESETS}
      bind:selectedId={selectedPresetId}
      onSelect={() => {
        stepIdx = 0;
        isPlaying = false;
      }}
    />
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
    <div class="flex flex-col gap-4 md:col-span-5">
      <RegistersPanel title="CPU Registers & try_unwrap Check" {registers} />
      <ControlsBar
        bind:stepIdx
        totalSteps={steps.length}
        bind:isPlaying
        bind:speed
        accentColor="emerald"
      />
    </div>
  </div>

  <!-- Heap Canvas -->
  <div class="rounded-xl border border-slate-800 bg-slate-900 p-5">
    <div
      class="mb-2 flex justify-between font-mono text-xs font-semibold tracking-wider text-slate-400 uppercase"
    >
      <span>Dual Memory Canvas: Top (Shared Rc) &rarr; Bottom (Unique Box Accumulator)</span>
      <span class="text-slate-500">Rc::try_unwrap Unlocks 0 Atomic Updates When Unique</span>
    </div>

    <div class="overflow-x-auto py-2">
      <svg width={activePreset.canvasWidth} height={activePreset.canvasHeight} class="select-none">
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

        <!-- External Roots Tags -->
        {#each activePreset.roots as root (root.name)}
          {@const target = nodeMeta[root.targetAddr]}
          {#if target}
            <g>
              <rect
                x={target.x - 30}
                y={target.y - 24}
                width="65"
                height="18"
                rx="4"
                fill="#0f172a"
                stroke={root.color}
                stroke-width="1.5"
              />
              <text
                x={target.x - 24}
                y={target.y - 12}
                fill={root.color}
                font-size="10"
                font-family="monospace"
                font-weight="bold"
              >
                {root.name}
              </text>
              <line
                x1={target.x + 5}
                y1={target.y - 6}
                x2={target.x + 10}
                y2={target.y + 12}
                stroke={root.color}
                stroke-width="1.5"
              />
            </g>
          {/if}
        {/each}

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
                {:else if ar.type === 'backward'}
                  <ForwardArrow
                    x1={src.x}
                    y1={src.y + 40}
                    x2={dst.x + 140}
                    y2={dst.y + 40}
                    color="#10b981"
                    markerId="arrow-backward"
                  />
                {/if}
              {/if}
            {/if}
          {/if}
        {/each}

        <!-- Top Row: Rc Nodes -->
        {#each current.rcNodes as addr (addr)}
          {@const meta = nodeMeta[addr]}
          {#if meta}
            {@const rc = current.nodeRCs[addr] || 0}
            <HeapBox
              x={meta.x}
              y={meta.y}
              width={140}
              height={80}
              address={meta.addr}
              val={meta.val}
              {rc}
              kind="rc"
              tag={meta.tag}
              isCurrent={current.rc_node === addr}
            />
          {/if}
        {/each}

        <!-- Bottom Row: Box Accumulator Nodes -->
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
              isAcc={current.acc === addr}
            />
          {/if}
        {/each}
      </svg>
    </div>
  </div>
</div>
