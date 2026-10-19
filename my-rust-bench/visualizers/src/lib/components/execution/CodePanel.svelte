<script lang="ts">
  import type { CodeLine } from '#lib/types/common';

  let {
    lines,
    activeLine,
    modeTitle,
    accentColor = 'emerald'
  }: {
    lines: CodeLine[];
    activeLine: number;
    modeTitle: string;
    accentColor?: 'emerald' | 'purple';
  } = $props();

  const activeClasses = {
    emerald: 'bg-emerald-500/20 text-emerald-200 font-bold border-l-2 border-emerald-400',
    purple: 'bg-purple-500/20 text-purple-200 font-bold border-l-2 border-purple-400'
  };
</script>

<div class="rounded-xl border border-slate-800 bg-slate-900 p-4 font-mono text-xs">
  <div
    class="mb-3 flex justify-between border-b border-slate-800 pb-1 text-[11px] font-semibold tracking-wider text-slate-400 uppercase"
  >
    <span>Active Execution Frame</span>
    <span class={accentColor === 'purple' ? 'text-purple-400' : 'text-emerald-400'}
      >{modeTitle}</span
    >
  </div>
  <div class="space-y-0.5">
    {#each lines as line (line.num)}
      {@const isActive = line.num === activeLine}
      <div
        class="flex items-center rounded px-2 py-0.5 transition-colors {isActive
          ? activeClasses[accentColor]
          : 'text-slate-400'}"
      >
        <span class="w-6 shrink-0 text-[10px] text-slate-600 select-none">{line.num}</span>
        <span class="font-mono whitespace-pre">{line.text}</span>
      </div>
    {/each}
  </div>
</div>
