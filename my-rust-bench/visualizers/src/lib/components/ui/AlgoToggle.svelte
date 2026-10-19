<script lang="ts">
  import type { AlgoMode } from '#lib/types/common';

  let {
    algoMode = $bindable(),
    accentColor = 'emerald'
  }: {
    algoMode: AlgoMode;
    accentColor?: 'emerald' | 'purple';
  } = $props();

  const activeClasses = {
    emerald: 'bg-emerald-600 text-white font-semibold',
    purple: 'bg-purple-600 text-white font-semibold'
  };
</script>

<div class="flex items-center gap-1 rounded-lg border border-slate-800 bg-slate-900 p-1">
  <button
    class="rounded px-2.5 py-1 font-mono text-xs transition-colors {algoMode === 'while'
      ? activeClasses[accentColor]
      : 'text-slate-400 hover:text-slate-200'}"
    onclick={() => {
      algoMode = 'while';
    }}
  >
    while-loop
  </button>
  <button
    class="rounded px-2.5 py-1 font-mono text-xs transition-colors {algoMode === 'tail'
      ? activeClasses[accentColor]
      : 'text-slate-400 hover:text-slate-200'}"
    onclick={() => {
      algoMode = 'tail';
    }}
  >
    tail-rec (FIP)
  </button>
</div>
