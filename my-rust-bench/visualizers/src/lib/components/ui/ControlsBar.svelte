<script lang="ts">
  let {
    stepIdx = $bindable(),
    totalSteps,
    isPlaying = $bindable(),
    speed = $bindable(),
    accentColor = 'emerald'
  }: {
    stepIdx: number;
    totalSteps: number;
    isPlaying: boolean;
    speed: number;
    accentColor?: 'emerald' | 'purple';
  } = $props();

  const playBtnClasses = {
    emerald: 'bg-emerald-600 hover:bg-emerald-500 text-white',
    purple: 'bg-purple-600 hover:bg-purple-500 text-white'
  };
</script>

<div
  class="flex flex-wrap items-center justify-between gap-3 rounded-xl border border-slate-800 bg-slate-900 p-3 shadow-lg"
>
  <div class="flex items-center gap-1.5">
    <button
      class="rounded border border-slate-700 bg-slate-800 px-2.5 py-1.5 text-xs text-slate-200 transition-colors hover:bg-slate-700 disabled:opacity-40"
      disabled={stepIdx === 0}
      onclick={() => {
        stepIdx = 0;
      }}
    >
      ⏮ Reset
    </button>
    <button
      class="rounded border border-slate-700 bg-slate-800 px-2.5 py-1.5 text-xs text-slate-200 transition-colors hover:bg-slate-700 disabled:opacity-40"
      disabled={stepIdx === 0}
      onclick={() => {
        stepIdx = Math.max(0, stepIdx - 1);
      }}
    >
      ◀ Prev
    </button>
    <button
      class="rounded px-3.5 py-1.5 text-xs font-semibold transition-colors {playBtnClasses[
        accentColor
      ]}"
      onclick={() => {
        isPlaying = !isPlaying;
      }}
    >
      {isPlaying ? '⏸ Pause' : '▶ Play'}
    </button>
    <button
      class="rounded border border-slate-700 bg-slate-800 px-2.5 py-1.5 text-xs text-slate-200 transition-colors hover:bg-slate-700 disabled:opacity-40"
      disabled={stepIdx === totalSteps - 1}
      onclick={() => {
        stepIdx = Math.min(totalSteps - 1, stepIdx + 1);
      }}
    >
      Next ▶
    </button>
  </div>

  <div class="flex items-center gap-2 font-mono text-xs text-slate-400">
    <span class="whitespace-nowrap">{(speed / 1000).toFixed(1)}s</span>
    <input
      type="range"
      min="400"
      max="3000"
      step="200"
      bind:value={speed}
      class="w-24 accent-purple-400"
    />
  </div>
</div>
