<script lang="ts">
  let {
    title,
    desc,
    stepNum,
    totalSteps,
    badge,
    badgeType = 'emerald'
  }: {
    title: string;
    desc: string;
    stepNum: number;
    totalSteps: number;
    badge?: string;
    badgeType?: 'emerald' | 'amber' | 'purple' | 'slate';
  } = $props();

  const badgeColors = {
    emerald: 'bg-emerald-500/20 text-emerald-300 border-emerald-500/30',
    amber: 'bg-amber-500/20 text-amber-300 border-amber-500/30',
    purple: 'bg-purple-500/20 text-purple-300 border-purple-500/30',
    slate: 'bg-slate-800 text-slate-400 border-slate-700'
  };
</script>

<div class="rounded-xl border border-slate-800 bg-slate-900/90 p-4 shadow-lg">
  <div class="mb-1 flex items-center justify-between">
    <div class="font-mono text-xs font-semibold tracking-wider text-slate-300 uppercase">
      Step {stepNum} of {totalSteps}: <span class="font-bold text-white">{title}</span>
    </div>
    {#if badge}
      <span
        class="rounded border px-2.5 py-0.5 font-mono text-xs font-semibold {badgeColors[
          badgeType
        ]}"
      >
        {badge}
      </span>
    {/if}
  </div>
  <p class="mt-1 text-sm text-slate-300">{desc}</p>
</div>
