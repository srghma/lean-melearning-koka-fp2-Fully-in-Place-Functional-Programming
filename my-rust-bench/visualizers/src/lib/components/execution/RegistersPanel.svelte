<script lang="ts">
  import type { RegisterItem } from '#lib/types/common';

  let {
    title = 'CPU Registers / Stack Pointers',
    registers
  }: {
    title?: string;
    registers: RegisterItem[];
  } = $props();
</script>

<div class="rounded-xl border border-slate-800 bg-slate-900 p-4 font-mono text-xs">
  <div
    class="mb-3 border-b border-slate-800 pb-1 text-[11px] font-semibold tracking-wider text-slate-400 uppercase"
  >
    {title}
  </div>
  <div class="space-y-2">
    {#each registers as reg (reg.label)}
      <div
        class="flex items-center justify-between rounded border-l-2 bg-slate-950/80 px-3 py-2 {reg.color}"
      >
        <span class="text-slate-400">{reg.label}</span>
        <span class="text-[11px] font-semibold">{reg.val}</span>
      </div>
    {/each}
  </div>
</div>
