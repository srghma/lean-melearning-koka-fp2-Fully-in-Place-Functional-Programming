<script lang="ts">
  import type { RcPresetConfig } from '#lib/types/rc';

  let {
    presets,
    selectedId = $bindable(),
    onSelect
  }: {
    presets: RcPresetConfig[];
    selectedId: string;
    onSelect: (preset: RcPresetConfig) => void;
  } = $props();
</script>

<div class="flex items-center gap-2 overflow-x-auto pb-1">
  {#each presets as p (p.id)}
    <button
      class="rounded-lg border px-3 py-1.5 font-mono text-xs whitespace-nowrap transition-colors {selectedId ===
      p.id
        ? 'border-purple-500 bg-purple-600 font-semibold text-white shadow-sm'
        : 'border-slate-800 bg-slate-900 text-slate-400 hover:border-slate-700 hover:text-slate-200'}"
      onclick={() => {
        selectedId = p.id;
        onSelect(p);
      }}
    >
      {p.name}
    </button>
  {/each}
</div>
