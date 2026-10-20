<script lang="ts">
  import type { MatrixCell } from '#lib/models/matrix/data';

  let { cell }: { cell: MatrixCell } = $props();
  let copied = $state(false);

  async function copyCode() {
    try {
      await navigator.clipboard.writeText(cell.code);
      copied = true;
      setTimeout(() => (copied = false), 2000);
    } catch {
      // fallback
    }
  }
</script>

<div
  class="space-y-4 rounded-xl border border-slate-800 bg-slate-900/90 p-6 shadow-xl backdrop-blur"
>
  <div class="flex flex-wrap items-center justify-between gap-3 border-b border-slate-800 pb-4">
    <div>
      <div class="flex items-center gap-2">
        <span class="h-2 w-2 rounded-full bg-sky-400"></span>
        <h2 class="text-lg font-bold text-white">{cell.title}</h2>
      </div>
      <p class="mt-1 font-mono text-xs text-sky-400">{cell.rustSig}</p>
    </div>
    <span
      class="rounded border border-slate-700 bg-slate-800 px-2.5 py-1 font-mono text-xs text-slate-300"
    >
      Row {cell.row + 1}, Col {cell.col + 1}
    </span>
  </div>

  <div class="grid grid-cols-1 gap-4 md:grid-cols-2">
    <div class="space-y-1 rounded-lg border border-slate-800 bg-slate-950/60 p-3 font-mono text-xs">
      <span class="text-[10px] font-semibold tracking-wider text-slate-400 uppercase"
        >Heap Allocator Traffic</span
      >
      <div class="font-semibold text-emerald-400">{cell.alloc}</div>
    </div>
    <div class="space-y-1 rounded-lg border border-slate-800 bg-slate-950/60 p-3 font-mono text-xs">
      <span class="text-[10px] font-semibold tracking-wider text-slate-400 uppercase"
        >LCU Calculus / Graded Modal Type</span
      >
      <div class="font-semibold text-purple-400">{cell.granuleGraded}</div>
    </div>
  </div>

  <div
    class="rounded-lg border border-slate-800/80 bg-slate-950/40 p-3 text-xs leading-relaxed text-slate-300"
  >
    <strong class="font-semibold text-slate-100">Theoretical Foundation (ESOP 2022):</strong>
    <p class="mt-1">{cell.theoryDesc}</p>
  </div>

  <div class="relative">
    <div
      class="flex items-center justify-between rounded-t-lg border-x border-t border-slate-800 bg-slate-950 px-4 py-2 font-mono text-[11px] text-slate-400"
    >
      <span>Rust In-Place Implementation</span>
      <button
        onclick={copyCode}
        class="rounded border border-slate-700 bg-slate-800 px-2 py-0.5 text-[10px] text-slate-300 transition-colors hover:bg-slate-700"
      >
        {copied ? 'Copied!' : 'Copy Code'}
      </button>
    </div>
    <pre
      class="overflow-x-auto rounded-b-lg border border-slate-800 bg-slate-950/90 p-4 font-mono text-xs text-slate-200"><code
        >{cell.code}</code
      ></pre>
  </div>
</div>
