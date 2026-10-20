<script lang="ts">
  import { matrixCells, type MatrixCell } from '#lib/models/matrix/data';
  import MatrixGrid from '#lib/components/matrix/MatrixGrid.svelte';
  import CellInspector from '#lib/components/matrix/CellInspector.svelte';
  import TheoryCards from '#lib/components/matrix/TheoryCards.svelte';

  let selectedCell: MatrixCell = $state(matrixCells[0][0]);

  function handleSelect(cell: MatrixCell) {
    selectedCell = cell;
  }
</script>

<svelte:head>
  <title>4×4 Ownership & Borrowing Reversal Matrix</title>
</svelte:head>

<div class="mx-auto max-w-6xl space-y-8 px-6 py-8">
  <header class="space-y-3 text-center">
    <div
      class="inline-flex items-center gap-2 rounded-full border border-sky-500/30 bg-sky-500/10 px-3 py-1 text-xs text-sky-400"
    >
      <span class="h-1.5 w-1.5 rounded-full bg-sky-400"></span>
      Marshall, Vollmer & Orchard (ESOP 2022) Alignment
    </div>
    <h1 class="text-3xl font-extrabold tracking-tight text-white md:text-4xl">
      The 4×4 Ownership & Borrowing Reversal Matrix
    </h1>
    <p class="mx-auto max-w-3xl text-sm leading-relaxed text-slate-400">
      A complete, theoretically rigorous map of linked-list reversal across Rust's ownership
      spectrum and Granule's Linear-Cartesian-Unique (LCU) calculus. Click any cell to inspect its
      tail-recursive mechanics, algebraic modal type, and memory traffic.
    </p>

    <!-- Legend bar -->
    <div class="flex flex-wrap items-center justify-center gap-4 pt-2 font-mono text-xs">
      <div class="flex items-center gap-1.5">
        <span class="h-2.5 w-2.5 rounded-full bg-emerald-500"></span>
        <span class="text-slate-300">Owned Unique (*1)</span>
      </div>
      <div class="flex items-center gap-1.5">
        <span class="h-2.5 w-2.5 rounded-full bg-amber-500"></span>
        <span class="text-slate-300">Borrowed Unique (&mut *1)</span>
      </div>
      <div class="flex items-center gap-1.5">
        <span class="h-2.5 w-2.5 rounded-full bg-purple-500"></span>
        <span class="text-slate-300">Owned Shared (Rc / !)</span>
      </div>
      <div class="flex items-center gap-1.5">
        <span class="h-2.5 w-2.5 rounded-full bg-sky-500"></span>
        <span class="text-slate-300">Borrowed Shared (*n, n &lt; 1)</span>
      </div>
      <div class="flex items-center gap-1.5">
        <span class="h-2.5 w-2.5 rounded-full bg-rose-500"></span>
        <span class="text-slate-300">Statically Forbidden</span>
      </div>
    </div>
  </header>

  <!-- Interactive 4x4 Table -->
  <MatrixGrid {selectedCell} onSelect={handleSelect} />

  <!-- Selected Cell Inspector -->
  <CellInspector cell={selectedCell} />

  <!-- Theory section -->
  <TheoryCards />
</div>
