<script lang="ts">
</script>

<div class="mx-auto max-w-5xl space-y-8 px-6 py-12">
  <div class="space-y-3 text-center">
    <h1 class="text-3xl font-bold tracking-tight text-white">
      Fully In-Place (FIP) Memory Visualizers
    </h1>
    <p class="mx-auto max-w-2xl text-sm text-slate-400">
      Interactive step-by-step memory visualizers illustrating linked-list reversal across all 4
      Granule uniqueness-typed modes in Rust.
    </p>
  </div>

  <!-- 4x4 Matrix Banner Card -->
  <a
    href="/ownership_and_borrowing_four_by_four_matrix"
    class="group block rounded-xl border border-sky-500/40 bg-gradient-to-r from-sky-950/40 via-slate-900 to-purple-950/40 p-6 shadow-xl transition-all hover:border-sky-400 hover:shadow-sky-500/10"
  >
    <div class="flex flex-wrap items-center justify-between gap-2">
      <span
        class="rounded border border-sky-500/30 bg-sky-500/20 px-2.5 py-0.5 font-mono text-xs font-semibold text-sky-300"
      >
        Theoretical Synthesis
      </span>
      <span class="font-mono text-xs text-slate-400">ESOP 2022 Entente Cordiale</span>
    </div>
    <h2 class="mt-3 text-xl font-bold text-white transition-colors group-hover:text-sky-300">
      The 4×4 Ownership & Borrowing Reversal Matrix
    </h2>
    <p class="mt-1 text-xs leading-relaxed text-slate-300">
      Comprehensive interactive taxonomy mapping BoxList, &mut BoxList, RcList, and &BoxList across
      all 16 input/output permutations with LCU modal types, memory traffic analysis, and in-place
      guarantees.
    </p>
    <div
      class="mt-4 flex items-center gap-1 font-mono text-xs font-semibold text-sky-400 transition-transform group-hover:translate-x-1"
    >
      Explore 4×4 Matrix &rarr;
    </div>
  </a>

  <div class="grid grid-cols-1 gap-6 md:grid-cols-2">
    <!-- Mode 1: Box -> Box -->
    <a
      href="/box-to-box"
      class="group space-y-4 rounded-xl border border-slate-800 bg-slate-900 p-6 shadow-lg transition-all hover:border-emerald-500/50 hover:shadow-emerald-500/10"
    >
      <div class="flex items-start justify-between">
        <div
          class="flex h-10 w-10 items-center justify-center rounded-lg border border-emerald-500/20 bg-emerald-500/10 font-mono text-sm font-bold text-emerald-400"
        >
          1
        </div>
        <span
          class="rounded border border-emerald-500/30 bg-emerald-500/20 px-2 py-0.5 font-mono text-xs text-emerald-300"
        >
          List a &lcub;Unique&rcub; &rarr; List a &lcub;Unique&rcub;
        </span>
      </div>
      <div>
        <h2 class="text-lg font-semibold text-white transition-colors group-hover:text-emerald-400">
          Box &rarr; Box (Zero Allocations)
        </h2>
        <p class="mt-1 text-xs leading-relaxed text-slate-400">
          Pure linear uniqueness. Pointer flipping via <code class="text-emerald-300">take()</code> in-place
          with zero memory allocations and $O(1)$ stack.
        </p>
      </div>
      <div
        class="flex items-center gap-1 font-mono text-xs text-emerald-400 transition-transform group-hover:translate-x-1"
      >
        Launch Box &rarr; Box &rarr;
      </div>
    </a>

    <!-- Mode 2: Rc -> Rc -->
    <a
      href="/rc-to-rc"
      class="group space-y-4 rounded-xl border border-slate-800 bg-slate-900 p-6 shadow-lg transition-all hover:border-purple-500/50 hover:shadow-purple-500/10"
    >
      <div class="flex items-start justify-between">
        <div
          class="flex h-10 w-10 items-center justify-center rounded-lg border border-purple-500/20 bg-purple-500/10 font-mono text-sm font-bold text-purple-400"
        >
          2
        </div>
        <span
          class="rounded border border-purple-500/30 bg-purple-500/20 px-2 py-0.5 font-mono text-xs text-purple-300"
        >
          List a &rarr; List a
        </span>
      </div>
      <div>
        <h2 class="text-lg font-semibold text-white transition-colors group-hover:text-purple-400">
          Rc &rarr; Rc (Perceus COW)
        </h2>
        <p class="mt-1 text-xs leading-relaxed text-slate-400">
          Dynamic uniqueness detection via <code class="text-purple-300">Rc::get_mut</code> (<code
            class="text-purple-300">is-unique</code
          >). Reuses in-place when $RC = 1$; falls back to Copy-On-Write when $RC &gt; 1$.
        </p>
      </div>
      <div
        class="flex items-center gap-1 font-mono text-xs text-purple-400 transition-transform group-hover:translate-x-1"
      >
        Launch Rc &rarr; Rc &rarr;
      </div>
    </a>

    <!-- Mode 3: Rc -> Box -->
    <a
      href="/rc-to-box"
      class="group space-y-4 rounded-xl border border-slate-800 bg-slate-900 p-6 shadow-lg transition-all hover:border-sky-500/50 hover:shadow-sky-500/10"
    >
      <div class="flex items-start justify-between">
        <div
          class="flex h-10 w-10 items-center justify-center rounded-lg border border-sky-500/20 bg-sky-500/10 font-mono text-sm font-bold text-sky-400"
        >
          3
        </div>
        <span
          class="rounded border border-sky-500/30 bg-sky-500/20 px-2 py-0.5 font-mono text-xs text-sky-300"
        >
          List a &rarr; List a &lcub;Unique&rcub;
        </span>
      </div>
      <div>
        <h2 class="text-lg font-semibold text-white transition-colors group-hover:text-sky-400">
          Rc &rarr; Box (try_unwrap & 0 Atomic Updates)
        </h2>
        <p class="mt-1 text-xs leading-relaxed text-slate-400">
          Tests <code class="text-sky-300">Rc::try_unwrap(rc_node)</code> first: moves value with zero
          atomic refcount increments when unique, or falls back to cloning when shared.
        </p>
      </div>
      <div
        class="flex items-center gap-1 font-mono text-xs text-sky-400 transition-transform group-hover:translate-x-1"
      >
        Launch Rc &rarr; Box &rarr;
      </div>
    </a>

    <!-- Mode 4: Box -> Rc -->
    <a
      href="/box-to-rc"
      class="group space-y-4 rounded-xl border border-slate-800 bg-slate-900 p-6 shadow-lg transition-all hover:border-amber-500/50 hover:shadow-amber-500/10"
    >
      <div class="flex items-start justify-between">
        <div
          class="flex h-10 w-10 items-center justify-center rounded-lg border border-amber-500/20 bg-amber-500/10 font-mono text-sm font-bold text-amber-400"
        >
          4
        </div>
        <span
          class="rounded border border-amber-500/30 bg-amber-500/20 px-2 py-0.5 font-mono text-xs text-amber-300"
        >
          List a &lcub;Unique&rcub; &rarr; List a
        </span>
      </div>
      <div>
        <h2 class="text-lg font-semibold text-white transition-colors group-hover:text-amber-400">
          Box &rarr; Rc (Wrapping into RcBox)
        </h2>
        <p class="mt-1 text-xs leading-relaxed text-slate-400">
          Transforms linear Box nodes into reference-counted Rc cells with strong=1, weak=0 control
          blocks for shared data structures.
        </p>
      </div>
      <div
        class="flex items-center gap-1 font-mono text-xs text-amber-400 transition-transform group-hover:translate-x-1"
      >
        Launch Box &rarr; Rc &rarr;
      </div>
    </a>
  </div>
</div>
