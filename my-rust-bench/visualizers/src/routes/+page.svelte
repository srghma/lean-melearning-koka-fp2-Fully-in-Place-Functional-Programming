<script lang="ts">
</script>

<div class="mx-auto max-w-4xl space-y-8 px-6 py-12">
  <div class="space-y-3 text-center">
    <h1 class="text-3xl font-bold tracking-tight text-white">
      Fully In-Place (FIP) Memory Visualizers
    </h1>
    <p class="mx-auto max-w-xl text-sm text-slate-400">
      Interactive step-by-step visualizations of in-place linked list reversal in Rust,
      demonstrating unique ownership reuse and Perceus Copy-on-Write reference counting.
    </p>
  </div>

  <div class="grid grid-cols-1 gap-6 md:grid-cols-2">
    <a
      href="/no-rc"
      class="group space-y-4 rounded-xl border border-slate-800 bg-slate-900 p-6 shadow-lg transition-all hover:border-emerald-500/50 hover:shadow-emerald-500/10"
    >
      <div class="flex items-start justify-between">
        <div
          class="flex h-10 w-10 items-center justify-center rounded-lg border border-emerald-500/20 bg-emerald-500/10 font-mono text-lg text-emerald-400"
        >
          Box
        </div>
        <span
          class="rounded border border-emerald-500/30 bg-emerald-500/20 px-2 py-0.5 font-mono text-xs text-emerald-300"
        >
          0 Allocations
        </span>
      </div>
      <div>
        <h2 class="text-lg font-semibold text-white transition-colors group-hover:text-emerald-400">
          No-RC List (Box&lt;Node&gt;)
        </h2>
        <p class="mt-1 text-xs leading-relaxed text-slate-400">
          Single unique ownership. Demonstrates in-place pointer flipping via <code
            class="text-emerald-300">take()</code
          >, showing that tail recursion and while loops compile to identical O(1) stack jumps.
        </p>
      </div>
      <div
        class="flex items-center gap-1 font-mono text-xs text-emerald-400 transition-transform group-hover:translate-x-1"
      >
        Launch visualizer &rarr;
      </div>
    </a>

    <a
      href="/rc"
      class="group space-y-4 rounded-xl border border-slate-800 bg-slate-900 p-6 shadow-lg transition-all hover:border-purple-500/50 hover:shadow-purple-500/10"
    >
      <div class="flex items-start justify-between">
        <div
          class="flex h-10 w-10 items-center justify-center rounded-lg border border-purple-500/20 bg-purple-500/10 font-mono text-lg text-purple-400"
        >
          Rc
        </div>
        <span
          class="rounded border border-purple-500/30 bg-purple-500/20 px-2 py-0.5 font-mono text-xs text-purple-300"
        >
          Perceus COW
        </span>
      </div>
      <div>
        <h2 class="text-lg font-semibold text-white transition-colors group-hover:text-purple-400">
          RC List (Rc&lt;Node&gt;)
        </h2>
        <p class="mt-1 text-xs leading-relaxed text-slate-400">
          Shared reference counting with <code class="text-purple-300">Rc::get_mut</code> (Koka's
          <code class="text-purple-300">is-unique</code>). Mutates in-place when RC=1 and falls back
          to Copy-on-Write when RC&gt;1.
        </p>
      </div>
      <div
        class="flex items-center gap-1 font-mono text-xs text-purple-400 transition-transform group-hover:translate-x-1"
      >
        Launch visualizer &rarr;
      </div>
    </a>
  </div>
</div>
