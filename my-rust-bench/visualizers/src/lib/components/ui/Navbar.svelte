<script lang="ts">
  import { page } from '$app/state';
</script>

<header class="sticky top-0 z-50 border-b border-slate-800 bg-slate-900/60 backdrop-blur">
  <div class="mx-auto flex h-14 max-w-6xl items-center justify-between px-6">
    <a href="/" class="flex items-center gap-3 no-underline transition-opacity hover:opacity-90">
      <span class="flex items-center gap-2 font-bold tracking-tight text-white">
        <span class="h-2.5 w-2.5 animate-pulse rounded-full bg-emerald-400"></span>
        FIP In-Place Reversal
      </span>
      <span
        class="rounded border border-slate-700 bg-slate-800 px-2 py-0.5 font-mono text-xs text-slate-400"
      >
        Rust &amp; Koka
      </span>
    </a>
    <nav class="flex items-center gap-2">
      <a
        href="/no-rc"
        class="rounded px-3 py-1.5 font-mono text-xs no-underline transition-colors {page.url
          .pathname === '/no-rc'
          ? 'bg-emerald-600 font-semibold text-white'
          : 'text-slate-400 hover:bg-slate-800 hover:text-slate-200'}"
      >
        No-RC (Box&lt;Node&gt;)
      </a>
      <a
        href="/rc"
        class="rounded px-3 py-1.5 font-mono text-xs no-underline transition-colors {page.url
          .pathname === '/rc'
          ? 'bg-purple-600 font-semibold text-white'
          : 'text-slate-400 hover:bg-slate-800 hover:text-slate-200'}"
      >
        RC (Rc&lt;Node&gt; &amp; Perceus COW)
      </a>
    </nav>
  </div>
</header>
