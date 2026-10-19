<script lang="ts">
	import './layout.css';
	import { page } from '$app/state';

	let { children } = $props();
</script>

<div class="min-h-screen bg-slate-950 text-slate-100 font-sans">
	<header class="border-b border-slate-800 bg-slate-900/60 backdrop-blur sticky top-0 z-50">
		<div class="max-w-6xl mx-auto px-6 h-14 flex items-center justify-between">
			<a href="/" class="flex items-center gap-3 hover:opacity-90 transition-opacity">
				<span class="font-bold tracking-tight text-white flex items-center gap-2">
					<span class="w-2.5 h-2.5 rounded-full bg-emerald-400 animate-pulse"></span>
					FIP In-Place Reversal Visualizers
				</span>
				<span class="text-xs bg-slate-800 text-slate-400 px-2 py-0.5 rounded font-mono border border-slate-700">
					Rust &amp; Koka
				</span>
			</a>
			<nav class="flex items-center gap-2">
				<a
					href="/no-rc"
					class="text-xs font-mono px-3 py-1.5 rounded transition-colors {page.url.pathname === '/no-rc' ? 'bg-emerald-600 text-white font-semibold shadow-sm' : 'text-slate-400 hover:text-slate-200 hover:bg-slate-800'}"
				>
					No-RC (Box&lt;Node&gt;)
				</a>
				<a
					href="/rc"
					class="text-xs font-mono px-3 py-1.5 rounded transition-colors {page.url.pathname === '/rc' ? 'bg-purple-600 text-white font-semibold shadow-sm' : 'text-slate-400 hover:text-slate-200 hover:bg-slate-800'}"
				>
					RC (Rc&lt;Node&gt; &amp; Perceus COW)
				</a>
			</nav>
		</div>
	</header>

	<main class="py-6">
		{@render children()}
	</main>
</div>
