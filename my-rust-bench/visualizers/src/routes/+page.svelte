<script lang="ts">
</script>

<div class="max-w-4xl mx-auto px-6 py-12 space-y-8">
	<div class="text-center space-y-3">
		<h1 class="text-3xl font-bold tracking-tight text-white">
			Fully In-Place (FIP) Memory Visualizers
		</h1>
		<p class="text-slate-400 text-sm max-w-xl mx-auto">
			Interactive step-by-step visualizations of in-place linked list reversal in Rust,
			demonstrating unique ownership reuse and Perceus Copy-on-Write reference counting.
		</p>
	</div>

	<div class="grid grid-cols-1 md:grid-cols-2 gap-6">
		<a
			href="/no-rc"
			class="group bg-slate-900 border border-slate-800 hover:border-emerald-500/50 rounded-xl p-6 transition-all shadow-lg hover:shadow-emerald-500/10 space-y-4"
		>
			<div class="flex justify-between items-start">
				<div class="w-10 h-10 rounded-lg bg-emerald-500/10 border border-emerald-500/20 flex items-center justify-center text-emerald-400 text-lg font-mono">
					Box
				</div>
				<span class="text-xs font-mono bg-emerald-500/20 text-emerald-300 px-2 py-0.5 rounded border border-emerald-500/30">
					0 Allocations
				</span>
			</div>
			<div>
				<h2 class="text-lg font-semibold text-white group-hover:text-emerald-400 transition-colors">
					No-RC List (Box&lt;Node&gt;)
				</h2>
				<p class="text-slate-400 text-xs mt-1 leading-relaxed">
					Single unique ownership. Demonstrates in-place pointer flipping via <code class="text-emerald-300">take()</code>,
					showing that tail recursion and while loops compile to identical O(1) stack jumps.
				</p>
			</div>
			<div class="text-xs text-emerald-400 font-mono flex items-center gap-1 group-hover:translate-x-1 transition-transform">
				Launch visualizer &rarr;
			</div>
		</a>

		<a
			href="/rc"
			class="group bg-slate-900 border border-slate-800 hover:border-purple-500/50 rounded-xl p-6 transition-all shadow-lg hover:shadow-purple-500/10 space-y-4"
		>
			<div class="flex justify-between items-start">
				<div class="w-10 h-10 rounded-lg bg-purple-500/10 border border-purple-500/20 flex items-center justify-center text-purple-400 text-lg font-mono">
					Rc
				</div>
				<span class="text-xs font-mono bg-purple-500/20 text-purple-300 px-2 py-0.5 rounded border border-purple-500/30">
					Perceus COW
				</span>
			</div>
			<div>
				<h2 class="text-lg font-semibold text-white group-hover:text-purple-400 transition-colors">
					RC List (Rc&lt;Node&gt;)
				</h2>
				<p class="text-slate-400 text-xs mt-1 leading-relaxed">
					Shared reference counting with <code class="text-purple-300">Rc::get_mut</code> (Koka's <code class="text-purple-300">is-unique</code>).
					Mutates in-place when RC=1 and falls back to Copy-on-Write when RC&gt;1.
				</p>
			</div>
			<div class="text-xs text-purple-400 font-mono flex items-center gap-1 group-hover:translate-x-1 transition-transform">
				Launch visualizer &rarr;
			</div>
		</a>
	</div>
</div>
