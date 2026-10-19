<script lang="ts">
	let values = $state([1, 2, 3]);
	let inputStr = $state('1, 2, 3');
	let stepIdx = $state(0);
	let isPlaying = $state(false);
	let speed = $state(1500);
	let algoMode = $state<'while' | 'tail'>('while');

	const addresses = $derived(values.map((_, i) => '0x' + (100 + i * 16).toString(16).toUpperCase()));

	interface Step {
		lineWhile: number;
		lineTail: number;
		xs: number | null;
		acc: number | null;
		node: number | null;
		next: number | null;
		heap: (number | null)[];
		severed: { from: number; to: number | null } | null;
		title: string;
		desc: string;
	}

	const steps = $derived.by(() => {
		const n = values.length;
		const list: Step[] = [];
		let heapPointers: (number | null)[] = values.map((_, i) => (i < n - 1 ? i + 1 : null));
		let xs: number | null = 0;
		let acc: number | null = null;

		list.push({
			lineWhile: 1, lineTail: 1,
			xs: 0, acc: null, node: null, next: null,
			heap: [...heapPointers], severed: null,
			title: 'Initial Call: reverse_acc(xs, None)',
			desc: 'List head starts at ' + addresses[0] + '. Accumulator is initialized to None (null / 0x0).'
		});

		for (let i = 0; i < n; i++) {
			const currNode = i;
			const nextTarget = heapPointers[currNode];

			list.push({
				lineWhile: 3, lineTail: 3,
				xs: currNode, acc, node: currNode, next: null,
				heap: [...heapPointers], severed: null,
				title: 'Match Node: Cons(' + values[currNode] + ', ...) @ ' + addresses[currNode],
				desc: 'Ownership of heap block ' + addresses[currNode] + ' acquired. Corresponds to Koka reuse credit (◇₂).'
			});

			const heapAfterTake = [...heapPointers];
			heapAfterTake[currNode] = null;
			list.push({
				lineWhile: 4, lineTail: 4,
				xs: currNode, acc, node: currNode, next: nextTarget,
				heap: heapAfterTake,
				severed: { from: currNode, to: nextTarget },
				title: 'take(): Sever forward pointer',
				desc: 'node.next.take() sets ' + addresses[currNode] + '->next to null and moves rest of list into local variable next.'
			});
			heapPointers = heapAfterTake;

			const heapAfterRewire = [...heapPointers];
			heapAfterRewire[currNode] = acc;
			list.push({
				lineWhile: 5, lineTail: 5,
				xs: currNode, acc, node: currNode, next: nextTarget,
				heap: heapAfterRewire, severed: null,
				title: 'node.next = acc: IN-PLACE POINTER FLIP',
				desc: 'Heap cell ' + addresses[currNode] + ' is mutated in-place to point backwards to ' + (acc !== null ? addresses[acc] : 'null') + '. 0 allocations!'
			});
			heapPointers = heapAfterRewire;

			acc = currNode;
			xs = nextTarget;
			list.push({
				lineWhile: 6, lineTail: 6,
				xs, acc, node: null, next: null,
				heap: [...heapPointers], severed: null,
				title: 'Advance: reverse_acc(next, Some(node))',
				desc: 'In-place argument swap. Stack depth stays O(1) (TCO). acc is now ' + addresses[acc] + '.'
			});
		}

		list.push({
			lineWhile: 8, lineTail: 8,
			xs: null, acc, node: null, next: null,
			heap: [...heapPointers], severed: null,
			title: 'Base Case: match None => acc',
			desc: 'xs is None (null). The accumulated reversed list starting at ' + (acc !== null ? addresses[acc] : 'null') + ' is returned. Total allocations: 0.'
		});

		return list;
	});

	const current = $derived(steps[stepIdx] || steps[0]);

	$effect(() => {
		if (!isPlaying) return;
		const timer = setTimeout(() => {
			if (stepIdx < steps.length - 1) {
				stepIdx += 1;
			} else {
				isPlaying = false;
			}
		}, speed);
		return () => clearTimeout(timer);
	});

	function handleUpdateList() {
		const parsed = inputStr.split(',').map(s => parseInt(s.trim(), 10)).filter(n => !isNaN(n));
		if (parsed.length >= 2 && parsed.length <= 6) {
			values = parsed;
			stepIdx = 0;
			isPlaying = false;
		}
	}

	const whileCode = [
		{ num: 1, text: "pub fn reverse(mut self) -> Self {" },
		{ num: 2, text: "    let mut acc = None;" },
		{ num: 3, text: "    let mut xs = self.head.take();" },
		{ num: 4, text: "    while let Some(mut node) = xs {" },
		{ num: 5, text: "        let next = node.next.take();" },
		{ num: 6, text: "        node.next = acc;" },
		{ num: 7, text: "        acc = Some(node);" },
		{ num: 8, text: "        xs = next;" },
		{ num: 9, text: "    }" },
		{ num: 10, text: "    List { head: acc }" },
		{ num: 11, text: "}" },
	];

	const tailCode = [
		{ num: 1, text: "fn reverse_acc<T>(xs: Link<T>, acc: Link<T>) -> Link<T> {" },
		{ num: 2, text: "    match xs {" },
		{ num: 3, text: "        Some(mut node) => {" },
		{ num: 4, text: "            let next = node.next.take();" },
		{ num: 5, text: "            node.next = acc;" },
		{ num: 6, text: "            reverse_acc(next, Some(node))" },
		{ num: 7, text: "        }" },
		{ num: 8, text: "        None => acc," },
		{ num: 9, text: "    }" },
		{ num: 10, text: "}" },
	];

	const codeLines = $derived(algoMode === 'while' ? whileCode : tailCode);
	const activeLine = $derived(algoMode === 'while' ? current.lineWhile : current.lineTail);

	const nodeW = 140;
	const nodeH = 85;
	const gap = 80;
	const startX = 40;
	const heapY = 60;
</script>

<div class="max-w-6xl mx-auto px-6 space-y-6">
	<div class="flex justify-between items-center border-b border-slate-800 pb-4">
		<div>
			<h1 class="text-2xl font-bold tracking-tight text-white flex items-center gap-3">
				No-RC List Reversal (Box&lt;Node&gt;)
				<span class="text-xs bg-emerald-500/20 text-emerald-300 font-mono px-2 py-0.5 rounded border border-emerald-500/30">
					Zero Allocation O(1) Stack
				</span>
			</h1>
			<p class="text-sm text-slate-400 mt-1">
				Unique ownership enables in-place mutation of existing heap cells.
			</p>
		</div>

		<div class="flex items-center gap-3">
			<div class="flex items-center gap-1 bg-slate-900 border border-slate-800 p-1 rounded-lg">
				<button
					class="text-xs px-2.5 py-1 rounded font-mono transition-colors {algoMode === 'while' ? 'bg-emerald-600 text-white font-semibold' : 'text-slate-400 hover:text-slate-200'}"
					onclick={() => { algoMode = 'while'; stepIdx = 0; isPlaying = false; }}
				>
					while-loop
				</button>
				<button
					class="text-xs px-2.5 py-1 rounded font-mono transition-colors {algoMode === 'tail' ? 'bg-emerald-600 text-white font-semibold' : 'text-slate-400 hover:text-slate-200'}"
					onclick={() => { algoMode = 'tail'; stepIdx = 0; isPlaying = false; }}
				>
					tail-rec (FIP)
				</button>
			</div>

			<div class="flex items-center gap-2">
				<input
					class="bg-slate-900 border border-slate-700 text-xs px-2 py-1.5 rounded font-mono text-slate-200 w-32"
					bind:value={inputStr}
				/>
				<button
					class="bg-slate-800 hover:bg-slate-700 text-xs px-3 py-1.5 rounded text-slate-200 border border-slate-700"
					onclick={handleUpdateList}
				>
					Set List
				</button>
			</div>
		</div>
	</div>

	<!-- Narrative Box -->
	<div class="bg-slate-900/90 border border-slate-800 rounded-xl p-4 shadow-lg">
		<div class="flex justify-between items-center mb-1">
			<div class="text-xs font-semibold tracking-wider uppercase text-emerald-400 font-mono">
				Step {stepIdx + 1} of {steps.length}: {current.title}
			</div>
			<div class="text-xs text-slate-500 font-mono">Stack Depth: 1 (TCO constant)</div>
		</div>
		<p class="text-sm text-slate-300">{current.desc}</p>
	</div>

	<!-- Code vs Registers -->
	<div class="grid grid-cols-1 md:grid-cols-12 gap-6">
		<div class="md:col-span-7 bg-slate-900 border border-slate-800 rounded-xl p-4 font-mono text-xs">
			<div class="text-slate-400 text-[11px] mb-3 uppercase tracking-wider font-semibold border-b border-slate-800 pb-1 flex justify-between">
				<span>Active Execution Frame</span>
				<span class="text-emerald-400">{algoMode === 'while' ? 'Iterative while let' : 'Tail-Recursive inlined'}</span>
			</div>
			<div class="space-y-0.5">
				{#each codeLines as line}
					{@const isActive = line.num === activeLine}
					<div class="flex items-center px-2 py-0.5 rounded transition-colors {isActive ? 'bg-emerald-500/20 text-emerald-200 font-bold border-l-2 border-emerald-400' : 'text-slate-400'}">
						<span class="w-6 text-slate-600 select-none text-[10px] shrink-0">{line.num}</span>
						<span class="whitespace-pre font-mono">{line.text}</span>
					</div>
				{/each}
			</div>
		</div>

		<div class="md:col-span-5 bg-slate-900 border border-slate-800 rounded-xl p-4 font-mono text-xs">
			<div class="text-slate-400 text-[11px] mb-3 uppercase tracking-wider font-semibold border-b border-slate-800 pb-1">
				CPU Registers / Stack Pointers
			</div>
			<div class="space-y-2">
				<div class="flex justify-between items-center bg-slate-950/80 px-3 py-2 rounded border-l-2 border-sky-500 text-sky-400">
					<span class="text-slate-400">xs (input head)</span>
					<span class="font-semibold">{current.xs !== null ? addresses[current.xs] : 'null (None)'}</span>
				</div>
				<div class="flex justify-between items-center bg-slate-950/80 px-3 py-2 rounded border-l-2 border-emerald-500 text-emerald-400">
					<span class="text-slate-400">acc (accumulator)</span>
					<span class="font-semibold">{current.acc !== null ? addresses[current.acc] : 'null (None)'}</span>
				</div>
				<div class="flex justify-between items-center bg-slate-950/80 px-3 py-2 rounded border-l-2 border-amber-500 text-amber-400">
					<span class="text-slate-400">node (owned box)</span>
					<span class="font-semibold">{current.node !== null ? addresses[current.node] : '—'}</span>
				</div>
				<div class="flex justify-between items-center bg-slate-950/80 px-3 py-2 rounded border-l-2 border-purple-500 text-purple-400">
					<span class="text-slate-400">next (rest of list)</span>
					<span class="font-semibold">{current.next !== null ? addresses[current.next] : (current.node !== null ? 'null (0x0)' : '—')}</span>
				</div>
			</div>
		</div>
	</div>

	<!-- Heap Canvas -->
	<div class="bg-slate-900 border border-slate-800 rounded-xl p-5">
		<div class="text-slate-400 text-xs font-mono mb-2 uppercase tracking-wider font-semibold flex justify-between">
			<span>Physical Heap Memory (Nodes Never Move)</span>
			<span class="text-slate-500">64-bit Pointer | In-Place Overwrite</span>
		</div>

		<div class="overflow-x-auto py-4">
			<svg width={Math.max(760, values.length * (nodeW + gap) + 120)} height="240" class="select-none">
				<defs>
					<marker id="arrow-forward" markerWidth="8" markerHeight="8" refX="6" refY="4" orient="auto">
						<path d="M0,1 L7,4 L0,7 Z" fill="#38bdf8" />
					</marker>
					<marker id="arrow-backward" markerWidth="8" markerHeight="8" refX="6" refY="4" orient="auto">
						<path d="M0,1 L7,4 L0,7 Z" fill="#10b981" />
					</marker>
				</defs>

				{#each current.heap as targetIdx, srcIdx}
					{@const x1 = startX + srcIdx * (nodeW + gap)}
					{#if targetIdx === null}
						<g>
							<line x1={x1 + nodeW} y1={heapY + 42} x2={x1 + nodeW + 30} y2={heapY + 42} stroke="#64748b" stroke-width="2" />
							<text x={x1 + nodeW + 36} y={heapY + 46} fill="#64748b" font-size="10" font-family="monospace">null</text>
						</g>
					{:else if targetIdx > srcIdx}
						{@const x2 = startX + targetIdx * (nodeW + gap)}
						<line x1={x1 + nodeW} y1={heapY + 42} x2={x2} y2={heapY + 42} stroke="#38bdf8" stroke-width="2.5" marker-end="url(#arrow-forward)" />
					{:else}
						{@const x2 = startX + targetIdx * (nodeW + gap)}
						{@const startPtX = x1 + nodeW / 2}
						{@const endPtX = x2 + nodeW / 2}
						{@const arcY = heapY + nodeH + 45}
						{@const d = `M ${startPtX} ${heapY + nodeH} Q ${(startPtX + endPtX) / 2} ${arcY + 30} ${endPtX} ${heapY + nodeH}`}
						<path {d} fill="none" stroke="#10b981" stroke-width="3" marker-end="url(#arrow-backward)" />
					{/if}
				{/each}

				{#if current.severed && current.severed.to !== null}
					<g>
						<line
							x1={startX + current.severed.from * (nodeW + gap) + nodeW}
							y1={heapY + 42}
							x2={startX + current.severed.to * (nodeW + gap)}
							y2={heapY + 42}
							stroke="#ef4444"
							stroke-width="2"
							stroke-dasharray="4 4"
						/>
						<text
							x={startX + current.severed.from * (nodeW + gap) + nodeW + 20}
							y={heapY + 30}
							fill="#ef4444"
							font-size="10"
							font-family="monospace"
							font-weight="bold"
						>
							✂ take()
						</text>
					</g>
				{/if}

				{#each values as val, idx}
					{@const x = startX + idx * (nodeW + gap)}
					{@const isCurrNode = current.node === idx}
					{@const isAcc = current.acc === idx}
					{@const isXs = current.xs === idx}
					{@const borderStroke = isCurrNode ? '#f59e0b' : (isAcc ? '#10b981' : (isXs ? '#38bdf8' : '#334155'))}

					<g>
						<rect
							{x} y={heapY} width={nodeW} height={nodeH} rx="8"
							fill="#020617" stroke={borderStroke} stroke-width={isCurrNode || isAcc ? 2.5 : 1.5}
						/>
						<rect {x} y={heapY} width={nodeW} height="24" rx="6" fill="#0f172a" />
						<text x={x + 10} y={heapY + 16} fill="#94a3b8" font-size="11" font-family="monospace" font-weight="bold">
							{addresses[idx]}
						</text>
						<text x={x + 12} y={heapY + 54} fill="#e2e8f0" font-size="13" font-family="monospace">
							val: {val}
						</text>
						<text x={x + 12} y={heapY + 74} fill="#64748b" font-size="10" font-family="monospace">
							next: {current.heap[idx] !== null ? addresses[current.heap[idx]!] : 'null'}
						</text>
					</g>
				{/each}
			</svg>
		</div>
	</div>

	<!-- Controls -->
	<div class="flex justify-between items-center bg-slate-900 border border-slate-800 rounded-xl p-4">
		<div class="flex items-center gap-2">
			<button
				class="bg-slate-800 hover:bg-slate-700 px-3 py-1.5 rounded text-xs text-slate-200 border border-slate-700 disabled:opacity-40"
				disabled={stepIdx === 0}
				onclick={() => { stepIdx = 0; }}
			>
				⏮ Reset
			</button>
			<button
				class="bg-slate-800 hover:bg-slate-700 px-3 py-1.5 rounded text-xs text-slate-200 border border-slate-700 disabled:opacity-40"
				disabled={stepIdx === 0}
				onclick={() => { stepIdx = Math.max(0, stepIdx - 1); }}
			>
				◀ Prev
			</button>
			<button
				class="bg-emerald-600 hover:bg-emerald-500 px-4 py-1.5 rounded text-xs text-white font-medium"
				onclick={() => { isPlaying = !isPlaying; }}
			>
				{isPlaying ? '⏸ Pause' : '▶ Play'}
			</button>
			<button
				class="bg-slate-800 hover:bg-slate-700 px-3 py-1.5 rounded text-xs text-slate-200 border border-slate-700 disabled:opacity-40"
				disabled={stepIdx === steps.length - 1}
				onclick={() => { stepIdx = Math.min(steps.length - 1, stepIdx + 1); }}
			>
				Next ▶
			</button>
		</div>

		<div class="flex items-center gap-4 text-xs font-mono text-slate-400">
			<span>Speed: {(speed / 1000).toFixed(1)}s</span>
			<input type="range" min="400" max="3000" step="200" bind:value={speed} class="w-28" />
		</div>
	</div>
</div>
