<script lang="ts">
	let algoMode = $state<'while' | 'tail'>('while');
	let stepIdx = $state(0);
	let isPlaying = $state(false);
	let speed = $state(1600);

	interface Arrow {
		from: string;
		to: string;
		type: 'forward' | 'shared-root' | 'severed' | 'backward' | 'cow-backward';
	}

	interface Step {
		lineWhile: number;
		lineTail: number;
		xs: string;
		acc: string;
		rc_node: string | null;
		getMut: string | null;
		nodeRCs: Record<string, number>;
		arrows: Arrow[];
		visibleNodes: string[];
		title: string;
		desc: string;
	}

	const steps: Step[] = [
		{
			lineWhile: 1, lineTail: 1,
			xs: "0x100", acc: "null", rc_node: null, getMut: null,
			nodeRCs: { "0x100": 1, "0x110": 1, "0x200": 2, "0x300": 1 },
			arrows: [
				{ from: "0x100", to: "0x200", type: "forward" },
				{ from: "0x110", to: "0x200", type: "shared-root" },
				{ from: "0x200", to: "0x300", type: "forward" },
				{ from: "0x300", to: "null", type: "forward" },
			],
			visibleNodes: ["0x100", "0x110", "0x200", "0x300"],
			title: "Initial State: Shared Tail (list1: 1->2->3, list2: 11->2->3)",
			desc: "list1 starts at 0x100. list2 starts at 0x110. Both converge on Node 2 (0x200), giving it RC = 2."
		},
		{
			lineWhile: 3, lineTail: 3,
			xs: "0x100", acc: "null", rc_node: "0x100", getMut: "Some(&mut node) [RC == 1] -> UNIQUE!",
			nodeRCs: { "0x100": 1, "0x110": 1, "0x200": 2, "0x300": 1 },
			arrows: [
				{ from: "0x100", to: "0x200", type: "forward" },
				{ from: "0x110", to: "0x200", type: "shared-root" },
				{ from: "0x200", to: "0x300", type: "forward" },
				{ from: "0x300", to: "null", type: "forward" },
			],
			visibleNodes: ["0x100", "0x110", "0x200", "0x300"],
			title: "Node 1 (0x100): Rc::get_mut checks RC == 1",
			desc: "Rc::get_mut(&mut rc_node) succeeds! Node 1 is uniquely owned by list1. Corresponds to Koka is-unique."
		},
		{
			lineWhile: 5, lineTail: 5,
			xs: "0x200", acc: "null", rc_node: "0x100", getMut: "Some(&mut node) [RC == 1]",
			nodeRCs: { "0x100": 1, "0x110": 1, "0x200": 2, "0x300": 1 },
			arrows: [
				{ from: "0x100", to: "0x200", type: "severed" },
				{ from: "0x110", to: "0x200", type: "shared-root" },
				{ from: "0x200", to: "0x300", type: "forward" },
				{ from: "0x300", to: "null", type: "forward" },
			],
			visibleNodes: ["0x100", "0x110", "0x200", "0x300"],
			title: "Node 1: xs = node.next.take()",
			desc: "Forward pointer from 0x100 is severed. 0x200 moved into xs. Node 1 next is temporarily null."
		},
		{
			lineWhile: 7, lineTail: 7,
			xs: "0x200", acc: "0x100", rc_node: "0x100", getMut: "Some(&mut node) [RC == 1]",
			nodeRCs: { "0x100": 1, "0x110": 1, "0x200": 2, "0x300": 1 },
			arrows: [
				{ from: "0x100", to: "null", type: "backward" },
				{ from: "0x110", to: "0x200", type: "shared-root" },
				{ from: "0x200", to: "0x300", type: "forward" },
				{ from: "0x300", to: "null", type: "forward" },
			],
			visibleNodes: ["0x100", "0x110", "0x200", "0x300"],
			title: "Node 1: node.next = acc (IN-PLACE REUSE)",
			desc: "Node 1 (0x100) next is set to acc (null). 0 allocations! Existing Rc heap cell at 0x100 is reused."
		},
		{
			lineWhile: 3, lineTail: 3,
			xs: "0x200", acc: "0x100", rc_node: "0x200", getMut: "None [RC == 2] -> SHARED (COW)!",
			nodeRCs: { "0x100": 1, "0x110": 1, "0x200": 2, "0x300": 1 },
			arrows: [
				{ from: "0x100", to: "null", type: "backward" },
				{ from: "0x110", to: "0x200", type: "shared-root" },
				{ from: "0x200", to: "0x300", type: "forward" },
				{ from: "0x300", to: "null", type: "forward" },
			],
			visibleNodes: ["0x100", "0x110", "0x200", "0x300"],
			title: "Node 2 (0x200): Rc::get_mut fails (RC = 2)",
			desc: "Rc::get_mut returns None because list2 also holds Node 2! In-place mutation would corrupt list2, so Rust branches to Copy-on-Write."
		},
		{
			lineWhile: 10, lineTail: 10,
			xs: "0x300", acc: "0x100", rc_node: "0x200", getMut: "None [RC == 2]",
			nodeRCs: { "0x100": 1, "0x110": 1, "0x200": 2, "0x300": 2 },
			arrows: [
				{ from: "0x100", to: "null", type: "backward" },
				{ from: "0x110", to: "0x200", type: "shared-root" },
				{ from: "0x200", to: "0x300", type: "forward" },
				{ from: "0x300", to: "null", type: "forward" },
			],
			visibleNodes: ["0x100", "0x110", "0x200", "0x300"],
			title: "Node 2: xs = rc_node.next.clone()",
			desc: "Cloning next advances xs to Node 3 (0x300) and increments Node 3's RC to 2."
		},
		{
			lineWhile: 12, lineTail: 14,
			xs: "0x300", acc: "0x220", rc_node: null, getMut: "None [COW Alloc]",
			nodeRCs: { "0x100": 1, "0x110": 1, "0x200": 1, "0x300": 2, "0x220": 1 },
			arrows: [
				{ from: "0x100", to: "null", type: "backward" },
				{ from: "0x110", to: "0x200", type: "shared-root" },
				{ from: "0x200", to: "0x300", type: "forward" },
				{ from: "0x300", to: "null", type: "forward" },
				{ from: "0x220", to: "0x100", type: "cow-backward" },
			],
			visibleNodes: ["0x100", "0x110", "0x200", "0x300", "0x220"],
			title: "Node 2: Allocate Fresh Node 2' (0x220) via COW",
			desc: "Rc::new allocates brand-new Node 2' (0x220) pointing to Node 1 (0x100). rc_node is dropped, lowering original Node 2 RC back to 1!"
		},
		{
			lineWhile: 3, lineTail: 3,
			xs: "0x300", acc: "0x220", rc_node: "0x300", getMut: "None [RC == 2] -> SHARED (COW)!",
			nodeRCs: { "0x100": 1, "0x110": 1, "0x200": 1, "0x300": 2, "0x220": 1 },
			arrows: [
				{ from: "0x100", to: "null", type: "backward" },
				{ from: "0x110", to: "0x200", type: "shared-root" },
				{ from: "0x200", to: "0x300", type: "forward" },
				{ from: "0x300", to: "null", type: "forward" },
				{ from: "0x220", to: "0x100", type: "cow-backward" },
			],
			visibleNodes: ["0x100", "0x110", "0x200", "0x300", "0x220"],
			title: "Node 3 (0x300): Rc::get_mut fails (RC = 2)",
			desc: "Node 3 is held by xs and original Node 2 (0x200). Rc::get_mut returns None -> Copy-on-Write triggers again."
		},
		{
			lineWhile: 12, lineTail: 14,
			xs: "null", acc: "0x320", rc_node: null, getMut: "None [COW Alloc]",
			nodeRCs: { "0x100": 1, "0x110": 1, "0x200": 1, "0x300": 1, "0x220": 1, "0x320": 1 },
			arrows: [
				{ from: "0x100", to: "null", type: "backward" },
				{ from: "0x110", to: "0x200", type: "shared-root" },
				{ from: "0x200", to: "0x300", type: "forward" },
				{ from: "0x300", to: "null", type: "forward" },
				{ from: "0x220", to: "0x100", type: "cow-backward" },
				{ from: "0x320", to: "0x220", type: "cow-backward" },
			],
			visibleNodes: ["0x100", "0x110", "0x200", "0x300", "0x220", "0x320"],
			title: "Node 3: Allocate Fresh Node 3' (0x320) via COW",
			desc: "Fresh Node 3' (0x320) points to Node 2' (0x220). rc_node dropped, original Node 3 RC falls back to 1."
		},
		{
			lineWhile: 18, lineTail: 18,
			xs: "null", acc: "0x320", rc_node: null, getMut: null,
			nodeRCs: { "0x100": 1, "0x110": 1, "0x200": 1, "0x300": 1, "0x220": 1, "0x320": 1 },
			arrows: [
				{ from: "0x100", to: "null", type: "backward" },
				{ from: "0x110", to: "0x200", type: "shared-root" },
				{ from: "0x200", to: "0x300", type: "forward" },
				{ from: "0x300", to: "null", type: "forward" },
				{ from: "0x220", to: "0x100", type: "cow-backward" },
				{ from: "0x320", to: "0x220", type: "cow-backward" },
			],
			visibleNodes: ["0x100", "0x110", "0x200", "0x300", "0x220", "0x320"],
			title: "Reversal Complete: Both Lists Valid & Safe",
			desc: "Reversed list1: [3' @ 0x320] -> [2' @ 0x220] -> [1 @ 0x100] (Node 1 reused in-place!). list2: [11 @ 0x110] -> [2 @ 0x200] -> [3 @ 0x300] is completely untouched!"
		}
	];

	const nodeMeta: Record<string, { val: number; label: string; x: number; y: number; tag: string }> = {
		"0x100": { val: 1, label: "Node 1", x: 40, y: 50, tag: "REUSED IN-PLACE" },
		"0x110": { val: 11, label: "Node 11 (list2)", x: 40, y: 175, tag: "list2 ROOT" },
		"0x200": { val: 2, label: "Node 2 (shared)", x: 270, y: 110, tag: "SHARED ORIGINAL" },
		"0x300": { val: 3, label: "Node 3 (shared)", x: 500, y: 110, tag: "SHARED ORIGINAL" },
		"0x220": { val: 2, label: "Node 2' (COW)", x: 270, y: 260, tag: "NEW COW ALLOC" },
		"0x320": { val: 3, label: "Node 3' (COW)", x: 500, y: 260, tag: "NEW COW ALLOC" }
	};

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

	const whileCode = [
		{ num: 1, text: "pub fn reverse<T: Clone>(mut xs: Link<T>) -> Link<T> {" },
		{ num: 2, text: "    let mut acc = None;" },
		{ num: 3, text: "    while let Some(mut rc_node) = xs {" },
		{ num: 4, text: "        match Rc::get_mut(&mut rc_node) {" },
		{ num: 5, text: "            Some(node) => { // RC == 1: IN-PLACE" },
		{ num: 6, text: "                xs = node.next.take();" },
		{ num: 7, text: "                node.next = acc;" },
		{ num: 8, text: "                acc = Some(rc_node); // Reuse block!" },
		{ num: 9, text: "            }" },
		{ num: 10, text: "            None => { // RC > 1: COPY-ON-WRITE" },
		{ num: 11, text: "                xs = rc_node.next.clone();" },
		{ num: 12, text: "                acc = Some(Rc::new(Node {" },
		{ num: 13, text: "                    val: rc_node.val.clone()," },
		{ num: 14, text: "                    next: acc," },
		{ num: 15, text: "                }));" },
		{ num: 16, text: "            }" },
		{ num: 17, text: "        }" },
		{ num: 18, text: "    }" },
		{ num: 19, text: "    acc" },
		{ num: 20, text: "}" },
	];

	const tailCode = [
		{ num: 1, text: "fn reverse_rc_tail_acc<T: Clone>(xs: Link<T>, acc: Link<T>) -> Link<T> {" },
		{ num: 2, text: "    match xs {" },
		{ num: 3, text: "        Some(mut rc_node) => match Rc::get_mut(&mut rc_node) {" },
		{ num: 4, text: "            Some(node) => { // UNIQUE: IN-PLACE" },
		{ num: 5, text: "                let next = node.next.take();" },
		{ num: 6, text: "                node.next = acc;" },
		{ num: 7, text: "                reverse_rc_tail_acc(next, Some(rc_node))" },
		{ num: 8, text: "            }" },
		{ num: 9, text: "            None => { // SHARED: COPY-ON-WRITE" },
		{ num: 10, text: "                let next = rc_node.next.clone();" },
		{ num: 11, text: "                let val = rc_node.val.clone();" },
		{ num: 12, text: "                drop(rc_node); // Critical for TCO" },
		{ num: 13, text: "                let new_node = Rc::new(Node { val, next: acc });" },
		{ num: 14, text: "                reverse_rc_tail_acc(next, Some(new_node))" },
		{ num: 15, text: "            }" },
		{ num: 16, text: "        }," },
		{ num: 17, text: "        None => acc," },
		{ num: 18, text: "    }" },
		{ num: 19, text: "}" },
	];

	const codeLines = $derived(algoMode === 'while' ? whileCode : tailCode);
	const activeLine = $derived(algoMode === 'while' ? current.lineWhile : current.lineTail);
</script>

<div class="max-w-6xl mx-auto px-6 space-y-6">
	<div class="flex justify-between items-center border-b border-slate-800 pb-4">
		<div>
			<h1 class="text-2xl font-bold tracking-tight text-white flex items-center gap-3">
				RC List Reversal (Rc&lt;Node&gt; &amp; Perceus COW)
				<span class="text-xs bg-purple-500/20 text-purple-300 font-mono px-2 py-0.5 rounded border border-purple-500/30">
					Rc::get_mut ⇄ is-unique
				</span>
			</h1>
			<p class="text-sm text-slate-400 mt-1">
				In-place mutation when RC == 1, automatic fallback to fresh allocation when RC &gt; 1.
			</p>
		</div>

		<div class="flex items-center gap-1 bg-slate-900 border border-slate-800 p-1 rounded-lg">
			<button
				class="text-xs px-3 py-1.5 rounded font-mono transition-colors {algoMode === 'while' ? 'bg-purple-600 text-white font-semibold' : 'text-slate-400 hover:text-slate-200'}"
				onclick={() => { algoMode = 'while'; stepIdx = 0; isPlaying = false; }}
			>
				while-loop
			</button>
			<button
				class="text-xs px-3 py-1.5 rounded font-mono transition-colors {algoMode === 'tail' ? 'bg-purple-600 text-white font-semibold' : 'text-slate-400 hover:text-slate-200'}"
				onclick={() => { algoMode = 'tail'; stepIdx = 0; isPlaying = false; }}
			>
				tail-rec (FIP)
			</button>
		</div>
	</div>

	<!-- Narrative Box -->
	<div class="bg-slate-900/90 border border-slate-800 rounded-xl p-4 shadow-lg">
		<div class="flex justify-between items-center mb-1">
			<div class="text-xs font-semibold tracking-wider uppercase text-purple-400 font-mono">
				Step {stepIdx + 1} of {steps.length}: {current.title}
			</div>
			{#if current.getMut}
				<div class="text-xs font-mono font-bold px-2 py-0.5 rounded {current.getMut.includes('UNIQUE') ? 'bg-emerald-500/20 text-emerald-300 border border-emerald-500/30' : 'bg-amber-500/20 text-amber-300 border border-amber-500/30'}">
					{current.getMut}
				</div>
			{/if}
		</div>
		<p class="text-sm text-slate-300">{current.desc}</p>
	</div>

	<!-- Code vs Stack -->
	<div class="grid grid-cols-1 md:grid-cols-12 gap-6">
		<div class="md:col-span-7 bg-slate-900 border border-slate-800 rounded-xl p-4 font-mono text-xs">
			<div class="text-slate-400 text-[11px] mb-3 uppercase tracking-wider font-semibold border-b border-slate-800 pb-1 flex justify-between">
				<span>Active Execution Frame</span>
				<span class="text-purple-400">{algoMode === 'while' ? 'Iterative while let' : 'Tail-Recursive inlined'}</span>
			</div>
			<div class="space-y-0.5">
				{#each codeLines as line}
					{@const isActive = line.num === activeLine}
					<div class="flex items-center px-2 py-0.5 rounded transition-colors {isActive ? 'bg-purple-500/20 text-purple-200 font-bold border-l-2 border-purple-400' : 'text-slate-400'}">
						<span class="w-6 text-slate-600 select-none text-[10px] shrink-0">{line.num}</span>
						<span class="whitespace-pre font-mono">{line.text}</span>
					</div>
				{/each}
			</div>
		</div>

		<div class="md:col-span-5 bg-slate-900 border border-slate-800 rounded-xl p-4 font-mono text-xs">
			<div class="text-slate-400 text-[11px] mb-3 uppercase tracking-wider font-semibold border-b border-slate-800 pb-1">
				CPU Registers &amp; Borrow Check
			</div>
			<div class="space-y-2">
				<div class="flex justify-between items-center bg-slate-950/80 px-3 py-2 rounded border-l-2 border-sky-500 text-sky-400">
					<span class="text-slate-400">xs (current input)</span>
					<span class="font-semibold">{current.xs}</span>
				</div>
				<div class="flex justify-between items-center bg-slate-950/80 px-3 py-2 rounded border-l-2 border-emerald-500 text-emerald-400">
					<span class="text-slate-400">acc (accumulator)</span>
					<span class="font-semibold">{current.acc}</span>
				</div>
				<div class="flex justify-between items-center bg-slate-950/80 px-3 py-2 rounded border-l-2 border-amber-500 text-amber-400">
					<span class="text-slate-400">rc_node (under test)</span>
					<span class="font-semibold">{current.rc_node || '—'}</span>
				</div>
				<div class="flex justify-between items-center bg-slate-950/80 px-3 py-2 rounded border-l-2 {current.getMut && current.getMut.includes('UNIQUE') ? 'border-emerald-500 text-emerald-400' : (current.getMut ? 'border-amber-500 text-amber-400' : 'border-slate-700 text-slate-500')}">
					<span class="text-slate-400">Rc::get_mut(&amp;mut rc_node)</span>
					<span class="font-semibold text-[11px]">{current.getMut || 'idle'}</span>
				</div>
			</div>
		</div>
	</div>

	<!-- Heap Canvas -->
	<div class="bg-slate-900 border border-slate-800 rounded-xl p-5">
		<div class="text-slate-400 text-xs font-mono mb-2 uppercase tracking-wider font-semibold flex justify-between">
			<span>Heap Memory &amp; Reference Counts</span>
			<span class="text-slate-500">Green = RC:1 (Unique) | Amber = RC:2 (Shared) | Purple = COW Allocated</span>
		</div>

		<div class="overflow-x-auto py-2">
			<svg width="740" height="380" class="select-none">
				<defs>
					<marker id="arrow-forward" markerWidth="8" markerHeight="8" refX="6" refY="4" orient="auto">
						<path d="M0,1 L7,4 L0,7 Z" fill="#38bdf8" />
					</marker>
					<marker id="arrow-backward" markerWidth="8" markerHeight="8" refX="6" refY="4" orient="auto">
						<path d="M0,1 L7,4 L0,7 Z" fill="#10b981" />
					</marker>
					<marker id="arrow-cow" markerWidth="8" markerHeight="8" refX="6" refY="4" orient="auto">
						<path d="M0,1 L7,4 L0,7 Z" fill="#c084fc" />
					</marker>
					<marker id="arrow-shared" markerWidth="8" markerHeight="8" refX="6" refY="4" orient="auto">
						<path d="M0,1 L7,4 L0,7 Z" fill="#f59e0b" />
					</marker>
				</defs>

				{#each current.arrows as ar}
					{@const src = nodeMeta[ar.from]}
					{#if ar.to === 'null'}
						<g>
							<line x1={src.x + 140} y1={src.y + 40} x2={src.x + 175} y2={src.y + 40} stroke="#64748b" stroke-width="2" />
							<text x={src.x + 182} y={src.y + 44} fill="#64748b" font-size="11" font-family="monospace">null</text>
						</g>
					{:else}
						{@const dst = nodeMeta[ar.to]}
						{#if dst}
							{#if ar.type === 'forward'}
								<line x1={src.x + 140} y1={src.y + 40} x2={dst.x} y2={dst.y + 40} stroke="#38bdf8" stroke-width="2.5" marker-end="url(#arrow-forward)" />
							{:else if ar.type === 'shared-root'}
								<line x1={src.x + 140} y1={src.y + 40} x2={dst.x} y2={dst.y + 50} stroke="#f59e0b" stroke-width="2.5" marker-end="url(#arrow-shared)" />
							{:else if ar.type === 'severed'}
								<g>
									<line x1={src.x + 140} y1={src.y + 40} x2={dst.x} y2={dst.y + 40} stroke="#ef4444" stroke-width="2" stroke-dasharray="4 4" />
									<text x={(src.x + dst.x) / 2 + 30} y={src.y + 25} fill="#ef4444" font-size="10" font-family="monospace" font-weight="bold">✂ take()</text>
								</g>
							{:else if ar.type === 'backward'}
								<line x1={src.x + 140} y1={src.y + 40} x2={src.x + 175} y2={src.y + 40} stroke="#10b981" stroke-width="2.5" marker-end="url(#arrow-backward)" />
							{:else if ar.type === 'cow-backward'}
								{@const d = `M ${src.x} ${src.y + 40} C ${src.x - 40} ${src.y + 40}, ${dst.x + 140} ${dst.y + 40}, ${dst.x + 140} ${dst.y + 40}`}
								<path {d} fill="none" stroke="#c084fc" stroke-width="2.5" marker-end="url(#arrow-cow)" />
							{/if}
						{/if}
					{/if}
				{/each}

				{#each current.visibleNodes as addr}
					{@const meta = nodeMeta[addr]}
					{@const rc = current.nodeRCs[addr] || 1}
					{@const isCurrent = current.rc_node === addr}
					{@const borderStroke = isCurrent ? '#f59e0b' : (addr.includes('220') || addr.includes('320') ? '#a855f7' : (rc > 1 ? '#f59e0b' : '#334155'))}

					<g>
						<rect
							x={meta.x} y={meta.y} width="140" height="80" rx="8"
							fill="#020617" stroke={borderStroke} stroke-width={isCurrent ? 2.5 : 1.5}
						/>
						<rect x={meta.x} y={meta.y} width="140" height="22" rx="6" fill="#0f172a" />
						<text x={meta.x + 8} y={meta.y + 15} fill="#94a3b8" font-size="11" font-family="monospace" font-weight="bold">
							{addr}
						</text>
						<rect x={meta.x + 85} y={meta.y + 3} width="48" height="16" rx="4" fill={rc > 1 ? '#78350f' : '#064e3b'} />
						<text x={meta.x + 90} y={meta.y + 14} fill={rc > 1 ? '#fde68a' : '#6ee7b7'} font-size="9" font-family="monospace" font-weight="bold">
							RC: {rc}
						</text>
						<text x={meta.x + 10} y={meta.y + 44} fill="#e2e8f0" font-size="12" font-family="monospace">
							val: {meta.val}
						</text>
						<text x={meta.x + 10} y={meta.y + 64} fill={meta.tag.includes('COW') ? '#c084fc' : (meta.tag.includes('REUSED') ? '#34d399' : '#64748b')} font-size="9" font-family="monospace" font-weight="bold">
							{meta.tag}
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
				class="bg-purple-600 hover:bg-purple-500 px-4 py-1.5 rounded text-xs text-white font-medium"
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
			<input type="range" min="500" max="3000" step="200" bind:value={speed} class="w-28" />
		</div>
	</div>
</div>
