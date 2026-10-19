<script lang="ts">
</script>

<div
  class="flex flex-wrap items-center gap-4 rounded-lg border border-slate-800/80 bg-slate-950/60 px-3 py-2 font-mono text-xs text-slate-400"
>
  <div class="flex items-center gap-1.5">
    <span class="h-2.5 w-2.5 rounded-full bg-emerald-400"></span>
    <span>RC: 1 (Unique / In-Place)</span>
  </div>
  <div class="flex items-center gap-1.5">
    <span class="h-2.5 w-2.5 rounded-full bg-amber-400"></span>
    <span>RC &gt; 1 (Shared / Read-Only)</span>
  </div>
  <div class="flex items-center gap-1.5">
    <span class="h-2.5 w-2.5 rounded-full bg-purple-400"></span>
    <span>Purple: Fresh COW Allocation</span>
  </div>
  <div class="flex items-center gap-1.5">
    <span class="h-2.5 w-2.5 rounded-full bg-sky-400"></span>
    <span>Blue: Forward Pointer</span>
  </div>
</div>
