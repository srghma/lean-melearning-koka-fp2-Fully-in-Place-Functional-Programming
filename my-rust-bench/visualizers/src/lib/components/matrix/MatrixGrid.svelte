<script lang="ts">
  import { matrixCells, columnHeaders, rowHeaders, type MatrixCell } from '#lib/models/matrix/data';

  let {
    selectedCell,
    onSelect
  }: {
    selectedCell: MatrixCell;
    onSelect: (cell: MatrixCell) => void;
  } = $props();

  const tagClasses = {
    fip: 'border-emerald-500/30 bg-emerald-500/20 text-emerald-300',
    cow: 'border-purple-500/30 bg-purple-500/20 text-purple-300',
    view: 'border-sky-500/30 bg-sky-500/20 text-sky-300',
    forbid: 'border-rose-500/30 bg-rose-500/20 text-rose-300'
  };
</script>

<div
  class="overflow-x-auto rounded-xl border border-slate-800 bg-slate-900/80 shadow-2xl backdrop-blur"
>
  <table class="w-full border-collapse text-left text-xs">
    <thead>
      <tr class="border-b border-slate-800 bg-slate-950/70">
        <th class="p-3 font-mono text-[11px] font-semibold tracking-wider text-slate-400 uppercase">
          Input \ Output
        </th>
        {#each columnHeaders as col, idx (idx)}
          <th class="border-l border-slate-800 p-3 font-mono">
            <div class="text-[11px] font-semibold text-slate-300 uppercase">
              [Col {idx + 1}] {col.title}
            </div>
            <div class="{col.color} font-mono text-[10px]">{col.subtitle}</div>
            <div class="text-[9px] text-slate-500">{col.typeBadge}</div>
          </th>
        {/each}
      </tr>
    </thead>
    <tbody class="divide-y divide-slate-800">
      {#each matrixCells as row, rIdx (rIdx)}
        {@const rowMeta = rowHeaders[rIdx]}
        <tr class="transition-colors hover:bg-slate-800/30">
          <td class="w-44 border-r border-slate-800 bg-slate-950/40 p-3 align-top font-mono">
            <div class="text-xs font-bold {rowMeta.color}">{rowMeta.title}</div>
            <div class="text-[10px] text-slate-400">{rowMeta.subtitle}</div>
            <div class="mt-1 text-[9px] text-slate-500">{rowMeta.typeBadge}</div>
          </td>
          {#each row as cell, cIdx (cIdx)}
            {@const isSelected = selectedCell.row === cell.row && selectedCell.col === cell.col}
            <td
              onclick={() => onSelect(cell)}
              class="cursor-pointer border-l border-slate-800 p-3 align-top transition-all duration-150 {isSelected
                ? 'border-sky-400/80 bg-sky-500/10 ring-2 ring-sky-500/50'
                : 'hover:bg-slate-800/60'}"
            >
              <div class="flex items-center justify-between gap-1">
                <span
                  class="font-mono text-xs font-bold {isSelected
                    ? 'text-sky-300'
                    : 'text-slate-200'}"
                >
                  {cell.id}
                </span>
                <span
                  class="rounded border px-1.5 py-0.5 font-mono text-[9px] font-semibold {tagClasses[
                    cell.tagType
                  ]}"
                >
                  {cell.tag}
                </span>
              </div>
              <div class="mt-1.5 line-clamp-2 text-[11px] leading-relaxed text-slate-400">
                {cell.theoryDesc}
              </div>
            </td>
          {/each}
        </tr>
      {/each}
    </tbody>
  </table>
</div>
