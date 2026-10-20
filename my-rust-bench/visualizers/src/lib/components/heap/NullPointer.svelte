<script lang="ts">
  let {
    x,
    y,
    length = 35
  }: {
    x: number;
    y: number;
    length?: number;
  } = $props();
</script>

<g>
  <line x1={x} y1={y} x2={x + length} y2={y} stroke="#64748b" stroke-width="2" />
  <text x={x + length + 6} y={y + 4} fill="#64748b" font-size="11" font-family="monospace">
    null
  </text>
</g>
