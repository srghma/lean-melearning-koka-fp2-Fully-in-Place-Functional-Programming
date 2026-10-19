<script lang="ts">
  let {
    x1,
    y1,
    x2,
    y2,
    label = '✂ take()'
  }: {
    x1: number;
    y1: number;
    x2: number;
    y2: number;
    label?: string;
  } = $props();
</script>

<g>
  <line {x1} {y1} {x2} {y2} stroke="#ef4444" stroke-width="2" stroke-dasharray="4 4" />
  <text
    x={(x1 + x2) / 2 + 15}
    y={y1 - 12}
    fill="#ef4444"
    font-size="10"
    font-family="monospace"
    font-weight="bold"
  >
    {label}
  </text>
</g>
