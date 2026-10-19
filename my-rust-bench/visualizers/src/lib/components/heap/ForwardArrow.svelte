<script lang="ts">
  let {
    x1,
    y1,
    x2,
    y2,
    color = '#38bdf8',
    markerId = 'arrow-forward'
  }: {
    x1: number;
    y1: number;
    x2: number;
    y2: number;
    color?: string;
    markerId?: string;
  } = $props();
</script>

<line {x1} {y1} {x2} {y2} stroke={color} stroke-width="2.5" marker-end="url(#{markerId})" />
