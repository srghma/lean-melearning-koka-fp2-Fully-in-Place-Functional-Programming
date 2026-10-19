<script lang="ts">
  let {
    d,
    color = '#10b981',
    markerId = 'arrow-backward'
  }: {
    d: string;
    color?: string;
    markerId?: string;
  } = $props();
</script>

<path {d} fill="none" stroke={color} stroke-width="2.5" marker-end="url(#{markerId})" />
