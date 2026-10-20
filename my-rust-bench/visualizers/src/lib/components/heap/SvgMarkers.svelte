<script lang="ts">
  let {
    includeCow = true,
    includeShared = true
  }: {
    includeCow?: boolean;
    includeShared?: boolean;
  } = $props();
</script>

<defs>
  <marker id="arrow-forward" markerWidth="8" markerHeight="8" refX="6" refY="4" orient="auto">
    <path d="M0,1 L7,4 L0,7 Z" fill="#38bdf8" />
  </marker>
  <marker id="arrow-backward" markerWidth="8" markerHeight="8" refX="6" refY="4" orient="auto">
    <path d="M0,1 L7,4 L0,7 Z" fill="#10b981" />
  </marker>
  {#if includeCow}
    <marker id="arrow-cow" markerWidth="8" markerHeight="8" refX="6" refY="4" orient="auto">
      <path d="M0,1 L7,4 L0,7 Z" fill="#c084fc" />
    </marker>
  {/if}
  {#if includeShared}
    <marker id="arrow-shared" markerWidth="8" markerHeight="8" refX="6" refY="4" orient="auto">
      <path d="M0,1 L7,4 L0,7 Z" fill="#f59e0b" />
    </marker>
  {/if}
</defs>
