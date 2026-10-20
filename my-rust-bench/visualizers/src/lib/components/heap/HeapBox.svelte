<script lang="ts">
  let {
    x,
    y,
    width = 140,
    height = 80,
    address,
    val,
    nextText,
    rc,
    tag,
    kind,
    isCurrent = false,
    isAcc = false,
    isXs = false,
    isCow = false
  }: {
    x: number;
    y: number;
    width?: number;
    height?: number;
    address: string;
    val: number;
    nextText?: string;
    rc?: number;
    tag?: string;
    kind?: 'box' | 'rc';
    isCurrent?: boolean;
    isAcc?: boolean;
    isXs?: boolean;
    isCow?: boolean;
  } = $props();

  const borderStroke = $derived(
    isCurrent
      ? '#f59e0b'
      : isCow
        ? '#a855f7'
        : isAcc
          ? '#10b981'
          : isXs
            ? '#38bdf8'
            : rc && rc > 1
              ? '#f59e0b'
              : '#334155'
  );
</script>

<g>
  <rect
    {x}
    {y}
    {width}
    {height}
    rx="8"
    fill="#020617"
    stroke={borderStroke}
    stroke-width={isCurrent || isAcc ? 2.5 : 1.5}
  />
  <rect {x} {y} {width} height="22" rx="6" fill="#0f172a" />

  <text
    x={x + 8}
    y={y + 15}
    fill="#94a3b8"
    font-size="11"
    font-family="monospace"
    font-weight="bold"
  >
    {address}
  </text>

  {#if kind === 'box'}
    <rect x={x + width - 46} y={y + 3} width="40" height="16" rx="4" fill="#064e3b" />
    <text
      x={x + width - 42}
      y={y + 14}
      fill="#6ee7b7"
      font-size="9"
      font-family="monospace"
      font-weight="bold"
    >
      BOX
    </text>
  {:else if rc !== undefined}
    <rect
      x={x + width - 55}
      y={y + 3}
      width="48"
      height="16"
      rx="4"
      fill={rc > 1 ? '#78350f' : '#064e3b'}
    />
    <text
      x={x + width - 50}
      y={y + 14}
      fill={rc > 1 ? '#fde68a' : '#6ee7b7'}
      font-size="9"
      font-family="monospace"
      font-weight="bold"
    >
      RC: {rc}
    </text>
  {/if}

  <text x={x + 10} y={y + 44} fill="#e2e8f0" font-size="12" font-family="monospace">
    val: {val}
  </text>

  {#if nextText}
    <text x={x + 10} y={y + 64} fill="#64748b" font-size="10" font-family="monospace">
      next: {nextText}
    </text>
  {:else if tag}
    <text
      x={x + 10}
      y={y + 64}
      fill={tag.includes('COW')
        ? '#c084fc'
        : tag.includes('REUSED') || tag.includes('UNIQUE')
          ? '#34d399'
          : '#64748b'}
      font-size="9"
      font-family="monospace"
      font-weight="bold"
    >
      {tag}
    </text>
  {/if}
</g>
