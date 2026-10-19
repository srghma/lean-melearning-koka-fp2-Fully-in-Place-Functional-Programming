<script lang="ts">
  import './layout.css';
  import Navbar from '#lib/components/ui/Navbar.svelte';

  let { children } = $props();
</script>

<div class="min-h-screen bg-slate-950 font-sans text-slate-100">
  <Navbar />
  <main class="py-6">
    {@render children()}
  </main>
</div>
