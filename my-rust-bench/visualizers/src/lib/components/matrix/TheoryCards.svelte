<script lang="ts">
</script>

<section class="space-y-4 pt-6">
  <div class="space-y-1">
    <h3 class="text-xl font-bold tracking-tight text-white">
      Theoretical Foundations (Marshall, Vollmer & Orchard, ESOP 2022)
    </h3>
    <p class="text-xs text-slate-400">
      How Rust's borrow checker and functional uniqueness typing systems relate to Girard's linear
      logic and Granule.
    </p>
  </div>

  <div class="grid grid-cols-1 gap-4 md:grid-cols-2">
    <div class="space-y-2 rounded-xl border border-slate-800 bg-slate-900/60 p-5">
      <h4 class="flex items-center gap-2 font-semibold text-emerald-400">
        <span class="h-2 w-2 rounded-full bg-emerald-400"></span>
        1. Linearity vs. Uniqueness
      </h4>
      <p class="text-xs leading-relaxed text-slate-400">
        <strong class="text-slate-300">Linearity</strong> is a contract on the <em>future</em>: a
        value must be consumed exactly once. Because of dereliction (<code class="text-emerald-300"
          >!A ⊸ A</code
        >), a linear value could have originated from a shared alias.
        <strong class="text-slate-300">Uniqueness</strong> (<code class="text-emerald-300">*A</code
        >) is a guarantee about the <em>past</em>: no other pointers exist. Safe in-place mutation
        requires uniqueness, not just linearity.
      </p>
    </div>

    <div class="space-y-2 rounded-xl border border-slate-800 bg-slate-900/60 p-5">
      <h4 class="flex items-center gap-2 font-semibold text-purple-400">
        <span class="h-2 w-2 rounded-full bg-purple-400"></span>
        2. The Relative Monad (* and !)
      </h4>
      <p class="text-xs leading-relaxed text-slate-400">
        In the LCU calculus, the non-linearity modality <code class="text-purple-300">!</code> forms
        a relative monad over uniqueness <code class="text-purple-300">*</code>:
        <code class="text-purple-300">borrow : *a ⊸ !a</code> serves as the return, while
        <code class="text-purple-300">copy : (*a ⊸ !b) ⊸ !a ⊸ !b</code> acts as the bind. Forgetting uniqueness
        into shared read access is free; manufacturing uniqueness from shared access requires deep cloning.
      </p>
    </div>

    <div class="space-y-2 rounded-xl border border-slate-800 bg-slate-900/60 p-5">
      <h4 class="flex items-center gap-2 font-semibold text-sky-400">
        <span class="h-2 w-2 rounded-full bg-sky-400"></span>
        3. Fractional Permissions as Borrowing
      </h4>
      <p class="text-xs leading-relaxed text-slate-400">
        Section 6 formalizes Rust's <code class="text-sky-300">&amp;T</code> via fractional
        uniqueness:
        <code class="text-sky-300">*n P ⊗ *m P &harr; *n+m P</code>. A complete
        <code class="text-sky-300">*1 P</code>
        allows destructive mutation. Splitting into fractions
        <code class="text-sky-300">*n P (n &lt; 1)</code> allows multiple concurrent readers while freezing
        mutation until recombined.
      </p>
    </div>

    <div class="space-y-2 rounded-xl border border-slate-800 bg-slate-900/60 p-5">
      <h4 class="flex items-center gap-2 font-semibold text-amber-400">
        <span class="h-2 w-2 rounded-full bg-amber-400"></span>
        4. Dynamic Perceus vs. Static LCU
      </h4>
      <p class="text-xs leading-relaxed text-slate-400">
        While LCU statically forbids promoting <code class="text-amber-300">!A &rarr; *A</code>
        without cloning, runtime reference counting (<code class="text-amber-300">Rc::get_mut</code>
        / <code class="text-amber-300">Rc::try_unwrap</code>) dynamically evaluates
        <code class="text-amber-300">is-unique</code>. When
        <code class="text-amber-300">RC == 1</code>, it executes FIP in-place; when
        <code class="text-amber-300">RC &gt; 1</code>, it executes a Copy-on-Write clone.
      </p>
    </div>
  </div>
</section>
