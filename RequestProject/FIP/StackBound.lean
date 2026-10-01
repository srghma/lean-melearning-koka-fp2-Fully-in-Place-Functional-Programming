module

public import RequestProject.FIP.StackLocal
public import RequestProject.FIP.StoreInv

@[expose] public section

/-!
# The stack bound (Theorem 4, corrected; Appendix C)

**Theorem 4** (`stack_bound`).  Let `Σ` be a signature of the paper's calculus in which every
function is fully in-place (or FBIP) and which is stack safe for a list of non-empty
mutually recursive groups.  Let `S` be a store of the paper's shape (so it contains no
functions).  At any intermediate step `S | f(ȳ; x̄) ⟼*ₛ S' | E[e']` we have

  `|E| ≤ (|Σ| + 1)² · max(1, |e_max|)`.

The statement of the paper, `|E| ≤ |e_max| · |Σ|²`, is false (see
`RequestProject/FIP/StackCex.lean`): already the initial call `f(ȳ; x̄)` has an evaluation
context of depth `1`, which exceeds `|e_max| · |Σ|² = 0` for the identity function.  The
corrected bound has the same shape (linear in `|e_max|`, quadratic in `|Σ|`).

## Proof

The intermediate expression is a stack of *frames* (`Run`): each frame is the current state
of the body of an active call (`Frame`), with a *weight* determined by the rank of the
function and the ranks of the function values it holds (`RequestProject/FIP/StackRank.lean`).
A non-tail call pushes a strictly lighter frame, a tail call replaces the frame by one of
the same weight, and all other steps stay within a frame (`Run.step`).  So at most
`|Σ|² + |Σ|` frames are nested, and each adds at most `max(1, |e_max|)` to the evaluation
context (`Run.bound`).
-/

namespace FIP

variable {sig : Sig} {fbip : Bool}

/-! ## The facts about function bodies that the proof uses -/

/-- What the proof needs to know about the body of every function `g` of `Σ`. -/
def StackSetting (sig : Sig) (groups : List (List FName)) (D : Nat) : Prop :=
  ∀ g fd, sig.lookup g = some fd →
    rank groups g < groups.length ∧ fd.body.sdepth ≤ D ∧
    Expr.TailC (fun h => rank groups h = rank groups g) fd.body ∧
    (∀ h ∈ fd.body.calls, rank groups h ≤ rank groups g) ∧
    (∀ h ∈ fd.body.fns, rank groups h < rank groups g) ∧
    Expr.BP (fd.borrowed.map (·.name)) fd.body

theorem Sig.depth_le_maxDepth {sig : Sig} {fd : FunDef} (h : fd ∈ sig) :
    fd.body.depth ≤ sig.maxDepth := by
  induction sig with
  | nil => simp at h
  | cons fd' sig ih =>
    simp only [Sig.maxDepth, List.map_cons, List.foldr_cons] at ih ⊢
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

theorem Sig.lookup_mem {sig : Sig} {g : FName} {fd : FunDef} (h : sig.lookup g = some fd) :
    fd ∈ sig ∧ fd.name = g := by
  unfold Sig.lookup at h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

theorem mem_binderScalars {xs : List Binder} {x : Var} (h : x ∈ Binder.scalars xs) :
    ∃ b ∈ xs, b.scalar = true := by
  simp only [Binder.scalars, List.mem_toFinset, List.mem_map, List.mem_filter] at h
  obtain ⟨b, ⟨hb, hs⟩, _⟩ := h
  exact ⟨b, hb, hs⟩

/-- The setting of Theorem 4 provides the facts about function bodies. -/
theorem stackSetting {groups : List (List FName)} (hsig : sig.PaperFragment)
    (hfip : ∀ fd ∈ sig, fd.annot ≠ .plain) (hss : sig.StackSafe groups) :
    StackSetting sig groups (max 1 sig.maxDepth) := by
  intro g fd hl
  obtain ⟨hmem, hname⟩ := Sig.lookup_mem hl
  have hnd : groups.flatten.Nodup := hss.partition.nodup_iff.mpr hsig.names
  have hgf : g ∈ groups.flatten :=
    hss.partition.mem_iff.mpr (List.mem_map.mpr ⟨fd, hmem, hname⟩)
  have hlt := rank_lt hgf
  have hgi := mem_of_rank hlt
  obtain ⟨htail, hfuns⟩ := hss.ordered _ hlt g hgi fd hl
  have hrk : ∀ h ∈ fd.body.funs, rank groups h ≤ rank groups g ∧
      (h ∈ groups[rank groups g] → rank groups h = rank groups g) := by
    intro h hh
    obtain ⟨j, hj, hjl, hhj⟩ := hfuns h hh
    rw [rank_of_mem hnd hjl hhj]
    exact ⟨hj, fun hh' => rank_of_mem hnd hlt hh' ▸ (rank_of_mem hnd hjl hhj).symm ▸ rfl⟩
  refine ⟨hlt, ?_, ?_, ?_, ?_, ?_⟩
  · exact le_trans (Expr.sdepth_le_depth _)
      (le_trans (Sig.depth_le_maxDepth hmem) (le_max_right _ _))
  · refine Expr.TailC.of_tailIn (fun h hh => ?_) htail
    have := mem_of_rank (hh ▸ hlt : rank groups h < groups.length)
    simpa [hh] using this
  · exact fun h hh => (hrk h (Expr.calls_subset_funs _ h hh)).1
  · intro h hh
    obtain ⟨j, hj, hjl, hhj⟩ := hfuns h (Expr.fns_subset_funs _ h hh)
    have hrj := rank_of_mem hnd hjl hhj
    rcases lt_or_eq_of_le hj with hj | hj
    · omega
    · subst hj
      exact absurd hhj (Expr.TailIn.fns_not_mem htail h hh)
  · obtain ⟨hnodup, hwf⟩ := hsig.wf fd hmem (hfip fd hmem)
    refine Wf.bp hwf _ fun s hs => ⟨fun hsc => ?_, fun hown => ?_⟩
    · have hall := (hsig.scalarFree fd hmem).1
      simp only [FunDef.scalars, Finset.mem_union] at hsc
      rcases hsc with hsc | hsc
      · obtain ⟨b, hb, hbs⟩ := mem_binderScalars hsc
        have := List.all_eq_true.mp hall b (List.mem_append_left _ hb)
        simp [hbs] at this
      · obtain ⟨b, hb, hbs⟩ := mem_binderScalars hsc
        have := List.all_eq_true.mp hall b (List.mem_append_right _ hb)
        simp [hbs] at this
    · simp only [FunDef.ownedCtx, Multiset.mem_add, Multiset.mem_replicate] at hown
      rcases hown with hown | ⟨-, hown⟩
      · have hso := name_mem_binderVars (mem_binderVars_of_owned hown)
        rw [List.map_append, List.nodup_append] at hnodup
        exact hnodup.2.2 _ hs _ hso rfl
      · cases hown

/-! ## Frames for the bodies of called functions -/

/-- The body of a function called from a frame is a frame. -/
theorem Frame.call {groups : List (List FName)} {D i M : Nat}
    (hset : StackSetting sig groups D) {E : ECtx} {g : FName} {fd : FunDef}
    {as1 as2 : List Val} (hf : Frame groups D i M (E.plug (.call g (.ret as1) (.ret as2))))
    (hl : sig.lookup g = some fd) (ha1 : ∀ a ∈ as1, a.Atomic) (ha2 : ∀ a ∈ as2, a.Atomic) :
    Frame groups D (rank groups g) (max (rank groups g) M)
      (fd.body.subst (zipSubst fd.borrowed as1 ++ zipSubst fd.owned as2)) := by
  obtain ⟨hlt, hsd, htl, hcl, hfn, hbp⟩ := hset g fd hl
  have hc := Expr.bp_nil_of_plug hf.bp (by simp)
  simp only [Expr.BP] at hc
  have h2 : ∀ a ∈ as2, Val.funs a = [] := fun a ha => (hc.2 a ha).1
  have hσ : ∀ p ∈ zipSubst fd.borrowed as1 ++ zipSubst fd.owned as2,
      (p.1 ∈ fd.borrowed.map (·.name) ∨ p.2 ∈ as2) ∧ (p.2 ∈ as1 ∨ p.2 ∈ as2) := by
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact ⟨.inl (mem_zipSubst hp).1, .inl (mem_zipSubst hp).2⟩
    · exact ⟨.inr (mem_zipSubst hp).2, .inr (mem_zipSubst hp).2⟩
  refine ⟨hlt, max_le hlt.le hf.le, by rw [Expr.sdepth_subst]; exact hsd, ?_, htl.subst _,
    by rw [Expr.calls_subst]; exact hcl, ?_⟩
  · refine Expr.bp_subst _ _ _ (fun p hp => ?_) (fun p hp hn => ?_) hbp
    · rcases (hσ p hp).2 with h | h
      · exact ha1 _ h
      · exact ha2 _ h
    · rcases (hσ p hp).1 with h | h
      · exact absurd h hn
      · exact h2 _ h
  · intro h hh
    rcases Expr.fns_subst _ _ h hh with hh | hh
    · exact lt_of_lt_of_le (hfn h hh) (le_max_left _ _)
    · obtain ⟨p, hp, hh⟩ := Subst.mem_fns.mp hh
      rcases (hσ p hp).2 with hp' | hp'
      · refine lt_of_lt_of_le (hf.fns h (ECtx.fns_sub E _ h ?_)) (le_max_right _ _)
        simp only [Expr.fns, List.mem_append, Val.mem_funsList]
        exact .inl ⟨_, hp', hh⟩
      · rw [h2 _ hp'] at hh; simp at hh

/-- The body of a function applied in a frame is a frame. -/
theorem Frame.app {groups : List (List FName)} {D i M : Nat}
    (hset : StackSetting sig groups D) {E : ECtx} {g : FName} {fd : FunDef}
    {as : List Val} (hf : Frame groups D i M (E.plug (.app (.val (.fn g)) (.ret as))))
    (hl : sig.lookup g = some fd) (hb : fd.borrowed = []) (ha : ∀ a ∈ as, a.Atomic) :
    Frame groups D (rank groups g) (rank groups g)
      (fd.body.subst (zipSubst fd.owned as)) := by
  obtain ⟨hlt, hsd, htl, hcl, hfn, hbp⟩ := hset g fd hl
  have hc := Expr.bp_nil_of_plug hf.bp (by simp)
  simp only [Expr.BP] at hc
  have h2 : ∀ a ∈ as, Val.funs a = [] := fun a ha => (hc.2 a ha).1
  rw [hb] at hbp
  refine ⟨hlt, hlt.le, by rw [Expr.sdepth_subst]; exact hsd, ?_, htl.subst _,
    by rw [Expr.calls_subst]; exact hcl, ?_⟩
  · exact Expr.bp_subst _ _ _ (fun p hp => ha _ (mem_zipSubst hp).2)
      (fun p hp _ => h2 _ (mem_zipSubst hp).2) hbp
  · intro h hh
    rcases Expr.fns_subst _ _ h hh with hh | hh
    · exact hfn h hh
    · obtain ⟨p, hp, hh⟩ := Subst.mem_fns.mp hh
      rw [h2 _ (mem_zipSubst hp).2] at hh; simp at hh

/-! ## Stacks of frames -/

/-- A stack of frames whose weights are below `W`: the innermost frame is a `Frame`, and
    every other frame is waiting in an evaluation context `F` for the result of a call `c`
    that it made. -/
inductive Run (groups : List (List FName)) (D : Nat) : Nat → Expr → Prop where
  | leaf {W i M : Nat} {e : Expr} : wt groups.length i M < W → Frame groups D i M e →
      Run groups D W e
  | push {W i M : Nat} (F : ECtx) (c e : Expr) : wt groups.length i M < W →
      Frame groups D i M (F.plug c) → 1 ≤ c.sdepth → (∀ vs, e ≠ .ret vs) →
      Run groups D (wt groups.length i M) e → Run groups D W (F.plug e)

theorem Run.bp {groups : List (List FName)} {D W : Nat} {e : Expr} (h : Run groups D W e) :
    Expr.BP [] e := by
  induction h with
  | leaf _ hf => exact hf.bp
  | push F c e _ hf _ _ _ ih => exact ECtx.bp_plug_repl F c e hf.bp ih

/-- **The bound on a stack of frames.** -/
theorem Run.bound {groups : List (List FName)} {D W : Nat} {e : Expr} (h : Run groups D W e) :
    ∀ (E : ECtx) (e' : Expr), E.plug e' = e → E.depth ≤ W * D := by
  induction h with
  | @leaf W i M e hW hf =>
    intro E e' he
    have h1 := ECtx.depth_plug_sdepth E e'
    rw [he] at h1
    have h2 : D ≤ W * D := Nat.le_mul_of_pos_left D (by omega)
    have := hf.sdepth
    omega
  | @push W i M F c e hW hf hc hne _ ih =>
    intro E e' he
    have hF := ECtx.depth_plug_sdepth F c
    have hFD := hf.sdepth
    have hmul : (wt groups.length i M + 1) * D ≤ W * D := Nat.mul_le_mul_right _ hW
    rw [Nat.succ_mul] at hmul
    rcases ECtx.plug_eq_plug_depth he hne with ⟨G, rfl, hG⟩ | hle
    · have := ih G e' hG
      rw [ECtx.depth_comp]
      omega
    · omega

/-- What happens to the innermost frame: a step other than a call stays in the frame, a
    tail call replaces it, and a non-tail call pushes a lighter frame. -/
theorem Run.leaf_step {groups : List (List FName)} {D W i M : Nat}
    (hset : StackSetting sig groups D) {e e' : Expr} {S S' : Store}
    (hW : wt groups.length i M < W) (hf : Frame groups D i M e) (hS : S.NoFn)
    (h : SStep sig fbip S e S' e') : Run groups D W e' := by
  have nontail : ∀ {E : ECtx} {c inst : Expr} {j M' : Nat}, Frame groups D i M (E.plug c) →
      1 ≤ c.sdepth → Frame groups D j M' inst → wt groups.length j M' < wt groups.length i M →
      Run groups D W (E.plug inst) := by
    intro E c inst j M' hfc hc hfi hlt
    by_cases hret : ∃ vs, inst = .ret vs
    · obtain ⟨vs, rfl⟩ := hret
      exact .leaf hW (hfc.ret fun v hv => (hfi.bp v hv).1)
    · exact .push E c inst hW hfc hc (fun vs h => hret ⟨vs, h⟩) (.leaf hlt hfi)
  cases h with
  | head E hh =>
    have hstep := fun hc ha => hf.head_step hS hh hc ha
    cases hh with
    | call S0 g fd as1 as2 hl ha1 ha2 _ _ =>
      have hfc := Frame.call hset hf hl ha1 ha2
      have hj : rank groups g ≤ i := hf.calls g (ECtx.calls_sub E _ g (by simp [Expr.calls]))
      have hcd : 1 ≤ (Expr.call g (.ret as1) (.ret as2)).sdepth := by simp [Expr.sdepth]
      rcases hf.tail.plug_avoid with rfl | hav
      · by_cases hji : rank groups g = i
        · subst hji
          exact .leaf (by rw [wt_tail]; exact hW) hfc
        · exact nontail hf hcd hfc (wt_call_lt (by omega))
      · have hji : rank groups g ≠ i := hav g (by simp [Expr.calls])
        exact nontail hf hcd hfc (wt_call_lt (by omega))
    | app S0 g fd as hl hb ha _ =>
      have hfa := Frame.app hset hf hl hb ha
      have hj : rank groups g < M :=
        hf.fns g (ECtx.fns_sub E _ g (by simp [Expr.fns, Val.funsList, Val.funs]))
      have hcd : 1 ≤ (Expr.app (.val (.fn g)) (.ret as)).sdepth := by simp [Expr.sdepth]
      exact nontail hf hcd hfa (wt_app_lt hj hfa.lt)
    | _ =>
      exact .leaf hW (hstep (fun _ _ _ h => Expr.noConfusion h) (fun _ _ h => Expr.noConfusion h))
  | val E done V rest hd hV hv =>
    exact .leaf hW (hf.val_step ⟨done, V, rest, _, _, hd, hV, hv, rfl, rfl⟩)

/-- **The store semantics preserves stacks of frames.** -/
theorem Run.step {groups : List (List FName)} {D : Nat} (hset : StackSetting sig groups D)
    {W : Nat} {e : Expr} (hr : Run groups D W e) :
    ∀ {S S' : Store} {e' : Expr}, S.NoFn → SStep sig fbip S e S' e' → Run groups D W e' := by
  induction hr with
  | leaf hW hf => exact fun hS h => Run.leaf_step hset hW hf hS h
  | @push W i M F c e hW hf hc hne hr ih =>
    intro S S' e' hS h
    rcases SStep.decomp h hne with ⟨e₁, hs, rfl⟩ | ⟨F', -, rfl, hall⟩
    · have hr₁ := ih hS hs
      by_cases hret : ∃ vs, e₁ = .ret vs
      · obtain ⟨vs, rfl⟩ := hret
        exact .leaf hW (hf.ret fun v hv => (hr₁.bp v hv).1)
      · exact .push F c e₁ hW hf hc (fun vs h => hret ⟨vs, h⟩) hr₁
    · obtain ⟨E', r, r', h1, h2, hv⟩ := hall c
      have hf' : Frame groups D i M (F'.plug c) := by
        rw [h2]; rw [h1] at hf; exact hf.val_step hv
      exact .push F' c e hW hf' hc hne hr

theorem Run.steps {groups : List (List FName)} {D : Nat} (hset : StackSetting sig groups D)
    {W : Nat} {S₁ S₂ : Store} {e₁ e₂ : Expr} (h : SSteps sig fbip S₁ e₁ S₂ e₂)
    (hr : Run groups D W e₁) (hS : S₁.NoFn) : Run groups D W e₂ ∧ S₂.NoFn := by
  induction h with
  | refl => exact ⟨hr, hS⟩
  | tail _ hs ih =>
    obtain ⟨hr', hS'⟩ := ih hr
    exact ⟨hr'.step hset hS' hs, hS'.step hr'.bp hs⟩

/-! ## Theorem 4 -/

/-- **Theorem 4** (a FIP program uses constant stack space, corrected bound).  Let `Σ` be a
    signature of the paper's calculus all of whose functions are fully in-place (or FBIP),
    and which is stack safe for a list of non-empty mutually recursive groups.  Let `S` be a
    store of the paper's shape (it contains no functions).  At any intermediate step
    `S | f(ȳ; x̄) ⟼*ₛ S' | E[e']` we have `|E| ≤ (|Σ| + 1)² · max(1, |e_max|)`. -/
theorem stack_bound {sig : Sig} (hsig : sig.PaperFragment) (hfip : ∀ fd ∈ sig, fd.annot ≠ .plain)
    {groups : List (List FName)} (hss : sig.StackSafe groups) (hne : ∀ g ∈ groups, g ≠ [])
    {fbip : Bool} {f : FName} {fd : FunDef} (hf : sig.lookup f = some fd) {ys xs : List Var}
    {S : Store} (hS : Store.Ptr S) {S' : Store} {e : Expr}
    (h : SSteps sig fbip S (.call f (.ret (ys.map .var)) (.ret (xs.map .var))) S' e)
    (E : ECtx) (e' : Expr) (he : e = E.plug e') :
    E.depth ≤ (sig.length + 1) ^ 2 * max 1 sig.maxDepth := by
  have hset := stackSetting hsig hfip hss
  have hm : groups.length ≤ sig.length := by
    have h1 := length_le_flatten hne
    rw [hss.partition.length_eq, List.length_map] at h1
    exact h1
  have hlt := (hset f fd hf).1
  have hfr : Frame groups (max 1 sig.maxDepth) (rank groups f) (rank groups f)
      (.call f (.ret (ys.map .var)) (.ret (xs.map .var))) := by
    refine ⟨hlt, hlt.le, by simp [Expr.sdepth], ⟨.inl ?_, fun v hv => ?_⟩,
      .call _ _ _ (by simp [Expr.calls]) (by simp [Expr.calls]), ?_, ?_⟩
    · intro y hy
      obtain ⟨x, -, rfl⟩ := List.mem_map.mp hy
      trivial
    · obtain ⟨x, -, rfl⟩ := List.mem_map.mp hv
      exact ⟨rfl, by simp⟩
    · intro g hg
      simp only [Expr.calls, List.append_nil, List.mem_singleton] at hg
      rw [hg]
    · intro g hg
      simp [Expr.fns, Val.mem_funsList, Val.funs] at hg
  have hrun : Run groups (max 1 sig.maxDepth)
      (groups.length * groups.length + groups.length + 1) _ :=
    .leaf (by have := wt_le hlt hlt.le; omega) hfr
  have hnofn : S.NoFn := by
    intro x c as hc a ha
    obtain ⟨n, rfl⟩ := (hS _ hc).2 a ha
    exact ⟨trivial, rfl⟩
  have hb := (Run.steps hset h hrun hnofn).1.bound E e' he.symm
  have hW : groups.length * groups.length + groups.length + 1 ≤ (sig.length + 1) ^ 2 := by nlinarith
  exact le_trans hb (Nat.mul_le_mul_right _ hW)

end FIP
