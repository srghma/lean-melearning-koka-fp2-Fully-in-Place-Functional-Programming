module

public import RequestProject.AppC_StackBound.StackLocal
public import RequestProject.AppB_StoreSoundness.StoreInv
public import RequestProject.AppB_StoreSoundness.StoreSoundCall

@[expose] public section

/- ══════════════════ PAPER sec. 2.6, App. C START: Stack Safe FIP: Theorem 4; Stack Bound (PDF p. 14; App. C on pp. 54-67) ══════════════════
   `stack_bound`: `|E| <= (|Sigma|+1)^2 * max(1, |e_max|)` for every context reached from a call. -/

/-!
# The stack bound (Theorem 4, corrected; Appendix C)

**Theorem 4** (`stack_bound`).  Let `Σ` be a signature of the paper's calculus in which every
function is fully in-place (or FBIP) and which is stack safe for a list of non-empty
mutually recursive groups.  Let `S` be a store of the paper's shape (so it contains no
functions).  At any intermediate step `S | f(ȳ; x̄) ⟼*ₛ S' | E[e']` we have

  `|E| ≤ (|Σ| + 1)² · max(1, |e_max|)`.

The statement of the paper, `|E| ≤ |e_max| · |Σ|²`, is false (see
`RequestProject/AppC_StackBound/StackCex.lean`): already the initial call `f(ȳ; x̄)` has an evaluation
context of depth `1`, which exceeds `|e_max| · |Σ|² = 0` for the identity function.  The
corrected bound has the same shape (linear in `|e_max|`, quadratic in `|Σ|`).

## Proof

The intermediate expression is a stack of *frames* (`Run`): each frame is the current state
of the body of an active call (`Frame`), with a *weight* determined by the rank of the
function and the ranks of the function values it holds (`RequestProject/AppC_StackBound/StackRank.lean`).
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
    Expr.BP (fun x => ∃ j, x = fd.bParam j) fd.body

theorem Sig.depth_le_maxDepth {sig : Sig} {fd : FunDef} (h : fd ∈ sig) :
    fd.body.depth ≤ sig.maxDepth := by
  induction sig with
  | nil => simp at h
  | cons fd' sig ih =>
    simp only [Sig.maxDepth, List.map_cons, List.foldr_cons] at ih ⊢
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

theorem Sig.mem_of_lookup {sig : Sig} {g : FName} {fd : FunDef} (h : sig.lookup g = some fd) :
    fd ∈ sig ∧ fd.name = g := by
  unfold Sig.lookup at h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

/-- The setting of Theorem 4 provides the facts about function bodies. -/
theorem stackSetting {groups : List (List FName)} (hsig : sig.PaperFragment)
    (hfip : ∀ fd ∈ sig, fd.annot ≠ .plain) (hss : sig.StackSafe groups) :
    StackSetting sig groups (max 1 sig.maxDepth) := by
  intro g fd hl
  obtain ⟨hmem, hname⟩ := Sig.mem_of_lookup hl
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
  · have hwf := hsig.wf fd hmem (hfip fd hmem)
    have hall := (hsig.scalarFree fd hmem).1
    rw [List.all_append, Bool.and_eq_true] at hall
    have hb0 := hsig.noBudget fd hmem
    refine Wf.bp hwf _ fun x hx => ⟨fun hsc => ?_, fun hown => ?_⟩
    · simp [FunDef.scalars, Binder.scalarsAt, Binder.select_true_of_all hall.1,
        Binder.select_true_of_all hall.2] at hsc
    · obtain ⟨j, rfl⟩ := hx
      simp only [FunDef.ownedCtx, hb0, Multiset.replicate_zero, add_zero,
        Binder.mem_ownedAt_var] at hown
      obtain ⟨i, -, hi⟩ := Binder.mem_select.mp hown
      simp only [FunDef.oParam, FunDef.bParam, Var.bvar.injEq, Fin.mk.injEq] at hi
      omega

/-! ## Frames for the bodies of called functions -/

/-- The values substituted for the parameters of a function body: a borrowed parameter is
    replaced by a borrowed argument, an owned one by an owned argument. -/
theorem FunDef.argSubst_mem {m : Nat} (fd : FunDef) {as1 as2 : List (Val m)}
    (hl1 : fd.borrowed.length = as1.length) (hl2 : fd.owned.length = as2.length)
    (i : Fin (fd.owned.length + fd.borrowed.length)) :
    ((∃ j, Var.bvar i = fd.bParam j) ∧ fd.argSubst as1 as2 i ∈ as1) ∨
      fd.argSubst as1 as2 i ∈ as2 := by
  by_cases hi : i.val < fd.borrowed.length
  · refine .inl ⟨⟨⟨i, hi⟩, rfl⟩, ?_⟩
    simp only [FunDef.argSubst]
    rw [Subst.inst_lt _ _ _ _ hi, List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem _
  · refine .inr ?_
    simp only [FunDef.argSubst]
    rw [Subst.inst_ge _ _ _ _ (by omega)]
    simp only [Subst.ofList]
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem _

/-- The body of a function called from a frame is a frame. -/
theorem Frame.call {groups : List (List FName)} {D i M : Nat}
    (hset : StackSetting sig groups D) {E : ECtx 0} {g : FName} {fd : FunDef}
    {as1 as2 : List (Val 0)} (hf : Frame groups D i M (E.plug (.call g (.ret as1) (.ret as2))))
    (hl : sig.lookup g = some fd) (ha1 : ∀ a ∈ as1, a.Atomic) (ha2 : ∀ a ∈ as2, a.Atomic)
    (hl1 : fd.borrowed.length = as1.length) (hl2 : fd.owned.length = as2.length) :
    Frame groups D (rank groups g) (max (rank groups g) M) (fd.instBody as1 as2) := by
  obtain ⟨hlt, hsd, htl, hcl, hfn, hbp⟩ := hset g fd hl
  have hc := Expr.bp_nil_of_plug hf.bp (by simp)
  simp only [Expr.BP] at hc
  have h2 : ∀ a ∈ as2, Val.funs a = [] := fun a ha => (hc.2 a ha).1
  have hσ := fd.argSubst_mem hl1 hl2
  unfold FunDef.instBody
  refine ⟨hlt, max_le hlt.le hf.le, by rw [Expr.sdepth_subst]; exact hsd, ?_, htl.subst _,
    by rw [Expr.calls_subst]; exact hcl, ?_⟩
  · refine Expr.bp_subst _ _ _ (fun p => ?_) (fun p hn => ?_) hbp
    · rcases hσ p with ⟨-, h⟩ | h
      · exact ha1 _ h
      · exact ha2 _ h
    · rcases hσ p with ⟨h, -⟩ | h
      · exact absurd h hn
      · exact h2 _ h
  · intro h hh
    rcases Expr.fns_subst _ _ h hh with hh | hh
    · exact lt_of_lt_of_le (hfn h hh) (le_max_left _ _)
    · obtain ⟨p, hh⟩ := Subst.mem_fns.mp hh
      rcases hσ p with ⟨-, hp'⟩ | hp'
      · refine lt_of_lt_of_le (hf.fns h (ECtx.fns_sub E _ h ?_)) (le_max_right _ _)
        simp only [Expr.fns, List.mem_append, Val.mem_funsList]
        exact .inl ⟨_, hp', hh⟩
      · rw [h2 _ hp'] at hh; simp at hh

/-- The body of a function applied in a frame is a frame. -/
theorem Frame.app {groups : List (List FName)} {D i M : Nat}
    (hset : StackSetting sig groups D) {E : ECtx 0} {g : FName} {fd : FunDef}
    {as : List (Val 0)} (hf : Frame groups D i M (E.plug (.app (.val (.fn g)) (.ret as))))
    (hl : sig.lookup g = some fd) (hb : fd.borrowed = []) (ha : ∀ a ∈ as, a.Atomic)
    (hl2 : fd.owned.length = as.length) :
    Frame groups D (rank groups g) (rank groups g) (fd.instBody [] as) := by
  obtain ⟨hlt, hsd, htl, hcl, hfn, hbp⟩ := hset g fd hl
  have hc := Expr.bp_nil_of_plug hf.bp (by simp)
  simp only [Expr.BP] at hc
  have h2 : ∀ a ∈ as, Val.funs a = [] := fun a ha => (hc.2 a ha).1
  have hσ := fd.argSubst_mem (as1 := []) (by simp [hb]) hl2
  unfold FunDef.instBody
  refine ⟨hlt, hlt.le, by rw [Expr.sdepth_subst]; exact hsd, ?_, htl.subst _,
    by rw [Expr.calls_subst]; exact hcl, ?_⟩
  · refine Expr.bp_subst _ _ _ (fun p => ?_) (fun p _ => ?_) hbp
    · rcases hσ p with ⟨-, h⟩ | h
      · simp at h
      · exact ha _ h
    · rcases hσ p with ⟨-, h⟩ | h
      · simp at h
      · exact h2 _ h
  · intro h hh
    rcases Expr.fns_subst _ _ h hh with hh | hh
    · exact hfn h hh
    · obtain ⟨p, hh⟩ := Subst.mem_fns.mp hh
      rcases hσ p with ⟨-, h'⟩ | h'
      · simp at h'
      · rw [h2 _ h'] at hh; simp at hh

/-! ## Stacks of frames -/

/-- A stack of frames whose weights are below `W`: the innermost frame is a `Frame`, and
    every other frame is waiting in an evaluation context `F` for the result of a call `c`
    that it made. -/
inductive Run (groups : List (List FName)) (D : Nat) : Nat → Expr 0 → Prop where
  | leaf {W i M : Nat} {e : Expr 0} : wt groups.length i M < W → Frame groups D i M e →
      Run groups D W e
  | push {W i M : Nat} (F : ECtx 0) (c e : Expr 0) : wt groups.length i M < W →
      Frame groups D i M (F.plug c) → 1 ≤ c.sdepth → (∀ vs, e ≠ .ret vs) →
      Run groups D (wt groups.length i M) e → Run groups D W (F.plug e)

theorem Run.bp {groups : List (List FName)} {D W : Nat} {e : Expr 0} (h : Run groups D W e) :
    Expr.BP (fun _ => False) e := by
  induction h with
  | leaf _ hf => exact hf.bp
  | push F c e _ hf _ _ _ ih => exact ECtx.bp_plug_repl F c e hf.bp ih

/-- **The bound on a stack of frames.** -/
theorem Run.bound {groups : List (List FName)} {D W : Nat} {e : Expr 0} (h : Run groups D W e) :
    ∀ (E : ECtx 0) (e' : Expr 0), E.plug e' = e → E.depth ≤ W * D := by
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
    (hset : StackSetting sig groups D) {e e' : Expr 0} {S S' : Store}
    (hW : wt groups.length i M < W) (hf : Frame groups D i M e) (hS : S.NoFn)
    (h : SStep sig fbip S e S' e') : Run groups D W e' := by
  have nontail : ∀ {E : ECtx 0} {c inst : Expr 0} {j M' : Nat}, Frame groups D i M (E.plug c) →
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
    | call S0 g fd as1 as2 hl ha1 ha2 hl1 hl2 =>
      have hfc := Frame.call hset hf hl ha1 ha2 hl1 hl2
      have hj : rank groups g ≤ i := hf.calls g (ECtx.calls_sub E _ g (by simp [Expr.calls]))
      have hcd : 1 ≤ (Expr.call g (.ret as1) (.ret as2)).sdepth := by simp [Expr.sdepth]
      rcases hf.tail.plug_avoid with rfl | hav
      · by_cases hji : rank groups g = i
        · subst hji
          exact .leaf (by rw [wt_tail]; exact hW) hfc
        · exact nontail hf hcd hfc (wt_call_lt (by omega))
      · have hji : rank groups g ≠ i := hav g (by simp [Expr.calls])
        exact nontail hf hcd hfc (wt_call_lt (by omega))
    | app S0 g fd as hl hb ha hl2 =>
      have hfa := Frame.app hset hf hl hb ha hl2
      have hj : rank groups g < M :=
        hf.fns g (ECtx.fns_sub E _ g (by simp [Expr.fns, Val.funsList, Val.funs]))
      have hcd : 1 ≤ (Expr.app (.val (.fn g)) (.ret as)).sdepth := by simp [Expr.sdepth]
      exact nontail hf hcd hfa (wt_app_lt hj hfa.lt)
    | _ =>
      exact .leaf hW (hstep (fun _ _ _ h => by cases h) (fun _ _ h => by cases h))
  | val E done V rest hd hV hv =>
    exact .leaf hW (hf.val_step ⟨done, V, rest, _, _, hd, hV, hv, rfl, rfl⟩)

/-- **The store semantics preserves stacks of frames.** -/
theorem Run.step {groups : List (List FName)} {D : Nat} (hset : StackSetting sig groups D)
    {W : Nat} {e : Expr 0} (hr : Run groups D W e) :
    ∀ {S S' : Store} {e' : Expr 0}, S.NoFn → SStep sig fbip S e S' e' → Run groups D W e' := by
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
    {W : Nat} {S₁ S₂ : Store} {e₁ e₂ : Expr 0} (h : SSteps sig fbip S₁ e₁ S₂ e₂)
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
    {fbip : Bool} {f : FName} {fd : FunDef} (hf : sig.lookup f = some fd) {ys xs : List (Var 0)}
    {S : Store} (hS : Store.Ptr S) {S' : Store} {e : Expr 0}
    (h : SSteps sig fbip S (.call f (.ret (ys.map .var)) (.ret (xs.map .var))) S' e)
    (E : ECtx 0) (e' : Expr 0) (he : e = E.plug e') :
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

/- ══════════════════ PAPER sec. 2.6, App. C END: Stack Safe FIP: Theorem 4; Stack Bound ══════════════════ -/
