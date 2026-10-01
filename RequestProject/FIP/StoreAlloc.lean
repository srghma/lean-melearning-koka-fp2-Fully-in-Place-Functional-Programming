module

public import RequestProject.FIP.StoreInv

@[expose] public section

/-!
# Allocating values and dropping trees in the store semantics

Auxiliary results for the proof of Theorem 1:

* reductions of the store semantics can be composed and performed inside evaluation
  contexts;
* a well-formed value is allocated in the store by consuming exactly its reuse credits
  (rules *reuse* and *atom*);
* `drop x` deallocates the whole tree rooted at `x` (rule *dcon* of Fig. 6).
-/

namespace FIP

/-! ## Composing reductions -/

theorem SSteps.single {sig : Sig} {fbip : Bool} {S S' : Store} {e e' : Expr}
    (h : SStep sig fbip S e S' e') : SSteps sig fbip S e S' e' := .tail (.refl _ _) h

theorem SSteps.trans {sig : Sig} {fbip : Bool} {S₁ S₂ S₃ : Store} {e₁ e₂ e₃ : Expr}
    (h₁ : SSteps sig fbip S₁ e₁ S₂ e₂) (h₂ : SSteps sig fbip S₂ e₂ S₃ e₃) :
    SSteps sig fbip S₁ e₁ S₃ e₃ := by
  induction h₂ with
  | refl => exact h₁
  | tail _ h ih => exact .tail (ih h₁) h

theorem SSteps.head {sig : Sig} {fbip : Bool} {S₁ S₂ S₃ : Store} {e₁ e₂ e₃ : Expr}
    (h₁ : SStep sig fbip S₁ e₁ S₂ e₂) (h₂ : SSteps sig fbip S₂ e₂ S₃ e₃) :
    SSteps sig fbip S₁ e₁ S₃ e₃ := (SSteps.single h₁).trans h₂

theorem SStep.ctx {sig : Sig} {fbip : Bool} {S S' : Store} {e e' : Expr} (E : ECtx)
    (h : SStep sig fbip S e S' e') : SStep sig fbip S (E.plug e) S' (E.plug e') := by
  cases h with
  | head E' h => simpa using SStep.head (E.comp E') h
  | val E' done V rest hd hV h => simpa using SStep.val (E.comp E') done V rest hd hV h

theorem SSteps.ctx {sig : Sig} {fbip : Bool} {S S' : Store} {e e' : Expr} (E : ECtx)
    (h : SSteps sig fbip S e S' e') : SSteps sig fbip S (E.plug e) S' (E.plug e') := by
  induction h with
  | refl => exact .refl _ _
  | tail _ h ih => exact .tail ih (h.ctx E)

theorem SStep.ofHead {sig : Sig} {fbip : Bool} {S S' : Store} {e e' : Expr}
    (h : SHead sig fbip S e S' e') : SStep sig fbip S e S' e' := by
  simpa using SStep.head .hole h

theorem SSteps.cast {sig : Sig} {fbip : Bool} {S T S' T' : Store} {e e' : Expr}
    (h : SSteps sig fbip S e S' e') (hS : S = T) (hS' : S' = T') :
    SSteps sig fbip T e T' e' := hS ▸ hS' ▸ h

/-! ## Value contexts -/

/-- Composition of value contexts. -/
def VCtx.comp : VCtx → VCtx → VCtx
  | .hole, W => W
  | .ctor c d V r, W => .ctor c d (V.comp W) r

@[simp] theorem VCtx.plug_comp (V W : VCtx) (w : Val) : (V.comp W).plug w = V.plug (W.plug w) := by
  induction V with
  | hole => rfl
  | ctor c d V r ih => simp [comp, plug, ih]

theorem VCtx.Ok.comp {V W : VCtx} (hV : V.Ok) (hW : W.Ok) : (V.comp W).Ok := by
  induction V with
  | hole => exact hW
  | ctor c d V r ih => exact ⟨hV.1, ih hV.2⟩

/-! ## Basic facts on variables of values -/

theorem Val.fvList_map_var (ls : List Var) : Val.fvList (ls.map Val.var) = ls := by
  induction ls with
  | nil => rfl
  | cons l ls ih => simp [Val.fvList, Val.fv, ih]

theorem Val.fvList_nil_of (vs : List Val) (h : ∀ v ∈ vs, Val.fv v = []) : Val.fvList vs = [] := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp only [Val.fvList, List.append_eq_nil_iff]
    exact ⟨h v List.mem_cons_self, ih fun w hw => h w (List.mem_cons_of_mem _ hw)⟩

theorem Val.atomic_var (x : Var) : (Val.var x).Atomic := trivial

/-! ## The invariant of the owned part of the store -/

/-- The owned part `S₂` of the store, next to the borrowed part `S₁`, is linear, the whole
    store has the shape of the paper's stores, and `σ` is `[S₁, S₂]`. -/
structure OwnedInv (S₁ S₂ : Store) (σ : Nat → Option Val) : Prop where
  disj : S₁.Disjoint S₂
  lin : S₂.Linear
  ptr : (S₁ + S₂).Ptr
  reads : (S₁ + S₂).Reads σ

theorem Store.dom_le {S T : Store} (hle : T ≤ S) : T.dom ≤ S.dom := by
  obtain ⟨U, rfl⟩ := Multiset.le_iff_exists_add.mp hle
  simp

theorem OwnedInv.mono {S₁ S₂ T : Store} {σ : Nat → Option Val} (h : OwnedInv S₁ S₂ σ)
    (hT : T.Linear) (hle : T ≤ S₂) : OwnedInv S₁ T σ where
  disj := fun x hx hx' => h.disj x hx (Multiset.mem_of_le (Store.dom_le hle) hx')
  lin := hT
  ptr := h.ptr.mono ((add_le_add_iff_left S₁).mpr hle)
  reads := h.reads.mono ((add_le_add_iff_left S₁).mpr hle)

theorem Store.roots_count_var_le_one {S : Store} (h : S.dom.Nodup) (y : Var) :
    (S.roots).count (Res.var y) ≤ 1 := by
  classical
  unfold Store.roots
  rw [Multiset.count_add]
  have h1 : Multiset.count (Res.var y) (S.bind Cell.credits) = 0 := by
    rw [Multiset.count_eq_zero]
    simp only [Multiset.mem_bind, not_exists, not_and]
    intro c _
    cases c with
    | bind => simp [Cell.credits]
    | credit k => by_cases hk : k = 0 <;> simp [Cell.credits, hk]
  rw [h1, add_zero, Multiset.count_map_eq_count' _ _ (fun a b h => by injection h)]
  exact (Multiset.count_le_of_le _ (Multiset.filter_le _ _)).trans
    (Multiset.nodup_iff_count_le_one.mp h y)

theorem Store.nodup_of_roots {S : Store} (h : S.dom.Nodup) {ls : List Var} {X : Ctx}
    (hr : S.roots = (ls.map Res.var : Multiset Res) + X) : ls.Nodup := by
  classical
  have : ((ls.map Res.var : List Res) : Multiset Res).Nodup := by
    rw [Multiset.nodup_iff_count_le_one]
    intro r
    cases r with
    | var y =>
      refine le_trans ?_ (Store.roots_count_var_le_one h y)
      rw [hr, Multiset.count_add]; omega
    | credit k =>
      rw [Multiset.coe_count, List.count_eq_zero.mpr (by simp)]; omega
    | alloc =>
      rw [Multiset.coe_count, List.count_eq_zero.mpr (by simp)]; omega
  exact List.Nodup.of_map _ (Multiset.coe_nodup.mp this)

/-- Update a location substitution at one location. -/
def updLoc (σ : Nat → Option Val) (x : Nat) (w : Val) : Nat → Option Val :=
  fun n => if n = x then some w else σ n

/-- Adding a fresh cell `x ↦ C l₁ … lₖ` whose arguments are roots of the owned part. -/
theorem OwnedInv.add_bind {S₁ T : Store} {σ : Nat → Option Val} (h : OwnedInv S₁ T σ)
    (hS₁ : S₁.Sound) {x : Nat} (hx : Var.loc x ∉ (S₁ + T).dom) (c : CName) {ls : List Var}
    (hls : ∀ l ∈ ls, l ∈ T.dom ∧ l ∉ T.rngFv) (hnd : ls.Nodup) :
    OwnedInv S₁ ({Cell.bind (.loc x) c (ls.map .var)} + T)
      (updLoc σ x (.ctor c ((ls.map Val.var).map (Val.substLoc σ)))) ∧
    Store.roots ({Cell.bind (.loc x) c (ls.map .var)} + T) + (ls.map Res.var : Multiset Res) =
      T.roots + {Res.var (.loc x)} ∧
    (∀ n, Var.loc n ∈ (S₁ + T).dom → updLoc σ x (.ctor c ((ls.map Val.var).map (Val.substLoc σ))) n = σ n) := by
  have hfv := Val.fvList_map_var ls
  have hxT : Var.loc x ∉ T.dom := fun h' => hx (by simp [h'])
  have hxS₁ : Var.loc x ∉ S₁.dom := fun h' => hx (by simp [h'])
  have hxr : Var.loc x ∉ T.rngFv := fun h' => hxT (h.lin.1.2 _ h')
  have hls' : ∀ a ∈ Val.fvList (ls.map Val.var), a ∈ T.dom ∧ a ∉ T.rngFv := by
    rw [hfv]; exact hls
  have hnd' : (Val.fvList (ls.map Val.var)).Nodup := by rw [hfv]; exact hnd
  have hagree : ∀ n, Var.loc n ∈ (S₁ + T).dom →
      updLoc σ x (.ctor c ((ls.map Val.var).map (Val.substLoc σ))) n = σ n := by
    intro n hn
    have : n ≠ x := by rintro rfl; exact hx hn
    simp [updLoc, this]
  -- the arguments are bound, so their values under `σ` are defined
  have hargs : ∀ l ∈ ls, ∃ m, l = .loc m ∧ Var.loc m ∈ T.dom := by
    intro l hl
    obtain ⟨m, rfl⟩ := (h.ptr.mono (Multiset.le_add_left _ _)).dom_loc (hls l hl).1
    exact ⟨m, rfl, (hls _ hl).1⟩
  have hroots := Store.roots_bind (c := c) h.lin.1.1 hxT hxr hls' hnd'
  rw [hfv] at hroots
  refine ⟨⟨?_, Store.linear_bind h.lin hxT hls' hnd', ?_, ⟨?_, ?_⟩⟩, hroots, hagree⟩
  · intro y hy hy'
    rw [Store.dom_bind_add, Multiset.mem_cons] at hy'
    rcases hy' with rfl | hy'
    · exact hxS₁ hy
    · exact h.disj y hy hy'
  · rw [add_left_comm]
    refine Store.Ptr.add ?_ h.ptr
    intro c' hc'
    rw [Multiset.mem_singleton] at hc'
    subst hc'
    refine ⟨⟨x, rfl⟩, fun a ha => ?_⟩
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp ha
    obtain ⟨m, rfl, -⟩ := hargs l hl
    exact ⟨m, rfl⟩
  · intro n w hw
    unfold updLoc at hw
    split at hw
    · cases hw
      simp only [Val.fv]
      refine Val.fvList_nil_of _ fun v hv => ?_
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp ha
      obtain ⟨m, rfl, hm⟩ := hargs l hl
      obtain ⟨c', as', hc'⟩ := Store.mem_dom.mp hm
      have := h.reads.2 m c' as' (Multiset.mem_add.mpr (.inr hc'))
      simp only [Val.substLoc, this, Option.getD_some]
      exact h.reads.1 m _ this
    · exact h.reads.1 n w hw
  · have hsub : ∀ m, m ≠ x → Val.substLoc
        (updLoc σ x (.ctor c ((ls.map Val.var).map (Val.substLoc σ)))) (.var (.loc m)) =
        Val.substLoc σ (.var (.loc m)) := by
      intro m hm; simp [Val.substLoc, updLoc, hm]
    have hs : (S₁ + T).Sound := Store.join_sound hS₁ h.lin.1 h.disj
    intro n c' as' hc'
    rw [add_left_comm, Multiset.mem_add, Multiset.mem_singleton] at hc'
    rcases hc' with hc' | hc'
    · cases hc'
      simp only [updLoc, if_true, Option.some.injEq, Val.ctor.injEq, true_and]
      refine List.map_congr_left fun a ha => ?_
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp ha
      obtain ⟨m, rfl, hm⟩ := hargs l hl
      refine (hsub m ?_).symm
      rintro rfl; exact hxT hm
    · have hn : n ≠ x := by
        rintro rfl; exact hx (Store.mem_dom.mpr ⟨c', as', hc'⟩)
      simp only [updLoc, hn, if_false]
      rw [h.reads.2 n c' as' hc', Option.some.injEq, Val.ctor.injEq]
      refine ⟨rfl, List.map_congr_left fun a ha => ?_⟩
      obtain ⟨m, rfl⟩ := h.ptr.args hc' a ha
      refine (hsub m ?_).symm
      rintro rfl
      apply hx
      refine hs.2 _ (Store.mem_rngFv.mpr ⟨_, c', as', hc', ?_⟩)
      exact Val.mem_fvList.mpr ⟨_, ha, by simp [Val.fv]⟩

/-! ## Allocating values -/

@[simp] theorem Val.substLocList_eq_map (σ : Nat → Option Val) (vs : List Val) :
    Val.substLocList σ vs = vs.map (Val.substLoc σ) := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp [Val.substLocList, ih]

theorem OwnedInv.root_loc {S₁ S₂ : Store} {σ : Nat → Option Val} (h : OwnedInv S₁ S₂ σ)
    {x : Var} (hx : Res.var x ∈ S₂.roots) : ∃ n, x = .loc n ∧ Var.loc n ∈ S₂.dom := by
  have hd := (Store.mem_roots_var.mp hx).1
  obtain ⟨n, rfl⟩ := (h.ptr.mono (Multiset.le_add_left _ _)).dom_loc hd
  exact ⟨n, rfl, hd⟩

/-- Values whose variables are owned roots of `S₂` denote the same under substitutions that
    agree on the store. -/
theorem substLoc_congr_vals {S₁ S₂ : Store} {σ σ' : Nat → Option Val}
    (hag : ∀ n, Var.loc n ∈ (S₁ + S₂).dom → σ' n = σ n) {Γ Γo : Ctx} {vs : List Val}
    (hvs : WfVals ∅ ∅ Γ vs) (hr : S₂.roots = Γ + Γo) :
    vs.map (Val.substLoc σ') = vs.map (Val.substLoc σ) := by
  have := Val.substLocList_congr (σ := σ') (σ' := σ) vs (fun n hn => by
    rcases WfVals.fv_subset hvs _ hn with h1 | h1 | h1
    · simp at h1
    · simp at h1
    · apply hag
      have : Res.var (Var.loc n) ∈ S₂.roots := by rw [hr]; exact Multiset.mem_add.mpr (.inl h1)
      simp [(Store.mem_roots_var.mp this).1])
  simpa using this

mutual
/-- **Allocation of a value**: a well-formed value is allocated in the store, inside any
    evaluation and value context, by consuming exactly its owned resources. -/
theorem alloc_val {sig : Sig} {fbip : Bool} {S₁ : Store} (hS₁ : S₁.Sound) :
    ∀ {Γv : Ctx} {v : Val}, WfVal ∅ ∅ Γv v → v.scalarFree = true →
    ∀ (E : ECtx) (done : List Val) (V : VCtx) (rest : List Val), (∀ a ∈ done, a.Atomic) →
    V.Ok → ∀ (S₂ : Store) (σ : Nat → Option Val) (Γo : Ctx), OwnedInv S₁ S₂ σ →
    S₂.roots = Γv + Γo →
    ∃ (l : Var) (S₂' : Store) (σ' : Nat → Option Val),
      SSteps sig fbip (S₁ + S₂) (E.plug (.ret (done ++ V.plug v :: rest)))
        (S₁ + S₂') (E.plug (.ret (done ++ V.plug (.var l) :: rest))) ∧
      OwnedInv S₁ S₂' σ' ∧ S₂'.roots = {Res.var l} + Γo ∧ S₂.dom ≤ S₂'.dom ∧
      (∀ n, Var.loc n ∈ (S₁ + S₂).dom → σ' n = σ n) ∧
      Val.substLoc σ' (.var l) = Val.substLoc σ v
  | _, _, .var x, _, E, done, V, rest, _, _, S₂, σ, Γo, hinv, hr =>
    ⟨x, S₂, σ, .refl _ _, hinv, hr, le_rfl, fun _ _ => rfl, rfl⟩
  | _, _, .svar x hx, _, _, _, _, _, _, _, _, _, _, _, _ => by simp at hx
  | _, _, .lit n, hsf, _, _, _, _, _, _, _, _, _, _, _ => by simp [Val.scalarFree] at hsf
  | _, _, .atom c, _, E, done, V, rest, hd, hV, S₂, σ, Γo, hinv, hr => by
    obtain ⟨n, hn⟩ := Store.exists_fresh (S₁ + S₂)
    obtain ⟨hinv', hroots, hag⟩ := hinv.add_bind hS₁ hn c (ls := []) (by simp) List.nodup_nil
    refine ⟨.loc n, _, _, ?_, hinv', ?_, ?_, hag, ?_⟩
    · refine SSteps.single ?_
      have := SStep.val (sig := sig) (fbip := fbip) E done V rest hd hV
        (SValHead.atom (S₁ + S₂) c n hn)
      simpa [add_left_comm] using this
    · simp only [List.map_nil, Multiset.coe_nil, add_zero] at hroots ⊢
      rw [hroots, hr, zero_add, add_comm]
    · rw [Store.dom_bind_add]; exact Multiset.le_cons_self _ _
    · simp [Val.substLoc, updLoc]
  | _, _, .reuse c vs Γ hne hvs, hsf, E, done, V, rest, hd, hV, S₂, σ, Γo, hinv, hr => by
    simp only [Val.scalarFree] at hsf
    obtain ⟨ls, S₂₁, σ₁, hs₁, hinv₁, hr₁, hdom₁, hag₁, hden₁⟩ :=
      alloc_vals (sig := sig) (fbip := fbip) hS₁ hvs hsf E done V rest c [] hd hV S₂ σ
        ({Res.credit vs.length} + Γo) hinv (by rw [hr]; abel)
    have hlen : ls.length = vs.length := by simpa using congrArg List.length hden₁
    have hk : Res.credit vs.length ∈ S₂₁.roots := by rw [hr₁]; simp
    obtain ⟨R, rfl⟩ := Store.exists_credit_of_root hk
    have hk0 : vs.length ≠ 0 := by simpa using hne
    have hRr : R.roots = (ls.map Res.var : Multiset Res) + Γo := by
      have := hr₁
      rw [Store.roots_credit] at this
      simp only [Cell.credits, hk0, if_false] at this
      have : R.roots + {Res.credit vs.length} = (ls.map Res.var : Multiset Res) + Γo +
          {Res.credit vs.length} := by rw [this]; abel
      exact add_right_cancel this
    have hinvR : OwnedInv S₁ R σ₁ :=
      hinv₁.mono (Store.linear_of_credit hinv₁.lin) (Multiset.le_add_left _ _)
    obtain ⟨n, hn⟩ := Store.exists_fresh (S₁ + R)
    have hls : ∀ l ∈ ls, l ∈ R.dom ∧ l ∉ R.rngFv := fun l hl =>
      Store.mem_roots_var.mp (by rw [hRr]; simp [hl])
    have hnd : ls.Nodup := Store.nodup_of_roots hinvR.lin.1.1 hRr
    obtain ⟨hinv₂, hroots₂, hag₂⟩ := hinvR.add_bind hS₁ hn c hls hnd
    refine ⟨.loc n, _, _, hs₁.trans (SSteps.single ?_), hinv₂, ?_, ?_, ?_, ?_⟩
    · have hne' : ls.map Val.var ≠ [] := by
        intro h; apply hk0; rw [← hlen]; simpa using h
      have := SStep.val (sig := sig) (fbip := fbip) E done V rest hd hV
        (SValHead.reuse (S₁ + R) c (ls.map .var) n hne' (fun a ha => by
          obtain ⟨l, -, rfl⟩ := List.mem_map.mp ha; trivial) hn)
      simp only [List.length_map, hlen] at this
      simpa [add_left_comm] using this
    · have : Store.roots ({Cell.bind (.loc n) c (ls.map .var)} + R) +
          (ls.map Res.var : Multiset Res) = {Res.var (.loc n)} + Γo +
          (ls.map Res.var : Multiset Res) := by rw [hroots₂, hRr]; abel
      exact add_right_cancel this
    · refine hdom₁.trans ?_
      rw [Store.dom_credit_add, Store.dom_bind_add]; exact Multiset.le_cons_self _ _
    · intro m hm
      rw [hag₂ m (by
        have : (S₁ + S₂).dom ≤ (S₁ + R).dom := by
          rw [Store.dom_credit_add] at hdom₁
          rw [Store.dom_add, Store.dom_add]
          exact (add_le_add_iff_left S₁.dom).mpr hdom₁
        exact Multiset.mem_of_le this hm)]
      exact hag₁ m hm
    · simp only [Val.substLoc, updLoc, if_true, Option.getD_some, Val.substLocList_eq_map,
        List.map_map]
      rw [← hden₁]
      rfl
/-- Allocation of the arguments of a constructor, from left to right. -/
theorem alloc_vals {sig : Sig} {fbip : Bool} {S₁ : Store} (hS₁ : S₁.Sound) :
    ∀ {Γs : Ctx} {vs : List Val}, WfVals ∅ ∅ Γs vs → Val.scalarFreeList vs = true →
    ∀ (E : ECtx) (done : List Val) (V : VCtx) (rest : List Val) (c : CName)
      (doneA : List Var), (∀ a ∈ done, a.Atomic) → V.Ok →
    ∀ (S₂ : Store) (σ : Nat → Option Val) (Γo : Ctx), OwnedInv S₁ S₂ σ →
    S₂.roots = Γs + Γo →
    ∃ (ls : List Var) (S₂' : Store) (σ' : Nat → Option Val),
      SSteps sig fbip (S₁ + S₂)
        (E.plug (.ret (done ++ V.plug (.ctor c (doneA.map .var ++ vs)) :: rest)))
        (S₁ + S₂') (E.plug (.ret (done ++ V.plug (.ctor c (doneA.map .var ++ ls.map .var)) :: rest))) ∧
      OwnedInv S₁ S₂' σ' ∧ S₂'.roots = (ls.map Res.var : Multiset Res) + Γo ∧
      S₂.dom ≤ S₂'.dom ∧ (∀ n, Var.loc n ∈ (S₁ + S₂).dom → σ' n = σ n) ∧
      ls.map (fun l => Val.substLoc σ' (.var l)) = vs.map (Val.substLoc σ)
  | _, _, .nil, _, E, done, V, rest, c, doneA, _, _, S₂, σ, Γo, hinv, hr =>
    ⟨[], S₂, σ, .refl _ _, hinv, by simpa using hr, le_rfl, fun _ _ => rfl, rfl⟩
  | _, _, .cons Γ₁ Γ₂ v vs hv hvs, hsf, E, done, V, rest, c, doneA, hd, hV, S₂, σ, Γo, hinv,
      hr => by
    simp only [Val.scalarFreeList, Bool.and_eq_true] at hsf
    have hV' : (V.comp (.ctor c (doneA.map .var) .hole vs)).Ok :=
      hV.comp ⟨fun a ha => by obtain ⟨l, -, rfl⟩ := List.mem_map.mp ha; trivial, trivial⟩
    obtain ⟨l, S₂₁, σ₁, hs₁, hinv₁, hr₁, hdom₁, hag₁, hden₁⟩ :=
      alloc_val (sig := sig) (fbip := fbip) hS₁ hv hsf.1 E done _ rest hd hV' S₂ σ (Γ₂ + Γo)
        hinv (by rw [hr]; abel)
    obtain ⟨ls, S₂₂, σ₂, hs₂, hinv₂, hr₂, hdom₂, hag₂, hden₂⟩ :=
      alloc_vals (sig := sig) (fbip := fbip) hS₁ hvs hsf.2 E done V rest c (doneA ++ [l]) hd hV
        S₂₁ σ₁ ({Res.var l} + Γo) hinv₁ (by rw [hr₁]; abel)
    refine ⟨l :: ls, S₂₂, σ₂, ?_, hinv₂, ?_, hdom₁.trans hdom₂, ?_, ?_⟩
    · simp only [VCtx.plug_comp, VCtx.plug] at hs₁
      simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc,
        List.singleton_append] at hs₂
      simpa using hs₁.trans hs₂
    · rw [hr₂]; simp only [List.map_cons]
      rw [← Multiset.cons_coe, ← Multiset.singleton_add]; abel
    · intro n hn
      rw [hag₂ n (by
        have : (S₁ + S₂).dom ≤ (S₁ + S₂₁).dom := by simpa using add_le_add_left hdom₁ S₁.dom
        exact Multiset.mem_of_le this hn)]
      exact hag₁ n hn
    · have hl : Res.var l ∈ S₂₁.roots := by rw [hr₁]; simp
      obtain ⟨m, rfl, hm⟩ := hinv₁.root_loc hl
      simp only [List.map_cons, List.cons.injEq]
      refine ⟨?_, ?_⟩
      · rw [← hden₁]
        simp only [Val.substLoc]
        rw [hag₂ m (by simp [hm])]
      · rw [hden₂]
        exact substLoc_congr_vals hag₁ hvs (Γo := Γ₁ + Γo) (by rw [hr]; abel)
end

/-- **Allocation of an unboxed tuple** of well-formed values. -/
theorem alloc_tuple {sig : Sig} {fbip : Bool} {S₁ : Store} (hS₁ : S₁.Sound) :
    ∀ {Γs : Ctx} {vs : List Val}, WfVals ∅ ∅ Γs vs → Val.scalarFreeList vs = true →
    ∀ (doneT : List Var) (S₂ : Store) (σ : Nat → Option Val) (Γo : Ctx),
    OwnedInv S₁ S₂ σ → S₂.roots = Γs + Γo →
    ∃ (ls : List Var) (S₂' : Store) (σ' : Nat → Option Val),
      SSteps sig fbip (S₁ + S₂) (.ret (doneT.map .var ++ vs))
        (S₁ + S₂') (.ret (doneT.map .var ++ ls.map .var)) ∧
      OwnedInv S₁ S₂' σ' ∧ S₂'.roots = (ls.map Res.var : Multiset Res) + Γo ∧
      S₂.dom ≤ S₂'.dom ∧ (∀ n, Var.loc n ∈ (S₁ + S₂).dom → σ' n = σ n) ∧
      ls.map (fun l => Val.substLoc σ' (.var l)) = vs.map (Val.substLoc σ)
  | _, _, .nil, _, doneT, S₂, σ, Γo, hinv, hr =>
    ⟨[], S₂, σ, .refl _ _, hinv, by simpa using hr, le_rfl, fun _ _ => rfl, rfl⟩
  | _, _, .cons Γ₁ Γ₂ v vs hv hvs, hsf, doneT, S₂, σ, Γo, hinv, hr => by
    simp only [Val.scalarFreeList, Bool.and_eq_true] at hsf
    obtain ⟨l, S₂₁, σ₁, hs₁, hinv₁, hr₁, hdom₁, hag₁, hden₁⟩ :=
      alloc_val (sig := sig) (fbip := fbip) hS₁ hv hsf.1 .hole (doneT.map .var) .hole vs
        (fun a ha => by obtain ⟨l, -, rfl⟩ := List.mem_map.mp ha; trivial) trivial S₂ σ
        (Γ₂ + Γo) hinv (by rw [hr]; abel)
    obtain ⟨ls, S₂₂, σ₂, hs₂, hinv₂, hr₂, hdom₂, hag₂, hden₂⟩ :=
      alloc_tuple (sig := sig) (fbip := fbip) hS₁ hvs hsf.2 (doneT ++ [l]) S₂₁ σ₁
        ({Res.var l} + Γo) hinv₁ (by rw [hr₁]; abel)
    refine ⟨l :: ls, S₂₂, σ₂, ?_, hinv₂, ?_, hdom₁.trans hdom₂, ?_, ?_⟩
    · simp only [ECtx.plug, VCtx.plug] at hs₁
      simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc,
        List.singleton_append] at hs₂
      simpa using hs₁.trans hs₂
    · rw [hr₂]; simp only [List.map_cons]
      rw [← Multiset.cons_coe, ← Multiset.singleton_add]; abel
    · intro n hn
      rw [hag₂ n (by
        have : (S₁ + S₂).dom ≤ (S₁ + S₂₁).dom := by simpa using add_le_add_left hdom₁ S₁.dom
        exact Multiset.mem_of_le this hn)]
      exact hag₁ n hn
    · have hl : Res.var l ∈ S₂₁.roots := by rw [hr₁]; simp
      obtain ⟨m, rfl, hm⟩ := hinv₁.root_loc hl
      simp only [List.map_cons, List.cons.injEq]
      refine ⟨?_, ?_⟩
      · rw [← hden₁]
        simp only [Val.substLoc]
        rw [hag₂ m (by simp [hm])]
      · rw [hden₂]
        exact substLoc_congr_vals hag₁ hvs (Γo := Γ₁ + Γo) (by rw [hr]; abel)


/-! ## Dropping trees (FBIP) -/

theorem drops_append (l1 l2 : List Val) (e : Expr) : drops (l1 ++ l2) e = drops l1 (drops l2 e) := by
  induction l1 with
  | nil => rfl
  | cons a l1 ih => cases a <;> simp [drops, ih]

/-- **Dropping trees**: `drop z₁; …; drop zₖ; e` deallocates the trees rooted at the owned
    roots `z₁ … zₖ` (rule *dcon* of Fig. 6). -/
theorem drop_tree {sig : Sig} {S₁ : Store} (e : Expr) :
    ∀ (n : Nat) (T : Store), Multiset.card T = n → ∀ (zs : List Var) (σ : Nat → Option Val)
    (X : Ctx), OwnedInv S₁ T σ → T.roots = (zs.map Res.var : Multiset Res) + X →
    ∃ T', SSteps sig true (S₁ + T) (drops (zs.map .var) e) (S₁ + T') e ∧ T' ≤ T ∧
      T'.Linear ∧ T'.roots = X := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro T hT zs σ X hinv hr
    cases zs with
    | nil => exact ⟨T, .refl _ _, le_rfl, hinv.lin, by simpa using hr⟩
    | cons z zs =>
      have hz : Res.var z ∈ T.roots := by rw [hr]; simp
      obtain ⟨c, as, R, rfl⟩ := Store.exists_cell_of_root hz
      have hzr : z ∉ Store.rngFv ({Cell.bind z c as} + R) := (Store.mem_roots_var.mp hz).2
      obtain ⟨hR, -, -, -, -⟩ := Store.remove_root hinv.lin hzr
      have hroots := Store.roots_remove_root hinv.lin hzr
      have has := (hinv.ptr.mono (Multiset.le_add_left _ _)).args_vars
        (Multiset.mem_add.mpr (.inl (Multiset.mem_singleton_self _)))
      set asv := Val.fvList as with hasv
      have hRr : R.roots = ((asv ++ zs).map Res.var : Multiset Res) + X := by
        rw [hr] at hroots
        have : R.roots + {Res.var z} = ((asv ++ zs).map Res.var : Multiset Res) + X +
            {Res.var z} := by
          rw [← hroots]
          simp only [List.map_cons, List.map_append, ← Multiset.coe_add]
          rw [← Multiset.cons_coe, ← Multiset.singleton_add]; abel
        exact add_right_cancel this
      have hinvR : OwnedInv S₁ R σ := hinv.mono hR (Multiset.le_add_left _ _)
      obtain ⟨T', hs, hle, hlin, hr'⟩ :=
        ih (Multiset.card R) (by rw [← hT]; simp) R rfl (asv ++ zs) σ X hinvR hRr
      refine ⟨T', SSteps.head ?_ hs, hle.trans (Multiset.le_add_left _ _), hlin, hr'⟩
      have := SStep.ofHead (SHead.drop (sig := sig) (S₁ + R) z c as (drops (zs.map .var) e) rfl)
      rw [List.map_append, drops_append, ← has]
      simpa [drops, add_left_comm] using this

end FIP
