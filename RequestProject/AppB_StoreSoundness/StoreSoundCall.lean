module

public import RequestProject.AppB_StoreSoundness.StoreSoundAux

@[expose] public section

/-!
# Binders and function calls in the proof of Theorem 1

Extending the substitution `ρ` under the binders of a `let` or a branch, and evaluating the
body of a called function in the borrowed store `S₁` and the owned store holding exactly
its owned arguments.
-/

namespace FIP

variable {sig : Sig} {fbip : Bool}

/-! ## Branches -/

theorem Branches.scalarFree_mem {n : Nat} : ∀ {bs : Branches n}, bs.scalarFree = true →
    ∀ {b : Branch n}, b ∈ bs.toList → b.binders.all (!·) = true ∧ b.body.scalarFree = true
  | .nil, _, _, hb => by simp at hb
  | .cons c xs e bs, h, b, hb => by
    simp only [Branches.scalarFree, Bool.and_eq_true] at h
    rw [Branches.toList_cons] at hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨h.1.1, h.1.2⟩
    · exact Branches.scalarFree_mem h.2 hb

/-! ## Substituting locations in an extended substitution -/

theorem List.getD_map_substLoc {m : Nat} (σ : Nat → Option (Val 0)) (ws : List (Val m))
    (i : Nat) : (ws.getD i default).substLoc σ = (ws.map (Val.substLoc σ)).getD i default := by
  by_cases h : i < ws.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by simp; omega)]
    rfl

theorem Subst.inst_substLoc {n m : Nat} (σ : Nat → Option (Val 0)) (k : Nat) (ws : List (Val m))
    (ρ : Fin n → Val m) (i : Fin (n + k)) :
    (Subst.inst k ws ρ i).substLoc σ =
      Subst.inst k (ws.map (Val.substLoc σ)) (fun j => (ρ j).substLoc σ) i := by
  unfold Subst.inst
  split
  · exact List.getD_map_substLoc σ ws _
  · rfl

theorem Subst.ofList_substLoc {m : Nat} (σ : Nat → Option (Val 0)) (k : Nat) (ws : List (Val m))
    (i : Fin k) :
    (Subst.ofList k ws i).substLoc σ = Subst.ofList k (ws.map (Val.substLoc σ)) i :=
  List.getD_map_substLoc σ ws _

/-- Substituting under the binders of a body, substituting locations and instantiating the
    binders, is substituting with the extended substitution and then substituting
    locations. -/
theorem body_subst_eq {m k : Nat} (σ : Nat → Option (Val 0)) (ρ : Fin m → Val 0)
    (ws : List (Val 0)) (body : Expr (m + k)) :
    ((body.subst (Subst.up k ρ)).substLoc σ).inst (ws.map (Val.substLoc σ)) =
      (body.subst (Subst.inst k ws ρ)).substLoc σ := by
  rw [Expr.substLoc_subst σ (Subst.up k ρ), Expr.substLoc_subst σ (Subst.inst k ws ρ),
    Expr.subst_congr (Subst.up_substLoc σ k ρ), Expr.subst_up_inst,
    Expr.subst_congr (Subst.inst_substLoc σ k ws ρ)]

/-! ## Atomic substitutions -/

theorem Subst.Atomic.ofList {k : Nat} {ws : List (Val 0)} (hl : ws.length = k)
    (hws : ∀ w ∈ ws, (∃ l, w = .var (.loc l)) ∨ ∃ g, w = .fn g) :
    Subst.Atomic (Subst.ofList k ws) := by
  intro i
  simp only [Subst.ofList]
  rw [List.getD_eq_getElem _ _ (by omega)]
  exact hws _ (List.getElem_mem _)

theorem Subst.Atomic.inst_locs {m : Nat} {ρ : Fin m → Val 0} (h : Subst.Atomic ρ) {k : Nat}
    {ls : List (Var 0)} (hl : ls.length = k) (hls : ∀ y ∈ ls, ∃ l, y = .loc l) :
    Subst.Atomic (Subst.inst k (ls.map .var) ρ) :=
  h.inst (by simp [hl]) fun w hw => by
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hw
    obtain ⟨l, rfl⟩ := hls y hy
    exact .inl ⟨l, rfl⟩

/-! ## Borrowed and owned variables under binders -/

theorem Borrowed.inst {m : Nat} {S₁ : Store} {ρ : Fin m → Val 0} {x : Var m}
    (h : Borrowed sig S₁ ρ x) (k : Nat) (ws : List (Val 0)) :
    Borrowed sig S₁ (Subst.inst k ws ρ) (x.shift k) := by
  unfold Borrowed at *
  rw [Val.subst_inst_shift]
  exact h

theorem Borrowed.shift_set {m : Nat} {S₁ : Store} {ρ : Fin m → Val 0} {Δ : Finset (Var m)}
    (h : ∀ x ∈ Δ, Borrowed sig S₁ ρ x) (k : Nat) (ws : List (Val 0)) :
    ∀ x ∈ Vars.shift k Δ, Borrowed sig S₁ (Subst.inst k ws ρ) x := by
  intro x hx
  obtain ⟨x0, hx0, rfl⟩ := Vars.mem_shift_iff.mp hx
  exact (h x0 hx0).inst k ws

theorem Ctx.exists_of_mem_shift_var {n k : Nat} {Γ : Ctx n} {y : Var (n + k)}
    (h : Res.var y ∈ Γ.shift k) : ∃ y0, Res.var y0 ∈ Γ ∧ y0.shift k = y := by
  obtain ⟨r, hr, he⟩ := Ctx.mem_shift_iff.mp h
  cases r with
  | var y0 => exact ⟨y0, hr, by simpa [Res.shift] using he⟩
  | credit j => simp [Res.shift] at he
  | alloc => simp [Res.shift] at he

theorem Binder.ownedAt_substR {N : Nat} {ρ : Fin N → Val 0} {xs : List Bool}
    (hall : xs.all (!·) = true) (f : Fin xs.length → Var N) {ls : List (Var 0)}
    (hl : xs.length = ls.length)
    (hf : ∀ j : Fin xs.length, Val.subst ρ (.var (f j)) = .var (ls[j.val]'(hl ▸ j.isLt))) :
    (Binder.ownedAt xs f).map (Res.substR ρ) =
      ((ls.map Res.var : List (Res 0)) : Multiset (Res 0)) := by
  rw [Binder.ownedAt, Binder.select_false_of_all hall, Multiset.map_coe, List.map_map,
    List.map_map]
  congr 1
  apply List.ext_getElem (by simp [hl])
  intro i h1 h2
  simp only [List.length_map, List.length_finRange] at h1
  simp only [List.getElem_map, Function.comp, List.getElem_finRange]
  rw [Res.substR_var (hf _)]
  rfl

/-- The owned environment, seen under `k` new binders. -/
theorem Owned.shift {m : Nat} {ρ : Fin m → Val 0} {Γ : Ctx m} {T : Store} (h : Owned ρ Γ T)
    (k : Nat) (ws : List (Val 0)) : Owned (Subst.inst k ws ρ) (Γ.shift k) T := by
  refine ⟨fun y hy => ?_, ?_⟩
  · obtain ⟨y0, hy0, rfl⟩ := Ctx.exists_of_mem_shift_var hy
    rw [Val.subst_inst_shift]
    exact h.var y0 hy0
  · rw [Ctx.shift_substR]; exact h.roots

/-- The owned environment extended by the owned variables bound to locations `ls`. -/
theorem Owned.inst {m : Nat} {ρ : Fin m → Val 0} {Γ : Ctx m} {T : Store} (h : Owned ρ Γ T)
    {xs : List Bool} (hall : xs.all (!·) = true) {ls : List (Var 0)} (hl : xs.length = ls.length)
    (hls : ∀ y ∈ ls, ∃ l, y = .loc l) {T' : Store}
    (hT' : T'.roots = T.roots + ((ls.map Res.var : List (Res 0)) : Multiset (Res 0))) :
    Owned (Subst.inst xs.length (ls.map .var) ρ) (Γ.shift xs.length + Binder.owned xs) T' := by
  refine ⟨fun y hy => ?_, ?_⟩
  · rcases Multiset.mem_add.mp hy with hy | hy
    · exact (h.shift _ _).var y hy
    · obtain ⟨j, -, rfl⟩ := Binder.mem_select.mp (Binder.mem_ownedAt_var.mp hy)
      rw [Val.subst_inst_newB ρ (by simp [hl])]
      simp only [List.getElem_map]
      obtain ⟨l, hl'⟩ := hls _ (List.getElem_mem _)
      exact ⟨l, by rw [hl']⟩
  · rw [Multiset.map_add, Ctx.nz_add, Ctx.shift_substR, h.roots, Binder.owned_substR hall hl,
      Ctx.nz_vars, hT']

/-- A non-scalar binder of a branch of a borrowing match is bound to a field. -/
theorem Binder.subst_ownedSet {m : Nat} {ρ : Fin m → Val 0} {xs : List Bool} {ws : List (Val 0)}
    (hl : xs.length = ws.length) {x : Var (m + xs.length)} (hx : x ∈ Binder.ownedSet xs) :
    ∃ w ∈ ws, Val.subst (Subst.inst xs.length ws ρ) (.var x) = w := by
  simp only [Binder.ownedSet, Binder.ownedSetAt, List.mem_toFinset] at hx
  obtain ⟨j, -, rfl⟩ := Binder.mem_select.mp hx
  exact ⟨_, List.getElem_mem _, Val.subst_inst_newB ρ hl.symm j⟩

/-! ## Locations of a body under binders -/

theorem locs_subst_up {cfg : Cfg} {m k : Nat} {U Δ : Finset (Var (m + k))} {Γ : Ctx (m + k)}
    {e : Expr (m + k)} (h : Wf cfg U Δ Γ e) (hU : U = ∅) {ρ : Fin m → Val 0} {D : Nat → Prop}
    (hΔ : ∀ x0 : Var m, x0.shift k ∈ Δ → ∀ l, Var.loc l ∈ Val.fv (Val.subst ρ (.var x0)) → D l)
    (hΓ : ∀ x0 : Var m, Res.var (x0.shift k) ∈ Γ →
      ∀ l, Var.loc l ∈ Val.fv (Val.subst ρ (.var x0)) → D l)
    (l : Nat) (hl : Var.loc l ∈ (e.subst (Subst.up k ρ)).fv) : D l := by
  obtain ⟨x, hx, hl'⟩ := Expr.fv_subst (Subst.up k ρ) (.loc l) e hl
  have hav := Wf.fv_subset h x hx
  subst hU
  obtain ⟨x0, rfl, hx0⟩ : ∃ x0 : Var m, x = x0.shift k ∧
      Var.loc l ∈ Val.fv (Val.subst ρ (.var x0)) := by
    cases x with
    | loc l' =>
      simp only [Val.subst_loc, Val.fv, List.mem_singleton, Var.loc.injEq] at hl'
      subst hl'
      exact ⟨.loc l, rfl, by simp [Val.fv]⟩
    | bvar i =>
      simp only [Val.subst_bvar, Subst.up] at hl'
      split at hl'
      · simp [Val.fv] at hl'
      · rename_i hi
        rw [Val.fv_shift, List.mem_map] at hl'
        obtain ⟨y, hy, hye⟩ := hl'
        cases y with
        | bvar j => simp [Var.shift] at hye
        | loc l' =>
          simp only [Var.shift, Var.loc.injEq] at hye
          subst hye
          refine ⟨.bvar ⟨i - k, by omega⟩, ?_, hy⟩
          simp only [Var.shift, Var.bvar.injEq]
          ext; simp; omega
  rcases hav with h1 | h1 | h1
  · simp at h1
  · exact hΔ x0 h1 l hx0
  · exact hΓ x0 h1 l hx0

/-! ## Miscellaneous -/

theorem OwnedInv.swap_credit {S₁ R : Store} {σ : Nat → Option (Val 0)} {x : Var 0} {c : CName}
    {as : List (Val 0)} (h : OwnedInv S₁ ({Cell.bind x c as} + R) σ) (hR : R.Linear) (k : Nat) :
    OwnedInv S₁ ({Cell.credit k} + R) σ where
  disj := fun y hy hy' => h.disj y hy (by rw [Store.dom_credit_add] at hy'; simp [hy'])
  lin := Store.linear_credit k hR
  ptr := by
    intro cell hc
    rcases Multiset.mem_add.mp hc with hc | hc
    · exact h.ptr cell (Multiset.mem_add.mpr (.inl hc))
    rcases Multiset.mem_add.mp hc with hc | hc
    · rw [Multiset.mem_singleton] at hc; subst hc; trivial
    · exact h.ptr cell (by simp [hc])
  reads := by
    refine ⟨h.reads.1, fun n c' as' hc => h.reads.2 n c' as' ?_⟩
    rcases Multiset.mem_add.mp hc with hc | hc
    · exact Multiset.mem_add.mpr (.inl hc)
    rcases Multiset.mem_add.mp hc with hc | hc
    · simp at hc
    · simp [hc]

theorem Ctx.mem_vars {m : Nat} {Γ : Ctx m} {x : Var m} : x ∈ Γ.vars ↔ Res.var x ∈ Γ := by
  simp only [Ctx.vars, Multiset.mem_filterMap]
  constructor
  · rintro ⟨r, hr, h⟩
    cases r with
    | var y => simp at h; subst h; exact hr
    | _ => simp at h
  · intro h; exact ⟨_, h, rfl⟩

theorem Owned.mem_roots {m : Nat} {ρ : Fin m → Val 0} {Γ : Ctx m} {S : Store} (h : Owned ρ Γ S)
    {x : Var m} (hx : Res.var x ∈ Γ) :
    ∃ l, Val.subst ρ (.var x) = .var (.loc l) ∧ Res.var (.loc l) ∈ S.roots := by
  obtain ⟨l, hl⟩ := h.var x hx
  refine ⟨l, hl, ?_⟩
  rw [← h.roots, Ctx.nz, Multiset.mem_filter]
  exact ⟨Multiset.mem_map.mpr ⟨_, hx, Res.substR_var hl⟩, by simp⟩

theorem Sig.lookup_mem {g : FName} {fd : FunDef} (h : sig.lookup g = some fd) :
    fd ∈ sig ∧ fd.name = g := by
  unfold Sig.lookup at h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

theorem Sig.lookup_of_mem (hn : (sig.map (·.name)).Nodup) {fd : FunDef} (h : fd ∈ sig) :
    sig.lookup fd.name = some fd := by
  induction sig with
  | nil => simp at h
  | cons fd' sig ih =>
    simp only [List.map_cons, List.nodup_cons] at hn
    unfold Sig.lookup at ih ⊢
    rw [List.find?_cons]
    by_cases heq : fd'.name = fd.name
    · simp only [heq, beq_self_eq_true]
      rcases List.mem_cons.mp h with rfl | h
      · rfl
      · exact absurd (heq ▸ List.mem_map_of_mem h) hn.1
    · have : (fd'.name == fd.name) = false := by simpa using heq
      simp only [this]
      rcases List.mem_cons.mp h with rfl | h
      · exact absurd rfl heq
      · exact ih hn.2 h

theorem Annot.ne_plain_of_callable {a b : Annot} (h : (b.isFip || (a.isFbip && b.isFbip)) = true) :
    b ≠ .plain := by
  rintro rfl; simp [Annot.isFip, Annot.isFbip] at h

theorem cfg_compatible (hsig : sig.PaperFragment)
    (hfb : ∀ fd ∈ sig, fd.annot.isFbip = true → fbip = true) {fd : FunDef} (hfd : fd ∈ sig) :
    (sig.cfg fd.annot).Compatible sig fbip := by
  refine ⟨?_, ?_, ?_, hfb⟩
  · intro g hg
    simp only [Sig.cfg, Sig.callable, List.mem_map, List.mem_filter] at hg
    obtain ⟨fd', ⟨hfd', hp⟩, rfl⟩ := hg
    exact ⟨fd', Sig.lookup_of_mem hsig.names hfd', Annot.ne_plain_of_callable hp⟩
  · intro g
    simp only [Sig.cfg]
    cases hl : sig.lookup g with
    | none => rfl
    | some fd' => simpa using hsig.noBudget fd' (Sig.lookup_mem hl).1
  · intro h
    exact hfb fd hfd h

/-! ## Function bodies -/

theorem body_noLoc (hsig : sig.PaperFragment) {fd : FunDef} (hfd : fd ∈ sig)
    (hann : fd.annot ≠ .plain) : NoLoc fd.body.fv := by
  intro k hk
  have := Wf.fv_subset (hsig.wf fd hfd hann) _ hk
  simp [Avail, FunDef.scalars, FunDef.borrowedSet, FunDef.ownedCtx, Binder.scalarsAt,
    Binder.ownedSetAt, Binder.ownedAt, Binder.select, FunDef.bParam, FunDef.oParam,
    Multiset.mem_replicate] at this

theorem body_substLoc {N m : Nat} (σ : Nat → Option (Val 0)) {body : Expr N}
    (hnl : NoLoc body.fv) (τ : Fin N → Val m) :
    (body.subst τ).substLoc σ = body.subst (fun i => (τ i).substLoc σ) := by
  rw [Expr.substLoc_subst, Expr.substLoc_of_noLoc σ body hnl]

theorem FunDef.argSubst_substLoc (fd : FunDef) (σ : Nat → Option (Val 0)) {m : Nat}
    (vs1 vs2 : List (Val m)) (i : Fin (fd.owned.length + fd.borrowed.length)) :
    (fd.argSubst vs1 vs2 i).substLoc σ =
      fd.argSubst (vs1.map (Val.substLoc σ)) (vs2.map (Val.substLoc σ)) i := by
  unfold FunDef.argSubst
  rw [Subst.inst_substLoc]
  congr 1
  funext j
  exact Subst.ofList_substLoc σ _ vs2 j

theorem FunDef.instBody_substLoc (hsig : sig.PaperFragment) {fd : FunDef} (hfd : fd ∈ sig)
    (hann : fd.annot ≠ .plain) (σ : Nat → Option (Val 0)) (vs1 vs2 : List (Val 0)) :
    (fd.instBody vs1 vs2).substLoc σ =
      fd.instBody (vs1.map (Val.substLoc σ)) (vs2.map (Val.substLoc σ)) := by
  unfold FunDef.instBody
  rw [body_substLoc σ (body_noLoc hsig hfd hann)]
  exact Expr.subst_congr (fd.argSubst_substLoc σ vs1 vs2) _

theorem FunDef.argSubst_bParam {m : Nat} (fd : FunDef) (vs1 vs2 : List (Val m))
    (hl : fd.borrowed.length = vs1.length) (j : Fin fd.borrowed.length) :
    Val.subst (fd.argSubst vs1 vs2) (.var (fd.bParam j)) = vs1[j.val]'(hl ▸ j.isLt) := by
  simp only [FunDef.bParam, Val.subst_bvar, FunDef.argSubst]
  rw [Subst.inst_lt _ _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp; omega)]

theorem FunDef.argSubst_oParam {m : Nat} (fd : FunDef) (vs1 vs2 : List (Val m))
    (hl : fd.owned.length = vs2.length) (i : Fin fd.owned.length) :
    Val.subst (fd.argSubst vs1 vs2) (.var (fd.oParam i)) = vs2[i.val]'(hl ▸ i.isLt) := by
  simp only [FunDef.oParam, Val.subst_bvar, FunDef.argSubst]
  rw [Subst.inst_ge _ _ _ _ (by simp)]
  simp only [Subst.ofList, Nat.add_sub_cancel_left]
  rw [List.getD_eq_getElem _ _ (by omega)]

/-- The argument of a borrowed parameter: a location of the borrowed store or an annotated
    top-level function. -/
def BorrowedVal (sig : Sig) (S₁ : Store) (a : Val 0) : Prop :=
  (∃ l, a = .var (.loc l) ∧ Var.loc l ∈ S₁.dom) ∨
    (∃ g fd, a = .fn g ∧ sig.lookup g = some fd ∧ fd.annot ≠ .plain)

theorem BorrowedVal.atomic {S₁ : Store} {a : Val 0} (h : BorrowedVal sig S₁ a) : a.Atomic := by
  rcases h with ⟨l, rfl, -⟩ | ⟨g, -, rfl, -⟩ <;> trivial

theorem BorrowedVal.substLoc {S₁ : Store} {a : Val 0} (h : BorrowedVal sig S₁ a)
    {σ σ' : Nat → Option (Val 0)} (hag : ∀ n, Var.loc n ∈ S₁.dom → σ' n = σ n) :
    Val.substLoc σ' a = Val.substLoc σ a := by
  rcases h with ⟨l, rfl, hl⟩ | ⟨g, -, rfl, -⟩
  · simp [hag l hl]
  · rfl

/-- **The body of a called function** satisfies the conclusion of Theorem 1. -/
theorem call_body (hsig : sig.PaperFragment)
    (hfb : ∀ fd ∈ sig, fd.annot.isFbip = true → fbip = true) {n2 : Nat}
    (IH2 : MainClaim sig fbip n2) {g : FName} {fd : FunDef} (hg : sig.lookup g = some fd)
    (hann : fd.annot ≠ .plain) {S₁ S₃ : Store} {σ₃ : Nat → Option (Val 0)} {as1 : List (Val 0)}
    (has1 : ∀ a ∈ as1, BorrowedVal sig S₁ a) {xs₁ : List (Var 0)}
    (hr3 : S₃.roots = (xs₁.map Res.var : Multiset (Res 0))) (hinv3 : OwnedInv S₁ S₃ σ₃)
    (hS₁ : S₁.Sound) (hl1 : fd.borrowed.length = as1.length) (hl2 : fd.owned.length = xs₁.length)
    {vs : List (Val 0)}
    (hev : StepsN sig n2 ((fd.instBody as1 (xs₁.map .var)).substLoc σ₃) (.ret vs)) :
    StoreResult sig fbip S₁ S₃ (fd.instBody as1 (xs₁.map .var)) σ₃ vs := by
  have hfd := (Sig.lookup_mem hg).1
  have hwf := hsig.wf fd hfd hann
  obtain ⟨hall, hsfb⟩ := hsig.scalarFree fd hfd
  have hb0 := hsig.noBudget fd hfd
  rw [List.all_append, Bool.and_eq_true] at hall
  obtain ⟨hallb, hallo⟩ := hall
  have hl2' : fd.owned.length = (xs₁.map Val.var).length := by simp [hl2]
  have hlocs : ∀ y ∈ xs₁, ∃ k, y = .loc k := by
    intro y hy
    obtain ⟨k, rfl, -⟩ := hinv3.root_loc (x := y) (by rw [hr3]; simp [hy])
    exact ⟨k, rfl⟩
  have hρ : Subst.Atomic (fd.argSubst as1 (xs₁.map .var)) := by
    refine Subst.Atomic.inst (Subst.Atomic.ofList hl2'.symm ?_) hl1.symm ?_
    · intro v hv
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hv
      obtain ⟨k, rfl⟩ := hlocs y hy
      exact .inl ⟨k, rfl⟩
    · intro v hv
      rcases has1 v hv with ⟨l, rfl, -⟩ | ⟨g', -, rfl, -⟩
      · exact .inl ⟨l, rfl⟩
      · exact .inr ⟨g', rfl⟩
  have hΔ : ∀ x ∈ fd.borrowedSet, Borrowed sig S₁ (fd.argSubst as1 (xs₁.map .var)) x := by
    intro x hx
    simp only [FunDef.borrowedSet, Binder.ownedSetAt, List.mem_toFinset] at hx
    obtain ⟨j, -, rfl⟩ := Binder.mem_select.mp hx
    unfold Borrowed
    rw [FunDef.argSubst_bParam _ _ _ hl1]
    rcases has1 _ (List.getElem_mem _) with ⟨l, hl, hlS⟩ | ⟨g', fd', hg', hl', hann'⟩
    · exact .inl ⟨l, hl, hlS⟩
    · exact .inr ⟨g', fd', hg', hl', hann'⟩
  have hΓ : Owned (fd.argSubst as1 (xs₁.map .var)) fd.ownedCtx S₃ := by
    have hctx : fd.ownedCtx = Binder.ownedAt fd.owned fd.oParam := by
      simp [FunDef.ownedCtx, hb0]
    rw [hctx]
    refine ⟨fun y hy => ?_, ?_⟩
    · obtain ⟨i, -, rfl⟩ := Binder.mem_select.mp (Binder.mem_ownedAt_var.mp hy)
      rw [FunDef.argSubst_oParam _ _ _ hl2']
      simp only [List.getElem_map]
      obtain ⟨k, hk⟩ := hlocs _ (List.getElem_mem _)
      exact ⟨k, by rw [hk]⟩
    · rw [Binder.ownedAt_substR hallo _ hl2
        (fun i => by rw [FunDef.argSubst_oParam _ _ _ hl2']; simp), Ctx.nz_vars, hr3]
  have hU : fd.scalars = ∅ := by
    simp [FunDef.scalars, Binder.scalarsAt, Binder.select_true_of_all hallb,
      Binder.select_true_of_all hallo]
  exact IH2 (cfg_compatible hsig hfb hfd) hU hsfb hwf hρ hΔ hΓ hS₁ hinv3 hev

end FIP
