module

public import RequestProject.Named.AppB_StoreSoundness.StoreSoundAux

@[expose] public section

/-!
# Function calls in the proof of Theorem 1

The body of a called function is evaluated in the borrowed store `S₁` and the owned store
holding exactly its owned arguments.
-/

namespace FIPNamed

variable {sig : Sig} {fbip : Bool}

/-! ## Helpers for matches -/

theorem findBranch_subst_inv {σ : Nat → Option Val} {ρ : Subst} {bs : List Branch} {c c' : CName}
    {k : Nat} {xs : List Binder} {e' : Expr}
    (h : findBranch (Expr.substLocB σ (Expr.substBranches ρ bs)) c k = some (.mk c' xs e')) :
    ∃ body, findBranch bs c k = some (.mk c' xs body) ∧
      e' = (body.subst (ρ.remove xs)).substLoc σ := by
  rw [findBranch_substLocB, findBranch_substBranches] at h
  cases hb : findBranch bs c k with
  | none => rw [hb] at h; simp at h
  | some b =>
    rw [hb] at h
    obtain ⟨c0, xs0, body⟩ := b
    simp only [Option.map_some, Option.some.injEq, Branch.mk.injEq, Branch.ctor, Branch.binders,
      Branch.body] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨body, rfl, rfl⟩

theorem findBranch_subst_some {ρ : Subst} {bs : List Branch} {c c' : CName} {k : Nat}
    {xs : List Binder} {body : Expr} (h : findBranch bs c k = some (.mk c' xs body)) :
    findBranch (Expr.substBranches ρ bs) c k = some (.mk c' xs (body.subst (ρ.remove xs))) := by
  rw [findBranch_substBranches, h]; rfl

theorem Expr.scalarFreeB_mem {bs : List Branch} (h : Expr.scalarFreeB bs = true) {b : Branch}
    (hb : b ∈ bs) : b.binders.all (!·.scalar) = true ∧ b.body.scalarFree = true := by
  induction bs with
  | nil => simp at hb
  | cons b' bs ih =>
    obtain ⟨c, xs, e⟩ := b'
    simp only [Expr.scalarFreeB, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨h.1.1, h.1.2⟩
    · exact ih h.2 hb

theorem body_subst_eq {σ : Nat → Option Val} (hσ : LocClosed σ) {ρ : Subst} (hρ : ρ.Atomic)
    (xs : List Binder) (as : List Val) (body : Expr) :
    ((body.subst (ρ.remove xs)).substLoc σ).subst (zipSubst xs (as.map (Val.substLoc σ))) =
      (body.subst (ρ.remove xs ++ zipSubst xs as)).substLoc σ := by
  rw [← Expr.subst_append (hρ.remove xs).noName, Expr.substLoc_subst hσ (zipSubst xs as),
    zipSubst_mapLoc]

theorem Val.subst_ext_vars (ρ : Subst) {xs : List Binder} {ws : List Val}
    (hn : (xs.map (·.name)).Nodup) (hl : xs.length = ws.length) {x : Var}
    (hx : x ∈ Binder.vars xs) :
    ∃ v ∈ ws, Val.subst (ρ.remove xs ++ zipSubst xs ws) (.var x) = v := by
  simp only [Binder.vars, List.mem_map] at hx
  obtain ⟨b, hb, rfl⟩ := hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
  exact ⟨_, List.getElem_mem _, Val.subst_ext_mem ρ hn hl hi⟩

theorem Binder.Fresh.not_mem_ctx {xs : List Binder} {U Δ : Finset Var} {Γ : Ctx}
    (h : Binder.Fresh xs U Δ Γ) {x : Var} (hx : Res.var x ∈ Γ) : x ∉ Binder.vars xs := by
  intro hx'
  simp only [Binder.vars, List.mem_map] at hx'
  obtain ⟨b, hb, rfl⟩ := hx'
  exact (h.2 b hb).2.2 hx

theorem Binder.Fresh.not_mem_borrowed {xs : List Binder} {U Δ : Finset Var} {Γ : Ctx}
    (h : Binder.Fresh xs U Δ Γ) {x : Var} (hx : x ∈ Δ) : x ∉ Binder.vars xs := by
  intro hx'
  simp only [Binder.vars, List.mem_map] at hx'
  obtain ⟨b, hb, rfl⟩ := hx'
  exact (h.2 b hb).2.1 hx

theorem Owned.congr {ρ ρ' : Subst} {Γ : Ctx} {S : Store} (h : Owned ρ Γ S)
    (hc : ∀ x, Res.var x ∈ Γ → Val.subst ρ' (.var x) = Val.subst ρ (.var x)) : Owned ρ' Γ S :=
  ⟨fun x hx => by rw [hc x hx]; exact h.var x hx, by rw [Ctx.map_substR_congr hc]; exact h.roots⟩

theorem Binder.mem_vars_of_owned {xs : List Binder} {x : Var} (h : Res.var x ∈ Binder.owned xs) :
    x ∈ Binder.vars xs := by
  simp only [Binder.owned, Multiset.mem_coe, List.mem_map, List.mem_filter] at h
  obtain ⟨b, ⟨hb, -⟩, hx⟩ := h
  cases hx
  exact List.mem_map_of_mem hb

theorem Binder.mem_vars_of_ownedSet {xs : List Binder} {x : Var} (h : x ∈ Binder.ownedSet xs) :
    x ∈ Binder.vars xs := by
  simp only [Binder.ownedSet, List.mem_toFinset, List.mem_map, List.mem_filter] at h
  obtain ⟨b, ⟨hb, -⟩, rfl⟩ := h
  exact List.mem_map_of_mem hb

theorem Val.mem_fvList_map_var {ls : List Var} {x : Var} : x ∈ Val.fvList (ls.map Val.var) ↔ x ∈ ls := by
  rw [Val.fvList_map_var]

theorem OwnedInv.swap_credit {S₁ R : Store} {σ : Nat → Option Val} {x : Var} {c : CName}
    {as : List Val} (h : OwnedInv S₁ ({Cell.bind x c as} + R) σ) (hR : R.Linear) (k : Nat) :
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

theorem Ctx.mem_vars {Γ : Ctx} {x : Var} : x ∈ Γ.vars ↔ Res.var x ∈ Γ := by
  simp only [Ctx.vars, Multiset.mem_filterMap]
  constructor
  · rintro ⟨r, hr, h⟩
    cases r with
    | var y => simp at h; subst h; exact hr
    | _ => simp at h
  · intro h; exact ⟨_, h, rfl⟩

theorem Owned.mem_roots {ρ : Subst} {Γ : Ctx} {S : Store} (h : Owned ρ Γ S) {x : Var}
    (hx : Res.var x ∈ Γ) : ∃ l, Val.subst ρ (.var x) = .var (.loc l) ∧ Res.var (.loc l) ∈ S.roots := by
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

theorem body_noLoc (hsig : sig.PaperFragment) {fd : FunDef} (hfd : fd ∈ sig)
    (hann : fd.annot ≠ .plain) : NoLoc fd.body.fv := by
  intro k hk
  rcases Wf.fv_subset (hsig.wf fd hfd hann).2 _ hk with h | h | h
  · simp [FunDef.scalars, Binder.scalars] at h
  · simp [Binder.ownedSet] at h
  · simp only [FunDef.ownedCtx, Multiset.mem_add, Multiset.mem_replicate] at h
    rcases h with h | h
    · simp [Binder.owned] at h
    · simp at h

theorem body_substLoc {σ : Nat → Option Val} (hσ : LocClosed σ) {body : Expr}
    (hnl : NoLoc body.fv) (τ : Subst) :
    (body.subst τ).substLoc σ = body.subst (τ.mapLoc σ) := by
  rw [Expr.substLoc_subst hσ, Expr.substLoc_of_noLoc σ body hnl]

theorem Val.subst_zip_append_mem {xs : List Binder} {ws : List Val} (τ : Subst)
    (hn : (xs.map (·.name)).Nodup) (hl : xs.length = ws.length) {i : Nat} (hi : i < xs.length) :
    Val.subst (zipSubst xs ws ++ τ) (.var (.name (xs[i]).name)) = ws[i]'(hl ▸ hi) := by
  simp [Val.subst, List.lookup_append, lookup_zipSubst_of_mem hn hl hi]

theorem remove_zipSubst_of_disjoint {xs ys : List Binder} (vs : List Val)
    (h : ∀ b ∈ xs, b.name ∉ ys.map (·.name)) : (zipSubst xs vs).remove ys = zipSubst xs vs := by
  unfold Subst.remove
  refine List.filter_eq_self.mpr fun p hp => ?_
  have := (List.of_mem_zip hp).1
  obtain ⟨b, hb, hb'⟩ := List.mem_map.mp this
  simp only [List.contains_eq_mem, decide_eq_false_iff_not, Bool.not_eq_eq_eq_not,
    Bool.not_true]
  rw [← hb']; exact h b hb

/-- The argument of a borrowed parameter: a location of the borrowed store or an annotated
    top-level function. -/
def BorrowedVal (sig : Sig) (S₁ : Store) (a : Val) : Prop :=
  (∃ l, a = .var (.loc l) ∧ Var.loc l ∈ S₁.dom) ∨
    (∃ g fd, a = .fn g ∧ sig.lookup g = some fd ∧ fd.annot ≠ .plain)

theorem BorrowedVal.atomic {S₁ : Store} {a : Val} (h : BorrowedVal sig S₁ a) : a.Atomic := by
  rcases h with ⟨l, rfl, -⟩ | ⟨g, -, rfl, -⟩ <;> trivial

theorem BorrowedVal.substLoc {S₁ : Store} {a : Val} (h : BorrowedVal sig S₁ a)
    {σ σ' : Nat → Option Val} (hag : ∀ n, Var.loc n ∈ S₁.dom → σ' n = σ n) :
    Val.substLoc σ' a = Val.substLoc σ a := by
  rcases h with ⟨l, rfl, hl⟩ | ⟨g, -, rfl, -⟩
  · simp [Val.substLoc, hag l hl]
  · rfl

/-- **The body of a called function** satisfies the conclusion of Theorem 1. -/
theorem call_body (hsig : sig.PaperFragment)
    (hfb : ∀ fd ∈ sig, fd.annot.isFbip = true → fbip = true) {n2 : Nat}
    (IH2 : MainClaim sig fbip n2) {g : FName} {fd : FunDef} (hg : sig.lookup g = some fd)
    (hann : fd.annot ≠ .plain) {S₁ S₃ : Store} {σ₃ : Nat → Option Val} {as1 : List Val}
    (has1 : ∀ a ∈ as1, BorrowedVal sig S₁ a) {xs₁ : List Var}
    (hr3 : S₃.roots = (xs₁.map Res.var : Multiset Res)) (hinv3 : OwnedInv S₁ S₃ σ₃)
    (hS₁ : S₁.Sound) (hl1 : fd.borrowed.length = as1.length) (hl2 : fd.owned.length = xs₁.length)
    {vs : List Val}
    (hev : StepsN sig n2
      ((fd.body.subst (zipSubst fd.borrowed as1 ++ zipSubst fd.owned (xs₁.map .var))).substLoc σ₃)
      (.ret vs)) :
    StoreResult sig fbip S₁ S₃
      (fd.body.subst (zipSubst fd.borrowed as1 ++ zipSubst fd.owned (xs₁.map .var))) σ₃ vs := by
  have hfd := (Sig.lookup_mem hg).1
  obtain ⟨hnd, hwf⟩ := hsig.wf fd hfd hann
  obtain ⟨hall, hsfb⟩ := hsig.scalarFree fd hfd
  have hb0 := hsig.noBudget fd hfd
  rw [List.all_append, Bool.and_eq_true] at hall
  obtain ⟨hallb, hallo⟩ := hall
  rw [List.map_append, List.nodup_append] at hnd
  obtain ⟨hndb, hndo, hdisj⟩ := hnd
  have hdisj' : ∀ b ∈ fd.borrowed, b.name ∉ fd.owned.map (·.name) := by
    intro b hb hb'
    exact hdisj _ (List.mem_map_of_mem hb) _ hb' rfl
  have hrem := remove_zipSubst_of_disjoint (ys := fd.owned) as1 hdisj'
  have hlocs : ∀ v ∈ xs₁.map Val.var, ∃ k, v = .var (.loc k) := by
    intro v hv
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hv
    obtain ⟨k, rfl, -⟩ := hinv3.root_loc (x := y) (by rw [hr3]; simp [hy])
    exact ⟨k, rfl⟩
  have hρ : (zipSubst fd.borrowed as1 ++ zipSubst fd.owned (xs₁.map .var)).Atomic := by
    refine (Subst.atomic_zipSubst _ _ fun v hv => ?_).append
      (Subst.atomic_zipSubst _ _ fun v hv => .inl (hlocs v hv))
    rcases has1 v hv with ⟨l, rfl, -⟩ | ⟨g', -, rfl, -⟩
    · exact .inl ⟨l, rfl⟩
    · exact .inr ⟨g', rfl⟩
  have hΔ : ∀ x ∈ Binder.ownedSet fd.borrowed,
      Borrowed sig S₁ (zipSubst fd.borrowed as1 ++ zipSubst fd.owned (xs₁.map .var)) x := by
    intro x hx
    have hx' := Binder.mem_vars_of_ownedSet hx
    simp only [Binder.vars, List.mem_map] at hx'
    obtain ⟨b, hb, rfl⟩ := hx'
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    unfold Borrowed
    rw [Val.subst_zip_append_mem _ hndb hl1 hi]
    rcases has1 _ (List.getElem_mem _) with ⟨l, hl, hlS⟩ | ⟨g', fd', hg', hl', hann'⟩
    · exact .inl ⟨l, hl, hlS⟩
    · exact .inr ⟨g', fd', hg', hl', hann'⟩
  have hlen' : fd.owned.length = (xs₁.map Val.var).length := by simp [hl2]
  have hΓ : Owned (zipSubst fd.borrowed as1 ++ zipSubst fd.owned (xs₁.map .var)) fd.ownedCtx S₃ := by
    have hctx : fd.ownedCtx = Binder.owned fd.owned := by simp [FunDef.ownedCtx, hb0]
    rw [hctx]
    conv => arg 1; rw [← hrem]
    refine ⟨fun y hy => ?_, ?_⟩
    · obtain ⟨v, hv, hv'⟩ := Val.subst_ext_vars _ hndo hlen' (Binder.mem_vars_of_owned hy)
      obtain ⟨k, rfl⟩ := hlocs v hv
      exact ⟨k, hv'⟩
    · rw [Binder.owned_substR hallo hndo hl2, Ctx.nz_vars, hr3]
  have hU : fd.scalars = ∅ := by
    simp [FunDef.scalars, Binder.scalars_of_all hallb, Binder.scalars_of_all hallo]
  exact IH2 (cfg_compatible hsig hfb hfd) hU hsfb hwf hρ hΔ hΓ hS₁ hinv3 hev

end FIPNamed
