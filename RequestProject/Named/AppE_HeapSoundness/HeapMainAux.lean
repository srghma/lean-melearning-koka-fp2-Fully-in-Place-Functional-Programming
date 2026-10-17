module

public import RequestProject.Named.AppE_HeapSoundness.HeapAlloc

@[expose] public section

/-!
# Auxiliary facts for the main invariant of Theorem 6
-/

namespace FIPNamed.Lam

variable {sig : LSig} {funs : List FName} {R : Multiset Var} {RC : Multiset Nat}

/-! ## Renaming environments of locations -/

theorem Res.ren_locOnly {τ : LSubst} (hτ : τ.LocRen) {Γ : Ctx} (h : Ctx.LocOnly Γ) :
    Γ.map (Res.ren τ) = Γ := by
  conv_rhs => rw [← Multiset.map_id Γ]
  apply Multiset.map_congr rfl
  intro r hr
  rcases h r hr with ⟨l, rfl⟩ | ⟨k, rfl⟩
  · simp [Res.ren, hτ.ren_loc]
  · rfl

theorem image_ren_locs {τ : LSubst} (hτ : τ.LocRen) {Δ : Finset Var}
    (h : ∀ x ∈ Δ, ∃ l, x = .loc l) : Δ.image τ.ren = Δ := by
  conv_rhs => rw [← Finset.image_id (s := Δ)]
  apply Finset.image_congr
  intro x hx
  obtain ⟨l, rfl⟩ := h x hx
  exact hτ.ren_loc l

theorem ctx_ren_lzip : ∀ (xs : List Binder) (ys : List Var), (xs.map (·.name)).Nodup →
    xs.length = ys.length →
    (Binder.ctx xs).map (Res.ren (lzip xs (ys.map .var))) = locCtx (ys.map .var)
  | [], [], _, _ => by simp [Binder.ctx, locCtx, LVal.fvList]
  | b :: xs, y :: ys, hnd, hl => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    have ih := ctx_ren_lzip xs ys hnd.2 (by simpa using hl)
    rw [List.map_cons, locCtx_cons_var, ← ih]
    have hb : Binder.ctx (b :: xs) = {Res.var (.name b.name)} + Binder.ctx xs := by
      simp [Binder.ctx]
    rw [hb, Multiset.map_add]
    congr 1
    · simp [Res.ren, LSubst.ren, lzip_cons]
    · apply Multiset.map_congr rfl
      intro r hr
      simp only [Binder.ctx, Multiset.mem_coe, List.mem_map] at hr
      obtain ⟨b', hb', rfl⟩ := hr
      have hne : Var.name b'.name ≠ Var.name b.name := by
        intro h; injection h with h; exact hnd.1 ⟨b', hb', h⟩
      simp only [Res.ren, LSubst.ren]
      rw [lzip_cons, if_neg hne]
  | [], _ :: _, _, hl => by simp at hl
  | _ :: _, [], _, hl => by simp at hl

theorem lzip_append : ∀ (bs os : List Binder) (as1 as2 : List LVal), bs.length = as1.length →
    ∀ y, lzip (bs ++ os) (as1 ++ as2) y =
      match lzip bs as1 y with
      | some v => some v
      | none => lzip os as2 y
  | [], os, [], as2, _, y => by simp [lzip]
  | b :: bs, os, a :: as1, as2, hl, y => by
    rw [List.cons_append, List.cons_append, lzip_cons, lzip_cons]
    split_ifs
    · rfl
    · exact lzip_append bs os as1 as2 (by simpa using hl) y
  | [], _, _ :: _, _, hl, _ => by simp at hl
  | _ :: _, _, [], _, hl, _ => by simp at hl

theorem lzip_some_of_mem : ∀ (bs : List Binder) (as : List LVal), bs.length = as.length →
    ∀ y, y ∈ Binder.vars bs → ∃ v ∈ as, lzip bs as y = some v
  | [], [], _, y, hy => by simp [Binder.vars] at hy
  | b :: bs, a :: as, hl, y, hy => by
    rw [lzip_cons]
    by_cases h : y = .name b.name
    · rw [if_pos h]; exact ⟨a, by simp, rfl⟩
    · rw [if_neg h]
      have hy' : y ∈ Binder.vars bs := by
        simp only [Binder.vars, List.map_cons, List.mem_cons] at hy
        rcases hy with hy | hy
        · exact absurd hy h
        · exact hy
      obtain ⟨v, hv, hv'⟩ := lzip_some_of_mem bs as (by simpa using hl) y hy'
      exact ⟨v, by simp [hv], hv'⟩
  | [], _ :: _, hl, _, _ => by simp at hl
  | _ :: _, [], hl, _, _ => by simp at hl

theorem lzip_none_of_not_mem {bs : List Binder} {as : List LVal} {y : Var}
    (h : y ∉ Binder.vars bs) : lzip bs as y = none := lzip_not_mem h

theorem lzip_locRen (xs : List Binder) (vs : List LVal) (h : ∀ v ∈ vs, v.IsLoc) :
    (lzip xs vs).LocRen :=
  ⟨lzip_loc xs vs, fun _ v hy => h v (lzip_mem hy)⟩

theorem vals_subst_lzip : ∀ (xs : List Binder) (vs : List LVal), (xs.map (·.name)).Nodup →
    xs.length = vs.length → LVal.substList (lzip xs vs) (Binder.vals xs) = vs
  | [], [], _, _ => rfl
  | b :: xs, v :: vs, hnd, hl => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    simp only [Binder.vals, List.map_cons, LVal.substList]
    rw [LVal.subst, lzip_cons, if_pos rfl]
    congr 1
    have ih := vals_subst_lzip xs vs hnd.2 (by simpa using hl)
    refine Eq.trans ?_ ih
    simp only [Binder.vals]
    rw [LVal.substList_eq_map, LVal.substList_eq_map]
    apply List.map_congr_left
    intro w hw
    obtain ⟨b', hb', rfl⟩ := List.mem_map.mp hw
    simp only [LVal.subst]
    have hne : Var.name b'.name ≠ Var.name b.name := by
      intro h; injection h with h; exact hnd.1 ⟨b', hb', h⟩
    rw [lzip_cons, if_neg hne]
  | [], _ :: _, _, hl => by simp at hl
  | _ :: _, [], _, hl => by simp at hl

theorem substB_eq_map (σ : LSubst) (bs : List LBranch) :
    LExpr.substB σ bs = bs.map fun b => .mk b.ctor b.binders (b.body.subst (σ.remove b.binders)) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    obtain ⟨c, xs, e⟩ := b
    simp [LExpr.substB, ih, LBranch.ctor, LBranch.binders, LBranch.body]

theorem lfindBranch_substB (σ : LSubst) (bs : List LBranch) (c : CName) (k : Nat) :
    lfindBranch (LExpr.substB σ bs) c k = (lfindBranch bs c k).map
      fun b => .mk b.ctor b.binders (b.body.subst (σ.remove b.binders)) := by
  simp only [lfindBranch, substB_eq_map, List.find?_map]
  rfl

theorem LSig.lookup_mem {sig : LSig} {f : FName} {fd : LFunDef} (h : sig.lookup f = some fd) :
    fd ∈ sig := List.mem_of_find?_eq_some h

/-! ## Functional reductions of `dup`s -/

theorem LStepsN.dups_inv : ∀ (vs : List LVal) {n : Nat} {e : LExpr} {ws : List LVal},
    LStepsN sig n (dups vs e) (.ret ws) → vs.length ≤ n ∧ LStepsN sig (n - vs.length) e (.ret ws)
  | [], n, e, ws, h => by simpa [dups] using h
  | v :: vs, n, e, ws, h => by
    obtain ⟨m, t, rfl, hh, hrest⟩ :=
      LStepsN.head_of (fun t hs => LStep.of_noCtx (e := LExpr.dup v (dups vs e)) trivial hs) (by simp [LExpr.IsRet]) h
    cases hh
    obtain ⟨h1, h2⟩ := LStepsN.dups_inv vs hrest
    refine ⟨by simp; omega, ?_⟩
    simpa [show m + 1 - (vs.length + 1) = m - vs.length by omega] using h2

theorem LExpr.Adm.of_dups : ∀ (vs : List LVal) {e : LExpr}, (dups vs e).Adm → e.Adm
  | [], e, h => h
  | v :: vs, e, h => by
    cases h with
    | dup _ _ _ h => exact LExpr.Adm.of_dups vs h

theorem dups_inj : ∀ (vs : List LVal) {e e' : LExpr}, dups vs e = dups vs e' → e = e'
  | [], _, _, h => h
  | v :: vs, e, e', h => by
    simp only [dups, LExpr.dup.injEq, true_and] at h
    exact dups_inj vs h

/-! ## Inverting `dropru` -/

theorem LWf.dropru_inv {Δ : Finset Var} {Γ : Ctx} {e : LExpr} (h : LWf funs Δ Γ e) :
    ∀ {x : Var} {k : Nat} {e₀ : LExpr}, e = .dropru (.var x) k e₀ →
    ∃ (Γ₀ : Ctx) (j : Nat), Γ = Γ₀ + {Res.var x} + Multiset.replicate j (Res.credit 0) ∧
      LWf funs Δ (Γ₀ + {Res.credit k}) e₀ := by
  match h with
  | .dropru y k' he =>
    intro x k e₀ heq
    simp only [LExpr.dropru.injEq, LVal.var.injEq] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    exact ⟨_, 0, by simp, he⟩
  | .empty he =>
    intro x k e₀ heq
    obtain ⟨Γ₀, j, rfl, h'⟩ := LWf.dropru_inv he heq
    exact ⟨Γ₀, j + 1, by rw [Multiset.replicate_succ, ← Multiset.singleton_add]; abel, h'⟩
  | .tuple _ => intro x k e₀ heq; cases heq
  | .call .. => intro x k e₀ heq; cases heq
  | .app .. => intro x k e₀ heq; cases heq
  | .letIn .. => intro x k e₀ heq; cases heq
  | .match .. => intro x k e₀ heq; cases heq
  | .dup .. => intro x k e₀ heq; cases heq
  | .drop .. => intro x k e₀ heq; cases heq
  | .free .. => intro x k e₀ heq; cases heq
  | .alloc .. => intro x k e₀ heq; cases heq

/-! ## Readback -/

theorem subst_agree {σ σ' : Nat → Option LVal} {S : Multiset Var} {e : LExpr}
    (hag : ∀ l, Var.loc l ∈ S → σ' l = σ l) (hS : ∀ l, Var.loc l ∈ e.dfv → Var.loc l ∈ S) :
    e.subst (locS σ') = e.subst (locS σ) := by
  apply LExpr.subst_congr
  intro y hy
  cases y with
  | name s => rfl
  | loc l => exact hag l (hS l hy)

theorem HInv.cell_rd {H : Heap} {Γ : Ctx} {σ : Nat → Option LVal}
    (h : HInv funs H R RC Γ σ) {y : Var} (hy : y ∈ H.cntM) :
    ∃ l n o, y = .loc l ∧ HCell.bind (.loc l) n o ∈ H ∧ rd σ y = o.toVal.subst (locS σ) := by
  obtain ⟨l, n, o, rfl, hc⟩ := h.loc_of_cntM hy
  refine ⟨l, n, o, rfl, hc, ?_⟩
  simp [rd, LVal.subst, locS, h.reads.cell l n o hc]

theorem HInv.locs_of_R {H : Heap} {Γ : Ctx} {σ : Nat → Option LVal}
    (h : HInv funs H R RC Γ σ) {Δ : Finset Var} (hΔ : ∀ x ∈ Δ, x ∈ R) :
    ∀ x ∈ Δ, ∃ l, x = .loc l := by
  intro x hx
  obtain ⟨l, -, -, rfl, -⟩ := h.loc_of_cntM (h.R_cntM (hΔ x hx))
  exact ⟨l, rfl⟩

theorem HInv.dom_of_R {H : Heap} {Γ : Ctx} {σ : Nat → Option LVal}
    (h : HInv funs H R RC Γ σ) {x : Var} (hx : x ∈ R) : x ∈ H.dom :=
  Heap.mem_dom_of_cntM (h.R_cntM hx)

end FIPNamed.Lam
