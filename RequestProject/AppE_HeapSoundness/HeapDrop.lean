module

public import RequestProject.AppE_HeapSoundness.HeapInv

@[expose] public section

/-!
# `dup` and `drop` in the heap semantics

* `heap_dups`: `dup x̄; e` increments the reference counts of `x̄` and adds them to the roots;
* `heap_drop`: `drop x; e`, for a root `x`, removes one root `x`: the reference count of
  `x` is decremented, or, if it was unique, the cell is freed and its fields are dropped
  recursively (`heap_drops`).  The recursion terminates since every freed cell makes the
  heap smaller.
-/

namespace FIP.Lam

variable {sig : LSig} {funs : List FName}

/-- `dup x̄; e` for locations `x̄` bound in the heap. -/
theorem heap_dups : ∀ (ls : List Nat) {H : Heap} {σ : Nat → Option (LVal 0)} (e : LExpr 0),
    HInv funs H σ → (∀ l ∈ ls, Var.loc l ∈ H.dom) →
    ∃ H', HSteps sig H (dups (ls.map locV) e) H' e ∧ HInv funs H' σ ∧
      H'.roots = H.roots + locsCtx ls ∧ H'.dom = H.dom
  | [], H, σ, e, h, _ => ⟨H, .refl _ _, h, by simp, rfl⟩
  | l :: ls, H, σ, e, h, hd => by
    obtain ⟨m, o, hc⟩ := Heap.mem_dom_iff.mp (hd l (by simp))
    obtain ⟨H₀, rfl⟩ := Multiset.exists_cons_of_mem hc
    rw [← Multiset.singleton_add] at h hd ⊢
    have h1 := h.inc
    have hstep : HStep sig ({HCell.bind (.loc l) m o} + H₀) (dups ((l :: ls).map locV) e)
        ({HCell.bind (.loc l) (m + 1) o} + H₀) (dups (ls.map locV) e) :=
      (HHead.dup H₀ (.loc l) m o _).step
    have hdom : Heap.dom ({HCell.bind (.loc l) (m + 1) o} + H₀) =
        Heap.dom ({HCell.bind (.loc l) m o} + H₀) := by simp
    obtain ⟨H', hs, hinv, hroots, hdom'⟩ := heap_dups ls e h1 (fun l' hl' => by
      rw [hdom]; exact hd l' (by simp [hl']))
    refine ⟨H', HSteps.head hstep hs, hinv, ?_, hdom'.trans hdom⟩
    rw [hroots, Heap.roots_inc h.linear, locsCtx_cons]
    abel

/-- After freeing a unique cell, its fields are roots. -/
theorem free_fvCtx_le {x : Var 0} {o : HObj} {H₀ : Heap}
    (h : Heap.Linear ({HCell.bind x 1 o} + H₀))
    (hx : Res.var x ∈ Heap.roots ({HCell.bind x 1 o} + H₀)) : o.fvCtx ≤ Heap.roots H₀ := by
  have hr := Heap.roots_free h hx
  have hx0 := Heap.free_refs h hx
  have hxo : Res.var x ∉ o.fvCtx := by
    intro hx'
    have := Multiset.count_pos.mpr hx'
    rw [Heap.fvCtx_count] at this
    simp [Multiset.singleton_add] at hx0
    omega
  rw [Multiset.le_iff_count]
  intro r
  have := congrArg (Multiset.count r) hr
  rw [Multiset.count_add, Multiset.count_add] at this
  by_cases hrx : r = Res.var x
  · subst hrx; rw [Multiset.count_eq_zero.mpr hxo]; omega
  · rw [Multiset.count_singleton, if_neg hrx] at this; omega

/-- The statement of `heap_drop` for heaps of size at most `N`. -/
def DropClaim (sig : LSig) (funs : List FName) (N : Nat) : Prop :=
  ∀ {H : Heap} {σ : Nat → Option (LVal 0)}, Multiset.card H ≤ N → HInv funs H σ →
    ∀ (l : Nat) (e : LExpr 0), Res.var (.loc l) ∈ H.roots →
      ∃ H', HSteps sig H (.drop (locV l) e) H' e ∧ HInv funs H' σ ∧
        H'.roots + {Res.var (.loc l)} = H.roots ∧ Multiset.card H' ≤ Multiset.card H

/-- `drop x̄; e` from `drop x; e`. -/
theorem drops_of_drop {N : Nat} (hdrop : DropClaim sig funs N) :
    ∀ (ls : List Nat) {H : Heap} {σ : Nat → Option (LVal 0)}, Multiset.card H ≤ N →
      HInv funs H σ → ∀ (e : LExpr 0), locsCtx ls ≤ H.roots →
      ∃ H', HSteps sig H (drops (ls.map locV) e) H' e ∧ HInv funs H' σ ∧
        H'.roots + locsCtx ls = H.roots ∧ Multiset.card H' ≤ Multiset.card H
  | [], H, σ, _, h, e, _ => ⟨H, .refl _ _, h, by simp, le_rfl⟩
  | l :: ls, H, σ, hN, h, e, hle => by
    rw [locsCtx_cons] at hle
    have hl : Res.var (.loc l) ∈ H.roots :=
      Multiset.mem_of_le hle (Multiset.mem_add.mpr (.inl (Multiset.mem_singleton_self _)))
    obtain ⟨H₁, hs₁, h₁, hr₁, hc₁⟩ := hdrop hN h l (drops (ls.map locV) e) hl
    have hle₁ : locsCtx ls ≤ Heap.roots H₁ := by
      rw [← hr₁, add_comm (Heap.roots H₁)] at hle; exact (add_le_add_iff_left _).mp hle
    obtain ⟨H₂, hs₂, h₂, hr₂, hc₂⟩ := drops_of_drop hdrop ls (le_trans hc₁ hN) h₁ e hle₁
    refine ⟨H₂, hs₁.trans hs₂, h₂, ?_, le_trans hc₂ hc₁⟩
    rw [← hr₁, ← hr₂, locsCtx_cons]; abel

theorem dropClaim : ∀ N, DropClaim sig funs N := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N IH =>
  intro H σ hN h l e hl
  obtain ⟨m, o, hc⟩ := Heap.mem_dom_iff.mp (h.linear.mem_dom_of_root hl)
  have hm := h.linear.1.2.1 _ m o hc
  obtain ⟨H₀, rfl⟩ := Multiset.exists_cons_of_mem hc
  rw [← Multiset.singleton_add] at h hl hN ⊢
  rcases Nat.lt_or_ge m 2 with hm1 | hm2
  · obtain rfl : m = 1 := by omega
    -- the cell is unique: free it and drop its fields
    have h₀ := h.free hl
    have hr := Heap.roots_free h.linear hl
    obtain ⟨ls, hls⟩ := (h.ok (.loc l) 1 o (by simp)).fields_locs
    have hfv : o.fvCtx = locsCtx ls := by
      simp only [HObj.fvCtx, HObj.fv_eq_fields, hls, LVal.fvList_locs, locsCtx, List.map_map]
      rfl
    have hle : locsCtx ls ≤ Heap.roots H₀ := hfv ▸ free_fvCtx_le h.linear hl
    have hcard : Multiset.card H₀ < N := by simp at hN; omega
    obtain ⟨H', hs, hinv, hroots, hc'⟩ :=
      drops_of_drop (IH _ hcard) ls (N := Multiset.card H₀) le_rfl h₀ e hle
    have hstep : HStep sig ({HCell.bind (.loc l) 1 o} + H₀) (.drop (locV l) e) H₀
        (drops (ls.map locV) e) := by
      cases o with
      | con c args =>
        simp only [HObj.fields] at hls; subst hls
        exact (HHead.dcon H₀ (.loc l) c _ e).step
      | clo zs c k b =>
        simp only [HObj.fields] at hls; subst hls
        exact (HHead.dlam H₀ (.loc l) _ c k b e).step
    refine ⟨H', HSteps.head hstep hs, hinv, ?_, by simp; omega⟩
    rw [← hfv] at hroots
    have := congrArg (· + ({Res.var (Var.loc l)} : Ctx 0)) hroots
    simp only at this
    rw [add_right_comm, hr] at this
    exact add_right_cancel this
  · obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
    exact ⟨_, HSteps.single (HHead.drop H₀ (.loc l) n o e).step, h.dec hl,
      Heap.roots_dec h.linear hl, by simp⟩

/-- `drop x; e` for a root `x`. -/
theorem heap_drop {H : Heap} {σ : Nat → Option (LVal 0)} (h : HInv funs H σ) (l : Nat)
    (e : LExpr 0) (hl : Res.var (.loc l) ∈ H.roots) :
    ∃ H', HSteps sig H (.drop (locV l) e) H' e ∧ HInv funs H' σ ∧
      H'.roots + {Res.var (.loc l)} = H.roots := by
  obtain ⟨H', hs, h', hr, -⟩ := dropClaim (sig := sig) _ le_rfl h l e hl
  exact ⟨H', hs, h', hr⟩

/-- `drop x̄; e` for roots `x̄`. -/
theorem heap_drops {H : Heap} {σ : Nat → Option (LVal 0)} (h : HInv funs H σ) (ls : List Nat)
    (e : LExpr 0) (hl : locsCtx ls ≤ H.roots) :
    ∃ H', HSteps sig H (drops (ls.map locV) e) H' e ∧ HInv funs H' σ ∧
      H'.roots + locsCtx ls = H.roots := by
  obtain ⟨H', hs, h', hr, -⟩ := drops_of_drop (dropClaim (sig := sig) _) ls le_rfl h e hl
  exact ⟨H', hs, h', hr⟩

end FIP.Lam
