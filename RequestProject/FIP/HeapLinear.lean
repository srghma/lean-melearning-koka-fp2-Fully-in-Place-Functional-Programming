module

public import RequestProject.FIP.HeapOps

@[expose] public section

/-!
# The invariant of Theorem 6 in terms of linear heaps and roots

A heap satisfying the invariant `HInv H R RC Γ σ` is linear in the sense of Appendix E
(`Heap.Linear`), and its roots `roots(H)` are, as locations, exactly the references `R` held
by the rest of the computation together with the owned locations of `Γ`.
-/

namespace FIP.Lam

theorem count_cntM_of_not_mem_dom {H : Heap} {x : Var} (hx : x ∉ H.dom) :
    H.cntM.count x = 0 := by
  rw [Multiset.count_eq_zero]
  intro hm
  obtain ⟨n, o, hc, -⟩ := Heap.mem_cntM.mp hm
  exact hx (Heap.mem_dom.mpr ⟨n, o, hc⟩)

theorem count_cntM_of_cell {H : Heap} (hnd : H.dom.Nodup) {x : Var} {n : Nat} {o : HObj}
    (hc : HCell.bind x n o ∈ H) : H.cntM.count x = n := by
  obtain ⟨H₀, rfl⟩ := Heap.eq_add_of_mem hc
  rw [Heap.dom_add, Heap.dom_bind, Multiset.singleton_add, Multiset.nodup_cons] at hnd
  rw [Heap.cntM_add, Heap.cntM_bind, Multiset.count_add, Multiset.count_replicate_self,
    count_cntM_of_not_mem_dom hnd.1, add_zero]

theorem Ctx.vars_replicate_var (k : Nat) (y : Var) :
    Ctx.vars (Multiset.replicate k (Res.var y)) = Multiset.replicate k y := by
  rw [← Multiset.map_replicate, Ctx.vars_map_var]

theorem vars_bind_count (M : Multiset Var) (g : HCell → Ctx)
    (hb : ∀ y n o, g (.bind y n o) = Multiset.replicate (n - M.count y) (Res.var y))
    (hcr : ∀ k, Ctx.vars (g (.credit k)) = 0) :
    ∀ (H : Heap), H.dom.Nodup → ∀ x, (Ctx.vars (H.bind g)).count x = H.cntM.count x - M.count x := by
  intro H
  induction H using Multiset.induction_on with
  | empty => intro _ x; simp [Ctx.vars_zero]
  | cons c H ih =>
    intro hnd x
    cases c with
    | credit k =>
      rw [Heap.dom_cons_credit] at hnd
      rw [Multiset.cons_bind, Ctx.vars_add, hcr, zero_add, Heap.cntM_cons_credit, ih hnd x]
    | bind y n o =>
      rw [Heap.dom_cons_bind, Multiset.nodup_cons] at hnd
      rw [Multiset.cons_bind, Ctx.vars_add, hb, Ctx.vars_replicate_var, Heap.cntM_cons_bind,
        Multiset.count_add, Multiset.count_add, ih hnd.2 x]
      by_cases hxy : x = y
      · subst hxy
        rw [Multiset.count_replicate_self, Multiset.count_replicate_self,
          count_cntM_of_not_mem_dom hnd.1]
        omega
      · rw [Multiset.count_replicate, Multiset.count_replicate, if_neg (Ne.symm hxy),
          if_neg (Ne.symm hxy)]
        omega

namespace HInv

variable {funs : List FName} {H : Heap} {R : Multiset Var} {RC : Multiset Nat} {Γ : Ctx}
  {σ : Nat → Option LVal}

/-- The roots of the heap, as locations, are `R, Γ`. -/
theorem vars_roots (h : HInv funs H R RC Γ σ) : Ctx.vars H.roots = R + Ctx.vars Γ := by
  classical
  ext x
  unfold Heap.roots
  rw [vars_bind_count H.rngFv _ (fun _ _ _ => rfl) (fun k => by dsimp only; split_ifs <;> rfl) H h.nodup x,
    h.cnt, Multiset.count_add _ (R + Ctx.vars Γ), Nat.add_sub_cancel]

/-- A heap satisfying the invariant is linear. -/
theorem linear (h : HInv funs H R RC Γ σ) : H.Linear := by
  refine ⟨⟨h.nodup, fun x n o hc => (h.cell_ok hc).2.1,
    fun x hx => Heap.mem_dom_of_cntM (h.rngFv_cntM hx)⟩, fun x n o hc => ?_⟩
  rw [← count_cntM_of_cell h.nodup hc, h.cnt]
  exact Multiset.count_le_of_le _ (Multiset.le_add_left _ _)

/-- The invariant for the empty heap. -/
theorem empty (funs : List FName) : HInv funs 0 0 0 0 (fun _ => none) :=
  ⟨by simp, by simp [Heap.dom], by simp [Ctx.vars, Heap.rngFv],
    by simp [nz, Heap.creditsM, Ctx.cr], fun r hr => by simp at hr,
    ⟨fun l v h => by simp at h, fun l n o h => by simp at h⟩⟩

end HInv

end FIP.Lam
