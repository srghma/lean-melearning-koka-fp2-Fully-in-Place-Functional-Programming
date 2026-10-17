module

public import RequestProject.Named.AppC_StackBound.StackSem

@[expose] public section

/-!
# Ranks and weights for the stack bound (Appendix C)

## Ranks and weights

The *rank* of a function is the index of its mutually recursive group.  Each active call of
the store semantics (a *frame*) is the instance of the body of a function of rank `i`, in
which every function value has rank `< M`; its *weight* is `max i M · |groups| + i + 1`.
A frame calls

* a function of its own group only in tail position (the frame is replaced),
* a function of a lower rank `j < i`, whose frame has the weight of `(j, max j M)`, or
* a function value of rank `j < M`, whose frame has the weight of `(j, j)`,

and both are strictly lighter (`wt_call_lt`, `wt_app_lt`).  Hence at most
`|groups|² + |groups|` frames are nested, and each contributes at most `|e_max|` to the
evaluation context.
-/

namespace FIPNamed

/-- The rank of a function: the index of its group. -/
def rank (groups : List (List FName)) (g : FName) : Nat :=
  groups.findIdx (fun l => decide (g ∈ l))

theorem rank_lt {groups : List (List FName)} {g : FName} (h : g ∈ groups.flatten) :
    rank groups g < groups.length := by
  obtain ⟨l, hl, hg⟩ := List.mem_flatten.mp h
  exact List.findIdx_lt_length_of_exists ⟨l, hl, by simpa using hg⟩

theorem mem_of_rank {groups : List (List FName)} {g : FName} (h : rank groups g < groups.length) :
    g ∈ groups[rank groups g] := by
  have := List.findIdx_getElem (p := fun l => decide (g ∈ l)) (xs := groups) (w := h)
  simpa using this

theorem rank_of_mem {groups : List (List FName)} (hnd : groups.flatten.Nodup) {g : FName}
    {j : Nat} (hj : j < groups.length) (hg : g ∈ groups[j]) : rank groups g = j := by
  have hlt : rank groups g < groups.length :=
    rank_lt (List.mem_flatten.mpr ⟨_, List.getElem_mem hj, hg⟩)
  have hk := mem_of_rank hlt
  have hdisj := (List.nodup_flatten.mp hnd).2
  rcases lt_trichotomy (rank groups g) j with h | h | h
  · exfalso
    exact (List.pairwise_iff_getElem.mp hdisj) _ _ hlt hj h hk hg
  · exact h
  · exfalso
    exact (List.pairwise_iff_getElem.mp hdisj) _ _ hj hlt h hg hk

theorem length_le_flatten {l : List (List FName)} (h : ∀ x ∈ l, x ≠ []) :
    l.length ≤ l.flatten.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatten_cons, List.length_append, List.length_cons]
    have := List.length_pos_iff.mpr (h a (by simp))
    have := ih (fun x hx => h x (by simp [hx]))
    omega

/-- The weight of a frame. -/
def wt (m i M : Nat) : Nat := max i M * m + i + 1

theorem wt_le {m i M : Nat} (hi : i < m) (hM : M ≤ m) : wt m i M ≤ m * m + m := by
  unfold wt
  have : max i M * m ≤ m * m := Nat.mul_le_mul_right _ (max_le hi.le hM)
  omega

theorem wt_call_lt {m i j M : Nat} (hj : j < i) : wt m j (max j M) < wt m i M := by
  unfold wt
  have : max j (max j M) * m ≤ max i M * m := Nat.mul_le_mul_right _ (by omega)
  omega

theorem wt_app_lt {m i j M : Nat} (hj : j < M) (hjm : j < m) : wt m j j < wt m i M := by
  unfold wt
  have h1 : (j + 1) * m ≤ max i M * m := Nat.mul_le_mul_right _ (by omega)
  have h2 : max j j * m + j + 1 ≤ (j + 1) * m := by
    rw [max_self, Nat.succ_mul]; omega
  omega

theorem wt_tail {m i M : Nat} : wt m i (max i M) = wt m i M := by
  unfold wt; rw [← max_assoc, max_self]

/-- A function value occurring in a tail context does not belong to the group. -/
theorem Expr.TailIn.fns_not_mem {fs : List FName} {e : Expr} (h : Expr.TailIn fs e) :
    ∀ g ∈ e.fns, g ∉ fs := by
  have av : ∀ {e : Expr}, e.Avoids fs → ∀ g ∈ e.fns, g ∉ fs :=
    fun he g hg => he g (Expr.fns_subset_funs _ g hg)
  induction h with
  | base e he => exact av he
  | call f e1 e2 _ h1 h2 =>
    intro g hg
    simp only [Expr.fns, List.mem_append] at hg
    rcases hg with hg | hg
    · exact av h1 g hg
    · exact av h2 g hg
  | letIn xs e0 e h0 _ ih =>
    intro g hg
    simp only [Expr.fns, List.mem_append] at hg
    rcases hg with hg | hg
    · exact av h0 g hg
    · exact ih g hg
  | bmatch e0 bs h0 _ ih =>
    intro g hg
    simp only [Expr.fns, List.mem_append] at hg
    rcases hg with hg | hg
    · exact av h0 g hg
    · obtain ⟨b, hb, hg⟩ := Expr.mem_fnsB.mp hg
      exact ih b hb g hg
  | dmatch e0 bs h0 _ ih =>
    intro g hg
    simp only [Expr.fns, List.mem_append] at hg
    rcases hg with hg | hg
    · exact av h0 g hg
    · obtain ⟨b, hb, hg⟩ := Expr.mem_fnsB.mp hg
      exact ih b hb g hg
  | drop x e _ ih => exact ih
  | free k e _ ih => exact ih

end FIPNamed
