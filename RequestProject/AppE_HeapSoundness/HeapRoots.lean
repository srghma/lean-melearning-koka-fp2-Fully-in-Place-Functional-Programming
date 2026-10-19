module

public import RequestProject.AppE_HeapSoundness.HeapFunSteps

@[expose] public section

/-!
# Reference counts and roots of heaps (Appendix E.1)

The roots of a heap are counted cell by cell: a location `y` is a root as often as its
reference count `rc H y` exceeds the number `refs H y` of references to it from the heap
(`count_roots_var`), and a reuse credit `⋄k` (`k ≠ 0`) as often as it occurs in the heap
(`count_roots_credit`).

From this we derive how the roots and linearity of a heap change under the basic heap
operations of Fig. 10:

* incrementing a reference count (`dup`): `Heap.inc_linear`, `Heap.roots_inc`;
* decrementing a shared reference count (`drop`): `Heap.dec_linear`, `Heap.roots_dec`;
* freeing a unique cell (`dcon`, `dlam`): `Heap.free_linear`, `Heap.roots_free`;
* allocating a fresh cell: `Heap.alloc_linear`, `Heap.roots_alloc`;
* adding or removing a reuse credit: `Heap.credit_linear`, `Heap.roots_credit`.
-/

namespace FIP.Lam

/-- The fields of an object, as owned resources. -/
def HObj.fvCtx (o : HObj) : Ctx 0 := ((o.fv.map Res.var : List (Res 0)))

namespace Heap

/-- The reference count of `y` in `H` (`0` if `y` is not bound). -/
def rc (H : Heap) (y : Var 0) : Nat :=
  (H.map fun c => match c with | .bind x n _ => if x = y then n else 0 | .credit _ => 0).sum

/-- The number of reuse credits `⋄k` in `H`. -/
def ncred (H : Heap) (k : Nat) : Nat :=
  (H.map fun c => match c with | .credit j => if j = k then 1 else 0 | .bind _ _ _ => 0).sum

/-- The number of references to `y` from the objects of `H`. -/
def refs (H : Heap) (y : Var 0) : Nat := H.rngFv.count y

variable {H H₀ H₁ H₂ : Heap} {x y : Var 0} {n k : Nat} {o : HObj}

@[simp] theorem rc_zero : rc 0 y = 0 := by simp [rc]
@[simp] theorem rc_add : rc (H₁ + H₂) y = rc H₁ y + rc H₂ y := by simp [rc]
@[simp] theorem rc_bind : rc {.bind x n o} y = if x = y then n else 0 := by simp [rc]
@[simp] theorem rc_credit : rc {.credit k} y = 0 := by simp [rc]

@[simp] theorem rngFv_zero : rngFv 0 = 0 := by simp [rngFv]
@[simp] theorem rngFv_add : rngFv (H₁ + H₂) = rngFv H₁ + rngFv H₂ := by simp [rngFv]
@[simp] theorem rngFv_bind : rngFv {.bind x n o} = (o.fv : Multiset (Var 0)) := by
  simp [rngFv]
@[simp] theorem rngFv_credit : rngFv {.credit k} = 0 := by simp [rngFv]

@[simp] theorem dom_zero : dom 0 = 0 := by simp [dom]
@[simp] theorem dom_add : dom (H₁ + H₂) = dom H₁ + dom H₂ := by simp [dom]
@[simp] theorem dom_bind : dom {.bind x n o} = {x} := by simp [dom]
@[simp] theorem dom_credit : dom {.credit k} = 0 := by simp [dom]

@[simp] theorem rc_cons_bind : rc (.bind x n o ::ₘ H) y = (if x = y then n else 0) + rc H y := by
  simp [rc]
@[simp] theorem rc_cons_credit : rc (.credit k ::ₘ H) y = rc H y := by simp [rc]
@[simp] theorem rngFv_cons_bind : rngFv (.bind x n o ::ₘ H) = (o.fv : Multiset (Var 0)) + rngFv H := by
  simp [rngFv]
@[simp] theorem rngFv_cons_credit : rngFv (.credit k ::ₘ H) = rngFv H := by simp [rngFv]
@[simp] theorem dom_cons_bind : dom (.bind x n o ::ₘ H) = x ::ₘ dom H := by simp [dom]
@[simp] theorem dom_cons_credit : dom (.credit k ::ₘ H) = dom H := by simp [dom]

@[simp] theorem ncred_zero : ncred 0 k = 0 := by simp [ncred]
@[simp] theorem ncred_cons_bind : ncred (.bind x n o ::ₘ H) k = ncred H k := by simp [ncred]
@[simp] theorem ncred_cons_credit {j : Nat} :
    ncred (.credit j ::ₘ H) k = (if j = k then 1 else 0) + ncred H k := by simp [ncred]

theorem mem_of_ncred (h : 0 < ncred H k) : HCell.credit k ∈ H := by
  induction H using Multiset.induction_on with
  | empty => simp at h
  | cons a H ih =>
    cases a with
    | bind x n o => simp only [ncred_cons_bind] at h; exact Multiset.mem_cons_of_mem (ih h)
    | credit j =>
      simp only [ncred_cons_credit] at h
      by_cases hj : j = k
      · subst hj; simp
      · simp only [hj, if_false, zero_add] at h; exact Multiset.mem_cons_of_mem (ih h)

theorem refs_add : refs (H₁ + H₂) y = refs H₁ y + refs H₂ y := by simp [refs]
@[simp] theorem refs_cons_bind : refs (.bind x n o ::ₘ H) y = o.fv.count y + refs H y := by
  simp [refs]
@[simp] theorem refs_cons_credit : refs (.credit k ::ₘ H) y = refs H y := by simp [refs]

theorem mem_dom_iff : y ∈ H.dom ↔ ∃ n o, HCell.bind y n o ∈ H := by
  induction H using Multiset.induction_on with
  | empty => simp
  | cons a H ih =>
    cases a with
    | bind x n o =>
      simp only [dom_cons_bind, Multiset.mem_cons, ih]
      constructor
      · rintro (rfl | ⟨n', o', h⟩)
        · exact ⟨n, o, by simp⟩
        · exact ⟨n', o', by simp [h]⟩
      · rintro ⟨n', o', h⟩
        simp only [Multiset.mem_cons, HCell.bind.injEq] at h
        rcases h with ⟨rfl, -, -⟩ | h
        · exact .inl rfl
        · exact .inr ⟨n', o', h⟩
    | credit k =>
      simp only [dom_cons_credit, ih]
      constructor
      · rintro ⟨n', o', h⟩; exact ⟨n', o', by simp [h]⟩
      · rintro ⟨n', o', h⟩
        simp only [Multiset.mem_cons, reduceCtorEq, false_or] at h
        exact ⟨n', o', h⟩

theorem rc_eq_zero (h : y ∉ H.dom) : rc H y = 0 := by
  induction H using Multiset.induction_on with
  | empty => simp
  | cons a H ih =>
    cases a with
    | bind x n o =>
      simp only [dom_cons_bind, Multiset.mem_cons, not_or] at h
      simp [Ne.symm h.1, ih h.2]
    | credit k => simp only [dom_cons_credit] at h; simp [ih h]

theorem rc_of_mem (hnd : H.dom.Nodup) (h : HCell.bind y n o ∈ H) : rc H y = n := by
  obtain ⟨H', rfl⟩ := Multiset.exists_cons_of_mem h
  simp only [dom_cons_bind, Multiset.nodup_cons] at hnd
  simp [rc_eq_zero hnd.1]

/-! ## Counting roots -/

/-- The roots of `H` for a given count of references `r`. -/
noncomputable def rootsW (r : Var 0 → Nat) (H : Heap) : Ctx 0 :=
  open Classical in
  H.bind fun
    | .bind x n _ => Multiset.replicate (n - r x) (Res.var x)
    | .credit k => if k = 0 then 0 else {Res.credit k}

theorem roots_eq_rootsW (H : Heap) : H.roots = rootsW (refs H) H := rfl

theorem rootsW_cons_bind (r : Var 0 → Nat) :
    rootsW r (.bind x n o ::ₘ H) = Multiset.replicate (n - r x) (Res.var x) + rootsW r H := by
  simp [rootsW]

theorem rootsW_cons_credit (r : Var 0 → Nat) :
    rootsW r (.credit k ::ₘ H) = (if k = 0 then 0 else {Res.credit k}) + rootsW r H := by
  simp [rootsW]

theorem count_rootsW_var (r : Var 0 → Nat) (hnd : H.dom.Nodup) (y : Var 0) :
    (rootsW r H).count (.var y) = rc H y - r y := by
  induction H using Multiset.induction_on with
  | empty => simp [rootsW, rc]
  | cons a H ih =>
    cases a with
    | bind x n o =>
      simp only [dom_cons_bind, Multiset.nodup_cons] at hnd
      rw [rootsW_cons_bind, Multiset.count_add, ih hnd.2, Multiset.count_replicate, rc_cons_bind]
      by_cases hxy : x = y
      · subst hxy; simp [rc_eq_zero hnd.1]
      · simp [hxy]
    | credit k =>
      simp only [dom_cons_credit] at hnd
      rw [rootsW_cons_credit, Multiset.count_add, ih hnd, rc_cons_credit]
      split <;> simp

theorem count_rootsW_credit (r : Var 0 → Nat) (k : Nat) :
    (rootsW r H).count (.credit k) = if k = 0 then 0 else ncred H k := by
  induction H using Multiset.induction_on with
  | empty => simp [rootsW]
  | cons a H ih =>
    cases a with
    | bind x n o =>
      rw [rootsW_cons_bind, Multiset.count_add, ih]
      simp [Multiset.count_replicate]
    | credit j =>
      rw [rootsW_cons_credit, Multiset.count_add, ih, ncred_cons_credit]
      split_ifs <;> simp_all [Multiset.count_singleton] <;> omega

theorem count_rootsW_alloc (r : Var 0 → Nat) : (rootsW r H).count .alloc = 0 := by
  induction H using Multiset.induction_on with
  | empty => simp [rootsW]
  | cons a H ih =>
    cases a with
    | bind x n o => rw [rootsW_cons_bind, Multiset.count_add, ih]; simp [Multiset.count_replicate]
    | credit j => rw [rootsW_cons_credit, Multiset.count_add, ih]; split <;> simp

theorem count_roots_var (hnd : H.dom.Nodup) (y : Var 0) :
    H.roots.count (.var y) = rc H y - refs H y :=
  count_rootsW_var _ hnd y

theorem count_roots_credit (k : Nat) :
    H.roots.count (.credit k) = if k = 0 then 0 else ncred H k :=
  count_rootsW_credit _ k

theorem count_roots_alloc : H.roots.count .alloc = 0 := count_rootsW_alloc _

/-! ## Linear heaps -/

theorem Linear.nodup (h : H.Linear) : H.dom.Nodup := h.1.1

theorem Linear.refs_le (h : H.Linear) (y : Var 0) : refs H y ≤ rc H y := by
  by_cases hy : y ∈ H.dom
  · obtain ⟨n, o, hc⟩ := mem_dom_iff.mp hy
    rw [rc_of_mem h.nodup hc]; exact h.2 y n o hc
  · have : refs H y = 0 := by
      unfold refs; rw [Multiset.count_eq_zero]; exact fun h' => hy (h.1.2.2 y h')
    omega

theorem Linear.mem_dom_of_refs (h : H.Linear) (hy : 0 < refs H y) : y ∈ H.dom :=
  h.1.2.2 y (Multiset.count_pos.mp hy)

theorem mem_dom_of_rc (hy : 0 < rc H y) : y ∈ H.dom := by
  by_contra h; rw [rc_eq_zero h] at hy; omega

theorem Linear.mem_dom_of_root (h : H.Linear) (hy : Res.var y ∈ H.roots) : y ∈ H.dom := by
  have := Multiset.count_pos.mpr hy
  rw [count_roots_var h.nodup] at this
  exact mem_dom_of_rc (by omega)

theorem credit_mem_of_root (hk : Res.credit k ∈ H.roots) : HCell.credit k ∈ H := by
  have := Multiset.count_pos.mpr hk
  rw [count_roots_credit] at this
  split at this
  · omega
  · exact mem_of_ncred this

theorem credit_root_ne_zero (hk : Res.credit k ∈ H.roots) : k ≠ 0 := by
  have := Multiset.count_pos.mpr hk
  rw [count_roots_credit] at this
  split at this <;> omega

/-- Linearity, cell by cell. -/
theorem linear_of (hnd : H.dom.Nodup) (hpos : ∀ x n o, HCell.bind x n o ∈ H → 1 ≤ n)
    (hrc : ∀ y, refs H y ≤ rc H y) : H.Linear := by
  refine ⟨⟨hnd, hpos, fun y hy => ?_⟩, fun y n o hc => ?_⟩
  · have := hrc y
    have h1 : 0 < refs H y := Multiset.count_pos.mpr hy
    exact mem_dom_of_rc (by omega)
  · have := hrc y; rw [rc_of_mem hnd hc] at this; exact this

/-! ## Incrementing a reference count -/

theorem inc_linear (h : Linear ({HCell.bind x n o} + H)) :
    Linear ({HCell.bind x (n + 1) o} + H) := by
  simp only [Multiset.singleton_add] at h ⊢
  refine linear_of ?_ ?_ ?_
  · simpa using h.nodup
  · intro z m p hc
    simp only [Multiset.mem_cons, HCell.bind.injEq] at hc
    rcases hc with ⟨rfl, rfl, rfl⟩ | hc
    · omega
    · exact h.1.2.1 z m p (by simp [hc])
  · intro z
    have := h.refs_le z
    simp only [refs_cons_bind, rc_cons_bind] at this ⊢
    split at this <;> simp_all <;> omega

theorem roots_inc (h : Linear ({HCell.bind x n o} + H)) :
    Heap.roots ({HCell.bind x (n + 1) o} + H) = Heap.roots ({HCell.bind x n o} + H) + {Res.var x} := by
  have h' := inc_linear h
  simp only [Multiset.singleton_add] at h h' ⊢
  ext r
  cases r with
  | var z =>
    rw [Multiset.count_add, count_roots_var h'.nodup, count_roots_var h.nodup]
    have := h.refs_le z
    simp only [refs_cons_bind, rc_cons_bind, Multiset.count_singleton, Res.var.injEq] at this ⊢
    by_cases hz : x = z
    · subst hz; simp at this ⊢; omega
    · simp [hz, Ne.symm hz]
  | credit j => simp [Multiset.count_add, count_roots_credit]
  | alloc => simp [Multiset.count_add, count_roots_alloc]

/-! ## Decrementing a shared reference count -/

theorem dec_linear (h : Linear ({HCell.bind x (n + 2) o} + H))
    (hx : Res.var x ∈ Heap.roots ({HCell.bind x (n + 2) o} + H)) :
    Linear ({HCell.bind x (n + 1) o} + H) := by
  simp only [Multiset.singleton_add] at h hx ⊢
  have hr := Multiset.count_pos.mpr hx
  rw [count_roots_var h.nodup] at hr
  refine linear_of ?_ ?_ ?_
  · simpa using h.nodup
  · intro z m p hc
    simp only [Multiset.mem_cons, HCell.bind.injEq] at hc
    rcases hc with ⟨rfl, rfl, rfl⟩ | hc
    · omega
    · exact h.1.2.1 z m p (by simp [hc])
  · intro z
    have := h.refs_le z
    simp only [refs_cons_bind, rc_cons_bind] at this hr ⊢
    by_cases hz : x = z
    · subst hz; simp at this hr ⊢; omega
    · simp [hz] at this ⊢; omega

theorem roots_dec (h : Linear ({HCell.bind x (n + 2) o} + H))
    (hx : Res.var x ∈ Heap.roots ({HCell.bind x (n + 2) o} + H)) :
    Heap.roots ({HCell.bind x (n + 1) o} + H) + {Res.var x} =
      Heap.roots ({HCell.bind x (n + 2) o} + H) := by
  have h' := dec_linear h hx
  simp only [Multiset.singleton_add] at h h' hx ⊢
  have hr := Multiset.count_pos.mpr hx
  rw [count_roots_var h.nodup] at hr
  ext r
  cases r with
  | var z =>
    rw [Multiset.count_add, count_roots_var h'.nodup, count_roots_var h.nodup]
    simp only [refs_cons_bind, rc_cons_bind, Multiset.count_singleton, Res.var.injEq] at hr ⊢
    by_cases hz : x = z
    · subst hz; simp at hr ⊢; omega
    · simp [hz, Ne.symm hz]
  | credit j => simp [Multiset.count_add, count_roots_credit]
  | alloc => simp [Multiset.count_add, count_roots_alloc]

/-! ## Freeing a unique cell -/

theorem fvCtx_count (o : HObj) (z : Var 0) : o.fvCtx.count (.var z) = o.fv.count z := by
  simp only [HObj.fvCtx, Multiset.coe_count]
  rw [List.count_map_of_injective _ _ (fun a b h => by cases h; rfl)]

theorem fvCtx_count_credit (o : HObj) (j : Nat) : o.fvCtx.count (.credit j) = 0 := by
  simp [HObj.fvCtx, List.count_eq_zero]

theorem fvCtx_count_alloc (o : HObj) : o.fvCtx.count .alloc = 0 := by
  simp [HObj.fvCtx, List.count_eq_zero]

theorem free_refs (h : Linear ({HCell.bind x 1 o} + H))
    (hx : Res.var x ∈ Heap.roots ({HCell.bind x 1 o} + H)) :
    refs ({HCell.bind x 1 o} + H) x = 0 := by
  simp only [Multiset.singleton_add] at h hx ⊢
  have hr := Multiset.count_pos.mpr hx
  rw [count_roots_var h.nodup] at hr
  have hnd := h.nodup
  simp only [dom_cons_bind, Multiset.nodup_cons] at hnd
  simp [rc_eq_zero hnd.1] at hr ⊢
  omega

theorem free_linear (h : Linear ({HCell.bind x 1 o} + H))
    (hx : Res.var x ∈ Heap.roots ({HCell.bind x 1 o} + H)) : Linear H := by
  have h0 := free_refs h hx
  simp only [Multiset.singleton_add] at h hx h0
  have hnd := h.nodup
  simp only [dom_cons_bind, Multiset.nodup_cons] at hnd
  refine linear_of hnd.2 (fun z m p hc => h.1.2.1 z m p (by simp [hc])) (fun z => ?_)
  have := h.refs_le z
  simp only [refs_cons_bind, rc_cons_bind] at this h0
  by_cases hz : x = z
  · subst hz; omega
  · simp [hz] at this; omega

theorem roots_free (h : Linear ({HCell.bind x 1 o} + H))
    (hx : Res.var x ∈ Heap.roots ({HCell.bind x 1 o} + H)) :
    Heap.roots H + {Res.var x} = Heap.roots ({HCell.bind x 1 o} + H) + o.fvCtx := by
  have h0 := free_refs h hx
  have h' := free_linear h hx
  simp only [Multiset.singleton_add] at h hx h0 ⊢
  have hnd := h.nodup
  simp only [dom_cons_bind, Multiset.nodup_cons] at hnd
  ext r
  cases r with
  | var z =>
    rw [Multiset.count_add, Multiset.count_add, count_roots_var h'.nodup,
      count_roots_var h.nodup, fvCtx_count]
    have hle := h.refs_le z
    have hle' := h'.refs_le z
    simp only [refs_cons_bind, rc_cons_bind, Multiset.count_singleton, Res.var.injEq]
      at h0 hle ⊢
    by_cases hz : x = z
    · subst hz; simp [rc_eq_zero hnd.1] at hle' ⊢; omega
    · simp [hz, Ne.symm hz] at hle ⊢; omega
  | credit j =>
    simp [Multiset.count_add, count_roots_credit, fvCtx_count_credit]
  | alloc => simp [Multiset.count_add, count_roots_alloc, fvCtx_count_alloc]

/-! ## Allocating a fresh cell -/

theorem alloc_linear (h : H.Linear) (hx : x ∉ H.dom) (hfv : o.fvCtx ≤ H.roots) :
    Linear ({HCell.bind x 1 o} + H) := by
  simp only [Multiset.singleton_add]
  refine linear_of ?_ ?_ ?_
  · simp [Multiset.nodup_cons, hx, h.nodup]
  · intro z m p hc
    simp only [Multiset.mem_cons, HCell.bind.injEq] at hc
    rcases hc with ⟨rfl, rfl, rfl⟩ | hc
    · exact le_rfl
    · exact h.1.2.1 z m p hc
  · intro z
    have hle := h.refs_le z
    have hc := (Multiset.le_iff_count.mp hfv) (.var z)
    rw [count_roots_var h.nodup, fvCtx_count] at hc
    simp only [refs_cons_bind, rc_cons_bind]
    by_cases hz : x = z
    · subst hz
      have : rc H x = 0 := rc_eq_zero hx
      simp; omega
    · simp [hz]; omega

theorem roots_alloc (h : H.Linear) (hx : x ∉ H.dom) (hfv : o.fvCtx ≤ H.roots) :
    Heap.roots ({HCell.bind x 1 o} + H) + o.fvCtx = H.roots + {Res.var x} := by
  have h' := alloc_linear h hx hfv
  simp only [Multiset.singleton_add] at h' ⊢
  ext r
  cases r with
  | var z =>
    have hle := h.refs_le z
    have hc := (Multiset.le_iff_count.mp hfv) (.var z)
    rw [count_roots_var h.nodup, fvCtx_count] at hc
    rw [Multiset.count_add, Multiset.count_add, count_roots_var h'.nodup,
      count_roots_var h.nodup, fvCtx_count]
    simp only [refs_cons_bind, rc_cons_bind, Multiset.count_singleton, Res.var.injEq]
    by_cases hz : x = z
    · subst hz
      have : rc H x = 0 := rc_eq_zero hx
      simp; omega
    · simp [hz, Ne.symm hz]; omega
  | credit j =>
    simp [Multiset.count_add, count_roots_credit, fvCtx_count_credit]
  | alloc => simp [Multiset.count_add, count_roots_alloc, fvCtx_count_alloc]

/-! ## Reuse credits -/

theorem credit_linear (h : H.Linear) (k : Nat) : Linear ({HCell.credit k} + H) := by
  simp only [Multiset.singleton_add]
  refine linear_of (by simpa using h.nodup) (fun z m p hc => ?_) (fun z => ?_)
  · simp only [Multiset.mem_cons, reduceCtorEq, false_or] at hc
    exact h.1.2.1 z m p hc
  · simpa using h.refs_le z

theorem linear_of_credit (h : Linear ({HCell.credit k} + H)) : H.Linear := by
  simp only [Multiset.singleton_add] at h
  refine linear_of (by simpa using h.nodup) (fun z m p hc => h.1.2.1 z m p (by simp [hc]))
    (fun z => ?_)
  simpa using h.refs_le z

theorem roots_credit (h : H.Linear) (k : Nat) :
    Heap.roots ({HCell.credit k} + H) = nzCtx {Res.credit k} + H.roots := by
  have h' := credit_linear h k
  simp only [Multiset.singleton_add] at h' ⊢
  ext r
  cases r with
  | var z =>
    rw [Multiset.count_add, count_roots_var h'.nodup, count_roots_var h.nodup]
    by_cases hk : k = 0
    · subst hk; simp
    · rw [nzCtx_credit hk]; simp
  | credit j =>
    rw [Multiset.count_add, count_roots_credit, count_roots_credit, ncred_cons_credit]
    by_cases hk : k = 0
    · subst hk
      by_cases hj : j = 0
      · subst hj; simp
      · simp [hj, Ne.symm hj]
    · rw [nzCtx_credit hk]
      by_cases hj : j = 0
      · subst hj; simp [hk, Ne.symm hk, Multiset.count_singleton]
      · by_cases hkj : k = j
        · subst hkj; simp [hj]
        · simp [hj, hkj, Ne.symm hkj, Multiset.count_singleton]
  | alloc =>
    rw [Multiset.count_add, count_roots_alloc, count_roots_alloc]
    by_cases hk : k = 0
    · subst hk; simp
    · rw [nzCtx_credit hk]; simp

end Heap

end FIP.Lam
