module

public import RequestProject.FIP.SubstFacts

@[expose] public section

/-!
# Invariants of stores (Appendix B.1–B.2)

* `Store.Ptr`: the shape of the paper's stores `S ::= ∅ | S, x ↦ Cᵏ x₁ … xₖ | S, ⋄k`:
  locations are bound to constructors applied to locations;
* `Store.Reads S σ`: `σ` assigns to every location of `S` the (closed) value it denotes,
  i.e. `σ` is the substitution `[S]`;
* how the roots of a store change when a cell is added or removed;
* splitting a linear store along a partition of its roots.
-/

namespace FIP

/-- A cell of the paper's stores: a location bound to a constructor applied to locations,
    or a reuse credit. -/
def Cell.Ptr : Cell → Prop
  | .bind x _ as => (∃ n, x = .loc n) ∧ ∀ a ∈ as, ∃ m, a = .var (.loc m)
  | .credit _ => True

namespace Store

/-- The store has the shape of the paper's stores. -/
def Ptr (S : Store) : Prop := ∀ c ∈ S, c.Ptr

/-- `σ` is the substitution `[S]`: it maps every location bound in `S` to the closed value
    it denotes. -/
def Reads (S : Store) (σ : Nat → Option Val) : Prop :=
  LocClosed σ ∧
    ∀ n c as, Cell.bind (.loc n) c as ∈ S → σ n = some (.ctor c (as.map (Val.substLoc σ)))

theorem Ptr.mono {S T : Store} (h : T.Ptr) (hle : S ≤ T) : S.Ptr :=
  fun c hc => h c (Multiset.mem_of_le hle hc)

theorem Reads.mono {S T : Store} {σ : Nat → Option Val} (h : T.Reads σ) (hle : S ≤ T) :
    S.Reads σ :=
  ⟨h.1, fun n c as hc => h.2 n c as (Multiset.mem_of_le hle hc)⟩

theorem Ptr.add {S T : Store} (hS : S.Ptr) (hT : T.Ptr) : (S + T).Ptr := by
  intro c hc
  rcases Multiset.mem_add.mp hc with hc | hc
  · exact hS c hc
  · exact hT c hc

theorem mem_dom {S : Store} {x : Var} : x ∈ S.dom ↔ ∃ c as, Cell.bind x c as ∈ S := by
  simp only [dom, Multiset.mem_bind]
  constructor
  · rintro ⟨cell, hc, hx⟩
    cases cell with
    | bind y c as =>
      simp only [Cell.dom, Multiset.mem_singleton] at hx
      subst hx; exact ⟨c, as, hc⟩
    | credit k => simp [Cell.dom] at hx
  · rintro ⟨c, as, h⟩
    exact ⟨_, h, by simp [Cell.dom]⟩

theorem mem_rngFv {S : Store} {x : Var} :
    x ∈ S.rngFv ↔ ∃ y c as, Cell.bind y c as ∈ S ∧ x ∈ Val.fvList as := by
  simp only [rngFv, Multiset.mem_bind]
  constructor
  · rintro ⟨cell, hc, hx⟩
    cases cell with
    | bind y c as =>
      simp only [Cell.fv, Multiset.mem_coe] at hx
      exact ⟨y, c, as, hc, hx⟩
    | credit k => simp [Cell.fv] at hx
  · rintro ⟨y, c, as, h, hx⟩
    exact ⟨_, h, by simpa [Cell.fv] using hx⟩

theorem Ptr.dom_loc {S : Store} (h : S.Ptr) {x : Var} (hx : x ∈ S.dom) : ∃ n, x = .loc n := by
  obtain ⟨c, as, hc⟩ := mem_dom.mp hx
  exact (h _ hc).1

theorem Ptr.args {S : Store} (h : S.Ptr) {x : Var} {c : CName} {as : List Val}
    (hc : Cell.bind x c as ∈ S) : ∀ a ∈ as, ∃ m, a = .var (.loc m) :=
  (h _ hc).2

theorem Ptr.args_vars {S : Store} (h : S.Ptr) {x : Var} {c : CName} {as : List Val}
    (hc : Cell.bind x c as ∈ S) : as = (Val.fvList as).map Val.var := by
  have := h.args hc
  clear hc
  induction as with
  | nil => rfl
  | cons a as ih =>
    obtain ⟨m, rfl⟩ := this a List.mem_cons_self
    simp only [Val.fvList, Val.fv, List.singleton_append, List.map_cons, List.cons.injEq,
      true_and]
    exact ih (fun b hb => this b (List.mem_cons_of_mem _ hb))

theorem exists_fresh (S : Store) : ∃ n, Var.loc n ∉ S.dom := by
  by_contra h
  push_neg at h
  have hinj : Set.InjOn (fun n => Var.loc n) Set.univ := fun a _ b _ h => by injection h
  have : (Set.univ : Set Nat).Finite :=
    Set.Finite.of_finite_image (s := Set.univ) (f := fun n => Var.loc n)
      ((S.dom.toFinset.finite_toSet).subset (by
        rintro _ ⟨n, -, rfl⟩; simpa using h n)) hinj
  exact Set.infinite_univ this

/-! ## Roots -/

theorem mem_roots_var {S : Store} {x : Var} : Res.var x ∈ S.roots ↔ x ∈ S.dom ∧ x ∉ S.rngFv := by
  simp only [roots, Multiset.mem_add, Multiset.mem_map, Multiset.mem_filter, Res.var.injEq,
    Multiset.mem_bind]
  constructor
  · rintro (⟨y, ⟨h1, h2⟩, rfl⟩ | ⟨c, _, hc⟩)
    · exact ⟨h1, h2⟩
    · cases c with
      | bind => simp [Cell.credits] at hc
      | credit k => by_cases hk : k = 0 <;> simp [Cell.credits, hk] at hc
  · rintro ⟨h1, h2⟩; exact .inl ⟨x, ⟨h1, h2⟩, rfl⟩

theorem mem_roots_credit {S : Store} {k : Nat} :
    Res.credit k ∈ S.roots ↔ k ≠ 0 ∧ Cell.credit k ∈ S := by
  simp only [roots, Multiset.mem_add, Multiset.mem_map, Multiset.mem_bind, reduceCtorEq,
    and_false, exists_false, false_or]
  constructor
  · rintro ⟨c, hc, hk⟩
    cases c with
    | bind => simp [Cell.credits] at hk
    | credit j =>
      by_cases hj : j = 0
      · simp [Cell.credits, hj] at hk
      · simp only [Cell.credits, hj, if_false, Multiset.mem_singleton, Res.credit.injEq] at hk
        subst hk; exact ⟨hj, hc⟩
  · rintro ⟨hk, hc⟩; exact ⟨_, hc, by simp [Cell.credits, hk]⟩

theorem alloc_not_mem_roots (S : Store) : Res.alloc ∉ S.roots := by
  simp only [roots, Multiset.mem_add, Multiset.mem_map, Multiset.mem_bind, reduceCtorEq,
    and_false, exists_false, false_or, not_exists, not_and]
  intro c _
  cases c with
  | bind => simp [Cell.credits]
  | credit j => by_cases hj : j = 0 <;> simp [Cell.credits, hj]

theorem credit_zero_not_mem_roots (S : Store) : Res.credit 0 ∉ S.roots := by
  simp [mem_roots_credit]

theorem roots_credit (k : Nat) (T : Store) :
    roots ({Cell.credit k} + T) = roots T + Cell.credits (.credit k) := by
  simp only [roots, dom_add, dom_singleton, Cell.dom, zero_add, rngFv_add, rngFv_singleton,
    Cell.fv, Multiset.add_bind, Multiset.singleton_bind]
  abel

theorem dom_bind_add (x : Var) (c : CName) (as : List Val) (T : Store) :
    dom ({Cell.bind x c as} + T) = x ::ₘ T.dom := by simp [Cell.dom]
theorem rngFv_bind_add (x : Var) (c : CName) (as : List Val) (T : Store) :
    rngFv ({Cell.bind x c as} + T) = (Val.fvList as : Multiset Var) + T.rngFv := by
  simp [Cell.fv]
theorem credits_bind_add (x : Var) (c : CName) (as : List Val) (T : Store) :
    ({Cell.bind x c as} + T).bind Cell.credits = T.bind Cell.credits := by simp [Cell.credits]
theorem dom_credit_add (k : Nat) (T : Store) : dom ({Cell.credit k} + T) = T.dom := by
  simp [Cell.dom]
theorem rngFv_credit_add (k : Nat) (T : Store) : rngFv ({Cell.credit k} + T) = T.rngFv := by
  simp [Cell.fv]

theorem roots_bind {T : Store} {x : Var} {c : CName} {as : List Val} (hTd : T.dom.Nodup)
    (hx : x ∉ T.dom) (hxr : x ∉ T.rngFv)
    (has : ∀ a ∈ Val.fvList as, a ∈ T.dom ∧ a ∉ T.rngFv) (hnd : (Val.fvList as).Nodup) :
    roots ({Cell.bind x c as} + T) + ((Val.fvList as : Multiset Var)).map Res.var =
      roots T + {Res.var x} := by
  classical
  set A : Multiset Var := (Val.fvList as : Multiset Var) with hA
  have hxA : x ∉ A := fun h => hx (has x h).1
  set F := T.dom.filter (· ∉ T.rngFv) with hF
  have h1 : F.filter (· ∈ A) = A := by
    refine (Multiset.Nodup.ext (Multiset.Nodup.filter _ (Multiset.Nodup.filter _ hTd))
      (by simpa [hA] using hnd)).mpr fun a => ?_
    simp only [Multiset.mem_filter]
    constructor
    · rintro ⟨-, h⟩; exact h
    · intro h; exact ⟨⟨(has a h).1, (has a h).2⟩, h⟩
  have h2 : F.filter (fun a => ¬ a ∈ A) = T.dom.filter (· ∉ A + T.rngFv) := by
    rw [hF, Multiset.filter_filter]
    congr 1
    ext a
    simp only [Multiset.mem_add, not_or]
  have key : F = T.dom.filter (· ∉ A + T.rngFv) + A := by
    conv_lhs => rw [← Multiset.filter_add_not (· ∈ A) F]
    rw [h1, h2, add_comm]
  unfold roots
  rw [dom_bind_add, rngFv_bind_add, credits_bind_add, ← hA, ← hF, key,
    Multiset.filter_cons_of_pos _ (by simp only [Multiset.mem_add, not_or]; exact ⟨hxA, hxr⟩)]
  simp only [Multiset.map_cons, Multiset.map_add, Multiset.cons_add]
  rw [← Multiset.singleton_add]
  abel

theorem linear_bind {T : Store} {x : Var} {c : CName} {as : List Val} (hT : T.Linear)
    (hx : x ∉ T.dom) (has : ∀ a ∈ Val.fvList as, a ∈ T.dom ∧ a ∉ T.rngFv)
    (hnd : (Val.fvList as).Nodup) : Linear ({Cell.bind x c as} + T) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [dom_bind_add, Multiset.nodup_cons]
    exact ⟨hx, hT.1.1⟩
  · intro y hy
    rw [rngFv_bind_add, Multiset.mem_add, Multiset.mem_coe] at hy
    rw [dom_bind_add, Multiset.mem_cons]
    rcases hy with hy | hy
    · exact .inr (has y hy).1
    · exact .inr (hT.1.2 y hy)
  · rw [rngFv_bind_add]
    refine Multiset.nodup_add.mpr ⟨by simpa using hnd, hT.2, ?_⟩
    exact Multiset.disjoint_left.mpr fun {a} ha => (has a (by simpa using ha)).2

theorem linear_credit {T : Store} (k : Nat) (hT : T.Linear) : Linear ({Cell.credit k} + T) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [dom_credit_add]; exact hT.1.1
  · intro y hy; rw [rngFv_credit_add] at hy; rw [dom_credit_add]; exact hT.1.2 y hy
  · rw [rngFv_credit_add]; exact hT.2

theorem linear_of_credit {T : Store} {k : Nat} (h : Linear ({Cell.credit k} + T)) : T.Linear := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have := h.1.1; rwa [dom_credit_add] at this
  · intro y hy
    have := h.1.2 y (by rw [rngFv_credit_add]; exact hy)
    rwa [dom_credit_add] at this
  · have := h.2; rwa [rngFv_credit_add] at this

/-- Removing a root cell from a linear store: the rest is linear, and the arguments of the
    removed cell become roots. -/
theorem remove_root {R : Store} {x : Var} {c : CName} {as : List Val}
    (h : Linear ({Cell.bind x c as} + R)) (hx : x ∉ rngFv ({Cell.bind x c as} + R)) :
    R.Linear ∧ x ∉ R.dom ∧ x ∉ R.rngFv ∧
      (∀ a ∈ Val.fvList as, a ∈ R.dom ∧ a ∉ R.rngFv) ∧ (Val.fvList as).Nodup := by
  rw [rngFv_bind_add, Multiset.mem_add, Multiset.mem_coe, not_or] at hx
  have hd := h.1.1
  rw [dom_bind_add, Multiset.nodup_cons] at hd
  have hr := h.2
  rw [rngFv_bind_add, Multiset.nodup_add, Multiset.coe_nodup] at hr
  have hs := h.1.2
  rw [rngFv_bind_add, dom_bind_add] at hs
  refine ⟨⟨⟨hd.2, fun y hy => ?_⟩, hr.2.1⟩, hd.1, hx.2, fun a ha => ⟨?_, ?_⟩, hr.1⟩
  · rcases Multiset.mem_cons.mp (hs y (Multiset.mem_add.mpr (.inr hy))) with rfl | h'
    · exact absurd hy hx.2
    · exact h'
  · rcases Multiset.mem_cons.mp (hs a (Multiset.mem_add.mpr (.inl (by simpa using ha)))) with
      rfl | h'
    · exact absurd ha hx.1
    · exact h'
  · exact Multiset.disjoint_left.mp hr.2.2 (by simpa using ha)

theorem roots_remove_root {R : Store} {x : Var} {c : CName} {as : List Val}
    (h : Linear ({Cell.bind x c as} + R)) (hx : x ∉ rngFv ({Cell.bind x c as} + R)) :
    roots ({Cell.bind x c as} + R) + ((Val.fvList as : Multiset Var)).map Res.var =
      roots R + {Res.var x} := by
  obtain ⟨hR, h1, h2, h3, h4⟩ := remove_root h hx
  exact roots_bind hR.1.1 h1 h2 h3 h4

/-- A root of a store is bound by a cell, which can be split off. -/
theorem exists_cell_of_root {S : Store} {x : Var} (h : Res.var x ∈ S.roots) :
    ∃ c as R, S = {Cell.bind x c as} + R := by
  obtain ⟨c, as, hc⟩ := mem_dom.mp (mem_roots_var.mp h).1
  obtain ⟨R, rfl⟩ := Multiset.exists_cons_of_mem hc
  exact ⟨c, as, R, by simp [Multiset.singleton_add]⟩

theorem exists_credit_of_root {S : Store} {k : Nat} (h : Res.credit k ∈ S.roots) :
    ∃ R, S = {Cell.credit k} + R := by
  obtain ⟨R, rfl⟩ := Multiset.exists_cons_of_mem (mem_roots_credit.mp h).2
  exact ⟨R, by simp [Multiset.singleton_add]⟩

/-! ## Splitting a linear store along its roots -/

/-- **Store splitting**: a linear store whose roots are `A + B` is the disjoint union of
    two linear stores with roots `A` and `B`. -/
theorem split {S : Store} (hS : S.Linear) {A B : Ctx} (hAB : S.roots = A + B) :
    ∃ Ta Tb, S = Ta + Tb ∧ Ta.roots = A ∧ Tb.roots = B ∧ Ta.Linear ∧ Tb.Linear := by
  induction hcard : Multiset.card S using Nat.strong_induction_on generalizing S A with
  | _ n ih =>
    subst hcard
    rcases Multiset.empty_or_exists_mem A with rfl | ⟨r, hr⟩
    · exact ⟨0, S, by simp, by simp [roots], by simpa using hAB, ⟨⟨by simp, by simp⟩, by simp⟩,
        hS⟩
    obtain ⟨A', rfl⟩ := Multiset.exists_cons_of_mem hr
    have hrS : r ∈ S.roots := by rw [hAB]; simp
    cases r with
    | alloc => exact absurd hrS (alloc_not_mem_roots S)
    | credit k =>
      obtain ⟨R, rfl⟩ := exists_credit_of_root hrS
      have hk : k ≠ 0 := (mem_roots_credit.mp hrS).1
      have hRr : R.roots = A' + B := by
        have := hAB
        rw [roots_credit] at this
        simp only [Cell.credits, hk, if_false] at this
        rw [Multiset.cons_add, ← Multiset.singleton_add, add_comm] at this
        exact add_left_cancel this
      obtain ⟨Ta, Tb, rfl, ha, hb, hla, hlb⟩ :=
        ih _ (by simp) (linear_of_credit hS) hRr rfl
      refine ⟨{Cell.credit k} + Ta, Tb, by rw [add_assoc], ?_, hb, linear_credit k hla, hlb⟩
      rw [roots_credit, ha]
      simp only [Cell.credits, hk, if_false]
      rw [add_comm, Multiset.singleton_add]
    | var x =>
      obtain ⟨c, as, R, rfl⟩ := exists_cell_of_root hrS
      have hxr : x ∉ rngFv ({Cell.bind x c as} + R) := (mem_roots_var.mp hrS).2
      obtain ⟨hR, h1, h2, h3, h4⟩ := remove_root hS hxr
      have hroots := roots_remove_root hS hxr
      set As : Multiset Res := ((Val.fvList as : Multiset Var)).map Res.var with hAs
      have hRr : R.roots = (A' + As) + B := by
        rw [hAB] at hroots
        have : R.roots + {Res.var x} = (A' + As + B) + {Res.var x} := by
          rw [← hroots]; simp only [Multiset.cons_add]
          rw [← Multiset.singleton_add]; abel
        exact add_right_cancel this
      obtain ⟨Ta, Tb, rfl, ha, hb, hla, hlb⟩ := ih _ (by simp) hR hRr rfl
      have hAsTa : ∀ a ∈ Val.fvList as, a ∈ Ta.dom ∧ a ∉ Ta.rngFv := by
        intro a ha'
        have : Res.var a ∈ Ta.roots := by rw [ha]; simp [hAs, ha']
        exact mem_roots_var.mp this
      have hxTa : x ∉ Ta.dom := fun h => h1 (by simp [h])
      have hxTar : x ∉ Ta.rngFv := fun h => h2 (by simp [h])
      refine ⟨{Cell.bind x c as} + Ta, Tb, by rw [add_assoc], ?_, hb,
        linear_bind hla hxTa hAsTa h4, hlb⟩
      have := roots_bind (c := c) hla.1.1 hxTa hxTar hAsTa h4
      rw [← hAs, ha] at this
      have : roots ({Cell.bind x c as} + Ta) + As = (Res.var x ::ₘ A') + As := by
        rw [this, Multiset.cons_add, ← Multiset.singleton_add]; abel
      exact add_right_cancel this

end Store

end FIP
