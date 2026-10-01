module

public import RequestProject.FIP.HeapFun

@[expose] public section

/-!
# The invariant of the proof of Theorem 6

The proof keeps a single heap `H` and accounts for every reference count:

* `H.cntM` contains each location `x ↦ⁿ φ` of `H` exactly `n` times;
* `H.rngFv` contains the references from the objects of the heap;
* `Γ` contains the references owned by the expression being evaluated;
* `R` contains the references held by the rest of the computation (the borrowed part of
  the heap in the paper, i.e. the roots of `H₁` in `H₁ ⊗ H₂`).

The invariant `HInv` requires `cntM H = R + Γ + rngFv H`: this is the statement of the
paper that `H` is linear with roots `R, Γ` (Lemma 49).  Likewise for the reuse credits.
`Heap.Reads H σ` states that `σ` is the substitution `[H]`.
-/

namespace FIP.Lam

/-- The value denoted by an object. -/
def HObj.toVal : HObj → LVal
  | .con c args => .ctor c args
  | .clo zs xs body => .lam zs xs body

/-- The substitution of values for locations given by `σ`. -/
def locS (σ : Nat → Option LVal) : LSubst := fun y =>
  match y with
  | .loc n => σ n
  | .name _ => none

namespace Heap

/-- Each location `x ↦ⁿ φ` of the heap, `n` times. -/
def cntM (H : Heap) : Multiset Var :=
  H.bind fun | .bind x n _ => Multiset.replicate n x | .credit _ => 0

/-- The sizes of the reuse credits of the heap. -/
def creditsM (H : Heap) : Multiset Nat :=
  H.bind fun | .bind _ _ _ => 0 | .credit k => {k}

/-- `σ` is the substitution `[H]`: it maps every location of `H` to the closed value it
    denotes. -/
structure Reads (H : Heap) (σ : Nat → Option LVal) : Prop where
  closed : ∀ l v, σ l = some v → v.dfv = []
  cell : ∀ l n o, HCell.bind (.loc l) n o ∈ H → σ l = some (o.toVal.subst (locS σ))

end Heap

/-- The non-empty reuse credits of an environment. -/
def Ctx.cr (Γ : Ctx) : Multiset Nat :=
  (Γ.bind fun | .credit k => {k} | _ => 0).filter (· ≠ 0)

/-- Discard the reuse credits of size `0`, which occupy no memory. -/
def nz (M : Multiset Nat) : Multiset Nat := M.filter (· ≠ 0)

/-- A well-formed object: a constructor applied to locations, or a closure whose captured
    variables are locations and whose body is well-formed and admissible. -/
def HObj.Ok (funs : List FName) : HObj → Prop
  | .con _ args => ∀ a ∈ args, a.IsLoc
  | .clo zs xs body => ∃ ls : List Nat, zs = ls.map (fun l => .var (.loc l)) ∧
      LWf funs ∅ (varCtx (ls.map .loc) + Binder.ctx xs) body ∧ body.Adm ∧
      (xs.map (·.name)).Nodup

/-- A well-formed cell: a location with a positive reference count bound to a
    well-formed object, or a reuse credit. -/
def HCell.Ok (funs : List FName) : HCell → Prop
  | .bind x n o => (∃ l, x = .loc l) ∧ 1 ≤ n ∧ o.Ok funs
  | .credit _ => True

/-- An environment of owned locations and reuse credits. -/
def Ctx.LocOnly (Γ : Ctx) : Prop := ∀ r ∈ Γ, (∃ l, r = .var (.loc l)) ∨ ∃ k, r = .credit k

/-- The invariant: `H` is a heap of the paper's shape whose reference counts are accounted
    for by the references `R` of the rest of the computation, the owned environment `Γ`
    and the references from the heap itself; its credits are `RC` and those of `Γ`; and
    `σ` is `[H]`. -/
structure HInv (funs : List FName) (H : Heap) (R : Multiset Var) (RC : Multiset Nat) (Γ : Ctx)
    (σ : Nat → Option LVal) : Prop where
  ok : ∀ c ∈ H, c.Ok funs
  nodup : H.dom.Nodup
  cnt : H.cntM = R + Ctx.vars Γ + H.rngFv
  cred : nz H.creditsM = RC + Ctx.cr Γ
  ctx : Ctx.LocOnly Γ
  reads : H.Reads σ

/-! ## Basic facts -/

namespace Heap

@[simp] theorem cntM_add (H₁ H₂ : Heap) : (H₁ + H₂).cntM = H₁.cntM + H₂.cntM := by
  simp [cntM]

@[simp] theorem cntM_bind (x : Var) (n : Nat) (o : HObj) :
    cntM {HCell.bind x n o} = Multiset.replicate n x := by simp [cntM]

@[simp] theorem cntM_credit (k : Nat) : cntM {HCell.credit k} = 0 := by simp [cntM]

@[simp] theorem cntM_zero : cntM 0 = 0 := by simp [cntM]

@[simp] theorem creditsM_add (H₁ H₂ : Heap) :
    (H₁ + H₂).creditsM = H₁.creditsM + H₂.creditsM := by simp [creditsM]

@[simp] theorem creditsM_bind (x : Var) (n : Nat) (o : HObj) :
    creditsM {HCell.bind x n o} = 0 := by simp [creditsM]

@[simp] theorem creditsM_credit (k : Nat) : creditsM {HCell.credit k} = {k} := by
  simp [creditsM]

@[simp] theorem rngFv_add (H₁ H₂ : Heap) : (H₁ + H₂).rngFv = H₁.rngFv + H₂.rngFv := by
  simp [rngFv]

@[simp] theorem rngFv_bind (x : Var) (n : Nat) (o : HObj) :
    rngFv {HCell.bind x n o} = (o.fv : Multiset Var) := by simp [rngFv]

@[simp] theorem rngFv_credit (k : Nat) : rngFv {HCell.credit k} = 0 := by simp [rngFv]

@[simp] theorem dom_add (H₁ H₂ : Heap) : (H₁ + H₂).dom = H₁.dom + H₂.dom := by simp [dom]

@[simp] theorem dom_bind (x : Var) (n : Nat) (o : HObj) :
    dom {HCell.bind x n o} = {x} := by simp [dom]

@[simp] theorem dom_credit (k : Nat) : dom {HCell.credit k} = 0 := by simp [dom]

@[simp] theorem dom_cons_bind (x : Var) (n : Nat) (o : HObj) (H : Heap) :
    dom (HCell.bind x n o ::ₘ H) = x ::ₘ dom H := by simp [dom]

@[simp] theorem dom_cons_credit (k : Nat) (H : Heap) : dom (HCell.credit k ::ₘ H) = dom H := by
  simp [dom]

@[simp] theorem cntM_cons_bind (x : Var) (n : Nat) (o : HObj) (H : Heap) :
    cntM (HCell.bind x n o ::ₘ H) = Multiset.replicate n x + cntM H := by simp [cntM]

@[simp] theorem cntM_cons_credit (k : Nat) (H : Heap) : cntM (HCell.credit k ::ₘ H) = cntM H := by
  simp [cntM]

@[simp] theorem creditsM_cons_bind (x : Var) (n : Nat) (o : HObj) (H : Heap) :
    creditsM (HCell.bind x n o ::ₘ H) = creditsM H := by simp [creditsM]

@[simp] theorem creditsM_cons_credit (k : Nat) (H : Heap) :
    creditsM (HCell.credit k ::ₘ H) = k ::ₘ creditsM H := by simp [creditsM]

@[simp] theorem rngFv_cons_bind (x : Var) (n : Nat) (o : HObj) (H : Heap) :
    rngFv (HCell.bind x n o ::ₘ H) = (o.fv : Multiset Var) + rngFv H := by simp [rngFv]

@[simp] theorem rngFv_cons_credit (k : Nat) (H : Heap) : rngFv (HCell.credit k ::ₘ H) = rngFv H := by
  simp [rngFv]

theorem mem_dom {H : Heap} {x : Var} : x ∈ H.dom ↔ ∃ n o, HCell.bind x n o ∈ H := by
  simp only [dom, Multiset.mem_bind]
  constructor
  · rintro ⟨c, hc, hx⟩
    cases c with
    | bind y n o => simp at hx; subst hx; exact ⟨n, o, hc⟩
    | credit k => simp at hx
  · rintro ⟨n, o, h⟩; exact ⟨_, h, by simp⟩

theorem mem_cntM {H : Heap} {x : Var} : x ∈ H.cntM ↔ ∃ n o, HCell.bind x n o ∈ H ∧ n ≠ 0 := by
  simp only [cntM, Multiset.mem_bind]
  constructor
  · rintro ⟨c, hc, hx⟩
    cases c with
    | bind y n o =>
      simp only [Multiset.mem_replicate] at hx
      obtain ⟨hn, rfl⟩ := hx
      exact ⟨n, o, hc, hn⟩
    | credit k => simp at hx
  · rintro ⟨n, o, h, hn⟩; exact ⟨_, h, Multiset.mem_replicate.mpr ⟨hn, rfl⟩⟩

theorem mem_creditsM {H : Heap} {k : Nat} : k ∈ H.creditsM ↔ HCell.credit k ∈ H := by
  simp only [creditsM, Multiset.mem_bind]
  constructor
  · rintro ⟨c, hc, hx⟩
    cases c with
    | bind y n o => simp at hx
    | credit k' => simp at hx; subst hx; exact hc
  · intro h; exact ⟨_, h, by simp⟩

theorem mem_rngFv {H : Heap} {x : Var} :
    x ∈ H.rngFv ↔ ∃ y n o, HCell.bind y n o ∈ H ∧ x ∈ o.fv := by
  simp only [rngFv, Multiset.mem_bind]
  constructor
  · rintro ⟨c, hc, hx⟩
    cases c with
    | bind y n o => exact ⟨y, n, o, hc, by simpa using hx⟩
    | credit k => simp at hx
  · rintro ⟨y, n, o, h, hx⟩; exact ⟨_, h, by simpa using hx⟩

theorem eq_add_of_mem {H : Heap} {c : HCell} (h : c ∈ H) : ∃ H₀, H = {c} + H₀ := by
  obtain ⟨t, ht⟩ := Multiset.exists_cons_of_mem h
  exact ⟨t, by rw [ht, Multiset.singleton_add]⟩

theorem Reads.mono {H H' : Heap} {σ : Nat → Option LVal} (h : H.Reads σ)
    (hle : ∀ l n o, HCell.bind (.loc l) n o ∈ H' → ∃ m, HCell.bind (.loc l) m o ∈ H) :
    H'.Reads σ := by
  refine ⟨h.closed, fun l n o hc => ?_⟩
  obtain ⟨m, hm⟩ := hle l n o hc
  exact h.cell l m o hm

end Heap

theorem nz_add (M N : Multiset Nat) : nz (M + N) = nz M + nz N := Multiset.filter_add _ _ _

theorem Ctx.cr_add (Γ Δ : Ctx) : Ctx.cr (Γ + Δ) = Ctx.cr Γ + Ctx.cr Δ := by
  simp [Ctx.cr, Multiset.filter_add]

@[simp] theorem Ctx.cr_var (x : Var) : Ctx.cr {Res.var x} = 0 := by simp [Ctx.cr]

@[simp] theorem Ctx.cr_credit (k : Nat) : Ctx.cr {Res.credit k} = nz {k} := by
  simp [Ctx.cr, nz]

@[simp] theorem Ctx.cr_alloc : Ctx.cr {Res.alloc} = 0 := by simp [Ctx.cr]

theorem Ctx.vars_add (Γ Δ : Ctx) : Ctx.vars (Γ + Δ) = Ctx.vars Γ + Ctx.vars Δ := by
  simp [Ctx.vars, Multiset.filterMap_add]

@[simp] theorem Ctx.vars_var (x : Var) : Ctx.vars {Res.var x} = {x} := rfl

@[simp] theorem Ctx.vars_credit (k : Nat) : Ctx.vars {Res.credit k} = 0 := rfl

@[simp] theorem Ctx.vars_alloc : Ctx.vars {Res.alloc} = 0 := rfl

@[simp] theorem Ctx.vars_zero : Ctx.vars 0 = 0 := by simp [Ctx.vars]

@[simp] theorem Ctx.cr_zero : Ctx.cr 0 = 0 := by simp [Ctx.cr]

theorem Ctx.vars_map_var (xs : Multiset Var) : Ctx.vars (xs.map Res.var) = xs := by
  induction xs using Multiset.induction_on with
  | empty => simp
  | cons x xs ih => simp [← Multiset.singleton_add, Ctx.vars_add, ih]

theorem Ctx.cr_map_var (xs : Multiset Var) : Ctx.cr (xs.map Res.var) = 0 := by
  induction xs using Multiset.induction_on with
  | empty => simp
  | cons x xs ih => simp [← Multiset.singleton_add, Ctx.cr_add, ih]

theorem Ctx.LocOnly.add {Γ Δ : Ctx} (h1 : Ctx.LocOnly Γ) (h2 : Ctx.LocOnly Δ) :
    Ctx.LocOnly (Γ + Δ) := by
  intro r hr
  rcases Multiset.mem_add.mp hr with hr | hr
  · exact h1 r hr
  · exact h2 r hr

theorem Ctx.LocOnly.of_le {Γ Δ : Ctx} (h : Ctx.LocOnly Δ) (hle : Γ ≤ Δ) : Ctx.LocOnly Γ :=
  fun r hr => h r (Multiset.mem_of_le hle hr)

theorem Ctx.LocOnly.left {Γ Δ : Ctx} (h : Ctx.LocOnly (Γ + Δ)) : Ctx.LocOnly Γ :=
  h.of_le (Multiset.le_add_right _ _)

theorem Ctx.LocOnly.right {Γ Δ : Ctx} (h : Ctx.LocOnly (Γ + Δ)) : Ctx.LocOnly Δ :=
  h.of_le (Multiset.le_add_left _ _)

theorem Ctx.LocOnly.credit (k : Nat) : Ctx.LocOnly {Res.credit k} := by
  intro r hr; simp at hr; exact .inr ⟨k, hr⟩

/-- The locations of a list of atomic values, as owned resources. -/
def locCtx (vs : List LVal) : Ctx := ((LVal.fvList vs : List Var) : Multiset Var).map Res.var

theorem locCtx_vars (vs : List LVal) : Ctx.vars (locCtx vs) = (LVal.fvList vs : Multiset Var) :=
  Ctx.vars_map_var _

theorem locCtx_cr (vs : List LVal) : Ctx.cr (locCtx vs) = 0 := Ctx.cr_map_var _

theorem fvList_loc {vs : List LVal} (h : ∀ v ∈ vs, v.IsLoc) :
    ∀ x ∈ LVal.fvList vs, ∃ l, x = .loc l := by
  intro x hx
  induction vs with
  | nil => simp [LVal.fvList] at hx
  | cons v vs ih =>
    simp only [LVal.fvList, List.mem_append] at hx
    rcases hx with hx | hx
    · obtain ⟨l, rfl⟩ := h v (by simp)
      simp [LVal.fv] at hx; exact ⟨l, hx⟩
    · exact ih (fun v hv => h v (by simp [hv])) hx

theorem locCtx_locOnly {vs : List LVal} (h : ∀ v ∈ vs, v.IsLoc) : Ctx.LocOnly (locCtx vs) := by
  intro r hr
  simp only [locCtx, Multiset.mem_map, Multiset.mem_coe] at hr
  obtain ⟨x, hx, rfl⟩ := hr
  obtain ⟨l, rfl⟩ := fvList_loc h x hx
  exact .inl ⟨l, rfl⟩

theorem locCtx_cons (l : Nat) (vs : List LVal) :
    locCtx (.var (.loc l) :: vs) = {Res.var (.loc l)} + locCtx vs := by
  simp [locCtx, LVal.fvList, LVal.fv]

theorem LVal.fvList_append (vs ws : List LVal) :
    LVal.fvList (vs ++ ws) = LVal.fvList vs ++ LVal.fvList ws := by
  induction vs with
  | nil => simp [LVal.fvList]
  | cons v vs ih => simp [LVal.fvList, ih]

theorem locCtx_append (vs ws : List LVal) : locCtx (vs ++ ws) = locCtx vs + locCtx ws := by
  simp [locCtx, LVal.fvList_append]

theorem locCtx_map (ys : List Var) : locCtx (ys.map .var) = ((ys : Multiset Var).map Res.var) := by
  simp only [locCtx]
  congr 2
  induction ys with
  | nil => simp [LVal.fvList]
  | cons y ys ih => simp [LVal.fvList, LVal.fv, ih]

/-! ## Facts about the invariant -/

namespace HInv

variable {funs : List FName} {H : Heap} {R : Multiset Var} {RC : Multiset Nat} {Γ : Ctx}
  {σ : Nat → Option LVal}

/-- Move references between the owned environment and the rest of the computation. -/
theorem shift (h : HInv funs H R RC Γ σ) {R' : Multiset Var} {RC' : Multiset Nat} {Γ' : Ctx}
    (hv : R + Ctx.vars Γ = R' + Ctx.vars Γ') (hc : RC + Ctx.cr Γ = RC' + Ctx.cr Γ')
    (hl : Ctx.LocOnly Γ') : HInv funs H R' RC' Γ' σ :=
  ⟨h.ok, h.nodup, by rw [h.cnt, hv], by rw [h.cred, hc], hl, h.reads⟩

theorem mem_of_cnt (h : HInv funs H R RC Γ σ) {x : Var} (hx : x ∈ R + Ctx.vars Γ) :
    ∃ n o, HCell.bind x n o ∈ H ∧ n ≠ 0 :=
  Heap.mem_cntM.mp (by rw [h.cnt]; exact Multiset.mem_add.mpr (.inl hx))

theorem rngFv_mem (h : HInv funs H R RC Γ σ) {x : Var} (hx : x ∈ H.rngFv) :
    ∃ n o, HCell.bind x n o ∈ H ∧ n ≠ 0 :=
  Heap.mem_cntM.mp (by rw [h.cnt]; exact Multiset.mem_add.mpr (.inr hx))

theorem cell_ok (h : HInv funs H R RC Γ σ) {x : Var} {n : Nat} {o : HObj}
    (hc : HCell.bind x n o ∈ H) : (∃ l, x = .loc l) ∧ 1 ≤ n ∧ o.Ok funs :=
  h.ok _ hc

/-- The references of an object are bound in the heap. -/
theorem fv_mem (h : HInv funs H R RC Γ σ) {x : Var} {n : Nat} {o : HObj}
    (hc : HCell.bind x n o ∈ H) {y : Var} (hy : y ∈ o.fv) :
    ∃ m p, HCell.bind y m p ∈ H ∧ m ≠ 0 :=
  h.rngFv_mem (Heap.mem_rngFv.mpr ⟨x, n, o, hc, hy⟩)

/-- Two cells at the same location are equal. -/
theorem cell_unique (h : HInv funs H R RC Γ σ) {x : Var} {n m : Nat} {o p : HObj}
    (h1 : HCell.bind x n o ∈ H) (h2 : HCell.bind x m p ∈ H) : n = m ∧ o = p := by
  by_contra hne
  have hne' : HCell.bind x n o ≠ HCell.bind x m p := by
    intro heq; simp only [HCell.bind.injEq] at heq; exact hne ⟨heq.2.1, heq.2.2⟩
  obtain ⟨H₀, rfl⟩ := Heap.eq_add_of_mem h1
  have h2' : HCell.bind x m p ∈ H₀ := by
    rcases Multiset.mem_add.mp h2 with h2 | h2
    · rw [Multiset.mem_singleton] at h2; exact absurd h2.symm hne'
    · exact h2
  have hnd := h.nodup
  rw [Heap.dom_add, Heap.dom_bind, Multiset.singleton_add, Multiset.nodup_cons] at hnd
  exact hnd.1 (Heap.mem_dom.mpr ⟨m, p, h2'⟩)

end HInv

end FIP.Lam
