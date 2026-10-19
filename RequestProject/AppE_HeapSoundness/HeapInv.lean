module

public import RequestProject.AppE_HeapSoundness.HeapRoots

@[expose] public section

/-!
# The heap invariant of the proof of Theorem 6

* `HObj.toVal σ o`: the closed value denoted by an object, `[H]φ`;
* `HInv funs H σ`: `H` is linear, its objects have locations as fields (and closures
  have well-formed, admissible bodies), `σ` is `[H]` (every bound location `l` denotes
  `σ l`), and `σ` has a finite support;
* `SubstExt σ σ'`: `σ'` extends `σ`.  Locations are never reused in the proof (a fresh
  location is chosen outside the support of `σ`), so the substitution only grows;
* the effect of `dup`, `drop`, freeing, allocation and credits on the invariant;
* reductions of the heap semantics in evaluation contexts.
-/

namespace FIP.Lam

/-- The closed value `[H]φ` denoted by an object, for `σ = [H]`. -/
def HObj.toVal (σ : Nat → Option (LVal 0)) : HObj → LVal 0
  | .con c args => .ctor c (LVals.ofList (args.map (LVal.substLoc σ)))
  | .clo zs c k b => .lam (LVals.ofList (zs.map (LVal.substLoc σ))) c k b

/-- The fields of an object. -/
def HObj.fields : HObj → List (LVal 0)
  | .con _ args => args
  | .clo zs _ _ _ => zs

/-- A well-formed object: its fields are locations, and a closure has a well-formed,
    admissible body of the right scope. -/
def HObj.Ok (funs : List FName) : HObj → Prop
  | .con _ args => ∀ a ∈ args, ∃ l, a = locV l
  | .clo zs c k b => (∀ a ∈ zs, ∃ l, a = locV l) ∧ zs.length = c ∧
      LWf funs ∅ (allCtx (c + k)) b ∧ b.Adm (fun _ => none)

/-- The invariant on heaps. -/
structure HInv (funs : List FName) (H : Heap) (σ : Nat → Option (LVal 0)) : Prop where
  linear : H.Linear
  ok : ∀ x n o, HCell.bind x n o ∈ H → o.Ok funs
  reads : ∀ l n o, HCell.bind (.loc l) n o ∈ H → σ l = some (o.toVal σ)
  bound : ∃ N, ∀ l, N ≤ l → σ l = none

/-- `σ'` extends `σ`. -/
def SubstExt (σ σ' : Nat → Option (LVal 0)) : Prop := ∀ l v, σ l = some v → σ' l = some v

theorem SubstExt.refl (σ : Nat → Option (LVal 0)) : SubstExt σ σ := fun _ _ h => h

theorem SubstExt.trans {σ σ' σ'' : Nat → Option (LVal 0)} (h : SubstExt σ σ')
    (h' : SubstExt σ' σ'') : SubstExt σ σ'' := fun l v hl => h' l v (h l v hl)

theorem Var.zero_eq_loc : ∀ x : Var 0, ∃ l, x = .loc l
  | .loc l => ⟨l, rfl⟩
  | .bvar i => i.elim0

theorem locV_substLoc (σ : Nat → Option (LVal 0)) (l : Nat) (v : LVal 0) (h : σ l = some v) :
    (locV l).substLoc σ = v := by
  simp [h]

theorem HObj.fv_eq_fields (o : HObj) : o.fv = LVal.fvList o.fields := by
  cases o <;> rfl

theorem LVal.fvList_locs : ∀ (ls : List Nat),
    LVal.fvList (ls.map locV) = ls.map Var.loc
  | [] => rfl
  | l :: ls => by simp [LVal.fvList, LVal.fv, LVal.fvList_locs ls]

theorem exists_locs : ∀ (as : List (LVal 0)), (∀ a ∈ as, ∃ l, a = locV l) →
    ∃ ls : List Nat, as = ls.map locV
  | [], _ => ⟨[], rfl⟩
  | a :: as, h => by
    obtain ⟨l, rfl⟩ := h a (by simp)
    obtain ⟨ls, hls⟩ := exists_locs as (fun b hb => h b (by simp [hb]))
    exact ⟨l :: ls, by simp [hls]⟩

/-- The fields of a well-formed object are locations. -/
theorem HObj.Ok.fields_locs {funs : List FName} {o : HObj} (h : o.Ok funs) :
    ∃ ls : List Nat, o.fields = ls.map locV := by
  apply exists_locs
  cases o with
  | con c args => exact h
  | clo zs c k b => exact h.1

theorem HObj.toVal_congr {funs : List FName} {o : HObj} (h : o.Ok funs)
    {σ σ' : Nat → Option (LVal 0)} (hσ : ∀ l, Var.loc l ∈ o.fv → σ l = σ' l) :
    o.toVal σ = o.toVal σ' := by
  obtain ⟨ls, hls⟩ := h.fields_locs
  have hf : ∀ l ∈ ls, σ l = σ' l := fun l hl => hσ l (by
    rw [HObj.fv_eq_fields, hls, LVal.fvList_locs]; simp [hl])
  have hmap : ∀ (as : List (LVal 0)), as = ls.map locV →
      as.map (LVal.substLoc σ) = as.map (LVal.substLoc σ') := by
    rintro as rfl
    simp only [List.map_map]
    apply List.map_congr_left
    intro l hl
    simp [hf l hl]
  cases o with
  | con c args => simp only [HObj.toVal]; rw [hmap args hls]
  | clo zs c k b => simp only [HObj.toVal]; rw [hmap zs hls]

/-! ## Basic consequences of the invariant -/

namespace HInv

variable {funs : List FName} {H H' : Heap} {σ : Nat → Option (LVal 0)}

theorem some_of_dom (h : HInv funs H σ) {l : Nat} (hl : Var.loc l ∈ H.dom) :
    ∃ v, σ l = some v := by
  obtain ⟨n, o, hc⟩ := Heap.mem_dom_iff.mp hl
  exact ⟨_, h.reads l n o hc⟩

theorem some_of_root (h : HInv funs H σ) {l : Nat} (hl : Res.var (.loc l) ∈ H.roots) :
    ∃ v, σ l = some v :=
  h.some_of_dom (h.linear.mem_dom_of_root hl)

/-- Changing reference counts or removing cells preserves the invariant. -/
theorem of_cells (h : HInv funs H σ) (hl : H'.Linear)
    (hc : ∀ x n o, HCell.bind x n o ∈ H' → ∃ m, HCell.bind x m o ∈ H) : HInv funs H' σ := by
  refine ⟨hl, fun x n o hx => ?_, fun l n o hx => ?_, h.bound⟩
  · obtain ⟨m, hm⟩ := hc x n o hx; exact h.ok x m o hm
  · obtain ⟨m, hm⟩ := hc (.loc l) n o hx; exact h.reads l m o hm

theorem inc (h : HInv funs ({HCell.bind x n o} + H) σ) :
    HInv funs ({HCell.bind x (n + 1) o} + H) σ := by
  refine h.of_cells (Heap.inc_linear h.linear) (fun z m p hz => ?_)
  simp only [Multiset.mem_add, Multiset.mem_singleton, HCell.bind.injEq] at hz
  rcases hz with ⟨rfl, -, rfl⟩ | hz
  · exact ⟨n, by simp⟩
  · exact ⟨m, by simp [hz]⟩

theorem dec (h : HInv funs ({HCell.bind x (n + 2) o} + H) σ)
    (hx : Res.var x ∈ Heap.roots ({HCell.bind x (n + 2) o} + H)) :
    HInv funs ({HCell.bind x (n + 1) o} + H) σ := by
  refine h.of_cells (Heap.dec_linear h.linear hx) (fun z m p hz => ?_)
  simp only [Multiset.mem_add, Multiset.mem_singleton, HCell.bind.injEq] at hz
  rcases hz with ⟨rfl, -, rfl⟩ | hz
  · exact ⟨n + 2, by simp⟩
  · exact ⟨m, by simp [hz]⟩

theorem free (h : HInv funs ({HCell.bind x 1 o} + H) σ)
    (hx : Res.var x ∈ Heap.roots ({HCell.bind x 1 o} + H)) : HInv funs H σ :=
  h.of_cells (Heap.free_linear h.linear hx) (fun z m p hz => ⟨m, by simp [hz]⟩)

theorem add_credit (h : HInv funs H σ) (k : Nat) : HInv funs ({HCell.credit k} + H) σ :=
  h.of_cells (Heap.credit_linear h.linear k) (fun z m p hz => ⟨m, by
    simpa using hz⟩)

theorem remove_credit {k : Nat} (h : HInv funs ({HCell.credit k} + H) σ) : HInv funs H σ :=
  h.of_cells (Heap.linear_of_credit h.linear) (fun z m p hz => ⟨m, by simp [hz]⟩)

/-- A location outside the support of `σ`, hence fresh for the heap. -/
theorem exists_fresh (h : HInv funs H σ) : ∃ N, σ N = none ∧ Var.loc N ∉ H.dom := by
  obtain ⟨N, hN⟩ := h.bound
  refine ⟨N, hN N le_rfl, fun hd => ?_⟩
  obtain ⟨v, hv⟩ := h.some_of_dom hd
  rw [hN N le_rfl] at hv; cases hv

/-- Allocating a fresh cell `N ↦¹ φ` whose fields are owned roots. -/
theorem alloc (h : HInv funs H σ) {N : Nat} (hN : σ N = none) {o : HObj} (ho : o.Ok funs)
    (hfv : o.fvCtx ≤ H.roots) :
    HInv funs ({HCell.bind (.loc N) 1 o} + H) (Function.update σ N (some (o.toVal σ))) ∧
      SubstExt σ (Function.update σ N (some (o.toVal σ))) := by
  have hNd : Var.loc N ∉ H.dom := fun hd => by
    obtain ⟨v, hv⟩ := h.some_of_dom hd; rw [hN] at hv; cases hv
  set σ' := Function.update σ N (some (o.toVal σ)) with hσ'
  have hext : SubstExt σ σ' := by
    intro l v hl
    have : l ≠ N := fun e => by subst e; rw [hN] at hl; cases hl
    simp [σ', Function.update_of_ne this, hl]
  have hagree : ∀ l, Var.loc l ∈ H.dom → σ l = σ' l := by
    intro l hl
    obtain ⟨v, hv⟩ := h.some_of_dom hl
    rw [hv, hext l v hv]
  -- fields of the new object are in the heap
  have hfvd : ∀ l, Var.loc l ∈ o.fv → Var.loc l ∈ H.dom := by
    intro l hl
    have h1 : Res.var (.loc l) ∈ o.fvCtx := by
      simp only [HObj.fvCtx, Multiset.mem_coe, List.mem_map]; exact ⟨_, hl, rfl⟩
    exact h.linear.mem_dom_of_root (Multiset.mem_of_le hfv h1)
  refine ⟨⟨Heap.alloc_linear h.linear hNd hfv, fun x n p hx => ?_, fun l n p hx => ?_, ?_⟩, hext⟩
  · simp only [Multiset.mem_add, Multiset.mem_singleton, HCell.bind.injEq] at hx
    rcases hx with ⟨-, -, rfl⟩ | hx
    · exact ho
    · exact h.ok x n p hx
  · simp only [Multiset.mem_add, Multiset.mem_singleton, HCell.bind.injEq, Var.loc.injEq] at hx
    rcases hx with ⟨rfl, -, rfl⟩ | hx
    · simp only [σ', Function.update_self]
      congr 1
      exact HObj.toVal_congr ho (fun l hl => hagree l (hfvd l hl))
    · have hl : l ≠ N := fun e => by
        subst e; exact hNd (Heap.mem_dom_iff.mpr ⟨n, p, hx⟩)
      rw [show σ' l = σ l from by simp [σ', Function.update_of_ne hl], h.reads l n p hx]
      congr 1
      refine HObj.toVal_congr (h.ok _ n p hx) (fun l' hl' => hagree l' ?_)
      exact h.linear.1.2.2 _ (by
        unfold Heap.rngFv
        exact Multiset.mem_bind.mpr ⟨_, hx, Multiset.mem_coe.mpr hl'⟩)
  · obtain ⟨M, hM⟩ := h.bound
    refine ⟨max M (N + 1), fun l hl => ?_⟩
    have hlN : l ≠ N := by omega
    simp [σ', Function.update_of_ne hlN, hM l (by omega)]

end HInv

/-! ## Reductions of the heap semantics -/

variable {sig : LSig}

theorem HStep.ctx (F : LECtx) {H H' : Heap} {e e' : LExpr 0} (h : HStep sig H e H' e') :
    HStep sig H (F.plug e) H' (F.plug e') := by
  cases h with
  | head E hh => rw [← LECtx.plug_comp, ← LECtx.plug_comp]; exact .head _ hh
  | val E done V rest hd hV hv =>
    rw [← LECtx.plug_comp, ← LECtx.plug_comp]; exact .val _ done V rest hd hV hv

theorem HSteps.single {H H' : Heap} {e e' : LExpr 0} (h : HStep sig H e H' e') :
    HSteps sig H e H' e' := .tail (.refl _ _) h

theorem HSteps.trans {H₁ H₂ H₃ : Heap} {e₁ e₂ e₃ : LExpr 0} (h₁ : HSteps sig H₁ e₁ H₂ e₂)
    (h₂ : HSteps sig H₂ e₂ H₃ e₃) : HSteps sig H₁ e₁ H₃ e₃ := by
  induction h₂ with
  | refl => exact h₁
  | tail _ hs ih => exact .tail (ih h₁) hs

theorem HSteps.head {H₁ H₂ H₃ : Heap} {e₁ e₂ e₃ : LExpr 0} (h₁ : HStep sig H₁ e₁ H₂ e₂)
    (h₂ : HSteps sig H₂ e₂ H₃ e₃) : HSteps sig H₁ e₁ H₃ e₃ :=
  (HSteps.single h₁).trans h₂

theorem HSteps.ctx (F : LECtx) {H H' : Heap} {e e' : LExpr 0} (h : HSteps sig H e H' e') :
    HSteps sig H (F.plug e) H' (F.plug e') := by
  induction h with
  | refl => exact .refl _ _
  | tail _ hs ih => exact .tail ih (hs.ctx F)

theorem HHead.step {H H' : Heap} {e e' : LExpr 0} (h : HHead sig H e H' e') :
    HStep sig H e H' e' := HStep.head .hole h

end FIP.Lam
