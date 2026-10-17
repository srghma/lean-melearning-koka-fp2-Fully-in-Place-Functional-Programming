module

public import RequestProject.Sec2_Calculus.SubstLemmas

@[expose] public section

/-!
# Structural lemmas about the FIP judgment (Appendix B.4)

* **Lemma 12** (`Wf.weakenΔ`): the borrowed environment can be weakened.
* **Lemma 11** (`Wf.rename`): renaming variables preserves well-formedness.

With de Bruijn indices there is no side condition about bound variables: a binder is
always distinct from the variables it is placed next to.  Lemma 11 is proved for an
arbitrary renaming `f : Fin n → Var m` of the variables in scope (not necessarily
injective; several owned variables may be merged, the owned environment being a
multiset).  The paper's statement `Δ | Γ, x ⊢ e ⟹ Δ | Γ, y ⊢ e[x:=y]` is the instance
that renames one variable.
-/

namespace FIP

/-! ## Lemma 12 -/

mutual
/-- The borrowed environment of a value is irrelevant. -/
theorem WfVal.anyΔ {n : Nat} {U Δ Δ' : Finset (Var n)} :
    ∀ {Γ : Ctx n} {v : Val n}, WfVal U Δ Γ v → WfVal U Δ' Γ v
  | _, _, .var x => .var x
  | _, _, .svar x hx => .svar x hx
  | _, _, .atom c => .atom c
  | _, _, .lit k => .lit k
  | _, _, .reuse c vs Γ hne hvs => .reuse c vs Γ hne (WfVals.anyΔ hvs)
theorem WfVals.anyΔ {n : Nat} {U Δ Δ' : Finset (Var n)} :
    ∀ {Γ : Ctx n} {vs : List (Val n)}, WfVals U Δ Γ vs → WfVals U Δ' Γ vs
  | _, _, .nil => .nil
  | _, _, .cons Γ₁ Γ₂ v vs hv hvs => .cons Γ₁ Γ₂ v vs (WfVal.anyΔ hv) (WfVals.anyΔ hvs)
end

theorem Vars.shift_mono {n : Nat} (k : Nat) {Δ Δ' : Finset (Var n)} (h : Δ ⊆ Δ') :
    Vars.shift k Δ ⊆ Vars.shift k Δ' :=
  Finset.map_subset_map.mpr h

/-- **Lemma 12** (the borrowed environment can be weakened): if `Δ | Γ ⊢ e` then
    `Δ' | Γ ⊢ e` for `Δ ⊆ Δ'`. -/
theorem Wf.weakenΔ {cfg : Cfg} {n : Nat} {U Δ : Finset (Var n)} {Γ : Ctx n} {e : Expr n}
    (h : Wf cfg U Δ Γ e) : ∀ {Δ'}, Δ ⊆ Δ' → Wf cfg U Δ' Γ e := by
  induction h with
  | tuple hv => intro Δ' _; exact .tuple (WfVals.anyΔ hv)
  | call f ys e hf hy _ ih =>
    intro Δ' hΔ
    refine .call f ys e hf (fun y hy' => ?_) (ih hΔ)
    have := hy y hy'
    cases y <;> simp_all [BorrowArg]
    rcases this with h | h
    · exact .inl (hΔ h)
    · exact .inr h
  | bapp y e hy _ ih => intro Δ' hΔ; exact .bapp y e (hΔ hy) (ih hΔ)
  | fapp f e hf _ ih => intro Δ' hΔ; exact .fapp f e hf (ih hΔ)
  | prim op vs hv =>
    intro Δ' hΔ
    refine .prim op vs (fun v hv' => ?_)
    have := hv v hv'
    cases v <;> simp_all [ScalarArg]
    rcases this with h | h
    · exact .inl (hΔ h)
    · exact .inr h
  | letIn Γ₁ Γ₂ Γ₃ xs e₁ e₂ h2 _ _ ih1 ih2 =>
    intro Δ' hΔ
    exact .letIn Γ₁ Γ₂ Γ₃ xs e₁ e₂ h2 (ih1 (Finset.union_subset_union hΔ subset_rfl))
      (ih2 (Vars.shift_mono _ hΔ))
  | bmatch y bs hy _ ih =>
    intro Δ' hΔ
    exact .bmatch y bs (hy.imp_left (hΔ ·)) fun b hb' =>
      ih b hb' (Finset.union_subset_union (Vars.shift_mono _ hΔ) subset_rfl)
  | dmatch x bs _ ih =>
    intro Δ' hΔ
    exact .dmatch x bs fun b hb' => ih b hb' (Vars.shift_mono _ hΔ)
  | empty _ ih => intro Δ' hΔ; exact .empty (ih hΔ)
  | drop x hf _ ih => intro Δ' hΔ; exact .drop x hf (ih hΔ)
  | free k hf hk _ ih => intro Δ' hΔ; exact .free k hf hk (ih hΔ)
  | inst k hk _ ih => intro Δ' hΔ; exact .inst k hk (ih hΔ)
  | weaken _ ih => intro Δ' hΔ; exact .weaken (ih hΔ)

/-! ## Renamings -/

/-- Rename a variable (locations are left alone). -/
def Var.rename {n m : Nat} (f : Fin n → Var m) : Var n → Var m
  | .bvar i => f i
  | .loc l => .loc l

/-- Rename the variable of a resource. -/
def Res.rename {n m : Nat} (f : Fin n → Var m) : Res n → Res m
  | .var x => .var (x.rename f)
  | .credit k => .credit k
  | .alloc => .alloc

/-- A renaming as a substitution. -/
def Subst.ofRen {n m : Nat} (f : Fin n → Var m) : Fin n → Val m := fun i => .var (f i)

/-- A renaming pushed under `k` binders. -/
def Ren.up {n m : Nat} (k : Nat) (f : Fin n → Var m) : Fin (n + k) → Var (m + k) :=
  fun i => if h : i.val < k then .bvar ⟨i, by omega⟩ else (f ⟨i - k, by omega⟩).shift k

@[simp] theorem Val.subst_ofRen {n m : Nat} (f : Fin n → Var m) (x : Var n) :
    Val.subst (Subst.ofRen f) (.var x) = .var (x.rename f) := by
  cases x <;> rfl

theorem Subst.up_ofRen {n m : Nat} (k : Nat) (f : Fin n → Var m) (i : Fin (n + k)) :
    Subst.up k (Subst.ofRen f) i = Subst.ofRen (Ren.up k f) i := by
  simp only [Subst.up, Subst.ofRen, Ren.up]
  split
  · rfl
  · rw [Val.shift_var]

theorem Var.rename_shift {n m : Nat} (k : Nat) (f : Fin n → Var m) (x : Var n) :
    (x.shift k).rename (Ren.up k f) = (x.rename f).shift k := by
  cases x with
  | loc l => rfl
  | bvar i =>
    simp only [Var.shift, Var.rename, Ren.up, show ¬ (k + i.val < k) by omega, dite_false]
    congr 2
    ext; simp

theorem Var.rename_newB {n m k : Nat} (f : Fin n → Var m) (j : Fin k) :
    (Var.newB j : Var (n + k)).rename (Ren.up k f) = Var.newB j := by
  simp [Var.newB, Var.rename, Ren.up]

theorem Vars.shift_image_rename {n m : Nat} (k : Nat) (f : Fin n → Var m) (U : Finset (Var n)) :
    (Vars.shift k U).image (Var.rename (Ren.up k f)) = Vars.shift k (U.image (Var.rename f)) := by
  ext y
  simp only [Finset.mem_image, Vars.mem_shift_iff]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, (Var.rename_shift k f x).symm⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, Var.rename_shift k f x⟩

theorem Binder.select_rename {n m : Nat} (f : Fin n → Var m) (xs : List Bool) (sc : Bool) :
    (Binder.select xs sc (Var.newB (n := n))).map (Var.rename (Ren.up xs.length f)) =
      Binder.select xs sc (Var.newB (n := m)) := by
  simp only [Binder.select, List.map_map]
  exact List.map_congr_left fun j _ => Var.rename_newB f j

theorem Binder.scalars_rename {n m : Nat} (f : Fin n → Var m) (xs : List Bool) :
    (Binder.scalars xs : Finset (Var (n + xs.length))).image (Var.rename (Ren.up xs.length f)) =
      Binder.scalars xs := by
  simp only [Binder.scalars, Binder.scalarsAt]
  ext y
  rw [Finset.mem_image]
  simp only [List.mem_toFinset]
  rw [← Binder.select_rename f xs true, List.mem_map]

theorem Binder.ownedSet_rename {n m : Nat} (f : Fin n → Var m) (xs : List Bool) :
    (Binder.ownedSet xs : Finset (Var (n + xs.length))).image
        (Var.rename (Ren.up xs.length f)) = Binder.ownedSet xs := by
  simp only [Binder.ownedSet, Binder.ownedSetAt]
  ext y
  rw [Finset.mem_image]
  simp only [List.mem_toFinset]
  rw [← Binder.select_rename f xs false, List.mem_map]

theorem Binder.owned_rename {n m : Nat} (f : Fin n → Var m) (xs : List Bool) :
    (Binder.owned xs : Ctx (n + xs.length)).map (Res.rename (Ren.up xs.length f)) =
      Binder.owned xs := by
  simp only [Binder.owned, Binder.ownedAt, Multiset.map_coe, List.map_map]
  congr 1
  rw [← Binder.select_rename f xs false, List.map_map]
  rfl

theorem Ctx.shift_rename {n m : Nat} (k : Nat) (f : Fin n → Var m) (Γ : Ctx n) :
    (Γ.shift k).map (Res.rename (Ren.up k f)) = Ctx.shift k (Γ.map (Res.rename f)) := by
  simp only [Ctx.shift, Multiset.map_map]
  refine Multiset.map_congr rfl fun r _ => ?_
  cases r with
  | var x => simp only [Function.comp, Res.shift, Res.rename, Var.rename_shift]
  | credit j => rfl
  | alloc => rfl

theorem Ctx.vars_map_rename {n m : Nat} (f : Fin n → Var m) (Γ : Ctx n) :
    Ctx.vars (Γ.map (Res.rename f)) = Γ.vars.map (Var.rename f) := by
  induction Γ using Multiset.induction with
  | empty => simp [Ctx.vars]
  | cons r Γ ih =>
    cases r <;> simp_all [Ctx.vars, Res.rename]

mutual
theorem WfVal.rename {n m : Nat} {f : Fin n → Var m} {U Δ : Finset (Var n)}
    {Δ' : Finset (Var m)} : ∀ {Γ : Ctx n} {v : Val n}, WfVal U Δ Γ v →
      WfVal (U.image (Var.rename f)) Δ' (Γ.map (Res.rename f)) (v.subst (Subst.ofRen f))
  | _, _, .var x => by
    rw [Val.subst_ofRen]; simpa [Res.rename] using WfVal.var (U := U.image (Var.rename f))
      (Δ := Δ') (x.rename f)
  | _, _, .svar x hx => by
    rw [Val.subst_ofRen]; simpa using WfVal.svar (Δ := Δ') _ (Finset.mem_image_of_mem _ hx)
  | _, _, .atom c => by simpa [Val.subst] using WfVal.atom (U := U.image (Var.rename f)) (Δ := Δ') c
  | _, _, .lit k => by simpa [Val.subst] using WfVal.lit (U := U.image (Var.rename f)) (Δ := Δ') k
  | _, _, .reuse c vs Γ hne hvs => by
    have h := WfVal.reuse (U := U.image (Var.rename f)) (Δ := Δ') c
      (vs.map (Val.subst (Subst.ofRen f))) _ (by simpa using hne) (WfVals.rename hvs)
    simp only [List.length_map] at h
    simpa [Val.subst, Res.rename] using h
theorem WfVals.rename {n m : Nat} {f : Fin n → Var m} {U Δ : Finset (Var n)}
    {Δ' : Finset (Var m)} : ∀ {Γ : Ctx n} {vs : List (Val n)}, WfVals U Δ Γ vs →
      WfVals (U.image (Var.rename f)) Δ' (Γ.map (Res.rename f))
        (vs.map (Val.subst (Subst.ofRen f)))
  | _, _, .nil => by simpa using WfVals.nil
  | _, _, .cons Γ₁ Γ₂ v vs hv hvs => by
    simpa using WfVals.cons _ _ _ _ (WfVal.rename (Δ' := Δ') hv) (WfVals.rename hvs)
end

/-- **Lemma 11** (renaming preserves FIP typing): renaming the variables of `Δ | Γ ⊢ e` by
    any `f` (in the scalar, borrowed and owned environments, and in `e`) preserves
    well-formedness.  This covers both `Δ | Γ, x ⊢ e ⟹ Δ | Γ, y ⊢ e[x:=y]` and
    `Δ, x | Γ ⊢ e ⟹ Δ, y | Γ ⊢ e[x:=y]`. -/
theorem Wf.rename {cfg : Cfg} {n : Nat} {U Δ : Finset (Var n)} {Γ : Ctx n} {e : Expr n}
    (h : Wf cfg U Δ Γ e) : ∀ {m : Nat} (f : Fin n → Var m),
    Wf cfg (U.image (Var.rename f)) (Δ.image (Var.rename f)) (Γ.map (Res.rename f))
      (e.subst (Subst.ofRen f)) := by
  induction h with
  | tuple hv =>
    intro m f
    simp only [Expr.subst, Val.substList_eq_map]; exact .tuple (WfVals.rename hv)
  | call g ys e hf hy _ ih =>
    intro m f
    simp only [Expr.subst, Val.substList_eq_map, Multiset.map_add, Multiset.map_replicate,
      Res.rename]
    have hys : (ys.map (Val.subst (Subst.ofRen f))).map (fnBudget cfg) =
        ys.map (fnBudget cfg) := by
      simp only [List.map_map]
      refine List.map_congr_left fun v hv => ?_
      cases v with
      | var x => simp only [Function.comp, Val.subst_ofRen, fnBudget]
      | _ => simp [Val.subst, fnBudget]
    rw [← hys]
    refine .call g _ _ hf (fun v hv => ?_) (ih f)
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
    have := hy w hw
    cases w with
    | var x =>
      rw [Val.subst_ofRen]
      rcases this with h | h
      · exact .inl (Finset.mem_image_of_mem _ h)
      · exact .inr (Finset.mem_image_of_mem _ h)
    | fn g => exact this
    | ctor _ _ => exact this.elim
    | lit _ => exact this.elim
  | bapp x e hx _ ih =>
    intro m f
    simp only [Expr.subst, Val.substList_eq_map, List.map_cons, List.map_nil]
    rw [Val.subst_ofRen]
    exact .bapp _ _ (Finset.mem_image_of_mem _ hx) (ih f)
  | fapp g e hf _ ih =>
    intro m f
    simp only [Expr.subst, Val.substList_eq_map, List.map_cons, List.map_nil, Val.subst,
      Multiset.map_add, Multiset.map_replicate, Res.rename]
    exact .fapp g _ hf (ih f)
  | prim op vs hv =>
    intro m f
    simp only [Expr.subst, Val.substList_eq_map, Multiset.map_zero]
    refine .prim op _ (fun v hv' => ?_)
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv'
    have := hv w hw
    cases w with
    | var x =>
      rw [Val.subst_ofRen]
      rcases this with h | h
      · exact .inl (Finset.mem_image_of_mem _ h)
      · exact .inr (Finset.mem_image_of_mem _ h)
    | lit _ => exact this
    | fn _ => exact this.elim
    | ctor _ _ => exact this.elim
  | letIn Γ₁ Γ₂ Γ₃ xs e₁ e₂ h2 _ _ ih1 ih2 =>
    intro m f
    simp only [Expr.subst, Multiset.map_add]
    have h1 := ih1 f
    have h2' := ih2 (Ren.up xs.length f)
    rw [Finset.image_union] at h1
    rw [Finset.image_union, Binder.scalars_rename, Vars.shift_image_rename,
      Vars.shift_image_rename, Multiset.map_add, Binder.owned_rename, Ctx.shift_rename,
      Multiset.map_add] at h2'
    rw [Expr.subst_congr (Subst.up_ofRen xs.length f)]
    refine .letIn _ _ _ xs _ _ ?_ ?_ h2'
    · intro r hr
      obtain ⟨r', hr', rfl⟩ := Multiset.mem_map.mp hr
      obtain ⟨x, rfl⟩ := h2 r' hr'
      exact ⟨_, rfl⟩
    · have : (Γ₂.vars.toFinset).image (Var.rename f) =
          (Ctx.vars (Γ₂.map (Res.rename f))).toFinset := by
        rw [Ctx.vars_map_rename, Multiset.toFinset_map]
      rw [← this]; exact h1
  | bmatch x bs hx _ ih =>
    intro m f
    simp only [Expr.subst, Val.substList_eq_map, List.map_cons, List.map_nil]
    rw [Val.subst_ofRen]
    refine .bmatch _ _ (hx.imp (Finset.mem_image_of_mem _) (Finset.mem_image_of_mem _))
      (fun b' hb' => ?_)
    rw [Branches.toList_subst] at hb'
    obtain ⟨b, hbm, rfl⟩ := List.mem_map.mp hb'
    have := ih b hbm (Ren.up b.binders.length f)
    rw [Finset.image_union, Finset.image_union, Binder.scalars_rename, Binder.ownedSet_rename,
      Vars.shift_image_rename, Vars.shift_image_rename, Ctx.shift_rename] at this
    show Wf cfg _ _ _ (b.body.subst (Subst.up b.binders.length (Subst.ofRen f)))
    rw [Expr.subst_congr (Subst.up_ofRen _ f)]
    exact this
  | dmatch x bs _ ih =>
    intro m f
    simp only [Expr.subst, Val.substList_eq_map, List.map_cons, List.map_nil,
      Multiset.map_add, Multiset.map_singleton, Res.rename]
    rw [Val.subst_ofRen]
    refine .dmatch _ _ (fun b' hb' => ?_)
    rw [Branches.toList_subst] at hb'
    obtain ⟨b, hbm, rfl⟩ := List.mem_map.mp hb'
    have := ih b hbm (Ren.up b.binders.length f)
    rw [Finset.image_union, Binder.scalars_rename, Vars.shift_image_rename,
      Vars.shift_image_rename, Multiset.map_add, Multiset.map_add, Binder.owned_rename,
      Ctx.shift_rename, Multiset.map_singleton] at this
    show Wf cfg _ _ _ (b.body.subst (Subst.up b.binders.length (Subst.ofRen f)))
    rw [Expr.subst_congr (Subst.up_ofRen _ f)]
    exact this
  | empty _ ih =>
    intro m f
    simpa [Multiset.map_add, Res.rename] using Wf.empty (ih f)
  | drop x hf _ ih =>
    intro m f
    simp only [Expr.subst, Multiset.map_add, Multiset.map_singleton, Res.rename]
    rw [Val.subst_ofRen]
    exact .drop _ hf (ih f)
  | free k hf hk _ ih =>
    intro m f
    simp only [Expr.subst, Multiset.map_add, Multiset.map_singleton, Res.rename]
    exact .free k hf hk (ih f)
  | inst k hk _ ih =>
    intro m f
    have := ih f
    simp only [Multiset.map_add, Multiset.map_singleton, Res.rename] at this ⊢
    exact .inst k hk this
  | weaken _ ih =>
    intro m f
    simpa [Multiset.map_add, Res.rename] using Wf.weaken (ih f)

end FIP
