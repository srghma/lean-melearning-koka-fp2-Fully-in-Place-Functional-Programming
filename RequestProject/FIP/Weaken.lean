module

public import RequestProject.FIP.TRMC

@[expose] public section

/-!
# Structural lemmas about the FIP judgment (Appendix B.4)

* **Lemma 12** (`Wf.weakenΔ`): the borrowed environment can be weakened.

Binders are named, so the paper's implicit convention that bound variables are distinct
from all other variables becomes the explicit side condition that the added borrowed
variables are not bound in the expression.
-/

namespace FIP

theorem Binder.Fresh.weakenΔ {xs : List Binder} {U Δ Δ' : Finset Var} {Γ : Ctx}
    (h : Binder.Fresh xs U Δ Γ) (hb : ∀ b ∈ xs, Var.name b.name ∉ Δ' \ Δ) :
    Binder.Fresh xs U Δ' Γ := by
  refine ⟨h.1, fun b hb' => ⟨(h.2 b hb').1, fun hΔ' => ?_, (h.2 b hb').2.2⟩⟩
  exact hb b hb' (Finset.mem_sdiff.mpr ⟨hΔ', (h.2 b hb').2.1⟩)

theorem union_sdiff_union_subset {Δ Δ' G : Finset Var} :
    (Δ' ∪ G) \ (Δ ∪ G) ⊆ Δ' \ Δ := by
  intro x hx
  simp only [Finset.mem_sdiff, Finset.mem_union, not_or] at hx ⊢
  rcases hx with ⟨h | h, h1, h2⟩
  · exact ⟨h, h1⟩
  · exact absurd h h2

/-- **Lemma 12** (the borrowed environment can be weakened): if `Δ | Γ ⊢ e` then
    `Δ' | Γ ⊢ e` for `Δ ⊆ Δ'`, provided the added variables are not bound in `e`. -/
theorem Wf.weakenΔ {cfg : Cfg} {U Δ : Finset Var} {Γ : Ctx} {e : Expr}
    (h : Wf cfg U Δ Γ e) :
    ∀ {Δ'}, Δ ⊆ Δ' → (∀ s ∈ e.binders, Var.name s ∉ Δ' \ Δ) → Wf cfg U Δ' Γ e := by
  induction h with
  | tuple hv => intro Δ' _ _; exact .tuple (WfVals.anyΔ hv)
  | call f ys e hf hy _ ih =>
    intro Δ' hΔ hb
    refine .call f ys e hf (fun y hy' => ?_) (ih hΔ (fun s hs => hb s (by
      simp [Expr.binders, hs])))
    have := hy y hy'
    cases y <;> simp_all [BorrowArg]
    rcases this with h | h
    · exact .inl (hΔ h)
    · exact .inr h
  | bapp y e hy _ ih =>
    intro Δ' hΔ hb
    exact .bapp y e (hΔ hy) (ih hΔ (fun s hs => hb s (by simp [Expr.binders, hs])))
  | fapp f e hf _ ih =>
    intro Δ' hΔ hb
    exact .fapp f e hf (ih hΔ (fun s hs => hb s (by simp [Expr.binders, hs])))
  | prim op vs hv =>
    intro Δ' hΔ _
    refine .prim op vs (fun v hv' => ?_)
    have := hv v hv'
    cases v <;> simp_all [ScalarArg]
    rcases this with h | h
    · exact .inl (hΔ h)
    · exact .inr h
  | letIn Γ₁ Γ₂ Γ₃ xs e₁ e₂ h2 _ _ hfr ih1 ih2 =>
    intro Δ' hΔ hb
    refine .letIn Γ₁ Γ₂ Γ₃ xs e₁ e₂ h2 (ih1 (Finset.union_subset_union hΔ subset_rfl)
      (fun s hs hs' => hb s (by simp [Expr.binders, hs]) (union_sdiff_union_subset hs')))
      (ih2 hΔ (fun s hs => hb s (by simp [Expr.binders, hs]))) ?_
    exact hfr.weakenΔ (fun b hb' => hb _ (by
      simp only [Expr.binders, List.mem_append, List.mem_map]
      exact .inl (.inl ⟨b, hb', rfl⟩)))
  | bmatch y bs hy hfr _ ih =>
    intro Δ' hΔ hb
    refine .bmatch y bs (hy.imp_left (hΔ ·)) (fun b hb' => ?_) (fun b hb' => ?_)
    · exact (hfr b hb').weakenΔ (fun x hx => hb _ (by
        simp only [Expr.binders, List.mem_append]
        exact .inr (Expr.mem_bindersB hb' (.inl (List.mem_map_of_mem hx)))))
    · exact ih b hb' (Finset.union_subset_union hΔ subset_rfl) (fun s hs hs' => hb s (by
        simp only [Expr.binders, List.mem_append]
        exact .inr (Expr.mem_bindersB hb' (.inr hs))) (union_sdiff_union_subset hs'))
  | dmatch x bs hfr _ ih =>
    intro Δ' hΔ hb
    refine .dmatch x bs (fun b hb' => ?_) (fun b hb' => ?_)
    · exact (hfr b hb').weakenΔ (fun x hx => hb _ (by
        simp only [Expr.binders, List.mem_append]
        exact .inr (Expr.mem_bindersB hb' (.inl (List.mem_map_of_mem hx)))))
    · exact ih b hb' hΔ (fun s hs => hb s (by
        simp only [Expr.binders, List.mem_append]
        exact .inr (Expr.mem_bindersB hb' (.inr hs))))
  | empty _ ih => intro Δ' hΔ hb; exact .empty (ih hΔ hb)
  | drop x hf _ ih =>
    intro Δ' hΔ hb; exact .drop x hf (ih hΔ (fun s hs => hb s (by simp [Expr.binders, hs])))
  | free k hf hk _ ih =>
    intro Δ' hΔ hb; exact .free k hf hk (ih hΔ (fun s hs => hb s (by simp [Expr.binders, hs])))
  | inst k hk _ ih => intro Δ' hΔ hb; exact .inst k hk (ih hΔ hb)
  | weaken _ ih => intro Δ' hΔ hb; exact .weaken (ih hΔ hb)

end FIP

/-! ## Lemma 11: renaming a variable -/

namespace FIP

/-- The renaming `x ↦ y` of the variable named `a` to `y`. -/
def renameVar (a : String) (y : Var) (v : Var) : Var := if v = .name a then y else v

/-- Rename the variables of a resource. -/
def Res.rename (ρ : Var → Var) : Res → Res
  | .var v => .var (ρ v)
  | r => r

theorem Val.subst_rename (a : String) (y : Var) (v : Var) :
    Val.subst [(a, .var y)] (.var v) = .var (renameVar a y v) := by
  cases v with
  | name s =>
    by_cases h : s = a
    · subst h; simp [Val.subst, renameVar]
    · have : (s == a) = false := by simpa using h
      simp [Val.subst, renameVar, h, List.lookup, this]
  | loc n => simp [Val.subst, renameVar]

theorem renameVar_of_ne {a : String} {y : Var} {v : Var} (h : v ≠ .name a) :
    renameVar a y v = v := by simp [renameVar, h]

theorem Subst.remove_single {a : String} {y : Var} {xs : List Binder}
    (h : a ∉ xs.map (·.name)) : Subst.remove [(a, .var y)] xs = [(a, .var y)] := by
  simp [Subst.remove, List.filter, h]

theorem Expr.substBranches_eq_map (σ : Subst) :
    ∀ bs : List Branch, Expr.substBranches σ bs =
      bs.map fun b => .mk b.ctor b.binders (b.body.subst (σ.remove b.binders))
  | [] => rfl
  | .mk c xs e :: bs => by
    rw [Expr.substBranches, List.map_cons, Expr.substBranches_eq_map σ bs]
    rfl

theorem Ctx.vars_map_rename (ρ : Var → Var) (Γ : Ctx) :
    Ctx.vars (Γ.map (Res.rename ρ)) = Γ.vars.map ρ := by
  induction Γ using Multiset.induction with
  | empty => simp [Ctx.vars]
  | cons r Γ ih =>
    cases r <;> simp_all [Ctx.vars, Res.rename]

theorem Finset.image_eq_self_of_fixed {ρ : Var → Var} {S : Finset Var}
    (h : ∀ v ∈ S, ρ v = v) : S.image ρ = S := by
  rw [Finset.image_congr (g := id) (fun v hv => h v hv), Finset.image_id]

/-- The binders of a list are fixed by the renaming (they are neither `a` nor `y`). -/
def Binder.AvoidRename (a : String) (y : Var) (xs : List Binder) : Prop :=
  ∀ b ∈ xs, b.name ≠ a ∧ Var.name b.name ≠ y

theorem Binder.scalars_rename {a : String} {y : Var} {xs : List Binder}
    (h : Binder.AvoidRename a y xs) : (Binder.scalars xs).image (renameVar a y) =
      Binder.scalars xs := by
  refine Finset.image_eq_self_of_fixed fun v hv => renameVar_of_ne ?_
  simp only [Binder.scalars, List.mem_toFinset, List.mem_map, List.mem_filter] at hv
  obtain ⟨b, ⟨hb, _⟩, rfl⟩ := hv
  simpa using (h b hb).1

theorem Binder.ownedSet_rename {a : String} {y : Var} {xs : List Binder}
    (h : Binder.AvoidRename a y xs) : (Binder.ownedSet xs).image (renameVar a y) =
      Binder.ownedSet xs := by
  refine Finset.image_eq_self_of_fixed fun v hv => renameVar_of_ne ?_
  simp only [Binder.ownedSet, List.mem_toFinset, List.mem_map, List.mem_filter] at hv
  obtain ⟨b, ⟨hb, _⟩, rfl⟩ := hv
  simpa using (h b hb).1

theorem Binder.owned_rename {a : String} {y : Var} {xs : List Binder}
    (h : Binder.AvoidRename a y xs) :
    (Binder.owned xs).map (Res.rename (renameVar a y)) = Binder.owned xs := by
  simp only [Binder.owned, Multiset.map_coe, List.map_map]
  congr 1
  refine List.map_congr_left fun b hb => ?_
  obtain ⟨hb, _⟩ := List.mem_filter.mp hb
  simp [Res.rename, renameVar_of_ne (y := y) (show Var.name b.name ≠ .name a by
    simpa using (h b hb).1)]

theorem Binder.Fresh.rename {a : String} {y : Var} {xs : List Binder} {U Δ : Finset Var}
    {Γ : Ctx} (h : Binder.Fresh xs U Δ Γ) (hr : Binder.AvoidRename a y xs) :
    Binder.Fresh xs (U.image (renameVar a y)) (Δ.image (renameVar a y))
      (Γ.map (Res.rename (renameVar a y))) := by
  refine ⟨h.1, fun b hb => ?_⟩
  have key : ∀ v, renameVar a y v = Var.name b.name → v = Var.name b.name := by
    intro v hv
    unfold renameVar at hv
    split at hv
    · exact absurd hv.symm (hr b hb).2
    · exact hv
  obtain ⟨h1, h2, h3⟩ := h.2 b hb
  refine ⟨fun hU => ?_, fun hΔ => ?_, fun hΓ => ?_⟩
  · obtain ⟨v, hv, hv'⟩ := Finset.mem_image.mp hU; exact h1 (key v hv' ▸ hv)
  · obtain ⟨v, hv, hv'⟩ := Finset.mem_image.mp hΔ; exact h2 (key v hv' ▸ hv)
  · obtain ⟨r, hr', hr''⟩ := Multiset.mem_map.mp hΓ
    cases r with
    | var v =>
      simp only [Res.rename, Res.var.injEq] at hr''
      exact h3 (key v hr'' ▸ hr')
    | credit k => simp [Res.rename] at hr''
    | alloc => simp [Res.rename] at hr''

mutual
theorem WfVal.rename {a : String} {y : Var} {U Δ Δ' : Finset Var} {Γ : Ctx} {v : Val} :
    WfVal U Δ Γ v → WfVal (U.image (renameVar a y)) Δ' (Γ.map (Res.rename (renameVar a y)))
      (v.subst [(a, .var y)])
  | .var x => by
    rw [Val.subst_rename]; simpa [Res.rename] using WfVal.var (renameVar a y x)
  | .svar x hx => by
    rw [Val.subst_rename]; simpa using WfVal.svar _ (Finset.mem_image_of_mem _ hx)
  | .atom c => by simpa [Val.subst] using WfVal.atom c
  | .lit n => by simpa [Val.subst] using WfVal.lit n
  | .reuse c vs Γ hne hvs => by
    have h := WfVal.reuse (U := U.image (renameVar a y)) (Δ := Δ') c
      (vs.map (Val.subst [(a, .var y)])) _ (by simpa using hne) (WfVals.rename hvs)
    simp only [List.length_map] at h
    simpa [Val.subst, Res.rename] using h
theorem WfVals.rename {a : String} {y : Var} {U Δ Δ' : Finset Var} {Γ : Ctx} {vs : List Val} :
    WfVals U Δ Γ vs → WfVals (U.image (renameVar a y)) Δ' (Γ.map (Res.rename (renameVar a y)))
      (vs.map (Val.subst [(a, .var y)]))
  | .nil => by simpa using WfVals.nil
  | .cons Γ₁ Γ₂ v vs hv hvs => by
    simpa using WfVals.cons _ _ _ _ (WfVal.rename (Δ' := Δ') hv) (WfVals.rename hvs)
end

/-- **Lemma 11** (variable substitution preserves FIP typing): renaming the variable
    named `a` to `y` in `Δ | Γ ⊢ e` (in the scalar, borrowed and owned environments, and
    in `e`) preserves well-formedness.  This covers both `Δ | Γ, x ⊢ e ⟹ Δ | Γ, y ⊢
    e[x:=y]` and `Δ, x | Γ ⊢ e ⟹ Δ, y | Γ ⊢ e[x:=y]`.  The binders of `e` must differ from
    `x` and `y`. -/
theorem Wf.rename {cfg : Cfg} {U Δ : Finset Var} {Γ : Ctx} {e : Expr}
    (h : Wf cfg U Δ Γ e) {a : String} {y : Var}
    (hb : ∀ s ∈ e.binders, s ≠ a ∧ Var.name s ≠ y) :
    Wf cfg (U.image (renameVar a y)) (Δ.image (renameVar a y))
      (Γ.map (Res.rename (renameVar a y))) (e.subst [(a, .var y)]) := by
  induction h with
  | tuple hv =>
    simp only [Expr.subst, Val.substList_eq_map]; exact .tuple (WfVals.rename hv)
  | call f ys e hf hy _ ih =>
    simp only [Expr.subst, Val.substList_eq_map, Multiset.map_add, Multiset.map_replicate,
      Res.rename]
    have hys : (ys.map (Val.subst [(a, .var y)])).map (fnBudget cfg) = ys.map (fnBudget cfg) := by
      simp only [List.map_map]
      refine List.map_congr_left fun v hv => ?_
      cases v with
      | var x => simp only [Function.comp, Val.subst_rename, fnBudget]
      | _ => simp [Val.subst, fnBudget]
    rw [← hys]
    refine .call f _ _ hf (fun v hv => ?_) (ih (fun s hs => hb s (by simp [Expr.binders, hs])))
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
    have := hy w hw
    cases w with
    | var x =>
      rw [Val.subst_rename]
      rcases this with h | h
      · exact .inl (Finset.mem_image_of_mem _ h)
      · exact .inr (Finset.mem_image_of_mem _ h)
    | fn g => exact this
    | ctor _ _ => exact this.elim
    | lit _ => exact this.elim
  | bapp x e hx _ ih =>
    simp only [Expr.subst, Val.substList_eq_map, List.map_cons, List.map_nil]
    rw [Val.subst_rename]
    exact .bapp _ _ (Finset.mem_image_of_mem _ hx)
      (ih (fun s hs => hb s (by simp [Expr.binders, hs])))
  | fapp f e hf _ ih =>
    simp only [Expr.subst, Val.substList_eq_map, List.map_cons, List.map_nil, Val.subst,
      Multiset.map_add, Multiset.map_replicate, Res.rename]
    exact .fapp f _ hf (ih (fun s hs => hb s (by simp [Expr.binders, hs])))
  | prim op vs hv =>
    simp only [Expr.subst, Val.substList_eq_map, Multiset.map_zero]
    refine .prim op _ (fun v hv' => ?_)
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv'
    have := hv w hw
    cases w with
    | var x =>
      rw [Val.subst_rename]
      rcases this with h | h
      · exact .inl (Finset.mem_image_of_mem _ h)
      · exact .inr (Finset.mem_image_of_mem _ h)
    | lit _ => exact this
    | fn _ => exact this.elim
    | ctor _ _ => exact this.elim
  | @letIn U₀ Δ₀ Γ₁ Γ₂ Γ₃ xs e₁ e₂ h2 _ _ hfr ih1 ih2 =>
    have hxs : Binder.AvoidRename a y xs := fun b hb' =>
      hb b.name (by simp only [Expr.binders, List.mem_append, List.mem_map]
                    exact .inl (.inl ⟨b, hb', rfl⟩))
    have ha : a ∉ xs.map (·.name) := by
      simp only [List.mem_map, not_exists, not_and]
      exact fun b hb' h' => (hxs b hb').1 h'
    simp only [Expr.subst, Subst.remove_single ha, Multiset.map_add]
    have h1 := ih1 (fun s hs => hb s (by simp [Expr.binders, hs]))
    have h2' := ih2 (fun s hs => hb s (by simp [Expr.binders, hs]))
    rw [Finset.image_union] at h1
    rw [Finset.image_union, Binder.scalars_rename hxs, Multiset.map_add, Multiset.map_add,
      Binder.owned_rename hxs] at h2'
    refine .letIn _ _ _ xs _ _ ?_ ?_ h2' ?_
    · intro r hr
      obtain ⟨r', hr', rfl⟩ := Multiset.mem_map.mp hr
      obtain ⟨x, rfl⟩ := h2 r' hr'
      exact ⟨_, rfl⟩
    · have : (Γ₂.vars.toFinset).image (renameVar a y) =
          (Ctx.vars (Γ₂.map (Res.rename (renameVar a y)))).toFinset := by
        rw [Ctx.vars_map_rename, Multiset.toFinset_map]
      rw [← this]; exact h1
    · have := hfr.rename hxs
      simpa [Multiset.map_add] using this
  | bmatch x bs hx hfr _ ih =>
    simp only [Expr.subst, Val.substList_eq_map, List.map_cons, List.map_nil,
      Expr.substBranches_eq_map]
    rw [Val.subst_rename]
    have hbs : ∀ b ∈ bs, Binder.AvoidRename a y b.binders ∧
        (∀ s ∈ b.body.binders, s ≠ a ∧ Var.name s ≠ y) := fun b hb' =>
      ⟨fun c hc => hb c.name (by
        simp only [Expr.binders, List.mem_append]
        exact .inr (Expr.mem_bindersB hb' (.inl (List.mem_map_of_mem hc)))),
       fun s hs => hb s (by
        simp only [Expr.binders, List.mem_append]
        exact .inr (Expr.mem_bindersB hb' (.inr hs)))⟩
    refine .bmatch _ _ (hx.imp (Finset.mem_image_of_mem _) (Finset.mem_image_of_mem _))
      (fun b' hb' => ?_) (fun b' hb' => ?_)
    · obtain ⟨b, hbm, rfl⟩ := List.mem_map.mp hb'
      exact (hfr b hbm).rename (hbs b hbm).1
    · obtain ⟨b, hbm, rfl⟩ := List.mem_map.mp hb'
      have ha : a ∉ b.binders.map (·.name) := by
        simp only [List.mem_map, not_exists, not_and]
        exact fun c hc h' => ((hbs b hbm).1 c hc).1 h'
      have := ih b hbm (hbs b hbm).2
      rw [Finset.image_union, Finset.image_union, Binder.scalars_rename (hbs b hbm).1,
        Binder.ownedSet_rename (hbs b hbm).1] at this
      show Wf cfg _ _ _ (Expr.subst (Subst.remove [(a, Val.var y)] b.binders) b.body)
      rw [Subst.remove_single ha]; exact this
  | @dmatch U₀ Δ₀ Γ₀ x bs hfr _ ih =>
    simp only [Expr.subst, Val.substList_eq_map, List.map_cons, List.map_nil,
      Expr.substBranches_eq_map, Multiset.map_add, Multiset.map_singleton, Res.rename]
    rw [Val.subst_rename]
    have hbs : ∀ b ∈ bs, Binder.AvoidRename a y b.binders ∧
        (∀ s ∈ b.body.binders, s ≠ a ∧ Var.name s ≠ y) := fun b hb' =>
      ⟨fun c hc => hb c.name (by
        simp only [Expr.binders, List.mem_append]
        exact .inr (Expr.mem_bindersB hb' (.inl (List.mem_map_of_mem hc)))),
       fun s hs => hb s (by
        simp only [Expr.binders, List.mem_append]
        exact .inr (Expr.mem_bindersB hb' (.inr hs)))⟩
    refine .dmatch _ _ (fun b' hb' => ?_) (fun b' hb' => ?_)
    · obtain ⟨b, hbm, rfl⟩ := List.mem_map.mp hb'
      exact (hfr b hbm).rename (hbs b hbm).1
    · obtain ⟨b, hbm, rfl⟩ := List.mem_map.mp hb'
      have ha : a ∉ b.binders.map (·.name) := by
        simp only [List.mem_map, not_exists, not_and]
        exact fun c hc h' => ((hbs b hbm).1 c hc).1 h'
      have := ih b hbm (hbs b hbm).2
      rw [Finset.image_union, Binder.scalars_rename (hbs b hbm).1, Multiset.map_add,
        Multiset.map_add, Binder.owned_rename (hbs b hbm).1] at this
      show Wf cfg _ _ _ (Expr.subst (Subst.remove [(a, Val.var y)] b.binders) b.body)
      rw [Subst.remove_single ha]
      convert this using 2
  | empty _ ih =>
    simpa [Multiset.map_add, Res.rename] using Wf.empty (ih hb)
  | drop x hf _ ih =>
    simp only [Expr.subst, Multiset.map_add, Multiset.map_singleton, Res.rename]
    rw [Val.subst_rename]
    exact .drop _ hf (ih (fun s hs => hb s (by simp [Expr.binders, hs])))
  | free k hf hk _ ih =>
    simp only [Expr.subst, Multiset.map_add, Multiset.map_singleton, Res.rename]
    exact .free k hf hk (ih (fun s hs => hb s (by simp [Expr.binders, hs])))
  | inst k hk _ ih =>
    have := ih hb
    simp only [Multiset.map_add, Multiset.map_singleton, Res.rename] at this ⊢
    exact .inst k hk this
  | weaken _ ih =>
    simpa [Multiset.map_add, Res.rename] using Wf.weaken (ih hb)

end FIP
