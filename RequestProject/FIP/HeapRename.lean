module

public import RequestProject.FIP.HeapSyntax

@[expose] public section

/-!
# Renaming names into locations (Theorem 6)

The heap semantics substitutes locations for the binders of `let`, of function calls, of
applications and of match branches.  Such a renaming preserves well-formedness
(`LWf.rename`) and admissibility (`LExpr.Adm.rename`), with the environments renamed
accordingly.
-/

namespace FIP.Lam

/-- `σ` renames names into locations. -/
structure LSubst.LocRen (σ : LSubst) : Prop where
  loc : ∀ n, σ (.loc n) = none
  val : ∀ y v, σ y = some v → v.IsLoc

/-- The variable a variable is renamed to. -/
def LSubst.ren (σ : LSubst) (y : Var) : Var :=
  match σ y with
  | some (.var z) => z
  | _ => y

/-- Rename an owned resource. -/
def Res.ren (σ : LSubst) : Res → Res
  | .var y => .var (σ.ren y)
  | r => r

namespace LSubst.LocRen

variable {σ : LSubst}

theorem nameOnly (h : σ.LocRen) : σ.NameOnly := by
  refine ⟨h.loc, ?_⟩
  intro y v hy z hz
  obtain ⟨n, rfl⟩ := h.val y v hy
  simp [LVal.dfv] at hz; exact ⟨n, hz⟩

theorem remove (h : σ.LocRen) (xs : List Binder) : (σ.remove xs).LocRen := by
  refine ⟨fun n => by rw [LSubst.remove_loc]; exact h.loc n, ?_⟩
  intro y v hy
  by_cases hx : y ∈ Binder.vars xs
  · rw [LSubst.remove_of_mem hx] at hy; cases hy
  · rw [LSubst.remove_of_not_mem hx] at hy; exact h.val y v hy

theorem subst_var (h : σ.LocRen) (y : Var) : (LVal.var y).subst σ = .var (σ.ren y) := by
  simp only [LVal.subst, LSubst.ren]
  cases hy : σ y with
  | none => rfl
  | some v =>
    obtain ⟨n, rfl⟩ := h.val y v hy
    rfl

theorem ren_cases (h : σ.LocRen) (y : Var) : σ.ren y = y ∨ ∃ n, σ.ren y = .loc n := by
  simp only [LSubst.ren]
  cases hy : σ y with
  | none => exact .inl rfl
  | some v =>
    obtain ⟨n, rfl⟩ := h.val y v hy
    exact .inr ⟨n, rfl⟩

theorem ren_name (h : σ.LocRen) {y : Var} {s : String} (hy : σ.ren y = .name s) :
    y = .name s := by
  rcases h.ren_cases y with h' | ⟨n, h'⟩
  · rw [← h', hy]
  · rw [h'] at hy; cases hy

theorem ren_loc (h : σ.LocRen) (n : Nat) : σ.ren (.loc n) = .loc n := by
  simp [LSubst.ren, h.loc n]

theorem ren_not_mem (h : σ.LocRen) {xs : List Binder} {y : Var} (hy : y ∉ Binder.vars xs) :
    σ.ren y ∉ Binder.vars xs := by
  rcases h.ren_cases y with h' | ⟨n, h'⟩
  · rwa [h']
  · rw [h']; exact loc_not_mem_vars xs n

end LSubst.LocRen

theorem LSubst.ren_remove_of_not_mem (σ : LSubst) {xs : List Binder} {y : Var}
    (h : y ∉ Binder.vars xs) : (σ.remove xs).ren y = σ.ren y := by
  simp only [LSubst.ren]; rw [LSubst.remove_of_not_mem h]

theorem LSubst.ren_remove_of_mem (σ : LSubst) {xs : List Binder} {y : Var}
    (h : y ∈ Binder.vars xs) : (σ.remove xs).ren y = y := by
  simp only [LSubst.ren]; rw [LSubst.remove_of_mem h]

theorem LVal.substList_vars {σ : LSubst} (h : σ.LocRen) (zs : List Var) :
    LVal.substList σ (zs.map .var) = (zs.map σ.ren).map .var := by
  rw [LVal.substList_eq_map]; simp [h.subst_var]

/-! ## Free variables of a renamed expression -/

theorem or_and_exists_mem_append {α β : Type} {P Q : α → Prop} {f : α → β} {y : β} :
    ((∃ z, P z ∧ f z = y) ∨ ∃ z, Q z ∧ f z = y) ↔ ∃ z, (P z ∨ Q z) ∧ f z = y := by
  constructor
  · rintro (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩)
    · exact ⟨z, .inl hz, rfl⟩
    · exact ⟨z, .inr hz, rfl⟩
  · rintro ⟨z, hz | hz, rfl⟩
    · exact .inl ⟨z, hz, rfl⟩
    · exact .inr ⟨z, hz, rfl⟩

theorem filter_ren {σ : LSubst} (hσ : σ.LocRen) (xs : List Binder) (L L' : List Var)
    (hL : ∀ y, y ∈ L' ↔ ∃ z ∈ L, (σ.remove xs).ren z = y) (y : Var) :
    y ∈ L'.filter (· ∉ Binder.vars xs) ↔ ∃ z ∈ L.filter (· ∉ Binder.vars xs), σ.ren z = y := by
  simp only [List.mem_filter, decide_eq_true_eq, hL]
  constructor
  · rintro ⟨⟨z, hz, rfl⟩, hy⟩
    by_cases hx : z ∈ Binder.vars xs
    · rw [LSubst.ren_remove_of_mem σ hx] at hy; exact absurd hx hy
    · exact ⟨z, ⟨hz, hx⟩, (LSubst.ren_remove_of_not_mem σ hx).symm⟩
  · rintro ⟨z, ⟨hz, hx⟩, rfl⟩
    exact ⟨⟨z, hz, LSubst.ren_remove_of_not_mem σ hx⟩, hσ.ren_not_mem hx⟩

mutual
theorem LVal.fv_rename : ∀ (v : LVal) {σ : LSubst}, σ.LocRen →
    ∀ y, y ∈ (v.subst σ).fv ↔ ∃ z ∈ v.fv, σ.ren z = y
  | .var x, σ, h, y => by rw [h.subst_var]; simp [LVal.fv, eq_comm]
  | .fn _, _, _, y => by simp [LVal.subst, LVal.fv]
  | .ctor c vs, σ, h, y => by
    simp only [LVal.subst, LVal.fv]; exact LVal.fvList_rename vs h y
  | .lam zs xs e, σ, h, y => by
    simp only [LVal.subst, LVal.fv]; exact LVal.fvList_rename zs h y
theorem LVal.fvList_rename : ∀ (vs : List LVal) {σ : LSubst}, σ.LocRen →
    ∀ y, y ∈ LVal.fvList (LVal.substList σ vs) ↔ ∃ z ∈ LVal.fvList vs, σ.ren z = y
  | [], _, _, y => by simp [LVal.substList, LVal.fvList]
  | v :: vs, σ, h, y => by
    simp only [LVal.substList, LVal.fvList, List.mem_append, LVal.fv_rename v h y,
      LVal.fvList_rename vs h y]
    constructor
    · rintro (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩)
      · exact ⟨z, .inl hz, rfl⟩
      · exact ⟨z, .inr hz, rfl⟩
    · rintro ⟨z, hz | hz, rfl⟩
      · exact .inl ⟨z, hz, rfl⟩
      · exact .inr ⟨z, hz, rfl⟩
theorem LExpr.fv_rename : ∀ (e : LExpr) {σ : LSubst}, σ.LocRen →
    ∀ y, y ∈ (e.subst σ).fv ↔ ∃ z ∈ e.fv, σ.ren z = y
  | .ret vs, σ, h, y => by simp only [LExpr.subst, LExpr.fv]; exact LVal.fvList_rename vs h y
  | .app e1 e2, σ, h, y => by
    simp only [LExpr.subst, LExpr.fv, List.mem_append, LExpr.fv_rename e1 h y,
      LExpr.fv_rename e2 h y]
    exact or_and_exists_mem_append
  | .call f e1 e2, σ, h, y => by
    simp only [LExpr.subst, LExpr.fv, List.mem_append, LExpr.fv_rename e1 h y,
      LExpr.fv_rename e2 h y]
    exact or_and_exists_mem_append
  | .letIn xs e1 e2, σ, h, y => by
    simp only [LExpr.subst, LExpr.fv, List.mem_append, LExpr.fv_rename e1 h y,
      filter_ren h xs _ _ (LExpr.fv_rename e2 (h.remove xs)) y]
    exact or_and_exists_mem_append
  | .match x bs, σ, h, y => by
    simp only [LExpr.subst, LExpr.fv, List.mem_append, LVal.fv_rename x h y,
      LExpr.fvB_rename bs h y]
    exact or_and_exists_mem_append
  | .dup x e, σ, h, y => by
    simp only [LExpr.subst, LExpr.fv, List.mem_append, LVal.fv_rename x h y,
      LExpr.fv_rename e h y]
    exact or_and_exists_mem_append
  | .drop x e, σ, h, y => by
    simp only [LExpr.subst, LExpr.fv, List.mem_append, LVal.fv_rename x h y,
      LExpr.fv_rename e h y]
    exact or_and_exists_mem_append
  | .dropru x k e, σ, h, y => by
    simp only [LExpr.subst, LExpr.fv, List.mem_append, LVal.fv_rename x h y,
      LExpr.fv_rename e h y]
    exact or_and_exists_mem_append
  | .free k e, σ, h, y => by simp only [LExpr.subst, LExpr.fv]; exact LExpr.fv_rename e h y
  | .alloc k e, σ, h, y => by simp only [LExpr.subst, LExpr.fv]; exact LExpr.fv_rename e h y
theorem LExpr.fvB_rename : ∀ (bs : List LBranch) {σ : LSubst}, σ.LocRen →
    ∀ y, y ∈ LExpr.fvB (LExpr.substB σ bs) ↔ ∃ z ∈ LExpr.fvB bs, σ.ren z = y
  | [], _, _, y => by simp [LExpr.substB, LExpr.fvB]
  | .mk c xs e :: bs, σ, h, y => by
    simp only [LExpr.substB, LExpr.fvB, List.mem_append,
      filter_ren h xs _ _ (LExpr.fv_rename e (h.remove xs)) y, LExpr.fvB_rename bs h y]
    exact or_and_exists_mem_append
end

/-! ## Renaming environments -/

theorem mem_substB {σ : LSubst} {bs : List LBranch} {b' : LBranch} :
    b' ∈ LExpr.substB σ bs ↔
      ∃ b ∈ bs, b' = .mk b.ctor b.binders (b.body.subst (σ.remove b.binders)) := by
  induction bs with
  | nil => simp [LExpr.substB]
  | cons b bs ih =>
    obtain ⟨c, xs, e⟩ := b
    simp [LExpr.substB, ih, LBranch.ctor, LBranch.binders, LBranch.body]

theorem Ctx.map_ren_remove {σ : LSubst} {xs : List Binder} {Γ : Ctx}
    (h : ∀ y, Res.var y ∈ Γ → y ∉ Binder.vars xs) :
    Γ.map (Res.ren (σ.remove xs)) = Γ.map (Res.ren σ) := by
  apply Multiset.map_congr rfl
  intro r hr
  cases r with
  | var y => simp only [Res.ren]; rw [LSubst.ren_remove_of_not_mem σ (h y hr)]
  | _ => rfl

theorem Binder.ctx_ren_remove (σ : LSubst) (xs : List Binder) :
    (Binder.ctx xs).map (Res.ren (σ.remove xs)) = Binder.ctx xs := by
  simp only [Binder.ctx, Multiset.map_coe, List.map_map]
  congr 1
  apply List.map_congr_left
  intro b hb
  simp only [Function.comp, Res.ren]
  rw [LSubst.ren_remove_of_mem σ (by simp [Binder.vars]; exact ⟨b, hb, rfl⟩)]

theorem varCtx_ren (σ : LSubst) (zs : List Var) :
    (varCtx zs).map (Res.ren σ) = varCtx (zs.map σ.ren) := by
  simp only [varCtx, Multiset.map_coe, List.map_map]
  congr 1

theorem Ctx.vars_ren (σ : LSubst) (Γ : Ctx) :
    Ctx.vars (Γ.map (Res.ren σ)) = (Ctx.vars Γ).map σ.ren := by
  induction Γ using Multiset.induction_on with
  | empty => simp [Ctx.vars]
  | cons r Γ ih =>
    cases r <;> simp_all [Ctx.vars, Res.ren]

theorem Ctx.OnlyVars.ren {Γ : Ctx} (h : Γ.OnlyVars) (σ : LSubst) :
    Ctx.OnlyVars (Γ.map (Res.ren σ)) := by
  intro r hr
  obtain ⟨r', hr', rfl⟩ := Multiset.mem_map.mp hr
  obtain ⟨y, rfl⟩ := h r' hr'
  exact ⟨_, rfl⟩

theorem Finset.image_ren_remove {σ : LSubst} {xs : List Binder} {Δ : Finset Var}
    (h : ∀ y ∈ Δ, y ∉ Binder.vars xs) :
    Δ.image (σ.remove xs).ren = Δ.image σ.ren :=
  Finset.image_congr fun y hy => LSubst.ren_remove_of_not_mem σ (h y hy)

theorem name_mem_vars {b : Binder} {xs : List Binder} (hb : b ∈ xs) :
    Var.name b.name ∈ Binder.vars xs := by
  simp [Binder.vars]; exact ⟨b, hb, rfl⟩

theorem Binder.LFresh.not_mem_Δ {xs : List Binder} {Δ : Finset Var} {Γ : Ctx}
    (h : Binder.LFresh xs Δ Γ) : ∀ y ∈ Δ, y ∉ Binder.vars xs := by
  intro y hy hx
  simp only [Binder.vars, List.mem_map] at hx
  obtain ⟨b, hb, rfl⟩ := hx
  exact (h.2 b hb).1 hy

theorem Binder.LFresh.not_mem_Γ {xs : List Binder} {Δ : Finset Var} {Γ : Ctx}
    (h : Binder.LFresh xs Δ Γ) : ∀ y, Res.var y ∈ Γ → y ∉ Binder.vars xs := by
  intro y hy hx
  simp only [Binder.vars, List.mem_map] at hx
  obtain ⟨b, hb, rfl⟩ := hx
  exact (h.2 b hb).2 hy

theorem Binder.LFresh.ren {xs : List Binder} {Δ : Finset Var} {Γ : Ctx}
    (h : Binder.LFresh xs Δ Γ) {σ : LSubst} (hσ : σ.LocRen) :
    Binder.LFresh xs (Δ.image σ.ren) (Γ.map (Res.ren σ)) := by
  refine ⟨h.1, fun b hb => ⟨?_, ?_⟩⟩
  · intro hm
    obtain ⟨y, hy, hy'⟩ := Finset.mem_image.mp hm
    rw [hσ.ren_name hy'] at hy
    exact (h.2 b hb).1 hy
  · intro hm
    obtain ⟨r, hr, hr'⟩ := Multiset.mem_map.mp hm
    cases r with
    | var y =>
      simp only [Res.ren, Res.var.injEq] at hr'
      rw [hσ.ren_name hr'] at hr
      exact (h.2 b hb).2 hr
    | _ => simp [Res.ren] at hr'

/-! ## Renaming preserves well-formedness -/

mutual
theorem LWfVal.rename {funs : List FName} : ∀ {Δ : Finset Var} {Γ : Ctx} {v : LVal},
    LWfVal funs Δ Γ v → ∀ {σ : LSubst}, σ.LocRen →
    LWfVal funs (Δ.image σ.ren) (Γ.map (Res.ren σ)) (v.subst σ)
  | _, _, _, .var x, σ, h => by
    rw [h.subst_var]; simpa [Res.ren] using LWfVal.var (funs := funs) (σ.ren x)
  | _, _, _, .atom c, σ, h => by
    simpa [LVal.subst, LVal.substList] using LWfVal.atom (funs := funs) c
  | _, _, _, .reuse c vs Γ hne hvs, σ, h => by
    have h1 := LWfVals.rename hvs h
    have hl : (LVal.substList σ vs).length = vs.length := by
      rw [LVal.substList_eq_map, List.length_map]
    have hne' : LVal.substList σ vs ≠ [] := by
      intro h'; apply hne; rw [← List.length_eq_zero_iff, ← hl, h', List.length_nil]
    have := LWfVal.reuse c _ _ hne' h1
    rw [hl] at this
    simpa [LVal.subst, Multiset.map_add, Res.ren] using this
  | _, _, _, .lam zs xs e hwf hzs, σ, h => by
    have hzx : ∀ y, Res.var y ∈ varCtx zs → y ∉ Binder.vars xs := by
      intro y hy
      simp [varCtx] at hy
      exact ((hzs y).mp hy).2
    have h1 := LWf.rename hwf (h.remove xs)
    rw [Finset.image_empty, Multiset.map_add, Binder.ctx_ren_remove,
      Ctx.map_ren_remove hzx, varCtx_ren] at h1
    simp only [LVal.subst]
    rw [LVal.substList_vars h, varCtx_ren]
    refine LWfVal.lam _ xs _ h1 ?_
    intro y
    have key := filter_ren h xs _ _ (LExpr.fv_rename e (h.remove xs)) y
    simp only [List.mem_filter, decide_eq_true_eq] at key
    rw [key]
    simp only [List.mem_map]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, (hzs z).mp hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, (hzs z).mpr hz, rfl⟩
theorem LWfVals.rename {funs : List FName} : ∀ {Δ : Finset Var} {Γ : Ctx} {vs : List LVal},
    LWfVals funs Δ Γ vs → ∀ {σ : LSubst}, σ.LocRen →
    LWfVals funs (Δ.image σ.ren) (Γ.map (Res.ren σ)) (LVal.substList σ vs)
  | _, _, _, .nil, σ, h => by simpa [LVal.substList] using LWfVals.nil (funs := funs)
  | _, _, _, .cons Γ₁ Γ₂ v vs hv hvs, σ, h => by
    rw [Multiset.map_add]
    exact LWfVals.cons _ _ _ _ (LWfVal.rename hv h) (LWfVals.rename hvs h)
theorem LWf.rename {funs : List FName} : ∀ {Δ : Finset Var} {Γ : Ctx} {e : LExpr},
    LWf funs Δ Γ e → ∀ {σ : LSubst}, σ.LocRen →
    LWf funs (Δ.image σ.ren) (Γ.map (Res.ren σ)) (e.subst σ)
  | _, _, _, .tuple hvs, σ, h => .tuple (LWfVals.rename hvs h)
  | Δ, _, _, .call f ys e hf hys he, σ, h => by
    simp only [LExpr.subst]
    refine LWf.call f _ _ hf ?_ (LWf.rename he h)
    intro y hy
    rw [LVal.substList_eq_map] at hy
    obtain ⟨y0, hy0, rfl⟩ := List.mem_map.mp hy
    have hb := hys y0 hy0
    cases y0 with
    | var z => rw [h.subst_var]; exact Finset.mem_image_of_mem _ hb
    | fn g => exact hb
    | ctor _ _ => exact hb.elim
    | lam _ _ _ => exact hb.elim
  | _, _, _, .app Γ₁ Γ₂ e₁ e₂ h₁ h₂, σ, h => by
    rw [Multiset.map_add]
    exact LWf.app _ _ _ _ (LWf.rename h₁ h) (LWf.rename h₂ h)
  | Δ, _, _, .letIn Γ₁ Γ₂ Γ₃ xs e₁ e₂ hov h₁ h₂ hfr, σ, h => by
    have r1 := LWf.rename h₁ h
    have r2 := LWf.rename h₂ (h.remove xs)
    rw [Finset.image_ren_remove hfr.not_mem_Δ, Multiset.map_add, Binder.ctx_ren_remove,
      Ctx.map_ren_remove hfr.not_mem_Γ, Multiset.map_add] at r2
    rw [Finset.image_union, Finset.image_toFinset, ← Ctx.vars_ren] at r1
    simp only [LExpr.subst, Multiset.map_add]
    exact LWf.letIn _ _ _ xs _ _ (Ctx.OnlyVars.ren hov σ) r1 r2
      (by have := hfr.ren h; rwa [Multiset.map_add] at this)
  | Δ, Γ, _, .match x bs hx hfr es hes hbs, σ, h => by
    simp only [LExpr.subst]
    rw [h.subst_var]
    refine LWf.match _ _ ?_ ?_ (fun b' => undups b'.binders.length b'.body) ?_ ?_
    · rcases hx with hx | hx
      · exact .inl (Finset.mem_image_of_mem _ hx)
      · exact .inr (Multiset.mem_map_of_mem (Res.ren σ) hx)
    · intro b' hb'
      obtain ⟨b, hb, rfl⟩ := mem_substB.mp hb'
      exact (hfr b hb).ren h
    · intro b' hb'
      obtain ⟨b, hb, rfl⟩ := mem_substB.mp hb'
      have he := hes b hb
      obtain ⟨c, xs, e⟩ := b
      simp only [LBranch.body, LBranch.binders] at he ⊢
      rw [he, subst_dups, substList_vals_remove]
      have hl : (Binder.vals xs).length = xs.length := by simp [Binder.vals]
      rw [undups_dups_of_length _ _ hl]
    · intro b' hb'
      obtain ⟨b, hb, rfl⟩ := mem_substB.mp hb'
      have he := hes b hb
      have r := LWf.rename (hbs b hb) (h.remove b.binders)
      have hfrb := hfr b hb
      obtain ⟨c, xs, e⟩ := b
      simp only [LBranch.body, LBranch.binders] at he hfrb r ⊢
      rw [he, subst_dups, substList_vals_remove]
      have hl : (Binder.vals xs).length = xs.length := by simp [Binder.vals]
      rw [undups_dups_of_length _ _ hl]
      rwa [Finset.image_ren_remove hfrb.not_mem_Δ, Multiset.map_add,
        Binder.ctx_ren_remove, Ctx.map_ren_remove hfrb.not_mem_Γ] at r
  | _, _, _, .dup x hx he, σ, h => by
    simp only [LExpr.subst]
    rw [h.subst_var]
    refine LWf.dup _ ?_ ?_
    · rcases hx with hx | hx
      · exact .inl (Finset.mem_image_of_mem _ hx)
      · exact .inr (Multiset.mem_map_of_mem (Res.ren σ) hx)
    · have := LWf.rename he h
      simpa [Multiset.map_add, Res.ren] using this
  | _, _, _, .drop x he, σ, h => by
    simp only [LExpr.subst]
    rw [h.subst_var, Multiset.map_add]
    simpa [Res.ren] using LWf.drop (σ.ren x) (LWf.rename he h)
  | _, _, _, .dropru x k he, σ, h => by
    simp only [LExpr.subst]
    rw [h.subst_var, Multiset.map_add]
    have := LWf.rename he h
    rw [Multiset.map_add] at this
    simpa [Res.ren] using LWf.dropru (σ.ren x) k this
  | _, _, _, .free k hk he, σ, h => by
    simp only [LExpr.subst]
    rw [Multiset.map_add]
    simpa [Res.ren] using LWf.free k hk (LWf.rename he h)
  | _, _, _, .alloc k hk he, σ, h => by
    simp only [LExpr.subst]
    have := LWf.rename he h
    rw [Multiset.map_add] at this
    exact LWf.alloc k hk (by simpa [Res.ren] using this)
  | _, _, _, .empty he, σ, h => by
    rw [Multiset.map_add]
    simpa [Res.ren] using LWf.empty (LWf.rename he h)
end

/-! ## Renaming preserves admissibility -/

mutual
theorem LVal.Adm.rename : ∀ {v : LVal}, LVal.Adm v → ∀ {σ : LSubst}, σ.LocRen →
    LVal.Adm (v.subst σ)
  | _, .var x, σ, h => by rw [h.subst_var]; exact .var _
  | _, .ctor c vs hvs, σ, h => by
    simp only [LVal.subst]
    refine .ctor c _ fun v hv => ?_
    rw [LVal.substList_eq_map] at hv
    obtain ⟨v0, hv0, rfl⟩ := List.mem_map.mp hv
    exact LVal.Adm.rename (hvs v0 hv0) h
  | _, .lam zs xs e hzs hnd he, σ, h => by
    simp only [LVal.subst]
    refine .lam _ xs _ (fun v hv => ?_) hnd (LExpr.Adm.rename he (h.remove xs))
    rw [LVal.substList_eq_map] at hv
    obtain ⟨v0, hv0, rfl⟩ := List.mem_map.mp hv
    exact LVal.Adm.rename (hzs v0 hv0) h
theorem LExpr.Adm.rename : ∀ {e : LExpr}, LExpr.Adm e → ∀ {σ : LSubst}, σ.LocRen →
    LExpr.Adm (e.subst σ)
  | _, .ret vs hvs, σ, h => by
    simp only [LExpr.subst]
    refine .ret _ fun v hv => ?_
    rw [LVal.substList_eq_map] at hv
    obtain ⟨v0, hv0, rfl⟩ := List.mem_map.mp hv
    exact LVal.Adm.rename (hvs v0 hv0) h
  | _, .app _ _ h1 h2, σ, h => .app _ _ (LExpr.Adm.rename h1 h) (LExpr.Adm.rename h2 h)
  | _, .call f _ _ h1 h2, σ, h => .call f _ _ (LExpr.Adm.rename h1 h) (LExpr.Adm.rename h2 h)
  | _, .letIn xs _ _ h1 h2, σ, h =>
    .letIn xs _ _ (LExpr.Adm.rename h1 h) (LExpr.Adm.rename h2 (h.remove xs))
  | _, .match x bs hbs, σ, h => by
    simp only [LExpr.subst]
    rw [h.subst_var]
    refine .match _ _ fun b' hb' => ?_
    obtain ⟨b, hb, rfl⟩ := mem_substB.mp hb'
    exact LBranch.Adm.rename (hbs b hb) h
  | _, .dup x e hx he, σ, h => .dup _ _ (LVal.Adm.rename hx h) (LExpr.Adm.rename he h)
  | _, .drop x e hx he, σ, h => .drop _ _ (LVal.Adm.rename hx h) (LExpr.Adm.rename he h)
  | _, .free k e he, σ, h => .free k _ (LExpr.Adm.rename he h)
  | _, .alloc k e he, σ, h => .alloc k _ (LExpr.Adm.rename he h)
theorem LBranch.Adm.rename : ∀ {x : Var} {b : LBranch}, LBranch.Adm x b →
    ∀ {σ : LSubst}, σ.LocRen →
    LBranch.Adm (σ.ren x) (.mk b.ctor b.binders (b.body.subst (σ.remove b.binders)))
  | _, _, .plain c xs e x he, σ, h => .plain _ _ _ _ (LExpr.Adm.rename he (h.remove xs))
  | _, _, .reuse c xs e x he hx, σ, h => by
    simp only [LBranch.ctor, LBranch.binders, LBranch.body]
    rw [subst_dups, substList_vals_remove]
    simp only [LExpr.subst]
    rw [(h.remove xs).subst_var, LSubst.ren_remove_of_not_mem σ hx]
    exact .reuse c xs _ _ (LExpr.Adm.rename he (h.remove xs)) (h.ren_not_mem hx)
end

theorem LBranch.Adm.rename' {x : Var} {bs : List LBranch} (h : ∀ b ∈ bs, LBranch.Adm x b)
    {σ : LSubst} (hσ : σ.LocRen) : ∀ b ∈ LExpr.substB σ bs, LBranch.Adm (σ.ren x) b := by
  intro b' hb'
  obtain ⟨b, hb, rfl⟩ := mem_substB.mp hb'
  exact (h b hb).rename hσ

/-! ## The free variables of a well-formed expression are available -/

theorem Ctx.mem_vars {Γ : Ctx} {y : Var} : y ∈ Ctx.vars Γ ↔ Res.var y ∈ Γ := by
  simp only [Ctx.vars, Multiset.mem_filterMap]
  constructor
  · rintro ⟨r, hr, h⟩
    cases r <;> simp at h
    subst h; exact hr
  · intro h; exact ⟨_, h, rfl⟩

theorem not_mem_ctx {y : Var} {xs : List Binder} (h : y ∉ Binder.vars xs) :
    Res.var y ∉ Binder.ctx xs := by
  intro h'
  apply h
  simp only [Binder.ctx, Multiset.mem_coe, List.mem_map, Res.var.injEq] at h'
  obtain ⟨b, hb, rfl⟩ := h'
  exact name_mem_vars hb

mutual
theorem LWfVal.dfv_sub {funs : List FName} : ∀ {Δ : Finset Var} {Γ : Ctx} {v : LVal},
    LWfVal funs Δ Γ v → ∀ y ∈ v.dfv, y ∈ Δ ∨ Res.var y ∈ Γ
  | _, _, _, .var x, y, hy => by simp [LVal.dfv] at hy; subst hy; simp
  | _, _, _, .atom c, y, hy => by simp [LVal.dfv, LVal.dfvList] at hy
  | _, _, _, .reuse c vs Γ _ hvs, y, hy => by
    simp only [LVal.dfv] at hy
    rcases LWfVals.dfv_sub hvs y hy with h | h
    · exact .inl h
    · exact .inr (Multiset.mem_add.mpr (.inl h))
  | _, _, _, .lam zs xs e hwf hzs, y, hy => by
    simp only [LVal.dfv, List.mem_append, List.mem_filter, decide_eq_true_eq] at hy
    rcases hy with hy | ⟨hy, hx⟩
    · rw [LVal.mem_dfvList] at hy
      obtain ⟨v, hv, hyv⟩ := hy
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hv
      simp [LVal.dfv] at hyv; subst hyv
      exact .inr (by simp [varCtx, hz])
    · rcases LWf.dfv_sub hwf y hy with h | h
      · simp at h
      · rcases Multiset.mem_add.mp h with h | h
        · exact .inr h
        · exact absurd h (not_mem_ctx hx)
theorem LWfVals.dfv_sub {funs : List FName} : ∀ {Δ : Finset Var} {Γ : Ctx} {vs : List LVal},
    LWfVals funs Δ Γ vs → ∀ y ∈ LVal.dfvList vs, y ∈ Δ ∨ Res.var y ∈ Γ
  | _, _, _, .nil, y, hy => by simp [LVal.dfvList] at hy
  | _, _, _, .cons Γ₁ Γ₂ v vs hv hvs, y, hy => by
    simp only [LVal.dfvList, List.mem_append] at hy
    rcases hy with hy | hy
    · rcases LWfVal.dfv_sub hv y hy with h | h
      · exact .inl h
      · exact .inr (Multiset.mem_add.mpr (.inl h))
    · rcases LWfVals.dfv_sub hvs y hy with h | h
      · exact .inl h
      · exact .inr (Multiset.mem_add.mpr (.inr h))
theorem LWf.dfv_sub {funs : List FName} : ∀ {Δ : Finset Var} {Γ : Ctx} {e : LExpr},
    LWf funs Δ Γ e → ∀ y ∈ e.dfv, y ∈ Δ ∨ Res.var y ∈ Γ
  | _, _, _, .tuple hvs, y, hy => LWfVals.dfv_sub hvs y hy
  | _, _, _, .call f ys e hf hys he, y, hy => by
    simp only [LExpr.dfv, List.mem_append] at hy
    rcases hy with hy | hy
    · rw [LVal.mem_dfvList] at hy
      obtain ⟨v, hv, hyv⟩ := hy
      have hb := hys v hv
      cases v with
      | var z => simp [LVal.dfv] at hyv; subst hyv; exact .inl hb
      | fn g => simp [LVal.dfv] at hyv
      | ctor _ _ => exact hb.elim
      | lam _ _ _ => exact hb.elim
    · exact LWf.dfv_sub he y hy
  | _, _, _, .app Γ₁ Γ₂ e₁ e₂ h₁ h₂, y, hy => by
    simp only [LExpr.dfv, List.mem_append] at hy
    rcases hy with hy | hy
    · rcases LWf.dfv_sub h₁ y hy with h | h
      · exact .inl h
      · exact .inr (Multiset.mem_add.mpr (.inl h))
    · rcases LWf.dfv_sub h₂ y hy with h | h
      · exact .inl h
      · exact .inr (Multiset.mem_add.mpr (.inr h))
  | _, _, _, .letIn Γ₁ Γ₂ Γ₃ xs e₁ e₂ _ h₁ h₂ _, y, hy => by
    simp only [LExpr.dfv, List.mem_append, List.mem_filter, decide_eq_true_eq] at hy
    rcases hy with hy | ⟨hy, hx⟩
    · rcases LWf.dfv_sub h₁ y hy with h | h
      · rcases Finset.mem_union.mp h with h | h
        · exact .inl h
        · rw [Multiset.mem_toFinset, Ctx.mem_vars] at h
          exact .inr (by simp [h])
      · exact .inr (by simp [h])
    · rcases LWf.dfv_sub h₂ y hy with h | h
      · exact .inl h
      · rcases Multiset.mem_add.mp h with h | h
        · exact .inr (by rw [add_assoc]; exact Multiset.mem_add.mpr (.inr h))
        · exact absurd h (not_mem_ctx hx)
  | _, _, _, .match x bs hx hfr es hes hbs, y, hy => by
    simp only [LExpr.dfv, List.mem_append] at hy
    rcases hy with hy | hy
    · simp [LVal.dfv] at hy; subst hy; exact hx
    · rw [LExpr.mem_dfvB] at hy
      obtain ⟨b, hb, hyb, hx'⟩ := hy
      rw [hes b hb, dfv_dups, dfvList_vals] at hyb
      rcases hyb with hyb | hyb
      · exact absurd hyb hx'
      · rcases LWf.dfv_sub (hbs b hb) y hyb with h | h
        · exact .inl h
        · rcases Multiset.mem_add.mp h with h | h
          · exact .inr h
          · exact absurd h (not_mem_ctx hx')
  | _, _, _, .dup x hx he, y, hy => by
    simp only [LExpr.dfv, List.mem_append] at hy
    rcases hy with hy | hy
    · simp [LVal.dfv] at hy; subst hy; exact hx
    · rcases LWf.dfv_sub he y hy with h | h
      · exact .inl h
      · rcases Multiset.mem_add.mp h with h | h
        · exact .inr h
        · simp at h; subst h; exact hx
  | _, _, _, .drop x he, y, hy => by
    simp only [LExpr.dfv, List.mem_append] at hy
    rcases hy with hy | hy
    · simp [LVal.dfv] at hy; subst hy; exact .inr (by simp)
    · rcases LWf.dfv_sub he y hy with h | h
      · exact .inl h
      · exact .inr (Multiset.mem_add.mpr (.inl h))
  | _, _, _, .dropru x k he, y, hy => by
    simp only [LExpr.dfv, List.mem_append] at hy
    rcases hy with hy | hy
    · simp [LVal.dfv] at hy; subst hy; exact .inr (by simp)
    · rcases LWf.dfv_sub he y hy with h | h
      · exact .inl h
      · rcases Multiset.mem_add.mp h with h | h
        · exact .inr (Multiset.mem_add.mpr (.inl h))
        · simp at h
  | _, _, _, .free k hk he, y, hy => by
    rcases LWf.dfv_sub he y hy with h | h
    · exact .inl h
    · exact .inr (Multiset.mem_add.mpr (.inl h))
  | _, _, _, .alloc k hk he, y, hy => by
    rcases LWf.dfv_sub he y hy with h | h
    · exact .inl h
    · rcases Multiset.mem_add.mp h with h | h
      · exact .inr h
      · simp at h
  | _, _, _, .empty he, y, hy => by
    rcases LWf.dfv_sub he y hy with h | h
    · exact .inl h
    · exact .inr (Multiset.mem_add.mpr (.inl h))
end

end FIP.Lam
