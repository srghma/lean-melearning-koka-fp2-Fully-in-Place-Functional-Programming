module

public import RequestProject.AppE_HeapSoundness.HeapDrop

@[expose] public section

/-!
# The locations of a well-formed `λfip` expression

The locations occurring in a well-formed expression `Δ | Γ ⊢ e`, after a substitution of
variables for its variables, come from the environments `Δ` and `Γ` (`LWf.locs_subst`).  In
particular, a closed body typed in an environment without locations has no locations
(`LWf.locs_nil`), and the locations of `e[ρ]` are the images by `ρ` of its environments
(`LWf.locs_ren`).
-/

namespace FIP.Lam

/-- A substitution of variables for variables. -/
def VarSubst {n m : Nat} (τ : Fin n → LVal m) : Prop := ∀ i, ∃ x, τ i = .var x

theorem VarSubst.locs {m : Nat} (ρ : Fin m → Nat) : VarSubst (LSubst.locs ρ) :=
  fun _ => ⟨_, rfl⟩

theorem VarSubst.subst_var {n m : Nat} {τ : Fin n → LVal m} (h : VarSubst τ) (x : Var n) :
    ∃ y, (LVal.var x).subst τ = .var y := by
  cases x with
  | bvar i => exact h i
  | loc l => exact ⟨.loc l, rfl⟩

theorem VarSubst.up {n m : Nat} {τ : Fin n → LVal m} (h : VarSubst τ) (k : Nat) :
    VarSubst (LSubst.up k τ) := by
  intro i
  simp only [LSubst.up]
  split
  · exact ⟨_, rfl⟩
  · obtain ⟨x, hx⟩ := h ⟨i.val - k, by omega⟩
    rw [hx, LVal.shift_var]; exact ⟨_, rfl⟩

theorem Var.shift_eq_loc {n : Nat} {k : Nat} {y : Var n} {l : Nat} (h : y.shift k = .loc l) :
    y = .loc l := by
  cases y <;> simp_all [Var.shift]

/-- A variable under a binder that is sent to a location comes from the outer scope. -/
theorem binder_loc {n m k : Nat} {τ : Fin n → LVal m} (hτ : VarSubst τ) {Δ : Finset (Var n)}
    {Γ : Ctx n} {x' : Var (n + k)} {l : Nat}
    (hx' : x' ∈ Vars.shift k Δ ∨ Res.var x' ∈ Ctx.shift k Γ + bCtx n k)
    (he : (LVal.var x').subst (LSubst.up k τ) = .var (.loc l)) :
    ∃ x, (x ∈ Δ ∨ Res.var x ∈ Γ) ∧ (LVal.var x).subst τ = .var (.loc l) := by
  have shift_case : ∀ x : Var n, (LVal.var (x.shift k)).subst (LSubst.up k τ) = .var (.loc l) →
      (LVal.var x).subst τ = .var (.loc l) := by
    intro x hx
    rw [LSubst.up_shift] at hx
    obtain ⟨y, hy⟩ := hτ.subst_var x
    rw [hy, LVal.shift_var] at hx
    rw [hy, Var.shift_eq_loc (LVal.var.inj hx)]
  rcases hx' with hx' | hx'
  · obtain ⟨x, hx, rfl⟩ := Vars.mem_shift_iff.mp hx'
    exact ⟨x, .inl hx, shift_case x he⟩
  · rcases Multiset.mem_add.mp hx' with hx' | hx'
    · obtain ⟨r, hr, hre⟩ := Ctx.mem_shift_iff.mp hx'
      cases r with
      | var x =>
        simp only [Res.shift, Res.var.injEq] at hre; subst hre
        exact ⟨x, .inr hr, shift_case x he⟩
      | credit j => simp [Res.shift] at hre
      | alloc => simp [Res.shift] at hre
    · simp only [bCtx, Multiset.mem_coe, List.mem_map, List.mem_finRange, true_and,
        Res.var.injEq] at hx'
      obtain ⟨j, rfl⟩ := hx'
      simp [Var.newB, LSubst.up] at he

theorem LVals.locs_eq {n : Nat} : ∀ vs : LVals n, vs.locs = vs.toList.flatMap LVal.locs
  | .nil => rfl
  | .cons v vs => by simp [LVals.locs, LVals.locs_eq vs]

theorem LExpr.locs_dups {n : Nat} : ∀ (vs : List (LVal n)) (e : LExpr n),
    (dups vs e).locs = vs.flatMap LVal.locs ++ e.locs
  | [], e => rfl
  | v :: vs, e => by simp [dups, LExpr.locs, LExpr.locs_dups vs e]

theorem bvals_locs {m k : Nat} : (bvals m k).flatMap LVal.locs = [] := by
  simp [bvals, LVal.locs, Var.newB]

theorem LBranches.mem_locs_subst {n m : Nat} (τ : Fin n → LVal m) :
    ∀ {bs : LBranches n} {l : Nat}, l ∈ (bs.subst τ).locs →
      ∃ b ∈ bs.toList, l ∈ (b.body.subst (LSubst.up b.k τ)).locs
  | .nil, l, h => by simp [LBranches.subst, LBranches.locs] at h
  | .cons c k e bs, l, h => by
    simp only [LBranches.subst, LBranches.locs, List.mem_append] at h
    rcases h with h | h
    · exact ⟨⟨c, k, e⟩, by simp, h⟩
    · obtain ⟨b, hb, hl⟩ := LBranches.mem_locs_subst τ h
      exact ⟨b, by simp [hb], hl⟩

/-- **The locations of a well-formed expression** come from its environments. -/
theorem LWf.locs_subst {funs : List FName} {n : Nat} {Δ : Finset (Var n)} {Γ : Ctx n}
    {e : LExpr n} (h : LWf funs Δ Γ e) :
    ∀ {m : Nat} (τ : Fin n → LVal m), VarSubst τ → ∀ l ∈ (e.subst τ).locs,
      ∃ x, (x ∈ Δ ∨ Res.var x ∈ Γ) ∧ (LVal.var x).subst τ = .var (.loc l) := by
  induction h using LWf.rec
    (motive_1 := @fun n Δ Γ v _ => ∀ {m : Nat} (τ : Fin n → LVal m), VarSubst τ →
      ∀ l ∈ (v.subst τ).locs, ∃ x, Res.var x ∈ Γ ∧ (LVal.var x).subst τ = .var (.loc l))
    (motive_2 := @fun n Δ Γ vs _ => ∀ {m : Nat} (τ : Fin n → LVal m), VarSubst τ →
      ∀ v ∈ vs, ∀ l ∈ (v.subst τ).locs,
        ∃ x, Res.var x ∈ Γ ∧ (LVal.var x).subst τ = .var (.loc l)) with
  | var x =>
    rename_i m τ hτ l hl
    obtain ⟨y, hy⟩ := hτ.subst_var x
    rw [hy] at hl
    cases y with
    | loc l' => simp [LVal.locs] at hl; subst hl; exact ⟨x, by simp, hy⟩
    | bvar i => simp [LVal.locs] at hl
  | atom c => rename_i m τ hτ l hl; simp [LVal.subst, LVals.subst, LVal.locs, LVals.locs] at hl
  | reuse c vs Γ hne hvs ih =>
    rename_i m τ hτ l hl
    simp only [LVal.subst, LVal.locs, LVals.locs_eq, LVals.toList_subst, List.mem_flatMap,
      List.mem_map] at hl
    obtain ⟨_, ⟨v, hv, rfl⟩, hl⟩ := hl
    obtain ⟨x, hx, hxe⟩ := ih τ hτ v hv l hl
    exact ⟨x, Multiset.mem_add.mpr (.inl hx), hxe⟩
  | lam zs c k e hc he _ =>
    rename_i m τ hτ l hl
    have hsub : (LVal.lam (LVals.ofList (zs.map LVal.var)) c k e).subst τ =
        .lam ((LVals.ofList (zs.map LVal.var)).subst τ) c k e := rfl
    rw [hsub] at hl
    simp only [LVal.locs, LVals.locs_eq, LVals.toList_subst, LVals.toList_ofList,
      List.map_map, List.mem_flatMap, List.mem_map] at hl
    obtain ⟨_, ⟨z, hz, rfl⟩, hl⟩ := hl
    simp only [Function.comp_apply] at hl
    obtain ⟨y, hy⟩ := hτ.subst_var z
    rw [hy] at hl
    cases y with
    | loc l' =>
      simp [LVal.locs] at hl; subst hl
      exact ⟨z, by simp [varCtx, hz], hy⟩
    | bvar i => simp [LVal.locs] at hl
  | nil => rename_i m τ hτ v hv l hl; simp at hv
  | cons Γ₁ Γ₂ v vs hv hvs ih₁ ih₂ =>
    rename_i m τ hτ w hw l hl
    rcases List.mem_cons.mp hw with rfl | hw
    · obtain ⟨x, hx, hxe⟩ := ih₁ τ hτ l hl
      exact ⟨x, Multiset.mem_add.mpr (.inl hx), hxe⟩
    · obtain ⟨x, hx, hxe⟩ := ih₂ τ hτ w hw l hl
      exact ⟨x, Multiset.mem_add.mpr (.inr hx), hxe⟩
  | tuple vs hvs ih =>
    intro m τ hτ l hl
    simp only [LExpr.subst, LExpr.locs, LVals.locs_eq, LVals.toList_subst, List.mem_flatMap,
      List.mem_map] at hl
    obtain ⟨_, ⟨v, hv, rfl⟩, hl⟩ := hl
    obtain ⟨x, hx, hxe⟩ := ih τ hτ v hv l hl
    exact ⟨x, .inr hx, hxe⟩
  | call f ys e hf hys he ih =>
    intro m τ hτ l hl
    simp only [LExpr.subst, LExpr.locs, List.mem_append, LVals.locs_eq, LVals.toList_subst,
      List.mem_flatMap, List.mem_map] at hl
    rcases hl with ⟨_, ⟨y, hy, rfl⟩, hl⟩ | hl
    · have := hys y hy
      cases y with
      | var x =>
        obtain ⟨z, hz⟩ := hτ.subst_var x
        rw [hz] at hl
        cases z with
        | loc l' => simp [LVal.locs] at hl; subst hl; exact ⟨x, .inl this, hz⟩
        | bvar i => simp [LVal.locs] at hl
      | fn g => simp [LVal.subst, LVal.locs] at hl
      | ctor c vs => exact this.elim
      | lam zs c k b => exact this.elim
    · exact ih τ hτ l hl
  | app Γ₁ Γ₂ e₁ e₂ h₁ h₂ ih₁ ih₂ =>
    intro m τ hτ l hl
    simp only [LExpr.subst, LExpr.locs, List.mem_append] at hl
    rcases hl with hl | hl
    · obtain ⟨x, hx, hxe⟩ := ih₁ τ hτ l hl
      exact ⟨x, hx.imp_right (fun h => Multiset.mem_add.mpr (.inl h)), hxe⟩
    · obtain ⟨x, hx, hxe⟩ := ih₂ τ hτ l hl
      exact ⟨x, hx.imp_right (fun h => Multiset.mem_add.mpr (.inr h)), hxe⟩
  | letIn Γ₁ Γ₂ Γ₃ k e₁ e₂ hΓ₂ h₁ h₂ ih₁ ih₂ =>
    intro m τ hτ l hl
    simp only [LExpr.subst, LExpr.locs, List.mem_append] at hl
    rcases hl with hl | hl
    · obtain ⟨x, hx, hxe⟩ := ih₁ τ hτ l hl
      refine ⟨x, ?_, hxe⟩
      rcases hx with hx | hx
      · rcases Finset.mem_union.mp hx with hx | hx
        · exact .inl hx
        · have : Res.var x ∈ Γ₂ := by
            simp only [Multiset.mem_toFinset, Ctx.vars, Multiset.mem_filterMap] at hx
            obtain ⟨r, hr, hre⟩ := hx
            cases r <;> simp_all
          exact .inr (by simp [this])
      · exact .inr (by simp [hx])
    · obtain ⟨x', hx', hxe'⟩ := ih₂ (LSubst.up k τ) (hτ.up k) l hl
      obtain ⟨x, hx, hxe⟩ := binder_loc hτ hx' hxe'
      refine ⟨x, ?_, hxe⟩
      rcases hx with hx | hx
      · exact .inl hx
      · exact .inr (by
          rcases Multiset.mem_add.mp hx with h | h <;> simp [h])
  | «match» x bs hx es hes hbs ih =>
    intro m τ hτ l hl
    simp only [LExpr.subst, LExpr.locs, List.mem_append] at hl
    rcases hl with hl | hl
    · obtain ⟨y, hy⟩ := hτ.subst_var x
      rw [hy] at hl
      cases y with
      | loc l' => simp [LVal.locs] at hl; subst hl; exact ⟨x, hx, hy⟩
      | bvar i => simp [LVal.locs] at hl
    · obtain ⟨b, hb, hl⟩ := LBranches.mem_locs_subst τ hl
      rw [hes b hb, subst_dups, LExpr.locs_dups, bvals_subst_up, bvals_locs,
        List.nil_append] at hl
      obtain ⟨x', hx', hxe'⟩ := ih b hb (LSubst.up b.k τ) (hτ.up b.k) l hl
      exact binder_loc hτ hx' hxe'
  | dup x hx he ih =>
    intro m τ hτ l hl
    simp only [LExpr.subst, LExpr.locs, List.mem_append] at hl
    rcases hl with hl | hl
    · obtain ⟨y, hy⟩ := hτ.subst_var x
      rw [hy] at hl
      cases y with
      | loc l' => simp [LVal.locs] at hl; subst hl; exact ⟨x, hx, hy⟩
      | bvar i => simp [LVal.locs] at hl
    · obtain ⟨z, hz, hze⟩ := ih τ hτ l hl
      refine ⟨z, ?_, hze⟩
      rcases hz with hz | hz
      · exact .inl hz
      · rcases Multiset.mem_add.mp hz with hz | hz
        · exact .inr hz
        · simp only [Multiset.mem_singleton, Res.var.injEq] at hz; subst hz; exact hx
  | drop x he ih =>
    intro m τ hτ l hl
    simp only [LExpr.subst, LExpr.locs, List.mem_append] at hl
    rcases hl with hl | hl
    · obtain ⟨y, hy⟩ := hτ.subst_var x
      rw [hy] at hl
      cases y with
      | loc l' => simp [LVal.locs] at hl; subst hl; exact ⟨x, .inr (by simp), hy⟩
      | bvar i => simp [LVal.locs] at hl
    · obtain ⟨z, hz, hze⟩ := ih τ hτ l hl
      exact ⟨z, hz.imp_right (fun h => Multiset.mem_add.mpr (.inl h)), hze⟩
  | dropru x k he ih =>
    intro m τ hτ l hl
    simp only [LExpr.subst, LExpr.locs, List.mem_append] at hl
    rcases hl with hl | hl
    · obtain ⟨y, hy⟩ := hτ.subst_var x
      rw [hy] at hl
      cases y with
      | loc l' => simp [LVal.locs] at hl; subst hl; exact ⟨x, .inr (by simp), hy⟩
      | bvar i => simp [LVal.locs] at hl
    · obtain ⟨z, hz, hze⟩ := ih τ hτ l hl
      refine ⟨z, ?_, hze⟩
      rcases hz with hz | hz
      · exact .inl hz
      · rcases Multiset.mem_add.mp hz with hz | hz
        · exact .inr (Multiset.mem_add.mpr (.inl hz))
        · simp at hz
  | free k hk he ih =>
    intro m τ hτ l hl
    simp only [LExpr.subst, LExpr.locs] at hl
    obtain ⟨z, hz, hze⟩ := ih τ hτ l hl
    exact ⟨z, hz.imp_right (fun h => Multiset.mem_add.mpr (.inl h)), hze⟩
  | alloc k hk he ih =>
    intro m τ hτ l hl
    simp only [LExpr.subst, LExpr.locs] at hl
    obtain ⟨z, hz, hze⟩ := ih τ hτ l hl
    refine ⟨z, ?_, hze⟩
    rcases hz with hz | hz
    · exact .inl hz
    · rcases Multiset.mem_add.mp hz with hz | hz
      · exact .inr hz
      · simp at hz
  | empty he ih =>
    intro m τ hτ l hl
    obtain ⟨z, hz, hze⟩ := ih τ hτ l hl
    exact ⟨z, hz.imp_right (fun h => Multiset.mem_add.mpr (.inl h)), hze⟩

/-- The locations of `e[ρ]` are the images by `ρ` of the variables of its environments. -/
theorem LWf.locs_ren {funs : List FName} {m : Nat} {Δ : Finset (Var m)} {Γ : Ctx m}
    {e : LExpr m} (h : LWf funs Δ Γ e) (ρ : Fin m → Nat) {l : Nat}
    (hl : l ∈ (e.subst (LSubst.locs ρ)).locs) :
    ∃ x, (x ∈ Δ ∨ Res.var x ∈ Γ) ∧ x.ren ρ = .loc l := by
  obtain ⟨x, hx, hxe⟩ := h.locs_subst (LSubst.locs ρ) (VarSubst.locs ρ) l hl
  rw [LVal.subst_locs_var] at hxe
  exact ⟨x, hx, LVal.var.inj hxe⟩

/-- The identity substitution. -/
def LSubst.id (n : Nat) : Fin n → LVal n := fun i => .var (.bvar i)

theorem LSubst.up_id (n k : Nat) (i : Fin (n + k)) : LSubst.up k (LSubst.id n) i = LSubst.id (n + k) i := by
  simp only [LSubst.up, LSubst.id]
  split
  · rfl
  · rename_i h
    simp only [LVal.shift, LVal.subst_bvar, LVal.var.injEq, Var.bvar.injEq]
    ext; simp; omega

mutual
theorem LVal.subst_id {n : Nat} : ∀ v : LVal n, v.subst (LSubst.id n) = v
  | .var (.bvar _) => rfl
  | .var (.loc _) => rfl
  | .fn _ => rfl
  | .ctor c vs => by simp only [LVal.subst]; rw [LVals.subst_id vs]
  | .lam zs c k b => by simp only [LVal.subst]; rw [LVals.subst_id zs]
theorem LVals.subst_id {n : Nat} : ∀ vs : LVals n, vs.subst (LSubst.id n) = vs
  | .nil => rfl
  | .cons v vs => by simp only [LVals.subst]; rw [LVal.subst_id v, LVals.subst_id vs]
end

mutual
theorem LExpr.subst_id {n : Nat} : ∀ e : LExpr n, e.subst (LSubst.id n) = e
  | .ret vs => by simp only [LExpr.subst]; rw [LVals.subst_id]
  | .app e1 e2 => by simp only [LExpr.subst]; rw [LExpr.subst_id e1, LExpr.subst_id e2]
  | .call f e1 e2 => by simp only [LExpr.subst]; rw [LExpr.subst_id e1, LExpr.subst_id e2]
  | .letIn k e1 e2 => by
    simp only [LExpr.subst]
    rw [LExpr.subst_id e1, LExpr.subst_congr (LSubst.up_id n k), LExpr.subst_id e2]
  | .match x bs => by simp only [LExpr.subst]; rw [LVal.subst_id, LBranches.subst_id bs]
  | .dup x e => by simp only [LExpr.subst]; rw [LVal.subst_id, LExpr.subst_id e]
  | .drop x e => by simp only [LExpr.subst]; rw [LVal.subst_id, LExpr.subst_id e]
  | .dropru x k e => by simp only [LExpr.subst]; rw [LVal.subst_id, LExpr.subst_id e]
  | .free k e => by simp only [LExpr.subst]; rw [LExpr.subst_id e]
  | .alloc k e => by simp only [LExpr.subst]; rw [LExpr.subst_id e]
theorem LBranches.subst_id {n : Nat} : ∀ bs : LBranches n, bs.subst (LSubst.id n) = bs
  | .nil => rfl
  | .cons c k e bs => by
    simp only [LBranches.subst]
    rw [LExpr.subst_congr (LSubst.up_id n k), LExpr.subst_id e, LBranches.subst_id bs]
end

/-- A well-formed expression whose environments contain no locations has no locations. -/
theorem LWf.locs_nil {funs : List FName} {n : Nat} {Δ : Finset (Var n)} {Γ : Ctx n}
    {e : LExpr n} (h : LWf funs Δ Γ e) (hΔ : ∀ l, Var.loc l ∉ Δ)
    (hΓ : ∀ l, Res.var (Var.loc l) ∉ Γ) : e.locs = [] := by
  rcases hl : e.locs with _ | ⟨l, _⟩
  · rfl
  · exfalso
    have : l ∈ (e.subst (LSubst.id n)).locs := by rw [LExpr.subst_id, hl]; simp
    obtain ⟨x, hx, hxe⟩ := h.locs_subst (LSubst.id n) (fun i => ⟨_, rfl⟩) l this
    cases x with
    | bvar i => simp [LSubst.id] at hxe
    | loc l' =>
      simp only [LVal.subst_loc, LVal.var.injEq, Var.loc.injEq] at hxe
      subst hxe
      rcases hx with hx | hx
      · exact hΔ _ hx
      · exact hΓ _ hx

theorem allCtx_no_loc (k : Nat) (l : Nat) : Res.var (Var.loc l) ∉ allCtx k := by
  simp [allCtx]

/-- The body of a closure has no locations. -/
theorem LWf.locs_nil_clo {funs : List FName} {k : Nat} {e : LExpr k}
    (h : LWf funs ∅ (allCtx k) e) : e.locs = [] :=
  h.locs_nil (fun _ h => by simp at h) (allCtx_no_loc k)

/-- The body of a function has no locations. -/
theorem LWf.locs_nil_fun {funs : List FName} {o b : Nat} {e : LExpr (o + b)}
    (h : LWf funs (bSet o b) (Ctx.shift b (allCtx o)) e) : e.locs = [] := by
  refine h.locs_nil (fun l hl => ?_) (fun l hl => ?_)
  · simp [bSet, Var.newB] at hl
  · obtain ⟨r, hr, hre⟩ := Ctx.mem_shift_iff.mp hl
    simp only [allCtx, Multiset.mem_coe, List.mem_map] at hr
    obtain ⟨i, -, rfl⟩ := hr
    simp [Res.shift, Var.shift] at hre

end FIP.Lam
