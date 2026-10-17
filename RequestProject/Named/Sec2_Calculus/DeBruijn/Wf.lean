module

public import RequestProject.Named.Sec2_Calculus.DeBruijn.Closed
public import RequestProject.Named.Sec2_Calculus.Rules

@[expose] public section

/-!
# Well-formed FIPNamed programs are well scoped

If `Δ | Γ ⊢ e` (Fig. 4, 6, 7, with the scalar environment `U`), every free variable of `e`
is in `U, Δ, Γ` (`Wf.fv_inEnv`), so `e` has a de Bruijn representation in any scope
binding those names (`Wf.toTerm_isSome`).  In particular a well-formed expression with
no variable in its environments is a `Term 0` (`Wf.toClosed_isSome`), and the body of every
function checked by `⊩ Σ` is a `Term (|x̄| + |ȳ|)` (`FunDef.Wf.toTFunDef_isSome`).
-/

namespace FIPNamed

/-- The variable `x` is bound by the environments `U, Δ, Γ`. -/
def InEnv (U Δ : Finset Var) (Γ : Ctx) (x : Var) : Prop :=
  x ∈ U ∨ x ∈ Δ ∨ Res.var x ∈ Γ

theorem InEnv.add_left {U Δ : Finset Var} {Γ₁ Γ₂ : Ctx} {x : Var} (h : InEnv U Δ Γ₁ x) :
    InEnv U Δ (Γ₁ + Γ₂) x :=
  h.imp id fun h => h.imp id fun h => Multiset.mem_add.mpr (.inl h)

theorem InEnv.add_right {U Δ : Finset Var} {Γ₁ Γ₂ : Ctx} {x : Var} (h : InEnv U Δ Γ₂ x) :
    InEnv U Δ (Γ₁ + Γ₂) x :=
  h.imp id fun h => h.imp id fun h => Multiset.mem_add.mpr (.inr h)

theorem Val.exists_of_mem_fvList {x : Var} : ∀ {vs : List Val}, x ∈ Val.fvList vs → ∃ v ∈ vs, x ∈ v.fv
  | [], h => by simp [Val.fvList] at h
  | v :: vs, h => by
    simp only [Val.fvList, List.mem_append] at h
    rcases h with h | h
    · exact ⟨v, List.mem_cons_self .., h⟩
    · obtain ⟨w, hw, h⟩ := Val.exists_of_mem_fvList h
      exact ⟨w, List.mem_cons_of_mem _ hw, h⟩

theorem Expr.exists_of_mem_fvBranches {x : Var} : ∀ {bs : List Branch}, x ∈ Expr.fvBranches bs →
    ∃ b ∈ bs, x ∈ b.body.fv ∧ x ∉ Binder.vars b.binders
  | [], h => by simp [Expr.fvBranches] at h
  | .mk c xs e :: bs, h => by
    simp only [Expr.fvBranches, List.mem_append, List.mem_filter, decide_eq_true_eq] at h
    rcases h with ⟨h, hn⟩ | h
    · exact ⟨.mk c xs e, List.mem_cons_self .., h, hn⟩
    · obtain ⟨b, hb, h⟩ := Expr.exists_of_mem_fvBranches h
      exact ⟨b, List.mem_cons_of_mem _ hb, h⟩

mutual
theorem WfVal.fv_inEnv {U Δ : Finset Var} :
    ∀ {Γ : Ctx} {v : Val}, WfVal U Δ Γ v → ∀ x ∈ v.fv, InEnv U Δ Γ x
  | _, _, .var y, x, hx => by
    simp only [Val.fv, List.mem_singleton] at hx; subst hx
    exact .inr (.inr (Multiset.mem_singleton_self _))
  | _, _, .svar y hy, x, hx => by
    simp only [Val.fv, List.mem_singleton] at hx; subst hx; exact .inl hy
  | _, _, .atom _, x, hx => by simp [Val.fv, Val.fvList] at hx
  | _, _, .lit _, x, hx => by simp [Val.fv] at hx
  | _, _, .reuse _ _ _ _ h, x, hx => (WfVals.fv_inEnv h x (by simpa [Val.fv] using hx)).add_left
theorem WfVals.fv_inEnv {U Δ : Finset Var} :
    ∀ {Γ : Ctx} {vs : List Val}, WfVals U Δ Γ vs → ∀ x ∈ Val.fvList vs, InEnv U Δ Γ x
  | _, _, .nil, x, hx => by simp [Val.fvList] at hx
  | _, _, .cons _ _ _ _ h1 h2, x, hx => by
    simp only [Val.fvList, List.mem_append] at hx
    rcases hx with hx | hx
    · exact (WfVal.fv_inEnv h1 x hx).add_left
    · exact (WfVals.fv_inEnv h2 x hx).add_right
end

theorem mem_vars_of_mem_scalars {x : Var} {xs : List Binder} (h : x ∈ Binder.scalars xs) :
    x ∈ Binder.vars xs := by
  simp only [Binder.scalars, List.mem_toFinset, List.mem_map, List.mem_filter] at h
  obtain ⟨b, ⟨hb, _⟩, rfl⟩ := h
  exact List.mem_map_of_mem hb

theorem mem_vars_of_mem_ownedSet {x : Var} {xs : List Binder} (h : x ∈ Binder.ownedSet xs) :
    x ∈ Binder.vars xs := by
  simp only [Binder.ownedSet, List.mem_toFinset, List.mem_map, List.mem_filter] at h
  obtain ⟨b, ⟨hb, _⟩, rfl⟩ := h
  exact List.mem_map_of_mem hb

theorem mem_vars_of_mem_owned {x : Var} {xs : List Binder} (h : Res.var x ∈ Binder.owned xs) :
    x ∈ Binder.vars xs := by
  simp only [Binder.owned, Multiset.mem_coe, List.mem_map, List.mem_filter, Res.var.injEq] at h
  obtain ⟨b, ⟨hb, _⟩, rfl⟩ := h
  exact List.mem_map_of_mem hb

theorem mem_of_mem_vars {x : Var} {Γ : Ctx} (h : x ∈ Γ.vars) : Res.var x ∈ Γ := by
  simp only [Ctx.vars, Multiset.mem_filterMap] at h
  obtain ⟨r, hr, hx⟩ := h
  cases r <;> simp_all

/-- **Well-formed expressions are well scoped**: every free variable of `e` is bound by
    `U, Δ, Γ`. -/
theorem Wf.fv_inEnv {cfg : Cfg} {U Δ : Finset Var} {Γ : Ctx} {e : Expr}
    (h : Wf cfg U Δ Γ e) : ∀ x ∈ e.fv, InEnv U Δ Γ x := by
  induction h with
  | tuple h => exact WfVals.fv_inEnv h
  | call f ys e _ hys _ ih =>
    intro x hx
    simp only [Expr.fv, List.mem_append] at hx
    rcases hx with hx | hx
    · obtain ⟨y, hy, hx⟩ := Val.exists_of_mem_fvList hx
      have := hys y hy
      cases y with
      | var y =>
        simp only [Val.fv, List.mem_singleton] at hx; subst hx
        exact this.elim (fun h => .inr (.inl h)) (fun h => .inl h)
      | fn _ => simp [Val.fv] at hx
      | _ => exact this.elim
    · exact (ih x hx).add_left
  | bapp y e hy _ ih =>
    intro x hx
    simp only [Expr.fv, Val.fvList, Val.fv, List.append_nil, List.mem_append,
      List.mem_singleton] at hx
    rcases hx with rfl | hx
    · exact .inr (.inl hy)
    · exact ih x hx
  | fapp f e _ _ ih =>
    intro x hx
    simp only [Expr.fv, Val.fvList, Val.fv, List.append_nil, List.nil_append] at hx
    exact (ih x hx).add_left
  | letIn Γ₁ Γ₂ Γ₃ xs e₁ e₂ _ _ _ _ ih1 ih2 =>
    intro x hx
    simp only [Expr.fv, List.mem_append, List.mem_filter, decide_eq_true_eq] at hx
    rcases hx with hx | ⟨hx, hn⟩
    · rcases ih1 x hx with h | h | h
      · exact .inl h
      · rcases Finset.mem_union.mp h with h | h
        · exact .inr (.inl h)
        · have h' := mem_of_mem_vars (Multiset.mem_toFinset.mp h)
          exact .inr (.inr (by simp [h']))
      · exact .inr (.inr (by simp [h]))
    · rcases ih2 x hx with h | h | h
      · rcases Finset.mem_union.mp h with h | h
        · exact .inl h
        · exact absurd (mem_vars_of_mem_scalars h) hn
      · exact .inr (.inl h)
      · rcases Multiset.mem_add.mp h with h | h
        · rcases Multiset.mem_add.mp h with h | h
          · exact .inr (.inr (by simp [h]))
          · exact .inr (.inr (by simp [h]))
        · exact absurd (mem_vars_of_mem_owned h) hn
  | bmatch y bs hy _ _ ih =>
    intro x hx
    simp only [Expr.fv, Val.fvList, Val.fv, List.append_nil, List.mem_append,
      List.mem_singleton] at hx
    rcases hx with rfl | hx
    · exact hy.elim (fun h => .inr (.inl h)) (fun h => .inl h)
    · obtain ⟨b, hb, hx, hn⟩ := Expr.exists_of_mem_fvBranches hx
      rcases ih b hb x hx with h | h | h
      · rcases Finset.mem_union.mp h with h | h
        · exact .inl h
        · exact absurd (mem_vars_of_mem_scalars h) hn
      · rcases Finset.mem_union.mp h with h | h
        · exact .inr (.inl h)
        · exact absurd (mem_vars_of_mem_ownedSet h) hn
      · exact .inr (.inr h)
  | dmatch y bs _ _ ih =>
    intro x hx
    simp only [Expr.fv, Val.fvList, Val.fv, List.append_nil, List.mem_append,
      List.mem_singleton] at hx
    rcases hx with rfl | hx
    · exact .inr (.inr (Multiset.mem_add.mpr (.inr (Multiset.mem_singleton_self _))))
    · obtain ⟨b, hb, hx, hn⟩ := Expr.exists_of_mem_fvBranches hx
      rcases ih b hb x hx with h | h | h
      · rcases Finset.mem_union.mp h with h | h
        · exact .inl h
        · exact absurd (mem_vars_of_mem_scalars h) hn
      · exact .inr (.inl h)
      · rcases Multiset.mem_add.mp h with h | h
        · rcases Multiset.mem_add.mp h with h | h
          · exact .inr (.inr (by simp [h]))
          · exact absurd (mem_vars_of_mem_owned h) hn
        · simp at h
  | empty _ ih => exact fun x hx => (ih x hx).add_left
  | drop y _ _ ih =>
    intro x hx
    simp only [Expr.fv, Val.fv, List.mem_append, List.mem_singleton] at hx
    rcases hx with rfl | hx
    · exact .inr (.inr (Multiset.mem_add.mpr (.inr (Multiset.mem_singleton_self _))))
    · exact (ih x hx).add_left
  | free _ _ _ _ ih => exact fun x hx => (ih x (by simpa [Expr.fv] using hx)).add_left
  | inst _ _ _ ih =>
    intro x hx
    rcases ih x hx with h | h | h
    · exact .inl h
    · exact .inr (.inl h)
    · rcases Multiset.mem_add.mp h with h | h
      · exact .inr (.inr (by simp [h]))
      · simp at h
  | weaken _ ih => exact fun x hx => (ih x hx).add_left
  | prim op vs hvs =>
    intro x hx
    simp only [Expr.fv] at hx
    obtain ⟨v, hv, hx⟩ := Val.exists_of_mem_fvList hx
    have := hvs v hv
    cases v with
    | var y =>
      simp only [Val.fv, List.mem_singleton] at hx; subst hx
      exact this.elim (fun h => .inr (.inl h)) (fun h => .inl h)
    | lit _ => simp [Val.fv] at hx
    | _ => exact this.elim

/-- A well-formed expression has a de Bruijn representation in every scope that binds
    the names of its environments. -/
theorem Wf.toTerm_isSome {cfg : Cfg} {U Δ : Finset Var} {Γ : Ctx} {e : Expr}
    (h : Wf cfg U Δ Γ e) {n : Nat} (S : Scope n)
    (hS : ∀ s, InEnv U Δ Γ (.name s) → (S s).isSome) : (e.toTerm S).isSome :=
  (Expr.toTerm_isSome_iff S e).mpr fun s hs => hS s (h.fv_inEnv _ hs)

/-- **A well-formed expression whose environments bind no name is a `Term 0`.** -/
theorem Wf.toClosed_isSome {cfg : Cfg} {U Δ : Finset Var} {Γ : Ctx} {e : Expr}
    (h : Wf cfg U Δ Γ e) (hU : ∀ s, Var.name s ∉ U) (hΔ : ∀ s, Var.name s ∉ Δ)
    (hΓ : ∀ s, Res.var (.name s) ∉ Γ) : e.toClosed.isSome :=
  h.toTerm_isSome Scope.empty fun s hs => by
    rcases hs with hs | hs | hs
    exacts [absurd hs (hU s), absurd hs (hΔ s), absurd hs (hΓ s)]

/-- **The body of a function checked by `deffun` only mentions its parameters**, so the
    function has a well-scoped version with body `Term (|x̄| + |ȳ|)`. -/
theorem FunDef.Wf.toTFunDef_isSome {sig : Sig} {fd : FunDef} (h : fd.Wf sig) :
    fd.toTFunDef.isSome := by
  rw [FunDef.toTFunDef_isSome_iff]
  intro s hs
  rcases h.2.fv_inEnv _ hs with h' | h' | h'
  · rcases Finset.mem_union.mp h' with h' | h'
    · left; simpa [Binder.vars] using mem_vars_of_mem_scalars h'
    · right; simpa [Binder.vars] using mem_vars_of_mem_scalars h'
  · left; simpa [Binder.vars] using mem_vars_of_mem_ownedSet h'
  · right
    rcases Multiset.mem_add.mp h' with h' | h'
    · simpa [Binder.vars] using mem_vars_of_mem_owned h'
    · exact absurd (Multiset.eq_of_mem_replicate h') (by simp)

/-- Every annotated (`fip`/`fbip`) function of a signature with `⊩ Σ` is well scoped. -/
theorem Sig.Wf.toTFunDef_isSome {sig : Sig} (h : sig.Wf) {fd : FunDef} (hfd : fd ∈ sig)
    (ha : fd.annot ≠ .plain) : fd.toTFunDef.isSome :=
  FunDef.Wf.toTFunDef_isSome (h fd hfd ha)

end FIPNamed
