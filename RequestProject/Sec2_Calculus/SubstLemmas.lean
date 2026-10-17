module

public import RequestProject.Sec2_Calculus.Rules

@[expose] public section

/-!
# The algebra of de Bruijn substitutions

Composition and identity laws for `Val.subst`, `Expr.subst` and `Branches.subst`, and how
they interact with weakening (`Val.shift`, `Subst.up`) and instantiation (`Subst.inst`,
`Expr.inst`, `FunDef.instBody`).  These are the standard laws of a well-scoped de Bruijn
representation; every proof that reduces under binders goes through them.
-/

namespace FIP

/-! ## Values -/

/-- A variable as a value, as substituted. -/
@[simp] theorem Val.subst_bvar {n m : Nat} (σ : Fin n → Val m) (i : Fin n) :
    Val.subst σ (.var (.bvar i)) = σ i := rfl

@[simp] theorem Val.subst_loc {n m : Nat} (σ : Fin n → Val m) (l : Nat) :
    Val.subst σ (.var (.loc l)) = .var (.loc l) := rfl

@[simp] theorem Val.subst_fn {n m : Nat} (σ : Fin n → Val m) (f : FName) :
    Val.subst σ (.fn f) = .fn f := rfl

@[simp] theorem Val.subst_lit {n m : Nat} (σ : Fin n → Val m) (k : Int) :
    Val.subst σ (.lit k) = .lit k := rfl

@[simp] theorem Val.subst_ctor {n m : Nat} (σ : Fin n → Val m) (c : CName) (vs : List (Val n)) :
    Val.subst σ (.ctor c vs) = .ctor c (vs.map (Val.subst σ)) := by
  simp [Val.subst]

mutual
/-- Substituting with the identity changes nothing. -/
theorem Val.subst_ids {n : Nat} : ∀ v : Val n, v.subst (Subst.ids n) = v
  | .var (.bvar i) => rfl
  | .var (.loc l) => rfl
  | .fn f => rfl
  | .lit k => rfl
  | .ctor c vs => by
    simp only [Val.subst_ctor, Val.ctor.injEq, true_and]
    exact Val.subst_ids_list vs
/-- The list version of `Val.subst_ids`. -/
theorem Val.subst_ids_list {n : Nat} : ∀ vs : List (Val n), vs.map (Val.subst (Subst.ids n)) = vs
  | [] => rfl
  | v :: vs => by simp only [List.map_cons, Val.subst_ids v, Val.subst_ids_list vs]
end

mutual
/-- Substituting twice is substituting with the composite. -/
theorem Val.subst_subst {n m p : Nat} (τ : Fin n → Val m) (σ : Fin m → Val p) :
    ∀ v : Val n, (v.subst τ).subst σ = v.subst (fun i => (τ i).subst σ)
  | .var (.bvar i) => rfl
  | .var (.loc l) => rfl
  | .fn f => rfl
  | .lit k => rfl
  | .ctor c vs => by
    simp only [Val.subst_ctor, List.map_map, Val.ctor.injEq, true_and]
    exact Val.subst_subst_list τ σ vs
/-- The list version of `Val.subst_subst`. -/
theorem Val.subst_subst_list {n m p : Nat} (τ : Fin n → Val m) (σ : Fin m → Val p) :
    ∀ vs : List (Val n),
      vs.map (Val.subst σ ∘ Val.subst τ) = vs.map (Val.subst fun i => (τ i).subst σ)
  | [] => rfl
  | v :: vs => by
    simp only [List.map_cons, Function.comp_apply, Val.subst_subst τ σ v,
      Val.subst_subst_list τ σ vs]
end

/-- Substitution only depends on the values of the substitution. -/
theorem Val.subst_congr {n m : Nat} {σ σ' : Fin n → Val m} (h : ∀ i, σ i = σ' i)
    (v : Val n) : v.subst σ = v.subst σ' := by
  rw [funext h]

@[simp] theorem Val.shift_var {m : Nat} (k : Nat) (x : Var m) :
    (Val.var x).shift k = .var (x.shift k) := by
  cases x <;> rfl

/-- Weakening a value commutes with a substitution pushed under the new binders. -/
theorem Val.shift_subst_up {n m : Nat} (k : Nat) (σ : Fin n → Val m) (v : Val n) :
    (v.shift k).subst (Subst.up k σ) = (v.subst σ).shift k := by
  unfold Val.shift
  rw [Val.subst_subst, Val.subst_subst]
  refine Val.subst_congr (fun i => ?_) v
  simp only [Val.subst_bvar, Subst.up]
  rw [dif_neg (by simp)]
  congr 2
  ext; simp

/-- Weakening then instantiating the new variables is the original substitution. -/
theorem Val.shift_subst_inst {n m : Nat} (k : Nat) (vs : List (Val m)) (σ : Fin n → Val m)
    (v : Val n) : (v.shift k).subst (Subst.inst k vs σ) = v.subst σ := by
  unfold Val.shift
  rw [Val.subst_subst]
  refine Val.subst_congr (fun i => ?_) v
  simp only [Val.subst_bvar, Subst.inst]
  rw [dif_neg (by simp)]
  congr 1
  ext; simp

/-! ## Pushing substitutions under binders -/

theorem Subst.up_ids (n k : Nat) : Subst.up k (Subst.ids n) = Subst.ids (n + k) := by
  funext i
  simp only [Subst.up, Subst.ids]
  split
  · rfl
  · simp only [Val.shift_var, Var.shift]
    congr 2
    ext; simp; omega

theorem Subst.up_comp {n m p : Nat} (k : Nat) (τ : Fin n → Val m) (σ : Fin m → Val p)
    (i : Fin (n + k)) :
    (Subst.up k τ i).subst (Subst.up k σ) = Subst.up k (fun j => (τ j).subst σ) i := by
  simp only [Subst.up]
  split
  · simp only [Val.subst_bvar, Subst.up]
    rw [dif_pos (by simpa using ‹_›)]
  · rw [Val.shift_subst_up]

theorem Subst.up_inst {n m : Nat} (k : Nat) (ρ : Fin n → Val m) (vs : List (Val m))
    (i : Fin (n + k)) :
    (Subst.up k ρ i).subst (Subst.inst k vs (Subst.ids m)) = Subst.inst k vs ρ i := by
  simp only [Subst.up, Subst.inst]
  split
  · simp only [Val.subst_bvar, Subst.inst]
    rw [dif_pos (by simpa using ‹_›)]
  · rw [Val.shift_subst_inst, Val.subst_ids]

/-! ## Expressions -/

mutual
/-- Substituting with the identity changes nothing. -/
theorem Expr.subst_ids : ∀ {n : Nat} (e : Expr n), e.subst (Subst.ids n) = e
  | _, .ret vs => by simp [Expr.subst, Val.subst_ids_list]
  | _, .app e1 e2 => by simp [Expr.subst, Expr.subst_ids e1, Expr.subst_ids e2]
  | _, .call f e1 e2 => by simp [Expr.subst, Expr.subst_ids e1, Expr.subst_ids e2]
  | n, .letIn xs e1 e2 => by
    simp only [Expr.subst, Subst.up_ids, Expr.subst_ids e1, Expr.subst_ids e2]
  | _, .bmatch e bs => by simp [Expr.subst, Expr.subst_ids e, Branches.subst_ids bs]
  | _, .dmatch e bs => by simp [Expr.subst, Expr.subst_ids e, Branches.subst_ids bs]
  | _, .drop x e => by simp [Expr.subst, Expr.subst_ids e, Val.subst_ids]
  | _, .free k e => by simp [Expr.subst, Expr.subst_ids e]
  | _, .prim op vs => by simp [Expr.subst, Val.subst_ids_list]
/-- Substituting with the identity changes nothing. -/
theorem Branches.subst_ids : ∀ {n : Nat} (bs : Branches n), bs.subst (Subst.ids n) = bs
  | _, .nil => rfl
  | _, .cons c xs e bs => by
    simp only [Branches.subst, Subst.up_ids, Expr.subst_ids e, Branches.subst_ids bs]
end

mutual
/-- Substituting twice is substituting with the composite. -/
theorem Expr.subst_subst : ∀ {n m p : Nat} (τ : Fin n → Val m) (σ : Fin m → Val p) (e : Expr n),
    (e.subst τ).subst σ = e.subst (fun i => (τ i).subst σ)
  | _, _, _, τ, σ, .ret vs => by
    simp [Expr.subst, Val.subst_subst_list]
  | _, _, _, τ, σ, .app e1 e2 => by
    simp [Expr.subst, Expr.subst_subst τ σ e1, Expr.subst_subst τ σ e2]
  | _, _, _, τ, σ, .call f e1 e2 => by
    simp [Expr.subst, Expr.subst_subst τ σ e1, Expr.subst_subst τ σ e2]
  | _, _, _, τ, σ, .letIn xs e1 e2 => by
    simp only [Expr.subst, Expr.subst_subst τ σ e1, Expr.subst_subst _ _ e2,
      Subst.up_comp]
  | _, _, _, τ, σ, .bmatch e bs => by
    simp [Expr.subst, Expr.subst_subst τ σ e, Branches.subst_subst τ σ bs]
  | _, _, _, τ, σ, .dmatch e bs => by
    simp [Expr.subst, Expr.subst_subst τ σ e, Branches.subst_subst τ σ bs]
  | _, _, _, τ, σ, .drop x e => by
    simp [Expr.subst, Expr.subst_subst τ σ e, Val.subst_subst]
  | _, _, _, τ, σ, .free k e => by
    simp [Expr.subst, Expr.subst_subst τ σ e]
  | _, _, _, τ, σ, .prim op vs => by
    simp [Expr.subst, Val.subst_subst_list]
/-- Substituting twice is substituting with the composite. -/
theorem Branches.subst_subst : ∀ {n m p : Nat} (τ : Fin n → Val m) (σ : Fin m → Val p)
    (bs : Branches n), (bs.subst τ).subst σ = bs.subst (fun i => (τ i).subst σ)
  | _, _, _, τ, σ, .nil => rfl
  | _, _, _, τ, σ, .cons c xs e bs => by
    simp only [Branches.subst, Expr.subst_subst _ _ e, Subst.up_comp,
      Branches.subst_subst τ σ bs]
end

theorem Expr.subst_congr {n m : Nat} {σ σ' : Fin n → Val m} (h : ∀ i, σ i = σ' i)
    (e : Expr n) : e.subst σ = e.subst σ' := by
  rw [funext h]

/-- Substituting under the binders of a body, then instantiating the binders, is
    instantiating with the substitution for the outer variables. -/
theorem Expr.subst_up_inst {n m k : Nat} (ρ : Fin n → Val m) (e : Expr (n + k))
    (vs : List (Val m)) : (e.subst (Subst.up k ρ)).inst vs = e.subst (Subst.inst k vs ρ) := by
  unfold Expr.inst
  rw [Expr.subst_subst]
  exact Expr.subst_congr (Subst.up_inst k ρ vs) e

/-- The value substituted for the `j`-th new variable by `Subst.inst`. -/
theorem Subst.inst_lt {n m : Nat} (k : Nat) (vs : List (Val m)) (σ : Fin n → Val m)
    (i : Fin (n + k)) (h : i.val < k) : Subst.inst k vs σ i = vs.getD i.val default := by
  simp [Subst.inst, h]

/-- The value substituted for an outer variable by `Subst.inst`. -/
theorem Subst.inst_ge {n m : Nat} (k : Nat) (vs : List (Val m)) (σ : Fin n → Val m)
    (i : Fin (n + k)) (h : k ≤ i.val) :
    Subst.inst k vs σ i = σ ⟨i.val - k, by omega⟩ := by
  simp [Subst.inst, show ¬ i.val < k by omega]

/-! ## Substitution of closed values -/

/-- A closed value seen in any scope. -/
def Val.weaken {n : Nat} (v : Val 0) : Val n := v.subst Fin.elim0

/-- A closed value is unchanged by any substitution. -/
theorem Val.weaken_subst {n m : Nat} (σ : Fin n → Val m) (v : Val 0) :
    (v.weaken : Val n).subst σ = v.weaken := by
  unfold Val.weaken
  rw [Val.subst_subst]
  exact Val.subst_congr (fun i => i.elim0) v

@[simp] theorem Val.weaken_zero (v : Val 0) : (v.weaken : Val 0) = v := by
  unfold Val.weaken
  exact (Val.subst_congr (σ' := Subst.ids 0) (fun i => i.elim0) v).trans (Val.subst_ids v)

/-! ## Binders and weakening of environments -/

@[simp] theorem Var.unshift_shift {n : Nat} (k : Nat) (x : Var n) : Var.unshift k (x.shift k) = some x := by
  cases x with
  | bvar i => simp [Var.shift, Var.unshift]
  | loc l => rfl

theorem Var.unshift_eq_some {n : Nat} {k : Nat} {y : Var (n + k)} {x : Var n} :
    Var.unshift k y = some x ↔ y = x.shift k := by
  constructor
  · intro h
    cases y with
    | bvar i =>
      simp only [Var.unshift] at h
      split at h
      · cases h; simp only [Var.shift, Var.bvar.injEq]; ext; simp; omega
      · simp at h
    | loc l => cases h; rfl
  · rintro rfl; exact Var.unshift_shift k x

theorem Var.shift_inj {n : Nat} {k : Nat} {x y : Var n} : x.shift k = y.shift k ↔ x = y :=
  (Var.shift_injective k).eq_iff

@[simp] theorem Vars.mem_shift {n : Nat} {k : Nat} {U : Finset (Var n)} {x : Var n} :
    x.shift k ∈ Vars.shift k U ↔ x ∈ U := by
  simp [Vars.shift, Var.shiftEmb]

theorem Vars.mem_shift_iff {n : Nat} {k : Nat} {U : Finset (Var n)} {y : Var (n + k)} :
    y ∈ Vars.shift k U ↔ ∃ x ∈ U, x.shift k = y := by
  simp [Vars.shift, Var.shiftEmb]

theorem Binder.mem_select {N : Nat} {xs : List Bool} {sc : Bool} {f : Fin xs.length → Var N}
    {y : Var N} : y ∈ Binder.select xs sc f ↔ ∃ j : Fin xs.length, xs[j] = sc ∧ f j = y := by
  simp [Binder.select]

theorem Var.shift_ne_newB {n k : Nat} (x : Var n) (j : Fin k) : x.shift k ≠ Var.newB j := by
  cases x with
  | bvar i => simp only [Var.shift, Var.newB, ne_eq, Var.bvar.injEq, Fin.ext_iff]; omega
  | loc l => simp [Var.shift, Var.newB]

theorem Binder.shift_not_mem_select {n : Nat} (xs : List Bool) (sc : Bool) (x : Var n) :
    x.shift xs.length ∉ Binder.select xs sc Var.newB := by
  rw [Binder.mem_select]
  rintro ⟨j, -, h⟩
  exact Var.shift_ne_newB x j h.symm

theorem Binder.shift_not_mem_scalars {n : Nat} (xs : List Bool) (x : Var n) :
    x.shift xs.length ∉ (Binder.scalars xs : Finset (Var (n + xs.length))) := by
  simp only [Binder.scalars, Binder.scalarsAt, List.mem_toFinset]
  exact Binder.shift_not_mem_select xs true x

theorem Binder.shift_not_mem_ownedSet {n : Nat} (xs : List Bool) (x : Var n) :
    x.shift xs.length ∉ (Binder.ownedSet xs : Finset (Var (n + xs.length))) := by
  simp only [Binder.ownedSet, Binder.ownedSetAt, List.mem_toFinset]
  exact Binder.shift_not_mem_select xs false x

theorem Binder.mem_ownedAt_var {N : Nat} {xs : List Bool} {f : Fin xs.length → Var N} {y : Var N} :
    Res.var y ∈ Binder.ownedAt xs f ↔ y ∈ Binder.select xs false f := by
  simp [Binder.ownedAt]

theorem Binder.shift_not_mem_owned {n : Nat} (xs : List Bool) (x : Var n) :
    Res.var (x.shift xs.length) ∉ (Binder.owned xs : Ctx (n + xs.length)) := by
  simp only [Binder.owned, Binder.mem_ownedAt_var]
  exact Binder.shift_not_mem_select xs false x

@[simp] theorem Binder.credit_not_mem_ownedAt {N : Nat} {xs : List Bool} {f : Fin xs.length → Var N}
    {k : Nat} : Res.credit k ∉ Binder.ownedAt xs f := by
  simp [Binder.ownedAt]

@[simp] theorem Binder.alloc_not_mem_ownedAt {N : Nat} {xs : List Bool} {f : Fin xs.length → Var N} :
    Res.alloc ∉ Binder.ownedAt xs f := by
  simp [Binder.ownedAt]

theorem Res.shift_injective {n : Nat} (k : Nat) : Function.Injective (Res.shift (n := n) k) := by
  intro a b h
  cases a <;> cases b <;> simp_all [Res.shift, Var.shift_inj]

theorem Ctx.mem_shift {n : Nat} {k : Nat} {Γ : Ctx n} {r : Res n} :
    r.shift k ∈ Γ.shift k ↔ r ∈ Γ := by
  simp only [Ctx.shift, Multiset.mem_map]
  constructor
  · rintro ⟨r', hr', h⟩; rwa [← Res.shift_injective k h]
  · intro h; exact ⟨r, h, rfl⟩

theorem Ctx.mem_shift_iff {n : Nat} {k : Nat} {Γ : Ctx n} {r : Res (n + k)} :
    r ∈ Γ.shift k ↔ ∃ r' ∈ Γ, r'.shift k = r := by
  simp [Ctx.shift]

theorem Ctx.mem_shift_var {n : Nat} {k : Nat} {Γ : Ctx n} {x : Var n} :
    Res.var (x.shift k) ∈ Γ.shift k ↔ Res.var x ∈ Γ :=
  Ctx.mem_shift (r := Res.var x)

/-! ## Free variables of substituted terms -/

mutual
/-- The free variables of a weakened value. -/
theorem Val.fv_shift {n : Nat} (k : Nat) : ∀ v : Val n, (v.shift k).fv = v.fv.map (Var.shift k)
  | .var (.bvar i) => rfl
  | .var (.loc l) => rfl
  | .fn f => rfl
  | .lit z => rfl
  | .ctor c vs => by
    have := Val.fvList_shift k vs
    simp only [Val.shift, Val.subst_ctor] at this ⊢
    simpa [Val.fv] using this
/-- The free variables of a weakened list of values. -/
theorem Val.fvList_shift {n : Nat} (k : Nat) : ∀ vs : List (Val n),
    Val.fvList (vs.map (Val.subst fun i => .var (.bvar ⟨k + i, by omega⟩))) =
      (Val.fvList vs).map (Var.shift k)
  | [] => rfl
  | v :: vs => by
    have h1 := Val.fv_shift k v
    have h2 := Val.fvList_shift k vs
    simp only [Val.shift] at h1
    simp [Val.fvList, h1, h2]
end

theorem Val.mem_fvList' {n : Nat} {x : Var n} {vs : List (Val n)} :
    x ∈ Val.fvList vs ↔ ∃ v ∈ vs, x ∈ Val.fv v := by
  induction vs with
  | nil => simp [Val.fvList]
  | cons v vs ih => simp [Val.fvList, ih]

mutual
/-- A free variable of `v[ρ]` comes from the value substituted for a free variable of
    `v`. -/
theorem Val.fv_subst {n m : Nat} (ρ : Fin n → Val m) (y : Var m) :
    ∀ v : Val n, y ∈ Val.fv (v.subst ρ) → ∃ x ∈ Val.fv v, y ∈ Val.fv (Val.subst ρ (.var x))
  | .var x, h => ⟨x, by simp [Val.fv], h⟩
  | .fn _, h => by simp [Val.subst, Val.fv] at h
  | .lit _, h => by simp [Val.subst, Val.fv] at h
  | .ctor c vs, h => by
    simp only [Val.subst, Val.fv] at h ⊢
    exact Val.fvList_subst ρ y vs h
/-- The list version of `Val.fv_subst`. -/
theorem Val.fvList_subst {n m : Nat} (ρ : Fin n → Val m) (y : Var m) :
    ∀ vs : List (Val n), y ∈ Val.fvList (Val.substList ρ vs) →
      ∃ x ∈ Val.fvList vs, y ∈ Val.fv (Val.subst ρ (.var x))
  | [], h => by simp [Val.substList, Val.fvList] at h
  | v :: vs, h => by
    simp only [Val.substList, Val.fvList, List.mem_append] at h
    rcases h with h | h
    · obtain ⟨x, hx, h'⟩ := Val.fv_subst ρ y v h
      exact ⟨x, by simp [Val.fvList, hx], h'⟩
    · obtain ⟨x, hx, h'⟩ := Val.fvList_subst ρ y vs h
      exact ⟨x, by simp [Val.fvList, hx], h'⟩
end

/-- A free variable of a body substituted under `k` binders that is not one of the new
    variables. -/
theorem fv_subst_up {n m k : Nat} {ρ : Fin n → Val m} {y : Var m} {x' : Var (n + k)}
    (h : y.shift k ∈ Val.fv (Val.subst (Subst.up k ρ) (.var x'))) :
    ∃ x, Var.unshift k x' = some x ∧ y ∈ Val.fv (Val.subst ρ (.var x)) := by
  cases x' with
  | loc l =>
    simp only [Val.subst_loc, Val.fv, List.mem_singleton] at h
    cases y with
    | bvar i => simp [Var.shift] at h
    | loc l' =>
      simp only [Var.shift, Var.loc.injEq] at h
      subst h
      exact ⟨.loc l', rfl, by simp [Val.fv]⟩
  | bvar i =>
    simp only [Val.subst_bvar, Subst.up] at h
    split at h
    · simp only [Val.fv, List.mem_singleton] at h
      cases y with
      | bvar j => simp only [Var.shift, Var.bvar.injEq, Fin.ext_iff] at h; omega
      | loc l => simp [Var.shift] at h
    · rename_i hik
      rw [Val.fv_shift, List.mem_map] at h
      obtain ⟨y', hy', hyy⟩ := h
      rw [Var.shift_inj] at hyy
      subst hyy
      refine ⟨.bvar ⟨i.val - k, by omega⟩, ?_, hy'⟩
      simp [Var.unshift, show k ≤ i.val by omega]

mutual
/-- A free variable of `e[ρ]` comes from the value substituted for a free variable of
    `e`. -/
theorem Expr.fv_subst : ∀ {n m : Nat} (ρ : Fin n → Val m) (y : Var m) (e : Expr n),
    y ∈ (e.subst ρ).fv → ∃ x ∈ e.fv, y ∈ Val.fv (Val.subst ρ (.var x))
  | _, _, ρ, y, .ret vs, h => by
    simp only [Expr.subst, Expr.fv] at h ⊢; exact Val.fvList_subst ρ y vs h
  | _, _, ρ, y, .app e1 e2, h => by
    simp only [Expr.subst, Expr.fv, List.mem_append] at h ⊢
    rcases h with h | h
    · obtain ⟨x, hx, h'⟩ := Expr.fv_subst ρ y e1 h; exact ⟨x, .inl hx, h'⟩
    · obtain ⟨x, hx, h'⟩ := Expr.fv_subst ρ y e2 h; exact ⟨x, .inr hx, h'⟩
  | _, _, ρ, y, .call f e1 e2, h => by
    simp only [Expr.subst, Expr.fv, List.mem_append] at h ⊢
    rcases h with h | h
    · obtain ⟨x, hx, h'⟩ := Expr.fv_subst ρ y e1 h; exact ⟨x, .inl hx, h'⟩
    · obtain ⟨x, hx, h'⟩ := Expr.fv_subst ρ y e2 h; exact ⟨x, .inr hx, h'⟩
  | _, _, ρ, y, .letIn xs e1 e2, h => by
    simp only [Expr.subst, Expr.fv, List.mem_append, List.mem_filterMap,
      Var.unshift_eq_some] at h ⊢
    rcases h with h | ⟨y', h, rfl⟩
    · obtain ⟨x, hx, h'⟩ := Expr.fv_subst ρ y e1 h; exact ⟨x, .inl hx, h'⟩
    · obtain ⟨x', hx', h'⟩ := Expr.fv_subst _ _ e2 h
      obtain ⟨x, hxx, h''⟩ := fv_subst_up h'
      exact ⟨x, .inr ⟨x', hx', by rw [Var.unshift_eq_some.mp hxx]⟩, h''⟩
  | _, _, ρ, y, .bmatch e bs, h => by
    simp only [Expr.subst, Expr.fv, List.mem_append] at h ⊢
    rcases h with h | h
    · obtain ⟨x, hx, h'⟩ := Expr.fv_subst ρ y e h; exact ⟨x, .inl hx, h'⟩
    · obtain ⟨x, hx, h'⟩ := Branches.fv_subst ρ y bs h; exact ⟨x, .inr hx, h'⟩
  | _, _, ρ, y, .dmatch e bs, h => by
    simp only [Expr.subst, Expr.fv, List.mem_append] at h ⊢
    rcases h with h | h
    · obtain ⟨x, hx, h'⟩ := Expr.fv_subst ρ y e h; exact ⟨x, .inl hx, h'⟩
    · obtain ⟨x, hx, h'⟩ := Branches.fv_subst ρ y bs h; exact ⟨x, .inr hx, h'⟩
  | _, _, ρ, y, .drop v e, h => by
    simp only [Expr.subst, Expr.fv, List.mem_append] at h ⊢
    rcases h with h | h
    · obtain ⟨x, hx, h'⟩ := Val.fv_subst ρ y v h; exact ⟨x, .inl hx, h'⟩
    · obtain ⟨x, hx, h'⟩ := Expr.fv_subst ρ y e h; exact ⟨x, .inr hx, h'⟩
  | _, _, ρ, y, .free k e, h => by
    simp only [Expr.subst, Expr.fv] at h ⊢; exact Expr.fv_subst ρ y e h
  | _, _, ρ, y, .prim op vs, h => by
    simp only [Expr.subst, Expr.fv] at h ⊢; exact Val.fvList_subst ρ y vs h
/-- The branches version of `Expr.fv_subst`. -/
theorem Branches.fv_subst : ∀ {n m : Nat} (ρ : Fin n → Val m) (y : Var m) (bs : Branches n),
    y ∈ Branches.fv (bs.subst ρ) → ∃ x ∈ Branches.fv bs, y ∈ Val.fv (Val.subst ρ (.var x))
  | _, _, ρ, y, .nil, h => by simp [Branches.subst, Branches.fv] at h
  | _, _, ρ, y, .cons c xs e bs, h => by
    simp only [Branches.subst, Branches.fv, List.mem_append, List.mem_filterMap,
      Var.unshift_eq_some] at h ⊢
    rcases h with ⟨y', h, rfl⟩ | h
    · obtain ⟨x', hx', h'⟩ := Expr.fv_subst _ _ e h
      obtain ⟨x, hxx, h''⟩ := fv_subst_up h'
      exact ⟨x, .inl ⟨x', hx', by rw [Var.unshift_eq_some.mp hxx]⟩, h''⟩
    · obtain ⟨x, hx, h'⟩ := Branches.fv_subst ρ y bs h; exact ⟨x, .inr hx, h'⟩
end

/-! ## Matching commutes with substitution -/

/-- Substitute in a branch (under its binders). -/
def Branch.subst {n m : Nat} (ρ : Fin n → Val m) (b : Branch n) : Branch m :=
  ⟨b.ctor, b.binders, b.body.subst (Subst.up b.binders.length ρ)⟩

theorem Branches.toList_subst {n m : Nat} (ρ : Fin n → Val m) :
    ∀ bs : Branches n, (bs.subst ρ).toList = bs.toList.map (Branch.subst ρ)
  | .nil => rfl
  | .cons c xs e bs => by
    simp only [Branches.subst, Branches.toList_cons, List.map_cons, Branches.toList_subst ρ bs]
    rfl

theorem Branches.find_mem {n : Nat} {bs : Branches n} {c : CName} {k : Nat} {b : Branch n}
    (h : bs.find c k = some b) : b ∈ bs.toList ∧ b.ctor = c ∧ b.binders.length = k := by
  unfold Branches.find at h
  have h1 := List.mem_of_find?_eq_some h
  have h2 := List.find?_some h
  simp only [Bool.and_eq_true, beq_iff_eq] at h2
  exact ⟨h1, h2.1, h2.2⟩

theorem Branches.find_subst {n m : Nat} (ρ : Fin n → Val m) (bs : Branches n) (c : CName)
    (k : Nat) : (bs.subst ρ).find c k = (bs.find c k).map (Branch.subst ρ) := by
  unfold Branches.find
  rw [Branches.toList_subst, List.find?_map]
  rfl

end FIP
