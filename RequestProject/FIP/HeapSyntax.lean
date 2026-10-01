module

public import RequestProject.FIP.Heap

@[expose] public section

/-!
# Syntactic facts about `λfip` used in the proof of Theorem 6

* `LVal.Adm`/`LExpr.Adm`: the *admissible* `λfip` expressions, for which the heap semantics
  is sound: they contain no function values (the heap semantics has no rule for `dup f`),
  and every `dropru x` is the reuse-drop of a match branch on `x`, right after the `dup`s of
  its fields, with the size of the matched constructor: `match x {C x̄ ↦ dup x̄; dropru x; e}`
  (this is the shape produced by the translation of `match!`, and it guarantees the side
  condition `k = size(x)` of the `dropru` rule, which our untyped expressions cannot
  express otherwise);
* `LVal.dfv`/`LExpr.dfv`: the free variables of an expression including those of the
  bodies of lambdas;
* facts about substitutions: congruence, composition, and commutation of a renaming of
  names into locations with the substitution of closed values for locations;
* renaming names into locations preserves well-formedness (`LWf.rename`) and
  admissibility (`LExpr.Adm.rename`);
* the free variables of a well-formed expression are available (`LWf.dfv_sub`).
-/

namespace FIP.Lam

/-! ## Admissible expressions -/

mutual
/-- An admissible value: no function values, and the parameters of each lambda are
    distinct. -/
inductive LVal.Adm : LVal → Prop
  | var (x : Var) : LVal.Adm (.var x)
  | ctor (c : CName) (vs : List LVal) : (∀ v ∈ vs, LVal.Adm v) → LVal.Adm (.ctor c vs)
  | lam (zs : List LVal) (xs : List Binder) (e : LExpr) : (∀ v ∈ zs, LVal.Adm v) →
      (xs.map (·.name)).Nodup → LExpr.Adm e → LVal.Adm (.lam zs xs e)
/-- An admissible expression: no function values, and every `dropru` is the reuse-drop of
    a match branch. -/
inductive LExpr.Adm : LExpr → Prop
  | ret (vs : List LVal) : (∀ v ∈ vs, LVal.Adm v) → LExpr.Adm (.ret vs)
  | app (e1 e2 : LExpr) : LExpr.Adm e1 → LExpr.Adm e2 → LExpr.Adm (.app e1 e2)
  | call (f : FName) (e1 e2 : LExpr) : LExpr.Adm e1 → LExpr.Adm e2 →
      LExpr.Adm (.call f e1 e2)
  | letIn (xs : List Binder) (e1 e2 : LExpr) : LExpr.Adm e1 → LExpr.Adm e2 →
      LExpr.Adm (.letIn xs e1 e2)
  | «match» (x : Var) (bs : List LBranch) : (∀ b ∈ bs, LBranch.Adm x b) →
      LExpr.Adm (.match (.var x) bs)
  | dup (x : LVal) (e : LExpr) : LVal.Adm x → LExpr.Adm e → LExpr.Adm (.dup x e)
  | drop (x : LVal) (e : LExpr) : LVal.Adm x → LExpr.Adm e → LExpr.Adm (.drop x e)
  | free (k : Nat) (e : LExpr) : LExpr.Adm e → LExpr.Adm (.free k e)
  | alloc (k : Nat) (e : LExpr) : LExpr.Adm e → LExpr.Adm (.alloc k e)
/-- An admissible branch of a match on `x`: an ordinary branch, or a branch
    `C x̄ ↦ dup x̄; dropru x; e` reusing the matched cell. -/
inductive LBranch.Adm : Var → LBranch → Prop
  | plain (c : CName) (xs : List Binder) (e : LExpr) (x : Var) : LExpr.Adm e →
      LBranch.Adm x (.mk c xs e)
  | reuse (c : CName) (xs : List Binder) (e : LExpr) (x : Var) : LExpr.Adm e →
      x ∉ Binder.vars xs →
      LBranch.Adm x (.mk c xs (dups (Binder.vals xs) (.dropru (.var x) xs.length e)))
end

/-- An admissible signature. -/
def LSig.Adm (sig : LSig) : Prop := ∀ fd ∈ sig, fd.body.Adm

/-! ## Free variables including those of lambda bodies -/

mutual
/-- The free variables of a value, including those of the bodies of lambdas. -/
def LVal.dfv : LVal → List Var
  | .var x => [x]
  | .fn _ => []
  | .ctor _ vs => LVal.dfvList vs
  | .lam zs xs e => LVal.dfvList zs ++ (LExpr.dfv e).filter (· ∉ Binder.vars xs)
/-- `LVal.dfv` of a list of values. -/
def LVal.dfvList : List LVal → List Var
  | [] => []
  | v :: vs => LVal.dfv v ++ LVal.dfvList vs
/-- The free variables of an expression, including those of the bodies of lambdas. -/
def LExpr.dfv : LExpr → List Var
  | .ret vs => LVal.dfvList vs
  | .app e1 e2 => LExpr.dfv e1 ++ LExpr.dfv e2
  | .call _ e1 e2 => LExpr.dfv e1 ++ LExpr.dfv e2
  | .letIn xs e1 e2 => LExpr.dfv e1 ++ (LExpr.dfv e2).filter (· ∉ Binder.vars xs)
  | .match x bs => LVal.dfv x ++ LExpr.dfvB bs
  | .dup x e => LVal.dfv x ++ LExpr.dfv e
  | .drop x e => LVal.dfv x ++ LExpr.dfv e
  | .dropru x _ e => LVal.dfv x ++ LExpr.dfv e
  | .free _ e => LExpr.dfv e
  | .alloc _ e => LExpr.dfv e
/-- `LExpr.dfv` of branches. -/
def LExpr.dfvB : List LBranch → List Var
  | [] => []
  | .mk _ xs e :: bs => (LExpr.dfv e).filter (· ∉ Binder.vars xs) ++ LExpr.dfvB bs
end

theorem LVal.mem_dfvList {vs : List LVal} {y : Var} :
    y ∈ LVal.dfvList vs ↔ ∃ v ∈ vs, y ∈ v.dfv := by
  induction vs with
  | nil => simp [LVal.dfvList]
  | cons v vs ih => simp [LVal.dfvList, ih]

theorem LExpr.mem_dfvB {bs : List LBranch} {y : Var} :
    y ∈ LExpr.dfvB bs ↔ ∃ b ∈ bs, y ∈ b.body.dfv ∧ y ∉ Binder.vars b.binders := by
  induction bs with
  | nil => simp [LExpr.dfvB]
  | cons b bs ih =>
    obtain ⟨c, xs, e⟩ := b
    simp [LExpr.dfvB, ih, LBranch.body, LBranch.binders]

theorem dfv_dups (vs : List LVal) (e : LExpr) :
    ∀ y, y ∈ (dups vs e).dfv ↔ y ∈ LVal.dfvList vs ∨ y ∈ e.dfv := by
  induction vs with
  | nil => simp [dups, LVal.dfvList]
  | cons v vs ih => intro y; simp [dups, LExpr.dfv, LVal.dfvList, ih, or_assoc]

theorem dfvList_vals (xs : List Binder) (y : Var) :
    y ∈ LVal.dfvList (Binder.vals xs) ↔ y ∈ Binder.vars xs := by
  rw [LVal.mem_dfvList]
  simp [Binder.vals, Binder.vars, LVal.dfv]
  constructor
  · rintro ⟨b, hb, rfl⟩; exact ⟨b, hb, rfl⟩
  · rintro ⟨b, hb, rfl⟩; exact ⟨b, hb, rfl⟩

/-! ## Substitutions -/

theorem LSubst.remove_of_mem {σ : LSubst} {xs : List Binder} {y : Var}
    (h : y ∈ Binder.vars xs) : σ.remove xs y = none := by
  simp only [LSubst.remove]; rw [if_pos h]

theorem LSubst.remove_of_not_mem {σ : LSubst} {xs : List Binder} {y : Var}
    (h : y ∉ Binder.vars xs) : σ.remove xs y = σ y := by
  simp only [LSubst.remove]; rw [if_neg h]

theorem LSubst.remove_loc (σ : LSubst) (xs : List Binder) (n : Nat) :
    σ.remove xs (.loc n) = σ (.loc n) :=
  LSubst.remove_of_not_mem (by simp [Binder.vars])

theorem LVal.substList_eq_map (σ : LSubst) (vs : List LVal) :
    LVal.substList σ vs = vs.map (LVal.subst σ) := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp [LVal.substList, ih]

theorem subst_dups (σ : LSubst) (vs : List LVal) (e : LExpr) :
    (dups vs e).subst σ = dups (LVal.substList σ vs) (e.subst σ) := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp [dups, LExpr.subst, LVal.substList, ih]

theorem substList_vals_remove (σ : LSubst) (xs : List Binder) :
    LVal.substList (σ.remove xs) (Binder.vals xs) = Binder.vals xs := by
  rw [LVal.substList_eq_map]
  simp only [Binder.vals, List.map_map]
  apply List.map_congr_left
  intro b hb
  simp only [Function.comp, LVal.subst]
  rw [LSubst.remove_of_mem (by simp [Binder.vars]; exact ⟨b, hb, rfl⟩)]
  rfl

/-! ### Congruence -/

mutual
theorem LVal.subst_congr : ∀ (v : LVal) {σ τ : LSubst}, (∀ y ∈ v.dfv, σ y = τ y) →
    v.subst σ = v.subst τ
  | .var x, σ, τ, h => by simp [LVal.subst, h x (by simp [LVal.dfv])]
  | .fn _, _, _, _ => rfl
  | .ctor c vs, σ, τ, h => by
    simp only [LVal.subst]
    rw [LVal.substList_congr vs (fun y hy => h y (by simpa [LVal.dfv] using hy))]
  | .lam zs xs e, σ, τ, h => by
    simp only [LVal.subst]
    rw [LVal.substList_congr zs (fun y hy => h y (by simp [LVal.dfv, hy])),
      LExpr.subst_congr e (σ := σ.remove xs) (τ := τ.remove xs) (fun y hy => by
        by_cases hx : y ∈ Binder.vars xs
        · rw [LSubst.remove_of_mem hx, LSubst.remove_of_mem hx]
        · rw [LSubst.remove_of_not_mem hx, LSubst.remove_of_not_mem hx]
          exact h y (by simp [LVal.dfv, hy, hx]))]
theorem LVal.substList_congr : ∀ (vs : List LVal) {σ τ : LSubst},
    (∀ y ∈ LVal.dfvList vs, σ y = τ y) → LVal.substList σ vs = LVal.substList τ vs
  | [], _, _, _ => rfl
  | v :: vs, σ, τ, h => by
    simp only [LVal.substList]
    rw [LVal.subst_congr v (fun y hy => h y (by simp [LVal.dfvList, hy])),
      LVal.substList_congr vs (fun y hy => h y (by simp [LVal.dfvList, hy]))]
theorem LExpr.subst_congr : ∀ (e : LExpr) {σ τ : LSubst}, (∀ y ∈ e.dfv, σ y = τ y) →
    e.subst σ = e.subst τ
  | .ret vs, σ, τ, h => by
    simp only [LExpr.subst]; rw [LVal.substList_congr vs (fun y hy => h y hy)]
  | .app e1 e2, σ, τ, h => by
    simp only [LExpr.subst]
    rw [LExpr.subst_congr e1 (fun y hy => h y (by simp [LExpr.dfv, hy])),
      LExpr.subst_congr e2 (fun y hy => h y (by simp [LExpr.dfv, hy]))]
  | .call f e1 e2, σ, τ, h => by
    simp only [LExpr.subst]
    rw [LExpr.subst_congr e1 (fun y hy => h y (by simp [LExpr.dfv, hy])),
      LExpr.subst_congr e2 (fun y hy => h y (by simp [LExpr.dfv, hy]))]
  | .letIn xs e1 e2, σ, τ, h => by
    simp only [LExpr.subst]
    rw [LExpr.subst_congr e1 (fun y hy => h y (by simp [LExpr.dfv, hy])),
      LExpr.subst_congr e2 (σ := σ.remove xs) (τ := τ.remove xs) (fun y hy => by
        by_cases hx : y ∈ Binder.vars xs
        · rw [LSubst.remove_of_mem hx, LSubst.remove_of_mem hx]
        · rw [LSubst.remove_of_not_mem hx, LSubst.remove_of_not_mem hx]
          exact h y (by simp [LExpr.dfv, hy, hx]))]
  | .match x bs, σ, τ, h => by
    simp only [LExpr.subst]
    rw [LVal.subst_congr x (fun y hy => h y (by simp [LExpr.dfv, hy])),
      LExpr.substB_congr bs (fun y hy => h y (by simp [LExpr.dfv, hy]))]
  | .dup x e, σ, τ, h => by
    simp only [LExpr.subst]
    rw [LVal.subst_congr x (fun y hy => h y (by simp [LExpr.dfv, hy])),
      LExpr.subst_congr e (fun y hy => h y (by simp [LExpr.dfv, hy]))]
  | .drop x e, σ, τ, h => by
    simp only [LExpr.subst]
    rw [LVal.subst_congr x (fun y hy => h y (by simp [LExpr.dfv, hy])),
      LExpr.subst_congr e (fun y hy => h y (by simp [LExpr.dfv, hy]))]
  | .dropru x k e, σ, τ, h => by
    simp only [LExpr.subst]
    rw [LVal.subst_congr x (fun y hy => h y (by simp [LExpr.dfv, hy])),
      LExpr.subst_congr e (fun y hy => h y (by simp [LExpr.dfv, hy]))]
  | .free k e, σ, τ, h => by
    simp only [LExpr.subst]; rw [LExpr.subst_congr e (fun y hy => h y hy)]
  | .alloc k e, σ, τ, h => by
    simp only [LExpr.subst]; rw [LExpr.subst_congr e (fun y hy => h y hy)]
theorem LExpr.substB_congr : ∀ (bs : List LBranch) {σ τ : LSubst},
    (∀ y ∈ LExpr.dfvB bs, σ y = τ y) → LExpr.substB σ bs = LExpr.substB τ bs
  | [], _, _, _ => rfl
  | .mk c xs e :: bs, σ, τ, h => by
    simp only [LExpr.substB]
    rw [LExpr.subst_congr e (σ := σ.remove xs) (τ := τ.remove xs) (fun y hy => by
        by_cases hx : y ∈ Binder.vars xs
        · rw [LSubst.remove_of_mem hx, LSubst.remove_of_mem hx]
        · rw [LSubst.remove_of_not_mem hx, LSubst.remove_of_not_mem hx]
          exact h y (by simp [LExpr.dfvB, hy, hx])),
      LExpr.substB_congr bs (fun y hy => h y (by simp [LExpr.dfvB, hy]))]
end

theorem LSubst.remove_none (xs : List Binder) :
    LSubst.remove (fun _ => none) xs = fun _ => none := by
  funext y; by_cases h : y ∈ Binder.vars xs
  · rw [LSubst.remove_of_mem h]
  · rw [LSubst.remove_of_not_mem h]

mutual
theorem LVal.subst_none : ∀ v : LVal, v.subst (fun _ => none) = v
  | .var x => rfl
  | .fn _ => rfl
  | .ctor c vs => by simp only [LVal.subst]; rw [LVal.substList_none vs]
  | .lam zs xs e => by
    simp only [LVal.subst]; rw [LVal.substList_none zs, LSubst.remove_none, LExpr.subst_none e]
theorem LVal.substList_none : ∀ vs : List LVal, LVal.substList (fun _ => none) vs = vs
  | [] => rfl
  | v :: vs => by simp only [LVal.substList]; rw [LVal.subst_none v, LVal.substList_none vs]
theorem LExpr.subst_none : ∀ e : LExpr, e.subst (fun _ => none) = e
  | .ret vs => by simp only [LExpr.subst]; rw [LVal.substList_none vs]
  | .app e1 e2 => by simp only [LExpr.subst]; rw [LExpr.subst_none e1, LExpr.subst_none e2]
  | .call f e1 e2 => by simp only [LExpr.subst]; rw [LExpr.subst_none e1, LExpr.subst_none e2]
  | .letIn xs e1 e2 => by
    simp only [LExpr.subst]; rw [LSubst.remove_none, LExpr.subst_none e1, LExpr.subst_none e2]
  | .match x bs => by simp only [LExpr.subst]; rw [LVal.subst_none x, LExpr.substB_none bs]
  | .dup x e => by simp only [LExpr.subst]; rw [LVal.subst_none x, LExpr.subst_none e]
  | .drop x e => by simp only [LExpr.subst]; rw [LVal.subst_none x, LExpr.subst_none e]
  | .dropru x k e => by simp only [LExpr.subst]; rw [LVal.subst_none x, LExpr.subst_none e]
  | .free k e => by simp only [LExpr.subst]; rw [LExpr.subst_none e]
  | .alloc k e => by simp only [LExpr.subst]; rw [LExpr.subst_none e]
theorem LExpr.substB_none : ∀ bs : List LBranch, LExpr.substB (fun _ => none) bs = bs
  | [] => rfl
  | .mk c xs e :: bs => by
    simp only [LExpr.substB]; rw [LSubst.remove_none, LExpr.subst_none e, LExpr.substB_none bs]
end

/-- A substitution acting only on variables outside the free variables is the identity. -/
theorem LExpr.subst_of_dfv (e : LExpr) {σ : LSubst} (h : ∀ y ∈ e.dfv, σ y = none) :
    e.subst σ = e := by
  rw [LExpr.subst_congr e (τ := fun _ => none) h, LExpr.subst_none]

theorem LVal.subst_of_dfv (v : LVal) {σ : LSubst} (h : ∀ y ∈ v.dfv, σ y = none) :
    v.subst σ = v := by
  rw [LVal.subst_congr v (τ := fun _ => none) h, LVal.subst_none]

/-- A closed value is unchanged by substitutions. -/
theorem LVal.subst_closed {v : LVal} (h : v.dfv = []) (σ : LSubst) : v.subst σ = v :=
  LVal.subst_of_dfv v (by simp [h])

/-! ### Composition -/

/-- `σ` followed by `τ`. -/
def LSubst.comp (σ τ : LSubst) : LSubst := fun y =>
  match σ y with
  | some v => some (v.subst τ)
  | none => τ y

/-- The values substituted by `σ` contain no free names. -/
def LSubst.NoName (σ : LSubst) : Prop :=
  ∀ y v, σ y = some v → ∀ z ∈ v.dfv, ∃ n, z = .loc n

theorem LSubst.NoName.remove {σ : LSubst} (h : σ.NoName) (xs : List Binder) :
    (σ.remove xs).NoName := by
  intro y v hy
  by_cases hx : y ∈ Binder.vars xs
  · rw [LSubst.remove_of_mem hx] at hy; cases hy
  · rw [LSubst.remove_of_not_mem hx] at hy; exact h y v hy

theorem loc_not_mem_vars (xs : List Binder) (n : Nat) : Var.loc n ∉ Binder.vars xs := by
  simp [Binder.vars]

theorem LSubst.remove_comp {σ : LSubst} (h : σ.NoName) (τ : LSubst) (xs : List Binder) :
    (σ.remove xs).comp (τ.remove xs) = (σ.comp τ).remove xs := by
  funext y
  by_cases hx : y ∈ Binder.vars xs
  · simp only [LSubst.comp]; rw [LSubst.remove_of_mem hx, LSubst.remove_of_mem hx,
      LSubst.remove_of_mem hx]
  · rw [LSubst.remove_of_not_mem hx]
    simp only [LSubst.comp]
    rw [LSubst.remove_of_not_mem hx, LSubst.remove_of_not_mem hx]
    cases hσ : σ y with
    | none => rfl
    | some v =>
      show some _ = some _
      congr 1
      apply LVal.subst_congr
      intro z hz
      obtain ⟨n, rfl⟩ := h y v hσ z hz
      exact LSubst.remove_loc τ xs n

mutual
theorem LVal.subst_comp : ∀ (v : LVal) {σ : LSubst} (τ : LSubst), σ.NoName →
    (v.subst σ).subst τ = v.subst (σ.comp τ)
  | .var x, σ, τ, _ => by
    simp only [LVal.subst, LSubst.comp]
    cases σ x <;> rfl
  | .fn _, _, _, _ => rfl
  | .ctor c vs, σ, τ, h => by
    simp only [LVal.subst]; rw [LVal.substList_comp vs τ h]
  | .lam zs xs e, σ, τ, h => by
    simp only [LVal.subst]
    rw [LVal.substList_comp zs τ h, LExpr.subst_comp e (τ.remove xs) (h.remove xs),
      LSubst.remove_comp h]
theorem LVal.substList_comp : ∀ (vs : List LVal) {σ : LSubst} (τ : LSubst), σ.NoName →
    LVal.substList τ (LVal.substList σ vs) = LVal.substList (σ.comp τ) vs
  | [], _, _, _ => rfl
  | v :: vs, σ, τ, h => by
    simp only [LVal.substList]; rw [LVal.subst_comp v τ h, LVal.substList_comp vs τ h]
theorem LExpr.subst_comp : ∀ (e : LExpr) {σ : LSubst} (τ : LSubst), σ.NoName →
    (e.subst σ).subst τ = e.subst (σ.comp τ)
  | .ret vs, σ, τ, h => by simp only [LExpr.subst]; rw [LVal.substList_comp vs τ h]
  | .app e1 e2, σ, τ, h => by
    simp only [LExpr.subst]; rw [LExpr.subst_comp e1 τ h, LExpr.subst_comp e2 τ h]
  | .call f e1 e2, σ, τ, h => by
    simp only [LExpr.subst]; rw [LExpr.subst_comp e1 τ h, LExpr.subst_comp e2 τ h]
  | .letIn xs e1 e2, σ, τ, h => by
    simp only [LExpr.subst]
    rw [LExpr.subst_comp e1 τ h, LExpr.subst_comp e2 (τ.remove xs) (h.remove xs),
      LSubst.remove_comp h]
  | .match x bs, σ, τ, h => by
    simp only [LExpr.subst]; rw [LVal.subst_comp x τ h, LExpr.substB_comp bs τ h]
  | .dup x e, σ, τ, h => by
    simp only [LExpr.subst]; rw [LVal.subst_comp x τ h, LExpr.subst_comp e τ h]
  | .drop x e, σ, τ, h => by
    simp only [LExpr.subst]; rw [LVal.subst_comp x τ h, LExpr.subst_comp e τ h]
  | .dropru x k e, σ, τ, h => by
    simp only [LExpr.subst]; rw [LVal.subst_comp x τ h, LExpr.subst_comp e τ h]
  | .free k e, σ, τ, h => by simp only [LExpr.subst]; rw [LExpr.subst_comp e τ h]
  | .alloc k e, σ, τ, h => by simp only [LExpr.subst]; rw [LExpr.subst_comp e τ h]
theorem LExpr.substB_comp : ∀ (bs : List LBranch) {σ : LSubst} (τ : LSubst), σ.NoName →
    LExpr.substB τ (LExpr.substB σ bs) = LExpr.substB (σ.comp τ) bs
  | [], _, _, _ => rfl
  | .mk c xs e :: bs, σ, τ, h => by
    simp only [LExpr.substB]
    rw [LExpr.subst_comp e (τ.remove xs) (h.remove xs), LSubst.remove_comp h,
      LExpr.substB_comp bs τ h]
end

/-! ### Commuting a renaming with the substitution of closed values -/

/-- Apply `σ` to the values substituted by `τ`. -/
def LSubst.post (τ σ : LSubst) : LSubst := fun y => (τ y).map (LVal.subst σ)

/-- `σ` substitutes closed values for locations only. -/
structure LSubst.ClosedLoc (σ : LSubst) : Prop where
  name : ∀ s, σ (.name s) = none
  closed : ∀ y v, σ y = some v → v.dfv = []

/-- `τ` substitutes values without free names, for names only. -/
structure LSubst.NameOnly (τ : LSubst) : Prop where
  loc : ∀ n, τ (.loc n) = none
  noName : τ.NoName

theorem LSubst.ClosedLoc.noName {σ : LSubst} (h : σ.ClosedLoc) : σ.NoName := by
  intro y v hy z hz; rw [h.closed y v hy] at hz; cases hz

theorem LExpr.subst_commute (e : LExpr) {τ σ : LSubst} (hτ : τ.NameOnly) (hσ : σ.ClosedLoc) :
    (e.subst τ).subst σ = (e.subst σ).subst (τ.post σ) := by
  rw [LExpr.subst_comp e σ hτ.noName, LExpr.subst_comp e _ hσ.noName]
  congr 1
  funext y
  simp only [LSubst.comp, LSubst.post]
  cases y with
  | name s =>
    rw [hσ.name s]
    cases τ (.name s) <;> rfl
  | loc n =>
    rw [hτ.loc n]
    cases hv : σ (.loc n) with
    | none => rfl
    | some v => simp only [Option.some.injEq]; exact (LVal.subst_closed (hσ.closed _ v hv) _).symm

theorem LVal.subst_commute (v : LVal) {τ σ : LSubst} (hτ : τ.NameOnly) (hσ : σ.ClosedLoc) :
    (v.subst τ).subst σ = (v.subst σ).subst (τ.post σ) := by
  rw [LVal.subst_comp v σ hτ.noName, LVal.subst_comp v _ hσ.noName]
  congr 1
  funext y
  simp only [LSubst.comp, LSubst.post]
  cases y with
  | name s =>
    rw [hσ.name s]
    cases τ (.name s) <;> rfl
  | loc n =>
    rw [hτ.loc n]
    cases hv : σ (.loc n) with
    | none => rfl
    | some v => simp only [Option.some.injEq]; exact (LVal.subst_closed (hσ.closed _ v hv) _).symm

/-! ### Substituting for binders -/

theorem lzip_cons (b : Binder) (xs : List Binder) (v : LVal) (vs : List LVal) (y : Var) :
    lzip (b :: xs) (v :: vs) y = if y = .name b.name then some v else lzip xs vs y := by
  simp only [lzip, List.map_cons, List.zip_cons_cons, List.lookup_cons]
  by_cases h : y = .name b.name
  · subst h; simp
  · have : (y == Var.name b.name) = false := by simpa using h
    rw [this, if_neg h]

theorem lzip_loc (xs : List Binder) (vs : List LVal) (n : Nat) : lzip xs vs (.loc n) = none := by
  induction xs generalizing vs with
  | nil => simp [lzip]
  | cons b xs ih =>
    cases vs with
    | nil => simp [lzip]
    | cons v vs => rw [lzip_cons, if_neg (by simp), ih]

theorem lzip_mem {xs : List Binder} {vs : List LVal} {y : Var} {v : LVal}
    (h : lzip xs vs y = some v) : v ∈ vs := by
  induction xs generalizing vs with
  | nil => simp [lzip] at h
  | cons b xs ih =>
    cases vs with
    | nil => simp [lzip] at h
    | cons w vs =>
      rw [lzip_cons] at h
      split_ifs at h with hy
      · cases h; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih h)

theorem lzip_not_mem {xs : List Binder} {vs : List LVal} {y : Var} (h : y ∉ Binder.vars xs) :
    lzip xs vs y = none := by
  induction xs generalizing vs with
  | nil => simp [lzip]
  | cons b xs ih =>
    cases vs with
    | nil => simp [lzip]
    | cons w vs =>
      rw [lzip_cons, if_neg (by intro h'; apply h; simp [Binder.vars, h']), ih]
      intro h'; apply h; simp only [Binder.vars, List.map_cons, List.mem_cons] at h' ⊢
      exact .inr h'

theorem lzip_post (xs : List Binder) (vs : List LVal) (σ : LSubst) :
    (lzip xs vs).post σ = lzip xs (vs.map (LVal.subst σ)) := by
  funext y
  simp only [LSubst.post]
  induction xs generalizing vs with
  | nil => simp [lzip]
  | cons b xs ih =>
    cases vs with
    | nil => simp [lzip]
    | cons w vs =>
      rw [List.map_cons, lzip_cons, lzip_cons]
      split_ifs
      · rfl
      · exact ih vs

/-- Atomic location values. -/
def LVal.IsLoc (v : LVal) : Prop := ∃ n, v = .var (.loc n)

theorem lzip_nameOnly (xs : List Binder) (vs : List LVal) (h : ∀ v ∈ vs, v.IsLoc) :
    (lzip xs vs).NameOnly := by
  refine ⟨lzip_loc xs vs, ?_⟩
  intro y v hy z hz
  obtain ⟨n, rfl⟩ := h v (lzip_mem hy)
  simp [LVal.dfv] at hz; exact ⟨n, hz⟩

/-! ### Free variables of a substituted expression -/

/-- The free variables `y` that a variable `z` contributes after substituting `τ`. -/
def LSubst.Contrib (τ : LSubst) (z y : Var) : Prop :=
  (τ z = none ∧ z = y) ∨ ∃ w, τ z = some w ∧ y ∈ w.dfv

theorem LSubst.contrib_remove {τ : LSubst} {xs : List Binder} {z y : Var}
    (h : (τ.remove xs).Contrib z y) (hy : y ∉ Binder.vars xs) :
    z ∉ Binder.vars xs ∧ τ.Contrib z y := by
  by_cases hz : z ∈ Binder.vars xs
  · rcases h with ⟨_, rfl⟩ | ⟨w, hw, _⟩
    · exact absurd hz hy
    · rw [LSubst.remove_of_mem hz] at hw; cases hw
  · rw [LSubst.Contrib, LSubst.remove_of_not_mem hz] at h
    exact ⟨hz, h⟩

mutual
theorem LVal.dfv_subst : ∀ (v : LVal) (τ : LSubst) (y : Var), y ∈ (v.subst τ).dfv →
    ∃ z ∈ v.dfv, τ.Contrib z y
  | .var x, τ, y, h => by
    simp only [LVal.subst] at h
    cases hx : τ x with
    | none => rw [hx] at h; simp [LVal.dfv] at h; exact ⟨x, by simp [LVal.dfv], .inl ⟨hx, h.symm⟩⟩
    | some w => rw [hx] at h; exact ⟨x, by simp [LVal.dfv], .inr ⟨w, hx, h⟩⟩
  | .fn _, _, y, h => by simp [LVal.subst, LVal.dfv] at h
  | .ctor c vs, τ, y, h => by
    simp only [LVal.subst, LVal.dfv] at h ⊢; exact LVal.dfvList_subst vs τ y h
  | .lam zs xs e, τ, y, h => by
    simp only [LVal.subst, LVal.dfv, List.mem_append, List.mem_filter, decide_eq_true_eq] at h ⊢
    rcases h with h | ⟨h, hy⟩
    · obtain ⟨z, hz, hc⟩ := LVal.dfvList_subst zs τ y h
      exact ⟨z, .inl hz, hc⟩
    · obtain ⟨z, hz, hc⟩ := LExpr.dfv_subst e (τ.remove xs) y h
      obtain ⟨hzx, hc⟩ := LSubst.contrib_remove hc hy
      exact ⟨z, .inr ⟨hz, hzx⟩, hc⟩
theorem LVal.dfvList_subst : ∀ (vs : List LVal) (τ : LSubst) (y : Var),
    y ∈ LVal.dfvList (LVal.substList τ vs) → ∃ z ∈ LVal.dfvList vs, τ.Contrib z y
  | [], _, y, h => by simp [LVal.substList, LVal.dfvList] at h
  | v :: vs, τ, y, h => by
    simp only [LVal.substList, LVal.dfvList, List.mem_append] at h ⊢
    rcases h with h | h
    · obtain ⟨z, hz, hc⟩ := LVal.dfv_subst v τ y h; exact ⟨z, .inl hz, hc⟩
    · obtain ⟨z, hz, hc⟩ := LVal.dfvList_subst vs τ y h; exact ⟨z, .inr hz, hc⟩
theorem LExpr.dfv_subst : ∀ (e : LExpr) (τ : LSubst) (y : Var), y ∈ (e.subst τ).dfv →
    ∃ z ∈ e.dfv, τ.Contrib z y
  | .ret vs, τ, y, h => by simp only [LExpr.subst, LExpr.dfv] at h ⊢; exact LVal.dfvList_subst vs τ y h
  | .app e1 e2, τ, y, h => by
    simp only [LExpr.subst, LExpr.dfv, List.mem_append] at h ⊢
    rcases h with h | h
    · obtain ⟨z, hz, hc⟩ := LExpr.dfv_subst e1 τ y h; exact ⟨z, .inl hz, hc⟩
    · obtain ⟨z, hz, hc⟩ := LExpr.dfv_subst e2 τ y h; exact ⟨z, .inr hz, hc⟩
  | .call f e1 e2, τ, y, h => by
    simp only [LExpr.subst, LExpr.dfv, List.mem_append] at h ⊢
    rcases h with h | h
    · obtain ⟨z, hz, hc⟩ := LExpr.dfv_subst e1 τ y h; exact ⟨z, .inl hz, hc⟩
    · obtain ⟨z, hz, hc⟩ := LExpr.dfv_subst e2 τ y h; exact ⟨z, .inr hz, hc⟩
  | .letIn xs e1 e2, τ, y, h => by
    simp only [LExpr.subst, LExpr.dfv, List.mem_append, List.mem_filter,
      decide_eq_true_eq] at h ⊢
    rcases h with h | ⟨h, hy⟩
    · obtain ⟨z, hz, hc⟩ := LExpr.dfv_subst e1 τ y h; exact ⟨z, .inl hz, hc⟩
    · obtain ⟨z, hz, hc⟩ := LExpr.dfv_subst e2 (τ.remove xs) y h
      obtain ⟨hzx, hc⟩ := LSubst.contrib_remove hc hy
      exact ⟨z, .inr ⟨hz, hzx⟩, hc⟩
  | .match x bs, τ, y, h => by
    simp only [LExpr.subst, LExpr.dfv, List.mem_append] at h ⊢
    rcases h with h | h
    · obtain ⟨z, hz, hc⟩ := LVal.dfv_subst x τ y h; exact ⟨z, .inl hz, hc⟩
    · obtain ⟨z, hz, hc⟩ := LExpr.dfvB_subst bs τ y h; exact ⟨z, .inr hz, hc⟩
  | .dup x e, τ, y, h => by
    simp only [LExpr.subst, LExpr.dfv, List.mem_append] at h ⊢
    rcases h with h | h
    · obtain ⟨z, hz, hc⟩ := LVal.dfv_subst x τ y h; exact ⟨z, .inl hz, hc⟩
    · obtain ⟨z, hz, hc⟩ := LExpr.dfv_subst e τ y h; exact ⟨z, .inr hz, hc⟩
  | .drop x e, τ, y, h => by
    simp only [LExpr.subst, LExpr.dfv, List.mem_append] at h ⊢
    rcases h with h | h
    · obtain ⟨z, hz, hc⟩ := LVal.dfv_subst x τ y h; exact ⟨z, .inl hz, hc⟩
    · obtain ⟨z, hz, hc⟩ := LExpr.dfv_subst e τ y h; exact ⟨z, .inr hz, hc⟩
  | .dropru x k e, τ, y, h => by
    simp only [LExpr.subst, LExpr.dfv, List.mem_append] at h ⊢
    rcases h with h | h
    · obtain ⟨z, hz, hc⟩ := LVal.dfv_subst x τ y h; exact ⟨z, .inl hz, hc⟩
    · obtain ⟨z, hz, hc⟩ := LExpr.dfv_subst e τ y h; exact ⟨z, .inr hz, hc⟩
  | .free k e, τ, y, h => by simp only [LExpr.subst, LExpr.dfv] at h ⊢; exact LExpr.dfv_subst e τ y h
  | .alloc k e, τ, y, h => by simp only [LExpr.subst, LExpr.dfv] at h ⊢; exact LExpr.dfv_subst e τ y h
theorem LExpr.dfvB_subst : ∀ (bs : List LBranch) (τ : LSubst) (y : Var),
    y ∈ LExpr.dfvB (LExpr.substB τ bs) → ∃ z ∈ LExpr.dfvB bs, τ.Contrib z y
  | [], _, y, h => by simp [LExpr.substB, LExpr.dfvB] at h
  | .mk c xs e :: bs, τ, y, h => by
    simp only [LExpr.substB, LExpr.dfvB, List.mem_append, List.mem_filter,
      decide_eq_true_eq] at h ⊢
    rcases h with ⟨h, hy⟩ | h
    · obtain ⟨z, hz, hc⟩ := LExpr.dfv_subst e (τ.remove xs) y h
      obtain ⟨hzx, hc⟩ := LSubst.contrib_remove hc hy
      exact ⟨z, .inl ⟨hz, hzx⟩, hc⟩
    · obtain ⟨z, hz, hc⟩ := LExpr.dfvB_subst bs τ y h; exact ⟨z, .inr hz, hc⟩
end

/-- Substituting closed values for all free variables gives a closed value. -/
theorem LVal.dfv_subst_closed (v : LVal) {τ : LSubst}
    (h : ∀ z ∈ v.dfv, ∃ w, τ z = some w ∧ w.dfv = []) : (v.subst τ).dfv = [] := by
  rcases hd : (v.subst τ).dfv with _ | ⟨y, _⟩
  · rfl
  · obtain ⟨z, hz, hc⟩ := LVal.dfv_subst v τ y (by rw [hd]; simp)
    obtain ⟨w, hw, hw'⟩ := h z hz
    rcases hc with ⟨hn, _⟩ | ⟨w', hw'', hy⟩
    · rw [hw] at hn; cases hn
    · rw [hw] at hw''; cases hw''; rw [hw'] at hy; cases hy

end FIP.Lam
