module

public import RequestProject.AppB_StoreSoundness.StoreSound

@[expose] public section

/-!
# Facts about substituting locations

How the substitution `Expr.substLoc σ` of closed values for locations interacts with the
substitution `Expr.subst ρ` of values for de Bruijn indices: they commute
(`Expr.substLoc_subst`), and `substLoc σ` only depends on `σ` at the free locations
(`Expr.substLoc_congr`).  Since the values substituted for locations are closed
(`Val 0`), no side condition is needed.
-/

namespace FIP

/-- Every value of `σ` is closed: it mentions no location (nor, being a `Val 0`, any bound
    variable). -/
def LocClosed (σ : Nat → Option (Val 0)) : Prop := ∀ n w, σ n = some w → Val.fv w = []

/-! ## Locations versus bound variables -/

/-- Substituting a location in scope `0`. -/
@[simp] theorem Val.substLoc_loc0 (σ : Nat → Option (Val 0)) (l : Nat) :
    Val.substLoc σ (.var (.loc l) : Val 0) = (σ l).getD (.var (.loc l)) := by
  simp only [Val.substLoc]
  cases σ l <;> simp

@[simp] theorem Val.substLoc_bvar {n : Nat} (σ : Nat → Option (Val 0)) (i : Fin n) :
    Val.substLoc σ (.var (.bvar i)) = .var (.bvar i) := rfl

@[simp] theorem Val.substLoc_ctor {n : Nat} (σ : Nat → Option (Val 0)) (c : CName)
    (vs : List (Val n)) : Val.substLoc σ (.ctor c vs) = .ctor c (vs.map (Val.substLoc σ)) := by
  simp [Val.substLoc]

mutual
theorem Val.substLoc_subst {n m : Nat} (σ : Nat → Option (Val 0)) (τ : Fin n → Val m) :
    ∀ v : Val n, (v.subst τ).substLoc σ = (v.substLoc σ).subst (fun i => (τ i).substLoc σ)
  | .var (.bvar i) => rfl
  | .var (.loc l) => by
    simp only [Val.subst_loc, Val.substLoc]
    cases σ l with
    | none => rfl
    | some w => simp [Val.weaken_subst]
  | .fn _ => rfl
  | .lit _ => rfl
  | .ctor c vs => by
    simp only [Val.subst_ctor, Val.substLoc_ctor, List.map_map]
    rw [Val.substLocList_subst σ τ vs]
theorem Val.substLocList_subst {n m : Nat} (σ : Nat → Option (Val 0)) (τ : Fin n → Val m) :
    ∀ vs : List (Val n), vs.map (Val.substLoc σ ∘ Val.subst τ) =
      vs.map (Val.subst (fun i => (τ i).substLoc σ) ∘ Val.substLoc σ)
  | [] => rfl
  | v :: vs => by
    simp only [List.map_cons, Function.comp_apply]
    rw [Val.substLoc_subst σ τ v, Val.substLocList_subst σ τ vs]
end

/-- `substLoc` commutes with seeing a closed value in a larger scope. -/
theorem Val.substLoc_weaken {n : Nat} (σ : Nat → Option (Val 0)) (v : Val 0) :
    (v.weaken : Val n).substLoc σ = (v.substLoc σ).weaken := by
  unfold Val.weaken
  rw [Val.substLoc_subst]
  exact Val.subst_congr (fun i => i.elim0) _

/-- `substLoc` commutes with weakening. -/
theorem Val.substLoc_shift {n : Nat} (σ : Nat → Option (Val 0)) (k : Nat) (v : Val n) :
    (v.shift k).substLoc σ = (v.substLoc σ).shift k := by
  unfold Val.shift
  rw [Val.substLoc_subst]
  rfl

theorem Subst.up_substLoc {n m : Nat} (σ : Nat → Option (Val 0)) (k : Nat) (τ : Fin n → Val m)
    (i : Fin (n + k)) :
    (Subst.up k τ i).substLoc σ = Subst.up k (fun j => (τ j).substLoc σ) i := by
  simp only [Subst.up]
  split
  · rfl
  · rw [Val.substLoc_shift]

mutual
theorem Expr.substLoc_subst : ∀ {n m : Nat} (σ : Nat → Option (Val 0)) (τ : Fin n → Val m)
    (e : Expr n), (e.subst τ).substLoc σ = (e.substLoc σ).subst (fun i => (τ i).substLoc σ)
  | _, _, σ, τ, .ret vs => by
    simp only [Expr.subst, Expr.substLoc, Val.substList_eq_map, Val.substLocList_eq_map,
      List.map_map]
    rw [Val.substLocList_subst]
  | _, _, σ, τ, .app e1 e2 => by
    simp only [Expr.subst, Expr.substLoc]
    rw [Expr.substLoc_subst σ τ e1, Expr.substLoc_subst σ τ e2]
  | _, _, σ, τ, .call f e1 e2 => by
    simp only [Expr.subst, Expr.substLoc]
    rw [Expr.substLoc_subst σ τ e1, Expr.substLoc_subst σ τ e2]
  | _, _, σ, τ, .letIn xs e1 e2 => by
    simp only [Expr.subst, Expr.substLoc]
    rw [Expr.substLoc_subst σ τ e1, Expr.substLoc_subst σ _ e2]
    congr 1
    exact Expr.subst_congr (Subst.up_substLoc σ _ τ) _
  | _, _, σ, τ, .bmatch e bs => by
    simp only [Expr.subst, Expr.substLoc]
    rw [Expr.substLoc_subst σ τ e, Branches.substLoc_subst σ τ bs]
  | _, _, σ, τ, .dmatch e bs => by
    simp only [Expr.subst, Expr.substLoc]
    rw [Expr.substLoc_subst σ τ e, Branches.substLoc_subst σ τ bs]
  | _, _, σ, τ, .drop x e => by
    simp only [Expr.subst, Expr.substLoc]
    rw [Val.substLoc_subst σ τ x, Expr.substLoc_subst σ τ e]
  | _, _, σ, τ, .free k e => by
    simp only [Expr.subst, Expr.substLoc]; rw [Expr.substLoc_subst σ τ e]
  | _, _, σ, τ, .prim op vs => by
    simp only [Expr.subst, Expr.substLoc, Val.substList_eq_map, Val.substLocList_eq_map,
      List.map_map]
    rw [Val.substLocList_subst]
theorem Branches.substLoc_subst : ∀ {n m : Nat} (σ : Nat → Option (Val 0)) (τ : Fin n → Val m)
    (bs : Branches n),
    (bs.subst τ).substLoc σ = (bs.substLoc σ).subst (fun i => (τ i).substLoc σ)
  | _, _, σ, τ, .nil => rfl
  | _, _, σ, τ, .cons c xs e bs => by
    simp only [Branches.subst, Branches.substLoc]
    rw [Expr.substLoc_subst σ _ e, Branches.substLoc_subst σ τ bs]
    congr 1
    exact Expr.subst_congr (Subst.up_substLoc σ _ τ) _
end

/-! ## Congruence of location substitution -/

mutual
theorem Val.substLoc_congr {n : Nat} {σ σ' : Nat → Option (Val 0)} :
    ∀ v : Val n, (∀ l, Var.loc l ∈ Val.fv v → σ l = σ' l) → v.substLoc σ = v.substLoc σ'
  | .var (.loc l), h => by simp only [Val.substLoc]; rw [h l (by simp [Val.fv])]
  | .var (.bvar _), _ => rfl
  | .fn _, _ => rfl
  | .lit _, _ => rfl
  | .ctor c vs, h => by
    simp only [Val.substLoc, Val.fv] at h ⊢; rw [Val.substLocList_congr vs h]
theorem Val.substLocList_congr {n : Nat} {σ σ' : Nat → Option (Val 0)} :
    ∀ vs : List (Val n), (∀ l, Var.loc l ∈ Val.fvList vs → σ l = σ' l) →
      Val.substLocList σ vs = Val.substLocList σ' vs
  | [], _ => rfl
  | v :: vs, h => by
    simp only [Val.substLocList]
    rw [Val.substLoc_congr v (fun l hl => h l (by simp [Val.fvList, hl])),
      Val.substLocList_congr vs (fun l hl => h l (by simp [Val.fvList, hl]))]
end

mutual
theorem Expr.substLoc_congr {n : Nat} {σ σ' : Nat → Option (Val 0)} :
    ∀ e : Expr n, (∀ l, Var.loc l ∈ e.fv → σ l = σ' l) → e.substLoc σ = e.substLoc σ'
  | .ret vs, h => by
    simp only [Expr.substLoc, Expr.fv] at h ⊢; rw [Val.substLocList_congr vs h]
  | .app e1 e2, h => by
    simp only [Expr.substLoc]
    rw [Expr.substLoc_congr e1 (fun l hl => h l (by simp [Expr.fv, hl])),
      Expr.substLoc_congr e2 (fun l hl => h l (by simp [Expr.fv, hl]))]
  | .call f e1 e2, h => by
    simp only [Expr.substLoc]
    rw [Expr.substLoc_congr e1 (fun l hl => h l (by simp [Expr.fv, hl])),
      Expr.substLoc_congr e2 (fun l hl => h l (by simp [Expr.fv, hl]))]
  | .letIn xs e1 e2, h => by
    simp only [Expr.substLoc]
    rw [Expr.substLoc_congr e1 (fun l hl => h l (by simp [Expr.fv, hl])),
      Expr.substLoc_congr e2 (fun l hl => h l (by
        simp only [Expr.fv, List.mem_append]; exact .inr (loc_mem_filterMap_unshift hl)))]
  | .bmatch e bs, h => by
    simp only [Expr.substLoc]
    rw [Expr.substLoc_congr e (fun l hl => h l (by simp [Expr.fv, hl])),
      Branches.substLoc_congr bs (fun l hl => h l (by simp [Expr.fv, hl]))]
  | .dmatch e bs, h => by
    simp only [Expr.substLoc]
    rw [Expr.substLoc_congr e (fun l hl => h l (by simp [Expr.fv, hl])),
      Branches.substLoc_congr bs (fun l hl => h l (by simp [Expr.fv, hl]))]
  | .drop x e, h => by
    simp only [Expr.substLoc]
    rw [Val.substLoc_congr x (fun l hl => h l (by simp [Expr.fv, hl])),
      Expr.substLoc_congr e (fun l hl => h l (by simp [Expr.fv, hl]))]
  | .free k e, h => by
    simp only [Expr.substLoc]
    rw [Expr.substLoc_congr e (fun l hl => h l (by simp [Expr.fv, hl]))]
  | .prim op vs, h => by
    simp only [Expr.substLoc, Expr.fv] at h ⊢; rw [Val.substLocList_congr vs h]
theorem Branches.substLoc_congr {n : Nat} {σ σ' : Nat → Option (Val 0)} :
    ∀ bs : Branches n, (∀ l, Var.loc l ∈ Branches.fv bs → σ l = σ' l) →
      Branches.substLoc σ bs = Branches.substLoc σ' bs
  | .nil, _ => rfl
  | .cons c xs e bs, h => by
    simp only [Branches.substLoc]
    rw [Expr.substLoc_congr e (fun l hl => h l (by
        simp only [Branches.fv, List.mem_append]; exact .inl (loc_mem_filterMap_unshift hl))),
      Branches.substLoc_congr bs (fun l hl => h l (by simp [Branches.fv, hl]))]
end

/-! ## Matching commutes with location substitution -/

/-- Substitute locations in a branch. -/
def Branch.substLoc {n : Nat} (σ : Nat → Option (Val 0)) (b : Branch n) : Branch n :=
  ⟨b.ctor, b.binders, b.body.substLoc σ⟩

theorem Branches.toList_substLoc {n : Nat} (σ : Nat → Option (Val 0)) :
    ∀ bs : Branches n, (bs.substLoc σ).toList = bs.toList.map (Branch.substLoc σ)
  | .nil => rfl
  | .cons c xs e bs => by
    simp only [Branches.substLoc, Branches.toList_cons, List.map_cons,
      Branches.toList_substLoc σ bs]
    rfl

theorem Branches.find_substLoc {n : Nat} (σ : Nat → Option (Val 0)) (bs : Branches n)
    (c : CName) (k : Nat) : (bs.substLoc σ).find c k = (bs.find c k).map (Branch.substLoc σ) := by
  unfold Branches.find
  rw [Branches.toList_substLoc, List.find?_map]
  rfl

end FIP
