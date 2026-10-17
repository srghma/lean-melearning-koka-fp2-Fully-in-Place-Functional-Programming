module

public import RequestProject.AppE_HeapSoundness.Heap

@[expose] public section

/-!
# Substitution lemmas for `λfip`

* congruence of substitutions, composition of substitutions on values, closed values;
* substituting closed values for locations commutes with the substitution of variables
  (`LExpr.substLoc_subst`), only depends on the locations of an expression
  (`LExpr.substLoc_congr`), and does nothing on an expression without locations;
* **renaming preserves well-formedness** (`LWf.rename`, Lemma 11 for `λfip`): for any
  renaming `f : Fin n → Var m` of the variables in scope;
* the locations of a well-formed expression are in its environments (`LWf.locs_sub`).
-/

namespace FIP.Lam

/-! ## Values -/

@[simp] theorem LVal.subst_bvar {n m : Nat} (σ : Fin n → LVal m) (i : Fin n) :
    (LVal.var (.bvar i)).subst σ = σ i := rfl

@[simp] theorem LVal.subst_loc {n m : Nat} (σ : Fin n → LVal m) (l : Nat) :
    (LVal.var (.loc l) : LVal n).subst σ = .var (.loc l) := rfl

mutual
theorem LVal.subst_congr {n m : Nat} {σ σ' : Fin n → LVal m} (h : ∀ i, σ i = σ' i) :
    ∀ v : LVal n, v.subst σ = v.subst σ'
  | .var (.bvar i) => h i
  | .var (.loc _) => rfl
  | .fn _ => rfl
  | .ctor c vs => by simp only [LVal.subst]; rw [LVals.subst_congr h vs]
  | .lam zs c k b => by simp only [LVal.subst]; rw [LVals.subst_congr h zs]
theorem LVals.subst_congr {n m : Nat} {σ σ' : Fin n → LVal m} (h : ∀ i, σ i = σ' i) :
    ∀ vs : LVals n, vs.subst σ = vs.subst σ'
  | .nil => rfl
  | .cons v vs => by simp only [LVals.subst]; rw [LVal.subst_congr h v, LVals.subst_congr h vs]
end

mutual
theorem LVal.subst_subst {n m p : Nat} (τ : Fin n → LVal m) (σ : Fin m → LVal p) :
    ∀ v : LVal n, (v.subst τ).subst σ = v.subst (fun i => (τ i).subst σ)
  | .var (.bvar _) => rfl
  | .var (.loc _) => rfl
  | .fn _ => rfl
  | .ctor c vs => by simp only [LVal.subst]; rw [LVals.subst_subst τ σ vs]
  | .lam zs c k b => by simp only [LVal.subst]; rw [LVals.subst_subst τ σ zs]
theorem LVals.subst_subst {n m p : Nat} (τ : Fin n → LVal m) (σ : Fin m → LVal p) :
    ∀ vs : LVals n, (vs.subst τ).subst σ = vs.subst (fun i => (τ i).subst σ)
  | .nil => rfl
  | .cons v vs => by
    simp only [LVals.subst]; rw [LVal.subst_subst τ σ v, LVals.subst_subst τ σ vs]
end

/-- A closed value is unchanged by any substitution. -/
theorem LVal.weaken_subst {n m : Nat} (σ : Fin n → LVal m) (v : LVal 0) :
    (v.weaken : LVal n).subst σ = v.weaken := by
  unfold LVal.weaken
  rw [LVal.subst_subst]
  exact LVal.subst_congr (fun i => i.elim0) v

mutual
theorem LVal.subst_elim0 : ∀ v : LVal 0, v.subst Fin.elim0 = v
  | .var (.bvar i) => i.elim0
  | .var (.loc _) => rfl
  | .fn _ => rfl
  | .ctor c vs => by simp only [LVal.subst]; rw [LVals.subst_elim0 vs]
  | .lam zs c k b => by simp only [LVal.subst]; rw [LVals.subst_elim0 zs]
theorem LVals.subst_elim0 : ∀ vs : LVals 0, vs.subst Fin.elim0 = vs
  | .nil => rfl
  | .cons v vs => by simp only [LVals.subst]; rw [LVal.subst_elim0 v, LVals.subst_elim0 vs]
end

@[simp] theorem LVal.weaken_zero (v : LVal 0) : (v.weaken : LVal 0) = v := LVal.subst_elim0 v

theorem LVal.shift_var {n : Nat} (k : Nat) (x : Var n) :
    (LVal.var x).shift k = .var (x.shift k) := by
  cases x <;> rfl

theorem LSubst.up_lt {n m : Nat} (k : Nat) (σ : Fin n → LVal m) (i : Fin (n + k)) (h : i.val < k) :
    LSubst.up k σ i = .var (.bvar ⟨i, by omega⟩) := by simp [LSubst.up, h]

theorem LSubst.up_shift {n m : Nat} (k : Nat) (σ : Fin n → LVal m) (x : Var n) :
    (LVal.var (x.shift k)).subst (LSubst.up k σ) = ((LVal.var x).subst σ).shift k := by
  cases x with
  | loc l => rfl
  | bvar i =>
    simp only [Var.shift, LVal.subst_bvar, LSubst.up, show ¬ (k + i.val < k) by omega,
      dite_false]
    congr 2; ext; simp

theorem LSubst.up_newB {n m k : Nat} (σ : Fin n → LVal m) (j : Fin k) :
    (LVal.var (Var.newB j : Var (n + k))).subst (LSubst.up k σ) = .var (Var.newB j) := by
  simp [Var.newB, LSubst.up]

theorem LSubst.inst_lt {n m : Nat} (k : Nat) (vs : List (LVal m)) (σ : Fin n → LVal m)
    (i : Fin (n + k)) (h : i.val < k) : LSubst.inst k vs σ i = vs.getD i.val default := by
  simp [LSubst.inst, h]

theorem LSubst.inst_ge {n m : Nat} (k : Nat) (vs : List (LVal m)) (σ : Fin n → LVal m)
    (i : Fin (n + k)) (h : k ≤ i.val) : LSubst.inst k vs σ i = σ ⟨i.val - k, by omega⟩ := by
  simp [LSubst.inst, show ¬ i.val < k by omega]

theorem LSubst.inst_shift {n m : Nat} (k : Nat) (vs : List (LVal m)) (σ : Fin n → LVal m)
    (x : Var n) : (LVal.var (x.shift k)).subst (LSubst.inst k vs σ) = (LVal.var x).subst σ := by
  cases x with
  | loc l => rfl
  | bvar i =>
    simp only [Var.shift, LVal.subst_bvar]
    rw [LSubst.inst_ge _ _ _ _ (by simp)]
    congr 1; ext; simp

theorem LSubst.inst_newB {n m k : Nat} (vs : List (LVal m)) (σ : Fin n → LVal m)
    (hl : vs.length = k) (j : Fin k) :
    (LVal.var (Var.newB j : Var (n + k))).subst (LSubst.inst k vs σ) = vs[j.val]'(by omega) := by
  simp only [Var.newB, LVal.subst_bvar]
  rw [LSubst.inst_lt _ _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp; omega)]

theorem bvals_subst_inst {n m k : Nat} (vs : List (LVal m)) (σ : Fin n → LVal m)
    (hl : vs.length = k) : (bvals n k).map (LVal.subst (LSubst.inst k vs σ)) = vs := by
  apply List.ext_getElem (by simp [bvals, hl])
  intro i h1 h2
  simp only [bvals, List.map_map, List.getElem_map, Function.comp, List.getElem_finRange]
  rw [LSubst.inst_newB vs σ hl]; rfl

theorem bvals_subst_up {n m k : Nat} (σ : Fin n → LVal m) :
    (bvals n k).map (LVal.subst (LSubst.up k σ)) = bvals m k := by
  simp only [bvals, List.map_map]
  exact List.map_congr_left fun j _ => LSubst.up_newB σ j

/-! ## Expressions -/

mutual
theorem LExpr.subst_congr {n m : Nat} {σ σ' : Fin n → LVal m} (h : ∀ i, σ i = σ' i) :
    ∀ e : LExpr n, e.subst σ = e.subst σ'
  | .ret vs => by simp only [LExpr.subst]; rw [LVals.subst_congr h vs]
  | .app e1 e2 => by simp only [LExpr.subst]; rw [LExpr.subst_congr h e1, LExpr.subst_congr h e2]
  | .call f e1 e2 => by
    simp only [LExpr.subst]; rw [LExpr.subst_congr h e1, LExpr.subst_congr h e2]
  | .letIn k e1 e2 => by
    simp only [LExpr.subst]
    rw [LExpr.subst_congr h e1, LExpr.subst_congr (σ := LSubst.up k σ) (σ' := LSubst.up k σ')
      (fun i => by simp only [LSubst.up]; split <;> simp [h]) e2]
  | .match x bs => by
    simp only [LExpr.subst]; rw [LVal.subst_congr h x, LBranches.subst_congr h bs]
  | .dup x e => by simp only [LExpr.subst]; rw [LVal.subst_congr h x, LExpr.subst_congr h e]
  | .drop x e => by simp only [LExpr.subst]; rw [LVal.subst_congr h x, LExpr.subst_congr h e]
  | .dropru x k e => by
    simp only [LExpr.subst]; rw [LVal.subst_congr h x, LExpr.subst_congr h e]
  | .free k e => by simp only [LExpr.subst]; rw [LExpr.subst_congr h e]
  | .alloc k e => by simp only [LExpr.subst]; rw [LExpr.subst_congr h e]
theorem LBranches.subst_congr {n m : Nat} {σ σ' : Fin n → LVal m} (h : ∀ i, σ i = σ' i) :
    ∀ bs : LBranches n, bs.subst σ = bs.subst σ'
  | .nil => rfl
  | .cons c k e bs => by
    simp only [LBranches.subst]
    rw [LExpr.subst_congr (σ := LSubst.up k σ) (σ' := LSubst.up k σ')
      (fun i => by simp only [LSubst.up]; split <;> simp [h]) e, LBranches.subst_congr h bs]
end

theorem subst_dups {n m : Nat} (σ : Fin n → LVal m) (vs : List (LVal n)) (e : LExpr n) :
    (dups vs e).subst σ = dups (vs.map (LVal.subst σ)) (e.subst σ) := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp [dups, LExpr.subst, ih]

/-- A branch with its body substituted. -/
def LBranch.subst {n m : Nat} (σ : Fin n → LVal m) (b : LBranch n) : LBranch m :=
  ⟨b.ctor, b.k, b.body.subst (LSubst.up b.k σ)⟩

theorem LBranches.toList_subst {n m : Nat} (σ : Fin n → LVal m) :
    ∀ bs : LBranches n, (bs.subst σ).toList = bs.toList.map (LBranch.subst σ)
  | .nil => rfl
  | .cons c k e bs => by
    simp [LBranches.subst, LBranches.toList_subst σ bs, LBranch.subst]

theorem LBranches.find_mem {n : Nat} {bs : LBranches n} {c : CName} {k : Nat} {b : LBranch n}
    (h : bs.find c k = some b) : b ∈ bs.toList := List.mem_of_find?_eq_some h

theorem LBranches.find_spec {n : Nat} {bs : LBranches n} {c : CName} {k : Nat} {b : LBranch n}
    (h : bs.find c k = some b) : b.ctor = c ∧ b.k = k := by
  have := List.find?_some h
  simpa using this

theorem LBranches.find_subst {n m : Nat} (σ : Fin n → LVal m) (bs : LBranches n) (c : CName)
    (k : Nat) : (bs.subst σ).find c k = (bs.find c k).map (LBranch.subst σ) := by
  simp only [LBranches.find, LBranches.toList_subst, List.find?_map]
  rfl

/-! ## Substituting closed values for locations -/

@[simp] theorem LVal.substLoc_loc {n : Nat} (σ : Nat → Option (LVal 0)) (l : Nat) :
    (LVal.var (.loc l) : LVal n).substLoc σ = ((σ l).map LVal.weaken).getD (.var (.loc l)) := rfl

@[simp] theorem LVal.substLoc_bvar {n : Nat} (σ : Nat → Option (LVal 0)) (i : Fin n) :
    (LVal.var (.bvar i)).substLoc σ = .var (.bvar i) := rfl

mutual
theorem LVal.substLoc_subst {n m : Nat} (σ : Nat → Option (LVal 0)) (τ : Fin n → LVal m) :
    ∀ v : LVal n, (v.subst τ).substLoc σ = (v.substLoc σ).subst (fun i => (τ i).substLoc σ)
  | .var (.bvar _) => rfl
  | .var (.loc l) => by
    simp only [LVal.subst_loc, LVal.substLoc_loc]
    cases σ l with
    | none => rfl
    | some w => simp [LVal.weaken_subst]
  | .fn _ => rfl
  | .ctor c vs => by simp only [LVal.subst, LVal.substLoc]; rw [LVals.substLoc_subst σ τ vs]
  | .lam zs c k b => by simp only [LVal.subst, LVal.substLoc]; rw [LVals.substLoc_subst σ τ zs]
theorem LVals.substLoc_subst {n m : Nat} (σ : Nat → Option (LVal 0)) (τ : Fin n → LVal m) :
    ∀ vs : LVals n, (vs.subst τ).substLoc σ = (vs.substLoc σ).subst (fun i => (τ i).substLoc σ)
  | .nil => rfl
  | .cons v vs => by
    simp only [LVals.subst, LVals.substLoc]
    rw [LVal.substLoc_subst σ τ v, LVals.substLoc_subst σ τ vs]
end

theorem LVal.substLoc_weaken {n : Nat} (σ : Nat → Option (LVal 0)) (v : LVal 0) :
    (v.weaken : LVal n).substLoc σ = (v.substLoc σ).weaken := by
  unfold LVal.weaken
  rw [LVal.substLoc_subst]
  exact LVal.subst_congr (fun i => i.elim0) _

theorem LVal.substLoc_shift {n : Nat} (σ : Nat → Option (LVal 0)) (k : Nat) (v : LVal n) :
    (v.shift k).substLoc σ = (v.substLoc σ).shift k := by
  unfold LVal.shift
  rw [LVal.substLoc_subst]; rfl

theorem LSubst.up_substLoc {n m : Nat} (σ : Nat → Option (LVal 0)) (k : Nat)
    (τ : Fin n → LVal m) (i : Fin (n + k)) :
    (LSubst.up k τ i).substLoc σ = LSubst.up k (fun j => (τ j).substLoc σ) i := by
  simp only [LSubst.up]
  split
  · rfl
  · exact LVal.substLoc_shift σ k _

mutual
theorem LExpr.substLoc_subst {n m : Nat} (σ : Nat → Option (LVal 0)) (τ : Fin n → LVal m) :
    ∀ e : LExpr n, (e.subst τ).substLoc σ = (e.substLoc σ).subst (fun i => (τ i).substLoc σ)
  | .ret vs => by simp only [LExpr.subst, LExpr.substLoc]; rw [LVals.substLoc_subst]
  | .app e1 e2 => by
    simp only [LExpr.subst, LExpr.substLoc]
    rw [LExpr.substLoc_subst σ τ e1, LExpr.substLoc_subst σ τ e2]
  | .call f e1 e2 => by
    simp only [LExpr.subst, LExpr.substLoc]
    rw [LExpr.substLoc_subst σ τ e1, LExpr.substLoc_subst σ τ e2]
  | .letIn k e1 e2 => by
    simp only [LExpr.subst, LExpr.substLoc]
    rw [LExpr.substLoc_subst σ τ e1, LExpr.substLoc_subst σ (LSubst.up k τ) e2,
      LExpr.subst_congr (LSubst.up_substLoc σ k τ)]
  | .match x bs => by
    simp only [LExpr.subst, LExpr.substLoc]
    rw [LVal.substLoc_subst σ τ x, LBranches.substLoc_subst σ τ bs]
  | .dup x e => by
    simp only [LExpr.subst, LExpr.substLoc]
    rw [LVal.substLoc_subst σ τ x, LExpr.substLoc_subst σ τ e]
  | .drop x e => by
    simp only [LExpr.subst, LExpr.substLoc]
    rw [LVal.substLoc_subst σ τ x, LExpr.substLoc_subst σ τ e]
  | .dropru x k e => by
    simp only [LExpr.subst, LExpr.substLoc]
    rw [LVal.substLoc_subst σ τ x, LExpr.substLoc_subst σ τ e]
  | .free k e => by simp only [LExpr.subst, LExpr.substLoc]; rw [LExpr.substLoc_subst σ τ e]
  | .alloc k e => by simp only [LExpr.subst, LExpr.substLoc]; rw [LExpr.substLoc_subst σ τ e]
theorem LBranches.substLoc_subst {n m : Nat} (σ : Nat → Option (LVal 0)) (τ : Fin n → LVal m) :
    ∀ bs : LBranches n,
      (bs.subst τ).substLoc σ = (bs.substLoc σ).subst (fun i => (τ i).substLoc σ)
  | .nil => rfl
  | .cons c k e bs => by
    simp only [LBranches.subst, LBranches.substLoc]
    rw [LExpr.substLoc_subst σ (LSubst.up k τ) e, LExpr.subst_congr (LSubst.up_substLoc σ k τ),
      LBranches.substLoc_subst σ τ bs]
end

theorem LSubst.inst_substLoc {n m : Nat} (σ : Nat → Option (LVal 0)) (k : Nat)
    (vs : List (LVal m)) (ρ : Fin n → LVal m) (i : Fin (n + k)) :
    (LSubst.inst k vs ρ i).substLoc σ =
      LSubst.inst k (vs.map (LVal.substLoc σ)) (fun j => (ρ j).substLoc σ) i := by
  simp only [LSubst.inst]
  split
  · rename_i h
    by_cases hl : i.val < vs.length
    · rw [List.getD_eq_getElem _ _ hl, List.getD_eq_getElem _ _ (by simpa using hl)]; simp
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by simp; omega)]; rfl
  · rfl

theorem LSubst.ofList_substLoc {m : Nat} (σ : Nat → Option (LVal 0)) (k : Nat)
    (vs : List (LVal m)) (i : Fin k) :
    (LSubst.ofList k vs i).substLoc σ = LSubst.ofList k (vs.map (LVal.substLoc σ)) i := by
  simp only [LSubst.ofList]
  by_cases hl : i.val < vs.length
  · rw [List.getD_eq_getElem _ _ hl, List.getD_eq_getElem _ _ (by simpa using hl)]; simp
  · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by simp; omega)]; rfl

/-! ### Congruence -/

mutual
theorem LVal.substLoc_congr {n : Nat} {σ σ' : Nat → Option (LVal 0)} :
    ∀ v : LVal n, (∀ l ∈ v.locs, σ l = σ' l) → v.substLoc σ = v.substLoc σ'
  | .var (.bvar _), _ => rfl
  | .var (.loc l), h => by simp [h l (by simp [LVal.locs])]
  | .fn _, _ => rfl
  | .ctor c vs, h => by
    simp only [LVal.substLoc]; rw [LVals.substLoc_congr vs (by simpa [LVal.locs] using h)]
  | .lam zs c k b, h => by
    simp only [LVal.substLoc]; rw [LVals.substLoc_congr zs (by simpa [LVal.locs] using h)]
theorem LVals.substLoc_congr {n : Nat} {σ σ' : Nat → Option (LVal 0)} :
    ∀ vs : LVals n, (∀ l ∈ vs.locs, σ l = σ' l) → vs.substLoc σ = vs.substLoc σ'
  | .nil, _ => rfl
  | .cons v vs, h => by
    simp only [LVals.substLoc]
    rw [LVal.substLoc_congr v (fun l hl => h l (by simp [LVals.locs, hl])),
      LVals.substLoc_congr vs (fun l hl => h l (by simp [LVals.locs, hl]))]
end

mutual
theorem LExpr.substLoc_congr {n : Nat} {σ σ' : Nat → Option (LVal 0)} :
    ∀ e : LExpr n, (∀ l ∈ e.locs, σ l = σ' l) → e.substLoc σ = e.substLoc σ'
  | .ret vs, h => by simp only [LExpr.substLoc]; rw [LVals.substLoc_congr vs h]
  | .app e1 e2, h => by
    simp only [LExpr.substLoc]
    rw [LExpr.substLoc_congr e1 (fun l hl => h l (by simp [LExpr.locs, hl])),
      LExpr.substLoc_congr e2 (fun l hl => h l (by simp [LExpr.locs, hl]))]
  | .call f e1 e2, h => by
    simp only [LExpr.substLoc]
    rw [LExpr.substLoc_congr e1 (fun l hl => h l (by simp [LExpr.locs, hl])),
      LExpr.substLoc_congr e2 (fun l hl => h l (by simp [LExpr.locs, hl]))]
  | .letIn k e1 e2, h => by
    simp only [LExpr.substLoc]
    rw [LExpr.substLoc_congr e1 (fun l hl => h l (by simp [LExpr.locs, hl])),
      LExpr.substLoc_congr e2 (fun l hl => h l (by simp [LExpr.locs, hl]))]
  | .match x bs, h => by
    simp only [LExpr.substLoc]
    rw [LVal.substLoc_congr x (fun l hl => h l (by simp [LExpr.locs, hl])),
      LBranches.substLoc_congr bs (fun l hl => h l (by simp [LExpr.locs, hl]))]
  | .dup x e, h => by
    simp only [LExpr.substLoc]
    rw [LVal.substLoc_congr x (fun l hl => h l (by simp [LExpr.locs, hl])),
      LExpr.substLoc_congr e (fun l hl => h l (by simp [LExpr.locs, hl]))]
  | .drop x e, h => by
    simp only [LExpr.substLoc]
    rw [LVal.substLoc_congr x (fun l hl => h l (by simp [LExpr.locs, hl])),
      LExpr.substLoc_congr e (fun l hl => h l (by simp [LExpr.locs, hl]))]
  | .dropru x k e, h => by
    simp only [LExpr.substLoc]
    rw [LVal.substLoc_congr x (fun l hl => h l (by simp [LExpr.locs, hl])),
      LExpr.substLoc_congr e (fun l hl => h l (by simp [LExpr.locs, hl]))]
  | .free k e, h => by simp only [LExpr.substLoc]; rw [LExpr.substLoc_congr e h]
  | .alloc k e, h => by simp only [LExpr.substLoc]; rw [LExpr.substLoc_congr e h]
theorem LBranches.substLoc_congr {n : Nat} {σ σ' : Nat → Option (LVal 0)} :
    ∀ bs : LBranches n, (∀ l ∈ bs.locs, σ l = σ' l) → bs.substLoc σ = bs.substLoc σ'
  | .nil, _ => rfl
  | .cons c k e bs, h => by
    simp only [LBranches.substLoc]
    rw [LExpr.substLoc_congr e (fun l hl => h l (by simp [LBranches.locs, hl])),
      LBranches.substLoc_congr bs (fun l hl => h l (by simp [LBranches.locs, hl]))]
end

mutual
theorem LVal.substLoc_none {n : Nat} : ∀ v : LVal n, v.substLoc (fun _ => none) = v
  | .var (.bvar _) => rfl
  | .var (.loc _) => rfl
  | .fn _ => rfl
  | .ctor c vs => by simp only [LVal.substLoc]; rw [LVals.substLoc_none vs]
  | .lam zs c k b => by simp only [LVal.substLoc]; rw [LVals.substLoc_none zs]
theorem LVals.substLoc_none {n : Nat} : ∀ vs : LVals n, vs.substLoc (fun _ => none) = vs
  | .nil => rfl
  | .cons v vs => by simp only [LVals.substLoc]; rw [LVal.substLoc_none v, LVals.substLoc_none vs]
end

mutual
theorem LExpr.substLoc_none {n : Nat} : ∀ e : LExpr n, e.substLoc (fun _ => none) = e
  | .ret vs => by simp only [LExpr.substLoc]; rw [LVals.substLoc_none]
  | .app e1 e2 => by simp only [LExpr.substLoc]; rw [LExpr.substLoc_none e1, LExpr.substLoc_none e2]
  | .call f e1 e2 => by
    simp only [LExpr.substLoc]; rw [LExpr.substLoc_none e1, LExpr.substLoc_none e2]
  | .letIn k e1 e2 => by
    simp only [LExpr.substLoc]; rw [LExpr.substLoc_none e1, LExpr.substLoc_none e2]
  | .match x bs => by
    simp only [LExpr.substLoc]; rw [LVal.substLoc_none x, LBranches.substLoc_none bs]
  | .dup x e => by simp only [LExpr.substLoc]; rw [LVal.substLoc_none x, LExpr.substLoc_none e]
  | .drop x e => by simp only [LExpr.substLoc]; rw [LVal.substLoc_none x, LExpr.substLoc_none e]
  | .dropru x k e => by
    simp only [LExpr.substLoc]; rw [LVal.substLoc_none x, LExpr.substLoc_none e]
  | .free k e => by simp only [LExpr.substLoc]; rw [LExpr.substLoc_none e]
  | .alloc k e => by simp only [LExpr.substLoc]; rw [LExpr.substLoc_none e]
theorem LBranches.substLoc_none {n : Nat} : ∀ bs : LBranches n, bs.substLoc (fun _ => none) = bs
  | .nil => rfl
  | .cons c k e bs => by
    simp only [LBranches.substLoc]; rw [LExpr.substLoc_none e, LBranches.substLoc_none bs]
end

/-- Substituting for locations does nothing on an expression without those locations. -/
theorem LExpr.substLoc_of_none {n : Nat} {σ : Nat → Option (LVal 0)} {e : LExpr n}
    (h : ∀ l ∈ e.locs, σ l = none) : e.substLoc σ = e :=
  (LExpr.substLoc_congr e h).trans (LExpr.substLoc_none e)

theorem LVal.substLoc_of_none {n : Nat} {σ : Nat → Option (LVal 0)} {v : LVal n}
    (h : ∀ l ∈ v.locs, σ l = none) : v.substLoc σ = v :=
  (LVal.substLoc_congr v h).trans (LVal.substLoc_none v)

theorem LExpr.substLoc_of_locs_nil {n : Nat} (σ : Nat → Option (LVal 0)) {e : LExpr n}
    (h : e.locs = []) : e.substLoc σ = e :=
  LExpr.substLoc_of_none (by simp [h])

end FIP.Lam
