module

public import RequestProject.AppB_StoreSoundness.Store

@[expose] public section

/- ══════════════════ PAPER sec. 2.3, App. B START: Store Semantics: Theorem 1 and Corollary 1; Soundness of Store Semantics (PDF p. 12; App. B.2-B.6 on pp. 40-54) ══════════════════
   The setting of Theorem 1: substituting store contents for locations (`[S]e`) and the
   paper's fragment of the calculus (`Sig.PaperFragment`). -/

/-!
# Soundness of the store semantics (Theorem 1, Corollary 1; Appendix B): the setting

`[S]e` substitutes, for every location bound in the store `S`, the value it denotes
(reading the store recursively).  Theorem 1 of the paper states that for a well-formed
FIP expression evaluated in a store whose owned part is linear and has exactly the owned
resources as roots, the store semantics computes the same result as the functional
semantics, without leaving garbage.

This file defines the substitution of values for locations (`Expr.substLoc`) and the
setting of the theorem.  The theorem concerns the calculus of the paper, so it is stated
for the *scalar-free* fragment (no literals, primitive operations or scalar binders) and
without allocation budgets `fip(n)` (the store has no room for allocation credits).

A store binds locations only (`Var 0`): with de Bruijn indices a closed expression has no
program variables, so a store cannot bind one.  (An earlier formulation over named syntax
allowed stores to bind program names, which made the theorem false.)  The theorem itself,
`store_sound`, is in `RequestProject/AppB_StoreSoundness/StoreSoundProof.lean`.
-/

namespace FIP

/-! ## Substituting locations -/

mutual
/-- Substitute closed values for locations in a value. -/
def Val.substLoc {n : Nat} (σ : Nat → Option (Val 0)) : Val n → Val n
  | .var (.loc l) => ((σ l).map Val.weaken).getD (.var (.loc l))
  | .var (.bvar i) => .var (.bvar i)
  | .fn f => .fn f
  | .ctor c vs => .ctor c (Val.substLocList σ vs)
  | .lit k => .lit k
/-- Substitute closed values for locations in a list of values. -/
def Val.substLocList {n : Nat} (σ : Nat → Option (Val 0)) : List (Val n) → List (Val n)
  | [] => []
  | v :: vs => Val.substLoc σ v :: Val.substLocList σ vs
end

@[simp] theorem Val.substLocList_eq_map {n : Nat} (σ : Nat → Option (Val 0)) (vs : List (Val n)) :
    Val.substLocList σ vs = vs.map (Val.substLoc σ) := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp [Val.substLocList, ih]

mutual
/-- Substitute closed values for locations in an expression (locations are never bound,
    and the values are closed, so there is no capture). -/
def Expr.substLoc {n : Nat} (σ : Nat → Option (Val 0)) : Expr n → Expr n
  | .ret vs => .ret (Val.substLocList σ vs)
  | .app e1 e2 => .app (Expr.substLoc σ e1) (Expr.substLoc σ e2)
  | .call f e1 e2 => .call f (Expr.substLoc σ e1) (Expr.substLoc σ e2)
  | .letIn xs e1 e2 => .letIn xs (Expr.substLoc σ e1) (Expr.substLoc σ e2)
  | .bmatch e bs => .bmatch (Expr.substLoc σ e) (Branches.substLoc σ bs)
  | .dmatch e bs => .dmatch (Expr.substLoc σ e) (Branches.substLoc σ bs)
  | .drop x e => .drop (Val.substLoc σ x) (Expr.substLoc σ e)
  | .free k e => .free k (Expr.substLoc σ e)
  | .prim op vs => .prim op (Val.substLocList σ vs)
/-- Substitute closed values for locations in branches. -/
def Branches.substLoc {n : Nat} (σ : Nat → Option (Val 0)) : Branches n → Branches n
  | .nil => .nil
  | .cons c xs e bs => .cons c xs (Expr.substLoc σ e) (Branches.substLoc σ bs)
end

/-- A value or expression *without locations*. -/
def NoLoc {n : Nat} (l : List (Var n)) : Prop := ∀ k, Var.loc k ∉ l

mutual
theorem Val.substLoc_of_noLoc {n : Nat} (σ : Nat → Option (Val 0)) :
    ∀ v : Val n, NoLoc (Val.fv v) → Val.substLoc σ v = v
  | .var (.loc k), h => absurd (by simp [Val.fv]) (h k)
  | .var (.bvar _), _ => rfl
  | .fn _, _ => rfl
  | .lit _, _ => rfl
  | .ctor c vs, h => by
    simp only [Val.substLoc, Val.fv] at h ⊢
    rw [Val.substLocList_of_noLoc σ vs h]
theorem Val.substLocList_of_noLoc {n : Nat} (σ : Nat → Option (Val 0)) :
    ∀ vs : List (Val n), NoLoc (Val.fvList vs) → Val.substLocList σ vs = vs
  | [], _ => rfl
  | v :: vs, h => by
    simp only [Val.substLocList]
    rw [Val.substLoc_of_noLoc σ v (fun k hk => h k (by simp [Val.fvList, hk])),
      Val.substLocList_of_noLoc σ vs (fun k hk => h k (by simp [Val.fvList, hk]))]
end

theorem loc_mem_filterMap_unshift {n k : Nat} {l : Nat} {fv : List (Var (n + k))}
    (h : Var.loc l ∈ fv) : Var.loc l ∈ fv.filterMap (Var.unshift k) :=
  List.mem_filterMap.mpr ⟨_, h, rfl⟩

mutual
theorem Expr.substLoc_of_noLoc {n : Nat} (σ : Nat → Option (Val 0)) :
    ∀ e : Expr n, NoLoc e.fv → e.substLoc σ = e
  | .ret vs, h => by
    simp only [Expr.substLoc, Expr.fv] at h ⊢; rw [Val.substLocList_of_noLoc σ vs h]
  | .app e1 e2, h => by
    simp only [Expr.substLoc]
    rw [Expr.substLoc_of_noLoc σ e1 (fun k hk => h k (by simp [Expr.fv, hk])),
      Expr.substLoc_of_noLoc σ e2 (fun k hk => h k (by simp [Expr.fv, hk]))]
  | .call f e1 e2, h => by
    simp only [Expr.substLoc]
    rw [Expr.substLoc_of_noLoc σ e1 (fun k hk => h k (by simp [Expr.fv, hk])),
      Expr.substLoc_of_noLoc σ e2 (fun k hk => h k (by simp [Expr.fv, hk]))]
  | .letIn xs e1 e2, h => by
    simp only [Expr.substLoc]
    rw [Expr.substLoc_of_noLoc σ e1 (fun k hk => h k (by simp [Expr.fv, hk])),
      Expr.substLoc_of_noLoc σ e2 (fun k hk => h k (by
        simp only [Expr.fv, List.mem_append]; exact .inr (loc_mem_filterMap_unshift hk)))]
  | .bmatch e bs, h => by
    simp only [Expr.substLoc]
    rw [Expr.substLoc_of_noLoc σ e (fun k hk => h k (by simp [Expr.fv, hk])),
      Branches.substLoc_of_noLoc σ bs (fun k hk => h k (by simp [Expr.fv, hk]))]
  | .dmatch e bs, h => by
    simp only [Expr.substLoc]
    rw [Expr.substLoc_of_noLoc σ e (fun k hk => h k (by simp [Expr.fv, hk])),
      Branches.substLoc_of_noLoc σ bs (fun k hk => h k (by simp [Expr.fv, hk]))]
  | .drop x e, h => by
    simp only [Expr.substLoc]
    rw [Val.substLoc_of_noLoc σ x (fun k hk => h k (by simp [Expr.fv, hk])),
      Expr.substLoc_of_noLoc σ e (fun k hk => h k (by simp [Expr.fv, hk]))]
  | .free k e, h => by
    simp only [Expr.substLoc]
    rw [Expr.substLoc_of_noLoc σ e (fun k hk => h k (by simp [Expr.fv, hk]))]
  | .prim op vs, h => by
    simp only [Expr.substLoc, Expr.fv] at h ⊢; rw [Val.substLocList_of_noLoc σ vs h]
theorem Branches.substLoc_of_noLoc {n : Nat} (σ : Nat → Option (Val 0)) :
    ∀ bs : Branches n, NoLoc (Branches.fv bs) → Branches.substLoc σ bs = bs
  | .nil, _ => rfl
  | .cons c xs e bs, h => by
    simp only [Branches.substLoc]
    rw [Expr.substLoc_of_noLoc σ e (fun k hk => h k (by
        simp only [Branches.fv, List.mem_append]; exact .inl (loc_mem_filterMap_unshift hk))),
      Branches.substLoc_of_noLoc σ bs (fun k hk => h k (by simp [Branches.fv, hk]))]
end

/-! ## The scalar-free fragment (the calculus of the paper) -/

mutual
/-- A value without literals. -/
def Val.scalarFree {n : Nat} : Val n → Bool
  | .lit _ => false
  | .ctor _ vs => Val.scalarFreeList vs
  | _ => true
/-- Values without literals. -/
def Val.scalarFreeList {n : Nat} : List (Val n) → Bool
  | [] => true
  | v :: vs => Val.scalarFree v && Val.scalarFreeList vs
end

mutual
/-- An expression of the paper's calculus: no literals, primitive operations or scalar
    binders. -/
def Expr.scalarFree {n : Nat} : Expr n → Bool
  | .ret vs => Val.scalarFreeList vs
  | .app e1 e2 => Expr.scalarFree e1 && Expr.scalarFree e2
  | .call _ e1 e2 => Expr.scalarFree e1 && Expr.scalarFree e2
  | .letIn xs e1 e2 => xs.all (!·) && Expr.scalarFree e1 && Expr.scalarFree e2
  | .bmatch e bs => Expr.scalarFree e && Branches.scalarFree bs
  | .dmatch e bs => Expr.scalarFree e && Branches.scalarFree bs
  | .drop x e => Val.scalarFree x && Expr.scalarFree e
  | .free _ e => Expr.scalarFree e
  | .prim _ _ => false
/-- Branches of the paper's calculus. -/
def Branches.scalarFree {n : Nat} : Branches n → Bool
  | .nil => true
  | .cons _ xs e bs => xs.all (!·) && Expr.scalarFree e && Branches.scalarFree bs
end

/-- The setting of Theorem 1: a signature of the paper's calculus whose annotated
    functions are fully in-place (or FBIP), without allocation budgets.  As in the paper,
    where `Σ` maps function names to definitions, the functions of the signature have
    distinct names (otherwise a call to an annotated function could be resolved to an
    unannotated definition of the same name). -/
structure Sig.PaperFragment (sig : Sig) : Prop where
  names : (sig.map (·.name)).Nodup
  wf : sig.Wf
  scalarFree : ∀ fd ∈ sig, (fd.borrowed ++ fd.owned).all (!·) ∧ fd.body.scalarFree
  noBudget : ∀ fd ∈ sig, fd.annot.budget = 0

/-- The functions an expression may call (`dom(Σ)` in the rules) are annotated
    functions of the signature, callable in the given mode of the store semantics. -/
def Cfg.Compatible (cfg : Cfg) (sig : Sig) (fbip : Bool) : Prop :=
  (∀ f ∈ cfg.funs, ∃ fd, sig.lookup f = some fd ∧ fd.annot ≠ .plain) ∧
  (∀ f, cfg.budget f = 0) ∧ (cfg.fbip = true → fbip = true) ∧
  (∀ fd ∈ sig, fd.annot.isFbip = true → fbip = true)

end FIP

/- ══════════════════ PAPER sec. 2.3, App. B END: Store Semantics: Theorem 1 and Corollary 1; Soundness of Store Semantics ══════════════════ -/
