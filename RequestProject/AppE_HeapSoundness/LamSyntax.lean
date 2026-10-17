module

public import RequestProject.AppB_StoreSoundness.Weaken

@[expose] public section

/- ══════════════════ PAPER sec. 5, 5.1, 5.2, App. E.1 START: Reference Counting with Borrowing and Unboxing; Elaborating borrowing; Heap semantics; Properties of Heaps (PDF pp. 22-25, Fig. 9, 10; App. E.1 on pp. 71-75) ══════════════════
   Syntax of `lambda-fip`: explicit `dup`/`drop`, closures `lam^zs xs. e`, substitution. -/

/-!
# The syntax of `λfip` (Fig. 9), with de Bruijn indices

`λfip` extends the FBIP calculus with lambdas `λ^z̄ x̄. e` (whose free variables `z̄` are
written explicitly), `dup x; e`, the reuse-drop `dropru x; e`, `alloc k; e`, and a
non-destructive `match x {Cᵢ x̄ᵢ ↦ dup x̄ᵢ; eᵢ}`.

As for the FIP calculus (`RequestProject/Sec2_Calculus/Syntax.lean`) variables are
**de Bruijn indices** `Fin n` and the scope `n` is an index of every syntactic category:
`LVal n`, `LVals n`, `LExpr n`, `LBranches n`.  **`LExpr 0` is the type of closed `λfip`
expressions**; closed expressions may mention heap locations `Var.loc l`.

## Lambdas are closure-converted

The rule `lam` of Fig. 9 types the body of `λ^z̄ x̄. e` in the environment `∅ | z̄, x̄`: the
body only mentions its parameters `x̄` and the captured variables `z̄`.  With de Bruijn
indices this is a property of the *type* of the body:

`LVal.lam (zs : LVals n) (c k : Nat) (body : LExpr (c + k))`

The `c` captured values `zs` live in the enclosing scope `n`, and the body lives in its own
scope of `c + k` variables: the index `j < k` is the parameter `xⱼ` and `k + i` is the
captured value `zᵢ` (the usual convention: the parameters are the innermost binders).
Substitution acts on the captured values only, and β-reduction instantiates the body with
the arguments and the captured values (`LHead.beta`).

## Lists of values

Values occur in lists (the arguments of a constructor, the components of a tuple, the
captured values of a lambda).  Lean's nested inductive types cannot nest `List` inside an
indexed family, so lists of values have their own type `LVals n`, with the conversions
`LVals.toList` and `LVals.ofList` to `List (LVal n)`.
-/

namespace FIP.Lam

mutual
/-- Values of `λfip` with at most `n` free variables: variables, top-level functions,
    constructors and lambdas. -/
inductive LVal : Nat → Type where
  | var {n : Nat} (x : Var n) : LVal n
  | fn {n : Nat} (f : FName) : LVal n
  | ctor {n : Nat} (c : CName) (args : LVals n) : LVal n
  /-- `λ^z̄ x̄. e`: `c` captured values `zs`, `k` parameters, and a body whose variables are
      the parameters (indices `< k`) and the captured values (indices `k + i`). -/
  | lam {n : Nat} (zs : LVals n) (c k : Nat) (body : LExpr (c + k)) : LVal n
/-- Lists of values. -/
inductive LVals : Nat → Type where
  | nil {n : Nat} : LVals n
  | cons {n : Nat} (v : LVal n) (vs : LVals n) : LVals n
/-- Expressions of `λfip` with at most `n` free variables. -/
inductive LExpr : Nat → Type where
  /-- the unboxed tuple `(v₁, …, vₖ)` -/
  | ret {n : Nat} (vs : LVals n) : LExpr n
  | app {n : Nat} (e1 e2 : LExpr n) : LExpr n
  | call {n : Nat} (f : FName) (e1 e2 : LExpr n) : LExpr n
  /-- `let x̄ = e₁ in e₂`, binding `k` variables -/
  | letIn {n : Nat} (k : Nat) (e1 : LExpr n) (e2 : LExpr (n + k)) : LExpr n
  /-- the non-destructive `match x {p ↦ e}` -/
  | «match» {n : Nat} (x : LVal n) (bs : LBranches n) : LExpr n
  | dup {n : Nat} (x : LVal n) (e : LExpr n) : LExpr n
  | drop {n : Nat} (x : LVal n) (e : LExpr n) : LExpr n
  /-- `dropru x; e`, where `k` is the size of `x` -/
  | dropru {n : Nat} (x : LVal n) (k : Nat) (e : LExpr n) : LExpr n
  | free {n : Nat} (k : Nat) (e : LExpr n) : LExpr n
  | alloc {n : Nat} (k : Nat) (e : LExpr n) : LExpr n
/-- The branches `Cᵢ x̄ᵢ ↦ eᵢ` of a match; the body of a branch binding `k` variables lives
    in the scope `n + k`. -/
inductive LBranches : Nat → Type where
  | nil {n : Nat} : LBranches n
  | cons {n : Nat} (c : CName) (k : Nat) (body : LExpr (n + k)) (rest : LBranches n) :
      LBranches n
end

instance {n : Nat} : Inhabited (LVal n) := ⟨.fn ""⟩

/-! ## Lists of values -/

namespace LVals

/-- The list of values. -/
def toList {n : Nat} : LVals n → List (LVal n)
  | .nil => []
  | .cons v vs => v :: vs.toList

/-- A list of values. -/
def ofList {n : Nat} : List (LVal n) → LVals n
  | [] => .nil
  | v :: vs => .cons v (ofList vs)

@[simp] theorem toList_nil {n : Nat} : (LVals.nil : LVals n).toList = [] := rfl
@[simp] theorem toList_cons {n : Nat} (v : LVal n) (vs : LVals n) :
    (LVals.cons v vs).toList = v :: vs.toList := rfl

@[simp] theorem toList_ofList {n : Nat} : ∀ vs : List (LVal n), (ofList vs).toList = vs
  | [] => rfl
  | v :: vs => by simp [ofList, toList_ofList vs]

@[simp] theorem ofList_toList {n : Nat} : ∀ vs : LVals n, ofList vs.toList = vs
  | .nil => rfl
  | .cons v vs => by simp [ofList, ofList_toList vs]

theorem toList_injective {n : Nat} : Function.Injective (toList (n := n)) := by
  intro a b h; rw [← ofList_toList a, h, ofList_toList]

theorem ofList_injective {n : Nat} : Function.Injective (ofList (n := n)) := by
  intro a b h; rw [← toList_ofList a, h, toList_ofList]

@[simp] theorem ofList_inj {n : Nat} {a b : List (LVal n)} : ofList a = ofList b ↔ a = b :=
  ofList_injective.eq_iff

/-- The number of values. -/
abbrev length {n : Nat} (vs : LVals n) : Nat := vs.toList.length

end LVals

/-! ## Branches -/

/-- A single branch `C x̄ ↦ e` binding `k` variables. -/
structure LBranch (n : Nat) where
  ctor : CName
  k : Nat
  body : LExpr (n + k)

/-- The branches of a match, as a list. -/
def LBranches.toList {n : Nat} : LBranches n → List (LBranch n)
  | .nil => []
  | .cons c k e bs => ⟨c, k, e⟩ :: bs.toList

@[simp] theorem LBranches.toList_nil {n : Nat} : (LBranches.nil : LBranches n).toList = [] := rfl
@[simp] theorem LBranches.toList_cons {n : Nat} (c : CName) (k : Nat) (e : LExpr (n + k))
    (bs : LBranches n) : (LBranches.cons c k e bs).toList = ⟨c, k, e⟩ :: bs.toList := rfl

/-- Find the branch for a constructor of the given arity. -/
def LBranches.find {n : Nat} (bs : LBranches n) (c : CName) (k : Nat) : Option (LBranch n) :=
  bs.toList.find? (fun b => b.ctor == c && b.k == k)

/-! ## Derived forms -/

/-- `dup x̄; e`. -/
def dups {n : Nat} : List (LVal n) → LExpr n → LExpr n
  | [], e => e
  | x :: xs, e => .dup x (dups xs e)

/-- `drop x̄; e` for the variables among `x̄`. -/
def drops {n : Nat} : List (LVal n) → LExpr n → LExpr n
  | [], e => e
  | .var x :: xs, e => .drop (.var x) (drops xs e)
  | _ :: xs, e => drops xs e

/-- The `k` variables bound by a binder, as values of the extended scope. -/
def bvals (n k : Nat) : List (LVal (n + k)) :=
  (List.finRange k).map fun j => .var (Var.newB j)

/-- The variables of scope `n`, as resources (each once). -/
def allCtx (n : Nat) : Ctx n :=
  (((List.finRange n).map fun i => Res.var (.bvar i)) : List (Res n))

/-- The resources bound by a binder of `k` variables (each owned once). -/
def bCtx (n k : Nat) : Ctx (n + k) :=
  (((List.finRange k).map fun j => Res.var (Var.newB j)) : List (Res (n + k)))

/-! ## Substitution

A substitution never enters the body of a lambda, which has its own scope: it acts on the
captured values. -/

mutual
/-- Apply a substitution to a value. -/
def LVal.subst {n m : Nat} (σ : Fin n → LVal m) : LVal n → LVal m
  | .var (.bvar i) => σ i
  | .var (.loc l) => .var (.loc l)
  | .fn f => .fn f
  | .ctor c vs => .ctor c (LVals.subst σ vs)
  | .lam zs c k b => .lam (LVals.subst σ zs) c k b
/-- Apply a substitution to a list of values. -/
def LVals.subst {n m : Nat} (σ : Fin n → LVal m) : LVals n → LVals m
  | .nil => .nil
  | .cons v vs => .cons (LVal.subst σ v) (LVals.subst σ vs)
end

@[simp] theorem LVals.toList_subst {n m : Nat} (σ : Fin n → LVal m) :
    ∀ vs : LVals n, (vs.subst σ).toList = vs.toList.map (LVal.subst σ)
  | .nil => rfl
  | .cons v vs => by simp [LVals.subst, LVals.toList_subst σ vs]

@[simp] theorem LVals.subst_ofList {n m : Nat} (σ : Fin n → LVal m) (vs : List (LVal n)) :
    (LVals.ofList vs).subst σ = LVals.ofList (vs.map (LVal.subst σ)) := by
  apply LVals.toList_injective; simp

/-- Weakening past `k` new innermost variables. -/
def LVal.shift {m : Nat} (k : Nat) (v : LVal m) : LVal (m + k) :=
  v.subst fun i => .var (.bvar ⟨k + i, by omega⟩)

/-- Push a substitution under `k` binders. -/
def LSubst.up {n m : Nat} (k : Nat) (σ : Fin n → LVal m) : Fin (n + k) → LVal (m + k) :=
  fun i => if h : i.val < k then .var (.bvar ⟨i, by omega⟩) else (σ ⟨i - k, by omega⟩).shift k

/-- `[x̄ := v̄]` for the `k` innermost variables of the scope `n + k`, the other variables
    being sent to `σ`. -/
def LSubst.inst {n m : Nat} (k : Nat) (vs : List (LVal m)) (σ : Fin n → LVal m) :
    Fin (n + k) → LVal m :=
  fun i => if hi : i.val < k then vs.getD i.val default else σ ⟨i - k, by omega⟩

/-- `[x̄ := v̄]` for a scope of `k` variables. -/
def LSubst.ofList {m : Nat} (k : Nat) (vs : List (LVal m)) : Fin k → LVal m :=
  fun i => vs.getD i.val default

mutual
/-- Apply a substitution to an expression. -/
def LExpr.subst {n m : Nat} (σ : Fin n → LVal m) : LExpr n → LExpr m
  | .ret vs => .ret (LVals.subst σ vs)
  | .app e1 e2 => .app (LExpr.subst σ e1) (LExpr.subst σ e2)
  | .call f e1 e2 => .call f (LExpr.subst σ e1) (LExpr.subst σ e2)
  | .letIn k e1 e2 => .letIn k (LExpr.subst σ e1) (LExpr.subst (LSubst.up k σ) e2)
  | .match x bs => .match (LVal.subst σ x) (LBranches.subst σ bs)
  | .dup x e => .dup (LVal.subst σ x) (LExpr.subst σ e)
  | .drop x e => .drop (LVal.subst σ x) (LExpr.subst σ e)
  | .dropru x k e => .dropru (LVal.subst σ x) k (LExpr.subst σ e)
  | .free k e => .free k (LExpr.subst σ e)
  | .alloc k e => .alloc k (LExpr.subst σ e)
/-- Apply a substitution to branches. -/
def LBranches.subst {n m : Nat} (σ : Fin n → LVal m) : LBranches n → LBranches m
  | .nil => .nil
  | .cons c k e bs => .cons c k (LExpr.subst (LSubst.up k σ) e) (LBranches.subst σ bs)
end

/-! ## Substituting closed values for locations -/

/-- A closed value, seen in any scope. -/
def LVal.weaken {n : Nat} (v : LVal 0) : LVal n := v.subst Fin.elim0

mutual
/-- Substitute closed values for locations in a value (not in the bodies of lambdas). -/
def LVal.substLoc {n : Nat} (σ : Nat → Option (LVal 0)) : LVal n → LVal n
  | .var (.loc l) => ((σ l).map LVal.weaken).getD (.var (.loc l))
  | .var (.bvar i) => .var (.bvar i)
  | .fn f => .fn f
  | .ctor c vs => .ctor c (LVals.substLoc σ vs)
  | .lam zs c k b => .lam (LVals.substLoc σ zs) c k b
/-- Substitute closed values for locations in a list of values. -/
def LVals.substLoc {n : Nat} (σ : Nat → Option (LVal 0)) : LVals n → LVals n
  | .nil => .nil
  | .cons v vs => .cons (LVal.substLoc σ v) (LVals.substLoc σ vs)
end

@[simp] theorem LVals.toList_substLoc {n : Nat} (σ : Nat → Option (LVal 0)) :
    ∀ vs : LVals n, (vs.substLoc σ).toList = vs.toList.map (LVal.substLoc σ)
  | .nil => rfl
  | .cons v vs => by simp [LVals.substLoc, LVals.toList_substLoc σ vs]

@[simp] theorem LVals.substLoc_ofList {n : Nat} (σ : Nat → Option (LVal 0)) (vs : List (LVal n)) :
    (LVals.ofList vs).substLoc σ = LVals.ofList (vs.map (LVal.substLoc σ)) := by
  apply LVals.toList_injective; simp

mutual
/-- Substitute closed values for locations in an expression. -/
def LExpr.substLoc {n : Nat} (σ : Nat → Option (LVal 0)) : LExpr n → LExpr n
  | .ret vs => .ret (LVals.substLoc σ vs)
  | .app e1 e2 => .app (LExpr.substLoc σ e1) (LExpr.substLoc σ e2)
  | .call f e1 e2 => .call f (LExpr.substLoc σ e1) (LExpr.substLoc σ e2)
  | .letIn k e1 e2 => .letIn k (LExpr.substLoc σ e1) (LExpr.substLoc σ e2)
  | .match x bs => .match (LVal.substLoc σ x) (LBranches.substLoc σ bs)
  | .dup x e => .dup (LVal.substLoc σ x) (LExpr.substLoc σ e)
  | .drop x e => .drop (LVal.substLoc σ x) (LExpr.substLoc σ e)
  | .dropru x k e => .dropru (LVal.substLoc σ x) k (LExpr.substLoc σ e)
  | .free k e => .free k (LExpr.substLoc σ e)
  | .alloc k e => .alloc k (LExpr.substLoc σ e)
/-- Substitute closed values for locations in branches. -/
def LBranches.substLoc {n : Nat} (σ : Nat → Option (LVal 0)) : LBranches n → LBranches n
  | .nil => .nil
  | .cons c k e bs => .cons c k (LExpr.substLoc σ e) (LBranches.substLoc σ bs)
end

/-! ## Locations

The locations occurring in a value or expression, outside the bodies of lambdas (which a
well-formed program never fills with locations). -/

mutual
/-- The locations of a value (with multiplicity). -/
def LVal.locs {n : Nat} : LVal n → List Nat
  | .var (.loc l) => [l]
  | .var (.bvar _) => []
  | .fn _ => []
  | .ctor _ vs => LVals.locs vs
  | .lam zs _ _ _ => LVals.locs zs
/-- The locations of a list of values. -/
def LVals.locs {n : Nat} : LVals n → List Nat
  | .nil => []
  | .cons v vs => LVal.locs v ++ LVals.locs vs
end

mutual
/-- The locations of an expression. -/
def LExpr.locs {n : Nat} : LExpr n → List Nat
  | .ret vs => LVals.locs vs
  | .app e1 e2 => LExpr.locs e1 ++ LExpr.locs e2
  | .call _ e1 e2 => LExpr.locs e1 ++ LExpr.locs e2
  | .letIn _ e1 e2 => LExpr.locs e1 ++ LExpr.locs e2
  | .match x bs => LVal.locs x ++ LBranches.locs bs
  | .dup x e => LVal.locs x ++ LExpr.locs e
  | .drop x e => LVal.locs x ++ LExpr.locs e
  | .dropru x _ e => LVal.locs x ++ LExpr.locs e
  | .free _ e => LExpr.locs e
  | .alloc _ e => LExpr.locs e
/-- The locations of branches. -/
def LBranches.locs {n : Nat} : LBranches n → List Nat
  | .nil => []
  | .cons _ _ e bs => LExpr.locs e ++ LBranches.locs bs
end

end FIP.Lam

namespace FIP.Lam

mutual
/-- The free variables (and locations) of a value, with multiplicity.  The free variables of
    a lambda are those of its captured values. -/
def LVal.fv {n : Nat} : LVal n → List (Var n)
  | .var x => [x]
  | .fn _ => []
  | .ctor _ vs => LVals.fv vs
  | .lam zs _ _ _ => LVals.fv zs
/-- The free variables of a list of values. -/
def LVals.fv {n : Nat} : LVals n → List (Var n)
  | .nil => []
  | .cons v vs => LVal.fv v ++ LVals.fv vs
end

/-- The free variables of a list of values. -/
def LVal.fvList {n : Nat} : List (LVal n) → List (Var n)
  | [] => []
  | v :: vs => LVal.fv v ++ LVal.fvList vs

theorem LVals.fv_eq {n : Nat} : ∀ vs : LVals n, vs.fv = LVal.fvList vs.toList
  | .nil => rfl
  | .cons v vs => by simp [LVals.fv, LVal.fvList, LVals.fv_eq vs]

end FIP.Lam

/- ══════════════════ PAPER sec. 5, 5.1, 5.2, App. E.1 END: Reference Counting with Borrowing and Unboxing; Elaborating borrowing; Heap semantics; Properties of Heaps ══════════════════ -/
