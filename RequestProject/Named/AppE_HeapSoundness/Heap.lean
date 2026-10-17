module

public import RequestProject.Named.AppD_TRMC.TRMC

@[expose] public section

/-!
# Reference counting with borrowing and unboxing: `λfip` and its heap semantics
(Section 5, Fig. 9, Fig. 10, Appendix E)

The `λfip` calculus extends the FBIP calculus with

* lambda expressions `λ^z̄ x̄. e` whose free variables `z̄` are written explicitly,
* `dup x; e`, which duplicates an owned (or borrowed) variable,
* `dropru x; e` ("drop reuse"), which drops `x` and yields a reuse credit `⋄k` of the
  size `k` of `x`,
* `alloc k; e`, which allocates a fresh reuse credit `⋄k`,

and replaces the destructive match by a *non-destructive* match on a variable whose
branches first duplicate the fields: `match x {Cᵢ x̄ᵢ ↦ dup x̄ᵢ; eᵢ}`.  In `dropru x; e`
the size `k` of `x` is recorded in the syntax (`LExpr.dropru x k e`), since our
expressions carry no types.

The *heap* extends a store with reference counts `n ≥ 1` and closures:
`H ::= ∅ | H, ⋄k | H, x ↦ⁿ φ` with `φ ::= C x̄ | λ^z̄ x̄. e`.

This file formalizes the syntax, the functional semantics, the typing rules of Fig. 9,
the heap semantics of Fig. 10 and the join `H₁ ⊗ H₂` of heaps (Appendix E.1).  The formal
statement of **Theorem 6** (soundness of the heap semantics) given below is false as stated
(heaps may bind program names); it is kept in a comment, and a counterexample is proved in
`RequestProject/AppE_HeapSoundness/HeapCex.lean`.  A corrected statement is proved as
`heap_sound_corrected` in `RequestProject/AppE_HeapSoundness/HeapTheorem.lean`.  We prove that the translation of a
destructive match into `λfip` is well-formed (`LWf.dmatch_translation`, Section 5).
-/

namespace FIPNamed.Lam

/-! ## Syntax (Fig. 9) -/

mutual
/-- Values of `λfip`: variables, top-level functions, constructors and lambdas
    `λ^z̄ x̄. e`. -/
inductive LVal where
  | var (x : Var)
  | fn (f : FName)
  | ctor (c : CName) (args : List LVal)
  /-- `λ^z̄ x̄. e`, where `z̄` are the free variables of `λx̄. e` -/
  | lam (zs : List LVal) (xs : List Binder) (body : LExpr)
/-- Expressions of `λfip`. -/
inductive LExpr where
  | ret (vs : List LVal)
  | app (e1 e2 : LExpr)
  | call (f : FName) (e1 e2 : LExpr)
  | letIn (xs : List Binder) (e1 e2 : LExpr)
  /-- the non-destructive `match x {p ↦ e}` -/
  | «match» (x : LVal) (bs : List LBranch)
  | dup (x : LVal) (e : LExpr)
  | drop (x : LVal) (e : LExpr)
  /-- `dropru x; e`, where `k` is the size of `x` -/
  | dropru (x : LVal) (k : Nat) (e : LExpr)
  | free (k : Nat) (e : LExpr)
  | alloc (k : Nat) (e : LExpr)
/-- A branch `C x̄ ↦ e`. -/
inductive LBranch where
  | mk (c : CName) (xs : List Binder) (body : LExpr)
end

namespace LBranch
def ctor : LBranch → CName | mk c _ _ => c
def binders : LBranch → List Binder | mk _ xs _ => xs
def body : LBranch → LExpr | mk _ _ e => e
end LBranch

/-- `dup x̄; e`. -/
def dups : List LVal → LExpr → LExpr
  | [], e => e
  | x :: xs, e => .dup x (dups xs e)

/-- Remove `n` leading `dup`s: the inverse of `dups`. -/
def undups : Nat → LExpr → LExpr
  | n + 1, .dup _ e => undups n e
  | _, e => e

theorem undups_dups : ∀ (xs : List LVal) (e : LExpr), undups xs.length (dups xs e) = e
  | [], e => by cases e <;> rfl
  | x :: xs, e => by simp only [List.length_cons, dups, undups]; exact undups_dups xs e

theorem undups_dups_of_length (xs : List LVal) (e : LExpr) {n : Nat} (h : xs.length = n) :
    undups n (dups xs e) = e := h ▸ undups_dups xs e

/-- `drop x̄; e` for the variables among `x̄`. -/
def drops : List LVal → LExpr → LExpr
  | [], e => e
  | .var x :: xs, e => .drop (.var x) (drops xs e)
  | _ :: xs, e => drops xs e

/-- The variables bound by binders, as values. -/
def Binder.vals (xs : List Binder) : List LVal := xs.map fun b => .var (.name b.name)

/-! ## Substitution and free variables -/

/-- A substitution of values for variables (names or locations). -/
abbrev LSubst := Var → Option LVal

/-- Substitution stops at binders. -/
def LSubst.remove (σ : LSubst) (xs : List Binder) : LSubst :=
  open Classical in fun y => if y ∈ Binder.vars xs then none else σ y

/-- The substitution `[x̄ := v̄]`. -/
def lzip (xs : List Binder) (vs : List LVal) : LSubst :=
  fun y => ((xs.map fun b => Var.name b.name).zip vs).lookup y

mutual
/-- Apply a substitution to a value. -/
def LVal.subst (σ : LSubst) : LVal → LVal
  | .var x => (σ x).getD (.var x)
  | .fn f => .fn f
  | .ctor c vs => .ctor c (LVal.substList σ vs)
  | .lam zs xs e => .lam (LVal.substList σ zs) xs (LExpr.subst (σ.remove xs) e)
/-- Apply a substitution to a list of values. -/
def LVal.substList (σ : LSubst) : List LVal → List LVal
  | [] => []
  | v :: vs => LVal.subst σ v :: LVal.substList σ vs
/-- Apply a substitution to an expression. -/
def LExpr.subst (σ : LSubst) : LExpr → LExpr
  | .ret vs => .ret (LVal.substList σ vs)
  | .app e1 e2 => .app (LExpr.subst σ e1) (LExpr.subst σ e2)
  | .call f e1 e2 => .call f (LExpr.subst σ e1) (LExpr.subst σ e2)
  | .letIn xs e1 e2 => .letIn xs (LExpr.subst σ e1) (LExpr.subst (σ.remove xs) e2)
  | .match x bs => .match (LVal.subst σ x) (LExpr.substB σ bs)
  | .dup x e => .dup (LVal.subst σ x) (LExpr.subst σ e)
  | .drop x e => .drop (LVal.subst σ x) (LExpr.subst σ e)
  | .dropru x k e => .dropru (LVal.subst σ x) k (LExpr.subst σ e)
  | .free k e => .free k (LExpr.subst σ e)
  | .alloc k e => .alloc k (LExpr.subst σ e)
/-- Apply a substitution to branches. -/
def LExpr.substB (σ : LSubst) : List LBranch → List LBranch
  | [] => []
  | .mk c xs e :: bs => .mk c xs (LExpr.subst (σ.remove xs) e) :: LExpr.substB σ bs
end

mutual
/-- The free variables of a value (with multiplicity).  The free variables of a lambda
    are its recorded variables `z̄`. -/
def LVal.fv : LVal → List Var
  | .var x => [x]
  | .fn _ => []
  | .ctor _ vs => LVal.fvList vs
  | .lam zs _ _ => LVal.fvList zs
/-- The free variables of a list of values. -/
def LVal.fvList : List LVal → List Var
  | [] => []
  | v :: vs => LVal.fv v ++ LVal.fvList vs
/-- The free variables of an expression (with multiplicity). -/
def LExpr.fv : LExpr → List Var
  | .ret vs => LVal.fvList vs
  | .app e1 e2 => LExpr.fv e1 ++ LExpr.fv e2
  | .call _ e1 e2 => LExpr.fv e1 ++ LExpr.fv e2
  | .letIn xs e1 e2 => LExpr.fv e1 ++ (LExpr.fv e2).filter (· ∉ Binder.vars xs)
  | .match x bs => LVal.fv x ++ LExpr.fvB bs
  | .dup x e => LVal.fv x ++ LExpr.fv e
  | .drop x e => LVal.fv x ++ LExpr.fv e
  | .dropru x _ e => LVal.fv x ++ LExpr.fv e
  | .free _ e => LExpr.fv e
  | .alloc _ e => LExpr.fv e
/-- The free variables of branches. -/
def LExpr.fvB : List LBranch → List Var
  | [] => []
  | .mk _ xs e :: bs => (LExpr.fv e).filter (· ∉ Binder.vars xs) ++ LExpr.fvB bs
end

/-! ## Functional semantics -/

/-- A top-level function `f(ȳ; x̄) = e` of `λfip`. -/
structure LFunDef where
  name : FName
  borrowed : List Binder
  owned : List Binder
  body : LExpr

/-- A signature of `λfip` functions. -/
abbrev LSig := List LFunDef

/-- Look up a function. -/
def LSig.lookup (sig : LSig) (f : FName) : Option LFunDef := sig.find? (·.name == f)

/-- Find the branch for a constructor of the given arity. -/
def lfindBranch (bs : List LBranch) (c : CName) (k : Nat) : Option LBranch :=
  bs.find? (fun b => b.ctor == c && b.binders.length == k)

/-- Evaluation contexts. -/
inductive LECtx where
  | hole
  | appL (E : LECtx) (e : LExpr)
  | appR (vs : List LVal) (E : LECtx)
  | callB (f : FName) (E : LECtx) (e : LExpr)
  | callO (f : FName) (vs : List LVal) (E : LECtx)
  | letIn (xs : List Binder) (E : LECtx) (e : LExpr)

/-- `E[e]`. -/
def LECtx.plug : LECtx → LExpr → LExpr
  | .hole, e => e
  | .appL E e2, e => .app (E.plug e) e2
  | .appR vs E, e => .app (.ret vs) (E.plug e)
  | .callB f E e2, e => .call f (E.plug e) e2
  | .callO f vs E, e => .call f (.ret vs) (E.plug e)
  | .letIn xs E e2, e => .letIn xs (E.plug e) e2

/-- Head reductions of `λfip` (Fig. 3 extended by Fig. 6 and Fig. 9): `dup`, `drop`,
    `dropru`, `free` and `alloc` have no effect in the functional semantics. -/
inductive LHead (sig : LSig) : LExpr → LExpr → Prop where
  | letIn (xs : List Binder) (vs : List LVal) (e : LExpr) : xs.length = vs.length →
      LHead sig (.letIn xs (.ret vs) e) (e.subst (lzip xs vs))
  | call (f : FName) (fd : LFunDef) (vs1 vs2 : List LVal) : sig.lookup f = some fd →
      fd.borrowed.length = vs1.length → fd.owned.length = vs2.length →
      LHead sig (.call f (.ret vs1) (.ret vs2))
        (fd.body.subst (lzip (fd.borrowed ++ fd.owned) (vs1 ++ vs2)))
  | appFn (f : FName) (fd : LFunDef) (vs : List LVal) : sig.lookup f = some fd →
      fd.borrowed = [] → fd.owned.length = vs.length →
      LHead sig (.app (.ret [.fn f]) (.ret vs)) (fd.body.subst (lzip fd.owned vs))
  /-- (*beta*) `(λ^z̄ x̄. e) v̄ ⟶ e[x̄ := v̄]` -/
  | beta (zs : List LVal) (xs : List Binder) (e : LExpr) (vs : List LVal) :
      xs.length = vs.length →
      LHead sig (.app (.ret [.lam zs xs e]) (.ret vs)) (e.subst (lzip xs vs))
  | «match» (c : CName) (vs : List LVal) (bs : List LBranch) (xs : List Binder) (e : LExpr) :
      lfindBranch bs c vs.length = some (.mk c xs e) →
      LHead sig (.match (.ctor c vs) bs) (e.subst (lzip xs vs))
  | dup (v : LVal) (e : LExpr) : LHead sig (.dup v e) e
  | drop (v : LVal) (e : LExpr) : LHead sig (.drop v e) e
  | dropru (v : LVal) (k : Nat) (e : LExpr) : LHead sig (.dropru v k e) e
  | free (k : Nat) (e : LExpr) : LHead sig (.free k e) e
  | alloc (k : Nat) (e : LExpr) : LHead sig (.alloc k e) e

/-- The functional semantics `e ⟼ e'`. -/
inductive LStep (sig : LSig) : LExpr → LExpr → Prop where
  | step (E : LECtx) {e e' : LExpr} : LHead sig e e' → LStep sig (E.plug e) (E.plug e')

/-- `⟼*`. -/
abbrev LSteps (sig : LSig) := Relation.ReflTransGen (LStep sig)

/-! ## Well-formed `λfip` expressions (Fig. 9)

The multiplicity of each variable in `Γ` is unconstrained: a variable may be owned
several times, once per reference. -/

/-- The owned environment `x̄` of binders. -/
def Binder.ctx (xs : List Binder) : Ctx := ((xs.map fun b => Res.var (.name b.name)) : List Res)

/-- The owned environment `z̄` of a list of variables. -/
def varCtx (zs : List Var) : Ctx := ((zs.map Res.var) : List Res)

/-- Binders are distinct and fresh for `Δ, Γ`. -/
def Binder.LFresh (xs : List Binder) (Δ : Finset Var) (Γ : Ctx) : Prop :=
  (xs.map (·.name)).Nodup ∧ ∀ b ∈ xs, Var.name b.name ∉ Δ ∧ Res.var (.name b.name) ∉ Γ

/-- A borrowed argument: a borrowed variable or a top-level function. -/
def LBorrowArg (funs : List FName) (Δ : Finset Var) : LVal → Prop
  | .var y => y ∈ Δ
  | .fn g => g ∈ funs
  | _ => False

mutual
/-- Well-formed values `Δ | Γ ⊢ v`. -/
inductive LWfVal (funs : List FName) : Finset Var → Ctx → LVal → Prop where
  /-- `var` -/
  | var {Δ} (x : Var) : LWfVal funs Δ {Res.var x} (.var x)
  /-- `atom` -/
  | atom {Δ} (c : CName) : LWfVal funs Δ 0 (.ctor c [])
  /-- `reuse`: `Δ | Γ₁, …, Γₖ, ⋄k ⊢ Cᵏ v₁ … vₖ` -/
  | reuse {Δ} (c : CName) (vs : List LVal) (Γ : Ctx) : vs ≠ [] →
      LWfVals funs Δ Γ vs → LWfVal funs Δ (Γ + {Res.credit vs.length}) (.ctor c vs)
  /-- `lam`: `Δ | z̄ ⊢ λ^z̄ x̄. e` if `∅ | z̄, x̄ ⊢ e` and `z̄ = fv(λx̄. e)` -/
  | lam {Δ} (zs : List Var) (xs : List Binder) (e : LExpr) :
      LWf funs ∅ (varCtx zs + Binder.ctx xs) e →
      (∀ y, y ∈ zs ↔ y ∈ e.fv ∧ y ∉ Binder.vars xs) →
      LWfVal funs Δ (varCtx zs) (.lam (zs.map .var) xs e)
/-- Well-formed lists of values. -/
inductive LWfVals (funs : List FName) : Finset Var → Ctx → List LVal → Prop where
  | nil {Δ} : LWfVals funs Δ 0 []
  | cons {Δ} (Γ₁ Γ₂ : Ctx) (v : LVal) (vs : List LVal) :
      LWfVal funs Δ Γ₁ v → LWfVals funs Δ Γ₂ vs → LWfVals funs Δ (Γ₁ + Γ₂) (v :: vs)
/-- Well-formed expressions `Δ | Γ ⊢ e` of `λfip`. -/
inductive LWf (funs : List FName) : Finset Var → Ctx → LExpr → Prop where
  /-- `tuple` -/
  | tuple {Δ Γ vs} : LWfVals funs Δ Γ vs → LWf funs Δ Γ (.ret vs)
  /-- `call` -/
  | call {Δ Γ} (f : FName) (ys : List LVal) (e : LExpr) : f ∈ funs →
      (∀ y ∈ ys, LBorrowArg funs Δ y) → LWf funs Δ Γ e → LWf funs Δ Γ (.call f (.ret ys) e)
  /-- `app`: `Δ | Γ₁, Γ₂ ⊢ e₁ e₂` -/
  | app {Δ} (Γ₁ Γ₂ : Ctx) (e₁ e₂ : LExpr) : LWf funs Δ Γ₁ e₁ → LWf funs Δ Γ₂ e₂ →
      LWf funs Δ (Γ₁ + Γ₂) (.app e₁ e₂)
  /-- `let` -/
  | letIn {Δ} (Γ₁ Γ₂ Γ₃ : Ctx) (xs : List Binder) (e₁ e₂ : LExpr) : Γ₂.OnlyVars →
      LWf funs (Δ ∪ Γ₂.vars.toFinset) Γ₁ e₁ → LWf funs Δ (Γ₂ + Γ₃ + Binder.ctx xs) e₂ →
      Binder.LFresh xs Δ (Γ₂ + Γ₃) → LWf funs Δ (Γ₁ + Γ₂ + Γ₃) (.letIn xs e₁ e₂)
  /-- `match`: `Δ | Γ ⊢ match x {Cᵢ x̄ᵢ ↦ dup x̄ᵢ; eᵢ}` for `x ∈ Δ, Γ` -/
  | «match» {Δ Γ} (x : Var) (bs : List LBranch) : (x ∈ Δ ∨ Res.var x ∈ Γ) →
      (∀ b ∈ bs, Binder.LFresh b.binders Δ Γ) →
      (es : LBranch → LExpr) → (∀ b ∈ bs, b.body = dups (Binder.vals b.binders) (es b)) →
      (∀ b ∈ bs, LWf funs Δ (Γ + Binder.ctx b.binders) (es b)) →
      LWf funs Δ Γ (.match (.var x) bs)
  /-- `dup`: `Δ | Γ ⊢ dup x; e` if `Δ | Γ, x ⊢ e` and `x ∈ Δ, Γ` -/
  | dup {Δ Γ e} (x : Var) : (x ∈ Δ ∨ Res.var x ∈ Γ) → LWf funs Δ (Γ + {Res.var x}) e →
      LWf funs Δ Γ (.dup (.var x) e)
  /-- `drop` -/
  | drop {Δ Γ e} (x : Var) : LWf funs Δ Γ e → LWf funs Δ (Γ + {Res.var x}) (.drop (.var x) e)
  /-- `dropru`: `Δ | Γ, x ⊢ dropru x; e` if `Δ | Γ, ⋄k ⊢ e` with `k = size(x)` -/
  | dropru {Δ Γ e} (x : Var) (k : Nat) : LWf funs Δ (Γ + {Res.credit k}) e →
      LWf funs Δ (Γ + {Res.var x}) (.dropru (.var x) k e)
  /-- `free` -/
  | free {Δ Γ e} (k : Nat) : 1 ≤ k → LWf funs Δ Γ e →
      LWf funs Δ (Γ + {Res.credit k}) (.free k e)
  /-- `alloc`: `Δ | Γ ⊢ alloc k; e` if `Δ | Γ, ⋄k ⊢ e` and `k ≥ 1` -/
  | alloc {Δ Γ e} (k : Nat) : 1 ≤ k → LWf funs Δ (Γ + {Res.credit k}) e →
      LWf funs Δ Γ (.alloc k e)
  /-- `empty` -/
  | empty {Δ Γ e} : LWf funs Δ Γ e → LWf funs Δ (Γ + {Res.credit 0}) e
end

/-- A well-formed `λfip` signature: `ȳ | x̄ ⊢ e` for each `f(ȳ; x̄) = e`. -/
def LSig.Wf (sig : LSig) : Prop :=
  ∀ fd ∈ sig, ((fd.borrowed ++ fd.owned).map (·.name)).Nodup ∧
    LWf (sig.map (·.name)) (Binder.vars fd.borrowed).toFinset (Binder.ctx fd.owned) fd.body

theorem LWf.dups {funs : List FName} {Δ : Finset Var} :
    ∀ (xs : List Var) {Γ : Ctx} {e : LExpr}, (∀ x ∈ xs, x ∈ Δ ∨ Res.var x ∈ Γ) →
      LWf funs Δ (Γ + varCtx xs) e → LWf funs Δ Γ (FIPNamed.Lam.dups (xs.map .var) e)
  | [], Γ, e, _, h => by simpa [varCtx, FIPNamed.Lam.dups] using h
  | x :: xs, Γ, e, hx, h => by
    simp only [List.map_cons, FIPNamed.Lam.dups]
    refine LWf.dup x (hx x (List.mem_cons_self ..)) (LWf.dups xs ?_ ?_)
    · intro y hy
      rcases hx y (List.mem_cons_of_mem _ hy) with h' | h'
      · exact .inl h'
      · exact .inr (Multiset.mem_add.mpr (.inl h'))
    · have : Γ + varCtx (x :: xs) = Γ + {Res.var x} + varCtx xs := by
        simp [varCtx, Multiset.singleton_add, add_assoc]
      rw [← this]; exact h

/-- **The translation of `match!`** (Section 5).  If the branches of a destructive match
    `match! x {Cᵢ x̄ᵢ ↦ eᵢ}` are well-formed in the FIPNamed style, `Δ | Γ, x̄ᵢ, ⋄k ⊢ eᵢ`, then
    its translation `match x {Cᵢ x̄ᵢ ↦ dup x̄ᵢ; dropru x; eᵢ}` is well-formed in `λfip`:
    `Δ | Γ, x ⊢ match x {…}`. -/
theorem LWf.dmatch_translation {funs : List FName} {Δ : Finset Var} {Γ : Ctx} (x : Var)
    (bs : List LBranch)
    (hfr : ∀ b ∈ bs, Binder.LFresh b.binders Δ (Γ + {Res.var x}))
    (hbs : ∀ b ∈ bs,
      LWf funs Δ (Γ + Binder.ctx b.binders + {Res.credit b.binders.length}) b.body) :
    LWf funs Δ (Γ + {Res.var x})
      (.match (.var x) (bs.map fun b => .mk b.ctor b.binders
        (FIPNamed.Lam.dups (Binder.vals b.binders) (.dropru (.var x) b.binders.length b.body)))) := by
  refine LWf.match x _ (.inr (Multiset.mem_add.mpr (.inr (Multiset.mem_singleton_self _))))
    ?_ (fun b => undups b.binders.length b.body) ?_ ?_
  · intro b' hb'
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hb'
    exact hfr b hb
  · intro b' hb'
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hb'
    have hl : (Binder.vals b.binders).length = b.binders.length := by simp [Binder.vals]
    show FIPNamed.Lam.dups (Binder.vals b.binders) (.dropru (.var x) b.binders.length b.body) =
      FIPNamed.Lam.dups (Binder.vals b.binders) (undups b.binders.length
        (FIPNamed.Lam.dups (Binder.vals b.binders) (.dropru (.var x) b.binders.length b.body)))
    rw [undups_dups_of_length _ _ hl]
  · intro b' hb'
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hb'
    have hl : (Binder.vals b.binders).length = b.binders.length := by simp [Binder.vals]
    show LWf funs Δ (Γ + {Res.var x} + Binder.ctx b.binders) (undups b.binders.length
        (FIPNamed.Lam.dups (Binder.vals b.binders) (.dropru (.var x) b.binders.length b.body)))
    rw [undups_dups_of_length _ _ hl]
    have h := LWf.dropru (Γ := Γ + Binder.ctx b.binders) x b.binders.length (hbs b hb)
    have : Γ + Binder.ctx b.binders + {Res.var x} = Γ + {Res.var x} + Binder.ctx b.binders := by
      abel
    rw [← this]; exact h

/-! ## Heaps (Fig. 10) -/

/-- The object `φ ::= C x̄ | λ^z̄ x̄. e` bound in a heap cell. -/
inductive HObj where
  | con (c : CName) (args : List LVal)
  | clo (zs : List LVal) (xs : List Binder) (body : LExpr)

/-- The free variables of an object. -/
def HObj.fv : HObj → List Var
  | .con _ args => LVal.fvList args
  | .clo zs _ _ => LVal.fvList zs

/-- A heap cell: `x ↦ⁿ φ` with reference count `n ≥ 1`, or a reuse credit `⋄k`. -/
inductive HCell where
  | bind (x : Var) (n : Nat) (o : HObj)
  | credit (k : Nat)

/-- A heap. -/
abbrev Heap := Multiset HCell

namespace Heap

/-- `dom(H)`. -/
def dom (H : Heap) : Multiset Var :=
  H.bind fun | .bind x _ _ => {x} | .credit _ => 0

/-- `fv(rng(H))`, with multiplicity. -/
def rngFv (H : Heap) : Multiset Var :=
  H.bind fun | .bind _ _ o => (o.fv : Multiset Var) | .credit _ => 0

/-- A heap is *sound* if each location is bound once, all reference counts are
    positive, and the free variables of its objects are bound. -/
def Sound (H : Heap) : Prop :=
  H.dom.Nodup ∧ (∀ x n o, HCell.bind x n o ∈ H → 1 ≤ n) ∧ ∀ x ∈ H.rngFv, x ∈ H.dom

/-- A heap is *linear* if it is sound and the reference count of each cell accounts at
    least for the references from the heap itself. -/
def Linear (H : Heap) : Prop :=
  H.Sound ∧ ∀ x n o, HCell.bind x n o ∈ H → H.rngFv.count x ≤ n

/-- `roots(H)`: each location as often as its reference count exceeds its references
    from the heap, and the non-empty reuse credits. -/
noncomputable def roots (H : Heap) : Ctx :=
  open Classical in
  H.bind fun
    | .bind x n _ => Multiset.replicate (n - H.rngFv.count x) (Res.var x)
    | .credit k => if k = 0 then 0 else {Res.credit k}

/-- The object bound to a location, if any. -/
noncomputable def lookup (H : Heap) (x : Var) : Option HObj :=
  open Classical in
  if h : ∃ p : Nat × HObj, HCell.bind x p.1 p.2 ∈ H then some h.choose.2 else none

/-- Read a value from the heap, following at most `n` bindings (closures are read back
    into lambdas). -/
noncomputable def readN (H : Heap) : Nat → LVal → LVal
  | 0, v => v
  | n + 1, .var x =>
    match H.lookup x with
    | some (.con c as) => .ctor c (as.map (readN H n))
    | some (.clo zs xs b) => .lam (zs.map (readN H n)) xs
        (b.subst fun y => match y with
          | .loc _ => if H.lookup y = none then none else some (readN H n (.var y))
          | .name _ => none)
    | none => .var x
  | n + 1, .ctor c vs => .ctor c (vs.map (readN H n))
  | n + 1, .lam zs xs b => .lam (zs.map (readN H n)) xs
      (b.subst fun y => match y with
        | .loc _ => if H.lookup y = none then none else some (readN H n (.var y))
        | .name _ => none)
  | _ + 1, v => v

/-- `[H]v`, with fuel sufficient for the values in a sound acyclic heap. -/
noncomputable def read (H : Heap) (v : LVal) : LVal :=
  H.readN (Multiset.card H + sizeOf v + 1) v

/-- `[H]e`: substitute the value of every location bound in `H`. -/
noncomputable def substE (H : Heap) (e : LExpr) : LExpr :=
  e.subst fun y => match y with
    | .loc _ => if H.lookup y = none then none else some (H.read (.var y))
    | .name _ => none

/-- Decrement the reference counts of the variables `zs` (once per occurrence). -/
def decr (zs : List Var) (H : Heap) : Heap :=
  H.map fun | .bind x n o => .bind x (n - zs.count x) o | .credit k => .credit k

end Heap

/-- The join `H₁ ⊗ H₂` of heaps (Appendix E.1):
```
∅ ⊗ H₂ = H₂
H₁, ⋄k ⊗ H₂ = H₁ ⊗ H₂, ⋄k
H₁, x ↦ⁿ v ⊗ H₂ = H₁ ⊗ H₂, x ↦ⁿ v                           iff x ∉ dom(H₂)
H₁, x ↦ⁿ v ⊗ H₂, x ↦ᵐ v, z̄ ↦ᵏ⁺¹ w̄ = H₁ ⊗ H₂, x ↦ⁿ⁺ᵐ v, z̄ ↦ᵏ w̄   iff z̄ = fv(v)
```
In the last case the reference counts of the children `z̄` of `v` are decremented once per
occurrence, since `v` is now shared. -/
inductive HJoin : Heap → Heap → Heap → Prop where
  | nil (H₂ : Heap) : HJoin 0 H₂ H₂
  | credit {H₁ H₂ H : Heap} (k : Nat) : HJoin H₁ ({HCell.credit k} + H₂) H →
      HJoin ({HCell.credit k} + H₁) H₂ H
  | fresh {H₁ H₂ H : Heap} (x : Var) (n : Nat) (o : HObj) : x ∉ H₂.dom →
      HJoin H₁ ({HCell.bind x n o} + H₂) H → HJoin ({HCell.bind x n o} + H₁) H₂ H
  | share {H₁ H₂ H : Heap} (x : Var) (n m : Nat) (o : HObj) :
      (∀ z ∈ o.fv, ∃ k p, HCell.bind z k p ∈ H₂ ∧ o.fv.count z < k) →
      HJoin H₁ ({HCell.bind x (n + m) o} + Heap.decr o.fv H₂) H →
      HJoin ({HCell.bind x n o} + H₁) ({HCell.bind x m o} + H₂) H

/-! ## Heap semantics (Fig. 10) -/

/-- Atomic values: variables and top-level functions. -/
def LVal.Atomic : LVal → Prop
  | .var _ => True
  | .fn _ => True
  | _ => False

/-- Head reductions of the heap semantics on expressions. -/
inductive HHead (sig : LSig) : Heap → LExpr → Heap → LExpr → Prop where
  | letIn (H : Heap) (xs : List Binder) (as : List LVal) (e : LExpr) :
      (∀ a ∈ as, a.Atomic) → xs.length = as.length →
      HHead sig H (.letIn xs (.ret as) e) H (e.subst (lzip xs as))
  | call (H : Heap) (f : FName) (fd : LFunDef) (as1 as2 : List LVal) :
      sig.lookup f = some fd → (∀ a ∈ as1 ++ as2, a.Atomic) →
      fd.borrowed.length = as1.length → fd.owned.length = as2.length →
      HHead sig H (.call f (.ret as1) (.ret as2)) H
        (fd.body.subst (lzip (fd.borrowed ++ fd.owned) (as1 ++ as2)))
  | appFn (H : Heap) (f : FName) (fd : LFunDef) (as : List LVal) :
      sig.lookup f = some fd → fd.borrowed = [] → (∀ a ∈ as, a.Atomic) →
      fd.owned.length = as.length →
      HHead sig H (.app (.ret [.fn f]) (.ret as)) H (fd.body.subst (lzip fd.owned as))
  /-- (*app_h*) `H | y ā ⟶ₕ H | dup z̄; drop y; e[x̄ := ā]` with `y ↦ⁿ λ^z̄ x̄. e ∈ H` -/
  | app (H : Heap) (y : Var) (n : Nat) (zs : List LVal) (xs : List Binder) (e : LExpr)
      (as : List LVal) : HCell.bind y n (.clo zs xs e) ∈ H → (∀ a ∈ as, a.Atomic) →
      xs.length = as.length →
      HHead sig H (.app (.ret [.var y]) (.ret as)) H
        (dups zs (.drop (.var y) (e.subst (lzip xs as))))
  /-- (*match_h*) `H | match x {p ↦ e} ⟶ₕ H | eᵢ[x̄ := z̄]` with `x ↦ⁿ C z̄ ∈ H` -/
  | «match» (H : Heap) (x : Var) (n : Nat) (c : CName) (zs : List LVal) (bs : List LBranch)
      (xs : List Binder) (e : LExpr) : HCell.bind x n (.con c zs) ∈ H →
      lfindBranch bs c zs.length = some (.mk c xs e) →
      HHead sig H (.match (.var x) bs) H (e.subst (lzip xs zs))
  /-- (*dup_h*) `H, x ↦ⁿ φ | dup x; e ⟶ₕ H, x ↦ⁿ⁺¹ φ | e` -/
  | dup (H : Heap) (x : Var) (n : Nat) (o : HObj) (e : LExpr) :
      HHead sig ({HCell.bind x n o} + H) (.dup (.var x) e) ({HCell.bind x (n + 1) o} + H) e
  /-- (*drop_h*) `H, x ↦ⁿ⁺¹ φ | drop x; e ⟶ₕ H, x ↦ⁿ φ | e` for `n ≥ 1` -/
  | drop (H : Heap) (x : Var) (n : Nat) (o : HObj) (e : LExpr) :
      HHead sig ({HCell.bind x (n + 2) o} + H) (.drop (.var x) e)
        ({HCell.bind x (n + 1) o} + H) e
  /-- (*dcon_h*) `H, x ↦¹ C z̄ | drop x; e ⟶ₕ H | drop z̄; e` -/
  | dcon (H : Heap) (x : Var) (c : CName) (zs : List LVal) (e : LExpr) :
      HHead sig ({HCell.bind x 1 (.con c zs)} + H) (.drop (.var x) e) H (drops zs e)
  /-- (*dlam_h*) `H, x ↦¹ λ^z̄ x̄. e' | drop x; e ⟶ₕ H | drop z̄; e` -/
  | dlam (H : Heap) (x : Var) (zs : List LVal) (xs : List Binder) (b e : LExpr) :
      HHead sig ({HCell.bind x 1 (.clo zs xs b)} + H) (.drop (.var x) e) H (drops zs e)
  /-- (*dropru_h*) `H, x ↦ⁿ⁺¹ Cᵏ z̄ | dropru x; e ⟶ₕ H, x ↦ⁿ Cᵏ z̄, ⋄k | e` for `n ≥ 1`:
      the cell is shared, so a fresh reuse credit is allocated -/
  | dropru (H : Heap) (x : Var) (n : Nat) (c : CName) (zs : List LVal) (e : LExpr) :
      HHead sig ({HCell.bind x (n + 2) (.con c zs)} + H) (.dropru (.var x) zs.length e)
        ({HCell.bind x (n + 1) (.con c zs)} + {HCell.credit zs.length} + H) e
  /-- (*dconru_h*) `H, x ↦¹ Cᵏ z̄ | dropru x; e ⟶ₕ H, ⋄k | drop z̄; e`: the cell is
      unique and becomes a reuse credit -/
  | dconru (H : Heap) (x : Var) (c : CName) (zs : List LVal) (e : LExpr) :
      HHead sig ({HCell.bind x 1 (.con c zs)} + H) (.dropru (.var x) zs.length e)
        ({HCell.credit zs.length} + H) (drops zs e)
  /-- (*free_h*) `H, ⋄k | free k; e ⟶ₕ H | e` -/
  | free (H : Heap) (k : Nat) (e : LExpr) :
      HHead sig ({HCell.credit k} + H) (.free k e) H e
  /-- (*alloc_h*) `H | alloc k; e ⟶ₕ H, ⋄k | e` -/
  | alloc (H : Heap) (k : Nat) (e : LExpr) :
      HHead sig H (.alloc k e) ({HCell.credit k} + H) e

/-- Reductions of the heap semantics on values: allocation of constructors (reusing a
    credit) and of closures (*lam_h*). -/
inductive HValHead : Heap → LVal → Heap → LVal → Prop where
  | reuse (H : Heap) (c : CName) (as : List LVal) (x : Nat) : as ≠ [] →
      (∀ a ∈ as, a.Atomic) → Var.loc x ∉ H.dom →
      HValHead ({HCell.credit as.length} + H) (.ctor c as)
        ({HCell.bind (.loc x) 1 (.con c as)} + H) (.var (.loc x))
  | atom (H : Heap) (c : CName) (x : Nat) : Var.loc x ∉ H.dom →
      HValHead H (.ctor c []) ({HCell.bind (.loc x) 1 (.con c [])} + H) (.var (.loc x))
  /-- (*lam_h*) `H | λ^z̄ x̄. e ⟶ₕ H, x ↦¹ λ^z̄ x̄. e | x` -/
  | lam (H : Heap) (zs : List LVal) (xs : List Binder) (e : LExpr) (x : Nat) :
      (∀ a ∈ zs, a.Atomic) → Var.loc x ∉ H.dom →
      HValHead H (.lam zs xs e) ({HCell.bind (.loc x) 1 (.clo zs xs e)} + H) (.var (.loc x))

/-- Value contexts: the components of a tuple and the arguments of a constructor are
    evaluated from left to right. -/
inductive LVCtx where
  | hole
  | ctor (c : CName) (done : List LVal) (V : LVCtx) (rest : List LVal)

/-- Plug a value into a value context. -/
def LVCtx.plug : LVCtx → LVal → LVal
  | .hole, v => v
  | .ctor c done V rest, v => .ctor c (done ++ V.plug v :: rest)

/-- The already evaluated arguments of a value context are atomic. -/
def LVCtx.Ok : LVCtx → Prop
  | .hole => True
  | .ctor _ done V _ => (∀ a ∈ done, a.Atomic) ∧ V.Ok

/-- The heap semantics `H | e ⟼ₕ H' | e'`. -/
inductive HStep (sig : LSig) : Heap → LExpr → Heap → LExpr → Prop where
  | head (E : LECtx) {H H' : Heap} {e e' : LExpr} :
      HHead sig H e H' e' → HStep sig H (E.plug e) H' (E.plug e')
  | val (E : LECtx) (done : List LVal) (V : LVCtx) (rest : List LVal) {H H' : Heap}
      {v v' : LVal} : (∀ a ∈ done, a.Atomic) → V.Ok → HValHead H v H' v' →
      HStep sig H (E.plug (.ret (done ++ V.plug v :: rest)))
        H' (E.plug (.ret (done ++ V.plug v' :: rest)))

/-- `⟼*ₕ`. -/
inductive HSteps (sig : LSig) : Heap → LExpr → Heap → LExpr → Prop where
  | refl (H : Heap) (e : LExpr) : HSteps sig H e H e
  | tail {H₁ H₂ H₃ : Heap} {e₁ e₂ e₃ : LExpr} :
      HSteps sig H₁ e₁ H₂ e₂ → HStep sig H₂ e₂ H₃ e₃ → HSteps sig H₁ e₁ H₃ e₃

/-! ## Basic properties -/

/-- Joining with the empty heap (Lemma 58, existence of a unit). -/
theorem HJoin.zero_left (H : Heap) : HJoin 0 H H := .nil H

/-- **Lemma 61** (dupping joins a root): a `dup` step adds a root. -/
theorem roots_dup (H : Heap) (x : Var) (n : Nat) (o : HObj) (hx : x ∉ o.fv)
    (hH : x ∉ H.rngFv) :
    Heap.roots ({HCell.bind x (n + 1) o} + H) =
      Heap.roots ({HCell.bind x n o} + H) + {Res.var x} := by
  classical
  have hr : ∀ m, Heap.rngFv ({HCell.bind x m o} + H) = (o.fv : Multiset Var) + H.rngFv := by
    intro m; simp [Heap.rngFv]
  have hc : (Heap.rngFv ({HCell.bind x n o} + H)).count x = 0 := by
    rw [hr]; simp [Multiset.count_eq_zero_of_notMem hH, List.count_eq_zero_of_not_mem hx]
  unfold Heap.roots
  rw [hr (n + 1), hr n, Multiset.add_bind, Multiset.add_bind, Multiset.singleton_bind,
    Multiset.singleton_bind]
  rw [hr] at hc
  dsimp only
  rw [hc, Nat.sub_zero, Nat.sub_zero, Multiset.replicate_succ, ← Multiset.singleton_add]
  abel

/-! The formal statement of Theorem 6 below is kept commented out: it is **false**, for the
same reason as the first statement of Theorem 1: it allows heaps to bind program names
(`Var.name`), while `[H]e` only substitutes locations.  See `not_heapSoundClaim` in
`RequestProject/AppE_HeapSoundness/HeapCex.lean`.  The corrected statement `heap_sound_corrected`
(`RequestProject/AppE_HeapSoundness/HeapTheorem.lean`) requires, as `store_sound` does for Theorem 1,
heaps of the paper's shape (locations bound to objects over locations) and expresses `[H]`
as a substitution of closed values for locations; it also requires admissible expressions
(`LExpr.Adm`, see `RequestProject/AppE_HeapSoundness/HeapAdmCex.lean` for why). -/

/-
/-- **Theorem 6** (the heap semantics is sound for well-formed Perceus programs).
    If `Δ | Γ ⊢ e` and given heaps `H₁, H₂` with `Δ ⊆ dom(H₁)`, `H₁` sound, `Γ = roots(H₂)`
    and `H₂` linear, then `[H₁ ⊗ H₂]e ⟼* v̄` implies `H₁ ⊗ H₂ | e ⟼*ₕ H₁ ⊗ H₃ | x̄` where
    `[H₃]x̄ = v̄`, `x̄ = roots(H₃)` and `H₃` is linear. -/
theorem heap_sound {sig : LSig} (hsig : sig.Wf) {Δ : Finset Var} {Γ : Ctx} {e : LExpr}
    (h : LWf (sig.map (·.name)) Δ Γ e) {H₁ H₂ H : Heap} (hj : HJoin H₁ H₂ H)
    (hΔ : ∀ x ∈ Δ, x ∈ H₁.dom) (hH₁ : H₁.Sound) (hΓ : Γ = H₂.roots) (hH₂ : H₂.Linear)
    {vs : List LVal} (hev : LSteps sig (H.substE e) (.ret vs)) :
    ∃ (H₃ H' : Heap) (xs : List Var), HJoin H₁ H₃ H' ∧
      HSteps sig H e H' (.ret (xs.map .var)) ∧
      xs.map (fun x => H₃.read (.var x)) = vs ∧
      H₃.roots = (xs : Multiset Var).map Res.var ∧ H₃.Linear := by
  sorry
-/

end FIPNamed.Lam
