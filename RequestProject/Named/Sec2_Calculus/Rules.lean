module

public import RequestProject.Named.Sec2_Calculus.Semantics

@[expose] public section

/-!
# The FIPNamed calculus: well-formed fully in-place expressions (Fig. 4, 6, 7)

`Wf cfg U Δ Γ e` is the judgment `Δ | Γ ⊢ e` of the paper:

* `Δ` is the *borrowed* environment (a set of variables),
* `Γ` is the *owned* environment, a multiset of owned variables, reuse credits `⋄k`
  and allocation credits `⋄` (Fig. 7),
* `U` is the set of *scalar* variables (extension for KokaNamed value types; empty in the
  paper's calculus),
* `cfg` records whether deallocation is allowed (FBIP, Fig. 6), which top-level
  functions may be called, and their allocation budgets `fip(n)` (Fig. 7).

The rules are those of Fig. 4 (`var`, `atom`, `tuple`, `reuse`, `call`, `let`, `bapp`,
`bmatch`, `empty`, `dmatch!`), Fig. 6 (`drop`, `free`) and Fig. 7 (`inst`, `weaken`
and the modified `call`), plus three rules for scalars (`svar`, `lit`, `prim`).
-/

namespace FIPNamed

/-- Resources of the owned environment `Γ ::= ∅ | Γ, x | Γ, ⋄k | Γ, ⋄`. -/
inductive Res where
  /-- an owned variable `x` -/
  | var (x : Var)
  /-- a reuse credit `⋄k` of size `k` -/
  | credit (k : Nat)
  /-- an allocation credit `⋄` (Fig. 7) -/
  | alloc
  deriving DecidableEq, Repr

/-- An owned environment. -/
abbrev Ctx := Multiset Res

/-- The owned variables of an environment. -/
def Ctx.vars (Γ : Ctx) : Multiset Var :=
  Γ.filterMap (fun r => match r with | .var x => some x | _ => none)

/-- An environment consisting only of variables (no credits), as required for the
    borrowed part `Γ₂` of the `let` rule. -/
def Ctx.OnlyVars (Γ : Ctx) : Prop := ∀ r ∈ Γ, ∃ x, r = .var x

/-- The resources bound by the non-scalar binders of a pattern or let. -/
def Binder.owned (xs : List Binder) : Ctx :=
  ((xs.filter (fun b => !b.scalar)).map (fun b => Res.var (.name b.name)) : List Res)

/-- The scalar variables bound by a list of binders. -/
def Binder.scalars (xs : List Binder) : Finset Var :=
  ((xs.filter (fun b => b.scalar)).map (fun b => Var.name b.name)).toFinset

/-- The non-scalar variables bound by a list of binders, as a set. -/
def Binder.ownedSet (xs : List Binder) : Finset Var :=
  ((xs.filter (fun b => !b.scalar)).map (fun b => Var.name b.name)).toFinset

/-- The binders are distinct and fresh for the given environments (`x̄ ∉ Δ, Γ`). -/
def Binder.Fresh (xs : List Binder) (U Δ : Finset Var) (Γ : Ctx) : Prop :=
  (xs.map (·.name)).Nodup ∧
  ∀ b ∈ xs, Var.name b.name ∉ U ∧ Var.name b.name ∉ Δ ∧ Res.var (.name b.name) ∉ Γ

/-- The configuration of the calculus. -/
structure Cfg where
  /-- whether deallocation (`drop`, `free`; the FBIP calculus of Fig. 6) is allowed -/
  fbip : Bool := false
  /-- the top-level functions that may be called (`dom(Σ)`) -/
  funs : List FName
  /-- the allocation budget `n` of each function annotated `fip(n)` (Fig. 7) -/
  budget : FName → Nat := fun _ => 0

/-- A borrowed argument of a call: a borrowed (or scalar) variable, or a top-level
    function `f ∈ dom(Σ)` (premise `ȳ ∈ Δ, dom(Σ)` of rule `call`). -/
def BorrowArg (cfg : Cfg) (U Δ : Finset Var) : Val → Prop
  | .var y => y ∈ Δ ∨ y ∈ U
  | .fn g => g ∈ cfg.funs
  | _ => False

/-- The allocation credits needed to pass a function as an argument (Fig. 7). -/
def fnBudget (cfg : Cfg) : Val → Nat
  | .fn g => cfg.budget g
  | _ => 0

/-- An argument of a primitive operation: a borrowed or scalar variable, or a literal. -/
def ScalarArg (U Δ : Finset Var) : Val → Prop
  | .var y => y ∈ Δ ∨ y ∈ U
  | .lit _ => True
  | _ => False

mutual
/-- Well-formed values `Δ | Γ ⊢ v` (rules `var`, `atom`, `reuse`, and the scalar rules
    `svar` and `lit`). -/
inductive WfVal (U Δ : Finset Var) : Ctx → Val → Prop where
  /-- `Δ | x ⊢ x` -/
  | var (x : Var) : WfVal U Δ {Res.var x} (.var x)
  /-- a scalar variable may be used freely (extension) -/
  | svar (x : Var) : x ∈ U → WfVal U Δ 0 (.var x)
  /-- `Δ | ∅ ⊢ C` -/
  | atom (c : CName) : WfVal U Δ 0 (.ctor c [])
  /-- a scalar literal (extension) -/
  | lit (n : Int) : WfVal U Δ 0 (.lit n)
  /-- `Δ | Γ₁, ..., Γₖ, ⋄k ⊢ Cᵏ v₁ ... vₖ` for `k ≥ 1` -/
  | reuse (c : CName) (vs : List Val) (Γ : Ctx) :
      vs ≠ [] → WfVals U Δ Γ vs → WfVal U Δ (Γ + {Res.credit vs.length}) (.ctor c vs)
/-- Well-formed lists of values, splitting the owned environment. -/
inductive WfVals (U Δ : Finset Var) : Ctx → List Val → Prop where
  | nil : WfVals U Δ 0 []
  | cons (Γ₁ Γ₂ : Ctx) (v : Val) (vs : List Val) :
      WfVal U Δ Γ₁ v → WfVals U Δ Γ₂ vs → WfVals U Δ (Γ₁ + Γ₂) (v :: vs)
end

/-- Well-formed FIPNamed expressions `Δ | Γ ⊢ e` (Fig. 4, 6, 7). -/
inductive Wf (cfg : Cfg) : Finset Var → Finset Var → Ctx → Expr → Prop where
  /-- `tuple`: `Δ | Γ₁, ..., Γₙ ⊢ (v₁, ..., vₙ)` -/
  | tuple {U Δ Γ vs} : WfVals U Δ Γ vs → Wf cfg U Δ Γ (.ret vs)
  /-- `call` (with the allocation credits of Fig. 7):
      `Δ | Γ, ⋄ⁿ⁺ⁿ' ⊢ f(ȳ; e)` -/
  | call {U Δ Γ} (f : FName) (ys : List Val) (e : Expr) :
      f ∈ cfg.funs → (∀ y ∈ ys, BorrowArg cfg U Δ y) → Wf cfg U Δ Γ e →
      Wf cfg U Δ
        (Γ + Multiset.replicate (cfg.budget f + (ys.map (fnBudget cfg)).sum) Res.alloc)
        (.call f (.ret ys) e)
  /-- `bapp`: `Δ | Γ ⊢ y e` for a borrowed function `y ∈ Δ` -/
  | bapp {U Δ Γ} (y : Var) (e : Expr) :
      y ∈ Δ → Wf cfg U Δ Γ e → Wf cfg U Δ Γ (.app (.var y) e)
  /-- `(f) e` for a top-level function `f ∈ dom(Σ)`, paying its allocation budget.  This
      is the instance of `bapp` obtained when a top-level function has been substituted
      for the borrowed variable `y` (the paper allows `ȳ ∈ Δ, dom(Σ)`). -/
  | fapp {U Δ Γ} (f : FName) (e : Expr) :
      f ∈ cfg.funs → Wf cfg U Δ Γ e →
      Wf cfg U Δ (Γ + Multiset.replicate (cfg.budget f) Res.alloc) (.app (.val (.fn f)) e)
  /-- `let`: `Δ | Γ₁, Γ₂, Γ₃ ⊢ let x̄ = e₁ in e₂` where `Γ₂` is borrowed in `e₁` -/
  | letIn {U Δ} (Γ₁ Γ₂ Γ₃ : Ctx) (xs : List Binder) (e₁ e₂ : Expr) :
      Γ₂.OnlyVars →
      Wf cfg U (Δ ∪ Γ₂.vars.toFinset) Γ₁ e₁ →
      Wf cfg (U ∪ Binder.scalars xs) Δ (Γ₂ + Γ₃ + Binder.owned xs) e₂ →
      Binder.Fresh xs U Δ (Γ₂ + Γ₃) →
      Wf cfg U Δ (Γ₁ + Γ₂ + Γ₃) (.letIn xs e₁ e₂)
  /-- `bmatch`: matching on a borrowed (or scalar) variable -/
  | bmatch {U Δ Γ} (y : Var) (bs : List Branch) :
      (y ∈ Δ ∨ y ∈ U) →
      (∀ b ∈ bs, Binder.Fresh b.binders U Δ Γ) →
      (∀ b ∈ bs,
        Wf cfg (U ∪ Binder.scalars b.binders) (Δ ∪ Binder.ownedSet b.binders) Γ b.body) →
      Wf cfg U Δ Γ (.bmatch (.var y) bs)
  /-- `dmatch!`: destructive match on an owned variable, yielding a reuse credit
      `⋄k` (`k = |x̄ᵢ|`) in each branch -/
  | dmatch {U Δ Γ} (x : Var) (bs : List Branch) :
      (∀ b ∈ bs, Binder.Fresh b.binders U Δ Γ) →
      (∀ b ∈ bs, Wf cfg (U ∪ Binder.scalars b.binders) Δ
          (Γ + Binder.owned b.binders + {Res.credit b.binders.length}) b.body) →
      Wf cfg U Δ (Γ + {Res.var x}) (.dmatch (.var x) bs)
  /-- `empty`: a reuse credit of size zero can be discarded -/
  | empty {U Δ Γ e} : Wf cfg U Δ Γ e → Wf cfg U Δ (Γ + {Res.credit 0}) e
  /-- `drop` (FBIP, Fig. 6) -/
  | drop {U Δ Γ e} (x : Var) : cfg.fbip → Wf cfg U Δ Γ e →
      Wf cfg U Δ (Γ + {Res.var x}) (.drop (.var x) e)
  /-- `free` (FBIP, Fig. 6) -/
  | free {U Δ Γ e} (k : Nat) : cfg.fbip → 1 ≤ k → Wf cfg U Δ Γ e →
      Wf cfg U Δ (Γ + {Res.credit k}) (.free k e)
  /-- `inst` (Fig. 7): an allocation credit can become a reuse credit of any size -/
  | inst {U Δ Γ e} (k : Nat) : 1 ≤ k → Wf cfg U Δ (Γ + {Res.credit k}) e →
      Wf cfg U Δ (Γ + {Res.alloc}) e
  /-- `weaken` (Fig. 7): allocation credits need not be spent -/
  | weaken {U Δ Γ e} : Wf cfg U Δ Γ e → Wf cfg U Δ (Γ + {Res.alloc}) e
  /-- primitive operations read borrowed or scalar arguments (extension) -/
  | prim {U Δ} (op : PrimOp) (vs : List Val) :
      (∀ v ∈ vs, ScalarArg U Δ v) → Wf cfg U Δ 0 (.prim op vs)

/-! ## Well-formed top-level functions (`deffun`) -/

/-- Is a function annotation fully in-place (`fip` or `fip(n)`)? -/
def Annot.isFip : Annot → Bool
  | .fip _ => true
  | _ => false

/-- Is a function annotation `fbip` or `fbip(n)`? -/
def Annot.isFbip : Annot → Bool
  | .fbip _ => true
  | _ => false

/-- The functions a function with annotation `a` may call: a `fip` function may call
    only `fip` functions, a `fbip` function may call `fip` and `fbip` functions. -/
def Sig.callable (sig : Sig) (a : Annot) : List FName :=
  (sig.filter (fun fd => fd.annot.isFip || (a.isFbip && fd.annot.isFbip))).map (·.name)

/-- The configuration used to check a function with annotation `a` in signature `sig`. -/
def Sig.cfg (sig : Sig) (a : Annot) : Cfg where
  fbip := a.isFbip
  funs := sig.callable a
  budget := fun f => ((sig.lookup f).map (·.annot.budget)).getD 0

/-- The owned environment of a function body: its owned non-scalar parameters and
    `n` allocation credits. -/
def FunDef.ownedCtx (fd : FunDef) : Ctx :=
  Binder.owned fd.owned + Multiset.replicate fd.annot.budget Res.alloc

/-- The scalar parameters of a function. -/
def FunDef.scalars (fd : FunDef) : Finset Var :=
  Binder.scalars fd.borrowed ∪ Binder.scalars fd.owned

/-- `deffun`: `ȳ | x̄, ⋄ⁿ ⊢ e` for `f(ȳ; x̄) = e`. -/
def FunDef.Wf (sig : Sig) (fd : FunDef) : Prop :=
  ((fd.borrowed ++ fd.owned).map (·.name)).Nodup ∧
  FIPNamed.Wf (sig.cfg fd.annot) fd.scalars (Binder.ownedSet fd.borrowed) fd.ownedCtx fd.body

/-- `⊩ Σ`: every annotated function of the signature is well-formed; such functions
    are *fully in-place* (or *functional but in-place* for `fbip`). -/
def Sig.Wf (sig : Sig) : Prop :=
  ∀ fd ∈ sig, fd.annot ≠ .plain → fd.Wf sig

end FIPNamed
