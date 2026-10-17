module

public import RequestProject.Sec2_Calculus.Semantics

@[expose] public section

/- ══════════════════ PAPER sec. 2.2 START: FIP: Fully In-Place: typing rules with owned Gamma and borrowed Delta (PDF pp. 9-11, Fig. 4) ══════════════════
   Environments, values (`var`, `atom`, `reuse`) and the rules `tuple`, `call`, `bapp`, `let`
   and `bmatch` of the judgment `Delta | Gamma |- e` (`Wf`). -/

/-!
# The FIP calculus: well-formed fully in-place expressions (Fig. 4, 6, 7)

`Wf cfg U Δ Γ e` is the judgment `Δ | Γ ⊢ e` of the paper, for `e : Expr n`:

* `Δ` is the *borrowed* environment (a set of variables of scope `n`),
* `Γ` is the *owned* environment, a multiset of owned variables, reuse credits `⋄k`
  and allocation credits `⋄` (Fig. 7),
* `U` is the set of *scalar* variables (extension for Koka value types; empty in the
  paper's calculus),
* `cfg` records whether deallocation is allowed (FBIP, Fig. 6), which top-level
  functions may be called, and their allocation budgets `fip(n)` (Fig. 7).

The rules are those of Fig. 4 (`var`, `atom`, `tuple`, `reuse`, `call`, `let`, `bapp`,
`bmatch`, `empty`, `dmatch!`), Fig. 6 (`drop`, `free`) and Fig. 7 (`inst`, `weaken`
and the modified `call`), plus three rules for scalars (`svar`, `lit`, `prim`).

## Binders

Under a binder of `k` variables the environments of the enclosing scope are weakened
(`Var.shift k`, `Ctx.shift k`, `Vars.shift k`) and the new variables (the indices
`< k`) are added.  The paper's side conditions `x̄ ∉ Δ, Γ` (the bound variables are
fresh) hold by construction: a weakened environment never mentions an index `< k`.
-/

namespace FIP

/-! ## Weakening of variables -/

/-- A variable of scope `n` seen in the scope `n + k` (past `k` new inner binders). -/
def Var.shift {n : Nat} (k : Nat) : Var n → Var (n + k)
  | .bvar i => .bvar ⟨k + i, by omega⟩
  | .loc l => .loc l

theorem Var.shift_injective {n : Nat} (k : Nat) : Function.Injective (Var.shift (n := n) k) := by
  intro a b h
  cases a <;> cases b <;> simp_all [Var.shift, Fin.ext_iff]

/-- `Var.shift` as an embedding. -/
def Var.shiftEmb {n : Nat} (k : Nat) : Var n ↪ Var (n + k) := ⟨Var.shift k, Var.shift_injective k⟩

/-- Weaken a set of variables past `k` new binders. -/
def Vars.shift {n : Nat} (k : Nat) (s : Finset (Var n)) : Finset (Var (n + k)) :=
  s.map (Var.shiftEmb k)

/-- The `j`-th of `k` new binders, as a variable of the scope `n + k`. -/
def Var.newB {n k : Nat} (j : Fin k) : Var (n + k) := .bvar ⟨j, by omega⟩

/-! ## Environments -/

/-- Resources of the owned environment `Γ ::= ∅ | Γ, x | Γ, ⋄k | Γ, ⋄`. -/
inductive Res (n : Nat) where
  /-- an owned variable `x` -/
  | var (x : Var n)
  /-- a reuse credit `⋄k` of size `k` -/
  | credit (k : Nat)
  /-- an allocation credit `⋄` (Fig. 7) -/
  | alloc
  deriving DecidableEq, Repr

/-- An owned environment. -/
abbrev Ctx (n : Nat) := Multiset (Res n)

/-- Weaken a resource past `k` new binders. -/
def Res.shift {n : Nat} (k : Nat) : Res n → Res (n + k)
  | .var x => .var (x.shift k)
  | .credit j => .credit j
  | .alloc => .alloc

/-- Weaken an owned environment past `k` new binders. -/
def Ctx.shift {n : Nat} (k : Nat) (Γ : Ctx n) : Ctx (n + k) := Γ.map (Res.shift k)

/-- The owned variables of an environment. -/
def Ctx.vars {n : Nat} (Γ : Ctx n) : Multiset (Var n) :=
  Γ.filterMap (fun r => match r with | .var x => some x | _ => none)

/-- An environment consisting only of variables (no credits), as required for the
    borrowed part `Γ₂` of the `let` rule. -/
def Ctx.OnlyVars {n : Nat} (Γ : Ctx n) : Prop := ∀ r ∈ Γ, ∃ x, r = .var x

/-- The variables among `xs` with scalar flag `sc`, placed in a scope by `f`. -/
def Binder.select {N : Nat} (xs : List Bool) (sc : Bool) (f : Fin xs.length → Var N) :
    List (Var N) :=
  ((List.finRange xs.length).filter (fun j => xs[j] == sc)).map f

/-- The resources bound by the non-scalar binders `xs` (placed by `f`). -/
def Binder.ownedAt {N : Nat} (xs : List Bool) (f : Fin xs.length → Var N) : Ctx N :=
  ((Binder.select xs false f).map Res.var : List (Res N))

/-- The scalar variables among the binders `xs` (placed by `f`). -/
def Binder.scalarsAt {N : Nat} (xs : List Bool) (f : Fin xs.length → Var N) : Finset (Var N) :=
  (Binder.select xs true f).toFinset

/-- The non-scalar variables among the binders `xs` (placed by `f`), as a set. -/
def Binder.ownedSetAt {N : Nat} (xs : List Bool) (f : Fin xs.length → Var N) :
    Finset (Var N) :=
  (Binder.select xs false f).toFinset

/-- The resources bound by the non-scalar binders of a pattern or let, which are the
    innermost variables of the scope `n + xs.length`. -/
abbrev Binder.owned {n : Nat} (xs : List Bool) : Ctx (n + xs.length) :=
  Binder.ownedAt xs Var.newB

/-- The scalar variables bound by a pattern or let. -/
abbrev Binder.scalars {n : Nat} (xs : List Bool) : Finset (Var (n + xs.length)) :=
  Binder.scalarsAt xs Var.newB

/-- The non-scalar variables bound by a pattern or let, as a set. -/
abbrev Binder.ownedSet {n : Nat} (xs : List Bool) : Finset (Var (n + xs.length)) :=
  Binder.ownedSetAt xs Var.newB

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
def BorrowArg {n : Nat} (cfg : Cfg) (U Δ : Finset (Var n)) : Val n → Prop
  | .var y => y ∈ Δ ∨ y ∈ U
  | .fn g => g ∈ cfg.funs
  | _ => False

/-- The allocation credits needed to pass a function as an argument (Fig. 7). -/
def fnBudget {n : Nat} (cfg : Cfg) : Val n → Nat
  | .fn g => cfg.budget g
  | _ => 0

/-- An argument of a primitive operation: a borrowed or scalar variable, or a literal. -/
def ScalarArg {n : Nat} (U Δ : Finset (Var n)) : Val n → Prop
  | .var y => y ∈ Δ ∨ y ∈ U
  | .lit _ => True
  | _ => False

mutual
/-- Well-formed values `Δ | Γ ⊢ v` (rules `var`, `atom`, `reuse`, and the scalar rules
    `svar` and `lit`). -/
inductive WfVal {n : Nat} (U Δ : Finset (Var n)) : Ctx n → Val n → Prop where
  /-- `Δ | x ⊢ x` -/
  | var (x : Var n) : WfVal U Δ {Res.var x} (.var x)
  /-- a scalar variable may be used freely (extension) -/
  | svar (x : Var n) : x ∈ U → WfVal U Δ 0 (.var x)
  /-- `Δ | ∅ ⊢ C` -/
  | atom (c : CName) : WfVal U Δ 0 (.ctor c [])
  /-- a scalar literal (extension) -/
  | lit (k : Int) : WfVal U Δ 0 (.lit k)
  /-- `Δ | Γ₁, ..., Γₖ, ⋄k ⊢ Cᵏ v₁ ... vₖ` for `k ≥ 1` -/
  | reuse (c : CName) (vs : List (Val n)) (Γ : Ctx n) :
      vs ≠ [] → WfVals U Δ Γ vs → WfVal U Δ (Γ + {Res.credit vs.length}) (.ctor c vs)
/-- Well-formed lists of values, splitting the owned environment. -/
inductive WfVals {n : Nat} (U Δ : Finset (Var n)) : Ctx n → List (Val n) → Prop where
  | nil : WfVals U Δ 0 []
  | cons (Γ₁ Γ₂ : Ctx n) (v : Val n) (vs : List (Val n)) :
      WfVal U Δ Γ₁ v → WfVals U Δ Γ₂ vs → WfVals U Δ (Γ₁ + Γ₂) (v :: vs)
end

/-- Well-formed FIP expressions `Δ | Γ ⊢ e` (Fig. 4, 6, 7). -/
inductive Wf (cfg : Cfg) : {n : Nat} → Finset (Var n) → Finset (Var n) → Ctx n → Expr n → Prop
    where
  /-- `tuple`: `Δ | Γ₁, ..., Γₙ ⊢ (v₁, ..., vₙ)` -/
  | tuple {n : Nat} {U Δ : Finset (Var n)} {Γ vs} : WfVals U Δ Γ vs → Wf cfg U Δ Γ (.ret vs)
  /-- `call` (with the allocation credits of Fig. 7):
      `Δ | Γ, ⋄ⁿ⁺ⁿ' ⊢ f(ȳ; e)` -/
  | call {n : Nat} {U Δ : Finset (Var n)} {Γ} (f : FName) (ys : List (Val n)) (e : Expr n) :
      f ∈ cfg.funs → (∀ y ∈ ys, BorrowArg cfg U Δ y) → Wf cfg U Δ Γ e →
      Wf cfg U Δ
        (Γ + Multiset.replicate (cfg.budget f + (ys.map (fnBudget cfg)).sum) Res.alloc)
        (.call f (.ret ys) e)
  /-- `bapp`: `Δ | Γ ⊢ y e` for a borrowed function `y ∈ Δ` -/
  | bapp {n : Nat} {U Δ : Finset (Var n)} {Γ} (y : Var n) (e : Expr n) :
      y ∈ Δ → Wf cfg U Δ Γ e → Wf cfg U Δ Γ (.app (.var y) e)
  /-- `(f) e` for a top-level function `f ∈ dom(Σ)`, paying its allocation budget.  This
      is the instance of `bapp` obtained when a top-level function has been substituted
      for the borrowed variable `y` (the paper allows `ȳ ∈ Δ, dom(Σ)`). -/
  | fapp {n : Nat} {U Δ : Finset (Var n)} {Γ} (f : FName) (e : Expr n) :
      f ∈ cfg.funs → Wf cfg U Δ Γ e →
      Wf cfg U Δ (Γ + Multiset.replicate (cfg.budget f) Res.alloc) (.app (.val (.fn f)) e)
  /-- `let`: `Δ | Γ₁, Γ₂, Γ₃ ⊢ let x̄ = e₁ in e₂` where `Γ₂` is borrowed in `e₁`.  The body
      `e₂` is checked in the scope extended by `x̄`. -/
  | letIn {n : Nat} {U Δ : Finset (Var n)} (Γ₁ Γ₂ Γ₃ : Ctx n) (xs : List Bool) (e₁ : Expr n)
      (e₂ : Expr (n + xs.length)) :
      Γ₂.OnlyVars →
      Wf cfg U (Δ ∪ Γ₂.vars.toFinset) Γ₁ e₁ →
      Wf cfg (Vars.shift xs.length U ∪ Binder.scalars xs) (Vars.shift xs.length Δ)
        ((Γ₂ + Γ₃).shift xs.length + Binder.owned xs) e₂ →
      Wf cfg U Δ (Γ₁ + Γ₂ + Γ₃) (.letIn xs e₁ e₂)
  /-- `bmatch`: matching on a borrowed (or scalar) variable; the pattern variables are
      borrowed in each branch -/
  | bmatch {n : Nat} {U Δ : Finset (Var n)} {Γ} (y : Var n) (bs : Branches n) :
      (y ∈ Δ ∨ y ∈ U) →
      (∀ b ∈ bs.toList,
        Wf cfg (Vars.shift b.binders.length U ∪ Binder.scalars b.binders)
          (Vars.shift b.binders.length Δ ∪ Binder.ownedSet b.binders)
          (Γ.shift b.binders.length) b.body) →
      Wf cfg U Δ Γ (.bmatch (.var y) bs)
/- ══════════════════ PAPER sec. 2.2 END: FIP: Fully In-Place: typing rules with owned Gamma and borrowed Delta ══════════════════ -/

/- ══════════════════ PAPER sec. 2.2, 2.4, 2.5 START: Reuse credits, FBIP: Allowing Deallocation, FIP and FBIP with bounded allocation (PDF pp. 9-14, Fig. 4, 6, 7) ══════════════════
   Destructive match `match!` yields a reuse credit; `empty`; FBIP `drop`/`free` (Fig. 6);
   allocation credits `inst`/`weaken` for `fip(n)` (Fig. 7); well-formed functions and
   signatures (`FunDef.Wf`, `Sig.Wf`, i.e. `||- Sigma`). -/

  /-- `dmatch!`: destructive match on an owned variable, yielding a reuse credit
      `⋄k` (`k = |x̄ᵢ|`) in each branch -/
  | dmatch {n : Nat} {U Δ : Finset (Var n)} {Γ} (x : Var n) (bs : Branches n) :
      (∀ b ∈ bs.toList,
        Wf cfg (Vars.shift b.binders.length U ∪ Binder.scalars b.binders)
          (Vars.shift b.binders.length Δ)
          (Γ.shift b.binders.length + Binder.owned b.binders +
            {Res.credit b.binders.length}) b.body) →
      Wf cfg U Δ (Γ + {Res.var x}) (.dmatch (.var x) bs)
  /-- `empty`: a reuse credit of size zero can be discarded -/
  | empty {n : Nat} {U Δ : Finset (Var n)} {Γ e} : Wf cfg U Δ Γ e →
      Wf cfg U Δ (Γ + {Res.credit 0}) e
  /-- `drop` (FBIP, Fig. 6) -/
  | drop {n : Nat} {U Δ : Finset (Var n)} {Γ e} (x : Var n) : cfg.fbip → Wf cfg U Δ Γ e →
      Wf cfg U Δ (Γ + {Res.var x}) (.drop (.var x) e)
  /-- `free` (FBIP, Fig. 6) -/
  | free {n : Nat} {U Δ : Finset (Var n)} {Γ e} (k : Nat) : cfg.fbip → 1 ≤ k → Wf cfg U Δ Γ e →
      Wf cfg U Δ (Γ + {Res.credit k}) (.free k e)
  /-- `inst` (Fig. 7): an allocation credit can become a reuse credit of any size -/
  | inst {n : Nat} {U Δ : Finset (Var n)} {Γ e} (k : Nat) : 1 ≤ k →
      Wf cfg U Δ (Γ + {Res.credit k}) e → Wf cfg U Δ (Γ + {Res.alloc}) e
  /-- `weaken` (Fig. 7): allocation credits need not be spent -/
  | weaken {n : Nat} {U Δ : Finset (Var n)} {Γ e} : Wf cfg U Δ Γ e →
      Wf cfg U Δ (Γ + {Res.alloc}) e
  /-- primitive operations read borrowed or scalar arguments (extension) -/
  | prim {n : Nat} {U Δ : Finset (Var n)} (op : PrimOp) (vs : List (Val n)) :
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

/-- A borrowed parameter `yⱼ` of a function, as a variable of its body. -/
def FunDef.bParam (fd : FunDef) (j : Fin fd.borrowed.length) :
    Var (fd.owned.length + fd.borrowed.length) :=
  .bvar ⟨j, by omega⟩

/-- An owned parameter `xᵢ` of a function, as a variable of its body. -/
def FunDef.oParam (fd : FunDef) (i : Fin fd.owned.length) :
    Var (fd.owned.length + fd.borrowed.length) :=
  .bvar ⟨fd.borrowed.length + i, by omega⟩

/-- The owned environment of a function body: its owned non-scalar parameters and
    `n` allocation credits. -/
def FunDef.ownedCtx (fd : FunDef) : Ctx (fd.owned.length + fd.borrowed.length) :=
  Binder.ownedAt fd.owned fd.oParam + Multiset.replicate fd.annot.budget Res.alloc

/-- The borrowed environment of a function body: its borrowed non-scalar parameters. -/
def FunDef.borrowedSet (fd : FunDef) : Finset (Var (fd.owned.length + fd.borrowed.length)) :=
  Binder.ownedSetAt fd.borrowed fd.bParam

/-- The scalar parameters of a function. -/
def FunDef.scalars (fd : FunDef) : Finset (Var (fd.owned.length + fd.borrowed.length)) :=
  Binder.scalarsAt fd.borrowed fd.bParam ∪ Binder.scalarsAt fd.owned fd.oParam

/-- `deffun`: `ȳ | x̄, ⋄ⁿ ⊢ e` for `f(ȳ; x̄) = e`.  (The parameters are distinct by
    construction.) -/
def FunDef.Wf (sig : Sig) (fd : FunDef) : Prop :=
  FIP.Wf (sig.cfg fd.annot) fd.scalars fd.borrowedSet fd.ownedCtx fd.body

/-- `⊩ Σ`: every annotated function of the signature is well-formed; such functions
    are *fully in-place* (or *functional but in-place* for `fbip`). -/
def Sig.Wf (sig : Sig) : Prop :=
  ∀ fd ∈ sig, fd.annot ≠ .plain → fd.Wf sig

end FIP

/- ══════════════════ PAPER sec. 2.2, 2.4, 2.5 END: Reuse credits, FBIP: Allowing Deallocation, FIP and FBIP with bounded allocation ══════════════════ -/
