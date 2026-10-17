module

public import RequestProject.Named.Sec2_Calculus.DeBruijn.Syntax

@[expose] public section

/-!
# Functional semantics of well-scoped terms (Fig. 3, nameless)

The rules of Fig. 3 for `Term n`.  A β-like step instantiates the bound variables of a
body by `Term.subst` with `Subst.inst` (or `Subst.args` for a call), so there is no
variable capture to worry about, and every step maps `Term n` to `Term n`: **closed
terms reduce to closed terms by construction** (`TStep sig : Term 0 → Term 0 → Prop`).

`RequestProject/Sec2_Calculus/DeBruijn/Simulation.lean` proves that, on closed programs,
this semantics and the named semantics of `RequestProject/Sec2_Calculus/Semantics.lean`
simulate each other step by step.
-/

namespace FIPNamed

/-- Evaluation contexts `E` for terms of scope `n`.  The hole is never under a binder, so
    a context does not change the scope. -/
inductive TECtx (n : Nat) where
  | hole
  | appL (E : TECtx n) (e : Term n)
  | appR (vs : List (TVal n)) (E : TECtx n)
  | callB (f : FName) (E : TECtx n) (e : Term n)
  | callO (f : FName) (vs : List (TVal n)) (E : TECtx n)
  | letIn (sc : List Bool) (E : TECtx n) (e : Term (n + sc.length))
  | bmatch (E : TECtx n) (bs : TBranches n)
  | dmatch (E : TECtx n) (bs : TBranches n)

/-- Plug a term into the hole: `E[e]`. -/
def TECtx.plug {n : Nat} : TECtx n → Term n → Term n
  | .hole, e => e
  | .appL E e2, e => .app (E.plug e) e2
  | .appR vs E, e => .app (.ret vs) (E.plug e)
  | .callB f E e2, e => .call f (E.plug e) e2
  | .callO f vs E, e => .call f (.ret vs) (E.plug e)
  | .letIn sc E e2, e => .letIn sc (E.plug e) e2
  | .bmatch E bs, e => .bmatch (E.plug e) bs
  | .dmatch E bs, e => .dmatch (E.plug e) bs

/-- Composition of evaluation contexts. -/
def TECtx.comp {n : Nat} : TECtx n → TECtx n → TECtx n
  | .hole, E' => E'
  | .appL E e2, E' => .appL (E.comp E') e2
  | .appR vs E, E' => .appR vs (E.comp E')
  | .callB f E e2, E' => .callB f (E.comp E') e2
  | .callO f vs E, E' => .callO f vs (E.comp E')
  | .letIn sc E e2, E' => .letIn sc (E.comp E') e2
  | .bmatch E bs, E' => .bmatch (E.comp E') bs
  | .dmatch E bs, E' => .dmatch (E.comp E') bs

@[simp] theorem TECtx.plug_comp {n : Nat} (E E' : TECtx n) (e : Term n) :
    (E.comp E').plug e = E.plug (E'.plug e) := by
  induction E <;> simp_all [comp, plug]

/-- The first branch for constructor `c` with `k` fields: its scalar flags (with
    `sc.length = k`) and its body. -/
def TBranches.find {n : Nat} : TBranches n → CName → Nat →
    Option (Σ sc : List Bool, Term (n + sc.length))
  | .nil, _, _ => none
  | .cons c' sc e bs, c, k =>
      if c' = c ∧ sc.length = k then some ⟨sc, e⟩ else TBranches.find bs c k

theorem TBranches.find_length {n : Nat} {c : CName} {k : Nat} :
    ∀ {bs : TBranches n} {sc : List Bool} {e : Term (n + sc.length)},
      bs.find c k = some ⟨sc, e⟩ → sc.length = k
  | .nil, _, _, h => by simp [find] at h
  | .cons c' sc' e' bs, sc, e, h => by
    simp only [find] at h
    split at h
    · rename_i h'; cases h; exact h'.2
    · exact TBranches.find_length h

/-- The atom `True` or `False`, as a value of any scope. -/
def tboolVal {n : Nat} (b : Bool) : TVal n := .ctor (if b then "True" else "False") []

/-- Head reductions of Fig. 3 on well-scoped terms. -/
inductive THead (sig : TSig) {n : Nat} : Term n → Term n → Prop where
  /-- `let x̄ = v̄ in e ⟶ e[x̄ := v̄]` -/
  | letIn (sc : List Bool) (vs : List (TVal n)) (e : Term (n + sc.length))
      (h : vs.length = sc.length) :
      THead sig (.letIn sc (.ret vs) e) (e.subst (Subst.inst vs h .bvar))
  /-- `f(v̄₁; v̄₂) ⟶ e[ȳ := v̄₁, x̄ := v̄₂]` -/
  | call (f : FName) (fd : TFunDef) (vs1 vs2 : List (TVal n)) (h1 : vs1.length = fd.borrowed.length)
      (h2 : vs2.length = fd.owned.length) :
      sig.lookup f = some fd →
      THead sig (.call f (.ret vs1) (.ret vs2)) (fd.body.subst (Subst.args vs1 vs2 h1 h2))
  /-- `(f) v̄ ⟶ e[x̄ := v̄]` with `f(; x̄) = e` -/
  | app (f : FName) (fd : TFunDef) (vs : List (TVal n)) (h1 : ([] : List (TVal n)).length = fd.borrowed.length)
      (h2 : vs.length = fd.owned.length) :
      sig.lookup f = some fd →
      THead sig (.app (.ret [.fn f]) (.ret vs)) (fd.body.subst (Subst.args [] vs h1 h2))
  /-- `match (C v̄) {p ↦ e} ⟶ eᵢ[ȳ := v̄]` -/
  | bmatch (c : CName) (vs : List (TVal n)) (bs : TBranches n) (sc : List Bool)
      (e : Term (n + sc.length)) (h : vs.length = sc.length) :
      bs.find c vs.length = some ⟨sc, e⟩ →
      THead sig (.bmatch (.ret [.ctor c vs]) bs) (e.subst (Subst.inst vs h .bvar))
  /-- `match! (C v̄) {p ↦ e} ⟶ eᵢ[x̄ := v̄]` -/
  | dmatch (c : CName) (vs : List (TVal n)) (bs : TBranches n) (sc : List Bool)
      (e : Term (n + sc.length)) (h : vs.length = sc.length) :
      bs.find c vs.length = some ⟨sc, e⟩ →
      THead sig (.dmatch (.ret [.ctor c vs]) bs) (e.subst (Subst.inst vs h .bvar))
  /-- `drop v; e ⟶ e` -/
  | drop (v : TVal n) (e : Term n) : THead sig (.drop v e) e
  /-- `free k; e ⟶ e` -/
  | free (k : Nat) (e : Term n) : THead sig (.free k e) e
  /-- primitive operations on scalar literals (extension) -/
  | prim (op : PrimOp) (a b : Int) :
      THead sig (.prim op [.lit a, .lit b]) (.ret [tboolVal (op.eval a b)])

/-- The small-step relation `E[e₁] ↦ E[e₂]` on well-scoped terms. -/
inductive TStep (sig : TSig) {n : Nat} : Term n → Term n → Prop where
  | step (E : TECtx n) (e1 e2 : Term n) : THead sig e1 e2 → TStep sig (E.plug e1) (E.plug e2)

/-- The reflexive-transitive closure `↦*` on well-scoped terms. -/
abbrev TSteps (sig : TSig) {n : Nat} := Relation.ReflTransGen (TStep sig (n := n))

theorem TStep.head {sig : TSig} {n : Nat} {e1 e2 : Term n} (h : THead sig e1 e2) :
    TStep sig e1 e2 :=
  TStep.step .hole e1 e2 h

theorem TStep.ctx {sig : TSig} {n : Nat} {e1 e2 : Term n} (E : TECtx n)
    (h : TStep sig e1 e2) : TStep sig (E.plug e1) (E.plug e2) := by
  cases h with
  | step E' a b hab => simpa using TStep.step (E.comp E') a b hab

end FIPNamed
