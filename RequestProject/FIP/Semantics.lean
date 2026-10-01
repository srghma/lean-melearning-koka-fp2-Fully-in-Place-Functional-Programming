module

public import RequestProject.FIP.Syntax

@[expose] public section

/-!
# Functional operational semantics (Fig. 3)

Substitution, evaluation contexts, head reductions and the small-step relation
`e ↦ e'` of the FIP calculus, together with free variables and a small-step
interpreter `Expr.step?` that is proved sound for the relation.
-/

namespace FIP

/-- A substitution of values for (program) names; `e[x̄ := v̄]` uses `zipSubst`. -/
abbrev Subst := List (String × Val)

/-- The substitution `[x1 := v1, ..., xn := vn]`. -/
def zipSubst (xs : List Binder) (vs : List Val) : Subst :=
  (xs.map (·.name)).zip vs

/-- Remove the names bound by `xs` from a substitution (substitution stops at binders). -/
def Subst.remove (σ : Subst) (xs : List Binder) : Subst :=
  σ.filter (fun p => !(xs.map (·.name)).contains p.1)

mutual
/-- Apply a substitution to a value. -/
def Val.subst (σ : Subst) : Val → Val
  | .var (.name s) => (σ.lookup s).getD (.var (.name s))
  | .var (.loc n) => .var (.loc n)
  | .fn f => .fn f
  | .ctor c vs => .ctor c (Val.substList σ vs)
  | .lit n => .lit n
/-- Apply a substitution to a list of values. -/
def Val.substList (σ : Subst) : List Val → List Val
  | [] => []
  | v :: vs => Val.subst σ v :: Val.substList σ vs
end

mutual
/-- Apply a substitution to an expression (bound names are not substituted). -/
def Expr.subst (σ : Subst) : Expr → Expr
  | .ret vs => .ret (Val.substList σ vs)
  | .app e1 e2 => .app (Expr.subst σ e1) (Expr.subst σ e2)
  | .call f e1 e2 => .call f (Expr.subst σ e1) (Expr.subst σ e2)
  | .letIn xs e1 e2 => .letIn xs (Expr.subst σ e1) (Expr.subst (σ.remove xs) e2)
  | .bmatch e bs => .bmatch (Expr.subst σ e) (Expr.substBranches σ bs)
  | .dmatch e bs => .dmatch (Expr.subst σ e) (Expr.substBranches σ bs)
  | .drop x e => .drop (Val.subst σ x) (Expr.subst σ e)
  | .free k e => .free k (Expr.subst σ e)
  | .prim op vs => .prim op (Val.substList σ vs)
/-- Apply a substitution to the branches of a match. -/
def Expr.substBranches (σ : Subst) : List Branch → List Branch
  | [] => []
  | .mk c xs e :: bs => .mk c xs (Expr.subst (σ.remove xs) e) :: Expr.substBranches σ bs
end

@[simp] theorem Val.substList_eq_map (σ : Subst) (vs : List Val) :
    Val.substList σ vs = vs.map (Val.subst σ) := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp [Val.substList, ih]

/-! ## Free variables -/

mutual
/-- The free variables of a value (as a list, with multiplicity). -/
def Val.fv : Val → List Var
  | .var x => [x]
  | .fn _ => []
  | .ctor _ vs => Val.fvList vs
  | .lit _ => []
/-- The free variables of a list of values. -/
def Val.fvList : List Val → List Var
  | [] => []
  | v :: vs => Val.fv v ++ Val.fvList vs
end

/-- The variables bound by a list of binders. -/
def Binder.vars (xs : List Binder) : List Var := xs.map (fun b => Var.name b.name)

mutual
/-- The free variables of an expression (as a list, with multiplicity). -/
def Expr.fv : Expr → List Var
  | .ret vs => Val.fvList vs
  | .app e1 e2 => Expr.fv e1 ++ Expr.fv e2
  | .call _ e1 e2 => Expr.fv e1 ++ Expr.fv e2
  | .letIn xs e1 e2 => Expr.fv e1 ++ (Expr.fv e2).filter (fun v => v ∉ Binder.vars xs)
  | .bmatch e bs => Expr.fv e ++ Expr.fvBranches bs
  | .dmatch e bs => Expr.fv e ++ Expr.fvBranches bs
  | .drop x e => Val.fv x ++ Expr.fv e
  | .free _ e => Expr.fv e
  | .prim _ vs => Val.fvList vs
/-- The free variables of the branches of a match. -/
def Expr.fvBranches : List Branch → List Var
  | [] => []
  | .mk _ xs e :: bs => (Expr.fv e).filter (fun v => v ∉ Binder.vars xs) ++ Expr.fvBranches bs
end

/-- A value is *closed* if it has no free variables. -/
def Val.Closed (v : Val) : Prop := v.fv = []

/-! ## Evaluation contexts

`E ::= □ | E e | v E | f(E; e) | f(v; E) | let x̄ = E in e | match E {p ↦ e}
      | match! E {p ↦ e}` -/

/-- Evaluation contexts of the functional semantics (Fig. 3). -/
inductive ECtx where
  | hole
  | appL (E : ECtx) (e : Expr)
  | appR (vs : List Val) (E : ECtx)
  | callB (f : FName) (E : ECtx) (e : Expr)
  | callO (f : FName) (vs : List Val) (E : ECtx)
  | letIn (xs : List Binder) (E : ECtx) (e : Expr)
  | bmatch (E : ECtx) (bs : List Branch)
  | dmatch (E : ECtx) (bs : List Branch)
  deriving Inhabited

/-- Plug an expression into the hole of an evaluation context: `E[e]`. -/
def ECtx.plug : ECtx → Expr → Expr
  | .hole, e => e
  | .appL E e2, e => .app (E.plug e) e2
  | .appR vs E, e => .app (.ret vs) (E.plug e)
  | .callB f E e2, e => .call f (E.plug e) e2
  | .callO f vs E, e => .call f (.ret vs) (E.plug e)
  | .letIn xs E e2, e => .letIn xs (E.plug e) e2
  | .bmatch E bs, e => .bmatch (E.plug e) bs
  | .dmatch E bs, e => .dmatch (E.plug e) bs

/-- Composition of evaluation contexts: `(E₁ ∘ E₂)[e] = E₁[E₂[e]]`. -/
def ECtx.comp : ECtx → ECtx → ECtx
  | .hole, E' => E'
  | .appL E e2, E' => .appL (E.comp E') e2
  | .appR vs E, E' => .appR vs (E.comp E')
  | .callB f E e2, E' => .callB f (E.comp E') e2
  | .callO f vs E, E' => .callO f vs (E.comp E')
  | .letIn xs E e2, E' => .letIn xs (E.comp E') e2
  | .bmatch E bs, E' => .bmatch (E.comp E') bs
  | .dmatch E bs, E' => .dmatch (E.comp E') bs

@[simp] theorem ECtx.plug_comp (E E' : ECtx) (e : Expr) :
    (E.comp E').plug e = E.plug (E'.plug e) := by
  induction E <;> simp_all [comp, plug]

/-! ## Head reductions -/

/-- Find the branch for constructor `c` (with arity `k`). -/
def findBranch (bs : List Branch) (c : CName) (k : Nat) : Option Branch :=
  bs.find? (fun b => b.ctor == c && b.binders.length == k)

/-- The atom `True` or `False`. -/
def boolVal (b : Bool) : Val := .ctor (if b then "True" else "False") []

/-- Evaluate a primitive operation on scalar literals. -/
def PrimOp.eval : PrimOp → Int → Int → Bool
  | .lt, a, b => decide (a < b)
  | .le, a, b => decide (a ≤ b)
  | .gt, a, b => decide (a > b)
  | .ge, a, b => decide (a ≥ b)
  | .eq, a, b => decide (a = b)
  | .ne, a, b => decide (a ≠ b)

/-- Head reductions `e ⟶ e'` of Fig. 3 (plus the extensions). -/
inductive Head (sig : Sig) : Expr → Expr → Prop where
  /-- `let x̄ = v̄ in e ⟶ e[x̄ := v̄]` -/
  | letIn (xs : List Binder) (vs : List Val) (e : Expr) :
      xs.length = vs.length →
      Head sig (.letIn xs (.ret vs) e) (e.subst (zipSubst xs vs))
  /-- `f(v̄₁; v̄₂) ⟶ e[ȳ := v̄₁, x̄ := v̄₂]` with `f(ȳ; x̄) = e ∈ Σ` -/
  | call (f : FName) (fd : FunDef) (vs1 vs2 : List Val) :
      sig.lookup f = some fd →
      fd.borrowed.length = vs1.length → fd.owned.length = vs2.length →
      Head sig (.call f (.ret vs1) (.ret vs2))
        (fd.body.subst (zipSubst fd.borrowed vs1 ++ zipSubst fd.owned vs2))
  /-- `(f) v̄ ⟶ e[x̄ := v̄]` with `f(; x̄) = e ∈ Σ` -/
  | app (f : FName) (fd : FunDef) (vs : List Val) :
      sig.lookup f = some fd → fd.borrowed = [] → fd.owned.length = vs.length →
      Head sig (.app (.val (.fn f)) (.ret vs)) (fd.body.subst (zipSubst fd.owned vs))
  /-- `match (C v̄) {p ↦ e} ⟶ eᵢ[ȳ := v̄]` with `pᵢ = C ȳ` -/
  | bmatch (c : CName) (vs : List Val) (bs : List Branch) (xs : List Binder) (e : Expr) :
      findBranch bs c vs.length = some (.mk c xs e) →
      Head sig (.bmatch (.val (.ctor c vs)) bs) (e.subst (zipSubst xs vs))
  /-- `match! (C v̄) {p ↦ e} ⟶ eᵢ[x̄ := v̄]` with `pᵢ = C x̄` -/
  | dmatch (c : CName) (vs : List Val) (bs : List Branch) (xs : List Binder) (e : Expr) :
      findBranch bs c vs.length = some (.mk c xs e) →
      Head sig (.dmatch (.val (.ctor c vs)) bs) (e.subst (zipSubst xs vs))
  /-- `drop v; e ⟶ e` (deallocation has no effect in the functional semantics) -/
  | drop (v : Val) (e : Expr) : Head sig (.drop v e) e
  /-- `free k; e ⟶ e` -/
  | free (k : Nat) (e : Expr) : Head sig (.free k e) e
  /-- primitive operations on scalar literals (extension) -/
  | prim (op : PrimOp) (a b : Int) :
      Head sig (.prim op [.lit a, .lit b]) (.val (boolVal (op.eval a b)))

/-- The small-step relation `E[e₁] ↦ E[e₂]` (rule *step*). -/
inductive Step (sig : Sig) : Expr → Expr → Prop where
  | step (E : ECtx) (e1 e2 : Expr) : Head sig e1 e2 → Step sig (E.plug e1) (E.plug e2)

/-- The reflexive-transitive closure `↦*`. -/
abbrev Steps (sig : Sig) := Relation.ReflTransGen (Step sig)

theorem Step.head {sig : Sig} {e1 e2 : Expr} (h : Head sig e1 e2) : Step sig e1 e2 :=
  Step.step .hole e1 e2 h

theorem Step.ctx {sig : Sig} {e1 e2 : Expr} (E : ECtx) (h : Step sig e1 e2) :
    Step sig (E.plug e1) (E.plug e2) := by
  cases h with
  | step E' a b hab => simpa using Step.step (E.comp E') a b hab

theorem Steps.ctx {sig : Sig} {e1 e2 : Expr} (E : ECtx) (h : Steps sig e1 e2) :
    Steps sig (E.plug e1) (E.plug e2) := by
  induction h with
  | refl => exact .refl
  | tail _ h ih => exact ih.tail (h.ctx E)

/-! ## A small-step interpreter

`Expr.step?` computes the unique reduct of an expression (if any). It is used to run
the examples of the paper; `Expr.step?_sound` shows that it agrees with `Step`. -/

/-- One head-reduction step, if the expression is a redex. -/
def headStep? (sig : Sig) : Expr → Option Expr
  | .letIn xs (.ret vs) e =>
      if xs.length = vs.length then some (e.subst (zipSubst xs vs)) else none
  | .call f (.ret vs1) (.ret vs2) =>
      match sig.lookup f with
      | some fd =>
        if fd.borrowed.length = vs1.length ∧ fd.owned.length = vs2.length then
          some (fd.body.subst (zipSubst fd.borrowed vs1 ++ zipSubst fd.owned vs2))
        else none
      | none => none
  | .app (.ret [.fn f]) (.ret vs) =>
      match sig.lookup f with
      | some fd =>
        if fd.borrowed = [] ∧ fd.owned.length = vs.length then
          some (fd.body.subst (zipSubst fd.owned vs))
        else none
      | none => none
  | .bmatch (.ret [.ctor c vs]) bs =>
      match findBranch bs c vs.length with
      | some (.mk c' xs e) => if c' = c then some (e.subst (zipSubst xs vs)) else none
      | none => none
  | .dmatch (.ret [.ctor c vs]) bs =>
      match findBranch bs c vs.length with
      | some (.mk c' xs e) => if c' = c then some (e.subst (zipSubst xs vs)) else none
      | none => none
  | .drop _ e => some e
  | .free _ e => some e
  | .prim op [.lit a, .lit b] => some (.val (boolVal (op.eval a b)))
  | _ => none

theorem headStep?_sound {sig : Sig} {e e' : Expr} (h : headStep? sig e = some e') :
    Head sig e e' := by
  unfold headStep? at h
  split at h <;> (try simp_all) <;> (try split at h) <;> (try simp_all)
  all_goals (try obtain ⟨_, rfl⟩ := h)
  all_goals (constructor <;> simp_all)

/-- One step of the functional semantics, if the expression is not stuck or final. -/
def Expr.step? (sig : Sig) (e : Expr) : Option Expr :=
  match headStep? sig e with
  | some e' => some e'
  | none =>
    match e with
    | .app (.ret vs) e2 => (Expr.step? sig e2).map (.app (.ret vs))
    | .app e1 e2 => (Expr.step? sig e1).map (.app · e2)
    | .call f (.ret vs) e2 => (Expr.step? sig e2).map (.call f (.ret vs))
    | .call f e1 e2 => (Expr.step? sig e1).map (.call f · e2)
    | .letIn xs e1 e2 => (Expr.step? sig e1).map (.letIn xs · e2)
    | .bmatch e1 bs => (Expr.step? sig e1).map (.bmatch · bs)
    | .dmatch e1 bs => (Expr.step? sig e1).map (.dmatch · bs)
    | _ => none

theorem Expr.step?_sound {sig : Sig} : ∀ {e e' : Expr}, e.step? sig = some e' → Step sig e e'
  | e, e', h => by
    unfold Expr.step? at h
    split at h
    · simp_all [headStep?_sound, Step.head]
    · rename_i hh
      split at h
      · obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
        exact (Expr.step?_sound ha).ctx (.appR _ .hole)
      · obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
        exact (Expr.step?_sound ha).ctx (.appL .hole _)
      · obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
        exact (Expr.step?_sound ha).ctx (.callO _ _ .hole)
      · obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
        exact (Expr.step?_sound ha).ctx (.callB _ .hole _)
      · obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
        exact (Expr.step?_sound ha).ctx (.letIn _ .hole _)
      · obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
        exact (Expr.step?_sound ha).ctx (.bmatch .hole _)
      · obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
        exact (Expr.step?_sound ha).ctx (.dmatch .hole _)
      · simp_all

/-- Run the interpreter for at most `fuel` steps. -/
def Expr.run (sig : Sig) : Nat → Expr → Expr
  | 0, e => e
  | n + 1, e => match e.step? sig with
    | some e' => Expr.run sig n e'
    | none => e

theorem Expr.run_sound (sig : Sig) (n : Nat) (e : Expr) : Steps sig e (e.run sig n) := by
  induction n generalizing e with
  | zero => exact .refl
  | succ n ih =>
    simp only [Expr.run]
    split
    · next e' h => exact Relation.ReflTransGen.head (Expr.step?_sound h) (ih e')
    · exact .refl

/-- Evaluate an expression to an unboxed tuple of values, using at most `fuel` steps. -/
def Expr.eval (sig : Sig) (fuel : Nat) (e : Expr) : Option (List Val) :=
  match e.run sig fuel with
  | .ret vs => some vs
  | _ => none

theorem Expr.eval_sound {sig : Sig} {fuel : Nat} {e : Expr} {vs : List Val}
    (h : e.eval sig fuel = some vs) : Steps sig e (.ret vs) := by
  unfold Expr.eval at h
  split at h
  · next h' => simp at h; rw [← h, ← h']; exact Expr.run_sound sig fuel e
  · simp at h

end FIP
