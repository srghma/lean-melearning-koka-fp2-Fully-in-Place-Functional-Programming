module

public import RequestProject.Sec2_Calculus.Syntax

@[expose] public section

/- ══════════════════ PAPER sec. 2.1 START: Functional Operational Semantics (PDF pp. 8-9, Fig. 3) ══════════════════
   Substitution, evaluation contexts `E`, head reductions, `e |->* e'`, and an executable
   interpreter proved sound (used by the `..._example` theorems). -/

/-!
# Functional operational semantics (Fig. 3)

Substitution, evaluation contexts, head reductions and the small-step relation
`e ↦ e'` of the FIP calculus on well-scoped de Bruijn terms, together with a small-step
interpreter `Expr.step?` that is proved sound for the relation.

## Substitution

A substitution `σ : Fin n → Val m` maps every bound variable of scope `n` to a value of
scope `m`; locations are left alone.  Values contain no binders, so a renaming is the
substitution `Val.var ∘ Var.bvar ∘ ρ`.  Under `k` binders a substitution is pushed with
`Subst.up k`.  The β-rules instantiate the `k` innermost variables with
`Subst.inst k vs σ`.

There is no variable capture to worry about, and every step maps `Expr n` to `Expr n`:
**closed expressions reduce to closed expressions by construction**
(`Step sig : Expr 0 → Expr 0 → Prop`).
-/

namespace FIP

/-! ## Substitution -/

/-- The identity substitution. -/
def Subst.ids (n : Nat) : Fin n → Val n := fun i => .var (.bvar i)

mutual
/-- Apply a substitution to a value. -/
def Val.subst {n m : Nat} (σ : Fin n → Val m) : Val n → Val m
  | .var (.bvar i) => σ i
  | .var (.loc l) => .var (.loc l)
  | .fn f => .fn f
  | .ctor c vs => .ctor c (Val.substList σ vs)
  | .lit k => .lit k
/-- Apply a substitution to a list of values. -/
def Val.substList {n m : Nat} (σ : Fin n → Val m) : List (Val n) → List (Val m)
  | [] => []
  | v :: vs => Val.subst σ v :: Val.substList σ vs
end

@[simp] theorem Val.substList_eq_map {n m : Nat} (σ : Fin n → Val m) (vs : List (Val n)) :
    Val.substList σ vs = vs.map (Val.subst σ) := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp [Val.substList, ih]

/-- Weakening: a value of scope `m` seen in the scope `m + k`, where the `k` new variables
    are the innermost ones (indices `< k`). -/
def Val.shift {m : Nat} (k : Nat) (v : Val m) : Val (m + k) :=
  v.subst fun i => .var (.bvar ⟨k + i, by omega⟩)

/-- Push a substitution under `k` binders: the new variables are left alone, and the
    values substituted for the old ones are weakened. -/
def Subst.up {n m : Nat} (k : Nat) (σ : Fin n → Val m) : Fin (n + k) → Val (m + k) :=
  fun i => if h : i.val < k then .var (.bvar ⟨i, by omega⟩) else (σ ⟨i - k, by omega⟩).shift k

/-- The substitution `[x̄ := v̄]` for the `k` innermost variables of the scope `n + k`
    (the `j`-th of them is sent to the `j`-th value of `vs`), the other variables being
    sent to `σ`. -/
def Subst.inst {n m : Nat} (k : Nat) (vs : List (Val m)) (σ : Fin n → Val m) :
    Fin (n + k) → Val m :=
  fun i => if hi : i.val < k then vs.getD i.val default else σ ⟨i - k, by omega⟩

/-- The substitution `[x̄ := v̄]` of a scope consisting of `k` variables only. -/
def Subst.ofList {m : Nat} (k : Nat) (vs : List (Val m)) : Fin k → Val m :=
  fun i => vs.getD i.val default

mutual
/-- Apply a substitution to an expression. -/
def Expr.subst {n m : Nat} (σ : Fin n → Val m) : Expr n → Expr m
  | .ret vs => .ret (Val.substList σ vs)
  | .app e1 e2 => .app (Expr.subst σ e1) (Expr.subst σ e2)
  | .call f e1 e2 => .call f (Expr.subst σ e1) (Expr.subst σ e2)
  | .letIn xs e1 e2 => .letIn xs (Expr.subst σ e1) (Expr.subst (Subst.up xs.length σ) e2)
  | .bmatch e bs => .bmatch (Expr.subst σ e) (Branches.subst σ bs)
  | .dmatch e bs => .dmatch (Expr.subst σ e) (Branches.subst σ bs)
  | .drop x e => .drop (Val.subst σ x) (Expr.subst σ e)
  | .free k e => .free k (Expr.subst σ e)
  | .prim op vs => .prim op (Val.substList σ vs)
/-- Apply a substitution to the branches of a match. -/
def Branches.subst {n m : Nat} (σ : Fin n → Val m) : Branches n → Branches m
  | .nil => .nil
  | .cons c xs e bs => .cons c xs (Expr.subst (Subst.up xs.length σ) e) (Branches.subst σ bs)
end

/-! ## Free variables -/

/-- A variable of scope `n + k` seen in the scope `n`, if it is not one of the `k`
    innermost (bound) variables. -/
def Var.unshift {n : Nat} (k : Nat) : Var (n + k) → Option (Var n)
  | .bvar i => if h : k ≤ i.val then some (.bvar ⟨i.val - k, by omega⟩) else none
  | .loc l => some (.loc l)

mutual
/-- The free variables (and locations) of a value, with multiplicity. -/
def Val.fv {n : Nat} : Val n → List (Var n)
  | .var x => [x]
  | .fn _ => []
  | .ctor _ vs => Val.fvList vs
  | .lit _ => []
/-- The free variables of a list of values. -/
def Val.fvList {n : Nat} : List (Val n) → List (Var n)
  | [] => []
  | v :: vs => Val.fv v ++ Val.fvList vs
end

mutual
/-- The free variables (and locations) of an expression, with multiplicity. -/
def Expr.fv {n : Nat} : Expr n → List (Var n)
  | .ret vs => Val.fvList vs
  | .app e1 e2 => Expr.fv e1 ++ Expr.fv e2
  | .call _ e1 e2 => Expr.fv e1 ++ Expr.fv e2
  | .letIn xs e1 e2 => Expr.fv e1 ++ (Expr.fv e2).filterMap (Var.unshift xs.length)
  | .bmatch e bs => Expr.fv e ++ Branches.fv bs
  | .dmatch e bs => Expr.fv e ++ Branches.fv bs
  | .drop x e => Val.fv x ++ Expr.fv e
  | .free _ e => Expr.fv e
  | .prim _ vs => Val.fvList vs
/-- The free variables of the branches of a match. -/
def Branches.fv {n : Nat} : Branches n → List (Var n)
  | .nil => []
  | .cons _ xs e bs => (Expr.fv e).filterMap (Var.unshift xs.length) ++ Branches.fv bs
end

/-- `e[x̄ := v̄]`: instantiate the `k` innermost variables of `e : Expr (n + k)`. -/
def Expr.inst {n k : Nat} (e : Expr (n + k)) (vs : List (Val n)) : Expr n :=
  e.subst (Subst.inst k vs (Subst.ids n))

/-- The substitution of the arguments `v̄₁; v̄₂` for the parameters `ȳ; x̄` of a function
    body. -/
def FunDef.argSubst {m : Nat} (fd : FunDef) (vs1 vs2 : List (Val m)) :
    Fin (fd.owned.length + fd.borrowed.length) → Val m :=
  Subst.inst fd.borrowed.length vs1 (Subst.ofList fd.owned.length vs2)

/-- The body of a function instantiated with its arguments: `e[ȳ := v̄₁, x̄ := v̄₂]`. -/
def FunDef.instBody {m : Nat} (fd : FunDef) (vs1 vs2 : List (Val m)) : Expr m :=
  fd.body.subst (fd.argSubst vs1 vs2)

/-! ## Evaluation contexts

`E ::= □ | E e | v E | f(E; e) | f(v; E) | let x̄ = E in e | match E {p ↦ e}
      | match! E {p ↦ e}` -/

/-- Evaluation contexts of the functional semantics (Fig. 3).  The hole is never under a
    binder, so a context does not change the scope. -/
inductive ECtx (n : Nat) where
  | hole
  | appL (E : ECtx n) (e : Expr n)
  | appR (vs : List (Val n)) (E : ECtx n)
  | callB (f : FName) (E : ECtx n) (e : Expr n)
  | callO (f : FName) (vs : List (Val n)) (E : ECtx n)
  | letIn (xs : List Bool) (E : ECtx n) (e : Expr (n + xs.length))
  | bmatch (E : ECtx n) (bs : Branches n)
  | dmatch (E : ECtx n) (bs : Branches n)

instance {n : Nat} : Inhabited (ECtx n) := ⟨.hole⟩

/-- Plug an expression into the hole of an evaluation context: `E[e]`. -/
def ECtx.plug {n : Nat} : ECtx n → Expr n → Expr n
  | .hole, e => e
  | .appL E e2, e => .app (E.plug e) e2
  | .appR vs E, e => .app (.ret vs) (E.plug e)
  | .callB f E e2, e => .call f (E.plug e) e2
  | .callO f vs E, e => .call f (.ret vs) (E.plug e)
  | .letIn xs E e2, e => .letIn xs (E.plug e) e2
  | .bmatch E bs, e => .bmatch (E.plug e) bs
  | .dmatch E bs, e => .dmatch (E.plug e) bs

/-- Composition of evaluation contexts: `(E₁ ∘ E₂)[e] = E₁[E₂[e]]`. -/
def ECtx.comp {n : Nat} : ECtx n → ECtx n → ECtx n
  | .hole, E' => E'
  | .appL E e2, E' => .appL (E.comp E') e2
  | .appR vs E, E' => .appR vs (E.comp E')
  | .callB f E e2, E' => .callB f (E.comp E') e2
  | .callO f vs E, E' => .callO f vs (E.comp E')
  | .letIn xs E e2, E' => .letIn xs (E.comp E') e2
  | .bmatch E bs, E' => .bmatch (E.comp E') bs
  | .dmatch E bs, E' => .dmatch (E.comp E') bs

@[simp] theorem ECtx.plug_comp {n : Nat} (E E' : ECtx n) (e : Expr n) :
    (E.comp E').plug e = E.plug (E'.plug e) := by
  induction E <;> simp_all [comp, plug]

/-! ## Head reductions -/

/-- Find the branch for constructor `c` (with arity `k`). -/
def Branches.find {n : Nat} (bs : Branches n) (c : CName) (k : Nat) : Option (Branch n) :=
  bs.toList.find? (fun b => b.ctor == c && b.binders.length == k)

/-- The atom `True` or `False`. -/
def boolVal {n : Nat} (b : Bool) : Val n := .ctor (if b then "True" else "False") []

/-- Evaluate a primitive operation on scalar literals. -/
def PrimOp.eval : PrimOp → Int → Int → Bool
  | .lt, a, b => decide (a < b)
  | .le, a, b => decide (a ≤ b)
  | .gt, a, b => decide (a > b)
  | .ge, a, b => decide (a ≥ b)
  | .eq, a, b => decide (a = b)
  | .ne, a, b => decide (a ≠ b)

/-- Head reductions `e ⟶ e'` of Fig. 3 (plus the extensions). -/
inductive Head (sig : Sig) {n : Nat} : Expr n → Expr n → Prop where
  /-- `let x̄ = v̄ in e ⟶ e[x̄ := v̄]` -/
  | letIn (xs : List Bool) (vs : List (Val n)) (e : Expr (n + xs.length)) :
      xs.length = vs.length →
      Head sig (.letIn xs (.ret vs) e) (e.inst vs)
  /-- `f(v̄₁; v̄₂) ⟶ e[ȳ := v̄₁, x̄ := v̄₂]` with `f(ȳ; x̄) = e ∈ Σ` -/
  | call (f : FName) (fd : FunDef) (vs1 vs2 : List (Val n)) :
      sig.lookup f = some fd →
      fd.borrowed.length = vs1.length → fd.owned.length = vs2.length →
      Head sig (.call f (.ret vs1) (.ret vs2)) (fd.instBody vs1 vs2)
  /-- `(f) v̄ ⟶ e[x̄ := v̄]` with `f(; x̄) = e ∈ Σ` -/
  | app (f : FName) (fd : FunDef) (vs : List (Val n)) :
      sig.lookup f = some fd → fd.borrowed = [] → fd.owned.length = vs.length →
      Head sig (.app (.val (.fn f)) (.ret vs)) (fd.instBody [] vs)
  /-- `match (C v̄) {p ↦ e} ⟶ eᵢ[ȳ := v̄]` with `pᵢ = C ȳ` -/
  | bmatch (c : CName) (vs : List (Val n)) (bs : Branches n) (b : Branch n) :
      bs.find c vs.length = some b →
      Head sig (.bmatch (.val (.ctor c vs)) bs) (b.body.inst vs)
  /-- `match! (C v̄) {p ↦ e} ⟶ eᵢ[x̄ := v̄]` with `pᵢ = C x̄` -/
  | dmatch (c : CName) (vs : List (Val n)) (bs : Branches n) (b : Branch n) :
      bs.find c vs.length = some b →
      Head sig (.dmatch (.val (.ctor c vs)) bs) (b.body.inst vs)
  /-- `drop v; e ⟶ e` (deallocation has no effect in the functional semantics) -/
  | drop (v : Val n) (e : Expr n) : Head sig (.drop v e) e
  /-- `free k; e ⟶ e` -/
  | free (k : Nat) (e : Expr n) : Head sig (.free k e) e
  /-- primitive operations on scalar literals (extension) -/
  | prim (op : PrimOp) (a b : Int) :
      Head sig (.prim op [.lit a, .lit b]) (.val (boolVal (op.eval a b)))

/-- A tuple of values does not reduce. -/
theorem Head.not_ret {sig : Sig} {n : Nat} {vs : List (Val n)} {e : Expr n} :
    ¬ Head sig (.ret vs) e := by
  intro h; cases h

/-- The small-step relation `E[e₁] ↦ E[e₂]` (rule *step*). -/
inductive Step (sig : Sig) {n : Nat} : Expr n → Expr n → Prop where
  | step (E : ECtx n) (e1 e2 : Expr n) : Head sig e1 e2 → Step sig (E.plug e1) (E.plug e2)

/-- The reflexive-transitive closure `↦*`. -/
abbrev Steps (sig : Sig) {n : Nat} := Relation.ReflTransGen (Step sig (n := n))

theorem Step.head {sig : Sig} {n : Nat} {e1 e2 : Expr n} (h : Head sig e1 e2) :
    Step sig e1 e2 :=
  Step.step .hole e1 e2 h

theorem Step.ctx {sig : Sig} {n : Nat} {e1 e2 : Expr n} (E : ECtx n) (h : Step sig e1 e2) :
    Step sig (E.plug e1) (E.plug e2) := by
  cases h with
  | step E' a b hab => simpa using Step.step (E.comp E') a b hab

theorem Steps.ctx {sig : Sig} {n : Nat} {e1 e2 : Expr n} (E : ECtx n) (h : Steps sig e1 e2) :
    Steps sig (E.plug e1) (E.plug e2) := by
  induction h with
  | refl => exact .refl
  | tail _ h ih => exact ih.tail (h.ctx E)

/-! ## A small-step interpreter

`Expr.step?` computes the unique reduct of an expression (if any). It is used to run
the examples of the paper; `Expr.step?_sound` shows that it agrees with `Step`. -/

/-- One head-reduction step, if the expression is a redex. -/
def headStep? (sig : Sig) {n : Nat} : Expr n → Option (Expr n)
  | .letIn xs (.ret vs) e =>
      if xs.length = vs.length then some (e.inst vs) else none
  | .call f (.ret vs1) (.ret vs2) =>
      match sig.lookup f with
      | some fd =>
        if fd.borrowed.length = vs1.length ∧ fd.owned.length = vs2.length then
          some (fd.instBody vs1 vs2)
        else none
      | none => none
  | .app (.ret [.fn f]) (.ret vs) =>
      match sig.lookup f with
      | some fd =>
        if fd.borrowed = [] ∧ fd.owned.length = vs.length then
          some (fd.instBody [] vs)
        else none
      | none => none
  | .bmatch (.ret [.ctor c vs]) bs =>
      match bs.find c vs.length with
      | some b => some (b.body.inst vs)
      | none => none
  | .dmatch (.ret [.ctor c vs]) bs =>
      match bs.find c vs.length with
      | some b => some (b.body.inst vs)
      | none => none
  | .drop _ e => some e
  | .free _ e => some e
  | .prim op [.lit a, .lit b] => some (.val (boolVal (op.eval a b)))
  | _ => none

theorem headStep?_sound {sig : Sig} {n : Nat} {e e' : Expr n} (h : headStep? sig e = some e') :
    Head sig e e' := by
  unfold headStep? at h
  split at h <;> (try simp_all) <;> (try split at h) <;> (try simp_all)
  all_goals (try obtain ⟨_, rfl⟩ := h)
  all_goals (constructor <;> simp_all)

/-- One step of the functional semantics, if the expression is not stuck or final. -/
def Expr.step? (sig : Sig) {n : Nat} (e : Expr n) : Option (Expr n) :=
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

theorem Expr.step?_sound {sig : Sig} {n : Nat} :
    ∀ {e e' : Expr n}, e.step? sig = some e' → Step sig e e'
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
def Expr.run (sig : Sig) {n : Nat} : Nat → Expr n → Expr n
  | 0, e => e
  | k + 1, e => match e.step? sig with
    | some e' => Expr.run sig k e'
    | none => e

theorem Expr.run_sound (sig : Sig) {n : Nat} (k : Nat) (e : Expr n) :
    Steps sig e (e.run sig k) := by
  induction k generalizing e with
  | zero => exact .refl
  | succ k ih =>
    simp only [Expr.run]
    split
    · next e' h => exact Relation.ReflTransGen.head (Expr.step?_sound h) (ih e')
    · exact .refl

/-- Evaluate an expression to an unboxed tuple of values, using at most `fuel` steps. -/
def Expr.eval (sig : Sig) {n : Nat} (fuel : Nat) (e : Expr n) : Option (List (Val n)) :=
  match e.run sig fuel with
  | .ret vs => some vs
  | _ => none

theorem Expr.eval_sound {sig : Sig} {n : Nat} {fuel : Nat} {e : Expr n} {vs : List (Val n)}
    (h : e.eval sig fuel = some vs) : Steps sig e (.ret vs) := by
  unfold Expr.eval at h
  split at h
  · next h' => simp at h; rw [← h, ← h']; exact Expr.run_sound sig fuel e
  · simp at h

end FIP

/- ══════════════════ PAPER sec. 2.1 END: Functional Operational Semantics ══════════════════ -/
