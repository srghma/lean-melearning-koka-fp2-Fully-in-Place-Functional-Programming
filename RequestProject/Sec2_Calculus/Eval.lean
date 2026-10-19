module

public import RequestProject.Sec2_Calculus.Semantics

@[expose] public section

/-!
# A fuel-free, terminating evaluator

The interpreter `Expr.run` of `Semantics.lean` takes a number of steps (*fuel*), because a
program of the calculus need not terminate: general recursion is allowed, even in `fip`
functions (`fip fun loop(x) = loop(x)` is fully in-place).  So no total function can
evaluate *every* expression to a value.

What can be done is to ask for a **proof of termination** instead of fuel:

* `Expr.Halts sig e` — `e` reduces to an unboxed tuple of values in the functional
  semantics of Fig. 3: `∃ vs, e ⟼* (vs)`.  The definition mentions no fuel;
  `Expr.halts_iff_run` relates it to the interpreter;
* `Expr.evalTotal sig e h : List (Val n)` — the result, with no fuel and no `Option`.
  It is defined by **well-founded recursion on the reduction of `e`**: it performs one
  step of the semantics (`Expr.step?`) after the other, and terminates because `e` halts
  (`Expr.acc_of_halts`: there is no infinite reduction from a halting expression).
  `Expr.evalTotal_sound` shows `e ⟼* (e.evalTotal sig h)`, and `Expr.evalTotal_unique`
  that it is the only such result.

`Expr.evalTotal_eq_run` relates it to the fuel-based interpreter, which is how concrete
results are computed by the kernel: any amount of fuel that is enough gives the same
answer.
-/

namespace FIP

variable {sig : Sig} {n : Nat}

/-- Is this expression an unboxed tuple of values? -/
def Expr.isRet : Expr n → Bool
  | .ret _ => true
  | _ => false

/-- The values of an unboxed tuple (and `[]` for any other expression). -/
def Expr.rets : Expr n → List (Val n)
  | .ret vs => vs
  | _ => []

@[simp] theorem Expr.step?_ret (vs : List (Val n)) : (Expr.ret vs).step? sig = none := by
  unfold Expr.step?; simp [headStep?]

@[simp] theorem Expr.run_ret (vs : List (Val n)) (k : Nat) :
    (Expr.ret vs).run sig k = .ret vs := by
  cases k <;> simp [Expr.run]

theorem Expr.run_add (e : Expr n) (k j : Nat) :
    e.run sig (k + j) = (e.run sig k).run sig j := by
  induction k generalizing e with
  | zero => simp [Expr.run]
  | succ k ih =>
    rw [Nat.add_right_comm]
    simp only [Expr.run]
    split
    · exact ih _
    · next h => cases j <;> simp [Expr.run, h]

theorem Expr.isRet_iff {e : Expr n} : e.isRet = true ↔ e = .ret e.rets := by
  cases e <;> simp [Expr.isRet, Expr.rets]

/-- Once the interpreter has reached a tuple of values, more fuel changes nothing. -/
theorem Expr.run_of_isRet {e : Expr n} {k j : Nat} (h : (e.run sig k).isRet = true)
    (hkj : k ≤ j) : e.run sig j = e.run sig k := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkj
  rw [Expr.run_add, Expr.isRet_iff.mp h]
  simp

/-! ## Completeness of the interpreter

`Expr.step?` finds *the* reduct of every reducible expression, so the semantics is
deterministic, and a reduction to a value is found by the interpreter. -/

/-- `headStep?` finds every head reduction. -/
theorem headStep?_complete {e e' : Expr n} (h : Head sig e e') : headStep? sig e = some e' := by
  cases h <;> simp_all [headStep?]

theorem ECtx.plug_head_ne_ret {e e' : Expr n} (h : Head sig e e') (E : ECtx n)
    (vs : List (Val n)) : E.plug e ≠ .ret vs := by
  cases E <;> simp only [ECtx.plug, ne_eq, reduceCtorEq, not_false_eq_true]
  rintro rfl
  exact Head.not_ret h

theorem Expr.step?_plug {e e' : Expr n} (h : Head sig e e') (E : ECtx n) :
    (E.plug e).step? sig = some (E.plug e') := by
  induction E with
  | hole => unfold Expr.step?; simp [headStep?_complete h, ECtx.plug]
  | appL E _ ih | appR _ E ih | callB _ E _ ih | callO _ _ E ih | letIn _ E _ ih
  | bmatch E _ ih | dmatch E _ ih =>
    unfold Expr.step?
    have hne := ECtx.plug_head_ne_ret h E
    simp only [ECtx.plug]
    split
    · next hh => exfalso; unfold headStep? at hh; split at hh <;> simp_all
    · simp_all

/-- `Expr.step?` finds every step. -/
theorem Expr.step?_complete {e e' : Expr n} (h : Step sig e e') : e.step? sig = some e' := by
  cases h with
  | step E a b hab => exact Expr.step?_plug hab E

/-- The functional semantics is deterministic. -/
theorem Step.deterministic {e e₁ e₂ : Expr n} (h₁ : Step sig e e₁) (h₂ : Step sig e e₂) :
    e₁ = e₂ := by
  have := (Expr.step?_complete h₁).symm.trans (Expr.step?_complete h₂)
  simpa using this

/-- A reduction sequence to a value is found by the interpreter. -/
theorem Expr.run_of_steps {e : Expr n} {vs : List (Val n)} (hs : Steps sig e (.ret vs)) :
    ∃ k, e.run sig k = .ret vs := by
  induction hs using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, rfl⟩
  | head hst _ ih =>
    obtain ⟨k, hk⟩ := ih
    exact ⟨k + 1, by simp [Expr.run, Expr.step?_complete hst, hk]⟩

/-- An expression reduces to at most one tuple of values. -/
theorem Steps.ret_unique {e : Expr n} {vs ws : List (Val n)} (h₁ : Steps sig e (.ret vs))
    (h₂ : Steps sig e (.ret ws)) : vs = ws := by
  obtain ⟨k₁, hk₁⟩ := Expr.run_of_steps h₁
  obtain ⟨k₂, hk₂⟩ := Expr.run_of_steps h₂
  have e₁ := Expr.run_of_isRet (sig := sig) (e := e) (by simp [hk₁, Expr.isRet])
    (le_max_left k₁ k₂)
  have e₂ := Expr.run_of_isRet (sig := sig) (e := e) (by simp [hk₂, Expr.isRet])
    (le_max_right k₁ k₂)
  rw [hk₁] at e₁
  rw [hk₂] at e₂
  simpa using e₁.symm.trans e₂

/-! ## Termination -/

/-- The expression `e` terminates: it reduces to an unboxed tuple of values in the
    functional semantics (Fig. 3).  No fuel is involved. -/
def Expr.Halts (sig : Sig) (e : Expr n) : Prop := ∃ vs, Steps sig e (.ret vs)

/-- `Halts` is termination in the functional semantics (by definition). -/
theorem Expr.halts_iff {e : Expr n} : e.Halts sig ↔ ∃ vs, Steps sig e (.ret vs) := Iff.rfl

/-- If the interpreter reaches a tuple of values, the expression halts. -/
theorem Expr.Halts.of_run {e : Expr n} {k : Nat} (hk : (e.run sig k).isRet = true) :
    e.Halts sig := by
  have := Expr.run_sound sig k e
  rw [Expr.isRet_iff.mp hk] at this
  exact ⟨_, this⟩

/-- An expression halts iff the interpreter reaches a tuple of values. -/
theorem Expr.halts_iff_run {e : Expr n} : e.Halts sig ↔ ∃ k, (e.run sig k).isRet = true := by
  refine ⟨fun ⟨vs, hs⟩ => ?_, fun ⟨k, hk⟩ => Expr.Halts.of_run hk⟩
  obtain ⟨k, hk⟩ := Expr.run_of_steps hs
  exact ⟨k, by simp [hk, Expr.isRet]⟩

/-- A halting expression that is not a value steps to a halting expression. -/
theorem Expr.Halts.step {e e' : Expr n} (h : e.Halts sig) (hs : e.step? sig = some e') :
    e'.Halts sig := by
  obtain ⟨vs, hvs⟩ := h
  rcases Relation.ReflTransGen.cases_head hvs with rfl | ⟨e'', h1, h2⟩
  · simp at hs
  · rw [Step.deterministic h1 (Expr.step?_sound hs)] at h2
    exact ⟨vs, h2⟩

/-- A halting expression that does not step is a value. -/
theorem Expr.Halts.eq_ret {e : Expr n} (h : e.Halts sig) (hs : e.step? sig = none) :
    e = .ret e.rets := by
  obtain ⟨vs, hvs⟩ := h
  rcases Relation.ReflTransGen.cases_head hvs with rfl | ⟨e'', h1, _⟩
  · rfl
  · simp [Expr.step?_complete h1] at hs

/-- A halting expression, as a subject of well-founded recursion. -/
structure HaltingExpr (sig : Sig) (n : Nat) where
  expr : Expr n
  halts : expr.Halts sig

/-- There is no infinite reduction from an expression the interpreter brings to a value. -/
theorem Expr.acc_of_run {k : Nat} : ∀ {e : Expr n}, (e.run sig k).isRet = true →
    Acc (fun a b : Expr n => b.step? sig = some a) e := by
  induction k with
  | zero =>
    intro e hk
    refine ⟨_, fun a ha => ?_⟩
    have he : e = .ret e.rets := Expr.isRet_iff.mp hk
    rw [he] at ha
    simp at ha
  | succ k ih =>
    intro e hk
    refine ⟨_, fun a ha => ih ?_⟩
    simpa [Expr.run, ha] using hk

/-- There is no infinite reduction from a halting expression. -/
theorem Expr.acc_of_halts {e : Expr n} (h : e.Halts sig) :
    Acc (fun a b : Expr n => b.step? sig = some a) e := by
  obtain ⟨k, hk⟩ := Expr.halts_iff_run.mp h
  exact Expr.acc_of_run hk

/-- Reduction is well-founded on halting expressions. -/
instance (sig : Sig) (n : Nat) : WellFoundedRelation (HaltingExpr sig n) where
  rel a b := b.expr.step? sig = some a.expr
  wf := ⟨fun a => InvImage.accessible HaltingExpr.expr (Expr.acc_of_halts a.halts)⟩

/-- The result of a terminating expression: perform steps of the semantics until a tuple
    of values is reached.  No fuel is needed: the recursion is well-founded because the
    expression halts. -/
def Expr.evalTotal (sig : Sig) (e : Expr n) (h : e.Halts sig) : List (Val n) :=
  match hs : e.step? sig with
  | none => e.rets
  | some e' => Expr.evalTotal sig e' (h.step hs)
termination_by HaltingExpr.mk e h
decreasing_by exact hs

/-- The total evaluator is sound: `e ⟼* (evalTotal e)`. -/
theorem Expr.evalTotal_sound {e : Expr n} (h : e.Halts sig) :
    Steps sig e (.ret (e.evalTotal sig h)) := by
  induction Expr.acc_of_halts h with
  | intro e _ ih =>
    rw [Expr.evalTotal]
    split
    · next hs =>
      rw [← h.eq_ret hs]
    · next e' hs =>
      exact Relation.ReflTransGen.head (Expr.step?_sound hs) (ih e' hs (h.step hs))

/-- The result of a terminating expression is unique. -/
theorem Expr.evalTotal_unique {e : Expr n} (h : e.Halts sig) {vs : List (Val n)}
    (hs : Steps sig e (.ret vs)) : e.evalTotal sig h = vs :=
  Steps.ret_unique (Expr.evalTotal_sound h) hs

/-- The result does not depend on how much fuel is used, provided it is enough. -/
theorem Expr.evalTotal_eq_run {e : Expr n} (h : e.Halts sig) {k : Nat}
    (hk : (e.run sig k).isRet = true) : e.evalTotal sig h = (e.run sig k).rets := by
  apply Expr.evalTotal_unique
  have := Expr.run_sound sig k e
  rwa [Expr.isRet_iff.mp hk] at this

/-- A successful run of the fuel-based evaluator proves termination. -/
theorem Expr.Halts.of_eval {e : Expr n} {fuel : Nat} {vs : List (Val n)}
    (he : e.eval sig fuel = some vs) : e.Halts sig :=
  ⟨vs, Expr.eval_sound he⟩

/-- The total evaluator agrees with the fuel-based one whenever the latter succeeds. -/
theorem Expr.evalTotal_eq_of_eval {e : Expr n} {fuel : Nat} {vs : List (Val n)}
    (he : e.eval sig fuel = some vs) (h : e.Halts sig) : e.evalTotal sig h = vs :=
  Expr.evalTotal_unique h (Expr.eval_sound he)

/-- An expression that steps to itself does not terminate. -/
theorem Expr.not_halts_of_step_self {e : Expr n} (h : e.step? sig = some e) :
    ¬ e.Halts sig := by
  intro hh
  obtain ⟨k, hk⟩ := Expr.halts_iff_run.mp hh
  have hrun : ∀ k, e.run sig k = e := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => simp [Expr.run, h, ih]
  rw [hrun, Expr.isRet_iff] at hk
  rw [hk] at h
  simp at h

end FIP

/-- `fip_halts` proves `e.Halts sig` for a concrete closed expression by running the
    interpreter in the kernel, for at most a million steps (the steps are only used to
    find the proof; `Expr.Halts` and `Expr.evalTotal` involve no fuel). -/
macro "fip_halts" : tactic =>
  `(tactic| exact FIP.Expr.Halts.of_run (k := 1000000) (by decide +kernel))
