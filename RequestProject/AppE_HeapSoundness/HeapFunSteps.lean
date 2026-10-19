module

public import RequestProject.AppE_HeapSoundness.HeapAdm

@[expose] public section

/-!
# Counted reductions of the functional semantics of `λfip` and their inversion

Auxiliary facts about the functional semantics `LStep` used in the proof of Theorem 6:

* reductions counted by their length (`LStepsN`);
* composition of evaluation contexts (`LECtx.comp`);
* **unique decomposition**: a reduction of `E[e]` to a value factors through a reduction
  of `e` to a value (`LStepsN.plug_inv`);
* the first step of an expression whose evaluation positions hold values is a head
  reduction (`LStepsN.head_inv`).
-/

namespace FIP.Lam

/-- `e ⟼ⁿ e'`: a functional reduction of length `n`. -/
inductive LStepsN (sig : LSig) : Nat → LExpr 0 → LExpr 0 → Prop where
  | refl (e : LExpr 0) : LStepsN sig 0 e e
  | step {n : Nat} {e1 e2 e3 : LExpr 0} : LStep sig e1 e2 → LStepsN sig n e2 e3 →
      LStepsN sig (n + 1) e1 e3

theorem LStepsN.of_steps {sig : LSig} {e e' : LExpr 0} (h : LSteps sig e e') :
    ∃ n, LStepsN sig n e e' := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, .refl _⟩
  | head h _ ih => obtain ⟨n, hn⟩ := ih; exact ⟨n + 1, .step h hn⟩

/-! ## Evaluation contexts -/

/-- `E[F]`: the composition of evaluation contexts. -/
def LECtx.comp : LECtx → LECtx → LECtx
  | .hole, F => F
  | .appL E e, F => .appL (E.comp F) e
  | .appR vs E, F => .appR vs (E.comp F)
  | .callB f E e, F => .callB f (E.comp F) e
  | .callO f vs E, F => .callO f vs (E.comp F)
  | .letIn k E e, F => .letIn k (E.comp F) e

theorem LECtx.plug_comp : ∀ (E F : LECtx) (e : LExpr 0), (E.comp F).plug e = E.plug (F.plug e)
  | .hole, _, _ => rfl
  | .appL E _, F, e => by simp [LECtx.comp, LECtx.plug, LECtx.plug_comp E F e]
  | .appR _ E, F, e => by simp [LECtx.comp, LECtx.plug, LECtx.plug_comp E F e]
  | .callB _ E _, F, e => by simp [LECtx.comp, LECtx.plug, LECtx.plug_comp E F e]
  | .callO _ _ E, F, e => by simp [LECtx.comp, LECtx.plug, LECtx.plug_comp E F e]
  | .letIn _ E _, F, e => by simp [LECtx.comp, LECtx.plug, LECtx.plug_comp E F e]

theorem LECtx.plug_eq_ret {E : LECtx} {e : LExpr 0} {vs : LVals 0} (h : E.plug e = .ret vs) :
    E = .hole ∧ e = .ret vs := by
  cases E <;> simp_all [LECtx.plug]

theorem LHead.not_ret {sig : LSig} {vs : LVals 0} {e : LExpr 0} : ¬ LHead sig (.ret vs) e := by
  intro h; cases h

/-- A head redex inside an evaluation context: either the plugged expression is a value,
    or the redex lies inside it. -/
theorem LECtx.decomp {sig : LSig} {r r' : LExpr 0} (hr : LHead sig r r') :
    ∀ (E E₂ : LECtx) (e : LExpr 0), E.plug e = E₂.plug r →
      (∃ vs, e = .ret vs) ∨ ∃ E₃, E₂ = E.comp E₃ ∧ e = E₃.plug r := by
  intro E
  induction E with
  | hole => intro E₂ e h; exact .inr ⟨E₂, rfl, h⟩
  | appL E e2 ih =>
    intro E₂ e h
    cases E₂ with
    | hole =>
      simp only [LECtx.plug] at h
      cases hr <;> simp only [LExpr.app.injEq, reduceCtorEq, false_and, and_false] at h
      all_goals (obtain ⟨rfl, rfl⟩ := LECtx.plug_eq_ret h.1; exact .inl ⟨_, rfl⟩)
    | appL E₂ e2' =>
      simp only [LECtx.plug, LExpr.app.injEq] at h
      rcases ih E₂ e h.1 with h' | ⟨E₃, rfl, h'⟩
      · exact .inl h'
      · exact .inr ⟨E₃, by simp [LECtx.comp, h.2], h'⟩
    | appR vs E₂ =>
      simp only [LECtx.plug, LExpr.app.injEq] at h
      obtain ⟨rfl, rfl⟩ := LECtx.plug_eq_ret h.1; exact .inl ⟨_, rfl⟩
    | _ => simp [LECtx.plug] at h
  | appR vs E ih =>
    intro E₂ e h
    cases E₂ with
    | hole =>
      simp only [LECtx.plug] at h
      cases hr <;> simp only [LExpr.app.injEq, reduceCtorEq, false_and, and_false] at h
      all_goals (obtain ⟨rfl, rfl⟩ := LECtx.plug_eq_ret h.2; exact .inl ⟨_, rfl⟩)
    | appL E₂ e2' =>
      simp only [LECtx.plug, LExpr.app.injEq] at h
      obtain ⟨rfl, rfl⟩ := LECtx.plug_eq_ret h.1.symm; exact absurd hr LHead.not_ret
    | appR vs' E₂ =>
      simp only [LECtx.plug, LExpr.app.injEq, LExpr.ret.injEq] at h
      rcases ih E₂ e h.2 with h' | ⟨E₃, rfl, h'⟩
      · exact .inl h'
      · exact .inr ⟨E₃, by simp [LECtx.comp, h.1], h'⟩
    | _ => simp [LECtx.plug] at h
  | callB f E e2 ih =>
    intro E₂ e h
    cases E₂ with
    | hole =>
      simp only [LECtx.plug] at h
      cases hr <;> simp only [LExpr.call.injEq, reduceCtorEq, false_and, and_false] at h
      all_goals (obtain ⟨rfl, rfl⟩ := LECtx.plug_eq_ret h.2.1; exact .inl ⟨_, rfl⟩)
    | callB f' E₂ e2' =>
      simp only [LECtx.plug, LExpr.call.injEq] at h
      rcases ih E₂ e h.2.1 with h' | ⟨E₃, rfl, h'⟩
      · exact .inl h'
      · exact .inr ⟨E₃, by simp [LECtx.comp, h.1, h.2.2], h'⟩
    | callO f' vs E₂ =>
      simp only [LECtx.plug, LExpr.call.injEq] at h
      obtain ⟨rfl, rfl⟩ := LECtx.plug_eq_ret h.2.1; exact .inl ⟨_, rfl⟩
    | _ => simp [LECtx.plug] at h
  | callO f vs E ih =>
    intro E₂ e h
    cases E₂ with
    | hole =>
      simp only [LECtx.plug] at h
      cases hr <;> simp only [LExpr.call.injEq, reduceCtorEq, false_and, and_false] at h
      all_goals (obtain ⟨rfl, rfl⟩ := LECtx.plug_eq_ret h.2.2; exact .inl ⟨_, rfl⟩)
    | callB f' E₂ e2' =>
      simp only [LECtx.plug, LExpr.call.injEq] at h
      obtain ⟨rfl, rfl⟩ := LECtx.plug_eq_ret h.2.1.symm; exact absurd hr LHead.not_ret
    | callO f' vs' E₂ =>
      simp only [LECtx.plug, LExpr.call.injEq, LExpr.ret.injEq] at h
      rcases ih E₂ e h.2.2 with h' | ⟨E₃, rfl, h'⟩
      · exact .inl h'
      · exact .inr ⟨E₃, by simp [LECtx.comp, h.1, h.2.1], h'⟩
    | _ => simp [LECtx.plug] at h
  | letIn k E e2 ih =>
    intro E₂ e h
    cases E₂ with
    | hole =>
      simp only [LECtx.plug] at h
      cases hr <;> simp only [LExpr.letIn.injEq, reduceCtorEq, false_and, and_false] at h
      all_goals (obtain ⟨rfl, rfl⟩ := LECtx.plug_eq_ret h.2.1; exact .inl ⟨_, rfl⟩)
    | letIn k' E₂ e2' =>
      simp only [LECtx.plug, LExpr.letIn.injEq] at h
      obtain ⟨rfl, h1, h2⟩ := h
      rcases ih E₂ e h1 with h' | ⟨E₃, rfl, h'⟩
      · exact .inl h'
      · exact .inr ⟨E₃, by simp [LECtx.comp, eq_of_heq h2], h'⟩
    | _ => simp [LECtx.plug] at h

/-- A step of `E[e]`: either `e` is a value, or `e` steps. -/
theorem LStep.plug_inv {sig : LSig} {E : LECtx} {e e'' : LExpr 0} (h : LStep sig (E.plug e) e'') :
    (∃ vs, e = .ret vs) ∨ ∃ e', LStep sig e e' ∧ e'' = E.plug e' := by
  generalize hx : E.plug e = x at h
  cases h with
  | step E₂ hh =>
    rcases LECtx.decomp hh E E₂ e hx with h' | ⟨E₃, rfl, rfl⟩
    · exact .inl h'
    · exact .inr ⟨_, LStep.step E₃ hh, (LECtx.plug_comp _ _ _)⟩

theorem LStep.not_ret {sig : LSig} {vs : LVals 0} {e : LExpr 0} : ¬ LStep sig (.ret vs) e := by
  intro h
  generalize hx : LExpr.ret vs = x at h
  cases h with
  | step E hh =>
    obtain ⟨rfl, rfl⟩ := LECtx.plug_eq_ret hx.symm
    exact LHead.not_ret hh

theorem LStepsN.ret_inv {sig : LSig} {n : Nat} {vs : LVals 0} {e : LExpr 0}
    (h : LStepsN sig n (.ret vs) e) : n = 0 ∧ e = .ret vs := by
  cases h with
  | refl => exact ⟨rfl, rfl⟩
  | step hs _ => exact absurd hs LStep.not_ret

/-- **Unique decomposition**: a reduction of `E[e]` to a value first reduces `e` to a
    value. -/
theorem LStepsN.plug_inv {sig : LSig} {E : LECtx} :
    ∀ {n : Nat} {e : LExpr 0} {vs : LVals 0}, LStepsN sig n (E.plug e) (.ret vs) →
      ∃ n₁ ws, n₁ ≤ n ∧ LStepsN sig n₁ e (.ret ws) ∧
        LStepsN sig (n - n₁) (E.plug (.ret ws)) (.ret vs)
  | 0, e, vs, h => by
    generalize hx : E.plug e = x at h
    cases h with
    | refl =>
      obtain ⟨rfl, rfl⟩ := LECtx.plug_eq_ret hx
      exact ⟨0, vs, le_rfl, .refl _, .refl _⟩
  | n + 1, e, vs, h => by
    cases h with
    | step hs hr =>
      rcases LStep.plug_inv hs with ⟨ws, rfl⟩ | ⟨e', he', rfl⟩
      · exact ⟨0, ws, Nat.zero_le _, .refl _, .step hs hr⟩
      · obtain ⟨n₁, ws, hn, h1, h2⟩ := LStepsN.plug_inv hr
        refine ⟨n₁ + 1, ws, by omega, .step he' h1, ?_⟩
        rwa [show n + 1 - (n₁ + 1) = n - n₁ by omega]

/-! ## Head reductions -/

/-- The evaluation positions of an expression hold values: every evaluation context in
    which it is a non-trivial plug is filled with a value. -/
def LExpr.Ready (e : LExpr 0) : Prop :=
  ∀ (E : LECtx) (r : LExpr 0), E ≠ .hole → E.plug r = e → ∃ vs, r = .ret vs

theorem LStep.head_of_ready {sig : LSig} {e e' : LExpr 0} (he : e.Ready) (h : LStep sig e e') :
    LHead sig e e' := by
  cases h with
  | step E hh =>
    by_cases hE : E = .hole
    · subst hE; exact hh
    · obtain ⟨vs, rfl⟩ := he E _ hE rfl
      exact absurd hh LHead.not_ret

/-- The first step of a reduction to a value of a ready expression which is not a value is
    a head reduction. -/
theorem LStepsN.head_inv {sig : LSig} {n : Nat} {e : LExpr 0} {vs : LVals 0}
    (he : e.Ready) (hne : ∀ ws, e ≠ .ret ws) (h : LStepsN sig n e (.ret vs)) :
    ∃ n' e', n = n' + 1 ∧ LHead sig e e' ∧ LStepsN sig n' e' (.ret vs) := by
  cases h with
  | refl => exact absurd rfl (hne vs)
  | step hs hr => exact ⟨_, _, rfl, LStep.head_of_ready he hs, hr⟩

theorem LExpr.ready_letIn (k : Nat) (vs : LVals 0) (e : LExpr (0 + k)) :
    (LExpr.letIn k (.ret vs) e).Ready := by
  intro E r hE h
  cases E with
  | hole => exact absurd rfl hE
  | letIn k' E e' =>
    simp only [LECtx.plug, LExpr.letIn.injEq] at h
    obtain ⟨rfl, h1, -⟩ := h
    obtain ⟨rfl, rfl⟩ := LECtx.plug_eq_ret h1; exact ⟨_, rfl⟩
  | _ => simp [LECtx.plug] at h

theorem LExpr.ready_call (f : FName) (vs ws : LVals 0) :
    (LExpr.call f (.ret vs) (.ret ws)).Ready := by
  intro E r hE h
  cases E with
  | hole => exact absurd rfl hE
  | callB f' E e' =>
    simp only [LECtx.plug, LExpr.call.injEq] at h
    obtain ⟨rfl, rfl⟩ := LECtx.plug_eq_ret h.2.1; exact ⟨_, rfl⟩
  | callO f' vs' E =>
    simp only [LECtx.plug, LExpr.call.injEq] at h
    obtain ⟨rfl, rfl⟩ := LECtx.plug_eq_ret h.2.2; exact ⟨_, rfl⟩
  | _ => simp [LECtx.plug] at h

theorem LExpr.ready_app (vs ws : LVals 0) : (LExpr.app (.ret vs) (.ret ws)).Ready := by
  intro E r hE h
  cases E with
  | hole => exact absurd rfl hE
  | appL E e' =>
    simp only [LECtx.plug, LExpr.app.injEq] at h
    obtain ⟨rfl, rfl⟩ := LECtx.plug_eq_ret h.1; exact ⟨_, rfl⟩
  | appR vs' E =>
    simp only [LECtx.plug, LExpr.app.injEq] at h
    obtain ⟨rfl, rfl⟩ := LECtx.plug_eq_ret h.2; exact ⟨_, rfl⟩
  | _ => simp [LECtx.plug] at h

theorem LExpr.ready_other {e : LExpr 0}
    (h : (∀ vs, e ≠ .ret vs) ∧ (∀ a b, e ≠ .app a b) ∧ (∀ f a b, e ≠ .call f a b) ∧
      (∀ k a b, e ≠ .letIn k a b)) : e.Ready := by
  intro E r hE h'
  cases E with
  | hole => exact absurd rfl hE
  | appL E e' => exact absurd h'.symm (h.2.1 _ _)
  | appR vs' E => exact absurd h'.symm (h.2.1 _ _)
  | callB f' E e' => exact absurd h'.symm (h.2.2.1 _ _ _)
  | callO f' vs' E => exact absurd h'.symm (h.2.2.1 _ _ _)
  | letIn k' E e' => exact absurd h'.symm (h.2.2.2 _ _ _)

/-- A reduction to a value of `dups v̄ e` first discards the `dup`s. -/
theorem LStepsN.dups_inv {sig : LSig} :
    ∀ (ws : List (LVal 0)) {n : Nat} {e : LExpr 0} {vs : LVals 0},
      LStepsN sig n (dups ws e) (.ret vs) → ∃ n', n = n' + ws.length ∧ LStepsN sig n' e (.ret vs)
  | [], n, e, vs, h => ⟨n, rfl, h⟩
  | w :: ws, n, e, vs, h => by
    obtain ⟨n', e', rfl, hh, hr⟩ := LStepsN.head_inv
      (LExpr.ready_other ⟨by simp [dups], by simp [dups], by simp [dups], by simp [dups]⟩)
      (by simp [dups]) h
    cases hh
    obtain ⟨n'', rfl, h''⟩ := LStepsN.dups_inv ws hr
    exact ⟨n'', by simp; omega, h''⟩

end FIP.Lam
