module

public import RequestProject.Named.AppE_HeapSoundness.HeapRename

@[expose] public section

/-!
# Counted reductions of the functional semantics of `λfip` and their inversion

Auxiliary facts used in the proof of Theorem 6: reductions counted by their length, values
do not reduce, a reduction of `E[e]` to a value factors through a reduction of `e` to a
value, and a redex reduces by a head step.  We also show that the heap semantics is closed
under evaluation contexts.
-/

namespace FIPNamed.Lam

variable {sig : LSig}

/-- `e ⟼ⁿ e'`: a reduction of length `n`. -/
inductive LStepsN (sig : LSig) : Nat → LExpr → LExpr → Prop where
  | refl (e : LExpr) : LStepsN sig 0 e e
  | step {n : Nat} {e1 e2 e3 : LExpr} : LStep sig e1 e2 → LStepsN sig n e2 e3 →
      LStepsN sig (n + 1) e1 e3

theorem LStepsN.of_steps {e e' : LExpr} (h : LSteps sig e e') : ∃ n, LStepsN sig n e e' := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, .refl _⟩
  | head h _ ih => obtain ⟨n, hn⟩ := ih; exact ⟨n + 1, .step h hn⟩

theorem LHead.not_ret {vs : List LVal} {e : LExpr} : ¬ LHead sig (.ret vs) e := by
  intro h; cases h

theorem LECtx.plug_eq_ret {E : LECtx} {e : LExpr} {vs : List LVal} (h : E.plug e = .ret vs) :
    E = .hole ∧ e = .ret vs := by
  cases E <;> simp_all [LECtx.plug]

theorem LStep.not_ret {vs : List LVal} {e : LExpr} : ¬ LStep sig (.ret vs) e := by
  intro h
  generalize he : LExpr.ret vs = e0 at h
  cases h with
  | step E hab =>
    obtain ⟨rfl, rfl⟩ := LECtx.plug_eq_ret he.symm
    exact LHead.not_ret hab

theorem LStepsN.ret_inv {n : Nat} {vs : List LVal} {e : LExpr}
    (h : LStepsN sig n (.ret vs) e) : n = 0 ∧ e = .ret vs := by
  cases h with
  | refl => exact ⟨rfl, rfl⟩
  | step hs _ => exact absurd hs LStep.not_ret

theorem LStepsN.ret_ret {n : Nat} {vs ws : List LVal}
    (h : LStepsN sig n (.ret vs) (.ret ws)) : n = 0 ∧ vs = ws := by
  obtain ⟨h1, h2⟩ := h.ret_inv
  exact ⟨h1, by injection h2.symm⟩

/-- An expression is a value. -/
def LExpr.IsRet : LExpr → Prop
  | .ret _ => True
  | _ => False

theorem LHead.not_isRet {e e' : LExpr} (h : LHead sig e e') : ¬ e.IsRet := by
  cases h <;> simp [LExpr.IsRet]

theorem LECtx.plug_not_isRet {E : LECtx} {e : LExpr} (h : ¬ e.IsRet) : ¬ (E.plug e).IsRet := by
  cases E <;> simp_all [LECtx.plug, LExpr.IsRet]

theorem LECtx.plug_isRet {E : LECtx} {e : LExpr} (h : (E.plug e).IsRet) : E = .hole := by
  cases E <;> simp_all [LECtx.plug, LExpr.IsRet]

theorem LHead.app_isRet {e1 e2 b : LExpr} (h : LHead sig (.app e1 e2) b) :
    e1.IsRet ∧ e2.IsRet := by
  cases h <;> simp [LExpr.IsRet]

theorem LHead.call_isRet {f : FName} {e1 e2 b : LExpr} (h : LHead sig (.call f e1 e2) b) :
    e1.IsRet ∧ e2.IsRet := by
  cases h; simp [LExpr.IsRet]

theorem LHead.letIn_isRet {xs : List Binder} {e1 e2 b : LExpr}
    (h : LHead sig (.letIn xs e1 e2) b) : e1.IsRet := by
  cases h; simp [LExpr.IsRet]

theorem LHead.plug_not_ret {F : LECtx} {a b : LExpr} {vs : List LVal} (h : LHead sig a b)
    (he : F.plug a = .ret vs) : False := by
  obtain ⟨rfl, rfl⟩ := LECtx.plug_eq_ret he
  exact LHead.not_ret h

theorem LECtx.plug_ne_ret {E : LECtx} {e : LExpr} {vs : List LVal} (hne : ¬ e.IsRet)
    (he : E.plug e = .ret vs) : False := by
  obtain ⟨rfl, rfl⟩ := LECtx.plug_eq_ret he
  exact hne trivial

/-- A step of `E[e]`, for `e` not a value, is a step of `e`. -/
theorem LStep.plug_inv : ∀ (E : LECtx) {e t : LExpr}, ¬ e.IsRet → LStep sig (E.plug e) t →
    ∃ e', LStep sig e e' ∧ t = E.plug e'
  | .hole, e, t, _, h => ⟨t, h, rfl⟩
  | .appL E e2, e, t, hne, h => by
    generalize hq : (LECtx.appL E e2).plug e = q at h
    cases h with
    | step F hab =>
      cases F with
      | hole =>
        simp only [LECtx.plug] at hq; subst hq
        exact absurd hab.app_isRet.1 (LECtx.plug_not_isRet hne)
      | appL F e2' =>
        simp only [LECtx.plug, LExpr.app.injEq] at hq
        obtain ⟨h1, rfl⟩ := hq
        obtain ⟨e', he', ht⟩ := LStep.plug_inv E hne (h1 ▸ LStep.step F hab)
        exact ⟨e', he', by simp [LECtx.plug, ht]⟩
      | appR vs F =>
        simp only [LECtx.plug, LExpr.app.injEq] at hq
        exact (LECtx.plug_ne_ret hne hq.1).elim
      | _ => simp [LECtx.plug] at hq
  | .appR vs E, e, t, hne, h => by
    generalize hq : (LECtx.appR vs E).plug e = q at h
    cases h with
    | step F hab =>
      cases F with
      | hole =>
        simp only [LECtx.plug] at hq; subst hq
        exact absurd hab.app_isRet.2 (LECtx.plug_not_isRet hne)
      | appL F e2' =>
        simp only [LECtx.plug, LExpr.app.injEq] at hq
        exact (hab.plug_not_ret hq.1.symm).elim
      | appR vs' F =>
        simp only [LECtx.plug, LExpr.app.injEq, LExpr.ret.injEq] at hq
        obtain ⟨rfl, h1⟩ := hq
        obtain ⟨e', he', ht⟩ := LStep.plug_inv E hne (h1 ▸ LStep.step F hab)
        exact ⟨e', he', by simp [LECtx.plug, ht]⟩
      | _ => simp [LECtx.plug] at hq
  | .callB f E e2, e, t, hne, h => by
    generalize hq : (LECtx.callB f E e2).plug e = q at h
    cases h with
    | step F hab =>
      cases F with
      | hole =>
        simp only [LECtx.plug] at hq; subst hq
        exact absurd hab.call_isRet.1 (LECtx.plug_not_isRet hne)
      | callB f' F e2' =>
        simp only [LECtx.plug, LExpr.call.injEq] at hq
        obtain ⟨rfl, h1, rfl⟩ := hq
        obtain ⟨e', he', ht⟩ := LStep.plug_inv E hne (h1 ▸ LStep.step F hab)
        exact ⟨e', he', by simp [LECtx.plug, ht]⟩
      | callO f' vs F =>
        simp only [LECtx.plug, LExpr.call.injEq] at hq
        exact (LECtx.plug_ne_ret hne hq.2.1).elim
      | _ => simp [LECtx.plug] at hq
  | .callO f vs E, e, t, hne, h => by
    generalize hq : (LECtx.callO f vs E).plug e = q at h
    cases h with
    | step F hab =>
      cases F with
      | hole =>
        simp only [LECtx.plug] at hq; subst hq
        exact absurd hab.call_isRet.2 (LECtx.plug_not_isRet hne)
      | callB f' F e2' =>
        simp only [LECtx.plug, LExpr.call.injEq] at hq
        exact (hab.plug_not_ret hq.2.1.symm).elim
      | callO f' vs' F =>
        simp only [LECtx.plug, LExpr.call.injEq, LExpr.ret.injEq] at hq
        obtain ⟨rfl, rfl, h1⟩ := hq
        obtain ⟨e', he', ht⟩ := LStep.plug_inv E hne (h1 ▸ LStep.step F hab)
        exact ⟨e', he', by simp [LECtx.plug, ht]⟩
      | _ => simp [LECtx.plug] at hq
  | .letIn xs E e2, e, t, hne, h => by
    generalize hq : (LECtx.letIn xs E e2).plug e = q at h
    cases h with
    | step F hab =>
      cases F with
      | hole =>
        simp only [LECtx.plug] at hq; subst hq
        exact absurd hab.letIn_isRet (LECtx.plug_not_isRet hne)
      | letIn xs' F e2' =>
        simp only [LECtx.plug, LExpr.letIn.injEq] at hq
        obtain ⟨rfl, h1, rfl⟩ := hq
        obtain ⟨e', he', ht⟩ := LStep.plug_inv E hne (h1 ▸ LStep.step F hab)
        exact ⟨e', he', by simp [LECtx.plug, ht]⟩
      | _ => simp [LECtx.plug] at hq

theorem LStepsN.step_of_ne {n : Nat} {e e' : LExpr} (h : LStepsN sig n e e') (hne : e ≠ e') :
    ∃ m t, n = m + 1 ∧ LStep sig e t ∧ LStepsN sig m t e' := by
  cases h with
  | refl => exact (hne rfl).elim
  | step hs hrest => exact ⟨_, _, rfl, hs, hrest⟩

/-- A reduction of `E[e]` to a value factors through a reduction of `e` to a value. -/
theorem LStepsN.plug : ∀ {n : Nat} (E : LECtx) {e : LExpr} {ws : List LVal},
    LStepsN sig n (E.plug e) (.ret ws) →
    ∃ k vs, k ≤ n ∧ LStepsN sig k e (.ret vs) ∧ LStepsN sig (n - k) (E.plug (.ret vs)) (.ret ws)
  | n, E, e, ws, h => by
    by_cases hr : e.IsRet
    · cases e with
      | ret vs => exact ⟨0, vs, Nat.zero_le _, .refl _, by simpa using h⟩
      | _ => exact hr.elim
    · have hne : E.plug e ≠ .ret ws := fun h' =>
        LECtx.plug_not_isRet hr (by rw [h']; trivial)
      obtain ⟨m, t, rfl, hs, hrest⟩ := h.step_of_ne hne
      obtain ⟨e', he', rfl⟩ := LStep.plug_inv E hr hs
      obtain ⟨k, vs, hk, h1, h2⟩ := LStepsN.plug E hrest
      exact ⟨k + 1, vs, by omega, .step he' h1, by
        rw [show m + 1 - (k + 1) = m - k by omega]; exact h2⟩

/-- A reduction of a redex to a value starts with a head step. -/
theorem LStepsN.head_of {n : Nat} {e : LExpr} {ws : List LVal}
    (hred : ∀ t, LStep sig e t → LHead sig e t) (hne : ¬ e.IsRet)
    (h : LStepsN sig n e (.ret ws)) :
    ∃ m t, n = m + 1 ∧ LHead sig e t ∧ LStepsN sig m t (.ret ws) := by
  cases h with
  | refl => exact (hne trivial).elim
  | step hs hrest => exact ⟨_, _, rfl, hred _ hs, hrest⟩

theorem LStep.head_of_noCtx {e t : LExpr}
    (hctx : ∀ (E : LECtx) (a : LExpr), E.plug a = e → (∃ b, LHead sig a b) → E = .hole)
    (h : LStep sig e t) : LHead sig e t := by
  cases h with
  | step E hab =>
    have := hctx E _ rfl ⟨_, hab⟩
    subst this
    exact hab

theorem LStep.app_ret_ret {vs1 vs2 : List LVal} {t : LExpr}
    (h : LStep sig (.app (.ret vs1) (.ret vs2)) t) : LHead sig (.app (.ret vs1) (.ret vs2)) t := by
  refine LStep.head_of_noCtx (fun E a he ⟨b, hb⟩ => ?_) h
  cases E with
  | hole => rfl
  | appL E e => simp only [LECtx.plug, LExpr.app.injEq] at he; exact (hb.plug_not_ret he.1).elim
  | appR vs E => simp only [LECtx.plug, LExpr.app.injEq] at he; exact (hb.plug_not_ret he.2).elim
  | _ => simp [LECtx.plug] at he

theorem LStep.call_ret_ret {f : FName} {vs1 vs2 : List LVal} {t : LExpr}
    (h : LStep sig (.call f (.ret vs1) (.ret vs2)) t) :
    LHead sig (.call f (.ret vs1) (.ret vs2)) t := by
  refine LStep.head_of_noCtx (fun E a he ⟨b, hb⟩ => ?_) h
  cases E with
  | hole => rfl
  | callB f E e =>
    simp only [LECtx.plug, LExpr.call.injEq] at he; exact (hb.plug_not_ret he.2.1).elim
  | callO f vs E =>
    simp only [LECtx.plug, LExpr.call.injEq] at he; exact (hb.plug_not_ret he.2.2).elim
  | _ => simp [LECtx.plug] at he

theorem LStep.letIn_ret {xs : List Binder} {vs : List LVal} {e2 t : LExpr}
    (h : LStep sig (.letIn xs (.ret vs) e2) t) : LHead sig (.letIn xs (.ret vs) e2) t := by
  refine LStep.head_of_noCtx (fun E a he ⟨b, hb⟩ => ?_) h
  cases E with
  | hole => rfl
  | letIn xs E e =>
    simp only [LECtx.plug, LExpr.letIn.injEq] at he; exact (hb.plug_not_ret he.2.1).elim
  | _ => simp [LECtx.plug] at he

/-- Expressions that are not built from an evaluation context. -/
def LExpr.NoCtx : LExpr → Prop
  | .match _ _ | .dup _ _ | .drop _ _ | .dropru _ _ _ | .free _ _ | .alloc _ _ => True
  | _ => False

theorem LStep.of_noCtx {e t : LExpr} (hn : e.NoCtx) (h : LStep sig e t) : LHead sig e t := by
  refine LStep.head_of_noCtx (fun E a he _ => ?_) h
  cases E
  · rfl
  all_goals (subst he; simp [LECtx.plug, LExpr.NoCtx] at hn)

/-! ## The heap semantics is closed under evaluation contexts -/

/-- Composition of evaluation contexts. -/
def LECtx.comp : LECtx → LECtx → LECtx
  | .hole, F => F
  | .appL E e, F => .appL (E.comp F) e
  | .appR vs E, F => .appR vs (E.comp F)
  | .callB f E e, F => .callB f (E.comp F) e
  | .callO f vs E, F => .callO f vs (E.comp F)
  | .letIn xs E e, F => .letIn xs (E.comp F) e

theorem LECtx.plug_comp : ∀ (E F : LECtx) (e : LExpr), (E.comp F).plug e = E.plug (F.plug e)
  | .hole, _, _ => rfl
  | .appL E _, F, e => by simp [LECtx.comp, LECtx.plug, LECtx.plug_comp E F e]
  | .appR _ E, F, e => by simp [LECtx.comp, LECtx.plug, LECtx.plug_comp E F e]
  | .callB _ E _, F, e => by simp [LECtx.comp, LECtx.plug, LECtx.plug_comp E F e]
  | .callO _ _ E, F, e => by simp [LECtx.comp, LECtx.plug, LECtx.plug_comp E F e]
  | .letIn _ E _, F, e => by simp [LECtx.comp, LECtx.plug, LECtx.plug_comp E F e]

theorem HStep.ctx {H H' : Heap} {e e' : LExpr} (E : LECtx) (h : HStep sig H e H' e') :
    HStep sig H (E.plug e) H' (E.plug e') := by
  cases h with
  | head F hh =>
    rw [← LECtx.plug_comp, ← LECtx.plug_comp]; exact .head _ hh
  | val F done V rest hd hV hv =>
    rw [← LECtx.plug_comp, ← LECtx.plug_comp]; exact .val _ done V rest hd hV hv

theorem HSteps.ctx {H H' : Heap} {e e' : LExpr} (E : LECtx) (h : HSteps sig H e H' e') :
    HSteps sig H (E.plug e) H' (E.plug e') := by
  induction h with
  | refl => exact .refl _ _
  | tail _ hs ih => exact .tail ih (hs.ctx E)

theorem HSteps.trans {H₁ H₂ H₃ : Heap} {e₁ e₂ e₃ : LExpr} (h₁ : HSteps sig H₁ e₁ H₂ e₂)
    (h₂ : HSteps sig H₂ e₂ H₃ e₃) : HSteps sig H₁ e₁ H₃ e₃ := by
  induction h₂ with
  | refl => exact h₁
  | tail _ hs ih => exact .tail (ih h₁) hs

theorem HSteps.single {H H' : Heap} {e e' : LExpr} (h : HStep sig H e H' e') :
    HSteps sig H e H' e' := .tail (.refl _ _) h

theorem HSteps.head {H H' : Heap} {e e' : LExpr} (h : HHead sig H e H' e') :
    HSteps sig H e H' e' := .single (by simpa [LECtx.plug] using HStep.head .hole h)

end FIPNamed.Lam
