module

public import RequestProject.FIP.Semantics

@[expose] public section

/-!
# Counted reductions of the functional semantics and their inversion

Auxiliary facts about the functional semantics of Fig. 3 used in the proof of
Theorem 1: reductions counted by their length, values do not reduce, and a reduction of
a `let`, a call, an application, a match or a `drop`/`free` to a value factors through
the evaluation of its subexpression.
-/

namespace FIP

/-- `e ↦ⁿ e'`: a reduction of length `n`. -/
inductive StepsN (sig : Sig) : Nat → Expr → Expr → Prop where
  | refl (e : Expr) : StepsN sig 0 e e
  | step {n : Nat} {e1 e2 e3 : Expr} : Step sig e1 e2 → StepsN sig n e2 e3 →
      StepsN sig (n + 1) e1 e3

theorem StepsN.of_steps {sig : Sig} {e e' : Expr} (h : Steps sig e e') :
    ∃ n, StepsN sig n e e' := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, .refl _⟩
  | head h _ ih => obtain ⟨n, hn⟩ := ih; exact ⟨n + 1, .step h hn⟩

theorem Head.not_ret {sig : Sig} {vs : List Val} {e : Expr} : ¬ Head sig (.ret vs) e := by
  intro h; cases h

theorem ECtx.plug_eq_ret {E : ECtx} {e : Expr} {vs : List Val} (h : E.plug e = .ret vs) :
    E = .hole ∧ e = .ret vs := by
  cases E <;> simp_all [ECtx.plug]

theorem Step.not_ret {sig : Sig} {vs : List Val} {e : Expr} : ¬ Step sig (.ret vs) e := by
  intro h
  generalize he : Expr.ret vs = e0 at h
  cases h with
  | step E a b hab =>
    obtain ⟨rfl, rfl⟩ := ECtx.plug_eq_ret he.symm
    exact Head.not_ret hab

theorem StepsN.ret_inv {sig : Sig} {n : Nat} {vs : List Val} {e : Expr}
    (h : StepsN sig n (.ret vs) e) : n = 0 ∧ e = .ret vs := by
  cases h with
  | refl => exact ⟨rfl, rfl⟩
  | step hs _ => exact absurd hs Step.not_ret

theorem StepsN.ret_ret {sig : Sig} {n : Nat} {vs ws : List Val}
    (h : StepsN sig n (.ret vs) (.ret ws)) : n = 0 ∧ vs = ws := by
  obtain ⟨h1, h2⟩ := h.ret_inv
  exact ⟨h1, by injection h2.symm⟩

/-! ## One-step inversion -/

theorem Step.letIn_inv {sig : Sig} {xs : List Binder} {e1 e2 e' : Expr}
    (h : Step sig (.letIn xs e1 e2) e') :
    (∃ e1', Step sig e1 e1' ∧ e' = .letIn xs e1' e2) ∨
    (∃ vs, e1 = .ret vs ∧ xs.length = vs.length ∧ e' = e2.subst (zipSubst xs vs)) := by
  generalize he : Expr.letIn xs e1 e2 = e0 at h
  cases h with
  | step E a b hab =>
    cases E with
    | hole =>
      simp only [ECtx.plug] at he ⊢
      subst he
      cases hab with
      | letIn _ vs _ hl => exact .inr ⟨vs, rfl, hl, rfl⟩
    | letIn xs' E e =>
      simp only [ECtx.plug, Expr.letIn.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      exact .inl ⟨_, .step E a b hab, rfl⟩
    | _ => simp [ECtx.plug] at he

theorem Step.callO_inv {sig : Sig} {f : FName} {vs1 : List Val} {e2 e' : Expr}
    (h : Step sig (.call f (.ret vs1) e2) e') :
    (∃ e2', Step sig e2 e2' ∧ e' = .call f (.ret vs1) e2') ∨
    (∃ vs2 fd, e2 = .ret vs2 ∧ sig.lookup f = some fd ∧ fd.borrowed.length = vs1.length ∧
      fd.owned.length = vs2.length ∧
      e' = fd.body.subst (zipSubst fd.borrowed vs1 ++ zipSubst fd.owned vs2)) := by
  generalize he : Expr.call f (.ret vs1) e2 = e0 at h
  cases h with
  | step E a b hab =>
    cases E with
    | hole =>
      simp only [ECtx.plug] at he ⊢
      subst he
      cases hab with
      | call _ fd _ vs2 hl h1 h2 => exact .inr ⟨vs2, fd, rfl, hl, h1, h2, rfl⟩
    | callO f' vs E =>
      simp only [ECtx.plug, Expr.call.injEq] at he
      obtain ⟨rfl, h1, rfl⟩ := he
      cases h1
      exact .inl ⟨_, .step E a b hab, rfl⟩
    | callB f' E e =>
      simp only [ECtx.plug, Expr.call.injEq] at he
      obtain ⟨rfl, h1, rfl⟩ := he
      obtain ⟨rfl, rfl⟩ := ECtx.plug_eq_ret h1.symm
      exact absurd hab Head.not_ret
    | _ => simp [ECtx.plug] at he

theorem Step.appR_inv {sig : Sig} {v : Val} {e2 e' : Expr}
    (h : Step sig (.app (.ret [v]) e2) e') :
    (∃ e2', Step sig e2 e2' ∧ e' = .app (.ret [v]) e2') ∨
    (∃ f fd vs, v = .fn f ∧ e2 = .ret vs ∧ sig.lookup f = some fd ∧ fd.borrowed = [] ∧
      fd.owned.length = vs.length ∧ e' = fd.body.subst (zipSubst fd.owned vs)) := by
  generalize he : Expr.app (.ret [v]) e2 = e0 at h
  cases h with
  | step E a b hab =>
    cases E with
    | hole =>
      simp only [ECtx.plug] at he ⊢
      subst he
      cases hab with
      | app f fd vs hl hb ho => exact .inr ⟨f, fd, vs, rfl, rfl, hl, hb, ho, rfl⟩
    | appR vs E =>
      simp only [ECtx.plug, Expr.app.injEq] at he
      obtain ⟨h1, rfl⟩ := he
      cases h1
      exact .inl ⟨_, .step E a b hab, rfl⟩
    | appL E e =>
      simp only [ECtx.plug, Expr.app.injEq] at he
      obtain ⟨h1, rfl⟩ := he
      obtain ⟨rfl, rfl⟩ := ECtx.plug_eq_ret h1.symm
      exact absurd hab Head.not_ret
    | _ => simp [ECtx.plug] at he

theorem Step.bmatch_inv {sig : Sig} {v : Val} {bs : List Branch} {e' : Expr}
    (h : Step sig (.bmatch (.ret [v]) bs) e') :
    ∃ c ws xs e, v = .ctor c ws ∧ findBranch bs c ws.length = some (.mk c xs e) ∧
      e' = e.subst (zipSubst xs ws) := by
  generalize he : Expr.bmatch (.ret [v]) bs = e0 at h
  cases h with
  | step E a b hab =>
    cases E with
    | hole =>
      simp only [ECtx.plug] at he ⊢
      subst he
      cases hab with
      | bmatch c ws _ xs e hf => exact ⟨c, ws, xs, e, rfl, hf, rfl⟩
    | bmatch E bs' =>
      simp only [ECtx.plug, Expr.bmatch.injEq] at he
      obtain ⟨h1, rfl⟩ := he
      obtain ⟨rfl, rfl⟩ := ECtx.plug_eq_ret h1.symm
      exact absurd hab Head.not_ret
    | _ => simp [ECtx.plug] at he

theorem Step.dmatch_inv {sig : Sig} {v : Val} {bs : List Branch} {e' : Expr}
    (h : Step sig (.dmatch (.ret [v]) bs) e') :
    ∃ c ws xs e, v = .ctor c ws ∧ findBranch bs c ws.length = some (.mk c xs e) ∧
      e' = e.subst (zipSubst xs ws) := by
  generalize he : Expr.dmatch (.ret [v]) bs = e0 at h
  cases h with
  | step E a b hab =>
    cases E with
    | hole =>
      simp only [ECtx.plug] at he ⊢
      subst he
      cases hab with
      | dmatch c ws _ xs e hf => exact ⟨c, ws, xs, e, rfl, hf, rfl⟩
    | dmatch E bs' =>
      simp only [ECtx.plug, Expr.dmatch.injEq] at he
      obtain ⟨h1, rfl⟩ := he
      obtain ⟨rfl, rfl⟩ := ECtx.plug_eq_ret h1.symm
      exact absurd hab Head.not_ret
    | _ => simp [ECtx.plug] at he

theorem Step.drop_inv {sig : Sig} {v : Val} {e e' : Expr} (h : Step sig (.drop v e) e') :
    e' = e := by
  generalize he : Expr.drop v e = e0 at h
  cases h with
  | step E a b hab =>
    cases E with
    | hole =>
      simp only [ECtx.plug] at he ⊢
      subst he
      cases hab; rfl
    | _ => simp [ECtx.plug] at he

theorem Step.free_inv {sig : Sig} {k : Nat} {e e' : Expr} (h : Step sig (.free k e) e') :
    e' = e := by
  generalize he : Expr.free k e = e0 at h
  cases h with
  | step E a b hab =>
    cases E with
    | hole =>
      simp only [ECtx.plug] at he ⊢
      subst he
      cases hab; rfl
    | _ => simp [ECtx.plug] at he

/-! ## Factoring reductions to values -/

theorem StepsN.letIn_inv {sig : Sig} {n : Nat} {xs : List Binder} {e1 e2 : Expr}
    {vs : List Val} (h : StepsN sig n (.letIn xs e1 e2) (.ret vs)) :
    ∃ n1 n2 ws, n1 + n2 + 1 ≤ n ∧ StepsN sig n1 e1 (.ret ws) ∧ xs.length = ws.length ∧
      StepsN sig n2 (e2.subst (zipSubst xs ws)) (.ret vs) := by
  induction n generalizing e1 with
  | zero => cases h
  | succ n ih =>
    cases h with
    | step hs hr =>
      rcases Step.letIn_inv hs with ⟨e1', hs', rfl⟩ | ⟨ws, rfl, hl, rfl⟩
      · obtain ⟨n1, n2, ws, hle, h1, hl, h2⟩ := ih hr
        exact ⟨n1 + 1, n2, ws, by omega, .step hs' h1, hl, h2⟩
      · exact ⟨0, n, ws, by omega, .refl _, hl, hr⟩

theorem StepsN.callO_inv {sig : Sig} {n : Nat} {f : FName} {vs1 : List Val} {e2 : Expr}
    {vs : List Val} (h : StepsN sig n (.call f (.ret vs1) e2) (.ret vs)) :
    ∃ n1 n2 vs2 fd, n1 + n2 + 1 ≤ n ∧ StepsN sig n1 e2 (.ret vs2) ∧
      sig.lookup f = some fd ∧ fd.borrowed.length = vs1.length ∧
      fd.owned.length = vs2.length ∧
      StepsN sig n2 (fd.body.subst (zipSubst fd.borrowed vs1 ++ zipSubst fd.owned vs2))
        (.ret vs) := by
  induction n generalizing e2 with
  | zero => cases h
  | succ n ih =>
    cases h with
    | step hs hr =>
      rcases Step.callO_inv hs with ⟨e2', hs', rfl⟩ | ⟨vs2, fd, rfl, hl, h1, h2, rfl⟩
      · obtain ⟨n1, n2, vs2, fd, hle, ha, hl, h1, h2, hb⟩ := ih hr
        exact ⟨n1 + 1, n2, vs2, fd, by omega, .step hs' ha, hl, h1, h2, hb⟩
      · exact ⟨0, n, vs2, fd, by omega, .refl _, hl, h1, h2, hr⟩

theorem StepsN.appR_inv {sig : Sig} {n : Nat} {v : Val} {e2 : Expr}
    {vs : List Val} (h : StepsN sig n (.app (.ret [v]) e2) (.ret vs)) :
    ∃ n1 n2 f fd ws, n1 + n2 + 1 ≤ n ∧ v = .fn f ∧ StepsN sig n1 e2 (.ret ws) ∧
      sig.lookup f = some fd ∧ fd.borrowed = [] ∧ fd.owned.length = ws.length ∧
      StepsN sig n2 (fd.body.subst (zipSubst fd.owned ws)) (.ret vs) := by
  induction n generalizing e2 with
  | zero => cases h
  | succ n ih =>
    cases h with
    | step hs hr =>
      rcases Step.appR_inv hs with ⟨e2', hs', rfl⟩ | ⟨f, fd, ws, rfl, rfl, hl, hb, ho, rfl⟩
      · obtain ⟨n1, n2, f, fd, ws, hle, hv, ha, hl, hb, ho, hr'⟩ := ih hr
        exact ⟨n1 + 1, n2, f, fd, ws, by omega, hv, .step hs' ha, hl, hb, ho, hr'⟩
      · exact ⟨0, n, f, fd, ws, by omega, rfl, .refl _, hl, hb, ho, hr⟩

theorem StepsN.bmatch_inv {sig : Sig} {n : Nat} {v : Val} {bs : List Branch}
    {vs : List Val} (h : StepsN sig n (.bmatch (.ret [v]) bs) (.ret vs)) :
    ∃ m c ws xs e, m + 1 ≤ n ∧ v = .ctor c ws ∧
      findBranch bs c ws.length = some (.mk c xs e) ∧
      StepsN sig m (e.subst (zipSubst xs ws)) (.ret vs) := by
  cases h with
  | step hs hr =>
    obtain ⟨c, ws, xs, e, rfl, hf, rfl⟩ := Step.bmatch_inv hs
    exact ⟨_, c, ws, xs, e, le_rfl, rfl, hf, hr⟩

theorem StepsN.dmatch_inv {sig : Sig} {n : Nat} {v : Val} {bs : List Branch}
    {vs : List Val} (h : StepsN sig n (.dmatch (.ret [v]) bs) (.ret vs)) :
    ∃ m c ws xs e, m + 1 ≤ n ∧ v = .ctor c ws ∧
      findBranch bs c ws.length = some (.mk c xs e) ∧
      StepsN sig m (e.subst (zipSubst xs ws)) (.ret vs) := by
  cases h with
  | step hs hr =>
    obtain ⟨c, ws, xs, e, rfl, hf, rfl⟩ := Step.dmatch_inv hs
    exact ⟨_, c, ws, xs, e, le_rfl, rfl, hf, hr⟩

theorem StepsN.drop_inv {sig : Sig} {n : Nat} {v : Val} {e : Expr} {vs : List Val}
    (h : StepsN sig n (.drop v e) (.ret vs)) : ∃ m, m + 1 ≤ n ∧ StepsN sig m e (.ret vs) := by
  cases h with
  | step hs hr => obtain rfl := Step.drop_inv hs; exact ⟨_, le_rfl, hr⟩

theorem StepsN.free_inv {sig : Sig} {n : Nat} {k : Nat} {e : Expr} {vs : List Val}
    (h : StepsN sig n (.free k e) (.ret vs)) : ∃ m, m + 1 ≤ n ∧ StepsN sig m e (.ret vs) := by
  cases h with
  | step hs hr => obtain rfl := Step.free_inv hs; exact ⟨_, le_rfl, hr⟩

end FIP
