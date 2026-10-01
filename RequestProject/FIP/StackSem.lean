module

public import RequestProject.FIP.StackBP

@[expose] public section

/-!
# Decomposing steps of the store semantics (Appendix C)

Two decompositions `E[a] = F[b]` of one expression are either nested, or they diverge at an
application or a call whose left part is a tuple (`ECtx.plug_eq_plug`).  From this we get
how a step of the store semantics on `F[e]` acts when `e` is not a tuple
(`SStep.decomp`): it is a step of `e`, or it allocates a constructor in a value to the left
of the hole of `F`.
-/

namespace FIP

theorem ECtx.comp_assoc (E F G : ECtx) : (E.comp F).comp G = E.comp (F.comp G) := by
  induction E <;> simp_all [ECtx.comp]

theorem ECtx.comp_hole (E : ECtx) : E.comp .hole = E := by
  induction E <;> simp_all [ECtx.comp]

theorem ECtx.plug_eq_ret {E : ECtx} {r : Expr} {vs : List Val} (h : E.plug r = .ret vs) :
    E = .hole ∧ r = .ret vs := by
  cases E with
  | hole => exact ⟨rfl, h⟩
  | _ => simp [ECtx.plug] at h

/-- The relative position of two decompositions `E[a] = F[b]`. -/
def ECtx.Decomp (E F : ECtx) (a b : Expr) : Prop :=
  (∃ G : ECtx, E = F.comp G ∧ b = G.plug a) ∨
  (∃ G : ECtx, F = E.comp G ∧ a = G.plug b) ∨
  (∃ (H E1 F1 : ECtx) (vs : List Val), E1.plug a = .ret vs ∧
    ((∃ x, E = H.comp (.appL E1 x) ∧ F = H.comp (.appR vs F1) ∧ x = F1.plug b) ∨
     (∃ f x, E = H.comp (.callB f E1 x) ∧ F = H.comp (.callO f vs F1) ∧ x = F1.plug b))) ∨
  (∃ (H E1 F1 : ECtx) (vs : List Val), F1.plug b = .ret vs ∧
    ((∃ x, F = H.comp (.appL F1 x) ∧ E = H.comp (.appR vs E1) ∧ x = E1.plug a) ∨
     (∃ f x, F = H.comp (.callB f F1 x) ∧ E = H.comp (.callO f vs E1) ∧ x = E1.plug a)))

theorem ECtx.Decomp.lift {E F : ECtx} {a b : Expr} (P : ECtx) (h : ECtx.Decomp E F a b) :
    ECtx.Decomp (P.comp E) (P.comp F) a b := by
  rcases h with ⟨G, rfl, hb⟩ | ⟨G, rfl, ha⟩ | ⟨H, E1, F1, vs, he, hd⟩ | ⟨H, E1, F1, vs, he, hd⟩
  · exact .inl ⟨G, by rw [ECtx.comp_assoc], hb⟩
  · exact .inr (.inl ⟨G, by rw [ECtx.comp_assoc], ha⟩)
  · refine .inr (.inr (.inl ⟨P.comp H, E1, F1, vs, he, ?_⟩))
    rcases hd with ⟨x, rfl, rfl, hx⟩ | ⟨f, x, rfl, rfl, hx⟩
    · exact .inl ⟨x, by rw [ECtx.comp_assoc], by rw [ECtx.comp_assoc], hx⟩
    · exact .inr ⟨f, x, by rw [ECtx.comp_assoc], by rw [ECtx.comp_assoc], hx⟩
  · refine .inr (.inr (.inr ⟨P.comp H, E1, F1, vs, he, ?_⟩))
    rcases hd with ⟨x, rfl, rfl, hx⟩ | ⟨f, x, rfl, rfl, hx⟩
    · exact .inl ⟨x, by rw [ECtx.comp_assoc], by rw [ECtx.comp_assoc], hx⟩
    · exact .inr ⟨f, x, by rw [ECtx.comp_assoc], by rw [ECtx.comp_assoc], hx⟩

/-- Two decompositions of the same expression are nested or diverge at a tuple. -/
theorem ECtx.plug_eq_plug {E F : ECtx} {a b : Expr} (h : E.plug a = F.plug b) :
    ECtx.Decomp E F a b := by
  induction E generalizing F with
  | hole => exact .inr (.inl ⟨F, rfl, h⟩)
  | appL E1 x ih =>
    cases F with
    | hole => exact .inl ⟨.appL E1 x, rfl, h.symm⟩
    | appL F1 y =>
      simp only [ECtx.plug, Expr.app.injEq] at h
      obtain ⟨h1, rfl⟩ := h
      exact (ih h1).lift (.appL .hole x)
    | appR vs F1 =>
      simp only [ECtx.plug, Expr.app.injEq] at h
      exact .inr (.inr (.inl ⟨.hole, E1, F1, vs, h.1, .inl ⟨x, rfl, rfl, h.2⟩⟩))
    | _ => simp [ECtx.plug] at h
  | appR vs E1 ih =>
    cases F with
    | hole => exact .inl ⟨.appR vs E1, rfl, h.symm⟩
    | appL F1 y =>
      simp only [ECtx.plug, Expr.app.injEq] at h
      exact .inr (.inr (.inr ⟨.hole, E1, F1, vs, h.1.symm, .inl ⟨y, rfl, rfl, h.2.symm⟩⟩))
    | appR ws F1 =>
      simp only [ECtx.plug, Expr.app.injEq, Expr.ret.injEq] at h
      obtain ⟨rfl, h1⟩ := h
      exact (ih h1).lift (.appR vs .hole)
    | _ => simp [ECtx.plug] at h
  | callB f E1 x ih =>
    cases F with
    | hole => exact .inl ⟨.callB f E1 x, rfl, h.symm⟩
    | callB g F1 y =>
      simp only [ECtx.plug, Expr.call.injEq] at h
      obtain ⟨rfl, h1, rfl⟩ := h
      exact (ih h1).lift (.callB f .hole x)
    | callO g vs F1 =>
      simp only [ECtx.plug, Expr.call.injEq] at h
      obtain ⟨rfl, h1, h2⟩ := h
      exact .inr (.inr (.inl ⟨.hole, E1, F1, vs, h1, .inr ⟨f, x, rfl, rfl, h2⟩⟩))
    | _ => simp [ECtx.plug] at h
  | callO f vs E1 ih =>
    cases F with
    | hole => exact .inl ⟨.callO f vs E1, rfl, h.symm⟩
    | callB g F1 y =>
      simp only [ECtx.plug, Expr.call.injEq] at h
      obtain ⟨rfl, h1, h2⟩ := h
      exact .inr (.inr (.inr ⟨.hole, E1, F1, vs, h1.symm, .inr ⟨f, y, rfl, rfl, h2.symm⟩⟩))
    | callO g ws F1 =>
      simp only [ECtx.plug, Expr.call.injEq, Expr.ret.injEq] at h
      obtain ⟨rfl, rfl, h1⟩ := h
      exact (ih h1).lift (.callO f vs .hole)
    | _ => simp [ECtx.plug] at h
  | letIn xs E1 x ih =>
    cases F with
    | hole => exact .inl ⟨.letIn xs E1 x, rfl, h.symm⟩
    | letIn ys F1 y =>
      simp only [ECtx.plug, Expr.letIn.injEq] at h
      obtain ⟨rfl, h1, rfl⟩ := h
      exact (ih h1).lift (.letIn xs .hole x)
    | _ => simp [ECtx.plug] at h
  | bmatch E1 bs ih =>
    cases F with
    | hole => exact .inl ⟨.bmatch E1 bs, rfl, h.symm⟩
    | bmatch F1 cs =>
      simp only [ECtx.plug, Expr.bmatch.injEq] at h
      obtain ⟨h1, rfl⟩ := h
      exact (ih h1).lift (.bmatch .hole bs)
    | _ => simp [ECtx.plug] at h
  | dmatch E1 bs ih =>
    cases F with
    | hole => exact .inl ⟨.dmatch E1 bs, rfl, h.symm⟩
    | dmatch F1 cs =>
      simp only [ECtx.plug, Expr.dmatch.injEq] at h
      obtain ⟨h1, rfl⟩ := h
      exact (ih h1).lift (.dmatch .hole bs)
    | _ => simp [ECtx.plug] at h

/-- A decomposition `E[a]` of `F[b]`, with `b` not a tuple, either extends `F` or is no
    deeper than `F`. -/
theorem ECtx.plug_eq_plug_depth {E F : ECtx} {a b : Expr} (h : E.plug a = F.plug b)
    (hb : ∀ vs, b ≠ .ret vs) : (∃ G, E = F.comp G ∧ G.plug a = b) ∨ E.depth ≤ F.depth := by
  rcases ECtx.plug_eq_plug h with ⟨G, rfl, hb'⟩ | ⟨G, rfl, _⟩ | ⟨H, E1, F1, vs, he, hd⟩ |
      ⟨H, E1, F1, vs, he, -⟩
  · exact .inl ⟨G, rfl, hb'.symm⟩
  · right; rw [ECtx.depth_comp]; omega
  · right
    obtain ⟨rfl, -⟩ := ECtx.plug_eq_ret he
    rcases hd with ⟨x, rfl, rfl, -⟩ | ⟨f, x, rfl, rfl, -⟩ <;>
      simp only [ECtx.depth_comp, ECtx.depth] <;> omega
  · exact absurd (ECtx.plug_eq_ret he).2 (hb vs)

/-! ## Steps of the store semantics -/

variable {sig : Sig} {fbip : Bool}

theorem SStep.ctx {S S' : Store} {e e' : Expr} (G : ECtx) (h : SStep sig fbip S e S' e') :
    SStep sig fbip S (G.plug e) S' (G.plug e') := by
  cases h with
  | head E hh => simpa using SStep.head (G.comp E) hh
  | val E done V rest hd hV hv => simpa using SStep.val (G.comp E) done V rest hd hV hv

/-- A step of the store semantics that allocates a constructor inside a tuple. -/
def ValRed (S : Store) (r : Expr) (S' : Store) (r' : Expr) : Prop :=
  ∃ (done : List Val) (V : VCtx) (rest : List Val) (v v' : Val),
    (∀ a ∈ done, a.Atomic) ∧ V.Ok ∧ SValHead S v S' v' ∧
    r = .ret (done ++ V.plug v :: rest) ∧ r' = .ret (done ++ V.plug v' :: rest)

theorem SHead.plug_inv {S S' : Store} {r r' : Expr} (h : SHead sig fbip S r S' r')
    {G : ECtx} {e : Expr} (hr : r = G.plug e) : G = .hole ∨ ∃ vs, e = .ret vs := by
  cases G with
  | hole => exact .inl rfl
  | _ =>
    right
    cases h <;> simp only [ECtx.plug, reduceCtorEq, Expr.letIn.injEq, Expr.call.injEq,
      Expr.app.injEq, Expr.bmatch.injEq, Expr.dmatch.injEq] at hr
    all_goals
      first
      | exact ⟨_, (ECtx.plug_eq_ret hr.2.1.symm).2⟩
      | exact ⟨_, (ECtx.plug_eq_ret hr.2.2.symm).2⟩
      | exact ⟨_, (ECtx.plug_eq_ret hr.1.symm).2⟩
      | exact ⟨_, (ECtx.plug_eq_ret hr.2.symm).2⟩

theorem SHead.not_ret {S S' : Store} {vs : List Val} {r' : Expr}
    (h : SHead sig fbip S (.ret vs) S' r') : False := by
  cases h

/-- **Steps below a context.**  A step of `F[e]`, for `e` not a tuple, is a step of `e`, or
    it allocates a constructor in a tuple to the left of the hole of `F` (independently of
    what is in the hole). -/
theorem SStep.decomp {S S' : Store} {F : ECtx} {e e' : Expr}
    (h : SStep sig fbip S (F.plug e) S' e') (he : ∀ vs, e ≠ .ret vs) :
    (∃ e₁, SStep sig fbip S e S' e₁ ∧ e' = F.plug e₁) ∨
    (∃ F' : ECtx, F'.depth = F.depth ∧ e' = F'.plug e ∧
      ∀ x, ∃ (E : ECtx) (r r' : Expr), F.plug x = E.plug r ∧ F'.plug x = E.plug r' ∧ ValRed S r S' r') := by
  generalize hx : F.plug e = x at h
  cases h with
  | head E hh =>
    rename_i r r'
    rcases ECtx.plug_eq_plug hx.symm with ⟨G, rfl, hb⟩ | ⟨G, rfl, ha⟩ |
        ⟨H, E1, F1, vs, he1, -⟩ | ⟨H, E1, F1, vs, he1, -⟩
    · exact .inl ⟨G.plug r', hb ▸ SStep.head G hh, by simp⟩
    · rcases SHead.plug_inv hh ha with rfl | ⟨vs, rfl⟩
      · refine .inl ⟨r', ?_, by simp [ECtx.comp_hole]⟩
        simp only [ECtx.plug] at ha
        subst ha
        exact SStep.head .hole hh
      · exact absurd rfl (he vs)
    · obtain ⟨-, rfl⟩ := ECtx.plug_eq_ret he1
      exact (SHead.not_ret hh).elim
    · exact absurd (ECtx.plug_eq_ret he1).2 (he vs)
  | val E done V rest hd hV hv =>
    rename_i v v'
    rcases ECtx.plug_eq_plug hx.symm with ⟨G, rfl, hb⟩ | ⟨G, rfl, ha⟩ |
        ⟨H, E1, F1, vs, he1, hdv⟩ | ⟨H, E1, F1, vs, he1, -⟩
    · exact .inl ⟨G.plug (.ret (done ++ V.plug v' :: rest)), hb ▸ SStep.val G done V rest hd hV hv,
        by simp⟩
    · obtain ⟨-, rfl⟩ := ECtx.plug_eq_ret ha.symm
      exact absurd rfl (he _)
    · obtain ⟨rfl, hvs⟩ := ECtx.plug_eq_ret he1
      have hred : ValRed S (.ret vs) S' (.ret (done ++ V.plug v' :: rest)) :=
        ⟨done, V, rest, v, v', hd, hV, hv, hvs.symm, rfl⟩
      right
      rcases hdv with ⟨y, rfl, rfl, rfl⟩ | ⟨f, y, rfl, rfl, rfl⟩
      · refine ⟨H.comp (.appR (done ++ V.plug v' :: rest) F1), by
          simp [ECtx.depth_comp, ECtx.depth], by simp [ECtx.plug], fun z => ?_⟩
        exact ⟨H.comp (.appL .hole (F1.plug z)), _, _, by simp [ECtx.plug],
          by simp [ECtx.plug], hred⟩
      · refine ⟨H.comp (.callO f (done ++ V.plug v' :: rest) F1), by
          simp [ECtx.depth_comp, ECtx.depth], by simp [ECtx.plug], fun z => ?_⟩
        exact ⟨H.comp (.callB f .hole (F1.plug z)), _, _, by simp [ECtx.plug],
          by simp [ECtx.plug], hred⟩
    · exact absurd (ECtx.plug_eq_ret he1).2 (he vs)

end FIP
