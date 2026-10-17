module

public import RequestProject.Named.Sec2_Calculus.DeBruijn.SubstComm
public import RequestProject.Named.Sec2_Calculus.DeBruijn.Semantics

@[expose] public section

/-!
# Evaluation contexts, signatures and branches under name resolution

Lemmas for `RequestProject/Sec2_Calculus/DeBruijn/Simulation.lean`: resolving the names of
`E[e]` is resolving those of `E` and of `e`; looking a function up in the resolved
signature is resolving the named function found; finding a branch in resolved branches is
resolving the named branch found; and the β-like reducts of the two semantics agree.
-/

namespace FIPNamed

/-! ## Evaluation contexts -/

/-- Resolve the names of an evaluation context. -/
def ECtx.toTECtx {n : Nat} (Δ : Scope n) : ECtx → Option (TECtx n)
  | .hole => some .hole
  | .appL E e => do pure (.appL (← E.toTECtx Δ) (← e.toTerm Δ))
  | .appR vs E => do pure (.appR (← Val.toTVals Δ vs) (← E.toTECtx Δ))
  | .callB f E e => do pure (.callB f (← E.toTECtx Δ) (← e.toTerm Δ))
  | .callO f vs E => do pure (.callO f (← Val.toTVals Δ vs) (← E.toTECtx Δ))
  | .letIn xs E e => do pure (.letIn (Binder.flags xs) (← E.toTECtx Δ) (← e.toTerm (Δ.extend xs)))
  | .bmatch E bs => do pure (.bmatch (← E.toTECtx Δ) (← Expr.toBranches Δ bs))
  | .dmatch E bs => do pure (.dmatch (← E.toTECtx Δ) (← Expr.toBranches Δ bs))

theorem bind2_eq_some' {α β γ : Type} {x : Option α} {y : Option β} {f : α → β → γ}
    {c : γ} (h : (do let a ← x; let b ← y; pure (f a b) : Option γ) = some c) :
    ∃ a b, x = some a ∧ y = some b ∧ c = f a b := by
  cases x <;> cases y <;> simp_all

theorem bind2_some {α β γ : Type} {x : Option α} {y : Option β} {f : α → β → γ}
    {a : α} {b : β} (hx : x = some a) (hy : y = some b) :
    (do let a ← x; let b ← y; pure (f a b) : Option γ) = some (f a b) := by
  subst hx hy; rfl

/-- Resolving `E[e]` from resolutions of `E` and `e`. -/
theorem ECtx.toTerm_plug {n : Nat} (Δ : Scope n) {e : Expr} {t0 : Term n}
    (he : e.toTerm Δ = some t0) :
    ∀ (E : ECtx) (TE : TECtx n), E.toTECtx Δ = some TE → (E.plug e).toTerm Δ = some (TE.plug t0)
  | .hole, TE, h => by cases h; exact he
  | .appL E e2, TE, h => by
    obtain ⟨a, b, ha, hb, rfl⟩ := bind2_eq_some' h
    exact bind2_some (ECtx.toTerm_plug Δ he E a ha) hb
  | .appR vs E, TE, h => by
    obtain ⟨a, b, ha, hb, rfl⟩ := bind2_eq_some' h
    exact bind2_some (by simp [Expr.toTerm, ha]) (ECtx.toTerm_plug Δ he E b hb)
  | .callB f E e2, TE, h => by
    obtain ⟨a, b, ha, hb, rfl⟩ := bind2_eq_some' h
    exact bind2_some (ECtx.toTerm_plug Δ he E a ha) hb
  | .callO f vs E, TE, h => by
    obtain ⟨a, b, ha, hb, rfl⟩ := bind2_eq_some' h
    exact bind2_some (by simp [Expr.toTerm, ha]) (ECtx.toTerm_plug Δ he E b hb)
  | .letIn xs E e2, TE, h => by
    obtain ⟨a, b, ha, hb, rfl⟩ := bind2_eq_some' h
    exact bind2_some (ECtx.toTerm_plug Δ he E a ha) hb
  | .bmatch E bs, TE, h => by
    obtain ⟨a, b, ha, hb, rfl⟩ := bind2_eq_some' h
    exact bind2_some (ECtx.toTerm_plug Δ he E a ha) hb
  | .dmatch E bs, TE, h => by
    obtain ⟨a, b, ha, hb, rfl⟩ := bind2_eq_some' h
    exact bind2_some (ECtx.toTerm_plug Δ he E a ha) hb

/-- Splitting a resolution of `E[e]` into resolutions of `E` and `e`. -/
theorem ECtx.toTerm_plug_inv {n : Nat} (Δ : Scope n) (e : Expr) :
    ∀ (E : ECtx) (t : Term n), (E.plug e).toTerm Δ = some t →
      ∃ TE t0, E.toTECtx Δ = some TE ∧ e.toTerm Δ = some t0 ∧ t = TE.plug t0
  | .hole, t, h => ⟨.hole, t, rfl, h, rfl⟩
  | .appL E e2, t, h => by
    obtain ⟨a, b, ha, hb, rfl⟩ := bind2_eq_some' h
    obtain ⟨TE, t0, h1, h2, rfl⟩ := ECtx.toTerm_plug_inv Δ e E a ha
    exact ⟨_, t0, bind2_some h1 hb, h2, rfl⟩
  | .appR vs E, t, h => by
    obtain ⟨a, b, ha, hb, rfl⟩ := bind2_eq_some' h
    obtain ⟨TE, t0, h1, h2, rfl⟩ := ECtx.toTerm_plug_inv Δ e E b hb
    simp only [Expr.toTerm, Option.map_eq_some_iff] at ha
    obtain ⟨ts, hts, rfl⟩ := ha
    exact ⟨_, t0, bind2_some hts h1, h2, rfl⟩
  | .callB f E e2, t, h => by
    obtain ⟨a, b, ha, hb, rfl⟩ := bind2_eq_some' h
    obtain ⟨TE, t0, h1, h2, rfl⟩ := ECtx.toTerm_plug_inv Δ e E a ha
    exact ⟨_, t0, bind2_some h1 hb, h2, rfl⟩
  | .callO f vs E, t, h => by
    obtain ⟨a, b, ha, hb, rfl⟩ := bind2_eq_some' h
    obtain ⟨TE, t0, h1, h2, rfl⟩ := ECtx.toTerm_plug_inv Δ e E b hb
    simp only [Expr.toTerm, Option.map_eq_some_iff] at ha
    obtain ⟨ts, hts, rfl⟩ := ha
    exact ⟨_, t0, bind2_some hts h1, h2, rfl⟩
  | .letIn xs E e2, t, h => by
    obtain ⟨a, b, ha, hb, rfl⟩ := bind2_eq_some' h
    obtain ⟨TE, t0, h1, h2, rfl⟩ := ECtx.toTerm_plug_inv Δ e E a ha
    exact ⟨_, t0, bind2_some h1 hb, h2, rfl⟩
  | .bmatch E bs, t, h => by
    obtain ⟨a, b, ha, hb, rfl⟩ := bind2_eq_some' h
    obtain ⟨TE, t0, h1, h2, rfl⟩ := ECtx.toTerm_plug_inv Δ e E a ha
    exact ⟨_, t0, bind2_some h1 hb, h2, rfl⟩
  | .dmatch E bs, t, h => by
    obtain ⟨a, b, ha, hb, rfl⟩ := bind2_eq_some' h
    obtain ⟨TE, t0, h1, h2, rfl⟩ := ECtx.toTerm_plug_inv Δ e E a ha
    exact ⟨_, t0, bind2_some h1 hb, h2, rfl⟩

/-- An expression resolving to the unboxed tuple `ret ts` is an unboxed tuple. -/
theorem Expr.toTerm_eq_ret {n : Nat} {Δ : Scope n} {e : Expr} {ts : List (TVal n)}
    (h : e.toTerm Δ = some (.ret ts)) : ∃ vs, e = .ret vs ∧ Val.toTVals Δ vs = some ts := by
  cases e with
  | ret vs =>
    simp only [Expr.toTerm, Option.map_eq_some_iff, Term.ret.injEq] at h
    obtain ⟨_, h, rfl⟩ := h; exact ⟨vs, rfl, h⟩
  | free k e => simp [Expr.toTerm] at h
  | prim op vs => simp [Expr.toTerm] at h
  | _ => obtain ⟨_, _, _, _, h⟩ := bind2_eq_some' h; cases h

/-- A value resolving to `ctor c ts` is a constructor value. -/
theorem Val.toTVal_eq_ctor {n : Nat} {Δ : Scope n} {v : Val} {c : CName} {ts : List (TVal n)}
    (h : v.toTVal Δ = some (.ctor c ts)) : ∃ vs, v = .ctor c vs ∧ Val.toTVals Δ vs = some ts := by
  cases v with
  | var x => cases x <;> simp [Val.toTVal] at h
  | fn f => simp [Val.toTVal] at h
  | ctor c' vs =>
    simp only [Val.toTVal, Option.map_eq_some_iff, TVal.ctor.injEq] at h
    obtain ⟨_, h, rfl, rfl⟩ := h; exact ⟨vs, rfl, h⟩
  | lit k => simp [Val.toTVal] at h

/-- Lists of values resolving to a singleton. -/
theorem Val.toTVals_eq_singleton {n : Nat} {Δ : Scope n} {vs : List Val} {t : TVal n}
    (h : Val.toTVals Δ vs = some [t]) : ∃ v, vs = [v] ∧ v.toTVal Δ = some t := by
  match vs, h with
  | [], h => simp [Val.toTVals] at h
  | [v], h =>
    simp only [Val.toTVals] at h
    cases hv : Val.toTVal Δ v <;> simp_all
  | v :: w :: ws, h =>
    obtain ⟨a, b, _, hb, hc⟩ := bind2_eq_some' h
    have := Val.toTVals_length Δ _ _ hb
    simp only [List.cons.injEq] at hc
    rw [← hc.2] at this; simp at this

/-- Decomposing a resolution of the form `TE[t0]`. -/
theorem Expr.toTerm_eq_plug {n : Nat} (Δ : Scope n) (t0 : Term n) :
    ∀ (TE : TECtx n) (e : Expr), e.toTerm Δ = some (TE.plug t0) →
      ∃ (E : ECtx) (e0 : Expr), e = E.plug e0 ∧ E.toTECtx Δ = some TE ∧ e0.toTerm Δ = some t0
  | .hole, e, h => ⟨.hole, e, rfl, rfl, h⟩
  | .appL TE t2, e, h => by
    cases e with
    | app e1 e2 =>
      obtain ⟨a, b, ha, hb, hc⟩ := bind2_eq_some' h
      simp only [TECtx.plug, Term.app.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      obtain ⟨E, e0, rfl, h1, h2⟩ := Expr.toTerm_eq_plug Δ t0 TE e1 ha
      exact ⟨.appL E e2, e0, rfl, bind2_some h1 hb, h2⟩
    | ret vs => simp [Expr.toTerm, TECtx.plug] at h
    | free k e => simp [Expr.toTerm, TECtx.plug] at h
    | prim op vs => simp [Expr.toTerm, TECtx.plug] at h
    | _ => obtain ⟨_, _, _, _, h⟩ := bind2_eq_some' h; cases h
  | .appR ts TE, e, h => by
    cases e with
    | app e1 e2 =>
      obtain ⟨a, b, ha, hb, hc⟩ := bind2_eq_some' h
      simp only [TECtx.plug, Term.app.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      obtain ⟨vs, rfl, hvs⟩ := Expr.toTerm_eq_ret ha
      obtain ⟨E, e0, rfl, h1, h2⟩ := Expr.toTerm_eq_plug Δ t0 TE e2 hb
      exact ⟨.appR vs E, e0, rfl, bind2_some hvs h1, h2⟩
    | ret vs => simp [Expr.toTerm, TECtx.plug] at h
    | free k e => simp [Expr.toTerm, TECtx.plug] at h
    | prim op vs => simp [Expr.toTerm, TECtx.plug] at h
    | _ => obtain ⟨_, _, _, _, h⟩ := bind2_eq_some' h; cases h
  | .callB f TE t2, e, h => by
    cases e with
    | call g e1 e2 =>
      obtain ⟨a, b, ha, hb, hc⟩ := bind2_eq_some' h
      simp only [TECtx.plug, Term.call.injEq] at hc
      obtain ⟨rfl, rfl, rfl⟩ := hc
      obtain ⟨E, e0, rfl, h1, h2⟩ := Expr.toTerm_eq_plug Δ t0 TE e1 ha
      exact ⟨.callB _ E e2, e0, rfl, bind2_some h1 hb, h2⟩
    | ret vs => simp [Expr.toTerm, TECtx.plug] at h
    | free k e => simp [Expr.toTerm, TECtx.plug] at h
    | prim op vs => simp [Expr.toTerm, TECtx.plug] at h
    | _ => obtain ⟨_, _, _, _, h⟩ := bind2_eq_some' h; cases h
  | .callO f ts TE, e, h => by
    cases e with
    | call g e1 e2 =>
      obtain ⟨a, b, ha, hb, hc⟩ := bind2_eq_some' h
      simp only [TECtx.plug, Term.call.injEq] at hc
      obtain ⟨rfl, rfl, rfl⟩ := hc
      obtain ⟨vs, rfl, hvs⟩ := Expr.toTerm_eq_ret ha
      obtain ⟨E, e0, rfl, h1, h2⟩ := Expr.toTerm_eq_plug Δ t0 TE e2 hb
      exact ⟨.callO _ vs E, e0, rfl, bind2_some hvs h1, h2⟩
    | ret vs => simp [Expr.toTerm, TECtx.plug] at h
    | free k e => simp [Expr.toTerm, TECtx.plug] at h
    | prim op vs => simp [Expr.toTerm, TECtx.plug] at h
    | _ => obtain ⟨_, _, _, _, h⟩ := bind2_eq_some' h; cases h
  | .letIn sc TE t2, e, h => by
    cases e with
    | letIn xs e1 e2 =>
      obtain ⟨a, b, ha, hb, hc⟩ := bind2_eq_some' h
      simp only [TECtx.plug, Term.letIn.injEq] at hc
      obtain ⟨rfl, rfl, hc⟩ := hc
      cases hc
      obtain ⟨E, e0, rfl, h1, h2⟩ := Expr.toTerm_eq_plug Δ t0 TE e1 ha
      exact ⟨.letIn xs E e2, e0, rfl, bind2_some h1 hb, h2⟩
    | ret vs => simp [Expr.toTerm, TECtx.plug] at h
    | free k e => simp [Expr.toTerm, TECtx.plug] at h
    | prim op vs => simp [Expr.toTerm, TECtx.plug] at h
    | _ => obtain ⟨_, _, _, _, h⟩ := bind2_eq_some' h; cases h
  | .bmatch TE tbs, e, h => by
    cases e with
    | bmatch e1 bs =>
      obtain ⟨a, b, ha, hb, hc⟩ := bind2_eq_some' h
      simp only [TECtx.plug, Term.bmatch.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      obtain ⟨E, e0, rfl, h1, h2⟩ := Expr.toTerm_eq_plug Δ t0 TE e1 ha
      exact ⟨.bmatch E bs, e0, rfl, bind2_some h1 hb, h2⟩
    | ret vs => simp [Expr.toTerm, TECtx.plug] at h
    | free k e => simp [Expr.toTerm, TECtx.plug] at h
    | prim op vs => simp [Expr.toTerm, TECtx.plug] at h
    | _ => obtain ⟨_, _, _, _, h⟩ := bind2_eq_some' h; cases h
  | .dmatch TE tbs, e, h => by
    cases e with
    | dmatch e1 bs =>
      obtain ⟨a, b, ha, hb, hc⟩ := bind2_eq_some' h
      simp only [TECtx.plug, Term.dmatch.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      obtain ⟨E, e0, rfl, h1, h2⟩ := Expr.toTerm_eq_plug Δ t0 TE e1 ha
      exact ⟨.dmatch E bs, e0, rfl, bind2_some h1 hb, h2⟩
    | ret vs => simp [Expr.toTerm, TECtx.plug] at h
    | free k e => simp [Expr.toTerm, TECtx.plug] at h
    | prim op vs => simp [Expr.toTerm, TECtx.plug] at h
    | _ => obtain ⟨_, _, _, _, h⟩ := bind2_eq_some' h; cases h

/-! ## Signatures and branches -/

/-- Looking a function up in the resolved signature. -/
theorem Sig.toTSig_lookup :
    ∀ {sig : Sig} {tsig : TSig}, sig.toTSig = some tsig → ∀ f : FName,
      tsig.lookup f = (sig.lookup f).bind FunDef.toTFunDef
  | [], tsig, h, f => by
    simp [Sig.toTSig] at h; subst h; rfl
  | fd :: sig, tsig, h, f => by
    simp only [Sig.toTSig, List.mapM_cons] at h
    obtain ⟨tfd, tsig', htfd, htsig', rfl⟩ := bind2_eq_some' h
    have ih := Sig.toTSig_lookup (sig := sig) htsig' f
    have hname : tfd.name = fd.name := by
      simp only [FunDef.toTFunDef, Option.map_eq_some_iff] at htfd
      obtain ⟨_, _, rfl⟩ := htfd; rfl
    simp only [TSig.lookup, Sig.lookup, List.find?_cons, hname] at ih ⊢
    split
    · simp [htfd]
    · exact ih

/-- Finding a branch in resolved branches. -/
theorem Expr.toBranches_find {n : Nat} (Δ : Scope n) (c : CName) (k : Nat) :
    ∀ {bs : List Branch} {tbs : TBranches n}, Expr.toBranches Δ bs = some tbs →
      tbs.find c k = (findBranch bs c k).bind fun b => match b with
        | .mk _ xs e => (e.toTerm (Δ.extend xs)).map fun te => ⟨Binder.flags xs, te⟩
  | [], tbs, h => by simp [Expr.toBranches] at h; subst h; rfl
  | .mk c' xs e :: bs, tbs, h => by
    obtain ⟨te, tbs', h1, h2, rfl⟩ := bind2_eq_some' h
    have ih := Expr.toBranches_find Δ c k h2
    simp only [findBranch, List.find?_cons, Branch.ctor, Branch.binders] at ih ⊢
    simp only [TBranches.find, Binder.flags, List.length_map]
    by_cases hc : c' = c ∧ xs.length = k
    · obtain ⟨rfl, rfl⟩ := hc
      simp [h1]
    · rw [if_neg hc, ih]
      have : (c' == c && xs.length == k) = false := by
        simpa [Bool.and_eq_false_iff] using fun h1 => fun h2 => hc ⟨h1, h2⟩
      rw [this]

end FIPNamed
