module

public import RequestProject.Named.AppE_HeapSoundness.LamDeBruijnBeta

@[expose] public section

/-!
# Evaluation contexts, signatures and branches of `λfip` under name resolution

Lemmas for `RequestProject/AppE_HeapSoundness/LamDeBruijnSim.lean`: resolving the names
of `E[e]` is resolving those of `E` and of `e`; looking a function up in the resolved
signature is resolving the named function found; and finding a branch in resolved
branches is resolving the named branch found.
-/

namespace FIPNamed.Lam

/-! ## Evaluation contexts -/

/-- Resolve the names of an evaluation context. -/
def LECtx.toLTECtx {n : Nat} (Δ : Scope n) : LECtx → Option (LTECtx n)
  | .hole => some .hole
  | .appL E e => do pure (.appL (← E.toLTECtx Δ) (← e.toLTerm Δ))
  | .appR vs E => do pure (.appR (← LVal.toLTVals Δ vs) (← E.toLTECtx Δ))
  | .callB f E e => do pure (.callB f (← E.toLTECtx Δ) (← e.toLTerm Δ))
  | .callO f vs E => do pure (.callO f (← LVal.toLTVals Δ vs) (← E.toLTECtx Δ))
  | .letIn xs E e => do
      pure (.letIn (Binder.flags xs) (← E.toLTECtx Δ) (← e.toLTerm (Δ.extend xs)))

/-- Resolving `E[e]` from resolutions of `E` and `e`. -/
theorem LECtx.toLTerm_plug {n : Nat} (Δ : Scope n) {e : LExpr} {t0 : LTerm n}
    (he : e.toLTerm Δ = some t0) :
    ∀ (E : LECtx) (TE : LTECtx n), E.toLTECtx Δ = some TE →
      (E.plug e).toLTerm Δ = some (TE.plug t0)
  | .hole, TE, h => by cases h; exact he
  | .appL E e2, TE, h => by
    obtain ⟨a, b, ha, hb, rfl⟩ := lbind2_eq_some h
    exact lbind2_some (LECtx.toLTerm_plug Δ he E a ha) hb
  | .appR vs E, TE, h => by
    obtain ⟨a, b, ha, hb, rfl⟩ := lbind2_eq_some h
    exact lbind2_some (by simp [LExpr.toLTerm, ha]) (LECtx.toLTerm_plug Δ he E b hb)
  | .callB f E e2, TE, h => by
    obtain ⟨a, b, ha, hb, rfl⟩ := lbind2_eq_some h
    exact lbind2_some (LECtx.toLTerm_plug Δ he E a ha) hb
  | .callO f vs E, TE, h => by
    obtain ⟨a, b, ha, hb, rfl⟩ := lbind2_eq_some h
    exact lbind2_some (by simp [LExpr.toLTerm, ha]) (LECtx.toLTerm_plug Δ he E b hb)
  | .letIn xs E e2, TE, h => by
    obtain ⟨a, b, ha, hb, rfl⟩ := lbind2_eq_some h
    exact lbind2_some (LECtx.toLTerm_plug Δ he E a ha) hb

/-- Splitting a resolution of `E[e]` into resolutions of `E` and `e`. -/
theorem LECtx.toLTerm_plug_inv {n : Nat} (Δ : Scope n) (e : LExpr) :
    ∀ (E : LECtx) (t : LTerm n), (E.plug e).toLTerm Δ = some t →
      ∃ TE t0, E.toLTECtx Δ = some TE ∧ e.toLTerm Δ = some t0 ∧ t = TE.plug t0
  | .hole, t, h => ⟨.hole, t, rfl, h, rfl⟩
  | .appL E e2, t, h => by
    obtain ⟨a, b, ha, hb, rfl⟩ := lbind2_eq_some h
    obtain ⟨TE, t0, h1, h2, rfl⟩ := LECtx.toLTerm_plug_inv Δ e E a ha
    exact ⟨_, t0, lbind2_some h1 hb, h2, rfl⟩
  | .appR vs E, t, h => by
    obtain ⟨a, b, ha, hb, rfl⟩ := lbind2_eq_some h
    obtain ⟨TE, t0, h1, h2, rfl⟩ := LECtx.toLTerm_plug_inv Δ e E b hb
    simp only [LExpr.toLTerm, Option.map_eq_some_iff] at ha
    obtain ⟨ts, hts, rfl⟩ := ha
    exact ⟨_, t0, lbind2_some hts h1, h2, rfl⟩
  | .callB f E e2, t, h => by
    obtain ⟨a, b, ha, hb, rfl⟩ := lbind2_eq_some h
    obtain ⟨TE, t0, h1, h2, rfl⟩ := LECtx.toLTerm_plug_inv Δ e E a ha
    exact ⟨_, t0, lbind2_some h1 hb, h2, rfl⟩
  | .callO f vs E, t, h => by
    obtain ⟨a, b, ha, hb, rfl⟩ := lbind2_eq_some h
    obtain ⟨TE, t0, h1, h2, rfl⟩ := LECtx.toLTerm_plug_inv Δ e E b hb
    simp only [LExpr.toLTerm, Option.map_eq_some_iff] at ha
    obtain ⟨ts, hts, rfl⟩ := ha
    exact ⟨_, t0, lbind2_some hts h1, h2, rfl⟩
  | .letIn xs E e2, t, h => by
    obtain ⟨a, b, ha, hb, rfl⟩ := lbind2_eq_some h
    obtain ⟨TE, t0, h1, h2, rfl⟩ := LECtx.toLTerm_plug_inv Δ e E a ha
    exact ⟨_, t0, lbind2_some h1 hb, h2, rfl⟩

/-- An expression resolving to an unboxed tuple is an unboxed tuple. -/
theorem LExpr.toLTerm_eq_ret {n : Nat} {Δ : Scope n} {e : LExpr} {k : Nat} {ts : LTVals n k}
    (h : e.toLTerm Δ = some (.ret ts)) :
    ∃ vs a, e = .ret vs ∧ LVal.toLTVals Δ vs = some a ∧
      (⟨_, a⟩ : Σ k, LTVals n k) = ⟨k, ts⟩ := by
  cases e with
  | ret vs =>
    simp only [LExpr.toLTerm, Option.map_eq_some_iff] at h
    obtain ⟨a, ha, hc⟩ := h
    injection hc with h0 h1 h2
    exact ⟨vs, a, rfl, ha, Sigma.ext h1 h2⟩
  | free k e => simp [LExpr.toLTerm] at h
  | alloc k e => simp [LExpr.toLTerm] at h
  | _ => obtain ⟨_, _, _, _, h⟩ := lbind2_eq_some h; cases h

/-- Lists of values resolving to a singleton. -/
theorem LVal.toLTVals_eq_one {n : Nat} {Δ : Scope n} {vs : List LVal} {a : LTVals n vs.length}
    {t : LTVal n} (h : LVal.toLTVals Δ vs = some a)
    (hs : (⟨_, a⟩ : Σ k, LTVals n k) = ⟨1, LTVals.one t⟩) :
    ∃ v, vs = [v] ∧ v.toLTVal Δ = some t := by
  cases vs with
  | nil => have := congrArg Sigma.fst hs; simp at this
  | cons v ws =>
    cases ws with
    | nil =>
      obtain ⟨t', tl, h1, h2, rfl⟩ := lbind2_eq_some h
      simp only [LVal.toLTVals, Option.some.injEq] at h2
      subst h2
      have := eq_of_heq (Sigma.mk.inj_iff.mp hs).2
      simp only [LTVals.cons.injEq, and_true] at this
      subst this
      exact ⟨v, rfl, h1⟩
    | cons w ws => have := congrArg Sigma.fst hs; simp at this

/-- Decomposing a resolution of the form `TE[t0]`. -/
theorem LExpr.toLTerm_eq_plug {n : Nat} (Δ : Scope n) (t0 : LTerm n) :
    ∀ (TE : LTECtx n) (e : LExpr), e.toLTerm Δ = some (TE.plug t0) →
      ∃ (E : LECtx) (e0 : LExpr), e = E.plug e0 ∧ E.toLTECtx Δ = some TE ∧
        e0.toLTerm Δ = some t0
  | .hole, e, h => ⟨.hole, e, rfl, rfl, h⟩
  | .appL TE t2, e, h => by
    cases e with
    | app e1 e2 =>
      obtain ⟨a, b, ha, hb, hc⟩ := lbind2_eq_some h
      simp only [LTECtx.plug, LTerm.app.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      obtain ⟨E, e0, rfl, h1, h2⟩ := LExpr.toLTerm_eq_plug Δ t0 TE e1 ha
      exact ⟨.appL E e2, e0, rfl, lbind2_some h1 hb, h2⟩
    | ret vs => simp [LExpr.toLTerm, LTECtx.plug] at h
    | free k e => simp [LExpr.toLTerm, LTECtx.plug] at h
    | alloc k e => simp [LExpr.toLTerm, LTECtx.plug] at h
    | _ => obtain ⟨_, _, _, _, h⟩ := lbind2_eq_some h; cases h
  | .appR ts TE, e, h => by
    cases e with
    | app e1 e2 =>
      obtain ⟨a, b, ha, hb, hc⟩ := lbind2_eq_some h
      simp only [LTECtx.plug, LTerm.app.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      obtain ⟨vs, a', rfl, hvs, hsa⟩ := LExpr.toLTerm_eq_ret ha
      obtain ⟨E, e0, rfl, h1, h2⟩ := LExpr.toLTerm_eq_plug Δ t0 TE e2 hb
      refine ⟨.appR vs E, e0, rfl, ?_, h2⟩
      rw [LECtx.toLTECtx, lbind2_some hvs h1]
      exact congrArg some (sigma_app (F := LTVals n) (fun k a => LTECtx.appR a TE) hsa)
    | ret vs => simp [LExpr.toLTerm, LTECtx.plug] at h
    | free k e => simp [LExpr.toLTerm, LTECtx.plug] at h
    | alloc k e => simp [LExpr.toLTerm, LTECtx.plug] at h
    | _ => obtain ⟨_, _, _, _, h⟩ := lbind2_eq_some h; cases h
  | .callB f TE t2, e, h => by
    cases e with
    | call g e1 e2 =>
      obtain ⟨a, b, ha, hb, hc⟩ := lbind2_eq_some h
      simp only [LTECtx.plug, LTerm.call.injEq] at hc
      obtain ⟨rfl, rfl, rfl⟩ := hc
      obtain ⟨E, e0, rfl, h1, h2⟩ := LExpr.toLTerm_eq_plug Δ t0 TE e1 ha
      exact ⟨.callB _ E e2, e0, rfl, lbind2_some h1 hb, h2⟩
    | ret vs => simp [LExpr.toLTerm, LTECtx.plug] at h
    | free k e => simp [LExpr.toLTerm, LTECtx.plug] at h
    | alloc k e => simp [LExpr.toLTerm, LTECtx.plug] at h
    | _ => obtain ⟨_, _, _, _, h⟩ := lbind2_eq_some h; cases h
  | .callO f ts TE, e, h => by
    cases e with
    | call g e1 e2 =>
      obtain ⟨a, b, ha, hb, hc⟩ := lbind2_eq_some h
      simp only [LTECtx.plug, LTerm.call.injEq] at hc
      obtain ⟨rfl, rfl, rfl⟩ := hc
      obtain ⟨vs, a', rfl, hvs, hsa⟩ := LExpr.toLTerm_eq_ret ha
      obtain ⟨E, e0, rfl, h1, h2⟩ := LExpr.toLTerm_eq_plug Δ t0 TE e2 hb
      refine ⟨.callO _ vs E, e0, rfl, ?_, h2⟩
      rw [LECtx.toLTECtx, lbind2_some hvs h1]
      exact congrArg some (sigma_app (F := LTVals n) (fun k a => LTECtx.callO f a TE) hsa)
    | ret vs => simp [LExpr.toLTerm, LTECtx.plug] at h
    | free k e => simp [LExpr.toLTerm, LTECtx.plug] at h
    | alloc k e => simp [LExpr.toLTerm, LTECtx.plug] at h
    | _ => obtain ⟨_, _, _, _, h⟩ := lbind2_eq_some h; cases h
  | .letIn sc TE t2, e, h => by
    cases e with
    | letIn xs e1 e2 =>
      obtain ⟨a, b, ha, hb, hc⟩ := lbind2_eq_some h
      simp only [LTECtx.plug, LTerm.letIn.injEq] at hc
      obtain ⟨rfl, rfl, hc⟩ := hc
      cases hc
      obtain ⟨E, e0, rfl, h1, h2⟩ := LExpr.toLTerm_eq_plug Δ t0 TE e1 ha
      exact ⟨.letIn xs E e2, e0, rfl, lbind2_some h1 hb, h2⟩
    | ret vs => simp [LExpr.toLTerm, LTECtx.plug] at h
    | free k e => simp [LExpr.toLTerm, LTECtx.plug] at h
    | alloc k e => simp [LExpr.toLTerm, LTECtx.plug] at h
    | _ => obtain ⟨_, _, _, _, h⟩ := lbind2_eq_some h; cases h

/-! ## Signatures -/

/-- Looking a function up in the resolved signature. -/
theorem LSig.toLTSig_lookup :
    ∀ {sig : LSig} {tsig : LTSig}, sig.toLTSig = some tsig → ∀ f : FName,
      tsig.lookup f = (sig.lookup f).bind LFunDef.toLTFunDef
  | [], tsig, h, f => by
    simp [LSig.toLTSig] at h; subst h; rfl
  | fd :: sig, tsig, h, f => by
    simp only [LSig.toLTSig, List.mapM_cons] at h
    obtain ⟨tfd, tsig', htfd, htsig', rfl⟩ := lbind2_eq_some h
    have ih := LSig.toLTSig_lookup (sig := sig) htsig' f
    have hname : tfd.name = fd.name := by
      simp only [LFunDef.toLTFunDef, Option.map_eq_some_iff] at htfd
      obtain ⟨_, _, rfl⟩ := htfd; rfl
    simp only [LTSig.lookup, LSig.lookup, List.find?_cons, hname] at ih ⊢
    split
    · simp [htfd]
    · exact ih

theorem LSig.toLTSig_isSome_of_mem :
    ∀ {sig : LSig} {tsig : LTSig}, sig.toLTSig = some tsig → ∀ fd ∈ sig, fd.toLTFunDef.isSome
  | [], _, _, fd, hfd => by simp at hfd
  | fd' :: sig, tsig, h, fd, hfd => by
    simp only [LSig.toLTSig, List.mapM_cons] at h
    obtain ⟨tfd, tsig', htfd, htsig', rfl⟩ := lbind2_eq_some h
    rcases List.mem_cons.mp hfd with rfl | hfd
    · simp [htfd]
    · exact LSig.toLTSig_isSome_of_mem (sig := sig) htsig' fd hfd

theorem LSig.toLTSig_lookup_some {sig : LSig} {tsig : LTSig} (hsig : sig.toLTSig = some tsig)
    {f : FName} {fd : LFunDef} (h : sig.lookup f = some fd) :
    ∃ tfd, fd.toLTFunDef = some tfd ∧ tsig.lookup f = some tfd := by
  have hmem : fd ∈ sig := List.mem_of_find?_eq_some h
  obtain ⟨tfd, htfd⟩ := Option.isSome_iff_exists.mp (LSig.toLTSig_isSome_of_mem hsig fd hmem)
  exact ⟨tfd, htfd, by rw [LSig.toLTSig_lookup hsig, h]; exact htfd⟩

theorem LSig.toLTSig_lookup_some' {sig : LSig} {tsig : LTSig} (hsig : sig.toLTSig = some tsig)
    {f : FName} {tfd : LTFunDef} (h : tsig.lookup f = some tfd) :
    ∃ fd, sig.lookup f = some fd ∧ fd.toLTFunDef = some tfd := by
  rw [LSig.toLTSig_lookup hsig] at h
  exact Option.bind_eq_some_iff.mp h

/-! ## Branches -/

/-- Finding a branch in resolved branches. -/
theorem LExpr.toLBranches_find {n : Nat} (Δ : Scope n) (c : CName) (k : Nat) :
    ∀ {bs : List LBranch} {tbs : LTBranches n}, LExpr.toLBranches Δ bs = some tbs →
      tbs.find c k = (lfindBranch bs c k).bind fun b => match b with
        | .mk _ xs e => (e.toLTerm (Δ.extend xs)).map fun te => ⟨Binder.flags xs, te⟩
  | [], tbs, h => by simp [LExpr.toLBranches] at h; subst h; rfl
  | .mk c' xs e :: bs, tbs, h => by
    obtain ⟨te, tbs', h1, h2, rfl⟩ := lbind2_eq_some h
    have ih := LExpr.toLBranches_find Δ c k h2
    simp only [lfindBranch, List.find?_cons, LBranch.ctor, LBranch.binders] at ih ⊢
    simp only [LTBranches.find, Binder.flags, List.length_map]
    by_cases hc : c' = c ∧ xs.length = k
    · obtain ⟨rfl, rfl⟩ := hc
      simp [h1]
    · rw [if_neg hc, ih]
      have : (c' == c && xs.length == k) = false := by
        simpa [Bool.and_eq_false_iff] using fun h1 => fun h2 => hc ⟨h1, h2⟩
      rw [this]

theorem lfindBranch_ctor {bs : List LBranch} {c c' : CName} {k : Nat} {xs : List Binder}
    {e : LExpr} (h : lfindBranch bs c k = some (.mk c' xs e)) : c' = c ∧ xs.length = k := by
  have := List.find?_some h
  simpa [LBranch.ctor, LBranch.binders] using this

/-- The branch found by `lfindBranch` is found, resolved, by `LTBranches.find`. -/
theorem LExpr.toLBranches_find_some {n : Nat} (Δ : Scope n) (c : CName) (k : Nat) :
    ∀ {bs : List LBranch} {tbs : LTBranches n}, LExpr.toLBranches Δ bs = some tbs →
      ∀ {c' : CName} {xs : List Binder} {e : LExpr}, lfindBranch bs c k = some (.mk c' xs e) →
        ∃ te, e.toLTerm (Δ.extend xs) = some te ∧ tbs.find c k = some ⟨Binder.flags xs, te⟩
  | [], _, _, _, _, _, hf => by simp [lfindBranch] at hf
  | .mk c'' ys e' :: bs, tbs, h, c', xs, e, hf => by
    obtain ⟨te, tbs', h1, h2, rfl⟩ := lbind2_eq_some h
    simp only [lfindBranch, List.find?_cons, LBranch.ctor, LBranch.binders] at hf
    simp only [LTBranches.find, Binder.flags, List.length_map]
    by_cases hc : c'' = c ∧ ys.length = k
    · obtain ⟨rfl, rfl⟩ := hc
      simp only [beq_self_eq_true, Bool.and_self] at hf
      cases hf
      exact ⟨te, h1, by simp⟩
    · have : (c'' == c && ys.length == k) = false := by
        simpa [Bool.and_eq_false_iff] using fun h1 => fun h2 => hc ⟨h1, h2⟩
      rw [this] at hf
      rw [if_neg hc]
      exact LExpr.toLBranches_find_some Δ c k h2 hf

end FIPNamed.Lam
