module

public import RequestProject.Named.Sec2_Calculus.DeBruijn.Beta

@[expose] public section

/-!
# The named and the de Bruijn semantics agree on closed programs

For a signature `sig` whose bodies only mention their parameters (`sig.toTSig = some tsig`)
and a closed expression `e` (`e.toClosed = some t`, so `t : Term 0`):

* every named step `e ↦ e'` is matched by a de Bruijn step `t ↦ t'` with
  `e'.toClosed = some t'` (`Step.toClosed`), and
* every de Bruijn step `t ↦ t'` is matched by a named step `e ↦ e'` with
  `e'.toClosed = some t'` (`TStep.ofClosed`);

and likewise for `↦*` (`Steps.toClosed`, `TSteps.ofClosed`).  So on closed programs the
two semantics are in lock-step, and every named reduct of a closed expression is closed.
-/

namespace FIPNamed

/-- Forward simulation of a head reduction. -/
theorem Head.toClosed {sig : Sig} {tsig : TSig} (hsig : sig.toTSig = some tsig)
    {e e' : Expr} (h : Head sig e e') {t : Term 0} (ht : e.toTerm Scope.empty = some t) :
    ∃ t', e'.toTerm Scope.empty = some t' ∧ THead tsig t t' := by
  cases h with
  | letIn xs vs e hlen =>
    obtain ⟨a, b, ha, hb, rfl⟩ := bind2_eq_some' ht
    obtain ⟨ts, hts, rfl⟩ := Option.map_eq_some_iff.mp ha
    have hl : ts.length = (Binder.flags xs).length := by
      rw [Val.toTVals_length _ _ _ hts]; simp [hlen]
    exact ⟨_, Expr.toTerm_subst_inst hts hb hl, THead.letIn _ ts b hl⟩
  | call f fd vs1 vs2 hlook hl1 hl2 =>
    obtain ⟨a, b, ha, hb, rfl⟩ := bind2_eq_some' ht
    obtain ⟨ts1, hts1, rfl⟩ := Option.map_eq_some_iff.mp ha
    obtain ⟨ts2, hts2, rfl⟩ := Option.map_eq_some_iff.mp hb
    obtain ⟨tfd, htfd, hlook'⟩ := Sig.toTSig_lookup_some hsig hlook
    obtain ⟨tb, htb, rfl⟩ := Option.map_eq_some_iff.mp htfd
    have h1 : ts1.length = (Binder.flags fd.borrowed).length := by
      rw [Val.toTVals_length _ _ _ hts1]; simp [hl1]
    have h2 : ts2.length = (Binder.flags fd.owned).length := by
      rw [Val.toTVals_length _ _ _ hts2]; simp [hl2]
    exact ⟨_, Expr.toTerm_subst_args hts1 hts2 htb h1 h2, THead.call f _ ts1 ts2 h1 h2 hlook'⟩
  | app f fd vs hlook hb hl =>
    obtain ⟨a, b, ha, hb', rfl⟩ := bind2_eq_some' ht
    simp only [Expr.toTerm, Val.toTVals, Val.toTVal] at ha
    cases ha
    obtain ⟨ts, hts, rfl⟩ := Option.map_eq_some_iff.mp hb'
    obtain ⟨tfd, htfd, hlook'⟩ := Sig.toTSig_lookup_some hsig hlook
    obtain ⟨tb, htb, rfl⟩ := Option.map_eq_some_iff.mp htfd
    have h1 : ([] : List (TVal 0)).length = (Binder.flags fd.borrowed).length := by simp [hb]
    have h2 : ts.length = (Binder.flags fd.owned).length := by
      rw [Val.toTVals_length _ _ _ hts]; simp [hl]
    have := Expr.toTerm_subst_args (vs1 := []) rfl hts htb h1 h2
    simp only [hb, zipSubst, List.map_nil, List.zip_nil_left, List.nil_append] at this
    exact ⟨_, this, THead.app f _ ts h1 h2 hlook'⟩
  | bmatch c vs bs xs e hfind =>
    obtain ⟨a, tbs, ha, hb, rfl⟩ := bind2_eq_some' ht
    obtain ⟨ts', hts', rfl⟩ := Option.map_eq_some_iff.mp ha
    obtain ⟨tv, htv⟩ : ∃ tv, ts' = [tv] := by
      have := Val.toTVals_length _ _ _ hts'; simp at this
      exact List.length_eq_one_iff.mp this
    subst htv
    simp only [Val.toTVals] at hts'
    obtain ⟨tv', tl, h1, h2, hc⟩ := bind2_eq_some' hts'
    cases h2
    simp only [List.cons.injEq, and_true] at hc; subst hc
    simp only [Val.toTVal, Option.map_eq_some_iff] at h1
    obtain ⟨ts, hts, rfl⟩ := h1
    have hl := Val.toTVals_length _ _ _ hts
    obtain ⟨te, hte, hf⟩ := Expr.toBranches_find_some Scope.empty c _ hb hfind
    have hlen : ts.length = (Binder.flags xs).length := by
      have := (findBranch_ctor hfind).2; simp [hl, this]
    rw [← hl] at hf
    exact ⟨_, Expr.toTerm_subst_inst hts hte hlen, THead.bmatch c ts tbs _ te hlen hf⟩
  | dmatch c vs bs xs e hfind =>
    obtain ⟨a, tbs, ha, hb, rfl⟩ := bind2_eq_some' ht
    obtain ⟨ts', hts', rfl⟩ := Option.map_eq_some_iff.mp ha
    obtain ⟨tv, htv⟩ : ∃ tv, ts' = [tv] := by
      have := Val.toTVals_length _ _ _ hts'; simp at this
      exact List.length_eq_one_iff.mp this
    subst htv
    simp only [Val.toTVals] at hts'
    obtain ⟨tv', tl, h1, h2, hc⟩ := bind2_eq_some' hts'
    cases h2
    simp only [List.cons.injEq, and_true] at hc; subst hc
    simp only [Val.toTVal, Option.map_eq_some_iff] at h1
    obtain ⟨ts, hts, rfl⟩ := h1
    have hl := Val.toTVals_length _ _ _ hts
    obtain ⟨te, hte, hf⟩ := Expr.toBranches_find_some Scope.empty c _ hb hfind
    have hlen : ts.length = (Binder.flags xs).length := by
      have := (findBranch_ctor hfind).2; simp [hl, this]
    rw [← hl] at hf
    exact ⟨_, Expr.toTerm_subst_inst hts hte hlen, THead.dmatch c ts tbs _ te hlen hf⟩
  | drop v e =>
    obtain ⟨a, b, _, hb, rfl⟩ := bind2_eq_some' ht
    exact ⟨b, hb, THead.drop a b⟩
  | free k e =>
    obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp ht
    exact ⟨b, hb, THead.free k b⟩
  | prim op a b =>
    simp only [Expr.toTerm, Val.toTVals, Val.toTVal] at ht
    cases ht
    refine ⟨_, ?_, THead.prim op a b⟩
    cases op.eval a b <;> rfl

theorem Val.toTVals_eq_cons {n : Nat} {Δ : Scope n} {vs : List Val} {t : TVal n}
    {ts : List (TVal n)} (h : Val.toTVals Δ vs = some (t :: ts)) :
    ∃ v vs', vs = v :: vs' ∧ v.toTVal Δ = some t ∧ Val.toTVals Δ vs' = some ts := by
  match vs, h with
  | [], h => simp [Val.toTVals] at h
  | v :: vs', h =>
    obtain ⟨a, b, ha, hb, hc⟩ := bind2_eq_some' h
    simp only [List.cons.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    exact ⟨v, vs', rfl, ha, hb⟩

theorem Val.toTVals_eq_nil {n : Nat} {Δ : Scope n} {vs : List Val}
    (h : Val.toTVals Δ vs = some []) : vs = [] := by
  have := Val.toTVals_length _ _ _ h
  exact List.length_eq_zero_iff.mp this.symm

theorem Val.toTVal_eq_lit {n : Nat} {Δ : Scope n} {v : Val} {k : Int}
    (h : v.toTVal Δ = some (.lit k)) : v = .lit k := by
  cases v with
  | var x => cases x <;> simp [Val.toTVal] at h
  | fn f => simp [Val.toTVal] at h
  | ctor c vs => simp [Val.toTVal] at h
  | lit k' => simp only [Val.toTVal, Option.some.injEq, TVal.lit.injEq] at h; rw [h]

theorem Val.toTVal_eq_fn {n : Nat} {Δ : Scope n} {v : Val} {f : FName}
    (h : v.toTVal Δ = some (.fn f)) : v = .fn f := by
  cases v with
  | var x => cases x <;> simp [Val.toTVal] at h
  | fn g => simp only [Val.toTVal, Option.some.injEq, TVal.fn.injEq] at h; rw [h]
  | ctor c vs => simp [Val.toTVal] at h
  | lit k' => simp [Val.toTVal] at h

/-- Backward simulation of a head reduction. -/
theorem THead.ofClosed {sig : Sig} {tsig : TSig} (hsig : sig.toTSig = some tsig)
    {t t' : Term 0} (h : THead tsig t t') {e : Expr} (ht : e.toTerm Scope.empty = some t) :
    ∃ e', Head sig e e' ∧ e'.toTerm Scope.empty = some t' := by
  cases h with
  | letIn sc ts te hlen =>
    cases e
    case letIn xs e1 e2 =>
      obtain ⟨a, b, ha, hb, hc⟩ := bind2_eq_some' ht
      simp only [Term.letIn.injEq] at hc
      obtain ⟨rfl, rfl, hc⟩ := hc
      cases hc
      obtain ⟨vs, rfl, hvs⟩ := Expr.toTerm_eq_ret ha
      have hl := Val.toTVals_length _ _ _ hvs
      refine ⟨_, Head.letIn xs vs e2 ?_, Expr.toTerm_subst_inst hvs hb hlen⟩
      simp at hlen; omega
    all_goals first
      | (obtain ⟨_, _, _, _, h⟩ := bind2_eq_some' ht; cases h)
      | simp [Expr.toTerm] at ht
  | call f tfd ts1 ts2 h1 h2 hlook =>
    cases e
    case call g e1 e2 =>
      obtain ⟨a, b, ha, hb, hc⟩ := bind2_eq_some' ht
      simp only [Term.call.injEq] at hc
      obtain ⟨rfl, rfl, rfl⟩ := hc
      obtain ⟨vs1, rfl, hvs1⟩ := Expr.toTerm_eq_ret ha
      obtain ⟨vs2, rfl, hvs2⟩ := Expr.toTerm_eq_ret hb
      obtain ⟨fd, hlook', htfd⟩ := Sig.toTSig_lookup_some' hsig hlook
      obtain ⟨tb, htb, rfl⟩ := Option.map_eq_some_iff.mp htfd
      have hl1 := Val.toTVals_length _ _ _ hvs1
      have hl2 := Val.toTVals_length _ _ _ hvs2
      refine ⟨_, Head.call f fd vs1 vs2 hlook' ?_ ?_, Expr.toTerm_subst_args hvs1 hvs2 htb h1 h2⟩
      · simp at h1; omega
      · simp at h2; omega
    all_goals first
      | (obtain ⟨_, _, _, _, h⟩ := bind2_eq_some' ht; cases h)
      | simp [Expr.toTerm] at ht
  | app f tfd ts h1 h2 hlook =>
    cases e
    case app e1 e2 =>
      obtain ⟨a, b, ha, hb, hc⟩ := bind2_eq_some' ht
      simp only [Term.app.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      obtain ⟨vs0, rfl, hvs0⟩ := Expr.toTerm_eq_ret ha
      obtain ⟨v, rfl, hv⟩ := Val.toTVals_eq_singleton hvs0
      obtain rfl := Val.toTVal_eq_fn hv
      obtain ⟨vs, rfl, hvs⟩ := Expr.toTerm_eq_ret hb
      obtain ⟨fd, hlook', htfd⟩ := Sig.toTSig_lookup_some' hsig hlook
      obtain ⟨tb, htb, rfl⟩ := Option.map_eq_some_iff.mp htfd
      have hl := Val.toTVals_length _ _ _ hvs
      have hb0 : fd.borrowed = [] := by simpa [eq_comm] using h1
      have := Expr.toTerm_subst_args (vs1 := []) rfl hvs htb h1 h2
      simp only [hb0, zipSubst, List.map_nil, List.zip_nil_left, List.nil_append] at this
      refine ⟨_, Head.app f fd vs hlook' hb0 ?_, this⟩
      simp at h2; omega
    all_goals first
      | (obtain ⟨_, _, _, _, h⟩ := bind2_eq_some' ht; cases h)
      | simp [Expr.toTerm] at ht
  | bmatch c ts tbs sc te hlen hfind =>
    cases e
    case bmatch e1 bs =>
      obtain ⟨a, b, ha, hb, hc⟩ := bind2_eq_some' ht
      simp only [Term.bmatch.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      obtain ⟨vs0, rfl, hvs0⟩ := Expr.toTerm_eq_ret ha
      obtain ⟨v, rfl, hv⟩ := Val.toTVals_eq_singleton hvs0
      obtain ⟨vs, rfl, hvs⟩ := Val.toTVal_eq_ctor hv
      have hl := Val.toTVals_length _ _ _ hvs
      rw [Expr.toBranches_find _ _ _ hb, Option.bind_eq_some_iff] at hfind
      obtain ⟨⟨c', xs, e2⟩, hb', hrest⟩ := hfind
      obtain ⟨te', hte', hs⟩ := Option.map_eq_some_iff.mp hrest
      obtain ⟨rfl, hs⟩ := Sigma.mk.inj_iff.mp hs
      cases hs
      obtain ⟨rfl, -⟩ := findBranch_ctor hb'
      rw [hl] at hb'
      exact ⟨_, Head.bmatch c' vs bs xs e2 hb', Expr.toTerm_subst_inst hvs hte' hlen⟩
    all_goals first
      | (obtain ⟨_, _, _, _, h⟩ := bind2_eq_some' ht; cases h)
      | simp [Expr.toTerm] at ht
  | dmatch c ts tbs sc te hlen hfind =>
    cases e
    case dmatch e1 bs =>
      obtain ⟨a, b, ha, hb, hc⟩ := bind2_eq_some' ht
      simp only [Term.dmatch.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      obtain ⟨vs0, rfl, hvs0⟩ := Expr.toTerm_eq_ret ha
      obtain ⟨v, rfl, hv⟩ := Val.toTVals_eq_singleton hvs0
      obtain ⟨vs, rfl, hvs⟩ := Val.toTVal_eq_ctor hv
      have hl := Val.toTVals_length _ _ _ hvs
      rw [Expr.toBranches_find _ _ _ hb, Option.bind_eq_some_iff] at hfind
      obtain ⟨⟨c', xs, e2⟩, hb', hrest⟩ := hfind
      obtain ⟨te', hte', hs⟩ := Option.map_eq_some_iff.mp hrest
      obtain ⟨rfl, hs⟩ := Sigma.mk.inj_iff.mp hs
      cases hs
      obtain ⟨rfl, -⟩ := findBranch_ctor hb'
      rw [hl] at hb'
      exact ⟨_, Head.dmatch c' vs bs xs e2 hb', Expr.toTerm_subst_inst hvs hte' hlen⟩
    all_goals first
      | (obtain ⟨_, _, _, _, h⟩ := bind2_eq_some' ht; cases h)
      | simp [Expr.toTerm] at ht
  | drop v te =>
    cases e
    case drop x e0 =>
      obtain ⟨a, b, ha, hb, hc⟩ := bind2_eq_some' ht
      simp only [Term.drop.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      exact ⟨e0, Head.drop x e0, hb⟩
    all_goals first
      | (obtain ⟨_, _, _, _, h⟩ := bind2_eq_some' ht; cases h)
      | simp [Expr.toTerm] at ht
  | free k te =>
    cases e
    case free k' e0 =>
      obtain ⟨b, hb, hc⟩ := Option.map_eq_some_iff.mp ht
      simp only [Term.free.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      exact ⟨e0, Head.free k' e0, hb⟩
    all_goals first
      | (obtain ⟨_, _, _, _, h⟩ := bind2_eq_some' ht; cases h)
      | simp [Expr.toTerm] at ht
  | prim op a b =>
    cases e
    case prim op' vs =>
      obtain ⟨ts, hts, hc⟩ := Option.map_eq_some_iff.mp ht
      simp only [Term.prim.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      obtain ⟨v1, vs1, rfl, h1, hts⟩ := Val.toTVals_eq_cons hts
      obtain ⟨v2, vs2, rfl, h2, hts⟩ := Val.toTVals_eq_cons hts
      obtain rfl := Val.toTVals_eq_nil hts
      obtain rfl := Val.toTVal_eq_lit h1
      obtain rfl := Val.toTVal_eq_lit h2
      refine ⟨_, Head.prim op' a b, ?_⟩
      cases op'.eval a b <;> rfl
    all_goals first
      | (obtain ⟨_, _, _, _, h⟩ := bind2_eq_some' ht; cases h)
      | simp [Expr.toTerm] at ht

/-! ## Steps -/

/-- **Forward simulation.**  A named step of a closed expression is matched by a step of
    its de Bruijn representation, and the reduct is again closed. -/
theorem Step.toClosed {sig : Sig} {tsig : TSig} (hsig : sig.toTSig = some tsig)
    {e e' : Expr} (h : Step sig e e') {t : Term 0} (ht : e.toClosed = some t) :
    ∃ t', e'.toClosed = some t' ∧ TStep tsig t t' := by
  obtain ⟨E, e1, e2, hh⟩ := h
  obtain ⟨TE, t0, hE, h0, rfl⟩ := ECtx.toTerm_plug_inv Scope.empty e1 E t ht
  obtain ⟨t0', h0', hth⟩ := Head.toClosed hsig hh h0
  exact ⟨_, ECtx.toTerm_plug Scope.empty h0' E TE hE, TStep.step TE t0 t0' hth⟩

/-- **Backward simulation.**  A step of the de Bruijn representation of a closed
    expression is matched by a named step. -/
theorem TStep.ofClosed {sig : Sig} {tsig : TSig} (hsig : sig.toTSig = some tsig)
    {t t' : Term 0} (h : TStep tsig t t') {e : Expr} (ht : e.toClosed = some t) :
    ∃ e', Step sig e e' ∧ e'.toClosed = some t' := by
  obtain ⟨TE, t0, t0', hth⟩ := h
  obtain ⟨E, e0, rfl, hE, h0⟩ := Expr.toTerm_eq_plug Scope.empty t0 TE e ht
  obtain ⟨e0', hh, h0'⟩ := THead.ofClosed hsig hth h0
  exact ⟨_, Step.step E e0 e0' hh, ECtx.toTerm_plug Scope.empty h0' E TE hE⟩

/-- Forward simulation of `↦*`. -/
theorem Steps.toClosed {sig : Sig} {tsig : TSig} (hsig : sig.toTSig = some tsig)
    {e e' : Expr} (h : Steps sig e e') {t : Term 0} (ht : e.toClosed = some t) :
    ∃ t', e'.toClosed = some t' ∧ TSteps tsig t t' := by
  induction h with
  | refl => exact ⟨t, ht, .refl⟩
  | tail _ hs ih =>
    obtain ⟨t1, h1, hs1⟩ := ih
    obtain ⟨t2, h2, hs2⟩ := Step.toClosed hsig hs h1
    exact ⟨t2, h2, hs1.tail hs2⟩

/-- Backward simulation of `↦*`. -/
theorem TSteps.ofClosed {sig : Sig} {tsig : TSig} (hsig : sig.toTSig = some tsig)
    {t t' : Term 0} (h : TSteps tsig t t') {e : Expr} (ht : e.toClosed = some t) :
    ∃ e', Steps sig e e' ∧ e'.toClosed = some t' := by
  induction h with
  | refl => exact ⟨e, .refl, ht⟩
  | tail _ hs ih =>
    obtain ⟨e1, h1, hs1⟩ := ih
    obtain ⟨e2, h2, hs2⟩ := TStep.ofClosed hsig hs hs1
    exact ⟨e2, h1.tail h2, hs2⟩

/-- **The two semantics compute the same results.**  A closed expression evaluates to an
    unboxed tuple of values in the named semantics exactly when its de Bruijn
    representation evaluates to the resolved tuple. -/
theorem Steps.ret_iff {sig : Sig} {tsig : TSig} (hsig : sig.toTSig = some tsig)
    {e : Expr} {t : Term 0} (ht : e.toClosed = some t) (ts : List (TVal 0)) :
    TSteps tsig t (.ret ts) ↔
      ∃ vs, Steps sig e (.ret vs) ∧ Val.toTVals Scope.empty vs = some ts := by
  constructor
  · intro h
    obtain ⟨e', hs, he'⟩ := TSteps.ofClosed hsig h ht
    obtain ⟨vs, rfl, hvs⟩ := Expr.toTerm_eq_ret he'
    exact ⟨vs, hs, hvs⟩
  · rintro ⟨vs, hs, hvs⟩
    obtain ⟨t', ht', hts⟩ := Steps.toClosed hsig hs ht
    simp only [Expr.toClosed, Expr.toTerm, hvs, Option.map_some, Option.some.injEq] at ht'
    exact ht' ▸ hts

end FIPNamed
