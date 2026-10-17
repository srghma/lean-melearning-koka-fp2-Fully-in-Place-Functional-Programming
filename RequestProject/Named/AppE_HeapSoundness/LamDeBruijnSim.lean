module

public import RequestProject.Named.AppE_HeapSoundness.LamDeBruijnSimLemmas

@[expose] public section

/-!
# The named and the de Bruijn semantics of `λfip` agree on closed programs

For a signature `sig` whose bodies only mention their parameters
(`sig.toLTSig = some tsig`) and a closed expression `e` whose lambdas are correctly
annotated (`e.toLTerm Scope.empty = some t`, so `t : LTerm 0`):

* every named step `e ⟼ e'` is matched by a de Bruijn step `t ⟼ t'` with
  `e'.toLTerm Scope.empty = some t'` (`LStep.toClosed`), and
* every de Bruijn step `t ⟼ t'` is matched by a named step `e ⟼ e'` with
  `e'.toLTerm Scope.empty = some t'` (`LTStep.ofClosed`);

and likewise for `⟼*` (`LSteps.toClosed`, `LTSteps.ofClosed`); in particular both compute
the same results (`LSteps.ret_iff`).  So on closed programs the two semantics are in
lock-step, and every named reduct of a closed, correctly annotated expression is again
closed and correctly annotated.

The de Bruijn semantics `LTStep` substitutes with `LTerm.isubst`, which reaches the body of
a closure through its captured values exactly as the named substitution of Fig. 9 enters
the body of a lambda; this is what makes the correspondence exact, step for step.
-/

namespace FIPNamed.Lam

/-- Forward simulation of a head reduction. -/
theorem LHead.toClosed {sig : LSig} {tsig : LTSig} (hsig : sig.toLTSig = some tsig)
    {e e' : LExpr} (h : LHead sig e e') {t : LTerm 0} (ht : e.toLTerm Scope.empty = some t) :
    ∃ t', e'.toLTerm Scope.empty = some t' ∧ LTHead tsig t t' := by
  cases h with
  | letIn xs vs e hlen =>
    obtain ⟨a, b, ha, hb, rfl⟩ := lbind2_eq_some ht
    obtain ⟨ts, hts, rfl⟩ := Option.map_eq_some_iff.mp ha
    have hl : vs.length = (Binder.flags xs).length := by simp [hlen]
    exact ⟨_, LExpr.toLTerm_subst_inst (Γ₀ := Scope.empty) (fun _ => rfl) LTVal.bvar hts hb hl,
      LTHead.letIn _ ts b hl⟩
  | call f fd vs1 vs2 hlook hl1 hl2 =>
    obtain ⟨a, b, ha, hb, rfl⟩ := lbind2_eq_some ht
    obtain ⟨ts1, hts1, rfl⟩ := Option.map_eq_some_iff.mp ha
    obtain ⟨ts2, hts2, rfl⟩ := Option.map_eq_some_iff.mp hb
    obtain ⟨tfd, htfd, hlook'⟩ := LSig.toLTSig_lookup_some hsig hlook
    obtain ⟨tb, htb, rfl⟩ := Option.map_eq_some_iff.mp htfd
    have h1 : vs1.length = (Binder.flags fd.borrowed).length := by simp [hl1]
    have h2 : vs2.length = (Binder.flags fd.owned).length := by simp [hl2]
    exact ⟨_, LExpr.toLTerm_subst_args hts1 hts2 htb h1 h2,
      LTHead.call f _ ts1 ts2 h1 h2 hlook'⟩
  | appFn f fd vs hlook hb hl =>
    obtain ⟨a, b, ha, hb', rfl⟩ := lbind2_eq_some ht
    simp only [LExpr.toLTerm, LVal.toLTVals, LVal.toLTVal] at ha
    cases ha
    obtain ⟨ts, hts, rfl⟩ := Option.map_eq_some_iff.mp hb'
    obtain ⟨tfd, htfd, hlook'⟩ := LSig.toLTSig_lookup_some hsig hlook
    obtain ⟨tb, htb, rfl⟩ := Option.map_eq_some_iff.mp htfd
    have h1 : ([] : List LVal).length = (Binder.flags fd.borrowed).length := by simp [hb]
    have h2 : vs.length = (Binder.flags fd.owned).length := by simp [hl]
    have := LExpr.toLTerm_subst_args (vs1 := []) rfl hts htb h1 h2
    simp only [hb, List.nil_append] at this
    refine ⟨_, this, ?_⟩
    exact LTHead.appFn f ⟨fd.name, Binder.flags fd.borrowed, Binder.flags fd.owned, tb⟩ ts h1 h2
      hlook'
  | beta zs xs e vs hlen =>
    obtain ⟨a, b, ha, hb, rfl⟩ := lbind2_eq_some ht
    obtain ⟨ts0, hts0, rfl⟩ := Option.map_eq_some_iff.mp ha
    obtain ⟨tl, tnil, htl, htnil, rfl⟩ := lbind2_eq_some hts0
    simp only [LVal.toLTVals, Option.some.injEq] at htnil
    subst htnil
    obtain ⟨tzs, tb, htzs, htb, rfl⟩ := lbind2_eq_some htl
    obtain ⟨ts, hts, rfl⟩ := Option.map_eq_some_iff.mp hb
    have hl : vs.length = (Binder.flags xs).length := by simp [hlen]
    exact ⟨_, LExpr.toLTerm_subst_inst (Scope.ofCaptured_closed htzs) tzs.get hts htb hl,
      LTHead.beta tzs _ tb ts hl⟩
  | «match» c vs bs xs e hfind =>
    obtain ⟨a, tbs, ha, hb, rfl⟩ := lbind2_eq_some ht
    simp only [LVal.toLTVal, Option.map_eq_some_iff] at ha
    obtain ⟨ts, hts, rfl⟩ := ha
    obtain ⟨te, hte, hf⟩ := LExpr.toLBranches_find_some Scope.empty c _ hb hfind
    have hlen : vs.length = (Binder.flags xs).length := by
      have := (lfindBranch_ctor hfind).2; simp [this]
    exact ⟨_, LExpr.toLTerm_subst_inst (Γ₀ := Scope.empty) (fun _ => rfl) LTVal.bvar hts hte hlen,
      LTHead.match c ts tbs _ te hlen hf⟩
  | dup v e =>
    obtain ⟨a, b, _, hb, rfl⟩ := lbind2_eq_some ht
    exact ⟨b, hb, LTHead.dup a b⟩
  | drop v e =>
    obtain ⟨a, b, _, hb, rfl⟩ := lbind2_eq_some ht
    exact ⟨b, hb, LTHead.drop a b⟩
  | dropru v k e =>
    obtain ⟨a, b, _, hb, rfl⟩ := lbind2_eq_some ht
    exact ⟨b, hb, LTHead.dropru a k b⟩
  | free k e =>
    obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp ht
    exact ⟨b, hb, LTHead.free k b⟩
  | alloc k e =>
    obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp ht
    exact ⟨b, hb, LTHead.alloc k b⟩

/-- Backward simulation of a head reduction. -/
theorem LTHead.ofClosed {sig : LSig} {tsig : LTSig} (hsig : sig.toLTSig = some tsig)
    {t t' : LTerm 0} (h : LTHead tsig t t') {e : LExpr} (ht : e.toLTerm Scope.empty = some t) :
    ∃ e', LHead sig e e' ∧ e'.toLTerm Scope.empty = some t' := by
  cases h with
  | letIn sc vs te hlen =>
    cases e
    case letIn xs e1 e2 =>
      obtain ⟨a, b, ha, hb, hc⟩ := lbind2_eq_some ht
      simp only [LTerm.letIn.injEq] at hc
      obtain ⟨rfl, rfl, hc⟩ := hc
      cases hc
      obtain ⟨vs0, a', rfl, hvs, hsa⟩ := LExpr.toLTerm_eq_ret ha
      cases hsa
      refine ⟨_, LHead.letIn xs vs0 e2 ?_,
        LExpr.toLTerm_subst_inst (Γ₀ := Scope.empty) (fun _ => rfl) LTVal.bvar hvs hb hlen⟩
      simp at hlen; omega
    all_goals first
      | (obtain ⟨_, _, _, _, h⟩ := lbind2_eq_some ht; cases h)
      | simp [LExpr.toLTerm] at ht
  | call f tfd vs1 vs2 h1 h2 hlook =>
    cases e
    case call g e1 e2 =>
      obtain ⟨a, b, ha, hb, hc⟩ := lbind2_eq_some ht
      simp only [LTerm.call.injEq] at hc
      obtain ⟨rfl, rfl, rfl⟩ := hc
      obtain ⟨ws1, a1, rfl, hws1, hs1⟩ := LExpr.toLTerm_eq_ret ha
      obtain ⟨ws2, a2, rfl, hws2, hs2⟩ := LExpr.toLTerm_eq_ret hb
      cases hs1
      cases hs2
      obtain ⟨fd, hlook', htfd⟩ := LSig.toLTSig_lookup_some' hsig hlook
      obtain ⟨tb, htb, rfl⟩ := Option.map_eq_some_iff.mp htfd
      refine ⟨_, LHead.call f fd ws1 ws2 hlook' ?_ ?_,
        LExpr.toLTerm_subst_args hws1 hws2 htb h1 h2⟩
      · simp at h1; omega
      · simp at h2; omega
    all_goals first
      | (obtain ⟨_, _, _, _, h⟩ := lbind2_eq_some ht; cases h)
      | simp [LExpr.toLTerm] at ht
  | appFn f tfd vs h1 h2 hlook =>
    cases e
    case app e1 e2 =>
      obtain ⟨a, b, ha, hb, hc⟩ := lbind2_eq_some ht
      simp only [LTerm.app.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      obtain ⟨ws0, a0, rfl, hws0, hs0⟩ := LExpr.toLTerm_eq_ret ha
      obtain ⟨v, rfl, hv⟩ := LVal.toLTVals_eq_one hws0 hs0
      obtain ⟨ws, a', rfl, hws, hs⟩ := LExpr.toLTerm_eq_ret hb
      cases hs
      obtain ⟨fd, hlook', htfd⟩ := LSig.toLTSig_lookup_some' hsig hlook
      obtain ⟨tb, htb, rfl⟩ := Option.map_eq_some_iff.mp htfd
      have hv' : v = .fn f := by
        cases v with
        | var x =>
          cases x with
          | name s => simp [LVal.toLTVal, Scope.empty] at hv
          | loc l => simp [LVal.toLTVal] at hv
        | fn g => simp only [LVal.toLTVal, Option.some.injEq, LTVal.fn.injEq] at hv; rw [hv]
        | ctor c vs => simp [LVal.toLTVal] at hv
        | lam zs xs e => obtain ⟨_, _, _, _, h⟩ := lbind2_eq_some hv; cases h
      subst hv'
      have hb0 : fd.borrowed = [] := by simpa [eq_comm] using h1
      have := LExpr.toLTerm_subst_args (vs1 := []) rfl hws htb h1 h2
      simp only [hb0, List.nil_append] at this
      refine ⟨_, LHead.appFn f fd ws hlook' hb0 ?_, this⟩
      simp at h2; omega
    all_goals first
      | (obtain ⟨_, _, _, _, h⟩ := lbind2_eq_some ht; cases h)
      | simp [LExpr.toLTerm] at ht
  | beta zs sc body vs h =>
    cases e
    case app e1 e2 =>
      obtain ⟨a, b, ha, hb, hc⟩ := lbind2_eq_some ht
      simp only [LTerm.app.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      obtain ⟨ws0, a0, rfl, hws0, hs0⟩ := LExpr.toLTerm_eq_ret ha
      obtain ⟨v, rfl, hv⟩ := LVal.toLTVals_eq_one hws0 hs0
      obtain ⟨ws, a', rfl, hws, hs⟩ := LExpr.toLTerm_eq_ret hb
      cases hs
      cases v with
      | lam zs' xs e' =>
        obtain ⟨a1, b1, ha1, hb1, hc1⟩ := lbind2_eq_some hv
        simp only [LTVal.lam.injEq] at hc1
        obtain ⟨rfl, hz, rfl, hbody⟩ := hc1
        cases hz
        cases hbody
        refine ⟨_, LHead.beta zs' xs e' ws ?_,
          LExpr.toLTerm_subst_inst (Scope.ofCaptured_closed ha1) a1.get hws hb1 h⟩
        simp at h; omega
      | var x =>
        cases x with
        | name s => simp [LVal.toLTVal, Scope.empty] at hv
        | loc l => simp [LVal.toLTVal] at hv
      | fn g => simp [LVal.toLTVal] at hv
      | ctor c vs => simp [LVal.toLTVal] at hv
    all_goals first
      | (obtain ⟨_, _, _, _, h⟩ := lbind2_eq_some ht; cases h)
      | simp [LExpr.toLTerm] at ht
  | «match» c vs tbs sc te hlen hfind =>
    cases e
    case «match» x bs =>
      obtain ⟨a, b, ha, hb, hc⟩ := lbind2_eq_some ht
      simp only [LTerm.match.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      cases x with
      | ctor c' ws =>
        simp only [LVal.toLTVal, Option.map_eq_some_iff] at ha
        obtain ⟨a', hws, hc'⟩ := ha
        simp only [LTVal.ctor.injEq] at hc'
        obtain ⟨rfl, rfl, hc'⟩ := hc'
        cases hc'
        rw [LExpr.toLBranches_find _ _ _ hb, Option.bind_eq_some_iff] at hfind
        obtain ⟨⟨c'', xs, e2⟩, hb', hrest⟩ := hfind
        obtain ⟨te', hte', hs⟩ := Option.map_eq_some_iff.mp hrest
        obtain ⟨rfl, hs⟩ := Sigma.mk.inj_iff.mp hs
        cases hs
        obtain ⟨rfl, -⟩ := lfindBranch_ctor hb'
        exact ⟨_, LHead.match c'' ws bs xs e2 hb',
          LExpr.toLTerm_subst_inst (Γ₀ := Scope.empty) (fun _ => rfl) LTVal.bvar hws hte' hlen⟩
      | var y =>
        cases y with
        | name s => simp [LVal.toLTVal, Scope.empty] at ha
        | loc l => simp [LVal.toLTVal] at ha
      | fn g => simp [LVal.toLTVal] at ha
      | lam zs xs e' => obtain ⟨_, _, _, _, h⟩ := lbind2_eq_some ha; cases h
    all_goals first
      | (obtain ⟨_, _, _, _, h⟩ := lbind2_eq_some ht; cases h)
      | simp [LExpr.toLTerm] at ht
  | dup v te =>
    cases e
    case dup x e0 =>
      obtain ⟨a, b, ha, hb, hc⟩ := lbind2_eq_some ht
      simp only [LTerm.dup.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      exact ⟨e0, LHead.dup x e0, hb⟩
    all_goals first
      | (obtain ⟨_, _, _, _, h⟩ := lbind2_eq_some ht; cases h)
      | simp [LExpr.toLTerm] at ht
  | drop v te =>
    cases e
    case drop x e0 =>
      obtain ⟨a, b, ha, hb, hc⟩ := lbind2_eq_some ht
      simp only [LTerm.drop.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      exact ⟨e0, LHead.drop x e0, hb⟩
    all_goals first
      | (obtain ⟨_, _, _, _, h⟩ := lbind2_eq_some ht; cases h)
      | simp [LExpr.toLTerm] at ht
  | dropru v k te =>
    cases e
    case dropru x k' e0 =>
      obtain ⟨a, b, ha, hb, hc⟩ := lbind2_eq_some ht
      simp only [LTerm.dropru.injEq] at hc
      obtain ⟨rfl, rfl, rfl⟩ := hc
      exact ⟨e0, LHead.dropru x _ e0, hb⟩
    all_goals first
      | (obtain ⟨_, _, _, _, h⟩ := lbind2_eq_some ht; cases h)
      | simp [LExpr.toLTerm] at ht
  | free k te =>
    cases e
    case free k' e0 =>
      obtain ⟨b, hb, hc⟩ := Option.map_eq_some_iff.mp ht
      simp only [LTerm.free.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      exact ⟨e0, LHead.free _ e0, hb⟩
    all_goals first
      | (obtain ⟨_, _, _, _, h⟩ := lbind2_eq_some ht; cases h)
      | simp [LExpr.toLTerm] at ht
  | alloc k te =>
    cases e
    case alloc k' e0 =>
      obtain ⟨b, hb, hc⟩ := Option.map_eq_some_iff.mp ht
      simp only [LTerm.alloc.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      exact ⟨e0, LHead.alloc _ e0, hb⟩
    all_goals first
      | (obtain ⟨_, _, _, _, h⟩ := lbind2_eq_some ht; cases h)
      | simp [LExpr.toLTerm] at ht

/-! ## Steps -/

/-- **Forward simulation.**  A named step of a closed, correctly annotated `λfip`
    expression is matched by a step of its de Bruijn representation, and the reduct is
    again closed and correctly annotated. -/
theorem LStep.toClosed {sig : LSig} {tsig : LTSig} (hsig : sig.toLTSig = some tsig)
    {e e' : LExpr} (h : LStep sig e e') {t : LTerm 0} (ht : e.toLTerm Scope.empty = some t) :
    ∃ t', e'.toLTerm Scope.empty = some t' ∧ LTStep tsig t t' := by
  obtain ⟨E, hh⟩ := h
  obtain ⟨TE, t0, hE, h0, rfl⟩ := LECtx.toLTerm_plug_inv Scope.empty _ E t ht
  obtain ⟨t0', h0', hth⟩ := LHead.toClosed hsig hh h0
  exact ⟨_, LECtx.toLTerm_plug Scope.empty h0' E TE hE, LTStep.step TE hth⟩

/-- **Backward simulation.**  A step of the de Bruijn representation of a closed `λfip`
    expression is matched by a named step. -/
theorem LTStep.ofClosed {sig : LSig} {tsig : LTSig} (hsig : sig.toLTSig = some tsig)
    {t t' : LTerm 0} (h : LTStep tsig t t') {e : LExpr} (ht : e.toLTerm Scope.empty = some t) :
    ∃ e', LStep sig e e' ∧ e'.toLTerm Scope.empty = some t' := by
  obtain ⟨TE, hth⟩ := h
  obtain ⟨E, e0, rfl, hE, h0⟩ := LExpr.toLTerm_eq_plug Scope.empty _ TE e ht
  obtain ⟨e0', hh, h0'⟩ := LTHead.ofClosed hsig hth h0
  exact ⟨_, LStep.step E hh, LECtx.toLTerm_plug Scope.empty h0' E TE hE⟩

/-- Forward simulation of `⟼*`. -/
theorem LSteps.toClosed {sig : LSig} {tsig : LTSig} (hsig : sig.toLTSig = some tsig)
    {e e' : LExpr} (h : LSteps sig e e') {t : LTerm 0} (ht : e.toLTerm Scope.empty = some t) :
    ∃ t', e'.toLTerm Scope.empty = some t' ∧ LTSteps tsig t t' := by
  induction h with
  | refl => exact ⟨t, ht, .refl⟩
  | tail _ hs ih =>
    obtain ⟨t1, h1, hs1⟩ := ih
    obtain ⟨t2, h2, hs2⟩ := LStep.toClosed hsig hs h1
    exact ⟨t2, h2, hs1.tail hs2⟩

/-- Backward simulation of `⟼*`. -/
theorem LTSteps.ofClosed {sig : LSig} {tsig : LTSig} (hsig : sig.toLTSig = some tsig)
    {t t' : LTerm 0} (h : LTSteps tsig t t') {e : LExpr} (ht : e.toLTerm Scope.empty = some t) :
    ∃ e', LSteps sig e e' ∧ e'.toLTerm Scope.empty = some t' := by
  induction h with
  | refl => exact ⟨e, .refl, ht⟩
  | tail _ hs ih =>
    obtain ⟨e1, h1, hs1⟩ := ih
    obtain ⟨e2, h2, hs2⟩ := LTStep.ofClosed hsig hs hs1
    exact ⟨e2, h1.tail h2, hs2⟩

/-- **The two semantics of `λfip` compute the same results.**  A closed, correctly
    annotated expression evaluates to an unboxed tuple of values in the named semantics
    exactly when its de Bruijn representation evaluates to the resolved tuple. -/
theorem LSteps.ret_iff {sig : LSig} {tsig : LTSig} (hsig : sig.toLTSig = some tsig)
    {e : LExpr} {t : LTerm 0} (ht : e.toLTerm Scope.empty = some t) {k : Nat}
    (ts : LTVals 0 k) :
    LTSteps tsig t (.ret ts) ↔
      ∃ vs a, LSteps sig e (.ret vs) ∧ LVal.toLTVals Scope.empty vs = some a ∧
        (⟨_, a⟩ : Σ k, LTVals 0 k) = ⟨k, ts⟩ := by
  constructor
  · intro h
    obtain ⟨e', hs, he'⟩ := LTSteps.ofClosed hsig h ht
    obtain ⟨vs, a, rfl, hvs, hsa⟩ := LExpr.toLTerm_eq_ret he'
    exact ⟨vs, a, hs, hvs, hsa⟩
  · rintro ⟨vs, a, hs, hvs, hsa⟩
    obtain ⟨t', ht', hts⟩ := LSteps.toClosed hsig hs ht
    simp only [LExpr.toLTerm, hvs, Option.map_some, Option.some.injEq] at ht'
    subst ht'
    cases hsa
    exact hts

end FIPNamed.Lam
