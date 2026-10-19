module

public import RequestProject.AppE_HeapSoundness.HeapSoundCalls

@[expose] public section

/- ══════════════════ PAPER sec. 5.2, App. E.6 START: Theorem 6 (soundness of the heap semantics), Corollary 3 (PDF p. 25; App. E.6 on p. 81) ══════════════════ -/

/-!
# Theorem 6: soundness of the heap semantics, on the de Bruijn `λfip`

**Theorem 6** of the paper: if `∅ | Γ ⊢ e`, `H` is a linear heap with `roots(H) = Γ`, and the
functional semantics evaluates `[H]e` to a value `v`, then the heap semantics evaluates
`H | e` to `H' | x` with `[H']x = v`, `H'` linear and `roots(H') = {x}`.

## Two hypotheses are added

`RequestProject/AppE_HeapSoundness/HeapCex.lean` shows that, as stated, the theorem is false
on our representation for two reasons, and so the statement here assumes:

* **admissibility** (`LExpr.Adm`, `LSig.Adm`, in `HeapAdm.lean`): no function values
  `LVal.fn` (`heap_sound_needs_no_fn`: a top-level function used as a value is not a heap
  object, so the heap semantics cannot run it as a closure), and `dropru x k` only with the
  actual size `k` of the constructor `x` was matched against (`heap_sound_needs_adm`), as
  produced by the translation of a destructive match (`dmatchBranches_adm`);
* **the heap invariant** `HInv sig.funs H σ` (in `HeapInv.lean`), which makes `[H]` precise:
  `H` is linear, the fields of its objects are locations and its closures have
  well-formed, admissible bodies, `σ` assigns to every bound location `l` the closed value
  `[H]l` it denotes, and `σ` has a finite support.

## Single heap, borrowed environment, frame

The paper splits the heap as `H₁ ⊗ H₂` to account for the borrowed environment.  Here a
single heap is used: its roots are the owned environment `Γ` plus a frame `R` that the
evaluation does not touch, and the borrowed variables `Δ` must be roots in the frame
(`∀ y ∈ Δ, Res.var y ∈ R`).  With `Δ = ∅` and `R = 0` this is the paper's statement; the
values `v` are a tuple (the result of `λfip` is an unboxed tuple), evaluated to a tuple of
locations `xs`.

## Proof

A big-step simulation (`MainClaim`): by strong induction on the number of functional steps
and by induction on the typing derivation (files `HeapSoundAux.lean`,
`HeapSoundSimple.lean`, `HeapSoundCases.lean`, `HeapSoundCalls.lean`).  Variables in scope are
replaced by locations (`ρ`), the functional semantics runs with the locations replaced by
the values `σ` they denote, and `σ` only grows (locations are never reused).
-/

namespace FIP.Lam

variable {sig : LSig}

/-- **The main lemma of Theorem 6**, for every number of functional steps. -/
theorem mainClaim (hsig : sig.Wf) (hadmS : sig.Adm) : ∀ n, MainClaim sig n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IHs =>
  intro m Δ Γ e hwf
  induction hwf using LWf.rec
    (motive_1 := @fun _ _ _ _ _ => True) (motive_2 := @fun _ _ _ _ _ => True) with
  | var => trivial
  | atom => trivial
  | reuse => trivial
  | lam => trivial
  | nil => trivial
  | cons => trivial
  | tuple vs h _ => exact exprClaim_tuple vs h
  | call f ys e _ hys _ ih => exact exprClaim_call hsig hadmS IHs f ys e hys ih
  | app Γ₁ Γ₂ e₁ e₂ _ h₂ ih₁ ih₂ => exact exprClaim_app IHs e₁ e₂ h₂ ih₁ ih₂
  | letIn Γ₁ Γ₂ Γ₃ k e₁ e₂ hΓ₂ h₁ h₂ ih₁ ih₂ => exact exprClaim_letIn hΓ₂ h₁ h₂ ih₁ ih₂
  | «match» x bs hx es hes _ ih => exact exprClaim_match x bs hx es hes ih
  | dup x hx _ ih => exact exprClaim_dup x hx ih
  | drop x _ ih => exact exprClaim_drop x ih
  | dropru x k _ ih => exact exprClaim_dropru x k ih
  | free k hk _ ih => exact exprClaim_free k hk ih
  | alloc k _ _ ih => exact exprClaim_alloc k ih
  | empty _ ih => exact exprClaim_empty ih

theorem Var.ren_scope_zero (ρ : Fin 0 → Nat) (x : Var 0) : x.ren ρ = x := by
  cases x with
  | loc l => rfl
  | bvar i => exact i.elim0

theorem Ctx.ren_scope_zero (ρ : Fin 0 → Nat) (Γ : Ctx 0) : Ctx.ren ρ Γ = Γ := by
  unfold Ctx.ren
  conv_rhs => rw [← Multiset.map_id Γ]
  apply Multiset.map_congr rfl
  intro r _
  cases r <;> simp [Res.ren, Var.ren_scope_zero]

theorem LExpr.subst_locs_scope_zero (ρ : Fin 0 → Nat) (e : LExpr 0) :
    e.subst (LSubst.locs ρ) = e := by
  rw [LExpr.subst_congr (σ' := LSubst.id 0) (fun i => i.elim0), LExpr.subst_id]

/-- A root environment has no empty credit. -/
theorem nzCtx_of_le_roots {H : Heap} {Γ : Ctx 0} (h : Γ ≤ H.roots) : nzCtx Γ = Γ := by
  unfold nzCtx
  rw [Multiset.filter_eq_self]
  intro r hr hr0
  subst hr0
  have := Multiset.count_le_of_le (Res.credit 0) h
  rw [Heap.count_roots_credit] at this
  simp only [if_true, nonpos_iff_eq_zero, Multiset.count_eq_zero] at this
  exact this hr

/-- **Theorem 6** (soundness of the heap semantics), for admissible programs, on the
    de Bruijn `λfip`.

    Let `sig` be a well-formed, admissible signature and `Δ | Γ ⊢ e` a well-formed,
    admissible closed expression.  Let `H` be a heap satisfying the invariant for `σ = [H]`
    (in particular `H` is linear) whose roots are `Γ` plus a frame `R` containing the
    borrowed variables `Δ`.  If the functional semantics evaluates `[H]e` to the tuple `vs`,
    then the heap semantics evaluates `H | e` to a tuple of locations `xs`, in a heap `H'`
    that again satisfies the invariant (so is linear), for a `σ'` extending `σ`, whose roots
    are the locations `xs` and the untouched frame `R`, and `[H']xs = vs`. -/
theorem heap_sound (hsig : sig.Wf) (hadmS : sig.Adm) {Δ : Finset (Var 0)} {Γ : Ctx 0}
    {e : LExpr 0} (hwf : LWf sig.funs Δ Γ e) (he : e.Adm (fun _ => none)) {H : Heap}
    {σ : Nat → Option (LVal 0)} (hH : HInv sig.funs H σ) {R : Ctx 0} (hR : H.roots = Γ + R)
    (hΔ : ∀ y ∈ Δ, Res.var y ∈ R) {vs : LVals 0} (hst : LSteps sig (e.substLoc σ) (.ret vs)) :
    ∃ (H' : Heap) (xs : List Nat) (σ' : Nat → Option (LVal 0)),
      HSteps sig H e H' (.ret (LVals.ofList (xs.map locV))) ∧ HInv sig.funs H' σ' ∧
        SubstExt σ σ' ∧ H'.roots = locsCtx xs + R ∧
        xs.map (fun l => (locV l).substLoc σ') = vs.toList := by
  obtain ⟨n, hn⟩ := LStepsN.of_steps hst
  have h := mainClaim hsig hadmS n hwf n le_rfl _ he Fin.elim0 H R σ vs (SzOk.none _ _) hH
    (by intro y hy; rw [Var.ren_scope_zero]; exact hΔ y hy)
    (by rw [Ctx.ren_scope_zero, nzCtx_of_le_roots (H := H) (by rw [hR]; exact le_add_right le_rfl),
      hR])
    (by rw [LExpr.subst_locs_scope_zero]; exact hn)
  rw [LExpr.subst_locs_scope_zero] at h
  exact h

/-- **Corollary 3**: a well-formed admissible program `∅ | ∅ ⊢ e` that evaluates to `vs`
    in the functional semantics evaluates from the empty heap to a tuple of locations `xs`
    denoting `vs`, in a linear heap whose roots are exactly `xs`. -/
theorem heap_sound_empty (hsig : sig.Wf) (hadmS : sig.Adm) {e : LExpr 0}
    (hwf : LWf sig.funs ∅ 0 e) (he : e.Adm (fun _ => none)) {vs : LVals 0}
    (hst : LSteps sig e (.ret vs)) :
    ∃ (H' : Heap) (xs : List Nat) (σ' : Nat → Option (LVal 0)),
      HSteps sig 0 e H' (.ret (LVals.ofList (xs.map locV))) ∧ H'.Linear ∧
        H'.roots = locsCtx xs ∧ xs.map (fun l => (locV l).substLoc σ') = vs.toList := by
  have hH : HInv sig.funs 0 (fun _ => none) :=
    { linear := ⟨⟨by simp, by simp, by simp [Heap.rngFv]⟩, by simp⟩
      ok := by simp
      reads := by simp
      bound := ⟨0, fun _ _ => rfl⟩ }
  obtain ⟨H', xs, σ', hs, hI, -, hr, hv⟩ := heap_sound hsig hadmS hwf he hH (R := 0)
    (by simp [Heap.roots]) (by simp) (by rw [LExpr.substLoc_none]; exact hst)
  exact ⟨H', xs, σ', hs, hI.linear, by simpa using hr, hv⟩

end FIP.Lam

/- ══════════════════ PAPER sec. 5.2, App. E.6 END: Theorem 6 (soundness of the heap semantics), Corollary 3 ══════════════════ -/
