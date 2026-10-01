module

public import RequestProject.FIP.HeapSound
public import RequestProject.FIP.HeapLinear

@[expose] public section

/-!
# Theorem 6, corrected: the heap semantics is sound (Appendix E)

The formal statement of Theorem 6 in `RequestProject/FIP/Heap.lean` is false
(`not_heapSoundClaim` in `RequestProject/FIP/HeapCex.lean`): it allows heaps that bind
program names.  The corrected statement below follows the paper's proof, with the two heaps
`H₁ ⊗ H₂` of the paper merged into one heap `H` whose reference counts are split into

* the references `R` held by the rest of the computation (the paper's borrowed heap `H₁`,
  which must contain the borrowed environment `Δ`), and
* the owned environment `Γ` (the paper's `roots(H₂) = Γ`),

as recorded by the invariant `HInv H R RC Γ σ`, where `σ` is the substitution `[H]` of the
values denoted by the locations of `H`.  The invariant implies that `H` is linear
(`HInv.linear`) and that its roots are `R, Γ` (`HInv.vars_roots`).

Besides heaps binding locations only, the theorem needs three further restrictions, which
are collected in the admissibility predicate `LExpr.Adm` (and `LSig.Adm`):

* no top-level function is used as a value (a borrowed function argument cannot be
  duplicated by the heap semantics, which has no rule `dup f`);
* every `dropru x; e` is the reuse-drop `match x {C x̄ ↦ dup x̄; dropru x; e}` of a match
  branch on `x` (the typing rule does not check that the size recorded in `dropru` is the
  size of the cell of `x`);
* the parameters of each lambda are distinct.
-/

namespace FIP.Lam

/-- **Theorem 6** (soundness of the heap semantics), corrected.  Let `Δ | Γ ⊢ e` be an
    admissible expression of an admissible well-formed signature, and let `H` be a heap
    satisfying the invariant with references `R ⊇ Δ` of the rest of the computation and
    owned environment `Γ`; let `σ = [H]`.  If `[H]e ⟼* v̄`, then `H | e ⟼*ₕ H' | ȳ` where
    `[H']ȳ = v̄`, `H'` is linear with roots `R, ȳ` (as locations) and again satisfies the
    invariant, and the locations of `R` denote the same values as before. -/
theorem heap_sound_corrected {sig : LSig} (hsig : sig.Wf) (hsigA : sig.Adm) {Δ : Finset Var}
    {Γ : Ctx} {e : LExpr} (hwf : LWf sig.funs Δ Γ e) (hadm : e.Adm) {H : Heap}
    {R : Multiset Var} {RC : Multiset Nat} {σ : Nat → Option LVal}
    (h : HInv sig.funs H R RC Γ σ) (hΔ : ∀ x ∈ Δ, x ∈ R) {vs : List LVal}
    (hev : LSteps sig (e.subst (locS σ)) (.ret vs)) :
    ∃ (H' : Heap) (ys : List Var) (σ' : Nat → Option LVal),
      HSteps sig H e H' (.ret (ys.map .var)) ∧ ys.map (rd σ') = vs ∧
      H'.Linear ∧ Ctx.vars H'.roots = R + (ys : Multiset Var) ∧
      HInv sig.funs H' R RC (locCtx (ys.map .var)) σ' ∧ (∀ l, Var.loc l ∈ R → σ' l = σ l) := by
  obtain ⟨n, hn⟩ := LStepsN.of_steps hev
  obtain ⟨H', ys, σ', hs, h', hag, hrd⟩ := hmain hsig hsigA n hwf hadm h hΔ hn
  refine ⟨H', ys, σ', hs, hrd, h'.linear, ?_, h', hag⟩
  rw [h'.vars_roots, locCtx_map, Ctx.vars_map_var]

theorem locS_none : locS (fun _ => none) = fun _ => none := by
  funext y; cases y <;> rfl

/-- **Theorem 6 for closed programs.**  If `∅ | ∅ ⊢ e` is admissible and `e ⟼* v̄`, then
    `∅ | e ⟼*ₕ H | ȳ` where `[H]ȳ = v̄`, `H` is linear, its roots are exactly the locations
    `ȳ`, and every non-empty reuse credit has been consumed. -/
theorem heap_sound_closed {sig : LSig} (hsig : sig.Wf) (hsigA : sig.Adm) {e : LExpr}
    (hwf : LWf sig.funs ∅ 0 e) (hadm : e.Adm) {vs : List LVal}
    (hev : LSteps sig e (.ret vs)) :
    ∃ (H : Heap) (ys : List Var) (σ : Nat → Option LVal),
      HSteps sig 0 e H (.ret (ys.map .var)) ∧ H.Reads σ ∧ ys.map (rd σ) = vs ∧
      H.Linear ∧ Ctx.vars H.roots = (ys : Multiset Var) ∧ nz H.creditsM = 0 := by
  obtain ⟨H, ys, σ, hs, hrd, hlin, hroots, h, -⟩ :=
    heap_sound_corrected hsig hsigA hwf hadm (HInv.empty sig.funs) (by simp)
      (by rw [locS_none, LExpr.subst_none]; exact hev)
  refine ⟨H, ys, σ, hs, h.reads, hrd, hlin, by simpa using hroots, ?_⟩
  rw [h.cred, locCtx_cr]; rfl

end FIP.Lam
