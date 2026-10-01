module

public import RequestProject.FIP.Heap

@[expose] public section

/-!
# The stated form of Theorem 6 is false

As for the first statement of Theorem 1 (`RequestProject/FIP/StoreSoundCex.lean`),
`heap_sound` allows heaps to bind *program names* (`Var.name`), while `[H]e` only replaces
locations.  With `H₂ = {x ↦¹ C}` for the name `x`, the expression `x` is well-formed with
`Γ = {x} = roots(H₂)` and evaluates (functionally) to the unsubstituted variable `x`, while
`[H₂]x = C`.

The corrected statement is `heap_sound_corrected` in `RequestProject/FIP/HeapTheorem.lean`.
-/

namespace FIP.Lam

theorem HStep.not_ret_var {sig : LSig} {H H' : Heap} {x : Var} {e0 e' : LExpr}
    (he : e0 = .ret [.var x]) : ¬ HStep sig H e0 H' e' := by
  intro h
  cases h with
  | head E hh =>
    cases E <;> simp [LECtx.plug] at he
    subst he
    cases hh
  | val E done V rest hd hV hv =>
    cases E <;> simp only [LECtx.plug, reduceCtorEq, LExpr.ret.injEq] at he
    rcases done with _ | ⟨d, done⟩
    · simp only [List.nil_append, List.cons.injEq] at he
      obtain ⟨hV', -⟩ := he
      cases V <;> simp [LVCtx.plug] at hV'
      subst hV'
      cases hv
    · simp at he

theorem HSteps.ret_var {sig : LSig} {H H' : Heap} {x : Var} {e0 e' : LExpr}
    (h : HSteps sig H e0 H' e') (he : e0 = .ret [.var x]) : H' = H ∧ e' = e0 := by
  induction h with
  | refl => exact ⟨rfl, rfl⟩
  | tail _ hs ih =>
    obtain ⟨rfl, rfl⟩ := ih he
    exact absurd hs (HStep.not_ret_var he)

theorem HJoin.zero_left_inv {H₂ H : Heap} (h : HJoin 0 H₂ H) : H₂ = H := by
  generalize h0 : (0 : Heap) = Z at h
  cases h with
  | nil => rfl
  | credit k _ => simp at h0
  | fresh x n o _ _ => simp at h0
  | share x n m o _ _ => simp at h0

/-- The statement of Theorem 6 as formalized in `heap_sound`. -/
def HeapSoundClaim : Prop :=
  ∀ {sig : LSig} (_hsig : sig.Wf) {Δ : Finset Var} {Γ : Ctx} {e : LExpr}
    (_h : LWf (sig.map (·.name)) Δ Γ e) {H₁ H₂ H : Heap} (_hj : HJoin H₁ H₂ H)
    (_hΔ : ∀ x ∈ Δ, x ∈ H₁.dom) (_hH₁ : H₁.Sound) (_hΓ : Γ = H₂.roots) (_hH₂ : H₂.Linear)
    {vs : List LVal} (_hev : LSteps sig (H.substE e) (.ret vs)),
    ∃ (H₃ H' : Heap) (xs : List Var), HJoin H₁ H₃ H' ∧
      HSteps sig H e H' (.ret (xs.map .var)) ∧
      xs.map (fun x => H₃.read (.var x)) = vs ∧
      H₃.roots = (xs : Multiset Var).map Res.var ∧ H₃.Linear

/-- The statement of Theorem 6 in `heap_sound` is false: a heap binding a program name is a
    counterexample. -/
theorem not_heapSoundClaim : ¬ HeapSoundClaim := by
  intro Hc
  let x : Var := .name "x"
  let H₂ : Heap := {HCell.bind x 1 (.con "C" [])}
  have hrng : H₂.rngFv = 0 := by simp [H₂, Heap.rngFv, HObj.fv, LVal.fvList]
  have hroots : ({Res.var x} : Ctx) = H₂.roots := by
    simp [H₂, Heap.roots, Heap.rngFv, HObj.fv, LVal.fvList]
  have hwf : LWf [] ∅ {Res.var x} (.ret [.var x]) := by
    have := LWfVals.cons (funs := []) (Δ := ∅) _ _ _ _ (LWfVal.var x) LWfVals.nil
    simp only [add_zero] at this
    exact .tuple this
  have hlin : H₂.Linear := by
    refine ⟨⟨by simp [H₂, Heap.dom], ?_, ?_⟩, ?_⟩
    · intro y n o hc; simp [H₂] at hc; omega
    · rw [hrng]; simp
    · intro y n o hc; rw [hrng]; simp
  have hsub : H₂.substE (.ret [.var x]) = .ret [.var x] := by
    simp [Heap.substE, LExpr.subst, LVal.substList, LVal.subst, x]
  obtain ⟨H₃, H', xs, hj, hs, hr, -, -⟩ := Hc (sig := []) (by simp [LSig.Wf])
    hwf (H₁ := 0) (H₂ := H₂) (H := H₂) (.nil _) (by simp) (by simp [Heap.Sound, Heap.dom, Heap.rngFv])
    hroots hlin (vs := [.var x]) (by rw [hsub])
  obtain ⟨h1, h2⟩ := hs.ret_var rfl
  subst h1
  have h3 := hj.zero_left_inv
  subst h3
  cases xs with
  | nil => simp at h2
  | cons y ys =>
    cases ys with
    | cons => simp at h2
    | nil =>
      simp only [List.map_cons, List.map_nil, LExpr.ret.injEq, List.cons.injEq, LVal.var.injEq,
        and_true] at h2
      subst h2
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hr
      have hl : H₂.lookup x = some (.con "C" []) := by
        have hex : ∃ p : Nat × HObj, HCell.bind x p.1 p.2 ∈ H₂ :=
          ⟨(1, .con "C" []), by simp [H₂]⟩
        unfold Heap.lookup
        rw [dif_pos hex, Option.some_inj]
        have := hex.choose_spec
        generalize hex.choose = p at this
        change HCell.bind x p.1 p.2 ∈ ({HCell.bind x 1 (.con "C" [])} : Heap) at this
        simp only [Multiset.mem_singleton, HCell.bind.injEq, true_and] at this
        exact this.2
      unfold Heap.read at hr
      rw [show Multiset.card H₂ + sizeOf (LVal.var x) + 1 = (Multiset.card H₂ + sizeOf (LVal.var x)) + 1
        from rfl, Heap.readN, hl] at hr
      simp at hr

end FIP.Lam
