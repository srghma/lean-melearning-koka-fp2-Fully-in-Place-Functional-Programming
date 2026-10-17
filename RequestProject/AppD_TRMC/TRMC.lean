module

public import RequestProject.AppC_StackBound.Stack
public import RequestProject.Sec2_Calculus.CheckSound
public import RequestProject.AppB_StoreSoundness.Weaken

@[expose] public section

/- ══════════════════ PAPER sec. 3.1, App. D START: Tail Recursion Modulo Reusable Defunctionalized CPS Contexts: Theorem 5; TRMC with Reuse Translation (PDF pp. 15-17; App. D on pp. 67-71, Fig. 12) ══════════════════
   Accumulators (Lemma 41), tail-context replacement (Lemma 43) and typed evaluation
   contexts (Lemma 45) for the TRMC-with-reuse translation. -/

/-!
# Tail recursion modulo contexts with reuse (Section 5, Appendix D)

The TRMC translation of Fig. 12 turns a function `f(ȳ; x̄)` whose recursive calls are
under an evaluation context into a tail-recursive `f'(ȳ; x̄, k)` together with a function
`app(ȳ; k, x')` that plugs a value into a *defunctionalized* context `k`.  The
defunctionalized context is built by accumulators `AccE(Γ; k')`, which reuse the reuse
credits `⋄k` of the frame they replace:

```
AccE(∅; k') = k'
AccE(Γ, ⋄k, x₁, …, xₙ; k') = Cᵏ_E x₁ … xₙ AccE(Γ; k') C_unit … C_unit   (0 ≤ n < k)
```

This file formalizes

* accumulators and **Lemma 41** (`accE_wf`): accumulators are FIP;
* tail contexts `T` with *all* their leaves replaced (`TailRepl`) and **Lemma 43**
  (`Wf.tailRepl`): the replacement lemma for tail contexts;
* the typing `Δ | Γ ⊢ E[□]` of evaluation contexts (`ECtx.Wf`) and **Lemma 45**
  (`ECtx.Wf.plug_val`): the value replacement lemma, together with the fact that a typed
  context can be filled by any typed expression (`ECtx.Wf.plug_gen`).

With de Bruijn indices the replacement lemma needs no side condition about the binders of
the tail context: under `k` binders the extra resources `Γ''` are simply weakened to
`Γ''.shift k`, which is built into `TailRepl`.
-/

namespace FIP

/-! ## Accumulators (Lemma 41) -/

/-- A frame `⋄k, x₁, …, xₙ` of an accumulator: a reuse credit of size `k` (from which the
    constructor `Cᵏ_E` is built) and the owned variables `xᵢ` it stores, `n < k`. -/
structure AccFrame (n : Nat) where
  /-- the constructor `C_E` of the defunctionalized context -/
  ctor : CName
  /-- the size `k` of the reuse credit -/
  size : Nat
  /-- the owned variables stored in the frame -/
  vars : List (Var n)
  lt : vars.length < size

/-- The name of the padding atom `C_unit`. -/
def unitCtor : CName := "Unit"

/-- The accumulator `AccE(Γ; k')`. -/
def accE {n : Nat} : List (AccFrame n) → Var n → Val n
  | [], k' => .var k'
  | fr :: frs, k' =>
    .ctor fr.ctor (fr.vars.map .var ++ [accE frs k'] ++
      List.replicate (fr.size - fr.vars.length - 1) (Val.ctor unitCtor []))

/-- The owned environment `Γ` of the frames of an accumulator. -/
def AccFrame.ctx {n : Nat} : List (AccFrame n) → Ctx n
  | [] => 0
  | fr :: frs => ((fr.vars.map Res.var : List (Res n)) : Ctx n) + {Res.credit fr.size} +
      AccFrame.ctx frs

theorem WfVals.append {n : Nat} {U Δ : Finset (Var n)} {Γ₁ Γ₂ : Ctx n} {vs ws : List (Val n)} :
    WfVals U Δ Γ₁ vs → WfVals U Δ Γ₂ ws → WfVals U Δ (Γ₁ + Γ₂) (vs ++ ws)
  | .nil, h₂ => by simpa using h₂
  | .cons _ _ _ _ hv h₁, h₂ => by
    have := WfVals.cons _ _ _ _ hv (WfVals.append h₁ h₂)
    rw [add_assoc]; exact this

theorem WfVals.vars {n : Nat} {U Δ : Finset (Var n)} (xs : List (Var n)) :
    WfVals U Δ ((xs.map Res.var : List (Res n)) : Ctx n) (xs.map .var) := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih =>
    have := WfVals.cons _ _ _ _ (WfVal.var (U := U) (Δ := Δ) x) ih
    simpa [Multiset.singleton_add] using this

theorem WfVals.units {n : Nat} {U Δ : Finset (Var n)} (k : Nat) :
    WfVals U Δ 0 (List.replicate k (Val.ctor unitCtor [])) := by
  induction k with
  | zero => exact .nil
  | succ k ih =>
    have := WfVals.cons _ _ _ _ (WfVal.atom (U := U) (Δ := Δ) unitCtor) ih
    simpa [List.replicate_succ] using this

/-- **Lemma 41** (accumulators are FIP): `∅ | Γ, k' ⊢ AccE(Γ; k')`. -/
theorem accE_wf {n : Nat} {U Δ : Finset (Var n)} (k' : Var n) :
    ∀ frs : List (AccFrame n), WfVal U Δ (AccFrame.ctx frs + {Res.var k'}) (accE frs k')
  | [] => by simpa [AccFrame.ctx, accE] using WfVal.var (U := U) (Δ := Δ) k'
  | fr :: frs => by
    have ih := accE_wf (U := U) (Δ := Δ) k' frs
    have hvs := ((WfVals.vars (U := U) (Δ := Δ) fr.vars).append
      (WfVals.cons _ _ _ _ ih .nil)).append
      (WfVals.units (U := U) (Δ := Δ) (fr.size - fr.vars.length - 1))
    have hlen : (fr.vars.map Val.var ++ [accE frs k'] ++
        List.replicate (fr.size - fr.vars.length - 1) (Val.ctor unitCtor [])).length =
        fr.size := by
      have := fr.lt; simp; omega
    have := WfVal.reuse fr.ctor _ _ (by simp) hvs
    rw [hlen] at this
    simp only [accE, AccFrame.ctx]
    convert this using 1
    simp only [add_zero]
    abel

/-! ## Tail contexts (Lemma 43) -/

mutual
/-- `TailRepl R Γ'' e e'`: `e = T[e₁, …, eₙ]` and `e' = T[e₁', …, eₙ']` for a tail context
    `T ::= □ | let x̄ = e₀ in T | match e₀ {pᵢ ↦ Tᵢ} | match! e₀ {pᵢ ↦ Tᵢ} | drop x; T
    | free k; T` whose leaves are related by `R Γ''ᵢ eᵢ eᵢ'`, where `Γ''ᵢ` is the extra
    resource environment `Γ''` weakened past the binders above the leaf. -/
inductive TailRepl (R : ∀ {m : Nat}, Ctx m → Expr m → Expr m → Prop) :
    {n : Nat} → Ctx n → Expr n → Expr n → Prop where
  | leaf {n : Nat} {G : Ctx n} {e e' : Expr n} : R G e e' → TailRepl R G e e'
  | letIn {n : Nat} {G : Ctx n} {xs : List Bool} {e₀ : Expr n} {e e' : Expr (n + xs.length)} :
      TailRepl R (G.shift xs.length) e e' → TailRepl R G (.letIn xs e₀ e) (.letIn xs e₀ e')
  | bmatch {n : Nat} {G : Ctx n} {e₀ : Expr n} {bs bs' : Branches n} :
      TailReplB R G bs bs' → TailRepl R G (.bmatch e₀ bs) (.bmatch e₀ bs')
  | dmatch {n : Nat} {G : Ctx n} {e₀ : Expr n} {bs bs' : Branches n} :
      TailReplB R G bs bs' → TailRepl R G (.dmatch e₀ bs) (.dmatch e₀ bs')
  | drop {n : Nat} {G : Ctx n} {x : Val n} {e e' : Expr n} :
      TailRepl R G e e' → TailRepl R G (.drop x e) (.drop x e')
  | free {n : Nat} {G : Ctx n} {k : Nat} {e e' : Expr n} :
      TailRepl R G e e' → TailRepl R G (.free k e) (.free k e')
/-- The branches of a match of a tail context, with their tail contexts replaced. -/
inductive TailReplB (R : ∀ {m : Nat}, Ctx m → Expr m → Expr m → Prop) :
    {n : Nat} → Ctx n → Branches n → Branches n → Prop where
  | nil {n : Nat} {G : Ctx n} : TailReplB R G .nil .nil
  | cons {n : Nat} {G : Ctx n} {c : CName} {xs : List Bool} {e e' : Expr (n + xs.length)}
      {bs bs' : Branches n} : TailRepl R (G.shift xs.length) e e' → TailReplB R G bs bs' →
      TailReplB R G (.cons c xs e bs) (.cons c xs e' bs')
end

theorem TailReplB.mem_right {R : ∀ {m : Nat}, Ctx m → Expr m → Expr m → Prop} {n : Nat}
    {G : Ctx n} : ∀ {bs bs' : Branches n}, TailReplB R G bs bs' →
    ∀ {b' : Branch n}, b' ∈ bs'.toList →
      ∃ e, (⟨b'.ctor, b'.binders, e⟩ : Branch n) ∈ bs.toList ∧
        TailRepl R (G.shift b'.binders.length) e b'.body
  | _, _, .nil, _, hb => by simp at hb
  | _, _, .cons (e := e) ht hbs, b', hb => by
    rw [Branches.toList_cons, List.mem_cons] at hb
    rcases hb with rfl | hb
    · exact ⟨e, by simp, ht⟩
    · obtain ⟨e₁, hm, h⟩ := TailReplB.mem_right hbs hb
      exact ⟨e₁, by simp [hm], h⟩

/-- **Lemma 43** (replacement lemma for tail contexts).  Let `Δ | Γ ⊢ T[e]`, and suppose
    that each leaf `eᵢ` of the tail context may be replaced by `eᵢ'` using the extra
    resources `Γ''` (`Δ' | Γ' ⊢ eᵢ` implies `Δ' | Γ', Γ'' ⊢ eᵢ'`).  Then
    `Δ | Γ, Γ'' ⊢ T[e']`. -/
theorem Wf.tailRepl {cfg : Cfg} {R : ∀ {m : Nat}, Ctx m → Expr m → Expr m → Prop}
    (hR : ∀ {m : Nat} {U Δ : Finset (Var m)} {Γ G : Ctx m} {e e' : Expr m}, R G e e' →
      Wf cfg U Δ Γ e → Wf cfg U Δ (Γ + G) e')
    {n : Nat} {U Δ : Finset (Var n)} {Γ : Ctx n} {e : Expr n} (h : Wf cfg U Δ Γ e) :
    ∀ {G : Ctx n} {e' : Expr n}, TailRepl R G e e' → Wf cfg U Δ (Γ + G) e' := by
  induction h with
  | tuple hv => intro G e' ht; cases ht with | leaf hr => exact hR hr (.tuple hv)
  | call f ys e hf hy he _ =>
    intro G e' ht; cases ht with | leaf hr => exact hR hr (.call f ys e hf hy he)
  | bapp y e hy he _ =>
    intro G e' ht; cases ht with | leaf hr => exact hR hr (.bapp y e hy he)
  | fapp f e hf he _ =>
    intro G e' ht; cases ht with | leaf hr => exact hR hr (.fapp f e hf he)
  | prim op vs hv => intro G e' ht; cases ht with | leaf hr => exact hR hr (.prim op vs hv)
  | letIn Γ₁ Γ₂ Γ₃ xs e₁ e₂ h2 h1 hb _ ih =>
    intro G e' ht
    cases ht with
    | leaf hr => exact hR hr (.letIn Γ₁ Γ₂ Γ₃ xs e₁ e₂ h2 h1 hb)
    | letIn ht =>
      have hb' := ih ht
      have := Wf.letIn Γ₁ Γ₂ (Γ₃ + G) xs e₁ _ h2 h1
        (Wf.cast (by rw [Ctx.shift_add, Ctx.shift_add, Ctx.shift_add]; abel) hb')
      exact Wf.cast (by abel) this
  | bmatch y bs hy hbs ih =>
    intro G e' ht
    cases ht with
    | leaf hr => exact hR hr (.bmatch y bs hy hbs)
    | bmatch hf =>
      rename_i bs'
      refine Wf.bmatch y bs' hy fun b' hb' => ?_
      obtain ⟨e₁, hm, ht⟩ := hf.mem_right hb'
      have := ih _ hm ht
      rw [Ctx.shift_add]
      exact this
  | @dmatch n U₀ Δ₀ Γ₀ x bs hbs ih =>
    intro G e' ht
    cases ht with
    | leaf hr => exact hR hr (.dmatch x bs hbs)
    | dmatch hf =>
      rename_i bs'
      refine Wf.cast (by abel) (Wf.dmatch (Γ := Γ₀ + G) x bs' fun b' hb' => ?_)
      obtain ⟨e₁, hm, ht⟩ := hf.mem_right hb'
      have := ih _ hm ht
      refine Wf.cast ?_ this
      rw [Ctx.shift_add]
      abel
  | empty h ih =>
    intro G e' ht
    exact Wf.cast (by abel) (Wf.empty (ih ht))
  | drop x hfb he ih =>
    intro G e' ht
    cases ht with
    | leaf hr => exact hR hr (.drop x hfb he)
    | drop ht => exact Wf.cast (by abel) (Wf.drop x hfb (ih ht))
  | free k hfb hk he ih =>
    intro G e' ht
    cases ht with
    | leaf hr => exact hR hr (.free k hfb hk he)
    | free ht => exact Wf.cast (by abel) (Wf.free k hfb hk (ih ht))
  | @inst n U₀ Δ₀ Γ₀ e₀ k hk he ih =>
    intro G e' ht
    exact Wf.cast (by abel) (Wf.inst (Γ := Γ₀ + G) k hk (Wf.cast (by abel) (ih ht)))
  | weaken he ih =>
    intro G e' ht
    exact Wf.cast (by abel) (Wf.weaken (ih ht))

/-! ## Typed evaluation contexts (Lemma 45) -/

/-- The judgment `Δ | Γ ⊢ E[□]` for evaluation contexts whose hole is in an argument
    position of a well-formed expression: the owned argument of a call `f(ȳ; E)`, the
    argument of an application `y E` or `(f) E`, or the bound expression of a
    `let x̄ = E in e` (which borrows the variables `Γ₂` of the body). -/
inductive ECtx.Wf (cfg : Cfg) {n : Nat} : Finset (Var n) → Finset (Var n) → Ctx n → ECtx n → Prop
    where
  | hole {U Δ} : ECtx.Wf cfg U Δ 0 .hole
  | callO {U Δ Γ E} (f : FName) (ys : List (Val n)) :
      f ∈ cfg.funs → (∀ y ∈ ys, BorrowArg cfg U Δ y) → ECtx.Wf cfg U Δ Γ E →
      ECtx.Wf cfg U Δ
        (Γ + Multiset.replicate (cfg.budget f + (ys.map (fnBudget cfg)).sum) Res.alloc)
        (.callO f ys E)
  | bapp {U Δ Γ E} (y : Var n) : y ∈ Δ → ECtx.Wf cfg U Δ Γ E →
      ECtx.Wf cfg U Δ Γ (.appR [.var y] E)
  | fapp {U Δ Γ E} (f : FName) : f ∈ cfg.funs → ECtx.Wf cfg U Δ Γ E →
      ECtx.Wf cfg U Δ (Γ + Multiset.replicate (cfg.budget f) Res.alloc) (.appR [.fn f] E)
  | letIn {U Δ E} (Γ₁ Γ₂ Γ₃ : Ctx n) (xs : List Bool) (e₂ : Expr (n + xs.length)) :
      Γ₂.OnlyVars →
      ECtx.Wf cfg U (Δ ∪ Γ₂.vars.toFinset) Γ₁ E →
      FIP.Wf cfg (Vars.shift xs.length U ∪ Binder.scalars xs) (Vars.shift xs.length Δ)
        ((Γ₂ + Γ₃).shift xs.length + Binder.owned xs) e₂ →
      ECtx.Wf cfg U Δ (Γ₁ + Γ₂ + Γ₃) (.letIn xs E e₂)

/-- A typed context can be filled with any expression typed in the hole's environments,
    extended by `Γ'`. -/
theorem ECtx.Wf.plug_gen {cfg : Cfg} {n : Nat} {U Δ : Finset (Var n)} {Γ : Ctx n} {E : ECtx n}
    (hE : ECtx.Wf cfg U Δ Γ E) {Γ' : Ctx n} {e : Expr n}
    (he : ∀ Δ', Δ ⊆ Δ' → FIP.Wf cfg U Δ' Γ' e) : FIP.Wf cfg U Δ (Γ + Γ') (E.plug e) := by
  induction hE with
  | hole => simpa [ECtx.plug] using he _ (subset_refl _)
  | callO f ys hf hy _ ih =>
    exact FIP.Wf.cast (by abel) (FIP.Wf.call f ys _ hf hy (ih he))
  | bapp y hy _ ih => exact FIP.Wf.bapp y _ hy (ih he)
  | fapp f hf _ ih => exact FIP.Wf.cast (by abel) (FIP.Wf.fapp f _ hf (ih he))
  | letIn Γ₁ Γ₂ Γ₃ xs e₂ h2 _ hb ih =>
    have := FIP.Wf.letIn (Γ₁ + Γ') Γ₂ Γ₃ xs _ e₂ h2
      (ih fun Δ' hΔ' => he Δ' (Finset.subset_union_left.trans hΔ')) hb
    exact FIP.Wf.cast (by abel) this

/-- **Lemma 45** (value replacement lemma): if `Δ | Γ ⊢ E[□]` and `∅ | Γ' ⊢ v` then
    `Δ | Γ, Γ' ⊢ E[v]`. -/
theorem ECtx.Wf.plug_val {cfg : Cfg} {n : Nat} {U Δ : Finset (Var n)} {Γ : Ctx n} {E : ECtx n}
    (hE : ECtx.Wf cfg U Δ Γ E) {Γ' : Ctx n} {v : Val n} (hv : WfVal U ∅ Γ' v) :
    FIP.Wf cfg U Δ (Γ + Γ') (E.plug (.val v)) :=
  hE.plug_gen fun _ _ => by
    simpa using FIP.Wf.tuple (WfVals.cons _ _ _ _ (WfVal.anyΔ hv) .nil)

end FIP

/- ══════════════════ PAPER sec. 3.1, App. D END: Tail Recursion Modulo Reusable Defunctionalized CPS Contexts: Theorem 5; TRMC with Reuse Translation ══════════════════ -/
