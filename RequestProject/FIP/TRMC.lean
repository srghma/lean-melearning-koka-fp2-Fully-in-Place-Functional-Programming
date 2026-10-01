module

public import RequestProject.FIP.Stack
public import RequestProject.FIP.CheckSound

@[expose] public section

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
  context can be filled by any typed expression (`ECtx.Wf.plug`).

Binders are named, so the replacement lemma needs the (Barendregt) side condition that the
binders of the tail context are not among the new resources `Γ''`; the paper leaves this
implicit.
-/

namespace FIP

/-! ## Accumulators (Lemma 41) -/

/-- A frame `⋄k, x₁, …, xₙ` of an accumulator: a reuse credit of size `k` (from which the
    constructor `Cᵏ_E` is built) and the owned variables `xᵢ` it stores, `n < k`. -/
structure AccFrame where
  /-- the constructor `C_E` of the defunctionalized context -/
  ctor : CName
  /-- the size `k` of the reuse credit -/
  size : Nat
  /-- the owned variables stored in the frame -/
  vars : List Var
  lt : vars.length < size

/-- The name of the padding atom `C_unit`. -/
def unitCtor : CName := "Unit"

/-- The accumulator `AccE(Γ; k')`. -/
def accE : List AccFrame → Var → Val
  | [], k' => .var k'
  | fr :: frs, k' =>
    .ctor fr.ctor (fr.vars.map .var ++ [accE frs k'] ++
      List.replicate (fr.size - fr.vars.length - 1) (Val.ctor unitCtor []))

/-- The owned environment `Γ` of the frames of an accumulator. -/
def AccFrame.ctx : List AccFrame → Ctx
  | [] => 0
  | fr :: frs => ((fr.vars.map Res.var : List Res) : Ctx) + {Res.credit fr.size} +
      AccFrame.ctx frs

theorem WfVals.append {U Δ : Finset Var} {Γ₁ Γ₂ : Ctx} {vs ws : List Val} :
    WfVals U Δ Γ₁ vs → WfVals U Δ Γ₂ ws → WfVals U Δ (Γ₁ + Γ₂) (vs ++ ws)
  | .nil, h₂ => by simpa using h₂
  | .cons _ _ _ _ hv h₁, h₂ => by
    have := WfVals.cons _ _ _ _ hv (WfVals.append h₁ h₂)
    rw [add_assoc]; exact this

theorem WfVals.vars {U Δ : Finset Var} (xs : List Var) :
    WfVals U Δ ((xs.map Res.var : List Res) : Ctx) (xs.map .var) := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih =>
    have := WfVals.cons _ _ _ _ (WfVal.var (U := U) (Δ := Δ) x) ih
    simpa [Multiset.singleton_add] using this

theorem WfVals.units {U Δ : Finset Var} (n : Nat) :
    WfVals U Δ 0 (List.replicate n (Val.ctor unitCtor [])) := by
  induction n with
  | zero => exact .nil
  | succ n ih =>
    have := WfVals.cons _ _ _ _ (WfVal.atom (U := U) (Δ := Δ) unitCtor) ih
    simpa [List.replicate_succ] using this

/-- **Lemma 41** (accumulators are FIP): `∅ | Γ, k' ⊢ AccE(Γ; k')`. -/
theorem accE_wf {U Δ : Finset Var} (k' : Var) :
    ∀ frs : List AccFrame, WfVal U Δ (AccFrame.ctx frs + {Res.var k'}) (accE frs k')
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
/-- The names bound anywhere in an expression. -/
def Expr.binders : Expr → List String
  | .ret _ => []
  | .app e1 e2 => Expr.binders e1 ++ Expr.binders e2
  | .call _ e1 e2 => Expr.binders e1 ++ Expr.binders e2
  | .letIn xs e1 e2 => xs.map (·.name) ++ Expr.binders e1 ++ Expr.binders e2
  | .bmatch e bs => Expr.binders e ++ Expr.bindersB bs
  | .dmatch e bs => Expr.binders e ++ Expr.bindersB bs
  | .drop _ e => Expr.binders e
  | .free _ e => Expr.binders e
  | .prim _ _ => []
/-- The names bound anywhere in the branches of a match. -/
def Expr.bindersB : List Branch → List String
  | [] => []
  | .mk _ xs e :: bs => xs.map (·.name) ++ Expr.binders e ++ Expr.bindersB bs
end

mutual
/-- `TailRepl R e e'`: `e = T[e₁, …, eₙ]` and `e' = T[e₁', …, eₙ']` for a tail context
    `T ::= □ | let x̄ = e₀ in T | match e₀ {pᵢ ↦ Tᵢ} | match! e₀ {pᵢ ↦ Tᵢ} | drop x; T
    | free k; T` whose leaves are related by `R eᵢ eᵢ'`. -/
inductive TailRepl (R : Expr → Expr → Prop) : Expr → Expr → Prop where
  | leaf {e e'} : R e e' → TailRepl R e e'
  | letIn {xs e₀ e e'} : TailRepl R e e' → TailRepl R (.letIn xs e₀ e) (.letIn xs e₀ e')
  | bmatch {e₀ bs bs'} : TailReplB R bs bs' → TailRepl R (.bmatch e₀ bs) (.bmatch e₀ bs')
  | dmatch {e₀ bs bs'} : TailReplB R bs bs' → TailRepl R (.dmatch e₀ bs) (.dmatch e₀ bs')
  | drop {x e e'} : TailRepl R e e' → TailRepl R (.drop x e) (.drop x e')
  | free {k e e'} : TailRepl R e e' → TailRepl R (.free k e) (.free k e')
/-- The branches of a match of a tail context, with their tail contexts replaced. -/
inductive TailReplB (R : Expr → Expr → Prop) : List Branch → List Branch → Prop where
  | nil : TailReplB R [] []
  | cons {c xs e e' bs bs'} : TailRepl R e e' → TailReplB R bs bs' →
      TailReplB R (.mk c xs e :: bs) (.mk c xs e' :: bs')
end

theorem TailReplB.mem_right {R : Expr → Expr → Prop} {bs bs' : List Branch} :
    TailReplB R bs bs' → ∀ {b'}, b' ∈ bs' →
      ∃ b ∈ bs, b.binders = b'.binders ∧ TailRepl R b.body b'.body
  | .nil, _, hb => by simp at hb
  | .cons (c := c) (xs := xs) (e := e) ht hbs, b', hb => by
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨.mk c xs e, List.mem_cons_self .., rfl, ht⟩
    · obtain ⟨b, hb, h⟩ := TailReplB.mem_right hbs hb
      exact ⟨b, List.mem_cons_of_mem _ hb, h⟩

theorem Branch.eta (b : Branch) : b = .mk b.ctor b.binders b.body := by cases b; rfl

theorem Expr.mem_bindersB {bs : List Branch} {b : Branch} (hb : b ∈ bs) {s : String}
    (hs : s ∈ b.binders.map (·.name) ∨ s ∈ b.body.binders) : s ∈ Expr.bindersB bs := by
  induction bs with
  | nil => simp at hb
  | cons b' bs ih =>
    obtain ⟨c, xs, e⟩ := b'
    simp only [Expr.bindersB, List.mem_append]
    rcases List.mem_cons.mp hb with rfl | hb
    · simp only [Branch.binders, Branch.body] at hs; tauto
    · exact .inr (ih hb)

theorem Binder.Fresh.add {xs : List Binder} {U Δ : Finset Var} {Γ Γ'' : Ctx}
    (h : Binder.Fresh xs U Δ Γ) (hΓ : ∀ b ∈ xs, Res.var (.name b.name) ∉ Γ'') :
    Binder.Fresh xs U Δ (Γ + Γ'') := by
  refine ⟨h.1, fun b hb => ⟨(h.2 b hb).1, (h.2 b hb).2.1, ?_⟩⟩
  rw [Multiset.mem_add]; exact fun h' => h'.elim (h.2 b hb).2.2 (hΓ b hb)

/-- **Lemma 43** (replacement lemma for tail contexts).  Let `Δ | Γ ⊢ T[e]`, and suppose
    that each leaf `eᵢ` of the tail context may be replaced by `eᵢ'` using the extra
    resources `Γ''` (`Δ' | Γ' ⊢ eᵢ` implies `Δ' | Γ', Γ'' ⊢ eᵢ'`).  If the binders of `T`
    are not among `Γ''`, then `Δ | Γ, Γ'' ⊢ T[e']`. -/
theorem Wf.tailRepl {cfg : Cfg} {Γ'' : Ctx} {R : Expr → Expr → Prop}
    (hR : ∀ {U Δ Γ e e'}, R e e' → Wf cfg U Δ Γ e → Wf cfg U Δ (Γ + Γ'') e')
    {U Δ : Finset Var} {Γ : Ctx} {e : Expr} (h : Wf cfg U Δ Γ e) :
    ∀ {e'}, TailRepl R e e' → (∀ s ∈ e.binders, Res.var (.name s) ∉ Γ'') →
      Wf cfg U Δ (Γ + Γ'') e' := by
  induction h with
  | tuple hv => intro e' ht _; cases ht with | leaf hr => exact hR hr (.tuple hv)
  | call f ys e hf hy he _ =>
    intro e' ht _; cases ht with | leaf hr => exact hR hr (.call f ys e hf hy he)
  | bapp y e hy he _ =>
    intro e' ht _; cases ht with | leaf hr => exact hR hr (.bapp y e hy he)
  | fapp f e hf he _ =>
    intro e' ht _; cases ht with | leaf hr => exact hR hr (.fapp f e hf he)
  | prim op vs hv => intro e' ht _; cases ht with | leaf hr => exact hR hr (.prim op vs hv)
  | @letIn U₀ Δ₀ Γ₁ Γ₂ Γ₃ xs e₁ e₂ h2 h1 hb hfr _ ih =>
    intro e' ht hbind
    cases ht with
    | leaf hr => exact hR hr (.letIn Γ₁ Γ₂ Γ₃ xs e₁ e₂ h2 h1 hb hfr)
    | letIn ht =>
      have hb' := ih ht (fun s hs => hbind s (by simp [Expr.binders, hs]))
      have hfr' : Binder.Fresh xs U₀ Δ₀ (Γ₂ + (Γ₃ + Γ'')) := by
        rw [← add_assoc]
        exact hfr.add (fun b hb => hbind _ (by simp [Expr.binders]; exact .inl ⟨b, hb, rfl⟩))
      have := Wf.letIn Γ₁ Γ₂ (Γ₃ + Γ'') xs e₁ _ h2 h1
        (Wf.cast (by abel) hb') hfr'
      exact Wf.cast (by abel) this
  | bmatch y bs hy hfr hbs ih =>
    intro e' ht hbind
    cases ht with
    | leaf hr => exact hR hr (.bmatch y bs hy hfr hbs)
    | bmatch hf =>
      rename_i bs'
      refine Wf.bmatch y bs' hy ?_ ?_
      · intro b' hb'
        obtain ⟨b, hb, hxs, _⟩ := hf.mem_right hb'
        rw [← hxs]
        exact (hfr b hb).add (fun x hx => hbind _ (by
          simp only [Expr.binders, List.mem_append]
          exact .inr (Expr.mem_bindersB hb (.inl (List.mem_map_of_mem hx)))))
      · intro b' hb'
        obtain ⟨b, hb, hxs, ht⟩ := hf.mem_right hb'
        rw [← hxs]
        exact ih b hb ht (fun s hs => hbind s (by
          simp only [Expr.binders, List.mem_append]
          exact .inr (Expr.mem_bindersB hb (.inr hs))))
  | @dmatch U₀ Δ₀ Γ₀ x bs hfr hbs ih =>
    intro e' ht hbind
    cases ht with
    | leaf hr => exact hR hr (.dmatch x bs hfr hbs)
    | dmatch hf =>
      rename_i bs'
      refine Wf.cast (by abel) (Wf.dmatch (Γ := Γ₀ + Γ'') x bs' ?_ ?_)
      · intro b' hb'
        obtain ⟨b, hb, hxs, _⟩ := hf.mem_right hb'
        rw [← hxs]
        exact (hfr b hb).add (fun x hx => hbind _ (by
          simp only [Expr.binders, List.mem_append]
          exact .inr (Expr.mem_bindersB hb (.inl (List.mem_map_of_mem hx)))))
      · intro b' hb'
        obtain ⟨b, hb, hxs, ht⟩ := hf.mem_right hb'
        rw [← hxs]
        exact Wf.cast (by abel) (ih b hb ht (fun s hs => hbind s (by
          simp only [Expr.binders, List.mem_append]
          exact .inr (Expr.mem_bindersB hb (.inr hs)))))
  | empty h ih =>
    intro e' ht hbind
    exact Wf.cast (by abel) (Wf.empty (ih ht hbind))
  | drop x hfb he ih =>
    intro e' ht hbind
    cases ht with
    | leaf hr => exact hR hr (.drop x hfb he)
    | drop ht => exact Wf.cast (by abel) (Wf.drop x hfb (ih ht hbind))
  | free k hfb hk he ih =>
    intro e' ht hbind
    cases ht with
    | leaf hr => exact hR hr (.free k hfb hk he)
    | free ht => exact Wf.cast (by abel) (Wf.free k hfb hk (ih ht hbind))
  | @inst U₀ Δ₀ Γ₀ e₀ k hk he ih =>
    intro e' ht hbind
    exact Wf.cast (by abel) (Wf.inst (Γ := Γ₀ + Γ'') k hk (Wf.cast (by abel) (ih ht hbind)))
  | weaken he ih =>
    intro e' ht hbind
    exact Wf.cast (by abel) (Wf.weaken (ih ht hbind))

/-! ## Typed evaluation contexts (Lemma 45) -/

/-- The judgment `Δ | Γ ⊢ E[□]` for evaluation contexts whose hole is in an argument
    position of a well-formed expression: the owned argument of a call `f(ȳ; E)`, the
    argument of an application `y E` or `(f) E`, or the bound expression of a
    `let x̄ = E in e` (which borrows the variables `Γ₂` of the body). -/
inductive ECtx.Wf (cfg : Cfg) : Finset Var → Finset Var → Ctx → ECtx → Prop where
  | hole {U Δ} : ECtx.Wf cfg U Δ 0 .hole
  | callO {U Δ Γ E} (f : FName) (ys : List Val) :
      f ∈ cfg.funs → (∀ y ∈ ys, BorrowArg cfg U Δ y) → ECtx.Wf cfg U Δ Γ E →
      ECtx.Wf cfg U Δ
        (Γ + Multiset.replicate (cfg.budget f + (ys.map (fnBudget cfg)).sum) Res.alloc)
        (.callO f ys E)
  | bapp {U Δ Γ E} (y : Var) : y ∈ Δ → ECtx.Wf cfg U Δ Γ E →
      ECtx.Wf cfg U Δ Γ (.appR [.var y] E)
  | fapp {U Δ Γ E} (f : FName) : f ∈ cfg.funs → ECtx.Wf cfg U Δ Γ E →
      ECtx.Wf cfg U Δ (Γ + Multiset.replicate (cfg.budget f) Res.alloc) (.appR [.fn f] E)
  | letIn {U Δ E} (Γ₁ Γ₂ Γ₃ : Ctx) (xs : List Binder) (e₂ : Expr) :
      Γ₂.OnlyVars →
      ECtx.Wf cfg U (Δ ∪ Γ₂.vars.toFinset) Γ₁ E →
      FIP.Wf cfg (U ∪ Binder.scalars xs) Δ (Γ₂ + Γ₃ + Binder.owned xs) e₂ →
      Binder.Fresh xs U Δ (Γ₂ + Γ₃) →
      ECtx.Wf cfg U Δ (Γ₁ + Γ₂ + Γ₃) (.letIn xs E e₂)

/-- A typed context can be filled with any expression typed in the hole's environments,
    extended by `Γ'`. -/
theorem ECtx.Wf.plug_gen {cfg : Cfg} {U Δ : Finset Var} {Γ : Ctx} {E : ECtx}
    (hE : ECtx.Wf cfg U Δ Γ E) {Γ' : Ctx} {e : Expr}
    (he : ∀ Δ', Δ ⊆ Δ' → FIP.Wf cfg U Δ' Γ' e) : FIP.Wf cfg U Δ (Γ + Γ') (E.plug e) := by
  induction hE with
  | hole => simpa [ECtx.plug] using he _ (subset_refl _)
  | callO f ys hf hy _ ih =>
    exact FIP.Wf.cast (by abel) (FIP.Wf.call f ys _ hf hy (ih he))
  | bapp y hy _ ih => exact FIP.Wf.bapp y _ hy (ih he)
  | fapp f hf _ ih => exact FIP.Wf.cast (by abel) (FIP.Wf.fapp f _ hf (ih he))
  | letIn Γ₁ Γ₂ Γ₃ xs e₂ h2 _ hb hfr ih =>
    have := FIP.Wf.letIn (Γ₁ + Γ') Γ₂ Γ₃ xs _ e₂ h2
      (ih fun Δ' hΔ' => he Δ' (Finset.subset_union_left.trans hΔ')) hb hfr
    exact FIP.Wf.cast (by abel) this

mutual
/-- The borrowed environment plays no role in typing values. -/
theorem WfVal.anyΔ {U Δ Δ' : Finset Var} {Γ : Ctx} {v : Val} :
    WfVal U Δ Γ v → WfVal U Δ' Γ v
  | .var x => .var x
  | .svar x hx => .svar x hx
  | .atom c => .atom c
  | .lit n => .lit n
  | .reuse c vs Γ hne hvs => .reuse c vs Γ hne (WfVals.anyΔ hvs)
/-- The borrowed environment plays no role in typing lists of values. -/
theorem WfVals.anyΔ {U Δ Δ' : Finset Var} {Γ : Ctx} {vs : List Val} :
    WfVals U Δ Γ vs → WfVals U Δ' Γ vs
  | .nil => .nil
  | .cons Γ₁ Γ₂ v vs hv hvs => .cons Γ₁ Γ₂ v vs (WfVal.anyΔ hv) (WfVals.anyΔ hvs)
end

/-- **Lemma 45** (value replacement lemma): if `Δ | Γ ⊢ E[□]` and `∅ | Γ' ⊢ v` then
    `Δ | Γ, Γ' ⊢ E[v]`. -/
theorem ECtx.Wf.plug_val {cfg : Cfg} {U Δ : Finset Var} {Γ : Ctx} {E : ECtx}
    (hE : ECtx.Wf cfg U Δ Γ E) {Γ' : Ctx} {v : Val} (hv : WfVal U ∅ Γ' v) :
    FIP.Wf cfg U Δ (Γ + Γ') (E.plug (.val v)) :=
  hE.plug_gen fun _ _ => by
    simpa using FIP.Wf.tuple (WfVals.cons _ _ _ _ (WfVal.anyΔ hv) .nil)

end FIP
