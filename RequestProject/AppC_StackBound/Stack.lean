module

public import RequestProject.AppB_StoreSoundness.StoreSound
public import RequestProject.Sec2_Calculus.SubstLemmas

@[expose] public section

/- ══════════════════ PAPER sec. 2.6, App. C START: Stack Safe FIP: Theorem 4; Stack Bound (PDF p. 14; App. C on pp. 54-67) ══════════════════
   Depths `|e|`, `|E|`, `e_max`, tail-recursive groups and stack safety `Sig.StackSafe`. -/

/-!
# Stack-safe FIP (Section 2.6, Appendix C)

To bound the stack, the paper requires every function to belong to a *mutually recursive
group* `f̄`, only functions of earlier groups (or of the group itself) to be called, and
recursive calls within a group to be in *tail position*:

```
T[f̄] ::= e₀ | fᵢ(e₀; e₀) | let x̄ = e₀ in T[f̄] | match e₀ {pᵢ ↦ Tᵢ[f̄]}
       | match! e₀ {pᵢ ↦ Tᵢ[f̄]} | drop x; T[f̄] | free k; T[f̄]      (f̄ ∉ fv(e₀))
```

where `fv` also collects the functions called or passed.  The size of the evaluation
context is the proxy for the stack: **Theorem 4** states that it stays below
`|e_max| · |Σ|²`.

This file defines expression and context depths (Appendix C.1) and proves Lemmas 25–27.
The formal statement of Theorem 4 with the bound `|e_max| · |Σ|²` is false as stated (the
initial call already has a context of depth `1`); a counterexample is proved in
`RequestProject/AppC_StackBound/StackCex.lean`.  The corrected Theorem 4, with the bound
`(|Σ| + 1)² · max(1, |e_max|)`, is `stack_bound` in
`RequestProject/AppC_StackBound/StackBound.lean`.
-/

namespace FIP

/-! ## Depths (Appendix C.1) -/

mutual
/-- The depth `|v|` of a value. -/
def Val.depth {n : Nat} : Val n → Nat
  | .ctor _ vs => 1 + Val.depthList vs
  | _ => 0
/-- The maximal depth of a list of values. -/
def Val.depthList {n : Nat} : List (Val n) → Nat
  | [] => 0
  | v :: vs => max (Val.depth v) (Val.depthList vs)
end

mutual
/-- The depth `|e|` of an expression. -/
def Expr.depth {n : Nat} : Expr n → Nat
  | .ret [v] => Val.depth v
  | .ret vs => 1 + Val.depthList vs
  | .app e1 e2 => 1 + max (Expr.depth e1) (Expr.depth e2)
  | .call _ e1 e2 => 1 + max (Expr.depth e1) (Expr.depth e2)
  | .letIn _ e1 e2 => 1 + max (Expr.depth e1) (Expr.depth e2)
  | .bmatch e bs => 1 + max (Expr.depth e) (Branches.depth bs)
  | .dmatch e bs => 1 + max (Expr.depth e) (Branches.depth bs)
  | .drop _ e => 1 + Expr.depth e
  | .free _ e => 1 + Expr.depth e
  | .prim _ vs => 1 + Val.depthList vs
/-- The maximal depth of the bodies of branches. -/
def Branches.depth {n : Nat} : Branches n → Nat
  | .nil => 0
  | .cons _ _ e bs => max (Expr.depth e) (Branches.depth bs)
end

/-- The depth `|E|` of an evaluation context. -/
def ECtx.depth {n : Nat} : ECtx n → Nat
  | .hole => 0
  | .appL E _ => 1 + E.depth
  | .appR _ E => 1 + E.depth
  | .callB _ E _ => 1 + E.depth
  | .callO _ _ E => 1 + E.depth
  | .letIn _ E _ => 1 + E.depth
  | .bmatch E _ => 1 + E.depth
  | .dmatch E _ => 1 + E.depth

/-- `|e_max|`: the maximal depth of a function body of the signature. -/
def Sig.maxDepth (sig : Sig) : Nat := (sig.map (·.body.depth)).foldr max 0

/-- **Lemma 25** (relating the depths of expressions and evaluation contexts):
    `|E[e]| ≥ |E| + |e|`. -/
theorem ECtx.depth_plug {n : Nat} (E : ECtx n) (e : Expr n) :
    E.depth + e.depth ≤ (E.plug e).depth := by
  induction E with
  | hole => simp [ECtx.depth, ECtx.plug]
  | appL E e2 ih => simp only [ECtx.depth, ECtx.plug, Expr.depth]; omega
  | appR vs E ih => simp only [ECtx.depth, ECtx.plug, Expr.depth]; omega
  | callB f E e2 ih => simp only [ECtx.depth, ECtx.plug, Expr.depth]; omega
  | callO f vs E ih => simp only [ECtx.depth, ECtx.plug, Expr.depth]; omega
  | letIn xs E e2 ih => simp only [ECtx.depth, ECtx.plug, Expr.depth]; omega
  | bmatch E bs ih => simp only [ECtx.depth, ECtx.plug, Expr.depth]; omega
  | dmatch E bs ih => simp only [ECtx.depth, ECtx.plug, Expr.depth]; omega

/-- **Lemma 27** (substitution inside an evaluation context): if `|e₁| ≥ |e₂|` then
    `|E[e₁]| ≥ |E[e₂]|`. -/
theorem ECtx.depth_plug_mono {n : Nat} (E : ECtx n) {e₁ e₂ : Expr n}
    (h : e₂.depth ≤ e₁.depth) : (E.plug e₂).depth ≤ (E.plug e₁).depth := by
  induction E with
  | hole => simpa [ECtx.plug] using h
  | appL E e2 ih => simp only [ECtx.plug, Expr.depth]; omega
  | appR vs E ih => simp only [ECtx.plug, Expr.depth]; omega
  | callB f E e2 ih => simp only [ECtx.plug, Expr.depth]; omega
  | callO f vs E ih => simp only [ECtx.plug, Expr.depth]; omega
  | letIn xs E e2 ih => simp only [ECtx.plug, Expr.depth]; omega
  | bmatch E bs ih => simp only [ECtx.plug, Expr.depth]; omega
  | dmatch E bs ih => simp only [ECtx.plug, Expr.depth]; omega

/-- A substitution of depth-zero values (variables, literals, functions) for variables. -/
def Subst.DepthZero {n m : Nat} (σ : Fin n → Val m) : Prop := ∀ i, (σ i).depth = 0

mutual
theorem Val.depth_subst {n m : Nat} {σ : Fin n → Val m} (hσ : Subst.DepthZero σ) :
    ∀ v : Val n, (v.subst σ).depth = v.depth
  | .var (.bvar i) => hσ i
  | .var (.loc _) => rfl
  | .fn _ => rfl
  | .lit _ => rfl
  | .ctor c vs => by
    simp only [Val.subst, Val.depth]
    rw [Val.depthList_subst hσ vs]
theorem Val.depthList_subst {n m : Nat} {σ : Fin n → Val m} (hσ : Subst.DepthZero σ) :
    ∀ vs : List (Val n), Val.depthList (Val.substList σ vs) = Val.depthList vs
  | [] => rfl
  | v :: vs => by
    simp only [Val.substList, Val.depthList]
    rw [Val.depth_subst hσ v, Val.depthList_subst hσ vs]
end

theorem Subst.DepthZero.up {n m : Nat} {σ : Fin n → Val m} (h : Subst.DepthZero σ) (k : Nat) :
    Subst.DepthZero (Subst.up k σ) := by
  intro i
  simp only [Subst.up]
  split
  · rfl
  · unfold Val.shift
    rw [Val.depth_subst (fun _ => rfl)]
    exact h _

mutual
/-- **Lemma 26** (substitution of variables leaves the depth unchanged). -/
theorem Expr.depth_subst : ∀ {n m : Nat} {σ : Fin n → Val m}, Subst.DepthZero σ →
    ∀ e : Expr n, (e.subst σ).depth = e.depth
  | _, _, _, _, .ret [] => rfl
  | _, _, σ, hσ, .ret [v] => by
    have := Val.depth_subst hσ v
    simp only [Expr.subst, Val.substList_eq_map, List.map_cons, List.map_nil, Expr.depth]
    exact this
  | _, _, σ, hσ, .ret (v :: w :: vs) => by
    have := Val.depthList_subst hσ (v :: w :: vs)
    simp only [Expr.subst, Val.substList_eq_map, List.map_cons, Expr.depth] at this ⊢
    rw [this]
  | _, _, σ, hσ, .app e1 e2 => by
    simp only [Expr.subst, Expr.depth, Expr.depth_subst hσ e1, Expr.depth_subst hσ e2]
  | _, _, σ, hσ, .call f e1 e2 => by
    simp only [Expr.subst, Expr.depth, Expr.depth_subst hσ e1, Expr.depth_subst hσ e2]
  | _, _, σ, hσ, .letIn xs e1 e2 => by
    simp only [Expr.subst, Expr.depth, Expr.depth_subst hσ e1,
      Expr.depth_subst (hσ.up xs.length) e2]
  | _, _, σ, hσ, .bmatch e bs => by
    simp only [Expr.subst, Expr.depth, Expr.depth_subst hσ e, Branches.depth_subst hσ bs]
  | _, _, σ, hσ, .dmatch e bs => by
    simp only [Expr.subst, Expr.depth, Expr.depth_subst hσ e, Branches.depth_subst hσ bs]
  | _, _, σ, hσ, .drop x e => by simp only [Expr.subst, Expr.depth, Expr.depth_subst hσ e]
  | _, _, σ, hσ, .free k e => by simp only [Expr.subst, Expr.depth, Expr.depth_subst hσ e]
  | _, _, σ, hσ, .prim op vs => by
    simp only [Expr.subst, Expr.depth]
    rw [Val.depthList_subst hσ vs]
theorem Branches.depth_subst : ∀ {n m : Nat} {σ : Fin n → Val m}, Subst.DepthZero σ →
    ∀ bs : Branches n, (Branches.subst σ bs).depth = bs.depth
  | _, _, _, _, .nil => rfl
  | _, _, σ, hσ, .cons c xs e bs => by
    simp only [Branches.subst, Branches.depth, Expr.depth_subst (hσ.up xs.length) e,
      Branches.depth_subst hσ bs]
end

/-! ## Tail-recursive groups (FIPS) -/

mutual
/-- The top-level functions a value mentions. -/
def Val.funs {n : Nat} : Val n → List FName
  | .fn f => [f]
  | .ctor _ vs => Val.funsList vs
  | _ => []
/-- The top-level functions a list of values mentions. -/
def Val.funsList {n : Nat} : List (Val n) → List FName
  | [] => []
  | v :: vs => Val.funs v ++ Val.funsList vs
end

mutual
/-- The top-level functions an expression calls or passes (the `fv` of Appendix C, which
    also collects directly called functions). -/
def Expr.funs {n : Nat} : Expr n → List FName
  | .ret vs => Val.funsList vs
  | .app e1 e2 => Expr.funs e1 ++ Expr.funs e2
  | .call f e1 e2 => f :: (Expr.funs e1 ++ Expr.funs e2)
  | .letIn _ e1 e2 => Expr.funs e1 ++ Expr.funs e2
  | .bmatch e bs => Expr.funs e ++ Branches.funs bs
  | .dmatch e bs => Expr.funs e ++ Branches.funs bs
  | .drop _ e => Expr.funs e
  | .free _ e => Expr.funs e
  | .prim _ _ => []
/-- The top-level functions branches call or pass. -/
def Branches.funs {n : Nat} : Branches n → List FName
  | .nil => []
  | .cons _ _ e bs => Expr.funs e ++ Branches.funs bs
end

/-- `e` does not mention the functions `fs`. -/
def Expr.Avoids {n : Nat} (fs : List FName) (e : Expr n) : Prop := ∀ f ∈ e.funs, f ∉ fs

/-- Tail contexts `T[f̄]`: every call to a function of the group `fs` is a tail call, and
    the arguments of such a call do not mention the group. -/
inductive Expr.TailIn (fs : List FName) : {n : Nat} → Expr n → Prop where
  | base {n : Nat} (e : Expr n) : e.Avoids fs → Expr.TailIn fs e
  | call {n : Nat} (f : FName) (e1 e2 : Expr n) :
      f ∈ fs → e1.Avoids fs → e2.Avoids fs → Expr.TailIn fs (.call f e1 e2)
  | letIn {n : Nat} (xs : List Bool) (e0 : Expr n) (e : Expr (n + xs.length)) :
      e0.Avoids fs → Expr.TailIn fs e → Expr.TailIn fs (.letIn xs e0 e)
  | bmatch {n : Nat} (e0 : Expr n) (bs : Branches n) :
      e0.Avoids fs → (∀ b ∈ bs.toList, Expr.TailIn fs b.body) → Expr.TailIn fs (.bmatch e0 bs)
  | dmatch {n : Nat} (e0 : Expr n) (bs : Branches n) :
      e0.Avoids fs → (∀ b ∈ bs.toList, Expr.TailIn fs b.body) → Expr.TailIn fs (.dmatch e0 bs)
  | drop {n : Nat} (x : Val n) (e : Expr n) : Expr.TailIn fs e → Expr.TailIn fs (.drop x e)
  | free {n : Nat} (k : Nat) (e : Expr n) : Expr.TailIn fs e → Expr.TailIn fs (.free k e)

/-- A signature is *stack safe* (FIPS) for a list of mutually recursive groups, given in
    order of definition, if the groups partition the signature, every function only calls
    functions of earlier groups or of its own group (in tail position), and only passes
    functions of strictly earlier groups as arguments. -/
structure Sig.StackSafe (sig : Sig) (groups : List (List FName)) : Prop where
  partition : (groups.flatten).Perm (sig.map (·.name))
  ordered : ∀ i (hi : i < groups.length), ∀ f ∈ groups[i], ∀ fd, sig.lookup f = some fd →
    Expr.TailIn groups[i] fd.body ∧
    (∀ g ∈ fd.body.funs, ∃ j ≤ i, ∃ hj : j < groups.length, g ∈ groups[j])

end FIP

/- ══════════════════ PAPER sec. 2.6, App. C END: Stack Safe FIP: Theorem 4; Stack Bound ══════════════════ -/
