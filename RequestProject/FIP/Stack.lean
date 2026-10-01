module

public import RequestProject.FIP.StoreSound

@[expose] public section

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
initial call already has a context of depth `1`); it is kept below in a comment, and a
counterexample is proved in `RequestProject/FIP/StackCex.lean`.  The corrected Theorem 4,
with the bound `(|Σ| + 1)² · max(1, |e_max|)`, is `stack_bound` in
`RequestProject/FIP/StackBound.lean`.
-/

namespace FIP

/-! ## Depths (Appendix C.1) -/

mutual
/-- The depth `|v|` of a value. -/
def Val.depth : Val → Nat
  | .ctor _ vs => 1 + Val.depthList vs
  | _ => 0
/-- The maximal depth of a list of values. -/
def Val.depthList : List Val → Nat
  | [] => 0
  | v :: vs => max (Val.depth v) (Val.depthList vs)
end

mutual
/-- The depth `|e|` of an expression. -/
def Expr.depth : Expr → Nat
  | .ret [v] => Val.depth v
  | .ret vs => 1 + Val.depthList vs
  | .app e1 e2 => 1 + max (Expr.depth e1) (Expr.depth e2)
  | .call _ e1 e2 => 1 + max (Expr.depth e1) (Expr.depth e2)
  | .letIn _ e1 e2 => 1 + max (Expr.depth e1) (Expr.depth e2)
  | .bmatch e bs => 1 + max (Expr.depth e) (Expr.depthB bs)
  | .dmatch e bs => 1 + max (Expr.depth e) (Expr.depthB bs)
  | .drop _ e => 1 + Expr.depth e
  | .free _ e => 1 + Expr.depth e
  | .prim _ vs => 1 + Val.depthList vs
/-- The maximal depth of the bodies of branches. -/
def Expr.depthB : List Branch → Nat
  | [] => 0
  | .mk _ _ e :: bs => max (Expr.depth e) (Expr.depthB bs)
end

/-- The depth `|E|` of an evaluation context. -/
def ECtx.depth : ECtx → Nat
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
theorem ECtx.depth_plug (E : ECtx) (e : Expr) : E.depth + e.depth ≤ (E.plug e).depth := by
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
theorem ECtx.depth_plug_mono (E : ECtx) {e₁ e₂ : Expr} (h : e₂.depth ≤ e₁.depth) :
    (E.plug e₂).depth ≤ (E.plug e₁).depth := by
  induction E with
  | hole => simpa [ECtx.plug] using h
  | appL E e2 ih => simp only [ECtx.plug, Expr.depth]; omega
  | appR vs E ih => simp only [ECtx.plug, Expr.depth]; omega
  | callB f E e2 ih => simp only [ECtx.plug, Expr.depth]; omega
  | callO f vs E ih => simp only [ECtx.plug, Expr.depth]; omega
  | letIn xs E e2 ih => simp only [ECtx.plug, Expr.depth]; omega
  | bmatch E bs ih => simp only [ECtx.plug, Expr.depth]; omega
  | dmatch E bs ih => simp only [ECtx.plug, Expr.depth]; omega

/-- A substitution of atomic values (variables, literals, functions) for variables. -/
def Subst.Atomic (σ : Subst) : Prop := ∀ p ∈ σ, p.2.depth = 0

theorem Subst.Atomic.remove {σ : Subst} (h : σ.Atomic) (xs : List Binder) :
    (σ.remove xs).Atomic := fun p hp => h p (List.mem_of_mem_filter hp)

theorem Subst.Atomic.lookup {σ : Subst} (h : σ.Atomic) {s : String} {v : Val}
    (hv : σ.lookup s = some v) : v.depth = 0 := by
  induction σ with
  | nil => simp at hv
  | cons p σ ih =>
    obtain ⟨a, b⟩ := p
    simp only [List.lookup_cons] at hv
    split at hv
    · cases hv; exact h _ (List.mem_cons_self ..)
    · exact ih (fun q hq => h q (List.mem_cons_of_mem _ hq)) hv

mutual
theorem Val.depth_subst {σ : Subst} (hσ : σ.Atomic) : ∀ v : Val, (v.subst σ).depth = v.depth
  | .var (.name s) => by
    simp only [Val.subst]
    cases h : σ.lookup s with
    | none => rfl
    | some v => simp [hσ.lookup h, Val.depth]
  | .var (.loc _) => rfl
  | .fn _ => rfl
  | .lit _ => rfl
  | .ctor c vs => by
    simp only [Val.subst, Val.depth]
    rw [Val.depthList_subst hσ vs]
theorem Val.depthList_subst {σ : Subst} (hσ : σ.Atomic) :
    ∀ vs : List Val, Val.depthList (Val.substList σ vs) = Val.depthList vs
  | [] => rfl
  | v :: vs => by
    simp only [Val.substList, Val.depthList]
    rw [Val.depth_subst hσ v, Val.depthList_subst hσ vs]
end

mutual
/-- **Lemma 26** (substitution of variables leaves the depth unchanged). -/
theorem Expr.depth_subst {σ : Subst} (hσ : σ.Atomic) : ∀ e : Expr, (e.subst σ).depth = e.depth
  | .ret [] => rfl
  | .ret [v] => by
    have := Val.depth_subst hσ v
    simp only [Expr.subst, Val.substList_eq_map, List.map_cons, List.map_nil, Expr.depth]
    exact this
  | .ret (v :: w :: vs) => by
    have := Val.depthList_subst hσ (v :: w :: vs)
    simp only [Expr.subst, Val.substList_eq_map, List.map_cons, Expr.depth] at this ⊢
    rw [this]
  | .app e1 e2 => by
    simp only [Expr.subst, Expr.depth, Expr.depth_subst hσ e1, Expr.depth_subst hσ e2]
  | .call f e1 e2 => by
    simp only [Expr.subst, Expr.depth, Expr.depth_subst hσ e1, Expr.depth_subst hσ e2]
  | .letIn xs e1 e2 => by
    simp only [Expr.subst, Expr.depth, Expr.depth_subst hσ e1,
      Expr.depth_subst (hσ.remove xs) e2]
  | .bmatch e bs => by
    simp only [Expr.subst, Expr.depth, Expr.depth_subst hσ e, Expr.depthB_subst hσ bs]
  | .dmatch e bs => by
    simp only [Expr.subst, Expr.depth, Expr.depth_subst hσ e, Expr.depthB_subst hσ bs]
  | .drop x e => by simp only [Expr.subst, Expr.depth, Expr.depth_subst hσ e]
  | .free k e => by simp only [Expr.subst, Expr.depth, Expr.depth_subst hσ e]
  | .prim op vs => by
    simp only [Expr.subst, Expr.depth]
    rw [Val.depthList_subst hσ vs]
theorem Expr.depthB_subst {σ : Subst} (hσ : σ.Atomic) :
    ∀ bs : List Branch, Expr.depthB (Expr.substBranches σ bs) = Expr.depthB bs
  | [] => rfl
  | .mk c xs e :: bs => by
    simp only [Expr.substBranches, Expr.depthB, Expr.depth_subst (hσ.remove xs) e,
      Expr.depthB_subst hσ bs]
end

/-! ## Tail-recursive groups (FIPS) -/

mutual
/-- The top-level functions a value mentions. -/
def Val.funs : Val → List FName
  | .fn f => [f]
  | .ctor _ vs => Val.funsList vs
  | _ => []
/-- The top-level functions a list of values mentions. -/
def Val.funsList : List Val → List FName
  | [] => []
  | v :: vs => Val.funs v ++ Val.funsList vs
end

mutual
/-- The top-level functions an expression calls or passes (the `fv` of Appendix C, which
    also collects directly called functions). -/
def Expr.funs : Expr → List FName
  | .ret vs => Val.funsList vs
  | .app e1 e2 => Expr.funs e1 ++ Expr.funs e2
  | .call f e1 e2 => f :: (Expr.funs e1 ++ Expr.funs e2)
  | .letIn _ e1 e2 => Expr.funs e1 ++ Expr.funs e2
  | .bmatch e bs => Expr.funs e ++ Expr.funsB bs
  | .dmatch e bs => Expr.funs e ++ Expr.funsB bs
  | .drop _ e => Expr.funs e
  | .free _ e => Expr.funs e
  | .prim _ _ => []
/-- The top-level functions branches call or pass. -/
def Expr.funsB : List Branch → List FName
  | [] => []
  | .mk _ _ e :: bs => Expr.funs e ++ Expr.funsB bs
end

/-- `e` does not mention the functions `fs`. -/
def Expr.Avoids (fs : List FName) (e : Expr) : Prop := ∀ f ∈ e.funs, f ∉ fs

/-- Tail contexts `T[f̄]`: every call to a function of the group `fs` is a tail call, and
    the arguments of such a call do not mention the group. -/
inductive Expr.TailIn (fs : List FName) : Expr → Prop where
  | base (e : Expr) : e.Avoids fs → Expr.TailIn fs e
  | call (f : FName) (e1 e2 : Expr) :
      f ∈ fs → e1.Avoids fs → e2.Avoids fs → Expr.TailIn fs (.call f e1 e2)
  | letIn (xs : List Binder) (e0 e : Expr) :
      e0.Avoids fs → Expr.TailIn fs e → Expr.TailIn fs (.letIn xs e0 e)
  | bmatch (e0 : Expr) (bs : List Branch) :
      e0.Avoids fs → (∀ b ∈ bs, Expr.TailIn fs b.body) → Expr.TailIn fs (.bmatch e0 bs)
  | dmatch (e0 : Expr) (bs : List Branch) :
      e0.Avoids fs → (∀ b ∈ bs, Expr.TailIn fs b.body) → Expr.TailIn fs (.dmatch e0 bs)
  | drop (x : Val) (e : Expr) : Expr.TailIn fs e → Expr.TailIn fs (.drop x e)
  | free (k : Nat) (e : Expr) : Expr.TailIn fs e → Expr.TailIn fs (.free k e)

/-- A signature is *stack safe* (FIPS) for a list of mutually recursive groups, given in
    order of definition, if the groups partition the signature, every function only calls
    functions of earlier groups or of its own group (in tail position), and only passes
    functions of strictly earlier groups as arguments. -/
structure Sig.StackSafe (sig : Sig) (groups : List (List FName)) : Prop where
  partition : (groups.flatten).Perm (sig.map (·.name))
  ordered : ∀ i (hi : i < groups.length), ∀ f ∈ groups[i], ∀ fd, sig.lookup f = some fd →
    Expr.TailIn groups[i] fd.body ∧
    (∀ g ∈ fd.body.funs, ∃ j ≤ i, ∃ hj : j < groups.length, g ∈ groups[j])

/-! The formal statement of Theorem 4 below is kept commented out: it is **false**.  Already
the initial expression `f(ȳ; x̄)` decomposes as `E[x̄]` with `E = f(ȳ; □)` of depth `1`, which
exceeds `|e_max| · |Σ|² = 0` when every function body has depth `0` (e.g. the identity
`f(; x) = x`).  See `not_stackBoundClaim` in `RequestProject/FIP/StackCex.lean`, and the
corrected statement `stack_bound` in `RequestProject/FIP/StackBound.lean`. -/

/-
/-- **Theorem 4** (a FIP program uses constant stack space).  Let `Σ` be fully in-place
    and stack safe, and let `S` be a store that contains no functions.  At any
    intermediate step `S | f(ȳ; x̄) ⟼*ₛ S' | E[e']` we have `|E| ≤ |e_max| · |Σ|²`. -/
theorem stack_bound {sig : Sig} (hsig : sig.PaperFragment) {groups : List (List FName)}
    (hss : sig.StackSafe groups) {fbip : Bool} {f : FName} {fd : FunDef}
    (hf : sig.lookup f = some fd) (hfip : fd.annot ≠ .plain) {ys xs : List Var}
    {S₁ S₂ : Store} (hd : S₁.Disjoint S₂) (hy : ∀ y ∈ ys, y ∈ S₁.dom) (hS₁ : S₁.Sound)
    (hx : S₂.roots = (xs : Multiset Var).map Res.var) (hS₂ : S₂.Linear)
    (hnofn : ∀ x c as, Cell.bind x c as ∈ S₁ + S₂ → ∀ a ∈ as, ∀ g, a ≠ .fn g)
    {S' : Store} {e : Expr}
    (h : SSteps sig fbip (S₁ + S₂) (.call f (.ret (ys.map .var)) (.ret (xs.map .var))) S' e)
    (E : ECtx) (e' : Expr) (he : e = E.plug e') :
    E.depth ≤ sig.maxDepth * sig.length ^ 2 := by
  sorry
-/

end FIP
