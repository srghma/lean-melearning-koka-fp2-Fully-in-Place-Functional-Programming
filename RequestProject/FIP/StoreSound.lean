module

public import RequestProject.FIP.Store

@[expose] public section

/-!
# Soundness of the store semantics (Theorem 1, Corollary 1; Appendix B)

`[S]e` substitutes, for every location bound in the store `S`, the value it denotes
(reading the store recursively).  Theorem 1 of the paper states that for a well-formed
FIP expression evaluated in a store whose owned part is linear and has exactly the owned
resources as roots, the store semantics computes the same result as the functional
semantics, without leaving garbage.

The theorem concerns the calculus of the paper, so it is stated for the *scalar-free*
fragment (no literals, primitive operations or scalar binders) and without allocation
budgets `fip(n)` (the store has no room for allocation credits).
-/

namespace FIP

/-! ## Substituting locations -/

mutual
/-- Substitute values for locations in a value. -/
def Val.substLoc (σ : Nat → Option Val) : Val → Val
  | .var (.loc n) => (σ n).getD (.var (.loc n))
  | .var (.name s) => .var (.name s)
  | .fn f => .fn f
  | .ctor c vs => .ctor c (Val.substLocList σ vs)
  | .lit n => .lit n
/-- Substitute values for locations in a list of values. -/
def Val.substLocList (σ : Nat → Option Val) : List Val → List Val
  | [] => []
  | v :: vs => Val.substLoc σ v :: Val.substLocList σ vs
end

mutual
/-- Substitute values for locations in an expression (binders are names, so there is no
    capture). -/
def Expr.substLoc (σ : Nat → Option Val) : Expr → Expr
  | .ret vs => .ret (Val.substLocList σ vs)
  | .app e1 e2 => .app (Expr.substLoc σ e1) (Expr.substLoc σ e2)
  | .call f e1 e2 => .call f (Expr.substLoc σ e1) (Expr.substLoc σ e2)
  | .letIn xs e1 e2 => .letIn xs (Expr.substLoc σ e1) (Expr.substLoc σ e2)
  | .bmatch e bs => .bmatch (Expr.substLoc σ e) (Expr.substLocB σ bs)
  | .dmatch e bs => .dmatch (Expr.substLoc σ e) (Expr.substLocB σ bs)
  | .drop x e => .drop (Val.substLoc σ x) (Expr.substLoc σ e)
  | .free k e => .free k (Expr.substLoc σ e)
  | .prim op vs => .prim op (Val.substLocList σ vs)
/-- Substitute values for locations in branches. -/
def Expr.substLocB (σ : Nat → Option Val) : List Branch → List Branch
  | [] => []
  | .mk c xs e :: bs => .mk c xs (Expr.substLoc σ e) :: Expr.substLocB σ bs
end

/-- A value or expression *without locations*. -/
def NoLoc (l : List Var) : Prop := ∀ n, Var.loc n ∉ l

mutual
theorem Val.substLoc_of_noLoc (σ : Nat → Option Val) :
    ∀ v : Val, NoLoc (Val.fv v) → Val.substLoc σ v = v
  | .var (.loc n), h => absurd (by simp [Val.fv]) (h n)
  | .var (.name _), _ => rfl
  | .fn _, _ => rfl
  | .lit _, _ => rfl
  | .ctor c vs, h => by
    simp only [Val.substLoc, Val.fv] at h ⊢
    rw [Val.substLocList_of_noLoc σ vs h]
theorem Val.substLocList_of_noLoc (σ : Nat → Option Val) :
    ∀ vs : List Val, NoLoc (Val.fvList vs) → Val.substLocList σ vs = vs
  | [], _ => rfl
  | v :: vs, h => by
    simp only [Val.substLocList]
    rw [Val.substLoc_of_noLoc σ v (fun n hn => h n (by simp [Val.fvList, hn])),
      Val.substLocList_of_noLoc σ vs (fun n hn => h n (by simp [Val.fvList, hn]))]
end

/-! ## Reading the store: `[S]x` -/

/-- The binding of a location in a store, if any. -/
noncomputable def Store.lookup (S : Store) (x : Var) : Option (CName × List Val) :=
  open Classical in
  if h : ∃ p : CName × List Val, Cell.bind x p.1 p.2 ∈ S then some h.choose else none

/-- Read a value from the store, following at most `n` bindings. -/
noncomputable def Store.readN (S : Store) : Nat → Val → Val
  | 0, v => v
  | n + 1, .var x =>
    match S.lookup x with
    | some (c, as) => .ctor c (as.map (Store.readN S n))
    | none => .var x
  | n + 1, .ctor c vs => .ctor c (vs.map (Store.readN S (n + 1) ·))
  | _ + 1, v => v
termination_by n v => (n, sizeOf v)
decreasing_by
  all_goals first
    | exact Prod.Lex.left _ _ (Nat.lt_succ_self _)
    | (apply Prod.Lex.right; have := List.sizeOf_lt_of_mem ‹_›; simp; omega)

/-- `[S]v`: the value denoted by `v` in the store `S` (a sound linear store is acyclic, so
    following `|S| + 1` bindings suffices). -/
noncomputable def Store.read (S : Store) (v : Val) : Val :=
  S.readN (Multiset.card S + 1) v

/-- `[S]e`: substitute the value of every location bound in `S`. -/
noncomputable def Store.substE (S : Store) (e : Expr) : Expr :=
  open Classical in
  e.substLoc fun n => if Var.loc n ∈ S.dom then some (S.read (.var (.loc n))) else none

theorem loc_not_mem_binderVars (xs : List Binder) (n : Nat) : Var.loc n ∉ Binder.vars xs := by
  simp [Binder.vars]

mutual
theorem Expr.substLoc_of_noLoc (σ : Nat → Option Val) :
    ∀ e : Expr, NoLoc e.fv → e.substLoc σ = e
  | .ret vs, h => by
    simp only [Expr.substLoc, Expr.fv] at h ⊢; rw [Val.substLocList_of_noLoc σ vs h]
  | .app e1 e2, h => by
    simp only [Expr.substLoc]
    rw [Expr.substLoc_of_noLoc σ e1 (fun n hn => h n (by simp [Expr.fv, hn])),
      Expr.substLoc_of_noLoc σ e2 (fun n hn => h n (by simp [Expr.fv, hn]))]
  | .call f e1 e2, h => by
    simp only [Expr.substLoc]
    rw [Expr.substLoc_of_noLoc σ e1 (fun n hn => h n (by simp [Expr.fv, hn])),
      Expr.substLoc_of_noLoc σ e2 (fun n hn => h n (by simp [Expr.fv, hn]))]
  | .letIn xs e1 e2, h => by
    simp only [Expr.substLoc]
    rw [Expr.substLoc_of_noLoc σ e1 (fun n hn => h n (by simp [Expr.fv, hn])),
      Expr.substLoc_of_noLoc σ e2 (fun n hn => h n (by
        simp [Expr.fv, hn, loc_not_mem_binderVars]))]
  | .bmatch e bs, h => by
    simp only [Expr.substLoc]
    rw [Expr.substLoc_of_noLoc σ e (fun n hn => h n (by simp [Expr.fv, hn])),
      Expr.substLocB_of_noLoc σ bs (fun n hn => h n (by simp [Expr.fv, hn]))]
  | .dmatch e bs, h => by
    simp only [Expr.substLoc]
    rw [Expr.substLoc_of_noLoc σ e (fun n hn => h n (by simp [Expr.fv, hn])),
      Expr.substLocB_of_noLoc σ bs (fun n hn => h n (by simp [Expr.fv, hn]))]
  | .drop x e, h => by
    simp only [Expr.substLoc]
    rw [Val.substLoc_of_noLoc σ x (fun n hn => h n (by simp [Expr.fv, hn])),
      Expr.substLoc_of_noLoc σ e (fun n hn => h n (by simp [Expr.fv, hn]))]
  | .free k e, h => by
    simp only [Expr.substLoc]
    rw [Expr.substLoc_of_noLoc σ e (fun n hn => h n (by simp [Expr.fv, hn]))]
  | .prim op vs, h => by
    simp only [Expr.substLoc, Expr.fv] at h ⊢; rw [Val.substLocList_of_noLoc σ vs h]
theorem Expr.substLocB_of_noLoc (σ : Nat → Option Val) :
    ∀ bs : List Branch, NoLoc (Expr.fvBranches bs) → Expr.substLocB σ bs = bs
  | [], _ => rfl
  | .mk c xs e :: bs, h => by
    simp only [Expr.substLocB]
    rw [Expr.substLoc_of_noLoc σ e (fun n hn => h n (by
        simp [Expr.fvBranches, hn, loc_not_mem_binderVars])),
      Expr.substLocB_of_noLoc σ bs (fun n hn => h n (by simp [Expr.fvBranches, hn]))]
end

/-! ## The scalar-free fragment (the calculus of the paper) -/

mutual
/-- A value without literals. -/
def Val.scalarFree : Val → Bool
  | .lit _ => false
  | .ctor _ vs => Val.scalarFreeList vs
  | _ => true
/-- Values without literals. -/
def Val.scalarFreeList : List Val → Bool
  | [] => true
  | v :: vs => Val.scalarFree v && Val.scalarFreeList vs
end

mutual
/-- An expression of the paper's calculus: no literals, primitive operations or scalar
    binders. -/
def Expr.scalarFree : Expr → Bool
  | .ret vs => Val.scalarFreeList vs
  | .app e1 e2 => Expr.scalarFree e1 && Expr.scalarFree e2
  | .call _ e1 e2 => Expr.scalarFree e1 && Expr.scalarFree e2
  | .letIn xs e1 e2 => xs.all (!·.scalar) && Expr.scalarFree e1 && Expr.scalarFree e2
  | .bmatch e bs => Expr.scalarFree e && Expr.scalarFreeB bs
  | .dmatch e bs => Expr.scalarFree e && Expr.scalarFreeB bs
  | .drop x e => Val.scalarFree x && Expr.scalarFree e
  | .free _ e => Expr.scalarFree e
  | .prim _ _ => false
/-- Branches of the paper's calculus. -/
def Expr.scalarFreeB : List Branch → Bool
  | [] => true
  | .mk _ xs e :: bs => xs.all (!·.scalar) && Expr.scalarFree e && Expr.scalarFreeB bs
end

/-- The setting of Theorem 1: a signature of the paper's calculus whose annotated
    functions are fully in-place (or FBIP), without allocation budgets.  As in the paper,
    where `Σ` maps function names to definitions, the functions of the signature have
    distinct names (otherwise a call to an annotated function could be resolved to an
    unannotated definition of the same name). -/
structure Sig.PaperFragment (sig : Sig) : Prop where
  names : (sig.map (·.name)).Nodup
  wf : sig.Wf
  scalarFree : ∀ fd ∈ sig, (fd.borrowed ++ fd.owned).all (!·.scalar) ∧ fd.body.scalarFree
  noBudget : ∀ fd ∈ sig, fd.annot.budget = 0

/-- The functions an expression may call (`dom(Σ)` in the rules) are annotated
    functions of the signature, callable in the given mode of the store semantics. -/
def Cfg.Compatible (cfg : Cfg) (sig : Sig) (fbip : Bool) : Prop :=
  (∀ f ∈ cfg.funs, ∃ fd, sig.lookup f = some fd ∧ fd.annot ≠ .plain) ∧
  (∀ f, cfg.budget f = 0) ∧ (cfg.fbip = true → fbip = true) ∧
  (∀ fd ∈ sig, fd.annot.isFbip = true → fbip = true)

/-! The first formal statement of Theorem 1 and Corollary 1 is kept below, commented
out.  It is **false**: it allows stores to bind program names (and constructor fields that
are not locations), while `[S]e` only substitutes locations; see
`not_storeSoundOriginalClaim` in `RequestProject/FIP/StoreSoundCex.lean` for a
counterexample.  The corrected statements, which require the stores to have the shape of
the paper's stores (`x ↦ Cᵏ x₁ … xₖ` with `x, xᵢ` locations) and express `[S]` as a
substitution `σ` of closed values for locations, are `store_sound` and
`store_sound_closed` in `RequestProject/FIP/StoreSoundProof.lean`. -/

/-
/-- **Theorem 1** (the store semantics is sound for well-formed FIP programs).
    If `Δ | Γ ⊢ e`, and `S₁, S₂` are disjoint stores with `Δ ⊆ dom(S₁)`, `S₁` sound,
    `Γ = roots(S₂)` and `S₂` linear, then `[S₁, S₂]e ⟼* v̄` implies
    `S₁, S₂ | e ⟼*ₛ S₁, S₃ | x̄` where `[S₃]x̄ = v̄`, `x̄ = roots(S₃)` and `S₃` is linear. -/
theorem store_sound {sig : Sig} (hsig : sig.PaperFragment) {fbip : Bool} {cfg : Cfg}
    (hcfg : cfg.Compatible sig fbip) {Δ : Finset Var} {Γ : Ctx} {e : Expr}
    (hsf : e.scalarFree = true) (h : Wf cfg ∅ Δ Γ e)
    {S₁ S₂ : Store} (hd : S₁.Disjoint S₂) (hΔ : ∀ x ∈ Δ, x ∈ S₁.dom) (hS₁ : S₁.Sound)
    (hΓ : Γ = S₂.roots) (hS₂ : S₂.Linear)
    {vs : List Val} (hev : Steps sig ((S₁ + S₂).substE e) (.ret vs)) :
    ∃ (S₃ : Store) (xs : List Var),
      SSteps sig fbip (S₁ + S₂) e (S₁ + S₃) (.ret (xs.map .var)) ∧
      xs.map (fun x => S₃.read (.var x)) = vs ∧
      S₃.roots = (xs : Multiset Var).map Res.var ∧ S₃.Linear := by
  sorry

/-- **Corollary 1.** If `e ⟼* v̄` and `∅ | ⋄k ⊢ e` (with `k ≥ 1`), then `⋄k | e ⟼*ₛ S | x̄` with
    `[S]x̄ = v̄`: a FIP expression runs in a store containing just the reuse credit it
    needs. -/
theorem store_sound_closed {sig : Sig} (hsig : sig.PaperFragment) {fbip : Bool}
    {cfg : Cfg} (hcfg : cfg.Compatible sig fbip) {e : Expr} {k : Nat} (hk : 0 < k)
    (hsf : e.scalarFree = true) (h : Wf cfg ∅ ∅ {Res.credit k} e)
    {vs : List Val} (hev : Steps sig e (.ret vs)) :
    ∃ (S : Store) (xs : List Var),
      SSteps sig fbip {Cell.credit k} e S (.ret (xs.map .var)) ∧
      xs.map (fun x => S.read (.var x)) = vs := by
  have hfv : e.fv = [] := by
    rcases hx : e.fv with _ | ⟨x, _⟩
    · rfl
    · have := Wf.fv_subset h x (by simp [hx])
      simp [Avail] at this
  have hsub : ((0 : Store) + {Cell.credit k}).substE e = e :=
    Expr.substLoc_of_noLoc _ e (by simp [NoLoc, hfv])
  have hroots : ({Res.credit k} : Ctx) = Store.roots {Cell.credit k} := by
    simp [Store.roots, Cell.dom, Cell.credits, Nat.pos_iff_ne_zero.mp hk]
  have hlin : Store.Linear {Cell.credit k} := by
    refine ⟨⟨?_, ?_⟩, ?_⟩ <;> simp [Cell.dom, Cell.fv]
  obtain ⟨S₃, xs, hs, hr, -, -⟩ :=
    store_sound hsig hcfg hsf h (S₁ := 0) (S₂ := {Cell.credit k}) (by simp [Store.Disjoint])
      (by simp) (by simp [Store.Sound]) hroots hlin (hsub ▸ hev)
  exact ⟨S₃, xs, by simpa using hs, hr⟩

-/

end FIP
