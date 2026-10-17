module

public import RequestProject.Sec2_Calculus.SubstLemmas

@[expose] public section

/- ══════════════════ PAPER sec. 2.3, App. B.1 START: Store Semantics; Properties of Stores (PDF pp. 11-12, Fig. 5; App. B.1 on pp. 38-40) ══════════════════
   Stores `S`, soundness and linearity of stores (Definition 1), `roots`, joining stores
   (Lemma 3) and the store semantics `S | e |->s S' | e'`. -/

/-!
# The store semantics (Fig. 5, Fig. 6) and its basic properties (Appendix B.1–B.2)

A *store* `S ::= ∅ | S, x ↦ Cᵏ x₁ … xₖ | S, ⋄k` binds locations to constructors whose
arguments are atomic values, or holds reuse credits.  The store semantics
`S | e ⟶ₛ S' | e'` evaluates without allocating or deallocating memory: a constructor
`Cᵏ x₁ … xₖ` (with `k ≥ 1`) can only be built by consuming a reuse credit `⋄k`
(rule *reuse*), and a destructive match turns the matched cell into a reuse credit
(rule *dmatch*).  Atoms are allocated freely (rule *atom*): they have size `0`.

We prove

* **Theorem 2** (`SSteps.size_eq`): a FIP program reduces in place — the size of the
  store never changes;
* **Theorem 3** (`SSteps.size_le`): with the deallocation rules of Fig. 6 (FBIP), the
  size of the store can only decrease;
* **Lemma 3** (`Store.join_sound`, `Store.join_linear`, `Store.roots_add`): joining
  disjoint sound (linear) stores;
* **Lemma 4** (`SStep.weaken`): weakening of the store semantics;
* **Lemma 5** (`Wf.fv_subset`): the free variables of a well-formed FIP expression are
  in `Δ, Γ` (and the scalar variables `U`).

## Representation

Locations are the variables `Var.loc n`; program variables `Var.name s` are
substituted by locations (or, for scalars, literals) as evaluation proceeds.  An
*atomic* value is a variable, a literal or a top-level function.  A store is a finite
multiset of cells; that each location is bound at most once is part of soundness.
-/

namespace FIP

/-! ## Stores -/

/-- Atomic values: what the store semantics substitutes for variables. -/
def Val.Atomic {n : Nat} : Val n → Prop
  | .var _ => True
  | .lit _ => True
  | .fn _ => True
  | .ctor _ _ => False

/-- A cell of the store: a binding `x ↦ Cᵏ a₁ … aₖ`, or a reuse credit `⋄k`. -/
inductive Cell where
  | bind (x : Var 0) (c : CName) (args : List (Val 0))
  | credit (k : Nat)
  deriving DecidableEq, Repr

/-- A store. -/
abbrev Store := Multiset Cell

/-- The size of a cell: `k` for `x ↦ Cᵏ …` and for `⋄k`. -/
def Cell.size : Cell → Nat
  | .bind _ _ args => args.length
  | .credit k => k

/-- The location bound by a cell. -/
def Cell.dom : Cell → Multiset (Var 0)
  | .bind x _ _ => {x}
  | .credit _ => 0

/-- The free variables of the value bound by a cell. -/
def Cell.fv : Cell → Multiset (Var 0)
  | .bind _ _ args => (Val.fvList args : Multiset (Var 0))
  | .credit _ => 0

/-- The (non-empty) reuse credits of a cell, as resources.  A credit `⋄0` of size zero
    occupies no memory and is not a root (it may be discarded by rule `empty`). -/
def Cell.credits : Cell → Ctx 0
  | .bind _ _ _ => 0
  | .credit k => if k = 0 then 0 else {Res.credit k}

namespace Store

/-- **Definition 2.** The size `|S|` of a store. -/
def size (S : Store) : Nat := (S.map Cell.size).sum

/-- `dom(S)`: the locations bound in `S` (with multiplicity). -/
def dom (S : Store) : Multiset (Var 0) := S.bind Cell.dom

/-- `fv(rng(S))`: the free variables of the values bound in `S` (with multiplicity). -/
def rngFv (S : Store) : Multiset (Var 0) := S.bind Cell.fv

/-- **Definition 1.** A store is *sound* if each location is bound at most once and all
    free variables of its values are bound. -/
def Sound (S : Store) : Prop := S.dom.Nodup ∧ ∀ x ∈ S.rngFv, x ∈ S.dom

/-- **Definition 1.** A store is *linear* if it is sound and every variable occurs at
    most once in the free variables of its values. -/
def Linear (S : Store) : Prop := S.Sound ∧ S.rngFv.Nodup

/-- **Definition 1.** `roots(S)`: the reuse credits of `S` and the bound locations that do
    not occur in the values of `S`. -/
noncomputable def roots (S : Store) : Ctx 0 :=
  (S.dom.filter (· ∉ S.rngFv)).map Res.var + S.bind Cell.credits

@[simp] theorem size_zero : size 0 = 0 := by simp [size]
@[simp] theorem size_add (S T : Store) : size (S + T) = size S + size T := by simp [size]
@[simp] theorem size_singleton (c : Cell) : size {c} = c.size := by simp [size]

@[simp] theorem size_cons (c : Cell) (S : Store) : size (c ::ₘ S) = c.size + size S := by
  simp [size]

@[simp] theorem dom_zero : dom 0 = 0 := by simp [dom]
@[simp] theorem dom_cons (c : Cell) (S : Store) : dom (c ::ₘ S) = c.dom + dom S := by
  simp [dom]
@[simp] theorem rngFv_cons (c : Cell) (S : Store) : rngFv (c ::ₘ S) = c.fv + rngFv S := by
  simp [rngFv]
@[simp] theorem dom_add (S T : Store) : dom (S + T) = dom S + dom T := by simp [dom]
@[simp] theorem dom_singleton (c : Cell) : dom {c} = c.dom := by simp [dom]

@[simp] theorem rngFv_zero : rngFv 0 = 0 := by simp [rngFv]
@[simp] theorem rngFv_add (S T : Store) : rngFv (S + T) = rngFv S + rngFv T := by simp [rngFv]
@[simp] theorem rngFv_singleton (c : Cell) : rngFv {c} = c.fv := by simp [rngFv]

/-- Two stores are disjoint if they bind different locations. -/
def Disjoint (S T : Store) : Prop := ∀ x ∈ S.dom, x ∉ T.dom

end Store

/-! ## Lemma 3: joining stores -/

namespace Store

/-- **Lemma 3** (store joining, soundness). -/
theorem join_sound {S T : Store} (hS : S.Sound) (hT : T.Sound) (hd : S.Disjoint T) :
    (S + T).Sound := by
  refine ⟨?_, ?_⟩
  · simp only [dom_add]
    exact Multiset.nodup_add.mpr ⟨hS.1, hT.1, Multiset.disjoint_left.mpr fun {x} hx hx' => hd x hx hx'⟩
  · intro x hx
    simp only [rngFv_add, Multiset.mem_add, dom_add] at hx ⊢
    rcases hx with hx | hx
    · exact Or.inl (hS.2 x hx)
    · exact Or.inr (hT.2 x hx)

/-- **Lemma 3** (store joining, linearity). -/
theorem join_linear {S T : Store} (hS : S.Linear) (hT : T.Linear) (hd : S.Disjoint T) :
    (S + T).Linear := by
  refine ⟨join_sound hS.1 hT.1 hd, ?_⟩
  simp only [rngFv_add]
  refine Multiset.nodup_add.mpr ⟨hS.2, hT.2, Multiset.disjoint_left.mpr fun {x} hx hx' => ?_⟩
  exact hd x (hS.1.2 x hx) (hT.1.2 x hx')

/-- **Lemma 3** (store joining, roots): the roots of joined disjoint sound stores are the
    union of their roots. -/
theorem roots_add {S T : Store} (hS : S.Sound) (hT : T.Sound) (hd : S.Disjoint T) :
    (S + T).roots = S.roots + T.roots := by
  unfold roots
  simp only [dom_add, rngFv_add, Multiset.add_bind, Multiset.filter_add, Multiset.map_add]
  have h1 : (S.dom.filter fun x => x ∉ S.rngFv + T.rngFv) = S.dom.filter (· ∉ S.rngFv) := by
    refine Multiset.filter_congr fun x hx => ?_
    simp only [Multiset.mem_add, not_or, and_iff_left_iff_imp]
    intro _ hxT
    exact hd x hx (hT.2 x hxT)
  have h2 : (T.dom.filter fun x => x ∉ S.rngFv + T.rngFv) = T.dom.filter (· ∉ T.rngFv) := by
    refine Multiset.filter_congr fun x hx => ?_
    simp only [Multiset.mem_add, not_or, and_iff_right_iff_imp]
    intro _ hxS
    exact hd x (hS.2 x hxS) hx
  rw [h1, h2]
  abel

end Store

/-! ## The store semantics -/

/-- Value contexts `C a₁ … aᵢ □ vᵢ₊₂ … vₖ`: the arguments of a constructor are evaluated
    from left to right (Fig. 5). -/
inductive VCtx where
  | hole
  | ctor (c : CName) (done : List (Val 0)) (V : VCtx) (rest : List (Val 0))

/-- Plug a value into a value context. -/
def VCtx.plug : VCtx → Val 0 → Val 0
  | .hole, v => v
  | .ctor c done V rest, v => .ctor c (done ++ V.plug v :: rest)

/-- The already evaluated arguments of a value context are atomic. -/
def VCtx.Ok : VCtx → Prop
  | .hole => True
  | .ctor _ done V _ => (∀ a ∈ done, a.Atomic) ∧ V.Ok

/-- `drop a₁; …; drop aₖ; e` for the variables among `a₁ … aₖ`. -/
def drops : List (Val 0) → Expr 0 → Expr 0
  | [], e => e
  | .var x :: as, e => .drop (.var x) (drops as e)
  | _ :: as, e => drops as e

/-- Head reductions of the store semantics on (closed) expressions (Fig. 5 and Fig. 6).
    The deallocation rules `dcon` and `free` of Fig. 6 are only available when `fbip` is
    set. -/
inductive SHead (sig : Sig) (fbip : Bool) : Store → Expr 0 → Store → Expr 0 → Prop where
  /-- (*lets*) `S | let x̄ = ā in e ⟶ₛ S | e[x̄ := ā]` -/
  | letIn (S : Store) (xs : List Bool) (as : List (Val 0)) (e : Expr (0 + xs.length)) :
      (∀ a ∈ as, a.Atomic) → xs.length = as.length →
      SHead sig fbip S (.letIn xs (.ret as) e) S (e.inst as)
  /-- (*calls*) `S | f(ā₁; ā₂) ⟶ₛ S | e[ȳ := ā₁, x̄ := ā₂]` -/
  | call (S : Store) (f : FName) (fd : FunDef) (as1 as2 : List (Val 0)) :
      sig.lookup f = some fd → (∀ a ∈ as1, a.Atomic) → (∀ a ∈ as2, a.Atomic) →
      fd.borrowed.length = as1.length → fd.owned.length = as2.length →
      SHead sig fbip S (.call f (.ret as1) (.ret as2)) S (fd.instBody as1 as2)
  /-- (*anons*) `S | (f) ā ⟶ₛ S | e[x̄ := ā]` -/
  | app (S : Store) (f : FName) (fd : FunDef) (as : List (Val 0)) :
      sig.lookup f = some fd → fd.borrowed = [] → (∀ a ∈ as, a.Atomic) →
      fd.owned.length = as.length →
      SHead sig fbip S (.app (.val (.fn f)) (.ret as)) S (fd.instBody [] as)
  /-- (*bmatchs*) `S, y ↦ C z̄ | match y {p ↦ e} ⟶ₛ S, y ↦ C z̄ | eᵢ[x̄ := z̄]` -/
  | bmatch (S : Store) (y : Var 0) (c : CName) (zs : List (Val 0)) (bs : Branches 0)
      (b : Branch 0) :
      Cell.bind y c zs ∈ S → bs.find c zs.length = some b →
      SHead sig fbip S (.bmatch (.var y) bs) S (b.body.inst zs)
  /-- (*dmatchs*) `S, x ↦ Cᵏ z̄ | match! x {p ↦ e} ⟶ₛ S, ⋄k | eᵢ[x̄ := z̄]` -/
  | dmatch (S : Store) (x : Var 0) (c : CName) (zs : List (Val 0)) (bs : Branches 0)
      (b : Branch 0) :
      bs.find c zs.length = some b →
      SHead sig fbip ({Cell.bind x c zs} + S) (.dmatch (.var x) bs)
        ({Cell.credit zs.length} + S) (b.body.inst zs)
  /-- (*dcons*, Fig. 6) `S, x ↦ Cᵏ z̄ | drop x; e ⟶ₛ S | drop z̄; e`: the cell is
      deallocated and its fields are dropped in turn. -/
  | drop (S : Store) (x : Var 0) (c : CName) (zs : List (Val 0)) (e : Expr 0) :
      fbip = true →
      SHead sig fbip ({Cell.bind x c zs} + S) (.drop (.var x) e) S (drops zs e)
  /-- (*frees*, Fig. 6) `S, ⋄k | free k; e ⟶ₛ S | e` -/
  | free (S : Store) (k : Nat) (e : Expr 0) :
      fbip = true → SHead sig fbip ({Cell.credit k} + S) (.free k e) S e
  /-- primitive operations on scalars (extension) -/
  | prim (S : Store) (op : PrimOp) (a b : Int) :
      SHead sig fbip S (.prim op [.lit a, .lit b]) S (.val (boolVal (op.eval a b)))

/-- Reductions of the store semantics on constructor values (Fig. 5). -/
inductive SValHead : Store → Val 0 → Store → Val 0 → Prop where
  /-- (*reuses*) `S, ⋄k | Cᵏ a₁ … aₖ ⟶ₛ S, x ↦ Cᵏ a₁ … aₖ | x` for `k ≥ 1` and fresh `x` -/
  | reuse (S : Store) (c : CName) (as : List (Val 0)) (x : Nat) :
      as ≠ [] → (∀ a ∈ as, a.Atomic) → Var.loc x ∉ S.dom →
      SValHead ({Cell.credit as.length} + S) (.ctor c as)
        ({Cell.bind (.loc x) c as} + S) (.var (.loc x))
  /-- (*atoms*) `S | C ⟶ₛ S, x ↦ C | x` for fresh `x` -/
  | atom (S : Store) (c : CName) (x : Nat) :
      Var.loc x ∉ S.dom →
      SValHead S (.ctor c []) ({Cell.bind (.loc x) c []} + S) (.var (.loc x))

/-- The store semantics `S | E[e] ⟼ₛ S' | E[e']` (rule *eval*), where the evaluation
    context may also descend into the components of an unboxed tuple and into the
    arguments of constructors.  It runs closed expressions (`Expr 0`), whose only free
    variables are the locations of the store. -/
inductive SStep (sig : Sig) (fbip : Bool) : Store → Expr 0 → Store → Expr 0 → Prop where
  | head (E : ECtx 0) {S S' : Store} {e e' : Expr 0} :
      SHead sig fbip S e S' e' → SStep sig fbip S (E.plug e) S' (E.plug e')
  | val (E : ECtx 0) (done : List (Val 0)) (V : VCtx) (rest : List (Val 0)) {S S' : Store}
      {v v' : Val 0} :
      (∀ a ∈ done, a.Atomic) → V.Ok → SValHead S v S' v' →
      SStep sig fbip S (E.plug (.ret (done ++ V.plug v :: rest)))
        S' (E.plug (.ret (done ++ V.plug v' :: rest)))

/-- The reflexive-transitive closure `⟼*ₛ` of the store semantics. -/
inductive SSteps (sig : Sig) (fbip : Bool) : Store → Expr 0 → Store → Expr 0 → Prop where
  | refl (S : Store) (e : Expr 0) : SSteps sig fbip S e S e
  | tail {S₁ S₂ S₃ : Store} {e₁ e₂ e₃ : Expr 0} :
      SSteps sig fbip S₁ e₁ S₂ e₂ → SStep sig fbip S₂ e₂ S₃ e₃ → SSteps sig fbip S₁ e₁ S₃ e₃

/- ══════════════════ PAPER sec. 2.3, App. B.1 END: Store Semantics; Properties of Stores ══════════════════ -/

/- ══════════════════ PAPER sec. 2.3, 2.4 START: Theorem 2 (FIP reduces in place) and Theorem 3 (FBIP only deallocates) (PDF pp. 12-13) ══════════════════
   `SSteps.size_eq`: a FIP program never changes the size of the store (Theorem 2);
   `SSteps.size_le`: a FBIP program can only shrink it (Theorem 3). -/

/-! ## Theorems 2 and 3: FIP programs reduce in place, FBIP programs only deallocate -/

theorem SHead.size_eq {sig : Sig} {S S' : Store} {e e' : Expr 0}
    (h : SHead sig false S e S' e') : S'.size = S.size := by
  cases h <;> simp_all [Cell.size]

theorem SHead.size_le {sig : Sig} {fbip : Bool} {S S' : Store} {e e' : Expr 0}
    (h : SHead sig fbip S e S' e') : S'.size ≤ S.size := by
  cases h <;> simp [Cell.size]

theorem SValHead.size_eq {S S' : Store} {v v' : Val 0} (h : SValHead S v S' v') :
    S'.size = S.size := by
  cases h <;> simp [Cell.size]

theorem SStep.size_eq {sig : Sig} {S S' : Store} {e e' : Expr 0}
    (h : SStep sig false S e S' e') : S'.size = S.size := by
  cases h with
  | head E h => exact h.size_eq
  | val E done V rest _ _ h => exact h.size_eq

theorem SStep.size_le {sig : Sig} {fbip : Bool} {S S' : Store} {e e' : Expr 0}
    (h : SStep sig fbip S e S' e') : S'.size ≤ S.size := by
  cases h with
  | head E h => exact h.size_le
  | val E done V rest _ _ h => exact h.size_eq.le

/-- **Theorem 2** (a FIP program reduces in-place): for any `S | e ⟼*ₛ S' | e'` we have
    `|S| = |S'|`. -/
theorem SSteps.size_eq {sig : Sig} {S S' : Store} {e e' : Expr 0}
    (h : SSteps sig false S e S' e') : S'.size = S.size := by
  induction h with
  | refl => rfl
  | tail _ h ih => rw [h.size_eq, ih]

/-- **Theorem 3** (a FBIP program can only deallocate): for any `S | e ⟼*ₛ S' | e'` with
    the deallocation rules, `|S| ≥ |S'|`. -/
theorem SSteps.size_le {sig : Sig} {fbip : Bool} {S S' : Store} {e e' : Expr 0}
    (h : SSteps sig fbip S e S' e') : S'.size ≤ S.size := by
  induction h with
  | refl => exact le_rfl
  | tail _ h ih => exact h.size_le.trans ih

/- ══════════════════ PAPER sec. 2.3, 2.4 END: Theorem 2 (FIP reduces in place) and Theorem 3 (FBIP only deallocates) ══════════════════ -/

/- ══════════════════ PAPER sec. 2.3, App. B START: Store Semantics: Theorem 1 and Corollary 1; Soundness of Store Semantics (PDF p. 12; App. B.2-B.6 on pp. 40-54) ══════════════════
   Supporting lemmas of App. B: weakening (Lemma 4) and free variables of well-formed
   expressions (Lemma 5). -/

/-! ## Lemma 4: weakening -/

theorem SHead.weaken {sig : Sig} {fbip : Bool} {S S' : Store} {e e' : Expr 0}
    (h : SHead sig fbip S e S' e') (T : Store) : SHead sig fbip (S + T) e (S' + T) e' := by
  cases h with
  | letIn => exact .letIn _ _ _ _ ‹_› ‹_›
  | call => exact .call _ _ _ _ _ ‹_› ‹_› ‹_› ‹_› ‹_›
  | app => exact .app _ _ _ _ ‹_› ‹_› ‹_› ‹_›
  | bmatch S y c zs bs b hm hb =>
    exact .bmatch _ _ _ _ _ _ (Multiset.mem_add.mpr (Or.inl hm)) hb
  | dmatch S x c zs bs b hb =>
    rw [add_assoc, add_assoc]; exact .dmatch _ _ _ _ _ _ hb
  | drop S x c zs e hf =>
    rw [add_assoc]; exact .drop _ _ _ _ _ hf
  | free S k e hf =>
    rw [add_assoc]; exact .free _ _ _ hf
  | prim => exact .prim _ _ _ _

theorem SValHead.weaken {S S' : Store} {v v' : Val 0} (h : SValHead S v S' v') (T : Store)
    (hT : ∀ x ∈ S'.dom, x ∉ T.dom) : SValHead (S + T) v (S' + T) v' := by
  cases h with
  | reuse S c as x hne ha hx =>
    rw [add_assoc, add_assoc]
    refine .reuse _ _ _ _ hne ha ?_
    have hxT : Var.loc x ∉ T.dom := hT _ (by simp [Cell.dom])
    simp only [Store.dom_add, Multiset.mem_add, not_or]
    exact ⟨hx, hxT⟩
  | atom S c x hx =>
    rw [add_assoc]
    refine .atom _ _ _ ?_
    have hxT : Var.loc x ∉ T.dom := hT _ (by simp [Cell.dom])
    simp only [Store.dom_add, Multiset.mem_add, not_or]
    exact ⟨hx, hxT⟩

/-- **Lemma 4** (weakening for the store semantics): a step can be taken in a larger
    store, provided the added part binds locations different from those of the result
    (in particular, from the freshly allocated location). -/
theorem SStep.weaken {sig : Sig} {fbip : Bool} {S S' : Store} {e e' : Expr 0}
    (h : SStep sig fbip S e S' e') (T : Store) (hT : ∀ x ∈ S'.dom, x ∉ T.dom) :
    SStep sig fbip (S + T) e (S' + T) e' := by
  cases h with
  | head E h => exact .head E (h.weaken T)
  | val E done V rest hd hV h => exact .val E done V rest hd hV (h.weaken T hT)

/-! ## Lemma 5: free variables of well-formed expressions -/

theorem Val.mem_fvList {n : Nat} {x : Var n} {vs : List (Val n)} :
    x ∈ Val.fvList vs ↔ ∃ v ∈ vs, x ∈ Val.fv v := by
  induction vs with
  | nil => simp [Val.fvList]
  | cons v vs ih => simp [Val.fvList, ih]

theorem Branches.mem_fv {n : Nat} {x : Var n} : ∀ {bs : Branches n},
    x ∈ Branches.fv bs ↔ ∃ b ∈ bs.toList, x.shift b.binders.length ∈ b.body.fv
  | .nil => by simp [Branches.fv]
  | .cons c xs e bs => by
    have ih := Branches.mem_fv (x := x) (bs := bs)
    simp only [Branches.fv, List.mem_append, List.mem_filterMap, Var.unshift_eq_some, ih,
      Branches.toList_cons, List.mem_cons, exists_eq_or_imp]
    constructor
    · rintro (⟨y, hy, rfl⟩ | h)
      · exact .inl hy
      · exact .inr h
    · rintro (h | h)
      · exact .inl ⟨_, h, rfl⟩
      · exact .inr h

theorem Expr.mem_fv_letIn {n : Nat} {xs : List Bool} {e₂ : Expr (n + xs.length)} {x : Var n} :
    x ∈ (e₂.fv).filterMap (Var.unshift xs.length) ↔ x.shift xs.length ∈ e₂.fv := by
  simp only [List.mem_filterMap, Var.unshift_eq_some]
  constructor
  · rintro ⟨y, hy, rfl⟩; exact hy
  · intro h; exact ⟨_, h, rfl⟩

/-- A variable is *available* in `U | Δ | Γ` if it is scalar, borrowed or owned. -/
def Avail {n : Nat} (U Δ : Finset (Var n)) (Γ : Ctx n) (x : Var n) : Prop :=
  x ∈ U ∨ x ∈ Δ ∨ Res.var x ∈ Γ

mutual
theorem WfVal.fv_subset {n : Nat} {U Δ : Finset (Var n)} :
    ∀ {Γ : Ctx n} {v : Val n}, WfVal U Δ Γ v → ∀ x ∈ Val.fv v, Avail U Δ Γ x
  | _, _, .var y, x, hx => by simp_all [Val.fv, Avail]
  | _, _, .svar y hy, x, hx => by simp_all [Val.fv, Avail]
  | _, _, .atom _, x, hx => by simp_all [Val.fv, Val.fvList]
  | _, _, .lit _, x, hx => by simp_all [Val.fv]
  | _, _, .reuse c vs Γ _ hvs, x, hx => by
    simp only [Val.fv] at hx
    rcases WfVals.fv_subset hvs x hx with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Multiset.mem_add.mpr (Or.inl h)))
theorem WfVals.fv_subset {n : Nat} {U Δ : Finset (Var n)} :
    ∀ {Γ : Ctx n} {vs : List (Val n)}, WfVals U Δ Γ vs → ∀ x ∈ Val.fvList vs, Avail U Δ Γ x
  | _, _, .nil, x, hx => by simp [Val.fvList] at hx
  | _, _, .cons Γ₁ Γ₂ v vs hv hvs, x, hx => by
    simp only [Val.fvList, List.mem_append] at hx
    rcases hx with hx | hx
    · rcases WfVal.fv_subset hv x hx with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Multiset.mem_add.mpr (Or.inl h)))
    · rcases WfVals.fv_subset hvs x hx with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Multiset.mem_add.mpr (Or.inr h)))
end

theorem Avail.mono {n : Nat} {U Δ U' Δ' : Finset (Var n)} {Γ Γ' : Ctx n} {x : Var n}
    (h : Avail U Δ Γ x) (hU : U ⊆ U') (hΔ : Δ ⊆ Δ') (hΓ : Γ ≤ Γ') : Avail U' Δ' Γ' x := by
  rcases h with h | h | h
  · exact Or.inl (hU h)
  · exact Or.inr (Or.inl (hΔ h))
  · exact Or.inr (Or.inr (Multiset.mem_of_le hΓ h))

theorem mem_vars_toFinset {n : Nat} {Γ : Ctx n} {x : Var n} (h : x ∈ Γ.vars.toFinset) :
    Res.var x ∈ Γ := by
  simp only [Multiset.mem_toFinset, Ctx.vars, Multiset.mem_filterMap] at h
  obtain ⟨r, hr, hx⟩ := h
  cases r <;> simp_all

/-- Availability of a weakened variable under a binder. -/
theorem Avail.unshift {n : Nat} {xs : List Bool} {U Δ : Finset (Var n)} {Γ : Ctx n} {x : Var n}
    {Δ' : Finset (Var (n + xs.length))}
    (hΔ' : ∀ y ∈ Δ', y ∈ Vars.shift xs.length Δ ∨ y ∈ Binder.ownedSet xs)
    (h : Avail (Vars.shift xs.length U ∪ Binder.scalars xs) Δ'
      (Γ.shift xs.length + Binder.owned xs) (x.shift xs.length)) : Avail U Δ Γ x := by
  rcases h with h | h | h
  · rcases Finset.mem_union.mp h with h | h
    · exact Or.inl (Vars.mem_shift.mp h)
    · exact absurd h (Binder.shift_not_mem_scalars xs x)
  · rcases hΔ' _ h with h | h
    · exact Or.inr (Or.inl (Vars.mem_shift.mp h))
    · exact absurd h (Binder.shift_not_mem_ownedSet xs x)
  · rcases Multiset.mem_add.mp h with h | h
    · exact Or.inr (Or.inr (Ctx.mem_shift_var.mp h))
    · exact absurd h (Binder.shift_not_mem_owned xs x)

/-- **Lemma 5** (free variables of FIP expressions are in `Δ, Γ`): if `Δ | Γ ⊢ e` then
    `fv(e) ⊆ Δ, Γ` (plus the scalar variables `U`, for the scalar extension). -/
theorem Wf.fv_subset {cfg : Cfg} {n : Nat} {U Δ : Finset (Var n)} {Γ : Ctx n} {e : Expr n}
    (h : Wf cfg U Δ Γ e) : ∀ x ∈ e.fv, Avail U Δ Γ x := by
  induction h with
  | tuple hvs => exact fun x hx => WfVals.fv_subset hvs x hx
  | call f ys e hf hys _ ih =>
    intro x hx
    simp only [Expr.fv, List.mem_append] at hx
    rcases hx with hx | hx
    · obtain ⟨v, hv, hxv⟩ := Val.mem_fvList.mp hx
      have := hys v hv
      cases v <;> (simp_all [Val.fv, BorrowArg, Avail]; try tauto)
    · exact (ih x hx).mono (Finset.Subset.refl _) (Finset.Subset.refl _) (Multiset.le_add_right _ _)
  | bapp y e hy _ ih =>
    intro x hx
    simp only [Expr.fv, List.mem_append] at hx
    rcases hx with hx | hx
    · simp_all [Val.fvList, Val.fv, Avail]
    · exact ih x hx
  | fapp f e hf _ ih =>
    intro x hx
    simp only [Expr.fv, List.mem_append] at hx
    rcases hx with hx | hx
    · simp [Val.fvList, Val.fv] at hx
    · exact (ih x hx).mono (Finset.Subset.refl _) (Finset.Subset.refl _)
        (Multiset.le_add_right _ _)
  | letIn Γ₁ Γ₂ Γ₃ xs e₁ e₂ hΓ₂ _ _ ih1 ih2 =>
    intro x hx
    simp only [Expr.fv, List.mem_append] at hx
    rcases hx with hx | hx
    · rcases ih1 x hx with h | h | h
      · exact Or.inl h
      · rcases Finset.mem_union.mp h with h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (by
            have := mem_vars_toFinset h
            exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_add.mpr (Or.inr this)))))
      · exact Or.inr (Or.inr (Multiset.mem_add.mpr
          (Or.inl (Multiset.mem_add.mpr (Or.inl h)))))
    · have := Avail.unshift (fun y hy => Or.inl hy) (ih2 _ (Expr.mem_fv_letIn.mp hx))
      refine this.mono (Finset.Subset.refl _) (Finset.Subset.refl _) ?_
      rw [add_assoc]; exact Multiset.le_add_left _ _
  | bmatch y bs hy _ ih =>
    intro x hx
    simp only [Expr.fv, List.mem_append] at hx
    rcases hx with hx | hx
    · simp only [Val.fvList, Val.fv, List.append_nil, List.mem_singleton] at hx
      subst hx
      rcases hy with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
    · obtain ⟨b, hb, hxb⟩ := Branches.mem_fv.mp hx
      have h := ih b hb _ hxb
      exact Avail.unshift (fun y hy => Finset.mem_union.mp hy)
        (h.mono (Finset.Subset.refl _) (Finset.Subset.refl _) (Multiset.le_add_right _ _))
  | @dmatch n U Δ Γ x' bs _ ih =>
    intro x hx
    simp only [Expr.fv, List.mem_append] at hx
    rcases hx with hx | hx
    · simp only [Val.fvList, Val.fv, List.append_nil, List.mem_singleton] at hx
      subst hx
      exact Or.inr (Or.inr (Multiset.mem_add.mpr (Or.inr (Multiset.mem_singleton_self _))))
    · obtain ⟨b, hb, hxb⟩ := Branches.mem_fv.mp hx
      have h := ih b hb _ hxb
      have h' : Avail (Vars.shift b.binders.length U ∪ Binder.scalars b.binders)
          (Vars.shift b.binders.length Δ) (Ctx.shift b.binders.length Γ + Binder.owned b.binders)
          (x.shift b.binders.length) := by
        rcases h with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · rcases Multiset.mem_add.mp h with h | h
          · exact Or.inr (Or.inr h)
          · simp at h
      exact (Avail.unshift (fun y hy => Or.inl hy) h').mono (Finset.Subset.refl _)
        (Finset.Subset.refl _) (Multiset.le_add_right _ _)
  | empty _ ih =>
    exact fun x hx => (ih x hx).mono (Finset.Subset.refl _) (Finset.Subset.refl _) (Multiset.le_add_right _ _)
  | drop x' _ _ ih =>
    intro x hx
    simp only [Expr.fv, List.mem_append] at hx
    rcases hx with hx | hx
    · simp only [Val.fv, List.mem_singleton] at hx
      subst hx
      exact Or.inr (Or.inr (Multiset.mem_add.mpr (Or.inr (Multiset.mem_singleton_self _))))
    · exact (ih x hx).mono (Finset.Subset.refl _) (Finset.Subset.refl _) (Multiset.le_add_right _ _)
  | free k _ _ _ ih =>
    exact fun x hx => (ih x hx).mono (Finset.Subset.refl _) (Finset.Subset.refl _) (Multiset.le_add_right _ _)
  | inst k _ _ ih =>
    intro x hx
    rcases ih x hx with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · refine Or.inr (Or.inr (Multiset.mem_add.mpr (Or.inl ?_)))
      rcases Multiset.mem_add.mp h with h | h
      · exact h
      · simp at h
  | weaken _ ih =>
    exact fun x hx => (ih x hx).mono (Finset.Subset.refl _) (Finset.Subset.refl _) (Multiset.le_add_right _ _)
  | prim op vs hvs =>
    intro x hx
    simp only [Expr.fv] at hx
    obtain ⟨v, hv, hxv⟩ := Val.mem_fvList.mp hx
    have := hvs v hv
    cases v <;> (simp_all [Val.fv, ScalarArg, Avail]; try tauto)

end FIP

/- ══════════════════ PAPER sec. 2.3, App. B END: Store Semantics: Theorem 1 and Corollary 1; Soundness of Store Semantics ══════════════════ -/
