module

public import RequestProject.AppE_HeapSoundness.LamSyntax

@[expose] public section

/- ══════════════════ PAPER sec. 5, 5.1, 5.2, App. E.1 START: Reference Counting with Borrowing and Unboxing; Elaborating borrowing; Heap semantics; Properties of Heaps (PDF pp. 22-25, Fig. 9, 10; App. E.1 on pp. 71-75) ══════════════════
   Functional semantics and typing of `lambda-fip`, elaboration of destructive match
   (sec. 5.1), heaps with reference counts and the heap semantics `H | e |->h H' | e'`. -/

/-!
# Reference counting with borrowing and unboxing: `λfip` and its heap semantics
(Section 5, Fig. 9, Fig. 10, Appendix E)

The `λfip` calculus (syntax in `RequestProject/AppE_HeapSoundness/LamSyntax.lean`) extends
the FBIP calculus with lambdas `λ^z̄ x̄. e`, `dup x; e`, the reuse-drop `dropru x; e` (which
drops `x` and yields a reuse credit `⋄k` of the size `k` of `x`), `alloc k; e`, and a
*non-destructive* match on a variable whose branches first duplicate the fields:
`match x {Cᵢ x̄ᵢ ↦ dup x̄ᵢ; eᵢ}`.  In `dropru x; e` the size `k` of `x` is recorded in the
syntax (`LExpr.dropru x k e`), since our expressions carry no types.

The *heap* extends a store with reference counts `n ≥ 1` and closures:
`H ::= ∅ | H, ⋄k | H, x ↦ⁿ φ` with `φ ::= C x̄ | λ^z̄ x̄. e`.

This file formalizes the functional semantics, the typing rules of Fig. 9, the heap
semantics of Fig. 10 and the join `H₁ ⊗ H₂` of heaps (Appendix E.1).  The functional and
the heap semantics run closed expressions `LExpr 0`; the heap binds locations only (the only
variables of scope `0`).  **Theorem 6** is proved in
`RequestProject/AppE_HeapSoundness/HeapSound.lean` (`heap_sound`);
`RequestProject/AppE_HeapSoundness/HeapCex.lean` shows that, as stated, it needs two extra
hypotheses (`heap_sound_needs_adm`, `heap_sound_needs_no_fn`).  We also
prove that the translation of a destructive match into `λfip` is well-formed
(`LWf.dmatch_translation`, Section 5).
-/

namespace FIP.Lam

/-! ## Functional semantics -/

/-- A top-level function `f(ȳ; x̄) = e` of `λfip` with `borrowed` parameters `ȳ` and `owned`
    parameters `x̄`; in the body the index `j < borrowed` is `yⱼ` and `borrowed + i` is
    `xᵢ`. -/
structure LFunDef where
  name : FName
  borrowed : Nat
  owned : Nat
  body : LExpr (owned + borrowed)

/-- A signature of `λfip` functions. -/
abbrev LSig := List LFunDef

/-- Look up a function. -/
def LSig.lookup (sig : LSig) (f : FName) : Option LFunDef := sig.find? (·.name == f)

/-- The names of the functions of a signature. -/
def LSig.funs (sig : LSig) : List FName := sig.map (·.name)

/-- The body of a function instantiated with its arguments: `e[ȳ := v̄₁, x̄ := v̄₂]`. -/
def LFunDef.instBody (fd : LFunDef) (vs1 vs2 : List (LVal 0)) : LExpr 0 :=
  fd.body.subst (LSubst.inst fd.borrowed vs1 (LSubst.ofList fd.owned vs2))

/-- `e[x̄ := v̄]` for the `k` variables of the body `e` of a closed binder. -/
def LExpr.inst0 {k : Nat} (e : LExpr (0 + k)) (vs : List (LVal 0)) : LExpr 0 :=
  e.subst (LSubst.inst k vs Fin.elim0)

/-- β-reduction: the body of `λ^z̄ x̄. e` instantiated with the arguments `v̄` and the
    captured values `z̄`. -/
def LExpr.beta {c k : Nat} (e : LExpr (c + k)) (zs vs : List (LVal 0)) : LExpr 0 :=
  e.subst (LSubst.inst k vs (LSubst.ofList c zs))

/-- The singleton tuple `(v)`. -/
abbrev LExpr.val {n : Nat} (v : LVal n) : LExpr n := .ret (.cons v .nil)

/-- Evaluation contexts (of closed expressions). -/
inductive LECtx where
  | hole
  | appL (E : LECtx) (e : LExpr 0)
  | appR (vs : LVals 0) (E : LECtx)
  | callB (f : FName) (E : LECtx) (e : LExpr 0)
  | callO (f : FName) (vs : LVals 0) (E : LECtx)
  | letIn (k : Nat) (E : LECtx) (e : LExpr (0 + k))

/-- `E[e]`. -/
def LECtx.plug : LECtx → LExpr 0 → LExpr 0
  | .hole, e => e
  | .appL E e2, e => .app (E.plug e) e2
  | .appR vs E, e => .app (.ret vs) (E.plug e)
  | .callB f E e2, e => .call f (E.plug e) e2
  | .callO f vs E, e => .call f (.ret vs) (E.plug e)
  | .letIn k E e2, e => .letIn k (E.plug e) e2

/-- Head reductions of `λfip` (Fig. 3 extended by Fig. 6 and Fig. 9): `dup`, `drop`,
    `dropru`, `free` and `alloc` have no effect in the functional semantics. -/
inductive LHead (sig : LSig) : LExpr 0 → LExpr 0 → Prop where
  | letIn (k : Nat) (vs : LVals 0) (e : LExpr (0 + k)) : vs.length = k →
      LHead sig (.letIn k (.ret vs) e) (e.inst0 vs.toList)
  | call (f : FName) (fd : LFunDef) (vs1 vs2 : LVals 0) : sig.lookup f = some fd →
      fd.borrowed = vs1.length → fd.owned = vs2.length →
      LHead sig (.call f (.ret vs1) (.ret vs2)) (fd.instBody vs1.toList vs2.toList)
  | appFn (f : FName) (fd : LFunDef) (vs : LVals 0) : sig.lookup f = some fd →
      fd.borrowed = 0 → fd.owned = vs.length →
      LHead sig (.app (.val (.fn f)) (.ret vs)) (fd.instBody [] vs.toList)
  /-- (*beta*) `(λ^z̄ x̄. e) v̄ ⟶ e[x̄ := v̄]` -/
  | beta (zs : LVals 0) (c k : Nat) (e : LExpr (c + k)) (vs : LVals 0) : vs.length = k →
      LHead sig (.app (.val (.lam zs c k e)) (.ret vs)) (e.beta zs.toList vs.toList)
  | «match» (c : CName) (vs : LVals 0) (bs : LBranches 0) (b : LBranch 0) :
      bs.find c vs.length = some b →
      LHead sig (.match (.ctor c vs) bs) (b.body.inst0 vs.toList)
  | dup (v : LVal 0) (e : LExpr 0) : LHead sig (.dup v e) e
  | drop (v : LVal 0) (e : LExpr 0) : LHead sig (.drop v e) e
  | dropru (v : LVal 0) (k : Nat) (e : LExpr 0) : LHead sig (.dropru v k e) e
  | free (k : Nat) (e : LExpr 0) : LHead sig (.free k e) e
  | alloc (k : Nat) (e : LExpr 0) : LHead sig (.alloc k e) e

/-- The functional semantics `e ⟼ e'`. -/
inductive LStep (sig : LSig) : LExpr 0 → LExpr 0 → Prop where
  | step (E : LECtx) {e e' : LExpr 0} : LHead sig e e' → LStep sig (E.plug e) (E.plug e')

/-- `⟼*`. -/
abbrev LSteps (sig : LSig) := Relation.ReflTransGen (LStep sig)

/-! ## Well-formed `λfip` expressions (Fig. 9)

The multiplicity of each variable in `Γ` is unconstrained: a variable may be owned
several times, once per reference.  Under a binder the environments are weakened and the
new variables are added; they are fresh by construction. -/

/-- The owned environment `z̄` of a list of variables. -/
def varCtx {n : Nat} (zs : List (Var n)) : Ctx n := ((zs.map Res.var : List (Res n)))

/-- The borrowed parameters `ȳ` of a function body (the innermost `k` variables). -/
def bSet (n k : Nat) : Finset (Var (n + k)) := ((List.finRange k).map Var.newB).toFinset

/-- A borrowed argument: a borrowed variable or a top-level function. -/
def LBorrowArg {n : Nat} (funs : List FName) (Δ : Finset (Var n)) : LVal n → Prop
  | .var y => y ∈ Δ
  | .fn g => g ∈ funs
  | _ => False

mutual
/-- Well-formed values `Δ | Γ ⊢ v`. -/
inductive LWfVal (funs : List FName) : {n : Nat} → Finset (Var n) → Ctx n → LVal n → Prop where
  /-- `var` -/
  | var {n : Nat} {Δ : Finset (Var n)} (x : Var n) : LWfVal funs Δ {Res.var x} (.var x)
  /-- `atom` -/
  | atom {n : Nat} {Δ : Finset (Var n)} (c : CName) : LWfVal funs Δ 0 (.ctor c .nil)
  /-- `reuse`: `Δ | Γ₁, …, Γₖ, ⋄k ⊢ Cᵏ v₁ … vₖ` -/
  | reuse {n : Nat} {Δ : Finset (Var n)} (c : CName) (vs : LVals n) (Γ : Ctx n) :
      vs ≠ .nil → LWfVals funs Δ Γ vs.toList →
      LWfVal funs Δ (Γ + {Res.credit vs.length}) (.ctor c vs)
  /-- `lam`: `Δ | z̄ ⊢ λ^z̄ x̄. e` if `∅ | z̄, x̄ ⊢ e`: the body owns each captured variable
      and each parameter once -/
  | lam {n : Nat} {Δ : Finset (Var n)} (zs : List (Var n)) (c k : Nat) (e : LExpr (c + k)) :
      zs.length = c → LWf funs ∅ (allCtx (c + k)) e →
      LWfVal funs Δ (varCtx zs) (.lam (LVals.ofList (zs.map .var)) c k e)
/-- Well-formed lists of values. -/
inductive LWfVals (funs : List FName) : {n : Nat} → Finset (Var n) → Ctx n → List (LVal n) →
    Prop where
  | nil {n : Nat} {Δ : Finset (Var n)} : LWfVals funs Δ 0 []
  | cons {n : Nat} {Δ : Finset (Var n)} (Γ₁ Γ₂ : Ctx n) (v : LVal n) (vs : List (LVal n)) :
      LWfVal funs Δ Γ₁ v → LWfVals funs Δ Γ₂ vs → LWfVals funs Δ (Γ₁ + Γ₂) (v :: vs)
/-- Well-formed expressions `Δ | Γ ⊢ e` of `λfip`. -/
inductive LWf (funs : List FName) : {n : Nat} → Finset (Var n) → Ctx n → LExpr n → Prop where
  /-- `tuple` -/
  | tuple {n : Nat} {Δ : Finset (Var n)} {Γ : Ctx n} (vs : LVals n) :
      LWfVals funs Δ Γ vs.toList → LWf funs Δ Γ (.ret vs)
  /-- `call` -/
  | call {n : Nat} {Δ : Finset (Var n)} {Γ : Ctx n} (f : FName) (ys : LVals n) (e : LExpr n) :
      f ∈ funs → (∀ y ∈ ys.toList, LBorrowArg funs Δ y) → LWf funs Δ Γ e →
      LWf funs Δ Γ (.call f (.ret ys) e)
  /-- `app`: `Δ | Γ₁, Γ₂ ⊢ e₁ e₂` -/
  | app {n : Nat} {Δ : Finset (Var n)} (Γ₁ Γ₂ : Ctx n) (e₁ e₂ : LExpr n) :
      LWf funs Δ Γ₁ e₁ → LWf funs Δ Γ₂ e₂ → LWf funs Δ (Γ₁ + Γ₂) (.app e₁ e₂)
  /-- `let` -/
  | letIn {n : Nat} {Δ : Finset (Var n)} (Γ₁ Γ₂ Γ₃ : Ctx n) (k : Nat) (e₁ : LExpr n)
      (e₂ : LExpr (n + k)) : Γ₂.OnlyVars →
      LWf funs (Δ ∪ Γ₂.vars.toFinset) Γ₁ e₁ →
      LWf funs (Vars.shift k Δ) (Ctx.shift k (Γ₂ + Γ₃) + bCtx n k) e₂ →
      LWf funs Δ (Γ₁ + Γ₂ + Γ₃) (.letIn k e₁ e₂)
  /-- `match`: `Δ | Γ ⊢ match x {Cᵢ x̄ᵢ ↦ dup x̄ᵢ; eᵢ}` for `x ∈ Δ, Γ` -/
  | «match» {n : Nat} {Δ : Finset (Var n)} {Γ : Ctx n} (x : Var n) (bs : LBranches n) :
      (x ∈ Δ ∨ Res.var x ∈ Γ) →
      (es : (b : LBranch n) → LExpr (n + b.k)) →
      (∀ b ∈ bs.toList, b.body = dups (bvals n b.k) (es b)) →
      (∀ b ∈ bs.toList, LWf funs (Vars.shift b.k Δ) (Ctx.shift b.k Γ + bCtx n b.k) (es b)) →
      LWf funs Δ Γ (.match (.var x) bs)
  /-- `dup`: `Δ | Γ ⊢ dup x; e` if `Δ | Γ, x ⊢ e` and `x ∈ Δ, Γ` -/
  | dup {n : Nat} {Δ : Finset (Var n)} {Γ : Ctx n} {e : LExpr n} (x : Var n) :
      (x ∈ Δ ∨ Res.var x ∈ Γ) → LWf funs Δ (Γ + {Res.var x}) e →
      LWf funs Δ Γ (.dup (.var x) e)
  /-- `drop` -/
  | drop {n : Nat} {Δ : Finset (Var n)} {Γ : Ctx n} {e : LExpr n} (x : Var n) :
      LWf funs Δ Γ e → LWf funs Δ (Γ + {Res.var x}) (.drop (.var x) e)
  /-- `dropru`: `Δ | Γ, x ⊢ dropru x; e` if `Δ | Γ, ⋄k ⊢ e` with `k = size(x)` -/
  | dropru {n : Nat} {Δ : Finset (Var n)} {Γ : Ctx n} {e : LExpr n} (x : Var n) (k : Nat) :
      LWf funs Δ (Γ + {Res.credit k}) e → LWf funs Δ (Γ + {Res.var x}) (.dropru (.var x) k e)
  /-- `free` -/
  | free {n : Nat} {Δ : Finset (Var n)} {Γ : Ctx n} {e : LExpr n} (k : Nat) : 1 ≤ k →
      LWf funs Δ Γ e → LWf funs Δ (Γ + {Res.credit k}) (.free k e)
  /-- `alloc`: `Δ | Γ ⊢ alloc k; e` if `Δ | Γ, ⋄k ⊢ e` and `k ≥ 1` -/
  | alloc {n : Nat} {Δ : Finset (Var n)} {Γ : Ctx n} {e : LExpr n} (k : Nat) : 1 ≤ k →
      LWf funs Δ (Γ + {Res.credit k}) e → LWf funs Δ Γ (.alloc k e)
  /-- `empty` -/
  | empty {n : Nat} {Δ : Finset (Var n)} {Γ : Ctx n} {e : LExpr n} :
      LWf funs Δ Γ e → LWf funs Δ (Γ + {Res.credit 0}) e
end

/-- A well-formed `λfip` signature: `ȳ | x̄ ⊢ e` for each `f(ȳ; x̄) = e`. -/
def LSig.Wf (sig : LSig) : Prop :=
  ∀ fd ∈ sig, LWf sig.funs (bSet fd.owned fd.borrowed) (Ctx.shift fd.borrowed (allCtx fd.owned))
    fd.body

/-- `dup x̄; e` is well-formed if `e` is well-formed with `x̄` added to the owned
    environment. -/
theorem LWf.dups {funs : List FName} {n : Nat} {Δ : Finset (Var n)} :
    ∀ (xs : List (Var n)) {Γ : Ctx n} {e : LExpr n}, (∀ x ∈ xs, x ∈ Δ ∨ Res.var x ∈ Γ) →
      LWf funs Δ (Γ + varCtx xs) e → LWf funs Δ Γ (FIP.Lam.dups (xs.map .var) e)
  | [], Γ, e, _, h => by simpa [varCtx, FIP.Lam.dups] using h
  | x :: xs, Γ, e, hx, h => by
    simp only [List.map_cons, FIP.Lam.dups]
    refine LWf.dup x (hx x (List.mem_cons_self ..)) (LWf.dups xs ?_ ?_)
    · intro y hy
      rcases hx y (List.mem_cons_of_mem _ hy) with h' | h'
      · exact .inl h'
      · exact .inr (Multiset.mem_add.mpr (.inl h'))
    · have : Γ + varCtx (x :: xs) = Γ + {Res.var x} + varCtx xs := by
        simp [varCtx, Multiset.singleton_add, add_assoc]
      rw [← this]; exact h

theorem bvals_eq_map (n k : Nat) :
    bvals n k = ((List.finRange k).map fun j => (Var.newB j : Var (n + k))).map LVal.var := by
  simp [bvals, List.map_map, Function.comp_def]

theorem varCtx_newB (n k : Nat) :
    varCtx ((List.finRange k).map fun j => (Var.newB j : Var (n + k))) = bCtx n k := by
  simp [varCtx, bCtx, List.map_map, Function.comp_def]

/-- Remove `j` leading `dup`s: the inverse of `dups`. -/
def undups {m : Nat} : Nat → LExpr m → LExpr m
  | j + 1, .dup _ e => undups j e
  | _, e => e

theorem undups_dups {m : Nat} : ∀ (xs : List (LVal m)) (e : LExpr m),
    undups xs.length (dups xs e) = e
  | [], e => by cases e <;> rfl
  | x :: xs, e => by simp only [List.length_cons, dups, undups]; exact undups_dups xs e

theorem length_bvals (n k : Nat) : (bvals n k).length = k := by simp [bvals]

/-- The translation of the branches of `match! x {Cᵢ x̄ᵢ ↦ eᵢ}` into the branches
    `Cᵢ x̄ᵢ ↦ dup x̄ᵢ; dropru x; eᵢ` of a non-destructive match. -/
def dmatchBranches {n : Nat} (x : Var n) : LBranches n → LBranches n
  | .nil => .nil
  | .cons c k e r => .cons c k (dups (bvals n k) (.dropru (.var (x.shift k)) k e))
      (dmatchBranches x r)

theorem mem_dmatchBranches {n : Nat} (x : Var n) :
    ∀ {bs : LBranches n} {b : LBranch n}, b ∈ (dmatchBranches x bs).toList →
      ∃ b₀ ∈ bs.toList, b = ⟨b₀.ctor, b₀.k,
        dups (bvals n b₀.k) (.dropru (.var (x.shift b₀.k)) b₀.k b₀.body)⟩
  | .nil, b, h => by simp [dmatchBranches] at h
  | .cons c k e r, b, h => by
    simp only [dmatchBranches, LBranches.toList_cons, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨⟨c, k, e⟩, by simp, rfl⟩
    · obtain ⟨b₀, hb₀, rfl⟩ := mem_dmatchBranches x h
      exact ⟨b₀, by simp [hb₀], rfl⟩

/-- **The translation of `match!`** (Section 5).  If the branches of a destructive match
    `match! x {Cᵢ x̄ᵢ ↦ eᵢ}` are well-formed in the FBIP style, `Δ | Γ, x̄ᵢ, ⋄k ⊢ eᵢ`, then
    its translation `match x {Cᵢ x̄ᵢ ↦ dup x̄ᵢ; dropru x; eᵢ}` is well-formed in `λfip`:
    `Δ | Γ, x ⊢ match x {…}`. -/
theorem LWf.dmatch_translation {funs : List FName} {n : Nat} {Δ : Finset (Var n)} {Γ : Ctx n}
    (x : Var n) (bs : LBranches n)
    (hbs : ∀ b ∈ bs.toList, LWf funs (Vars.shift b.k Δ)
      (Ctx.shift b.k Γ + bCtx n b.k + {Res.credit b.k}) b.body) :
    LWf funs Δ (Γ + {Res.var x}) (.match (.var x) (dmatchBranches x bs)) := by
  refine LWf.match x _ (.inr (Multiset.mem_add.mpr (.inr (Multiset.mem_singleton_self _))))
    (fun b => undups b.k b.body) ?_ ?_
  · intro b hb
    obtain ⟨b₀, -, rfl⟩ := mem_dmatchBranches x hb
    dsimp only
    conv_lhs => rw [← undups_dups (bvals n b₀.k) (.dropru (.var (x.shift b₀.k)) b₀.k b₀.body)]
    rw [length_bvals]
  · intro b hb
    obtain ⟨b₀, hb₀, rfl⟩ := mem_dmatchBranches x hb
    dsimp only
    have := undups_dups (bvals n b₀.k) (.dropru (.var (x.shift b₀.k)) b₀.k b₀.body)
    rw [length_bvals] at this
    rw [this]
    have h := LWf.dropru (Γ := Ctx.shift b₀.k Γ + bCtx n b₀.k) (x.shift b₀.k) b₀.k (hbs b₀ hb₀)
    have e : Ctx.shift b₀.k Γ + bCtx n b₀.k + {Res.var (x.shift b₀.k)} =
        Ctx.shift b₀.k (Γ + {Res.var x}) + bCtx n b₀.k := by
      simp [Ctx.shift, Res.shift]; abel
    rwa [e] at h

/-! ## Heaps (Fig. 10) -/

/-- The object `φ ::= C x̄ | λ^z̄ x̄. e` bound in a heap cell. -/
inductive HObj where
  | con (c : CName) (args : List (LVal 0))
  | clo (zs : List (LVal 0)) (c k : Nat) (body : LExpr (c + k))

/-- The free variables (locations) of an object. -/
def HObj.fv : HObj → List (Var 0)
  | .con _ args => LVal.fvList args
  | .clo zs _ _ _ => LVal.fvList zs

/-- A heap cell: `x ↦ⁿ φ` with reference count `n ≥ 1`, or a reuse credit `⋄k`. -/
inductive HCell where
  | bind (x : Var 0) (n : Nat) (o : HObj)
  | credit (k : Nat)

/-- A heap. -/
abbrev Heap := Multiset HCell

namespace Heap

/-- `dom(H)`. -/
def dom (H : Heap) : Multiset (Var 0) :=
  H.bind fun | .bind x _ _ => {x} | .credit _ => 0

/-- `fv(rng(H))`, with multiplicity. -/
def rngFv (H : Heap) : Multiset (Var 0) :=
  H.bind fun | .bind _ _ o => (o.fv : Multiset (Var 0)) | .credit _ => 0

/-- A heap is *sound* if each location is bound once, all reference counts are
    positive, and the free variables of its objects are bound. -/
def Sound (H : Heap) : Prop :=
  H.dom.Nodup ∧ (∀ x n o, HCell.bind x n o ∈ H → 1 ≤ n) ∧ ∀ x ∈ H.rngFv, x ∈ H.dom

/-- A heap is *linear* if it is sound and the reference count of each cell accounts at
    least for the references from the heap itself. -/
def Linear (H : Heap) : Prop :=
  H.Sound ∧ ∀ x n o, HCell.bind x n o ∈ H → H.rngFv.count x ≤ n

/-- `roots(H)`: each location as often as its reference count exceeds its references
    from the heap, and the non-empty reuse credits. -/
noncomputable def roots (H : Heap) : Ctx 0 :=
  open Classical in
  H.bind fun
    | .bind x n _ => Multiset.replicate (n - H.rngFv.count x) (Res.var x)
    | .credit k => if k = 0 then 0 else {Res.credit k}

/-- Decrement the reference counts of the variables `zs` (once per occurrence). -/
def decr (zs : List (Var 0)) (H : Heap) : Heap :=
  H.map fun | .bind x n o => .bind x (n - zs.count x) o | .credit k => .credit k

end Heap

/-- The join `H₁ ⊗ H₂` of heaps (Appendix E.1):
```
∅ ⊗ H₂ = H₂
H₁, ⋄k ⊗ H₂ = H₁ ⊗ H₂, ⋄k
H₁, x ↦ⁿ v ⊗ H₂ = H₁ ⊗ H₂, x ↦ⁿ v                           iff x ∉ dom(H₂)
H₁, x ↦ⁿ v ⊗ H₂, x ↦ᵐ v, z̄ ↦ᵏ⁺¹ w̄ = H₁ ⊗ H₂, x ↦ⁿ⁺ᵐ v, z̄ ↦ᵏ w̄   iff z̄ = fv(v)
```
In the last case the reference counts of the children `z̄` of `v` are decremented once per
occurrence, since `v` is now shared. -/
inductive HJoin : Heap → Heap → Heap → Prop where
  | nil (H₂ : Heap) : HJoin 0 H₂ H₂
  | credit {H₁ H₂ H : Heap} (k : Nat) : HJoin H₁ ({HCell.credit k} + H₂) H →
      HJoin ({HCell.credit k} + H₁) H₂ H
  | fresh {H₁ H₂ H : Heap} (x : Var 0) (n : Nat) (o : HObj) : x ∉ H₂.dom →
      HJoin H₁ ({HCell.bind x n o} + H₂) H → HJoin ({HCell.bind x n o} + H₁) H₂ H
  | share {H₁ H₂ H : Heap} (x : Var 0) (n m : Nat) (o : HObj) :
      (∀ z ∈ o.fv, ∃ k p, HCell.bind z k p ∈ H₂ ∧ o.fv.count z < k) →
      HJoin H₁ ({HCell.bind x (n + m) o} + Heap.decr o.fv H₂) H →
      HJoin ({HCell.bind x n o} + H₁) ({HCell.bind x m o} + H₂) H

/-! ## Heap semantics (Fig. 10) -/

/-- Atomic values: variables and top-level functions. -/
def LVal.Atomic {n : Nat} : LVal n → Prop
  | .var _ => True
  | .fn _ => True
  | _ => False

/-- Head reductions of the heap semantics on expressions. -/
inductive HHead (sig : LSig) : Heap → LExpr 0 → Heap → LExpr 0 → Prop where
  | letIn (H : Heap) (k : Nat) (as : LVals 0) (e : LExpr (0 + k)) :
      (∀ a ∈ as.toList, a.Atomic) → as.length = k →
      HHead sig H (.letIn k (.ret as) e) H (e.inst0 as.toList)
  | call (H : Heap) (f : FName) (fd : LFunDef) (as1 as2 : LVals 0) :
      sig.lookup f = some fd → (∀ a ∈ as1.toList ++ as2.toList, a.Atomic) →
      fd.borrowed = as1.length → fd.owned = as2.length →
      HHead sig H (.call f (.ret as1) (.ret as2)) H (fd.instBody as1.toList as2.toList)
  | appFn (H : Heap) (f : FName) (fd : LFunDef) (as : LVals 0) :
      sig.lookup f = some fd → fd.borrowed = 0 → (∀ a ∈ as.toList, a.Atomic) →
      fd.owned = as.length →
      HHead sig H (.app (.val (.fn f)) (.ret as)) H (fd.instBody [] as.toList)
  /-- (*app_h*) `H | y ā ⟶ₕ H | dup z̄; drop y; e[x̄ := ā]` with `y ↦ⁿ λ^z̄ x̄. e ∈ H` -/
  | app (H : Heap) (y : Var 0) (n : Nat) (zs : List (LVal 0)) (c k : Nat) (e : LExpr (c + k))
      (as : LVals 0) : HCell.bind y n (.clo zs c k e) ∈ H → (∀ a ∈ as.toList, a.Atomic) →
      as.length = k →
      HHead sig H (.app (.val (.var y)) (.ret as)) H
        (dups zs (.drop (.var y) (e.beta zs as.toList)))
  /-- (*match_h*) `H | match x {p ↦ e} ⟶ₕ H | eᵢ[x̄ := z̄]` with `x ↦ⁿ C z̄ ∈ H` -/
  | «match» (H : Heap) (x : Var 0) (n : Nat) (c : CName) (zs : List (LVal 0))
      (bs : LBranches 0) (b : LBranch 0) : HCell.bind x n (.con c zs) ∈ H →
      bs.find c zs.length = some b →
      HHead sig H (.match (.var x) bs) H (b.body.inst0 zs)
  /-- (*dup_h*) `H, x ↦ⁿ φ | dup x; e ⟶ₕ H, x ↦ⁿ⁺¹ φ | e` -/
  | dup (H : Heap) (x : Var 0) (n : Nat) (o : HObj) (e : LExpr 0) :
      HHead sig ({HCell.bind x n o} + H) (.dup (.var x) e) ({HCell.bind x (n + 1) o} + H) e
  /-- (*drop_h*) `H, x ↦ⁿ⁺¹ φ | drop x; e ⟶ₕ H, x ↦ⁿ φ | e` for `n ≥ 1` -/
  | drop (H : Heap) (x : Var 0) (n : Nat) (o : HObj) (e : LExpr 0) :
      HHead sig ({HCell.bind x (n + 2) o} + H) (.drop (.var x) e)
        ({HCell.bind x (n + 1) o} + H) e
  /-- (*dcon_h*) `H, x ↦¹ C z̄ | drop x; e ⟶ₕ H | drop z̄; e` -/
  | dcon (H : Heap) (x : Var 0) (c : CName) (zs : List (LVal 0)) (e : LExpr 0) :
      HHead sig ({HCell.bind x 1 (.con c zs)} + H) (.drop (.var x) e) H (drops zs e)
  /-- (*dlam_h*) `H, x ↦¹ λ^z̄ x̄. e' | drop x; e ⟶ₕ H | drop z̄; e` -/
  | dlam (H : Heap) (x : Var 0) (zs : List (LVal 0)) (c k : Nat) (b : LExpr (c + k))
      (e : LExpr 0) :
      HHead sig ({HCell.bind x 1 (.clo zs c k b)} + H) (.drop (.var x) e) H (drops zs e)
  /-- (*dropru_h*) `H, x ↦ⁿ⁺¹ Cᵏ z̄ | dropru x; e ⟶ₕ H, x ↦ⁿ Cᵏ z̄, ⋄k | e` for `n ≥ 1`:
      the cell is shared, so a fresh reuse credit is allocated -/
  | dropru (H : Heap) (x : Var 0) (n : Nat) (c : CName) (zs : List (LVal 0)) (e : LExpr 0) :
      HHead sig ({HCell.bind x (n + 2) (.con c zs)} + H) (.dropru (.var x) zs.length e)
        ({HCell.bind x (n + 1) (.con c zs)} + {HCell.credit zs.length} + H) e
  /-- (*dconru_h*) `H, x ↦¹ Cᵏ z̄ | dropru x; e ⟶ₕ H, ⋄k | drop z̄; e`: the cell is
      unique and becomes a reuse credit -/
  | dconru (H : Heap) (x : Var 0) (c : CName) (zs : List (LVal 0)) (e : LExpr 0) :
      HHead sig ({HCell.bind x 1 (.con c zs)} + H) (.dropru (.var x) zs.length e)
        ({HCell.credit zs.length} + H) (drops zs e)
  /-- (*free_h*) `H, ⋄k | free k; e ⟶ₕ H | e` -/
  | free (H : Heap) (k : Nat) (e : LExpr 0) :
      HHead sig ({HCell.credit k} + H) (.free k e) H e
  /-- (*alloc_h*) `H | alloc k; e ⟶ₕ H, ⋄k | e` -/
  | alloc (H : Heap) (k : Nat) (e : LExpr 0) :
      HHead sig H (.alloc k e) ({HCell.credit k} + H) e

/-- Reductions of the heap semantics on values: allocation of constructors (reusing a
    credit) and of closures (*lam_h*). -/
inductive HValHead : Heap → LVal 0 → Heap → LVal 0 → Prop where
  | reuse (H : Heap) (c : CName) (as : LVals 0) (x : Nat) : as ≠ .nil →
      (∀ a ∈ as.toList, a.Atomic) → Var.loc x ∉ H.dom →
      HValHead ({HCell.credit as.length} + H) (.ctor c as)
        ({HCell.bind (.loc x) 1 (.con c as.toList)} + H) (.var (.loc x))
  | atom (H : Heap) (c : CName) (x : Nat) : Var.loc x ∉ H.dom →
      HValHead H (.ctor c .nil) ({HCell.bind (.loc x) 1 (.con c [])} + H) (.var (.loc x))
  /-- (*lam_h*) `H | λ^z̄ x̄. e ⟶ₕ H, x ↦¹ λ^z̄ x̄. e | x` -/
  | lam (H : Heap) (zs : LVals 0) (c k : Nat) (e : LExpr (c + k)) (x : Nat) :
      (∀ a ∈ zs.toList, a.Atomic) → Var.loc x ∉ H.dom →
      HValHead H (.lam zs c k e) ({HCell.bind (.loc x) 1 (.clo zs.toList c k e)} + H)
        (.var (.loc x))

/-- Value contexts: the components of a tuple and the arguments of a constructor are
    evaluated from left to right. -/
inductive LVCtx where
  | hole
  | ctor (c : CName) (done : List (LVal 0)) (V : LVCtx) (rest : List (LVal 0))

/-- Plug a value into a value context. -/
def LVCtx.plug : LVCtx → LVal 0 → LVal 0
  | .hole, v => v
  | .ctor c done V rest, v => .ctor c (LVals.ofList (done ++ V.plug v :: rest))

/-- The already evaluated arguments of a value context are atomic. -/
def LVCtx.Ok : LVCtx → Prop
  | .hole => True
  | .ctor _ done V _ => (∀ a ∈ done, a.Atomic) ∧ V.Ok

/-- The heap semantics `H | e ⟼ₕ H' | e'`. -/
inductive HStep (sig : LSig) : Heap → LExpr 0 → Heap → LExpr 0 → Prop where
  | head (E : LECtx) {H H' : Heap} {e e' : LExpr 0} :
      HHead sig H e H' e' → HStep sig H (E.plug e) H' (E.plug e')
  | val (E : LECtx) (done : List (LVal 0)) (V : LVCtx) (rest : List (LVal 0)) {H H' : Heap}
      {v v' : LVal 0} : (∀ a ∈ done, a.Atomic) → V.Ok → HValHead H v H' v' →
      HStep sig H (E.plug (.ret (LVals.ofList (done ++ V.plug v :: rest))))
        H' (E.plug (.ret (LVals.ofList (done ++ V.plug v' :: rest))))

/-- `⟼*ₕ`. -/
inductive HSteps (sig : LSig) : Heap → LExpr 0 → Heap → LExpr 0 → Prop where
  | refl (H : Heap) (e : LExpr 0) : HSteps sig H e H e
  | tail {H₁ H₂ H₃ : Heap} {e₁ e₂ e₃ : LExpr 0} :
      HSteps sig H₁ e₁ H₂ e₂ → HStep sig H₂ e₂ H₃ e₃ → HSteps sig H₁ e₁ H₃ e₃

/-! ## Basic properties -/

/-- Joining with the empty heap (Lemma 58, existence of a unit). -/
theorem HJoin.zero_left (H : Heap) : HJoin 0 H H := .nil H

/-- **Lemma 61** (dupping joins a root): a `dup` step adds a root. -/
theorem roots_dup (H : Heap) (x : Var 0) (n : Nat) (o : HObj) (hx : x ∉ o.fv)
    (hH : x ∉ H.rngFv) :
    Heap.roots ({HCell.bind x (n + 1) o} + H) =
      Heap.roots ({HCell.bind x n o} + H) + {Res.var x} := by
  classical
  have hr : ∀ m, Heap.rngFv ({HCell.bind x m o} + H) =
      (o.fv : Multiset (Var 0)) + H.rngFv := by
    intro m; simp [Heap.rngFv]
  have hc : (Heap.rngFv ({HCell.bind x n o} + H)).count x = 0 := by
    rw [hr]; simp [Multiset.count_eq_zero_of_notMem hH, List.count_eq_zero_of_not_mem hx]
  unfold Heap.roots
  rw [hr (n + 1), hr n, Multiset.add_bind, Multiset.add_bind, Multiset.singleton_bind,
    Multiset.singleton_bind]
  rw [hr] at hc
  dsimp only
  rw [hc, Nat.sub_zero, Nat.sub_zero, Multiset.replicate_succ, ← Multiset.singleton_add]
  abel

end FIP.Lam

/- ══════════════════ PAPER sec. 5, 5.1, 5.2, App. E.1 END: Reference Counting with Borrowing and Unboxing; Elaborating borrowing; Heap semantics; Properties of Heaps ══════════════════ -/
