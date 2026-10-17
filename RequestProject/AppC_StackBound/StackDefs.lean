module

public import RequestProject.AppC_StackBound.Stack
public import RequestProject.AppB_StoreSoundness.SubstFacts
public import RequestProject.AppB_StoreSoundness.Store

@[expose] public section

/-!
# Syntactic tools for the stack bound (Appendix C)

This file collects the syntactic notions used in the proof of the corrected Theorem 4
(`RequestProject/AppC_StackBound/StackBound.lean`):

* `Expr.sdepth`: the depth of an expression counting only the nodes that can become part of
  an evaluation context (values, `drop`, `free` and primitive operations count `0`).  It
  is bounded by the paper's depth `|e|` and, unlike `|e|`, it is unchanged by *every*
  substitution and is not increased by any step of the store semantics other than calls;
* `Expr.calls` and `Expr.fns`: the functions an expression calls directly, and the
  functions it mentions as values;
* `Expr.BP B e`: function values, and the free names `B`, occur in `e` only in *borrowed
  positions* (borrowed arguments of calls, heads of applications, scrutinees of borrowing
  matches, arguments of primitives).  This is what the FIP typing rules guarantee for the
  borrowed parameters of a function;
* `Expr.TailC P e`: every call to a function satisfying `P` is a tail call (the first-order
  tail contexts of Appendix C.2).
-/

namespace FIP

/-! ## The stack depth of an expression -/

mutual
/-- The depth of an expression, counting only nodes that can be part of an evaluation
    context. -/
def Expr.sdepth {n : Nat} : Expr n → Nat
  | .ret _ => 0
  | .app e1 e2 => 1 + max (Expr.sdepth e1) (Expr.sdepth e2)
  | .call _ e1 e2 => 1 + max (Expr.sdepth e1) (Expr.sdepth e2)
  | .letIn _ e1 e2 => 1 + max (Expr.sdepth e1) (Expr.sdepth e2)
  | .bmatch e bs => 1 + max (Expr.sdepth e) (Expr.sdepthB bs)
  | .dmatch e bs => 1 + max (Expr.sdepth e) (Expr.sdepthB bs)
  | .drop _ e => Expr.sdepth e
  | .free _ e => Expr.sdepth e
  | .prim _ _ => 0
/-- The maximal stack depth of the bodies of branches. -/
def Expr.sdepthB {n : Nat} : Branches n → Nat
  | .nil => 0
  | .cons _ _ e bs => max (Expr.sdepth e) (Expr.sdepthB bs)
end

mutual
theorem Expr.sdepth_le_depth {n : Nat} : ∀ e : Expr n, e.sdepth ≤ e.depth
  | .ret _ => Nat.zero_le _
  | .app e1 e2 => by
    have := Expr.sdepth_le_depth e1; have := Expr.sdepth_le_depth e2
    simp only [Expr.sdepth, Expr.depth]; omega
  | .call _ e1 e2 => by
    have := Expr.sdepth_le_depth e1; have := Expr.sdepth_le_depth e2
    simp only [Expr.sdepth, Expr.depth]; omega
  | .letIn _ e1 e2 => by
    have := Expr.sdepth_le_depth e1; have := Expr.sdepth_le_depth e2
    simp only [Expr.sdepth, Expr.depth]; omega
  | .bmatch e bs => by
    have := Expr.sdepth_le_depth e; have := Expr.sdepthB_le_depthB bs
    simp only [Expr.sdepth, Expr.depth]; omega
  | .dmatch e bs => by
    have := Expr.sdepth_le_depth e; have := Expr.sdepthB_le_depthB bs
    simp only [Expr.sdepth, Expr.depth]; omega
  | .drop _ e => by
    have := Expr.sdepth_le_depth e
    simp only [Expr.sdepth, Expr.depth]; omega
  | .free _ e => by
    have := Expr.sdepth_le_depth e
    simp only [Expr.sdepth, Expr.depth]; omega
  | .prim _ _ => Nat.zero_le _
theorem Expr.sdepthB_le_depthB {n : Nat} : ∀ bs : Branches n, Expr.sdepthB bs ≤ Branches.depth bs
  | .nil => le_refl _
  | .cons _ _ e bs => by
    have := Expr.sdepth_le_depth e; have := Expr.sdepthB_le_depthB bs
    simp only [Expr.sdepthB, Branches.depth]; omega
end

mutual
theorem Expr.sdepth_subst {n m : Nat} (σ : Fin n → Val m) : ∀ e : Expr n, (e.subst σ).sdepth = e.sdepth
  | .ret _ => rfl
  | .app e1 e2 => by
    simp only [Expr.subst, Expr.sdepth, Expr.sdepth_subst σ e1, Expr.sdepth_subst σ e2]
  | .call _ e1 e2 => by
    simp only [Expr.subst, Expr.sdepth, Expr.sdepth_subst σ e1, Expr.sdepth_subst σ e2]
  | .letIn xs e1 e2 => by
    simp only [Expr.subst, Expr.sdepth, Expr.sdepth_subst σ e1,
      Expr.sdepth_subst (Subst.up xs.length σ) e2]
  | .bmatch e bs => by
    simp only [Expr.subst, Expr.sdepth, Expr.sdepth_subst σ e, Expr.sdepthB_subst σ bs]
  | .dmatch e bs => by
    simp only [Expr.subst, Expr.sdepth, Expr.sdepth_subst σ e, Expr.sdepthB_subst σ bs]
  | .drop _ e => by simp only [Expr.subst, Expr.sdepth, Expr.sdepth_subst σ e]
  | .free _ e => by simp only [Expr.subst, Expr.sdepth, Expr.sdepth_subst σ e]
  | .prim _ _ => rfl
theorem Expr.sdepthB_subst {n m : Nat} (σ : Fin n → Val m) :
    ∀ bs : Branches n, Expr.sdepthB (Branches.subst σ bs) = Expr.sdepthB bs
  | .nil => rfl
  | .cons _ xs e bs => by
    simp only [Branches.subst, Expr.sdepthB, Expr.sdepth_subst (Subst.up xs.length σ) e,
      Expr.sdepthB_subst σ bs]
end

theorem Expr.sdepthB_mem {n : Nat} : ∀ {bs : Branches n} {b : Branch n}, b ∈ bs.toList →
    b.body.sdepth ≤ Expr.sdepthB bs
  | .nil, _, hb => by simp at hb
  | .cons c xs e bs, b, hb => by
    rw [Branches.toList_cons, List.mem_cons] at hb
    simp only [Expr.sdepthB]
    rcases hb with rfl | hb
    · exact le_max_left _ _
    · exact le_trans (Expr.sdepthB_mem hb) (le_max_right _ _)

theorem Expr.sdepth_drops (zs : List (Val 0)) (e : Expr 0) : (drops zs e).sdepth = e.sdepth := by
  induction zs with
  | nil => rfl
  | cons z zs ih => cases z <;> simp [drops, Expr.sdepth, ih]

/-- **Lemma 25** for the stack depth: `|E| + ψ(e) ≤ ψ(E[e])`. -/
theorem ECtx.depth_plug_sdepth {n : Nat} (E : ECtx n) (e : Expr n) :
    E.depth + e.sdepth ≤ (E.plug e).sdepth := by
  induction E with
  | hole => simp [ECtx.depth, ECtx.plug]
  | appL E e2 ih => simp only [ECtx.depth, ECtx.plug, Expr.sdepth]; omega
  | appR vs E ih => simp only [ECtx.depth, ECtx.plug, Expr.sdepth]; omega
  | callB f E e2 ih => simp only [ECtx.depth, ECtx.plug, Expr.sdepth]; omega
  | callO f vs E ih => simp only [ECtx.depth, ECtx.plug, Expr.sdepth]; omega
  | letIn xs E e2 ih => simp only [ECtx.depth, ECtx.plug, Expr.sdepth]; omega
  | bmatch E bs ih => simp only [ECtx.depth, ECtx.plug, Expr.sdepth]; omega
  | dmatch E bs ih => simp only [ECtx.depth, ECtx.plug, Expr.sdepth]; omega

/-- **Lemma 27** for the stack depth. -/
theorem ECtx.sdepth_plug_mono {n : Nat} (E : ECtx n) {e₁ e₂ : Expr n} (h : e₂.sdepth ≤ e₁.sdepth) :
    (E.plug e₂).sdepth ≤ (E.plug e₁).sdepth := by
  induction E with
  | hole => simpa [ECtx.plug] using h
  | appL E e2 ih => simp only [ECtx.plug, Expr.sdepth]; omega
  | appR vs E ih => simp only [ECtx.plug, Expr.sdepth]; omega
  | callB f E e2 ih => simp only [ECtx.plug, Expr.sdepth]; omega
  | callO f vs E ih => simp only [ECtx.plug, Expr.sdepth]; omega
  | letIn xs E e2 ih => simp only [ECtx.plug, Expr.sdepth]; omega
  | bmatch E bs ih => simp only [ECtx.plug, Expr.sdepth]; omega
  | dmatch E bs ih => simp only [ECtx.plug, Expr.sdepth]; omega

theorem ECtx.depth_comp {n : Nat} (E F : ECtx n) : (E.comp F).depth = E.depth + F.depth := by
  induction E with
  | hole => simp [ECtx.comp, ECtx.depth]
  | _ => simp only [ECtx.comp, ECtx.depth]; omega

/-! ## Called functions and function values -/

mutual
/-- The functions an expression calls directly. -/
def Expr.calls {n : Nat} : Expr n → List FName
  | .ret _ => []
  | .app e1 e2 => Expr.calls e1 ++ Expr.calls e2
  | .call f e1 e2 => f :: (Expr.calls e1 ++ Expr.calls e2)
  | .letIn _ e1 e2 => Expr.calls e1 ++ Expr.calls e2
  | .bmatch e bs => Expr.calls e ++ Expr.callsB bs
  | .dmatch e bs => Expr.calls e ++ Expr.callsB bs
  | .drop _ e => Expr.calls e
  | .free _ e => Expr.calls e
  | .prim _ _ => []
/-- The functions branches call directly. -/
def Expr.callsB {n : Nat} : Branches n → List FName
  | .nil => []
  | .cons _ _ e bs => Expr.calls e ++ Expr.callsB bs
end

mutual
/-- The functions an expression mentions as values (as in `Expr.funs`, but without the
    directly called functions). -/
def Expr.fns {n : Nat} : Expr n → List FName
  | .ret vs => Val.funsList vs
  | .app e1 e2 => Expr.fns e1 ++ Expr.fns e2
  | .call _ e1 e2 => Expr.fns e1 ++ Expr.fns e2
  | .letIn _ e1 e2 => Expr.fns e1 ++ Expr.fns e2
  | .bmatch e bs => Expr.fns e ++ Expr.fnsB bs
  | .dmatch e bs => Expr.fns e ++ Expr.fnsB bs
  | .drop _ e => Expr.fns e
  | .free _ e => Expr.fns e
  | .prim _ _ => []
/-- The functions branches mention as values. -/
def Expr.fnsB {n : Nat} : Branches n → List FName
  | .nil => []
  | .cons _ _ e bs => Expr.fns e ++ Expr.fnsB bs
end

mutual
theorem Expr.calls_subset_funs {n : Nat} : ∀ (e : Expr n), ∀ g ∈ e.calls, g ∈ e.funs
  | .ret _ => by simp [Expr.calls]
  | .app e1 e2 => by
    intro g hg
    simp only [Expr.calls, Expr.funs, List.mem_append] at hg ⊢
    rcases hg with h | h
    · exact .inl (Expr.calls_subset_funs e1 g h)
    · exact .inr (Expr.calls_subset_funs e2 g h)
  | .call f e1 e2 => by
    intro g hg
    simp only [Expr.calls, Expr.funs, List.mem_cons, List.mem_append] at hg ⊢
    rcases hg with h | h | h
    · exact .inl h
    · exact .inr (.inl (Expr.calls_subset_funs e1 g h))
    · exact .inr (.inr (Expr.calls_subset_funs e2 g h))
  | .letIn _ e1 e2 => by
    intro g hg
    simp only [Expr.calls, Expr.funs, List.mem_append] at hg ⊢
    rcases hg with h | h
    · exact .inl (Expr.calls_subset_funs e1 g h)
    · exact .inr (Expr.calls_subset_funs e2 g h)
  | .bmatch e bs => by
    intro g hg
    simp only [Expr.calls, Expr.funs, List.mem_append] at hg ⊢
    rcases hg with h | h
    · exact .inl (Expr.calls_subset_funs e g h)
    · exact .inr (Expr.callsB_subset_funsB bs g h)
  | .dmatch e bs => by
    intro g hg
    simp only [Expr.calls, Expr.funs, List.mem_append] at hg ⊢
    rcases hg with h | h
    · exact .inl (Expr.calls_subset_funs e g h)
    · exact .inr (Expr.callsB_subset_funsB bs g h)
  | .drop _ e => by
    intro g hg; simp only [Expr.calls, Expr.funs] at hg ⊢; exact Expr.calls_subset_funs e g hg
  | .free _ e => by
    intro g hg; simp only [Expr.calls, Expr.funs] at hg ⊢; exact Expr.calls_subset_funs e g hg
  | .prim _ _ => by simp [Expr.calls]
theorem Expr.callsB_subset_funsB {n : Nat} : ∀ (bs : Branches n), ∀ g ∈ Expr.callsB bs, g ∈ Branches.funs bs
  | .nil => by simp [Expr.callsB]
  | .cons _ _ e bs => by
    intro g hg
    simp only [Expr.callsB, Branches.funs, List.mem_append] at hg ⊢
    rcases hg with h | h
    · exact .inl (Expr.calls_subset_funs e g h)
    · exact .inr (Expr.callsB_subset_funsB bs g h)
end

mutual
theorem Expr.fns_subset_funs {n : Nat} : ∀ (e : Expr n), ∀ g ∈ e.fns, g ∈ e.funs
  | .ret _ => by intro g hg; simpa [Expr.fns, Expr.funs] using hg
  | .app e1 e2 => by
    intro g hg
    simp only [Expr.fns, Expr.funs, List.mem_append] at hg ⊢
    rcases hg with h | h
    · exact .inl (Expr.fns_subset_funs e1 g h)
    · exact .inr (Expr.fns_subset_funs e2 g h)
  | .call f e1 e2 => by
    intro g hg
    simp only [Expr.fns, Expr.funs, List.mem_cons, List.mem_append] at hg ⊢
    rcases hg with h | h
    · exact .inr (.inl (Expr.fns_subset_funs e1 g h))
    · exact .inr (.inr (Expr.fns_subset_funs e2 g h))
  | .letIn _ e1 e2 => by
    intro g hg
    simp only [Expr.fns, Expr.funs, List.mem_append] at hg ⊢
    rcases hg with h | h
    · exact .inl (Expr.fns_subset_funs e1 g h)
    · exact .inr (Expr.fns_subset_funs e2 g h)
  | .bmatch e bs => by
    intro g hg
    simp only [Expr.fns, Expr.funs, List.mem_append] at hg ⊢
    rcases hg with h | h
    · exact .inl (Expr.fns_subset_funs e g h)
    · exact .inr (Expr.fnsB_subset_funsB bs g h)
  | .dmatch e bs => by
    intro g hg
    simp only [Expr.fns, Expr.funs, List.mem_append] at hg ⊢
    rcases hg with h | h
    · exact .inl (Expr.fns_subset_funs e g h)
    · exact .inr (Expr.fnsB_subset_funsB bs g h)
  | .drop _ e => by
    intro g hg; simp only [Expr.fns, Expr.funs] at hg ⊢; exact Expr.fns_subset_funs e g hg
  | .free _ e => by
    intro g hg; simp only [Expr.fns, Expr.funs] at hg ⊢; exact Expr.fns_subset_funs e g hg
  | .prim _ _ => by simp [Expr.fns]
theorem Expr.fnsB_subset_funsB {n : Nat} : ∀ (bs : Branches n), ∀ g ∈ Expr.fnsB bs, g ∈ Branches.funs bs
  | .nil => by simp [Expr.fnsB]
  | .cons _ _ e bs => by
    intro g hg
    simp only [Expr.fnsB, Branches.funs, List.mem_append] at hg ⊢
    rcases hg with h | h
    · exact .inl (Expr.fns_subset_funs e g h)
    · exact .inr (Expr.fnsB_subset_funsB bs g h)
end

mutual
theorem Expr.calls_subst {n m : Nat} (σ : Fin n → Val m) : ∀ e : Expr n, (e.subst σ).calls = e.calls
  | .ret _ => rfl
  | .app e1 e2 => by
    simp only [Expr.subst, Expr.calls, Expr.calls_subst σ e1, Expr.calls_subst σ e2]
  | .call _ e1 e2 => by
    simp only [Expr.subst, Expr.calls, Expr.calls_subst σ e1, Expr.calls_subst σ e2]
  | .letIn xs e1 e2 => by
    simp only [Expr.subst, Expr.calls, Expr.calls_subst σ e1,
      Expr.calls_subst (Subst.up xs.length σ) e2]
  | .bmatch e bs => by
    simp only [Expr.subst, Expr.calls, Expr.calls_subst σ e, Expr.callsB_subst σ bs]
  | .dmatch e bs => by
    simp only [Expr.subst, Expr.calls, Expr.calls_subst σ e, Expr.callsB_subst σ bs]
  | .drop _ e => by simp only [Expr.subst, Expr.calls, Expr.calls_subst σ e]
  | .free _ e => by simp only [Expr.subst, Expr.calls, Expr.calls_subst σ e]
  | .prim _ _ => rfl
theorem Expr.callsB_subst {n m : Nat} (σ : Fin n → Val m) :
    ∀ bs : Branches n, Expr.callsB (Branches.subst σ bs) = Expr.callsB bs
  | .nil => rfl
  | .cons _ xs e bs => by
    simp only [Branches.subst, Expr.callsB, Expr.calls_subst (Subst.up xs.length σ) e,
      Expr.callsB_subst σ bs]
end

/-- The functions mentioned by the values of a substitution. -/
def Subst.fns {n m : Nat} (σ : Fin n → Val m) : List FName :=
  (List.finRange n).flatMap (fun i => Val.funs (σ i))

theorem Subst.mem_fns {n m : Nat} {σ : Fin n → Val m} {g : FName} :
    g ∈ Subst.fns σ ↔ ∃ i, g ∈ Val.funs (σ i) := by
  simp [Subst.fns]

mutual
theorem Val.funs_shift {n : Nat} (k : Nat) : ∀ v : Val n, Val.funs (v.shift k) = Val.funs v
  | .var (.bvar _) => rfl
  | .var (.loc _) => rfl
  | .fn _ => rfl
  | .lit _ => rfl
  | .ctor c vs => by
    have := Val.funsList_shift k vs
    simp only [Val.shift, Val.subst, Val.funs, Val.substList_eq_map] at this ⊢
    exact this
theorem Val.funsList_shift {n : Nat} (k : Nat) :
    ∀ vs : List (Val n), Val.funsList (vs.map (Val.shift k)) = Val.funsList vs
  | [] => rfl
  | v :: vs => by
    simp only [List.map_cons, Val.funsList, Val.funs_shift k v, Val.funsList_shift k vs]
end

theorem Subst.fns_up_subset {n m : Nat} (σ : Fin n → Val m) (k : Nat) :
    ∀ g ∈ Subst.fns (Subst.up k σ), g ∈ Subst.fns σ := by
  intro g hg
  obtain ⟨i, hi⟩ := Subst.mem_fns.mp hg
  simp only [Subst.up] at hi
  split at hi
  · simp [Val.funs] at hi
  · rw [Val.funs_shift] at hi
    exact Subst.mem_fns.mpr ⟨_, hi⟩

mutual
theorem Val.funs_subst {n m : Nat} (σ : Fin n → Val m) : ∀ v : Val n, ∀ g ∈ (v.subst σ).funs, g ∈ v.funs ∨ g ∈ Subst.fns σ
  | .var (.bvar i) => by
    intro g hg
    exact .inr (Subst.mem_fns.mpr ⟨i, hg⟩)
  | .var (.loc _) => by intro g hg; simp [Val.subst, Val.funs] at hg
  | .fn f => by intro g hg; exact .inl (by simpa [Val.subst] using hg)
  | .lit _ => by intro g hg; simp [Val.subst, Val.funs] at hg
  | .ctor c vs => by
    intro g hg
    simp only [Val.subst, Val.funs] at hg ⊢
    exact Val.funsList_subst σ vs g hg
theorem Val.funsList_subst {n m : Nat} (σ : Fin n → Val m) :
    ∀ vs : List (Val n), ∀ g ∈ Val.funsList (Val.substList σ vs), g ∈ Val.funsList vs ∨ g ∈ Subst.fns σ
  | [] => by simp [Val.substList, Val.funsList]
  | v :: vs => by
    intro g hg
    simp only [Val.substList, Val.funsList, List.mem_append] at hg ⊢
    rcases hg with h | h
    · rcases Val.funs_subst σ v g h with h | h
      · exact .inl (.inl h)
      · exact .inr h
    · rcases Val.funsList_subst σ vs g h with h | h
      · exact .inl (.inr h)
      · exact .inr h
end

mutual
theorem Expr.fns_subst {n m : Nat} (σ : Fin n → Val m) : ∀ e : Expr n, ∀ g ∈ (e.subst σ).fns, g ∈ e.fns ∨ g ∈ Subst.fns σ
  | .ret vs => by
    intro g hg
    simp only [Expr.subst, Expr.fns] at hg ⊢
    exact Val.funsList_subst σ vs g hg
  | .app e1 e2 => by
    intro g hg
    simp only [Expr.subst, Expr.fns, List.mem_append] at hg ⊢
    rcases hg with h | h
    · rcases Expr.fns_subst σ e1 g h with h | h
      · exact .inl (.inl h)
      · exact .inr h
    · rcases Expr.fns_subst σ e2 g h with h | h
      · exact .inl (.inr h)
      · exact .inr h
  | .call _ e1 e2 => by
    intro g hg
    simp only [Expr.subst, Expr.fns, List.mem_append] at hg ⊢
    rcases hg with h | h
    · rcases Expr.fns_subst σ e1 g h with h | h
      · exact .inl (.inl h)
      · exact .inr h
    · rcases Expr.fns_subst σ e2 g h with h | h
      · exact .inl (.inr h)
      · exact .inr h
  | .letIn xs e1 e2 => by
    intro g hg
    simp only [Expr.subst, Expr.fns, List.mem_append] at hg ⊢
    rcases hg with h | h
    · rcases Expr.fns_subst σ e1 g h with h | h
      · exact .inl (.inl h)
      · exact .inr h
    · rcases Expr.fns_subst (Subst.up xs.length σ) e2 g h with h | h
      · exact .inl (.inr h)
      · exact .inr (Subst.fns_up_subset σ _ g h)
  | .bmatch e bs => by
    intro g hg
    simp only [Expr.subst, Expr.fns, List.mem_append] at hg ⊢
    rcases hg with h | h
    · rcases Expr.fns_subst σ e g h with h | h
      · exact .inl (.inl h)
      · exact .inr h
    · rcases Expr.fnsB_subst σ bs g h with h | h
      · exact .inl (.inr h)
      · exact .inr h
  | .dmatch e bs => by
    intro g hg
    simp only [Expr.subst, Expr.fns, List.mem_append] at hg ⊢
    rcases hg with h | h
    · rcases Expr.fns_subst σ e g h with h | h
      · exact .inl (.inl h)
      · exact .inr h
    · rcases Expr.fnsB_subst σ bs g h with h | h
      · exact .inl (.inr h)
      · exact .inr h
  | .drop _ e => by
    intro g hg
    simp only [Expr.subst, Expr.fns] at hg ⊢
    exact Expr.fns_subst σ e g hg
  | .free _ e => by
    intro g hg
    simp only [Expr.subst, Expr.fns] at hg ⊢
    exact Expr.fns_subst σ e g hg
  | .prim _ _ => by intro g hg; simp [Expr.subst, Expr.fns] at hg
theorem Expr.fnsB_subst {n m : Nat} (σ : Fin n → Val m) :
    ∀ bs : Branches n, ∀ g ∈ Expr.fnsB (Branches.subst σ bs), g ∈ Expr.fnsB bs ∨ g ∈ Subst.fns σ
  | .nil => by simp [Branches.subst, Expr.fnsB]
  | .cons _ xs e bs => by
    intro g hg
    simp only [Branches.subst, Expr.fnsB, List.mem_append] at hg ⊢
    rcases hg with h | h
    · rcases Expr.fns_subst (Subst.up xs.length σ) e g h with h | h
      · exact .inl (.inl h)
      · exact .inr (Subst.fns_up_subset σ _ g h)
    · rcases Expr.fnsB_subst σ bs g h with h | h
      · exact .inl (.inr h)
      · exact .inr h
end

theorem Expr.calls_drops (zs : List (Val 0)) (e : Expr 0) : (drops zs e).calls = e.calls := by
  induction zs with
  | nil => rfl
  | cons z zs ih => cases z <;> simp [drops, Expr.calls, ih]

theorem Expr.fns_drops (zs : List (Val 0)) (e : Expr 0) : (drops zs e).fns = e.fns := by
  induction zs with
  | nil => rfl
  | cons z zs ih => cases z <;> simp [drops, Expr.fns, ih]

theorem Expr.mem_fnsB {n : Nat} {g : FName} : ∀ {bs : Branches n},
    g ∈ Expr.fnsB bs ↔ ∃ b ∈ bs.toList, g ∈ b.body.fns
  | .nil => by simp [Expr.fnsB]
  | .cons c xs e bs => by
    simp only [Expr.fnsB, List.mem_append, Expr.mem_fnsB (bs := bs), Branches.toList_cons,
      List.mem_cons, exists_eq_or_imp]

theorem Expr.mem_callsB {n : Nat} {g : FName} : ∀ {bs : Branches n},
    g ∈ Expr.callsB bs ↔ ∃ b ∈ bs.toList, g ∈ b.body.calls
  | .nil => by simp [Expr.callsB]
  | .cons c xs e bs => by
    simp only [Expr.callsB, List.mem_append, Expr.mem_callsB (bs := bs), Branches.toList_cons,
      List.mem_cons, exists_eq_or_imp]

theorem Expr.callsB_mem {n : Nat} {bs : Branches n} {b : Branch n} (hb : b ∈ bs.toList) :
    ∀ g ∈ b.body.calls, g ∈ Expr.callsB bs := fun _ hg => Expr.mem_callsB.mpr ⟨b, hb, hg⟩

theorem Expr.fnsB_mem {n : Nat} {bs : Branches n} {b : Branch n} (hb : b ∈ bs.toList) :
    ∀ g ∈ b.body.fns, g ∈ Expr.fnsB bs := fun _ hg => Expr.mem_fnsB.mpr ⟨b, hb, hg⟩

/-- The calls of `E[e₂]` are calls of `E[e₁]` or of `e₂`. -/
theorem ECtx.calls_plug {n : Nat} (E : ECtx n) (e₁ e₂ : Expr n) :
    ∀ g ∈ (E.plug e₂).calls, g ∈ (E.plug e₁).calls ∨ g ∈ e₂.calls := by
  induction E with
  | hole => intro g hg; exact .inr hg
  | appL E x ih =>
    intro g hg
    simp only [ECtx.plug, Expr.calls, List.mem_append] at hg ⊢
    rcases hg with h | h
    · rcases ih g h with h | h
      · exact .inl (.inl h)
      · exact .inr h
    · exact .inl (.inr h)
  | appR vs E ih =>
    intro g hg
    simp only [ECtx.plug, Expr.calls, List.mem_append] at hg ⊢
    rcases hg with h | h
    · exact .inl (.inl h)
    · rcases ih g h with h | h
      · exact .inl (.inr h)
      · exact .inr h
  | callB f E x ih =>
    intro g hg
    simp only [ECtx.plug, Expr.calls, List.mem_cons, List.mem_append] at hg ⊢
    rcases hg with h | h | h
    · exact .inl (.inl h)
    · rcases ih g h with h | h
      · exact .inl (.inr (.inl h))
      · exact .inr h
    · exact .inl (.inr (.inr h))
  | callO f vs E ih =>
    intro g hg
    simp only [ECtx.plug, Expr.calls, List.mem_cons, List.mem_append] at hg ⊢
    rcases hg with h | h | h
    · exact .inl (.inl h)
    · exact .inl (.inr (.inl h))
    · rcases ih g h with h | h
      · exact .inl (.inr (.inr h))
      · exact .inr h
  | letIn xs E x ih =>
    intro g hg
    simp only [ECtx.plug, Expr.calls, List.mem_append] at hg ⊢
    rcases hg with h | h
    · rcases ih g h with h | h
      · exact .inl (.inl h)
      · exact .inr h
    · exact .inl (.inr h)
  | bmatch E bs ih =>
    intro g hg
    simp only [ECtx.plug, Expr.calls, List.mem_append] at hg ⊢
    rcases hg with h | h
    · rcases ih g h with h | h
      · exact .inl (.inl h)
      · exact .inr h
    · exact .inl (.inr h)
  | dmatch E bs ih =>
    intro g hg
    simp only [ECtx.plug, Expr.calls, List.mem_append] at hg ⊢
    rcases hg with h | h
    · rcases ih g h with h | h
      · exact .inl (.inl h)
      · exact .inr h
    · exact .inl (.inr h)

/-- The calls of `e` are calls of `E[e]`. -/
theorem ECtx.calls_sub {n : Nat} (E : ECtx n) (e : Expr n) : ∀ g ∈ e.calls, g ∈ (E.plug e).calls := by
  induction E with
  | hole => exact fun g hg => hg
  | _ => intro g hg; simp_all [ECtx.plug, Expr.calls]

/-- The function values of `E[e₂]` are function values of `E[e₁]` or of `e₂`. -/
theorem ECtx.fns_plug {n : Nat} (E : ECtx n) (e₁ e₂ : Expr n) :
    ∀ g ∈ (E.plug e₂).fns, g ∈ (E.plug e₁).fns ∨ g ∈ e₂.fns := by
  induction E with
  | hole => intro g hg; exact .inr hg
  | appL E x ih =>
    intro g hg
    simp only [ECtx.plug, Expr.fns, List.mem_append] at hg ⊢
    rcases hg with h | h
    · rcases ih g h with h | h
      · exact .inl (.inl h)
      · exact .inr h
    · exact .inl (.inr h)
  | appR vs E ih =>
    intro g hg
    simp only [ECtx.plug, Expr.fns, List.mem_append] at hg ⊢
    rcases hg with h | h
    · exact .inl (.inl h)
    · rcases ih g h with h | h
      · exact .inl (.inr h)
      · exact .inr h
  | callB f E x ih =>
    intro g hg
    simp only [ECtx.plug, Expr.fns, List.mem_append] at hg ⊢
    rcases hg with h | h
    · rcases ih g h with h | h
      · exact .inl (.inl h)
      · exact .inr h
    · exact .inl (.inr h)
  | callO f vs E ih =>
    intro g hg
    simp only [ECtx.plug, Expr.fns, List.mem_append] at hg ⊢
    rcases hg with h | h
    · exact .inl (.inl h)
    · rcases ih g h with h | h
      · exact .inl (.inr h)
      · exact .inr h
  | letIn xs E x ih =>
    intro g hg
    simp only [ECtx.plug, Expr.fns, List.mem_append] at hg ⊢
    rcases hg with h | h
    · rcases ih g h with h | h
      · exact .inl (.inl h)
      · exact .inr h
    · exact .inl (.inr h)
  | bmatch E bs ih =>
    intro g hg
    simp only [ECtx.plug, Expr.fns, List.mem_append] at hg ⊢
    rcases hg with h | h
    · rcases ih g h with h | h
      · exact .inl (.inl h)
      · exact .inr h
    · exact .inl (.inr h)
  | dmatch E bs ih =>
    intro g hg
    simp only [ECtx.plug, Expr.fns, List.mem_append] at hg ⊢
    rcases hg with h | h
    · rcases ih g h with h | h
      · exact .inl (.inl h)
      · exact .inr h
    · exact .inl (.inr h)

/-- The function values of `e` are function values of `E[e]`. -/
theorem ECtx.fns_sub {n : Nat} (E : ECtx n) (e : Expr n) : ∀ g ∈ e.fns, g ∈ (E.plug e).fns := by
  induction E with
  | hole => exact fun g hg => hg
  | _ => intro g hg; simp_all [ECtx.plug, Expr.fns]

end FIP
