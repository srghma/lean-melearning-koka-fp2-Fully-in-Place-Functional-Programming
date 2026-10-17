module

public import RequestProject.Named.AppC_StackBound.Stack
public import RequestProject.Named.AppB_StoreSoundness.SubstFacts

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
  matches, arguments of primitives).  This is what the FIPNamed typing rules guarantee for the
  borrowed parameters of a function;
* `Expr.TailC P e`: every call to a function satisfying `P` is a tail call (the first-order
  tail contexts of Appendix C.2).
-/

namespace FIPNamed

/-! ## The stack depth of an expression -/

mutual
/-- The depth of an expression, counting only nodes that can be part of an evaluation
    context. -/
def Expr.sdepth : Expr → Nat
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
def Expr.sdepthB : List Branch → Nat
  | [] => 0
  | .mk _ _ e :: bs => max (Expr.sdepth e) (Expr.sdepthB bs)
end

mutual
theorem Expr.sdepth_le_depth : ∀ e : Expr, e.sdepth ≤ e.depth
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
theorem Expr.sdepthB_le_depthB : ∀ bs : List Branch, Expr.sdepthB bs ≤ Expr.depthB bs
  | [] => le_refl _
  | .mk _ _ e :: bs => by
    have := Expr.sdepth_le_depth e; have := Expr.sdepthB_le_depthB bs
    simp only [Expr.sdepthB, Expr.depthB]; omega
end

mutual
theorem Expr.sdepth_subst (σ : Subst) : ∀ e : Expr, (e.subst σ).sdepth = e.sdepth
  | .ret _ => rfl
  | .app e1 e2 => by
    simp only [Expr.subst, Expr.sdepth, Expr.sdepth_subst σ e1, Expr.sdepth_subst σ e2]
  | .call _ e1 e2 => by
    simp only [Expr.subst, Expr.sdepth, Expr.sdepth_subst σ e1, Expr.sdepth_subst σ e2]
  | .letIn xs e1 e2 => by
    simp only [Expr.subst, Expr.sdepth, Expr.sdepth_subst σ e1,
      Expr.sdepth_subst (σ.remove xs) e2]
  | .bmatch e bs => by
    simp only [Expr.subst, Expr.sdepth, Expr.sdepth_subst σ e, Expr.sdepthB_subst σ bs]
  | .dmatch e bs => by
    simp only [Expr.subst, Expr.sdepth, Expr.sdepth_subst σ e, Expr.sdepthB_subst σ bs]
  | .drop _ e => by simp only [Expr.subst, Expr.sdepth, Expr.sdepth_subst σ e]
  | .free _ e => by simp only [Expr.subst, Expr.sdepth, Expr.sdepth_subst σ e]
  | .prim _ _ => rfl
theorem Expr.sdepthB_subst (σ : Subst) :
    ∀ bs : List Branch, Expr.sdepthB (Expr.substBranches σ bs) = Expr.sdepthB bs
  | [] => rfl
  | .mk _ xs e :: bs => by
    simp only [Expr.substBranches, Expr.sdepthB, Expr.sdepth_subst (σ.remove xs) e,
      Expr.sdepthB_subst σ bs]
end

theorem Expr.sdepthB_mem {bs : List Branch} {b : Branch} (hb : b ∈ bs) :
    b.body.sdepth ≤ Expr.sdepthB bs := by
  induction bs with
  | nil => simp at hb
  | cons b' bs ih =>
    obtain ⟨c, xs, e⟩ := b'
    simp only [Expr.sdepthB]
    rcases List.mem_cons.mp hb with rfl | hb
    · simp [Branch.body]
    · exact le_trans (ih hb) (le_max_right _ _)

theorem Expr.sdepth_drops (zs : List Val) (e : Expr) : (drops zs e).sdepth = e.sdepth := by
  induction zs with
  | nil => rfl
  | cons z zs ih => cases z <;> simp [drops, Expr.sdepth, ih]

/-- **Lemma 25** for the stack depth: `|E| + ψ(e) ≤ ψ(E[e])`. -/
theorem ECtx.depth_plug_sdepth (E : ECtx) (e : Expr) :
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
theorem ECtx.sdepth_plug_mono (E : ECtx) {e₁ e₂ : Expr} (h : e₂.sdepth ≤ e₁.sdepth) :
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

theorem ECtx.depth_comp (E F : ECtx) : (E.comp F).depth = E.depth + F.depth := by
  induction E with
  | hole => simp [ECtx.comp, ECtx.depth]
  | _ => simp only [ECtx.comp, ECtx.depth]; omega

/-! ## Called functions and function values -/

mutual
/-- The functions an expression calls directly. -/
def Expr.calls : Expr → List FName
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
def Expr.callsB : List Branch → List FName
  | [] => []
  | .mk _ _ e :: bs => Expr.calls e ++ Expr.callsB bs
end

mutual
/-- The functions an expression mentions as values (as in `Expr.funs`, but without the
    directly called functions). -/
def Expr.fns : Expr → List FName
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
def Expr.fnsB : List Branch → List FName
  | [] => []
  | .mk _ _ e :: bs => Expr.fns e ++ Expr.fnsB bs
end

mutual
theorem Expr.calls_subset_funs : ∀ (e : Expr), ∀ g ∈ e.calls, g ∈ e.funs
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
theorem Expr.callsB_subset_funsB : ∀ (bs : List Branch), ∀ g ∈ Expr.callsB bs, g ∈ Expr.funsB bs
  | [] => by simp [Expr.callsB]
  | .mk _ _ e :: bs => by
    intro g hg
    simp only [Expr.callsB, Expr.funsB, List.mem_append] at hg ⊢
    rcases hg with h | h
    · exact .inl (Expr.calls_subset_funs e g h)
    · exact .inr (Expr.callsB_subset_funsB bs g h)
end

mutual
theorem Expr.fns_subset_funs : ∀ (e : Expr), ∀ g ∈ e.fns, g ∈ e.funs
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
theorem Expr.fnsB_subset_funsB : ∀ (bs : List Branch), ∀ g ∈ Expr.fnsB bs, g ∈ Expr.funsB bs
  | [] => by simp [Expr.fnsB]
  | .mk _ _ e :: bs => by
    intro g hg
    simp only [Expr.fnsB, Expr.funsB, List.mem_append] at hg ⊢
    rcases hg with h | h
    · exact .inl (Expr.fns_subset_funs e g h)
    · exact .inr (Expr.fnsB_subset_funsB bs g h)
end

mutual
theorem Expr.calls_subst (σ : Subst) : ∀ e : Expr, (e.subst σ).calls = e.calls
  | .ret _ => rfl
  | .app e1 e2 => by
    simp only [Expr.subst, Expr.calls, Expr.calls_subst σ e1, Expr.calls_subst σ e2]
  | .call _ e1 e2 => by
    simp only [Expr.subst, Expr.calls, Expr.calls_subst σ e1, Expr.calls_subst σ e2]
  | .letIn xs e1 e2 => by
    simp only [Expr.subst, Expr.calls, Expr.calls_subst σ e1,
      Expr.calls_subst (σ.remove xs) e2]
  | .bmatch e bs => by
    simp only [Expr.subst, Expr.calls, Expr.calls_subst σ e, Expr.callsB_subst σ bs]
  | .dmatch e bs => by
    simp only [Expr.subst, Expr.calls, Expr.calls_subst σ e, Expr.callsB_subst σ bs]
  | .drop _ e => by simp only [Expr.subst, Expr.calls, Expr.calls_subst σ e]
  | .free _ e => by simp only [Expr.subst, Expr.calls, Expr.calls_subst σ e]
  | .prim _ _ => rfl
theorem Expr.callsB_subst (σ : Subst) :
    ∀ bs : List Branch, Expr.callsB (Expr.substBranches σ bs) = Expr.callsB bs
  | [] => rfl
  | .mk _ xs e :: bs => by
    simp only [Expr.substBranches, Expr.callsB, Expr.calls_subst (σ.remove xs) e,
      Expr.callsB_subst σ bs]
end

/-- The functions mentioned by the values of a substitution. -/
def Subst.fns (σ : Subst) : List FName := σ.flatMap (fun p => Val.funs p.2)

theorem Subst.fns_remove_subset (σ : Subst) (xs : List Binder) :
    ∀ g ∈ (σ.remove xs).fns, g ∈ σ.fns := by
  intro g hg
  simp only [Subst.fns, List.mem_flatMap] at hg ⊢
  obtain ⟨p, hp, hg⟩ := hg
  exact ⟨p, List.mem_of_mem_filter hp, hg⟩

theorem Subst.mem_of_lookup {σ : Subst} {s : String} {v : Val} (h : σ.lookup s = some v) :
    (s, v) ∈ σ := by
  induction σ with
  | nil => simp at h
  | cons p σ ih =>
    obtain ⟨a, b⟩ := p
    simp only [List.lookup_cons] at h
    split at h
    · rename_i hab; cases h; simp only [beq_iff_eq] at hab; subst hab; simp
    · exact List.mem_cons_of_mem _ (ih h)

mutual
theorem Val.funs_subst (σ : Subst) : ∀ v : Val, ∀ g ∈ (v.subst σ).funs, g ∈ v.funs ∨ g ∈ σ.fns
  | .var (.name s) => by
    intro g hg
    simp only [Val.subst] at hg
    cases h : σ.lookup s with
    | none => rw [h] at hg; simp [Val.funs] at hg
    | some w =>
      rw [h] at hg
      refine .inr ?_
      simp only [Subst.fns, List.mem_flatMap]
      exact ⟨(s, w), Subst.mem_of_lookup h, by simpa using hg⟩
  | .var (.loc _) => by intro g hg; simp [Val.subst, Val.funs] at hg
  | .fn f => by intro g hg; exact .inl (by simpa [Val.subst] using hg)
  | .lit _ => by intro g hg; simp [Val.subst, Val.funs] at hg
  | .ctor c vs => by
    intro g hg
    simp only [Val.subst, Val.funs] at hg ⊢
    exact Val.funsList_subst σ vs g hg
theorem Val.funsList_subst (σ : Subst) :
    ∀ vs : List Val, ∀ g ∈ Val.funsList (Val.substList σ vs), g ∈ Val.funsList vs ∨ g ∈ σ.fns
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
theorem Expr.fns_subst (σ : Subst) : ∀ e : Expr, ∀ g ∈ (e.subst σ).fns, g ∈ e.fns ∨ g ∈ σ.fns
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
    · rcases Expr.fns_subst (σ.remove xs) e2 g h with h | h
      · exact .inl (.inr h)
      · exact .inr (Subst.fns_remove_subset σ xs g h)
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
theorem Expr.fnsB_subst (σ : Subst) :
    ∀ bs : List Branch, ∀ g ∈ Expr.fnsB (Expr.substBranches σ bs), g ∈ Expr.fnsB bs ∨ g ∈ σ.fns
  | [] => by simp [Expr.substBranches, Expr.fnsB]
  | .mk _ xs e :: bs => by
    intro g hg
    simp only [Expr.substBranches, Expr.fnsB, List.mem_append] at hg ⊢
    rcases hg with h | h
    · rcases Expr.fns_subst (σ.remove xs) e g h with h | h
      · exact .inl (.inl h)
      · exact .inr (Subst.fns_remove_subset σ xs g h)
    · rcases Expr.fnsB_subst σ bs g h with h | h
      · exact .inl (.inr h)
      · exact .inr h
end

theorem Expr.calls_drops (zs : List Val) (e : Expr) : (drops zs e).calls = e.calls := by
  induction zs with
  | nil => rfl
  | cons z zs ih => cases z <;> simp [drops, Expr.calls, ih]

theorem Expr.fns_drops (zs : List Val) (e : Expr) : (drops zs e).fns = e.fns := by
  induction zs with
  | nil => rfl
  | cons z zs ih => cases z <;> simp [drops, Expr.fns, ih]

theorem Expr.callsB_mem {bs : List Branch} {b : Branch} (hb : b ∈ bs) :
    ∀ g ∈ b.body.calls, g ∈ Expr.callsB bs := by
  induction bs with
  | nil => simp at hb
  | cons b' bs ih =>
    obtain ⟨c, xs, e⟩ := b'
    intro g hg
    simp only [Expr.callsB, List.mem_append]
    rcases List.mem_cons.mp hb with rfl | hb
    · exact .inl (by simpa [Branch.body] using hg)
    · exact .inr (ih hb g hg)

theorem Expr.fnsB_mem {bs : List Branch} {b : Branch} (hb : b ∈ bs) :
    ∀ g ∈ b.body.fns, g ∈ Expr.fnsB bs := by
  induction bs with
  | nil => simp at hb
  | cons b' bs ih =>
    obtain ⟨c, xs, e⟩ := b'
    intro g hg
    simp only [Expr.fnsB, List.mem_append]
    rcases List.mem_cons.mp hb with rfl | hb
    · exact .inl (by simpa [Branch.body] using hg)
    · exact .inr (ih hb g hg)

/-- The calls of `E[e₂]` are calls of `E[e₁]` or of `e₂`. -/
theorem ECtx.calls_plug (E : ECtx) (e₁ e₂ : Expr) :
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
theorem ECtx.calls_sub (E : ECtx) (e : Expr) : ∀ g ∈ e.calls, g ∈ (E.plug e).calls := by
  induction E with
  | hole => exact fun g hg => hg
  | _ => intro g hg; simp_all [ECtx.plug, Expr.calls]

/-- The function values of `E[e₂]` are function values of `E[e₁]` or of `e₂`. -/
theorem ECtx.fns_plug (E : ECtx) (e₁ e₂ : Expr) :
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
theorem ECtx.fns_sub (E : ECtx) (e : Expr) : ∀ g ∈ e.fns, g ∈ (E.plug e).fns := by
  induction E with
  | hole => exact fun g hg => hg
  | _ => intro g hg; simp_all [ECtx.plug, Expr.fns]

theorem Expr.mem_fnsB {g : FName} {bs : List Branch} :
    g ∈ Expr.fnsB bs ↔ ∃ b ∈ bs, g ∈ b.body.fns := by
  induction bs with
  | nil => simp [Expr.fnsB]
  | cons b bs ih =>
    obtain ⟨c, xs, e⟩ := b
    simp [Expr.fnsB, ih, Branch.body]

theorem Expr.mem_callsB {g : FName} {bs : List Branch} :
    g ∈ Expr.callsB bs ↔ ∃ b ∈ bs, g ∈ b.body.calls := by
  induction bs with
  | nil => simp [Expr.callsB]
  | cons b bs ih =>
    obtain ⟨c, xs, e⟩ := b
    simp [Expr.callsB, ih, Branch.body]

end FIPNamed
