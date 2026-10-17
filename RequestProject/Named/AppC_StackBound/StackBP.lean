module

public import RequestProject.Named.AppC_StackBound.StackDefs

@[expose] public section

/-!
# Borrowed positions and first-order tail contexts (Appendix C)

* `Expr.BP B e`: function values and the free names `B` occur in `e` only in borrowed
  positions.  The FIPNamed typing rules guarantee `Expr.BP ȳ e` for the body `e` of a function
  `f(ȳ; x̄) = e` (`Wf.bp`): borrowed parameters are only passed as borrowed arguments,
  applied, matched on or compared.  Consequently a function passed as an argument is never
  returned, stored in a constructor or passed as an owned argument.
* `Expr.TailC P e`: every call to a function satisfying `P` is in tail position.
-/

namespace FIPNamed

/-! ## Borrowed positions -/

/-- `v` mentions no top-level function and none of the names `B`. -/
def Val.NoB (B : List String) (v : Val) : Prop :=
  Val.funs v = [] ∧ ∀ s ∈ B, Var.name s ∉ v.fv

/-- A tuple of atomic values (the borrowed arguments of a call). -/
def Expr.AtomArgs : Expr → Prop
  | .ret ys => ∀ y ∈ ys, y.Atomic
  | _ => False

/-- A single atomic value (the head of an application, the scrutinee of a match). -/
def Expr.AtomArg : Expr → Prop
  | .ret [a] => a.Atomic
  | _ => False

/-- The names `B` without those bound by `xs`. -/
def hideNames (B : List String) (xs : List Binder) : List String :=
  B.filter (fun s => !(xs.map (·.name)).contains s)

mutual
/-- Function values, and the free names `B`, occur in `e` only in borrowed positions:
    borrowed arguments of calls, heads of applications, scrutinees of borrowing matches
    and arguments of primitive operations. -/
def Expr.BP (B : List String) : Expr → Prop
  | .ret vs => ∀ v ∈ vs, Val.NoB B v
  | .app e1 e2 => (e1.AtomArg ∨ Expr.BP B e1) ∧ Expr.BP B e2
  | .call _ e1 e2 => (e1.AtomArgs ∨ Expr.BP B e1) ∧ Expr.BP B e2
  | .letIn xs e1 e2 => Expr.BP B e1 ∧ Expr.BP (hideNames B xs) e2
  | .bmatch e bs => (e.AtomArg ∨ Expr.BP B e) ∧ Expr.BPB B bs
  | .dmatch e bs => Expr.BP B e ∧ Expr.BPB B bs
  | .drop x e => Val.NoB B x ∧ Expr.BP B e
  | .free _ e => Expr.BP B e
  | .prim _ _ => True
/-- `Expr.BP` for the bodies of branches. -/
def Expr.BPB (B : List String) : List Branch → Prop
  | [] => True
  | .mk _ xs e :: bs => Expr.BP (hideNames B xs) e ∧ Expr.BPB B bs
end

theorem Expr.BPB_iff {B : List String} {bs : List Branch} :
    Expr.BPB B bs ↔ ∀ b ∈ bs, Expr.BP (hideNames B b.binders) b.body := by
  induction bs with
  | nil => simp [Expr.BPB]
  | cons b bs ih =>
    obtain ⟨c, xs, e⟩ := b
    simp [Expr.BPB, ih, Branch.binders, Branch.body]

theorem hideNames_nil (xs : List Binder) : hideNames [] xs = [] := rfl

theorem Val.funsList_eq_nil {vs : List Val} : Val.funsList vs = [] ↔ ∀ v ∈ vs, Val.funs v = [] := by
  induction vs with
  | nil => simp [Val.funsList]
  | cons v vs ih => simp [Val.funsList, ih]

theorem Val.atomic_subst {σ : Subst} (hσ : ∀ p ∈ σ, p.2.Atomic) :
    ∀ {v : Val}, v.Atomic → (v.subst σ).Atomic
  | .var (.name s), _ => by
    simp only [Val.subst]
    cases hl : σ.lookup s with
    | none => trivial
    | some w => exact hσ _ (Subst.mem_of_lookup hl)
  | .var (.loc _), _ => trivial
  | .fn _, _ => trivial
  | .lit _, _ => trivial

theorem Expr.atomArg_subst {σ : Subst} (hσ : ∀ p ∈ σ, p.2.Atomic) {e : Expr}
    (h : e.AtomArg) : (e.subst σ).AtomArg := by
  cases e with
  | ret vs =>
    match vs, h with
    | [a], h =>
      simp only [Expr.subst, Val.substList_eq_map, List.map_cons, List.map_nil, Expr.AtomArg]
      exact Val.atomic_subst hσ h
  | _ => simp [Expr.AtomArg] at h

theorem Expr.atomArgs_subst {σ : Subst} (hσ : ∀ p ∈ σ, p.2.Atomic) {e : Expr}
    (h : e.AtomArgs) : (e.subst σ).AtomArgs := by
  cases e with
  | ret vs =>
    simp only [Expr.subst, Val.substList_eq_map, Expr.AtomArgs, List.mem_map] at h ⊢
    rintro _ ⟨y, hy, rfl⟩
    exact Val.atomic_subst hσ (h y hy)
  | _ => simp [Expr.AtomArgs] at h

mutual
theorem Val.funs_subst_noB {B : List String} {σ : Subst}
    (hσ : ∀ p ∈ σ, p.1 ∉ B → Val.funs p.2 = []) :
    ∀ v : Val, Val.NoB B v → Val.funs (v.subst σ) = []
  | .var (.name s), h => by
    simp only [Val.subst]
    cases hl : σ.lookup s with
    | none => simp [Val.funs]
    | some w =>
      simp only [Option.getD_some]
      exact hσ _ (Subst.mem_of_lookup hl) (fun hs => h.2 s hs (by simp [Val.fv]))
  | .var (.loc _), _ => rfl
  | .fn f, h => by simp [Val.NoB, Val.funs] at h
  | .lit _, _ => rfl
  | .ctor c vs, h => by
    simp only [Val.subst, Val.funs]
    exact Val.funsList_subst_noB hσ vs h.1 (fun s hs => by simpa [Val.fv] using h.2 s hs)
theorem Val.funsList_subst_noB {B : List String} {σ : Subst}
    (hσ : ∀ p ∈ σ, p.1 ∉ B → Val.funs p.2 = []) :
    ∀ vs : List Val, Val.funsList vs = [] → (∀ s ∈ B, Var.name s ∉ Val.fvList vs) →
      Val.funsList (Val.substList σ vs) = []
  | [], _, _ => rfl
  | v :: vs, h1, h2 => by
    simp only [Val.funsList, List.append_eq_nil_iff, Val.fvList, List.mem_append, not_or]
      at h1 h2
    simp only [Val.substList, Val.funsList, List.append_eq_nil_iff]
    exact ⟨Val.funs_subst_noB hσ v ⟨h1.1, fun s hs => (h2 s hs).1⟩,
      Val.funsList_subst_noB hσ vs h1.2 (fun s hs => (h2 s hs).2)⟩
end

theorem Subst.remove_cond {B : List String} {σ : Subst} (xs : List Binder)
    (hσ : ∀ p ∈ σ, p.1 ∉ B → Val.funs p.2 = []) :
    ∀ p ∈ σ.remove xs, p.1 ∉ hideNames B xs → Val.funs p.2 = [] := by
  intro p hp hn
  have hp' := List.mem_of_mem_filter hp
  have hx : (!(xs.map (·.name)).contains p.1) = true := (List.mem_filter.mp hp).2
  refine hσ p hp' (fun hB => hn ?_)
  exact List.mem_filter.mpr ⟨hB, hx⟩

theorem Subst.remove_atomic {σ : Subst} (xs : List Binder) (hσ : ∀ p ∈ σ, p.2.Atomic) :
    ∀ p ∈ σ.remove xs, p.2.Atomic := fun p hp => hσ p (List.mem_of_mem_filter hp)

mutual
/-- Substituting atomic values, where values for names outside `B` mention no functions,
    into an expression with `BP B` yields an expression with `BP []`. -/
theorem Expr.bp_subst : ∀ (e : Expr) (B : List String) (σ : Subst), (∀ p ∈ σ, p.2.Atomic) →
    (∀ p ∈ σ, p.1 ∉ B → Val.funs p.2 = []) → Expr.BP B e → Expr.BP [] (e.subst σ)
  | .ret vs, B, σ, _, hσ, h => by
    simp only [Expr.subst, Val.substList_eq_map, Expr.BP, List.mem_map]
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨Val.funs_subst_noB hσ v (h v hv), by simp⟩
  | .app e1 e2, B, σ, ha, hσ, h => by
    simp only [Expr.subst, Expr.BP] at h ⊢
    refine ⟨?_, Expr.bp_subst e2 B σ ha hσ h.2⟩
    rcases h.1 with h1 | h1
    · exact .inl (Expr.atomArg_subst ha h1)
    · exact .inr (Expr.bp_subst e1 B σ ha hσ h1)
  | .call _ e1 e2, B, σ, ha, hσ, h => by
    simp only [Expr.subst, Expr.BP] at h ⊢
    refine ⟨?_, Expr.bp_subst e2 B σ ha hσ h.2⟩
    rcases h.1 with h1 | h1
    · exact .inl (Expr.atomArgs_subst ha h1)
    · exact .inr (Expr.bp_subst e1 B σ ha hσ h1)
  | .letIn xs e1 e2, B, σ, ha, hσ, h => by
    simp only [Expr.subst, Expr.BP] at h ⊢
    exact ⟨Expr.bp_subst e1 B σ ha hσ h.1,
      Expr.bp_subst e2 (hideNames B xs) (σ.remove xs) (Subst.remove_atomic xs ha)
        (Subst.remove_cond xs hσ) h.2⟩
  | .bmatch e bs, B, σ, ha, hσ, h => by
    simp only [Expr.subst, Expr.BP] at h ⊢
    refine ⟨?_, Expr.bpB_subst bs B σ ha hσ h.2⟩
    rcases h.1 with h1 | h1
    · exact .inl (Expr.atomArg_subst ha h1)
    · exact .inr (Expr.bp_subst e B σ ha hσ h1)
  | .dmatch e bs, B, σ, ha, hσ, h => by
    simp only [Expr.subst, Expr.BP] at h ⊢
    exact ⟨Expr.bp_subst e B σ ha hσ h.1, Expr.bpB_subst bs B σ ha hσ h.2⟩
  | .drop x e, B, σ, ha, hσ, h => by
    simp only [Expr.subst, Expr.BP] at h ⊢
    exact ⟨⟨Val.funs_subst_noB hσ x h.1, by simp⟩, Expr.bp_subst e B σ ha hσ h.2⟩
  | .free _ e, B, σ, ha, hσ, h => by
    simp only [Expr.subst, Expr.BP] at h ⊢
    exact Expr.bp_subst e B σ ha hσ h
  | .prim _ _, _, _, _, _, _ => trivial
theorem Expr.bpB_subst : ∀ (bs : List Branch) (B : List String) (σ : Subst),
    (∀ p ∈ σ, p.2.Atomic) → (∀ p ∈ σ, p.1 ∉ B → Val.funs p.2 = []) →
    Expr.BPB B bs → Expr.BPB [] (Expr.substBranches σ bs)
  | [], _, _, _, _, _ => trivial
  | .mk _ xs e :: bs, B, σ, ha, hσ, h => by
    simp only [Expr.substBranches, Expr.BPB] at h ⊢
    exact ⟨Expr.bp_subst e (hideNames B xs) (σ.remove xs) (Subst.remove_atomic xs ha)
        (Subst.remove_cond xs hσ) h.1, Expr.bpB_subst bs B σ ha hσ h.2⟩
end

theorem Expr.bp_drops {B : List String} (zs : List Val) (hz : ∀ z ∈ zs, Val.NoB B z)
    {e : Expr} (h : Expr.BP B e) : Expr.BP B (drops zs e) := by
  induction zs with
  | nil => exact h
  | cons z zs ih =>
    have ih' := ih (fun z' hz' => hz z' (List.mem_cons_of_mem _ hz'))
    cases z with
    | var x => exact ⟨hz _ List.mem_cons_self, ih'⟩
    | _ => exact ih'

theorem Expr.atomArg_plug {E : ECtx} {r : Expr} (h : (E.plug r).AtomArg) : E = .hole := by
  cases E with
  | hole => rfl
  | _ => simp [ECtx.plug, Expr.AtomArg] at h

theorem Expr.atomArgs_plug {E : ECtx} {r : Expr} (h : (E.plug r).AtomArgs) : E = .hole := by
  cases E with
  | hole => rfl
  | _ => simp [ECtx.plug, Expr.AtomArgs] at h

theorem Expr.atomArgs_of_atomArg {e : Expr} (h : e.AtomArg) : e.AtomArgs := by
  cases e with
  | ret vs =>
    match vs, h with
    | [a], h => simpa [Expr.AtomArgs] using h
  | _ => simp [Expr.AtomArg] at h

/-- The subterm in the hole of an evaluation context is in a borrowed position only if it
    is a tuple of atomic values. -/
theorem ECtx.bp_plug_inv {B : List String} (E : ECtx) (r : Expr) (h : Expr.BP B (E.plug r)) :
    Expr.BP B r ∨ r.AtomArgs := by
  induction E with
  | hole => exact .inl h
  | appL E x ih =>
    simp only [ECtx.plug, Expr.BP] at h
    rcases h.1 with h1 | h1
    · have := Expr.atomArg_plug h1; subst this
      exact .inr (Expr.atomArgs_of_atomArg h1)
    · exact ih h1
  | appR vs E ih => simp only [ECtx.plug, Expr.BP] at h; exact ih h.2
  | callB f E x ih =>
    simp only [ECtx.plug, Expr.BP] at h
    rcases h.1 with h1 | h1
    · have := Expr.atomArgs_plug h1; subst this
      exact .inr h1
    · exact ih h1
  | callO f vs E ih => simp only [ECtx.plug, Expr.BP] at h; exact ih h.2
  | letIn xs E x ih => simp only [ECtx.plug, Expr.BP] at h; exact ih h.1
  | bmatch E bs ih =>
    simp only [ECtx.plug, Expr.BP] at h
    rcases h.1 with h1 | h1
    · have := Expr.atomArg_plug h1; subst this
      exact .inr (Expr.atomArgs_of_atomArg h1)
    · exact ih h1
  | dmatch E bs ih => simp only [ECtx.plug, Expr.BP] at h; exact ih h.1

/-- Replacing the subterm in the hole by one with `BP`. -/
theorem ECtx.bp_plug_repl {B : List String} (E : ECtx) (r r2 : Expr)
    (h : Expr.BP B (E.plug r)) (h2 : Expr.BP B r2) : Expr.BP B (E.plug r2) := by
  induction E with
  | hole => exact h2
  | appL E x ih =>
    simp only [ECtx.plug, Expr.BP] at h ⊢
    rcases h.1 with h1 | h1
    · have := Expr.atomArg_plug h1; subst this
      exact ⟨.inr h2, h.2⟩
    · exact ⟨.inr (ih h1), h.2⟩
  | appR vs E ih =>
    simp only [ECtx.plug, Expr.BP] at h ⊢; exact ⟨h.1, ih h.2⟩
  | callB f E x ih =>
    simp only [ECtx.plug, Expr.BP] at h ⊢
    rcases h.1 with h1 | h1
    · have := Expr.atomArgs_plug h1; subst this
      exact ⟨.inr h2, h.2⟩
    · exact ⟨.inr (ih h1), h.2⟩
  | callO f vs E ih =>
    simp only [ECtx.plug, Expr.BP] at h ⊢; exact ⟨h.1, ih h.2⟩
  | letIn xs E x ih =>
    simp only [ECtx.plug, Expr.BP] at h ⊢; exact ⟨ih h.1, h.2⟩
  | bmatch E bs ih =>
    simp only [ECtx.plug, Expr.BP] at h ⊢
    rcases h.1 with h1 | h1
    · have := Expr.atomArg_plug h1; subst this
      exact ⟨.inr h2, h.2⟩
    · exact ⟨.inr (ih h1), h.2⟩
  | dmatch E bs ih =>
    simp only [ECtx.plug, Expr.BP] at h ⊢; exact ⟨ih h.1, h.2⟩

/-! ## Borrowed positions follow from the FIPNamed typing rules -/

mutual
theorem WfVal.noFn {U Δ : Finset Var} :
    ∀ {Γ : Ctx} {v : Val}, WfVal U Δ Γ v →
      Val.funs v = [] ∧ ∀ x ∈ Val.fv v, x ∈ U ∨ Res.var x ∈ Γ
  | _, _, .var y => ⟨rfl, by simp [Val.fv]⟩
  | _, _, .svar y hy => ⟨rfl, by simp [Val.fv, hy]⟩
  | _, _, .atom _ => ⟨rfl, by simp [Val.fv, Val.fvList]⟩
  | _, _, .lit _ => ⟨rfl, by simp [Val.fv]⟩
  | _, _, .reuse c vs Γ _ hvs => by
    have h := WfVals.noFn hvs
    refine ⟨?_, ?_⟩
    · simp only [Val.funs]
      exact Val.funsList_eq_nil.mpr (fun v hv => (h v hv).1)
    · intro x hx
      simp only [Val.fv] at hx
      obtain ⟨v, hv, hx⟩ := Val.mem_fvList.mp hx
      rcases (h v hv).2 x hx with h' | h'
      · exact .inl h'
      · exact .inr (Multiset.mem_add.mpr (.inl h'))
theorem WfVals.noFn {U Δ : Finset Var} :
    ∀ {Γ : Ctx} {vs : List Val}, WfVals U Δ Γ vs →
      ∀ v ∈ vs, Val.funs v = [] ∧ ∀ x ∈ Val.fv v, x ∈ U ∨ Res.var x ∈ Γ
  | _, _, .nil => by simp
  | _, _, .cons Γ₁ Γ₂ v vs hv hvs => by
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · obtain ⟨h1, h2⟩ := WfVal.noFn hv
      refine ⟨h1, fun x hx => ?_⟩
      rcases h2 x hx with h | h
      · exact .inl h
      · exact .inr (Multiset.mem_add.mpr (.inl h))
    · obtain ⟨h1, h2⟩ := WfVals.noFn hvs w hw
      refine ⟨h1, fun x hx => ?_⟩
      rcases h2 x hx with h | h
      · exact .inl h
      · exact .inr (Multiset.mem_add.mpr (.inr h))
end

theorem mem_hideNames {B : List String} {xs : List Binder} {s : String} :
    s ∈ hideNames B xs ↔ s ∈ B ∧ s ∉ xs.map (·.name) := by
  simp [hideNames]

theorem name_mem_binderVars {xs : List Binder} {s : String}
    (h : Var.name s ∈ Binder.vars xs) : s ∈ xs.map (·.name) := by
  simp only [Binder.vars, List.mem_map] at h ⊢
  obtain ⟨b, hb, he⟩ := h
  cases he
  exact ⟨b, hb, rfl⟩

/-- **FIPNamed typing puts borrowed variables in borrowed positions**: if `Δ | Γ ⊢ e`, then
    function values, and the names `B` which are neither scalar nor owned, occur in `e`
    only in borrowed positions. -/
theorem Wf.bp {cfg : Cfg} {U Δ : Finset Var} {Γ : Ctx} {e : Expr} (h : Wf cfg U Δ Γ e) :
    ∀ B : List String, (∀ s ∈ B, Var.name s ∉ U ∧ Res.var (.name s) ∉ Γ) → Expr.BP B e := by
  induction h with
  | tuple hvs =>
    intro B hB v hv
    obtain ⟨h1, h2⟩ := WfVals.noFn hvs v hv
    refine ⟨h1, fun s hs hx => ?_⟩
    rcases h2 _ hx with h | h
    · exact (hB s hs).1 h
    · exact (hB s hs).2 h
  | call f ys e hf hys he ih =>
    intro B hB
    refine ⟨.inl ?_, ih B fun s hs => ⟨(hB s hs).1, fun h' => (hB s hs).2
      (Multiset.mem_add.mpr (.inl h'))⟩⟩
    intro y hy
    have := hys y hy
    cases y <;> simp_all [BorrowArg, Val.Atomic]
  | bapp y e hy he ih =>
    intro B hB
    exact ⟨.inl trivial, ih B hB⟩
  | fapp f e hf he ih =>
    intro B hB
    exact ⟨.inl trivial, ih B fun s hs => ⟨(hB s hs).1, fun h' => (hB s hs).2
      (Multiset.mem_add.mpr (.inl h'))⟩⟩
  | letIn Γ₁ Γ₂ Γ₃ xs e₁ e₂ _ h1 h2 hfr ih1 ih2 =>
    intro B hB
    refine ⟨ih1 B fun s hs => ⟨(hB s hs).1, fun h' => (hB s hs).2 ?_⟩, ih2 _ ?_⟩
    · exact Multiset.mem_add.mpr (.inl (Multiset.mem_add.mpr (.inl h')))
    · intro s hs
      obtain ⟨hsB, hsx⟩ := mem_hideNames.mp hs
      refine ⟨fun h' => ?_, fun h' => ?_⟩
      · rcases Finset.mem_union.mp h' with h' | h'
        · exact (hB s hsB).1 h'
        · exact hsx (name_mem_binderVars (mem_binderVars_of_scalars h'))
      · rcases Multiset.mem_add.mp h' with h' | h'
        · apply (hB s hsB).2
          rcases Multiset.mem_add.mp h' with h' | h'
          · exact Multiset.mem_add.mpr (.inl (Multiset.mem_add.mpr (.inr h')))
          · exact Multiset.mem_add.mpr (.inr h')
        · exact hsx (name_mem_binderVars (mem_binderVars_of_owned h'))
  | bmatch y bs hy hfr hbs ih =>
    intro B hB
    refine ⟨.inl trivial, Expr.BPB_iff.mpr fun b hb => ih b hb _ ?_⟩
    intro s hs
    obtain ⟨hsB, hsx⟩ := mem_hideNames.mp hs
    refine ⟨fun h' => ?_, (hB s hsB).2⟩
    rcases Finset.mem_union.mp h' with h' | h'
    · exact (hB s hsB).1 h'
    · exact hsx (name_mem_binderVars (mem_binderVars_of_scalars h'))
  | dmatch x bs hfr hbs ih =>
    intro B hB
    refine ⟨fun v hv => ?_, Expr.BPB_iff.mpr fun b hb => ih b hb _ ?_⟩
    · simp only [List.mem_singleton] at hv
      subst hv
      refine ⟨rfl, fun s hs hx => ?_⟩
      simp only [Val.fv, List.mem_singleton] at hx
      subst hx
      exact (hB s hs).2 (Multiset.mem_add.mpr (.inr (Multiset.mem_singleton_self _)))
    · intro s hs
      obtain ⟨hsB, hsx⟩ := mem_hideNames.mp hs
      refine ⟨fun h' => ?_, fun h' => ?_⟩
      · rcases Finset.mem_union.mp h' with h' | h'
        · exact (hB s hsB).1 h'
        · exact hsx (name_mem_binderVars (mem_binderVars_of_scalars h'))
      · rcases Multiset.mem_add.mp h' with h' | h'
        · rcases Multiset.mem_add.mp h' with h' | h'
          · exact (hB s hsB).2 (Multiset.mem_add.mpr (.inl h'))
          · exact hsx (name_mem_binderVars (mem_binderVars_of_owned h'))
        · simp at h'
  | empty he ih =>
    intro B hB
    exact ih B fun s hs => ⟨(hB s hs).1, fun h' => (hB s hs).2 (Multiset.mem_add.mpr (.inl h'))⟩
  | drop x _ he ih =>
    intro B hB
    refine ⟨⟨rfl, fun s hs hx => ?_⟩, ih B fun s hs => ⟨(hB s hs).1, fun h' => (hB s hs).2
      (Multiset.mem_add.mpr (.inl h'))⟩⟩
    simp only [Val.fv, List.mem_singleton] at hx
    subst hx
    exact (hB s hs).2 (Multiset.mem_add.mpr (.inr (Multiset.mem_singleton_self _)))
  | free k _ _ he ih =>
    intro B hB
    exact ih B fun s hs => ⟨(hB s hs).1, fun h' => (hB s hs).2 (Multiset.mem_add.mpr (.inl h'))⟩
  | inst k _ he ih =>
    intro B hB
    refine ih B fun s hs => ⟨(hB s hs).1, fun h' => ?_⟩
    rcases Multiset.mem_add.mp h' with h' | h'
    · exact (hB s hs).2 (Multiset.mem_add.mpr (.inl h'))
    · simp at h'
  | weaken he ih =>
    intro B hB
    exact ih B fun s hs => ⟨(hB s hs).1, fun h' => (hB s hs).2 (Multiset.mem_add.mpr (.inl h'))⟩
  | prim op vs _ =>
    intro B _
    trivial

/-! ## First-order tail contexts (Appendix C.2) -/

/-- First-order tail contexts: every call to a function satisfying `P` is in tail
    position, and nothing evaluated before such a call calls a function satisfying `P`.
    (Function *values* are not restricted, unlike `Expr.TailIn`.) -/
inductive Expr.TailC (P : FName → Prop) : Expr → Prop where
  | base (e : Expr) : (∀ g ∈ e.calls, ¬ P g) → Expr.TailC P e
  | call (f : FName) (e1 e2 : Expr) : (∀ g ∈ e1.calls, ¬ P g) → (∀ g ∈ e2.calls, ¬ P g) →
      Expr.TailC P (.call f e1 e2)
  | letIn (xs : List Binder) (e0 e : Expr) : (∀ g ∈ e0.calls, ¬ P g) → Expr.TailC P e →
      Expr.TailC P (.letIn xs e0 e)
  | bmatch (e0 : Expr) (bs : List Branch) : (∀ g ∈ e0.calls, ¬ P g) →
      (∀ b ∈ bs, Expr.TailC P b.body) → Expr.TailC P (.bmatch e0 bs)
  | dmatch (e0 : Expr) (bs : List Branch) : (∀ g ∈ e0.calls, ¬ P g) →
      (∀ b ∈ bs, Expr.TailC P b.body) → Expr.TailC P (.dmatch e0 bs)
  | drop (x : Val) (e : Expr) : Expr.TailC P e → Expr.TailC P (.drop x e)
  | free (k : Nat) (e : Expr) : Expr.TailC P e → Expr.TailC P (.free k e)

theorem mem_substBranches {σ : Subst} {bs : List Branch} {b' : Branch}
    (h : b' ∈ Expr.substBranches σ bs) :
    ∃ b ∈ bs, b'.body = b.body.subst (σ.remove b.binders) := by
  induction bs with
  | nil => simp [Expr.substBranches] at h
  | cons b bs ih =>
    obtain ⟨c, xs, e⟩ := b
    simp only [Expr.substBranches, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨_, List.mem_cons_self, rfl⟩
    · obtain ⟨b, hb, he⟩ := ih h
      exact ⟨b, List.mem_cons_of_mem _ hb, he⟩

/-- **Lemma 31** (substitution preserves first-order tail contexts). -/
theorem Expr.TailC.subst {P : FName → Prop} {e : Expr} (h : Expr.TailC P e) (σ : Subst) :
    Expr.TailC P (e.subst σ) := by
  induction h generalizing σ with
  | base e he => exact .base _ (by rw [Expr.calls_subst]; exact he)
  | call f e1 e2 h1 h2 =>
    exact .call _ _ _ (by rw [Expr.calls_subst]; exact h1) (by rw [Expr.calls_subst]; exact h2)
  | letIn xs e0 e h0 _ ih =>
    exact .letIn _ _ _ (by rw [Expr.calls_subst]; exact h0) (ih _)
  | bmatch e0 bs h0 _ ih =>
    refine .bmatch _ _ (by rw [Expr.calls_subst]; exact h0) fun b' hb' => ?_
    obtain ⟨b, hb, he⟩ := mem_substBranches hb'
    rw [he]; exact ih b hb _
  | dmatch e0 bs h0 _ ih =>
    refine .dmatch _ _ (by rw [Expr.calls_subst]; exact h0) fun b' hb' => ?_
    obtain ⟨b, hb, he⟩ := mem_substBranches hb'
    rw [he]; exact ih b hb _
  | drop x e _ ih => exact .drop _ _ (ih _)
  | free k e _ ih => exact .free _ _ (ih _)

theorem Expr.TailC.of_tailIn {P : FName → Prop} {fs : List FName} (hP : ∀ g, P g → g ∈ fs)
    {e : Expr} (h : Expr.TailIn fs e) : Expr.TailC P e := by
  have av : ∀ {e : Expr}, e.Avoids fs → ∀ g ∈ e.calls, ¬ P g :=
    fun he g hg hPg => he g (Expr.calls_subset_funs _ g hg) (hP g hPg)
  induction h with
  | base e he => exact .base _ (av he)
  | call f e1 e2 _ h1 h2 => exact .call _ _ _ (av h1) (av h2)
  | letIn xs e0 e h0 _ ih => exact .letIn _ _ _ (av h0) ih
  | bmatch e0 bs h0 _ ih => exact .bmatch _ _ (av h0) ih
  | dmatch e0 bs h0 _ ih => exact .dmatch _ _ (av h0) ih
  | drop x e _ ih => exact .drop _ _ ih
  | free k e _ ih => exact .free _ _ ih

/-- **Lemma 30** (the evaluation context is complementary to the tail context): below a
    non-empty evaluation context, a tail context calls no function of the group. -/
theorem Expr.TailC.plug_avoid {P : FName → Prop} {E : ECtx} {r : Expr}
    (h : Expr.TailC P (E.plug r)) : E = .hole ∨ ∀ g ∈ r.calls, ¬ P g := by
  have key := ECtx.calls_sub E r
  cases E with
  | hole => exact .inl rfl
  | appL E x =>
    right; simp only [ECtx.plug] at h key
    cases h with
    | base _ hb => exact fun g hg => hb g (key g hg)
  | appR vs E =>
    right; simp only [ECtx.plug] at h key
    cases h with
    | base _ hb => exact fun g hg => hb g (key g hg)
  | callB f E x =>
    right; simp only [ECtx.plug] at h key
    cases h with
    | base _ hb => exact fun g hg => hb g (key g hg)
    | call _ _ _ h1 _ => exact fun g hg => h1 g (ECtx.calls_sub E r g hg)
  | callO f vs E =>
    right; simp only [ECtx.plug] at h key
    cases h with
    | base _ hb => exact fun g hg => hb g (key g hg)
    | call _ _ _ _ h2 => exact fun g hg => h2 g (ECtx.calls_sub E r g hg)
  | letIn xs E x =>
    right; simp only [ECtx.plug] at h key
    cases h with
    | base _ hb => exact fun g hg => hb g (key g hg)
    | letIn _ _ _ h0 _ => exact fun g hg => h0 g (ECtx.calls_sub E r g hg)
  | bmatch E bs =>
    right; simp only [ECtx.plug] at h key
    cases h with
    | base _ hb => exact fun g hg => hb g (key g hg)
    | bmatch _ _ h0 _ => exact fun g hg => h0 g (ECtx.calls_sub E r g hg)
  | dmatch E bs =>
    right; simp only [ECtx.plug] at h key
    cases h with
    | base _ hb => exact fun g hg => hb g (key g hg)
    | dmatch _ _ h0 _ => exact fun g hg => h0 g (ECtx.calls_sub E r g hg)

/-- Replacing the subterm in the hole by one that calls no function of the group. -/
theorem Expr.TailC.plug_repl {P : FName → Prop} {E : ECtx} {r r2 : Expr}
    (h : Expr.TailC P (E.plug r)) (h2 : ∀ g ∈ r2.calls, ¬ P g) : Expr.TailC P (E.plug r2) := by
  have avoid : ∀ (F : ECtx), (∀ g ∈ (F.plug r).calls, ¬ P g) →
      ∀ g ∈ (F.plug r2).calls, ¬ P g := by
    intro F hF g hg
    rcases ECtx.calls_plug F r r2 g hg with h' | h'
    · exact hF g h'
    · exact h2 g h'
  cases E with
  | hole => exact .base _ h2
  | appL E x =>
    cases h with
    | base _ hb => exact .base _ (avoid _ hb)
  | appR vs E =>
    cases h with
    | base _ hb => exact .base _ (avoid _ hb)
  | callB f E x =>
    cases h with
    | base _ hb => exact .base _ (avoid _ hb)
    | call _ _ _ h1 h3 => exact .call _ _ _ (avoid E h1) h3
  | callO f vs E =>
    cases h with
    | base _ hb => exact .base _ (avoid _ hb)
    | call _ _ _ h1 h3 => exact .call _ _ _ h1 (avoid E h3)
  | letIn xs E x =>
    cases h with
    | base _ hb => exact .base _ (avoid _ hb)
    | letIn _ _ _ h0 h3 => exact .letIn _ _ _ (avoid E h0) h3
  | bmatch E bs =>
    cases h with
    | base _ hb => exact .base _ (avoid _ hb)
    | bmatch _ _ h0 h3 => exact .bmatch _ _ (avoid E h0) h3
  | dmatch E bs =>
    cases h with
    | base _ hb => exact .base _ (avoid _ hb)
    | dmatch _ _ h0 h3 => exact .dmatch _ _ (avoid E h0) h3

theorem Expr.TailC.drops {P : FName → Prop} (zs : List Val) {e : Expr} (h : Expr.TailC P e) :
    Expr.TailC P (FIPNamed.drops zs e) := by
  induction zs with
  | nil => exact h
  | cons z zs ih =>
    cases z with
    | var x => exact .drop _ _ ih
    | _ => exact ih

end FIPNamed
