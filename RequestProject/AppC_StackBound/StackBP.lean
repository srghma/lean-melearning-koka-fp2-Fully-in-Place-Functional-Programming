module

public import RequestProject.AppC_StackBound.StackDefs

@[expose] public section

/-!
# Borrowed positions and first-order tail contexts (Appendix C)

* `Expr.BP B e`: function values and the free variables satisfying `B` occur in `e` only
  in borrowed positions.  The FIP typing rules guarantee `Expr.BP B e` for the body `e` of
  a function `f(ȳ; x̄) = e`, where `B` holds of the borrowed parameters `ȳ` (`Wf.bp`):
  borrowed parameters are only passed as borrowed arguments, applied, matched on or
  compared.  Consequently a function passed as an argument is never returned, stored in a
  constructor or passed as an owned argument.  Under `k` binders the predicate `B` is
  weakened to `VarPred.shift k B`.
* `Expr.TailC P e`: every call to a function satisfying `P` is in tail position.
-/

namespace FIP

/-! ## Borrowed positions -/

/-- A predicate on the variables of scope `n`, seen under `k` new binders (which do not
    satisfy it). -/
def VarPred.shift {n : Nat} (k : Nat) (B : Var n → Prop) : Var (n + k) → Prop :=
  fun y => ∃ x, B x ∧ x.shift k = y

/-- `v` mentions no top-level function and no variable satisfying `B`. -/
def Val.NoB {n : Nat} (B : Var n → Prop) (v : Val n) : Prop :=
  Val.funs v = [] ∧ ∀ x ∈ v.fv, ¬ B x

/-- A tuple of atomic values (the borrowed arguments of a call). -/
def Expr.AtomArgs {n : Nat} : Expr n → Prop
  | .ret ys => ∀ y ∈ ys, y.Atomic
  | _ => False

/-- A single atomic value (the head of an application, the scrutinee of a match). -/
def Expr.AtomArg {n : Nat} : Expr n → Prop
  | .ret [a] => a.Atomic
  | _ => False

mutual
/-- Function values, and the free variables satisfying `B`, occur in `e` only in borrowed
    positions: borrowed arguments of calls, heads of applications, scrutinees of borrowing
    matches and arguments of primitive operations. -/
def Expr.BP {n : Nat} (B : Var n → Prop) : Expr n → Prop
  | .ret vs => ∀ v ∈ vs, Val.NoB B v
  | .app e1 e2 => (e1.AtomArg ∨ Expr.BP B e1) ∧ Expr.BP B e2
  | .call _ e1 e2 => (e1.AtomArgs ∨ Expr.BP B e1) ∧ Expr.BP B e2
  | .letIn xs e1 e2 => Expr.BP B e1 ∧ Expr.BP (VarPred.shift xs.length B) e2
  | .bmatch e bs => (e.AtomArg ∨ Expr.BP B e) ∧ Expr.BPB B bs
  | .dmatch e bs => Expr.BP B e ∧ Expr.BPB B bs
  | .drop x e => Val.NoB B x ∧ Expr.BP B e
  | .free _ e => Expr.BP B e
  | .prim _ _ => True
/-- `Expr.BP` for the bodies of branches. -/
def Expr.BPB {n : Nat} (B : Var n → Prop) : Branches n → Prop
  | .nil => True
  | .cons _ xs e bs => Expr.BP (VarPred.shift xs.length B) e ∧ Expr.BPB B bs
end

theorem Expr.BPB_iff {n : Nat} {B : Var n → Prop} : ∀ {bs : Branches n},
    Expr.BPB B bs ↔ ∀ b ∈ bs.toList, Expr.BP (VarPred.shift b.binders.length B) b.body
  | .nil => by simp [Expr.BPB]
  | .cons c xs e bs => by
    simp only [Expr.BPB, Expr.BPB_iff (bs := bs), Branches.toList_cons, List.mem_cons,
      forall_eq_or_imp]

theorem Val.funsList_eq_nil {n : Nat} {vs : List (Val n)} :
    Val.funsList vs = [] ↔ ∀ v ∈ vs, Val.funs v = [] := by
  induction vs with
  | nil => simp [Val.funsList]
  | cons v vs ih => simp [Val.funsList, ih]

/-! ### Monotonicity in the predicate -/

theorem Val.NoB.mono {n : Nat} {B B' : Var n → Prop} (hB : ∀ x, B x → B' x) {v : Val n}
    (h : Val.NoB B' v) : Val.NoB B v :=
  ⟨h.1, fun x hx hb => h.2 x hx (hB x hb)⟩

theorem VarPred.shift_mono {n : Nat} {B B' : Var n → Prop} (hB : ∀ x, B x → B' x) (k : Nat) :
    ∀ y, VarPred.shift k B y → VarPred.shift k B' y := by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, hB x hx, rfl⟩

mutual
theorem Expr.BP.mono : ∀ {n : Nat} {B B' : Var n → Prop}, (∀ x, B x → B' x) →
    ∀ e : Expr n, Expr.BP B' e → Expr.BP B e
  | _, _, _, hB, .ret _, h => fun v hv => (h v hv).mono hB
  | _, _, _, hB, .app e1 e2, h =>
    ⟨h.1.imp id (Expr.BP.mono hB e1), Expr.BP.mono hB e2 h.2⟩
  | _, _, _, hB, .call _ e1 e2, h =>
    ⟨h.1.imp id (Expr.BP.mono hB e1), Expr.BP.mono hB e2 h.2⟩
  | _, _, _, hB, .letIn xs e1 e2, h =>
    ⟨Expr.BP.mono hB e1 h.1, Expr.BP.mono (VarPred.shift_mono hB xs.length) e2 h.2⟩
  | _, _, _, hB, .bmatch e bs, h =>
    ⟨h.1.imp id (Expr.BP.mono hB e), Expr.BPB.mono hB bs h.2⟩
  | _, _, _, hB, .dmatch e bs, h => ⟨Expr.BP.mono hB e h.1, Expr.BPB.mono hB bs h.2⟩
  | _, _, _, hB, .drop _ e, h => ⟨h.1.mono hB, Expr.BP.mono hB e h.2⟩
  | _, _, _, hB, .free _ e, h => Expr.BP.mono hB e h
  | _, _, _, _, .prim _ _, _ => trivial
theorem Expr.BPB.mono : ∀ {n : Nat} {B B' : Var n → Prop}, (∀ x, B x → B' x) →
    ∀ bs : Branches n, Expr.BPB B' bs → Expr.BPB B bs
  | _, _, _, _, .nil, _ => trivial
  | _, _, _, hB, .cons _ xs e bs, h =>
    ⟨Expr.BP.mono (VarPred.shift_mono hB xs.length) e h.1, Expr.BPB.mono hB bs h.2⟩
end

/-! ### Substitution -/

theorem Val.atomic_shift {n : Nat} (k : Nat) {v : Val n} (h : v.Atomic) : (v.shift k).Atomic := by
  cases v with
  | var x => rw [Val.shift_var]; trivial
  | fn _ => trivial
  | lit _ => trivial
  | ctor _ _ => exact h.elim

theorem Val.atomic_subst {n m : Nat} {σ : Fin n → Val m} (hσ : ∀ i, (σ i).Atomic) :
    ∀ {v : Val n}, v.Atomic → (v.subst σ).Atomic
  | .var (.bvar i), _ => hσ i
  | .var (.loc _), _ => trivial
  | .fn _, _ => trivial
  | .lit _, _ => trivial

theorem Subst.atomic_up {n m : Nat} {σ : Fin n → Val m} (hσ : ∀ i, (σ i).Atomic) (k : Nat) :
    ∀ i, (Subst.up k σ i).Atomic := by
  intro i
  simp only [Subst.up]
  split
  · trivial
  · exact Val.atomic_shift k (hσ _)

theorem Expr.atomArg_subst {n m : Nat} {σ : Fin n → Val m} (hσ : ∀ i, (σ i).Atomic)
    {e : Expr n} (h : e.AtomArg) : (e.subst σ).AtomArg := by
  cases e with
  | ret vs =>
    match vs, h with
    | [a], h =>
      simp only [Expr.subst, Val.substList_eq_map, List.map_cons, List.map_nil, Expr.AtomArg]
      exact Val.atomic_subst hσ h
  | _ => simp [Expr.AtomArg] at h

theorem Expr.atomArgs_subst {n m : Nat} {σ : Fin n → Val m} (hσ : ∀ i, (σ i).Atomic)
    {e : Expr n} (h : e.AtomArgs) : (e.subst σ).AtomArgs := by
  cases e with
  | ret vs =>
    simp only [Expr.subst, Val.substList_eq_map, Expr.AtomArgs, List.mem_map] at h ⊢
    rintro _ ⟨y, hy, rfl⟩
    exact Val.atomic_subst hσ (h y hy)
  | _ => simp [Expr.AtomArgs] at h

mutual
theorem Val.funs_subst_noB {n m : Nat} {B : Var n → Prop} {σ : Fin n → Val m}
    (hσ : ∀ i, ¬ B (.bvar i) → Val.funs (σ i) = []) :
    ∀ v : Val n, Val.NoB B v → Val.funs (v.subst σ) = []
  | .var (.bvar i), h => hσ i (h.2 _ (by simp [Val.fv]))
  | .var (.loc _), _ => rfl
  | .fn f, h => by simp [Val.NoB, Val.funs] at h
  | .lit _, _ => rfl
  | .ctor c vs, h => by
    simp only [Val.subst, Val.funs]
    exact Val.funsList_subst_noB hσ vs h.1 (fun x hx => h.2 x (by simpa [Val.fv] using hx))
theorem Val.funsList_subst_noB {n m : Nat} {B : Var n → Prop} {σ : Fin n → Val m}
    (hσ : ∀ i, ¬ B (.bvar i) → Val.funs (σ i) = []) :
    ∀ vs : List (Val n), Val.funsList vs = [] → (∀ x ∈ Val.fvList vs, ¬ B x) →
      Val.funsList (Val.substList σ vs) = []
  | [], _, _ => rfl
  | v :: vs, h1, h2 => by
    simp only [Val.funsList, List.append_eq_nil_iff, Val.fvList, List.mem_append] at h1 h2
    simp only [Val.substList, Val.funsList, List.append_eq_nil_iff]
    exact ⟨Val.funs_subst_noB hσ v ⟨h1.1, fun x hx => h2 x (.inl hx)⟩,
      Val.funsList_subst_noB hσ vs h1.2 (fun x hx => h2 x (.inr hx))⟩
end

theorem Subst.up_cond {n m : Nat} {B : Var n → Prop} {σ : Fin n → Val m} (k : Nat)
    (hσ : ∀ i, ¬ B (.bvar i) → Val.funs (σ i) = []) :
    ∀ i, ¬ VarPred.shift k B (.bvar i) → Val.funs (Subst.up k σ i) = [] := by
  intro i hn
  simp only [Subst.up]
  split
  · rfl
  · rename_i hi
    rw [Val.funs_shift]
    refine hσ _ fun hb => hn ⟨_, hb, ?_⟩
    simp only [Var.shift, Var.bvar.injEq]
    ext; simp; omega

theorem VarPred.shift_false {n : Nat} (k : Nat) :
    ∀ y, VarPred.shift k (fun _ : Var n => False) y → False := by
  rintro _ ⟨_, h, -⟩; exact h

mutual
/-- Substituting atomic values, where the values for variables outside `B` mention no
    functions, into an expression with `BP B` yields an expression without function values
    or variables in non-borrowed positions. -/
theorem Expr.bp_subst : ∀ {n m : Nat} (e : Expr n) (B : Var n → Prop) (σ : Fin n → Val m),
    (∀ i, (σ i).Atomic) → (∀ i, ¬ B (.bvar i) → Val.funs (σ i) = []) → Expr.BP B e →
    Expr.BP (fun _ => False) (e.subst σ)
  | _, _, .ret vs, B, σ, _, hσ, h => by
    simp only [Expr.subst, Val.substList_eq_map, Expr.BP, List.mem_map]
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨Val.funs_subst_noB hσ v (h v hv), by simp⟩
  | _, _, .app e1 e2, B, σ, ha, hσ, h => by
    simp only [Expr.subst, Expr.BP] at h ⊢
    refine ⟨?_, Expr.bp_subst e2 B σ ha hσ h.2⟩
    rcases h.1 with h1 | h1
    · exact .inl (Expr.atomArg_subst ha h1)
    · exact .inr (Expr.bp_subst e1 B σ ha hσ h1)
  | _, _, .call _ e1 e2, B, σ, ha, hσ, h => by
    simp only [Expr.subst, Expr.BP] at h ⊢
    refine ⟨?_, Expr.bp_subst e2 B σ ha hσ h.2⟩
    rcases h.1 with h1 | h1
    · exact .inl (Expr.atomArgs_subst ha h1)
    · exact .inr (Expr.bp_subst e1 B σ ha hσ h1)
  | _, _, .letIn xs e1 e2, B, σ, ha, hσ, h => by
    simp only [Expr.subst, Expr.BP] at h ⊢
    exact ⟨Expr.bp_subst e1 B σ ha hσ h.1,
      Expr.BP.mono (VarPred.shift_false _) _
        (Expr.bp_subst e2 _ (Subst.up xs.length σ) (Subst.atomic_up ha _)
          (Subst.up_cond _ hσ) h.2)⟩
  | _, _, .bmatch e bs, B, σ, ha, hσ, h => by
    simp only [Expr.subst, Expr.BP] at h ⊢
    refine ⟨?_, Expr.bpB_subst bs B σ ha hσ h.2⟩
    rcases h.1 with h1 | h1
    · exact .inl (Expr.atomArg_subst ha h1)
    · exact .inr (Expr.bp_subst e B σ ha hσ h1)
  | _, _, .dmatch e bs, B, σ, ha, hσ, h => by
    simp only [Expr.subst, Expr.BP] at h ⊢
    exact ⟨Expr.bp_subst e B σ ha hσ h.1, Expr.bpB_subst bs B σ ha hσ h.2⟩
  | _, _, .drop x e, B, σ, ha, hσ, h => by
    simp only [Expr.subst, Expr.BP] at h ⊢
    exact ⟨⟨Val.funs_subst_noB hσ x h.1, by simp⟩, Expr.bp_subst e B σ ha hσ h.2⟩
  | _, _, .free _ e, B, σ, ha, hσ, h => by
    simp only [Expr.subst, Expr.BP] at h ⊢
    exact Expr.bp_subst e B σ ha hσ h
  | _, _, .prim _ _, _, _, _, _, _ => trivial
theorem Expr.bpB_subst : ∀ {n m : Nat} (bs : Branches n) (B : Var n → Prop)
    (σ : Fin n → Val m), (∀ i, (σ i).Atomic) → (∀ i, ¬ B (.bvar i) → Val.funs (σ i) = []) →
    Expr.BPB B bs → Expr.BPB (fun _ => False) (Branches.subst σ bs)
  | _, _, .nil, _, _, _, _, _ => trivial
  | _, _, .cons _ xs e bs, B, σ, ha, hσ, h => by
    simp only [Branches.subst, Expr.BPB] at h ⊢
    exact ⟨Expr.BP.mono (VarPred.shift_false _) _
        (Expr.bp_subst e _ (Subst.up xs.length σ) (Subst.atomic_up ha _)
          (Subst.up_cond _ hσ) h.1), Expr.bpB_subst bs B σ ha hσ h.2⟩
end

theorem Expr.bp_drops {B : Var 0 → Prop} (zs : List (Val 0)) (hz : ∀ z ∈ zs, Val.NoB B z)
    {e : Expr 0} (h : Expr.BP B e) : Expr.BP B (drops zs e) := by
  induction zs with
  | nil => exact h
  | cons z zs ih =>
    have ih' := ih (fun z' hz' => hz z' (List.mem_cons_of_mem _ hz'))
    cases z with
    | var x => exact ⟨hz _ List.mem_cons_self, ih'⟩
    | _ => exact ih'

theorem Expr.atomArg_plug {n : Nat} {E : ECtx n} {r : Expr n} (h : (E.plug r).AtomArg) :
    E = .hole := by
  cases E with
  | hole => rfl
  | _ => simp [ECtx.plug, Expr.AtomArg] at h

theorem Expr.atomArgs_plug {n : Nat} {E : ECtx n} {r : Expr n} (h : (E.plug r).AtomArgs) :
    E = .hole := by
  cases E with
  | hole => rfl
  | _ => simp [ECtx.plug, Expr.AtomArgs] at h

theorem Expr.atomArgs_of_atomArg {n : Nat} {e : Expr n} (h : e.AtomArg) : e.AtomArgs := by
  cases e with
  | ret vs =>
    match vs, h with
    | [a], h => simpa [Expr.AtomArgs] using h
  | _ => simp [Expr.AtomArg] at h

/-- The subterm in the hole of an evaluation context is in a borrowed position only if it
    is a tuple of atomic values. -/
theorem ECtx.bp_plug_inv {n : Nat} {B : Var n → Prop} (E : ECtx n) (r : Expr n)
    (h : Expr.BP B (E.plug r)) : Expr.BP B r ∨ r.AtomArgs := by
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
theorem ECtx.bp_plug_repl {n : Nat} {B : Var n → Prop} (E : ECtx n) (r r2 : Expr n)
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

/-! ## Borrowed positions follow from the FIP typing rules -/

mutual
theorem WfVal.noFn {n : Nat} {U Δ : Finset (Var n)} :
    ∀ {Γ : Ctx n} {v : Val n}, WfVal U Δ Γ v →
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
theorem WfVals.noFn {n : Nat} {U Δ : Finset (Var n)} :
    ∀ {Γ : Ctx n} {vs : List (Val n)}, WfVals U Δ Γ vs →
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

/-- Variables satisfying `B` which are neither scalar nor owned, seen under binders. -/
theorem VarPred.shift_avoid {n : Nat} {B : Var n → Prop} {U : Finset (Var n)} {Γ : Ctx n}
    (hB : ∀ x, B x → x ∉ U ∧ Res.var x ∉ Γ) (xs : List Bool) :
    ∀ y, VarPred.shift xs.length B y →
      y ∉ Vars.shift xs.length U ∪ Binder.scalars xs ∧
        Res.var y ∉ Γ.shift xs.length + Binder.owned xs := by
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases Finset.mem_union.mp h with h | h
    · exact (hB x hx).1 (Vars.mem_shift.mp h)
    · exact Binder.shift_not_mem_scalars xs x h
  · rcases Multiset.mem_add.mp h with h | h
    · exact (hB x hx).2 (Ctx.mem_shift_var.mp h)
    · exact Binder.shift_not_mem_owned xs x h

/-- **FIP typing puts borrowed variables in borrowed positions**: if `Δ | Γ ⊢ e`, then
    function values, and the variables satisfying `B` which are neither scalar nor owned,
    occur in `e` only in borrowed positions. -/
theorem Wf.bp {cfg : Cfg} {n : Nat} {U Δ : Finset (Var n)} {Γ : Ctx n} {e : Expr n}
    (h : Wf cfg U Δ Γ e) :
    ∀ B : Var n → Prop, (∀ x, B x → x ∉ U ∧ Res.var x ∉ Γ) → Expr.BP B e := by
  induction h with
  | tuple hvs =>
    intro B hB v hv
    obtain ⟨h1, h2⟩ := WfVals.noFn hvs v hv
    refine ⟨h1, fun x hx hxB => ?_⟩
    rcases h2 _ hx with h | h
    · exact (hB x hxB).1 h
    · exact (hB x hxB).2 h
  | call f ys e hf hys he ih =>
    intro B hB
    refine ⟨.inl ?_, ih B fun x hx => ⟨(hB x hx).1, fun h' => (hB x hx).2
      (Multiset.mem_add.mpr (.inl h'))⟩⟩
    intro y hy
    have := hys y hy
    cases y <;> simp_all [BorrowArg, Val.Atomic]
  | bapp y e hy he ih =>
    intro B hB
    exact ⟨.inl trivial, ih B hB⟩
  | fapp f e hf he ih =>
    intro B hB
    exact ⟨.inl trivial, ih B fun x hx => ⟨(hB x hx).1, fun h' => (hB x hx).2
      (Multiset.mem_add.mpr (.inl h'))⟩⟩
  | @letIn n U Δ Γ₁ Γ₂ Γ₃ xs e₁ e₂ _ h1 h2 ih1 ih2 =>
    intro B hB
    refine ⟨ih1 B fun x hx => ⟨(hB x hx).1, fun h' => (hB x hx).2 ?_⟩, ih2 _ ?_⟩
    · exact Multiset.mem_add.mpr (.inl (Multiset.mem_add.mpr (.inl h')))
    · refine VarPred.shift_avoid (U := U) (Γ := Γ₂ + Γ₃) (fun x hx => ⟨(hB x hx).1, fun h' => ?_⟩) xs
      apply (hB x hx).2
      rcases Multiset.mem_add.mp h' with h' | h'
      · exact Multiset.mem_add.mpr (.inl (Multiset.mem_add.mpr (.inr h')))
      · exact Multiset.mem_add.mpr (.inr h')
  | bmatch y bs hy hbs ih =>
    intro B hB
    refine ⟨.inl trivial, Expr.BPB_iff.mpr fun b hb => ih b hb _ ?_⟩
    intro y hy
    have := VarPred.shift_avoid hB b.binders y hy
    refine ⟨this.1, fun h' => this.2 (Multiset.mem_add.mpr (.inl h'))⟩
  | @dmatch n U Δ Γ x bs hbs ih =>
    intro B hB
    refine ⟨fun v hv => ?_, Expr.BPB_iff.mpr fun b hb => ih b hb _ ?_⟩
    · simp only [List.mem_singleton] at hv
      subst hv
      refine ⟨rfl, fun y hy hyB => ?_⟩
      simp only [Val.fv, List.mem_singleton] at hy
      subst hy
      exact (hB _ hyB).2 (Multiset.mem_add.mpr (.inr (Multiset.mem_singleton_self _)))
    · intro y hy
      have := VarPred.shift_avoid (Γ := Γ)
        (fun x hx => ⟨(hB x hx).1, fun h' => (hB x hx).2 (Multiset.mem_add.mpr (.inl h'))⟩)
        b.binders y hy
      refine ⟨this.1, fun h' => ?_⟩
      rcases Multiset.mem_add.mp h' with h' | h'
      · exact this.2 h'
      · simp at h'
  | empty he ih =>
    intro B hB
    exact ih B fun x hx => ⟨(hB x hx).1, fun h' => (hB x hx).2 (Multiset.mem_add.mpr (.inl h'))⟩
  | drop x _ he ih =>
    intro B hB
    refine ⟨⟨rfl, fun y hy hyB => ?_⟩, ih B fun x hx => ⟨(hB x hx).1, fun h' => (hB x hx).2
      (Multiset.mem_add.mpr (.inl h'))⟩⟩
    simp only [Val.fv, List.mem_singleton] at hy
    subst hy
    exact (hB _ hyB).2 (Multiset.mem_add.mpr (.inr (Multiset.mem_singleton_self _)))
  | free k _ _ he ih =>
    intro B hB
    exact ih B fun x hx => ⟨(hB x hx).1, fun h' => (hB x hx).2 (Multiset.mem_add.mpr (.inl h'))⟩
  | inst k _ he ih =>
    intro B hB
    refine ih B fun x hx => ⟨(hB x hx).1, fun h' => ?_⟩
    rcases Multiset.mem_add.mp h' with h' | h'
    · exact (hB x hx).2 (Multiset.mem_add.mpr (.inl h'))
    · simp at h'
  | weaken he ih =>
    intro B hB
    exact ih B fun x hx => ⟨(hB x hx).1, fun h' => (hB x hx).2 (Multiset.mem_add.mpr (.inl h'))⟩
  | prim op vs _ =>
    intro B _
    trivial

/-! ## First-order tail contexts (Appendix C.2) -/

/-- First-order tail contexts: every call to a function satisfying `P` is in tail
    position, and nothing evaluated before such a call calls a function satisfying `P`.
    (Function *values* are not restricted, unlike `Expr.TailIn`.) -/
inductive Expr.TailC (P : FName → Prop) : {n : Nat} → Expr n → Prop where
  | base {n : Nat} (e : Expr n) : (∀ g ∈ e.calls, ¬ P g) → Expr.TailC P e
  | call {n : Nat} (f : FName) (e1 e2 : Expr n) : (∀ g ∈ e1.calls, ¬ P g) →
      (∀ g ∈ e2.calls, ¬ P g) → Expr.TailC P (.call f e1 e2)
  | letIn {n : Nat} (xs : List Bool) (e0 : Expr n) (e : Expr (n + xs.length)) :
      (∀ g ∈ e0.calls, ¬ P g) → Expr.TailC P e → Expr.TailC P (.letIn xs e0 e)
  | bmatch {n : Nat} (e0 : Expr n) (bs : Branches n) : (∀ g ∈ e0.calls, ¬ P g) →
      (∀ b ∈ bs.toList, Expr.TailC P b.body) → Expr.TailC P (.bmatch e0 bs)
  | dmatch {n : Nat} (e0 : Expr n) (bs : Branches n) : (∀ g ∈ e0.calls, ¬ P g) →
      (∀ b ∈ bs.toList, Expr.TailC P b.body) → Expr.TailC P (.dmatch e0 bs)
  | drop {n : Nat} (x : Val n) (e : Expr n) : Expr.TailC P e → Expr.TailC P (.drop x e)
  | free {n : Nat} (k : Nat) (e : Expr n) : Expr.TailC P e → Expr.TailC P (.free k e)

/-- **Lemma 31** (substitution preserves first-order tail contexts). -/
theorem Expr.TailC.subst {P : FName → Prop} {n : Nat} {e : Expr n} (h : Expr.TailC P e) :
    ∀ {m : Nat} (σ : Fin n → Val m), Expr.TailC P (e.subst σ) := by
  induction h with
  | base e he => intro m σ; exact .base _ (by rw [Expr.calls_subst]; exact he)
  | call f e1 e2 h1 h2 =>
    intro m σ
    exact .call _ _ _ (by rw [Expr.calls_subst]; exact h1) (by rw [Expr.calls_subst]; exact h2)
  | letIn xs e0 e h0 _ ih =>
    intro m σ
    exact .letIn _ _ _ (by rw [Expr.calls_subst]; exact h0) (ih _)
  | bmatch e0 bs h0 _ ih =>
    intro m σ
    refine .bmatch _ _ (by rw [Expr.calls_subst]; exact h0) fun b' hb' => ?_
    rw [Branches.toList_subst] at hb'
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hb'
    exact ih b hb _
  | dmatch e0 bs h0 _ ih =>
    intro m σ
    refine .dmatch _ _ (by rw [Expr.calls_subst]; exact h0) fun b' hb' => ?_
    rw [Branches.toList_subst] at hb'
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hb'
    exact ih b hb _
  | drop x e _ ih => intro m σ; exact .drop _ _ (ih _)
  | free k e _ ih => intro m σ; exact .free _ _ (ih _)

theorem Expr.TailC.of_tailIn {P : FName → Prop} {fs : List FName} (hP : ∀ g, P g → g ∈ fs)
    {n : Nat} {e : Expr n} (h : Expr.TailIn fs e) : Expr.TailC P e := by
  have av : ∀ {n : Nat} {e : Expr n}, e.Avoids fs → ∀ g ∈ e.calls, ¬ P g :=
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
theorem Expr.TailC.plug_avoid {P : FName → Prop} {n : Nat} {E : ECtx n} {r : Expr n}
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
theorem Expr.TailC.plug_repl {P : FName → Prop} {n : Nat} {E : ECtx n} {r r2 : Expr n}
    (h : Expr.TailC P (E.plug r)) (h2 : ∀ g ∈ r2.calls, ¬ P g) : Expr.TailC P (E.plug r2) := by
  have avoid : ∀ (F : ECtx n), (∀ g ∈ (F.plug r).calls, ¬ P g) →
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

theorem Expr.TailC.drops {P : FName → Prop} (zs : List (Val 0)) {e : Expr 0}
    (h : Expr.TailC P e) : Expr.TailC P (FIP.drops zs e) := by
  induction zs with
  | nil => exact h
  | cons z zs ih =>
    cases z with
    | var x => exact .drop _ _ ih
    | _ => exact ih

end FIP
