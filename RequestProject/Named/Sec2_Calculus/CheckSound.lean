module

public import RequestProject.Named.Sec2_Calculus.Check

@[expose] public section

/-!
# Soundness of the FIPNamed checker

`check_sound`: if `check cfg U Δ V C A e = true` then `Δ | V, C, ⋄^A ⊢ e` is derivable.
Consequently `FunDef.check_sound` and `Sig.check_sound` turn a successful (decidable)
check into a proof of `FunDef.Wf` / `Sig.Wf`.
-/

namespace FIPNamed

/-- The reuse credits `C` as an environment. -/
def creditsCtx (C : List Nat) : Ctx := ((C.map Res.credit : List Res) : Multiset Res)

/-- The variables `V` as an environment. -/
def varsCtx (V : List Var) : Ctx := ((V.map Res.var : List Res) : Multiset Res)

@[simp] theorem creditsCtx_nil : creditsCtx [] = 0 := rfl
@[simp] theorem creditsCtx_cons (c : Nat) (C : List Nat) :
    creditsCtx (c :: C) = {Res.credit c} + creditsCtx C := by
  simp [creditsCtx, ← Multiset.cons_coe, Multiset.singleton_add]
@[simp] theorem creditsCtx_append (C D : List Nat) :
    creditsCtx (C ++ D) = creditsCtx C + creditsCtx D := by
  simp [creditsCtx]
@[simp] theorem varsCtx_nil : varsCtx [] = 0 := rfl
@[simp] theorem varsCtx_cons (x : Var) (V : List Var) :
    varsCtx (x :: V) = {Res.var x} + varsCtx V := by
  simp [varsCtx, ← Multiset.cons_coe, Multiset.singleton_add]
@[simp] theorem varsCtx_append (V W : List Var) :
    varsCtx (V ++ W) = varsCtx V + varsCtx W := by
  simp [varsCtx]
theorem creditsCtx_perm {C D : List Nat} (h : C.Perm D) : creditsCtx C = creditsCtx D :=
  Multiset.coe_eq_coe.mpr (h.map _)
theorem varsCtx_perm {V W : List Var} (h : V.Perm W) : varsCtx V = varsCtx W :=
  Multiset.coe_eq_coe.mpr (h.map _)

theorem ctxOf_eq (V : List Var) (C : List Nat) (A : Nat) :
    ctxOf V C A = varsCtx V + creditsCtx C + Multiset.replicate A Res.alloc := rfl

/-- Normalize an equation between environments and close it by commutativity. -/
macro "ms_abel" : tactic =>
  `(tactic| (
    simp only [creditsCtx_cons, creditsCtx_append, creditsCtx_nil, varsCtx_cons,
      varsCtx_append, varsCtx_nil, ctxOf_eq, Multiset.replicate_succ,
      ← Multiset.singleton_add, Multiset.cons_zero, add_zero, zero_add]
    abel))

theorem Wf.cast {cfg : Cfg} {U Δ : Finset Var} {Γ Γ' : Ctx} {e : Expr} (h : Γ = Γ')
    (w : Wf cfg U Δ Γ e) : Wf cfg U Δ Γ' e := h ▸ w

theorem Wf.weakenN {cfg : Cfg} {U Δ : Finset Var} {Γ : Ctx} {e : Expr} (A : Nat)
    (w : Wf cfg U Δ Γ e) : Wf cfg U Δ (Γ + Multiset.replicate A Res.alloc) e := by
  induction A with
  | zero => simpa using w
  | succ n ih =>
    refine Wf.cast ?_ (Wf.weaken ih)
    rw [Multiset.replicate_succ, ← Multiset.singleton_add]
    abel

/-- Paying for demanded reuse credits `D` with available credits `C` and `A` allocation
    credits. -/
theorem Wf.supply {cfg : Cfg} {U Δ : Finset Var} {e : Expr} :
    ∀ (C D : List Nat) (A : Nat) (Γ : Ctx), creditsOk C D A = true →
      Wf cfg U Δ (Γ + creditsCtx D) e →
      Wf cfg U Δ (Γ + creditsCtx C + Multiset.replicate A Res.alloc) e := by
  intro C
  induction C with
  | nil =>
    intro D
    induction D with
    | nil =>
      intro A Γ _ w
      simpa [creditsCtx] using w.weakenN A
    | cons d D ih =>
      intro A Γ hok w
      simp only [creditsOk, List.all_cons, Bool.and_eq_true, decide_eq_true_eq,
        List.length_cons] at hok
      obtain ⟨⟨hd, hD⟩, hlen⟩ := hok
      obtain ⟨A', rfl⟩ : ∃ A', A = A' + 1 := ⟨A - 1, by omega⟩
      have w' : Wf cfg U Δ ((Γ + {Res.credit d}) + creditsCtx D) e :=
        Wf.cast (by ms_abel) w
      have h2 := ih A' (Γ + {Res.credit d})
        (by simp [creditsOk, hD]; omega) w'
      have h3 : Wf cfg U Δ ((Γ + Multiset.replicate A' Res.alloc) + {Res.credit d}) e :=
        Wf.cast (by ms_abel) h2
      refine Wf.cast ?_ (Wf.inst d hd h3)
      ms_abel
  | cons c C ih =>
    intro D A Γ hok w
    rcases c with _ | c
    · simp only [creditsOk] at hok
      have := Wf.empty (ih D A Γ hok w)
      refine Wf.cast ?_ this
      ms_abel
    · simp only [creditsOk, Bool.and_eq_true, List.contains_iff_mem] at hok
      obtain ⟨hmem, hok⟩ := hok
      have hperm := List.perm_cons_erase hmem
      have w' : Wf cfg U Δ ((Γ + {Res.credit (c+1)}) + creditsCtx (D.erase (c+1))) e := by
        refine Wf.cast ?_ w
        rw [creditsCtx_perm hperm]
        ms_abel
      refine Wf.cast ?_ (ih _ A _ hok w')
      ms_abel

theorem WfVal.cast {U Δ : Finset Var} {Γ Γ' : Ctx} {v : Val} (h : Γ = Γ')
    (w : WfVal U Δ Γ v) : WfVal U Δ Γ' v := h ▸ w

theorem WfVals.cast' {U Δ : Finset Var} {Γ : Ctx} {vs : List Val} (w : WfVals U Δ Γ vs)
    {Γ' : Ctx} (h : Γ = Γ') : WfVals U Δ Γ' vs := h ▸ w

mutual
theorem val_sound (U Δ : List Var) : ∀ v : Val, Val.plain v = true →
    WfVal U.toFinset Δ.toFinset (varsCtx (Val.ownedUses U v) + creditsCtx (Val.credits v)) v
  | .var x, _ => by
    by_cases hx : x ∈ U
    · simpa [Val.ownedUses, hx, Val.credits] using WfVal.svar x (List.mem_toFinset.mpr hx)
    · simpa [Val.ownedUses, hx, Val.credits, varsCtx] using WfVal.var (U := U.toFinset)
        (Δ := Δ.toFinset) x
  | .ctor c [], _ => by simpa [Val.ownedUses, Val.ownedUsesList, Val.credits] using WfVal.atom c
  | .ctor c (v :: vs), h => by
    simp only [Val.plain] at h
    have := WfVal.reuse (U := U.toFinset) (Δ := Δ.toFinset) c (v :: vs) _ (by simp)
      (vals_sound U Δ (v :: vs) h)
    refine WfVal.cast ?_ this
    simp only [Val.ownedUses, Val.credits]
    ms_abel
  | .lit n, _ => by simpa [Val.ownedUses, Val.credits] using WfVal.lit n
  | .fn f, h => by simp [Val.plain] at h
theorem vals_sound (U Δ : List Var) :
    ∀ vs : List Val, Val.plainList vs = true →
      WfVals U.toFinset Δ.toFinset
        (varsCtx (Val.ownedUsesList U vs) + creditsCtx (Val.creditsList vs)) vs
  | [], _ => by simpa [Val.ownedUsesList, Val.creditsList] using WfVals.nil
  | v :: vs, h => by
    simp only [Val.plainList, Bool.and_eq_true] at h
    have := WfVals.cons _ _ v vs (val_sound U Δ v h.1) (vals_sound U Δ vs h.2)
    refine this.cast' ?_
    simp only [Val.ownedUsesList, Val.creditsList]
    ms_abel
end

@[simp] theorem mem_ctxOf_var {x : Var} {V : List Var} {C : List Nat} {A : Nat} :
    Res.var x ∈ ctxOf V C A ↔ x ∈ V := by
  simp [ctxOf, Multiset.mem_replicate]

theorem freshB_sound {xs : List Binder} {U Δ V : List Var} (C : List Nat) (A : Nat)
    (h : Binder.freshB xs U Δ V = true) :
    Binder.Fresh xs U.toFinset Δ.toFinset (ctxOf V C A) := by
  simp only [Binder.freshB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  refine ⟨h.1, fun b hb => ?_⟩
  have := h.2 b hb
  simp_all

theorem creditsCtx_eq_map (C : List Nat) :
    creditsCtx C = Multiset.map Res.credit (C : Multiset Nat) := by
  simp [creditsCtx]

theorem creditsCtx_split (C D : List Nat) :
    creditsCtx C = creditsCtx (C.bagInter D) + creditsCtx (C.diff (C.bagInter D)) := by
  rw [creditsCtx_eq_map, creditsCtx_eq_map, creditsCtx_eq_map, ← Multiset.map_add,
    ← Multiset.coe_sub]
  congr 1
  rw [add_tsub_cancel_of_le]
  exact Multiset.coe_le.mpr List.bagInter_sublist_left.subperm

theorem perm_filter3 {α : Type} (p q : α → Bool) : ∀ l : List α,
    l.Perm (l.filter (fun x => p x && !q x) ++ l.filter (fun x => p x && q x) ++
      l.filter (fun x => !p x))
  | [] => by simp
  | a :: l => by
    have ih := perm_filter3 p q l
    simp only [List.append_assoc] at ih ⊢
    cases hp : p a <;> cases hq : q a <;> simp [hp, hq]
    · exact (List.Perm.cons a ih).trans (List.perm_middle.symm.trans
        (List.Perm.append_left _ List.perm_middle.symm))
    · exact (List.Perm.cons a ih).trans (List.perm_middle.symm.trans
        (List.Perm.append_left _ List.perm_middle.symm))
    · exact ih
    · exact (List.Perm.cons a ih).trans (List.perm_middle.symm.trans (by simp))

@[simp] theorem Ctx.vars_varsCtx (V : List Var) : Ctx.vars (varsCtx V) = (V : Multiset Var) := by
  simp [Ctx.vars, varsCtx, Multiset.filterMap_coe, List.filterMap_map, Function.comp_def]

theorem Binder.owned_eq (xs : List Binder) : Binder.owned xs = varsCtx (Binder.ownedList xs) := by
  simp [Binder.owned, varsCtx, Binder.ownedList, List.map_map, Function.comp_def]

theorem Binder.scalars_eq (xs : List Binder) :
    Binder.scalars xs = (Binder.scalarList xs).toFinset := rfl

theorem Binder.ownedSet_eq (xs : List Binder) :
    Binder.ownedSet xs = (Binder.ownedList xs).toFinset := rfl

theorem creditsOk_zeros : ∀ (C : List Nat) (A : Nat), (∀ c ∈ C, c = 0) → creditsOk C [] A = true
  | [], A, _ => by simp [creditsOk]
  | c :: C, A, h => by
    obtain rfl : c = 0 := h c (by simp)
    simp only [creditsOk]
    exact creditsOk_zeros C A (fun c hc => h c (by simp [hc]))

theorem borrowArgB_sound {cfg : Cfg} {U Δ : List Var} {v : Val} (h : borrowArgB cfg U Δ v = true) :
    BorrowArg cfg U.toFinset Δ.toFinset v := by
  cases v <;> simp_all [borrowArgB, BorrowArg]

theorem scalarArgB_sound {U Δ : List Var} {v : Val} (h : scalarArgB U Δ v = true) :
    ScalarArg U.toFinset Δ.toFinset v := by
  cases v <;> simp_all [scalarArgB, ScalarArg]

mutual
theorem check_sound {cfg : Cfg} : ∀ {U Δ V : List Var} {C : List Nat} {A : Nat} {e : Expr},
    check cfg U Δ V C A e = true → Wf cfg U.toFinset Δ.toFinset (ctxOf V C A) e
  | U, Δ, V, C, A, e, h => by
    unfold check at h
    split at h
    · -- ret
      rename_i vs
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨hpl, hperm⟩, hok⟩ := h
      have w := Wf.supply (cfg := cfg) C _ A _ hok (Wf.tuple (vals_sound U Δ vs hpl))
      refine Wf.cast ?_ w
      rw [ctxOf_eq, varsCtx_perm hperm]
    · -- call
      rename_i f ys e
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem,
        List.all_eq_true] at h
      obtain ⟨⟨⟨hf, hys⟩, hn⟩, he⟩ := h
      have w := Wf.call (cfg := cfg) (U := U.toFinset) (Δ := Δ.toFinset) f ys e hf
        (fun y hy => borrowArgB_sound (hys y hy)) (check_sound he)
      refine Wf.cast ?_ w
      simp only [ctxOf_eq, add_assoc, ← Multiset.replicate_add]
      congr 3
      omega
    · -- app
      rename_i y e
      simp only [Bool.and_eq_true, List.contains_iff_mem] at h
      exact Wf.bapp y e (List.mem_toFinset.mpr h.1) (check_sound h.2)
    · -- let
      rename_i xs e1 e2
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨hA, hfr⟩, h1⟩, h2⟩ := h
      have w1 := check_sound h1
      have w2 := check_sound h2
      have hfr' := freshB_sound (C.diff (C.bagInter (e1.demand cfg).1))
        (A - ((e1.demand cfg).2 + ((e1.demand cfg).1.diff (C.bagInter (e1.demand cfg).1)).length))
        hfr
      have hV : V.Perm (V.filter (fun x => e1.fv.contains x && !e2.fv.contains x) ++
          V.filter (fun x => e1.fv.contains x && e2.fv.contains x) ++
          V.filter (fun x => !e1.fv.contains x)) :=
        perm_filter3 (fun x => e1.fv.contains x) (fun x => e2.fv.contains x) V
      have hΓ2 : (varsCtx (V.filter (fun x => e1.fv.contains x && e2.fv.contains x))).OnlyVars := by
        intro r hr
        simp only [varsCtx, Multiset.mem_coe, List.mem_map] at hr
        obtain ⟨x, _, rfl⟩ := hr
        exact ⟨x, rfl⟩
      have p1 : Wf cfg U.toFinset (Δ.toFinset ∪ (varsCtx (V.filter
          (fun x => e1.fv.contains x && e2.fv.contains x))).vars.toFinset)
          (ctxOf (V.filter (fun x => e1.fv.contains x && !e2.fv.contains x))
            (C.bagInter (e1.demand cfg).1)
            ((e1.demand cfg).2 + ((e1.demand cfg).1.diff (C.bagInter (e1.demand cfg).1)).length))
          e1 := by
        convert w1 using 2
        simp [List.toFinset_append]
      have p2 := w2
      rw [List.toFinset_append, ← Binder.scalars_eq] at p2
      have p2' := Wf.cast (Γ' := varsCtx (V.filter (fun x => e1.fv.contains x && e2.fv.contains x))
        + ctxOf (V.filter (fun x => !e1.fv.contains x)) _ _ + Binder.owned xs)
        (by rw [Binder.owned_eq]; ms_abel) p2
      have p3 : Binder.Fresh xs U.toFinset Δ.toFinset
          (varsCtx (V.filter (fun x => e1.fv.contains x && e2.fv.contains x))
            + ctxOf (V.filter (fun x => !e1.fv.contains x)) (C.diff (C.bagInter (e1.demand cfg).1))
        (A - ((e1.demand cfg).2 + ((e1.demand cfg).1.diff (C.bagInter (e1.demand cfg).1)).length)))
          := by
        refine (congrArg (Binder.Fresh xs U.toFinset Δ.toFinset) ?_).mp hfr'
        ms_abel
      have := Wf.letIn _ _ _ xs e1 e2 hΓ2 p1 p2' p3
      refine Wf.cast ?_ this
      conv_rhs => rw [ctxOf_eq V, varsCtx_perm hV, creditsCtx_split C (e1.demand cfg).1]
      rw [← Nat.add_sub_cancel' hA, Multiset.replicate_add]
      simp only [Nat.add_sub_cancel_left]
      ms_abel
    · -- bmatch
      rename_i y bs
      simp only [Bool.and_eq_true, Bool.or_eq_true, List.contains_iff_mem] at h
      have hb := checkB_sound h.2
      refine Wf.bmatch y bs ?_ (fun b hb' => (hb b hb').1) (fun b hb' => (hb b hb').2)
      simpa using h.1
    · -- dmatch
      rename_i x bs
      simp only [Bool.and_eq_true, List.contains_iff_mem] at h
      have hb := checkD_sound h.2
      have w := Wf.dmatch (cfg := cfg) (U := U.toFinset) (Δ := Δ.toFinset) x bs
        (fun b hb' => (hb b hb').1) (fun b hb' => (hb b hb').2)
      refine Wf.cast ?_ w
      rw [ctxOf_eq, ctxOf_eq, varsCtx_perm (List.perm_cons_erase h.1)]
      ms_abel
    · -- drop
      rename_i x e
      simp only [Bool.and_eq_true, List.contains_iff_mem] at h
      have w := Wf.drop (cfg := cfg) x h.1.1 (check_sound h.2)
      refine Wf.cast ?_ w
      rw [ctxOf_eq, ctxOf_eq, varsCtx_perm (List.perm_cons_erase h.1.2)]
      ms_abel
    · -- free
      rename_i k e
      simp only [Bool.and_eq_true, List.contains_iff_mem, decide_eq_true_eq] at h
      have w := Wf.free (cfg := cfg) k h.1.1.1 h.1.1.2 (check_sound h.2)
      refine Wf.cast ?_ w
      rw [ctxOf_eq, ctxOf_eq, creditsCtx_perm (List.perm_cons_erase h.1.2)]
      ms_abel
    · -- prim
      rename_i op vs
      simp only [Bool.and_eq_true, List.all_eq_true, List.isEmpty_iff, beq_iff_eq] at h
      obtain ⟨⟨hvs, rfl⟩, hC⟩ := h
      have w := Wf.prim (cfg := cfg) (U := U.toFinset) (Δ := Δ.toFinset) op vs
        (fun v hv => scalarArgB_sound (hvs v hv))
      have := Wf.supply C [] A 0 (creditsOk_zeros C A hC) (by simpa using w)
      simpa [ctxOf_eq] using this
    · simp at h
theorem checkB_sound {cfg : Cfg} :
    ∀ {U Δ V : List Var} {C : List Nat} {A : Nat} {bs : List Branch},
    checkB cfg U Δ V C A bs = true → ∀ b ∈ bs,
      Binder.Fresh b.binders U.toFinset Δ.toFinset (ctxOf V C A) ∧
      Wf cfg (U.toFinset ∪ Binder.scalars b.binders)
        (Δ.toFinset ∪ Binder.ownedSet b.binders) (ctxOf V C A) b.body
  | _, _, _, _, _, [], _ => by simp
  | U, Δ, V, C, A, .mk c xs e :: bs, h => by
    simp only [checkB, Bool.and_eq_true] at h
    obtain ⟨⟨hfr, he⟩, hbs⟩ := h
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · refine ⟨freshB_sound C A hfr, ?_⟩
      have w := check_sound he
      simp only [List.toFinset_append] at w
      exact w
    · exact checkB_sound hbs b hb
theorem checkD_sound {cfg : Cfg} :
    ∀ {U Δ V : List Var} {C : List Nat} {A : Nat} {bs : List Branch},
    checkD cfg U Δ V C A bs = true → ∀ b ∈ bs,
      Binder.Fresh b.binders U.toFinset Δ.toFinset (ctxOf V C A) ∧
      Wf cfg (U.toFinset ∪ Binder.scalars b.binders) Δ.toFinset
        (ctxOf V C A + Binder.owned b.binders + {Res.credit b.binders.length}) b.body
  | _, _, _, _, _, [], _ => by simp
  | U, Δ, V, C, A, .mk c xs e :: bs, h => by
    simp only [checkD, Bool.and_eq_true] at h
    obtain ⟨⟨hfr, he⟩, hbs⟩ := h
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · refine ⟨freshB_sound C A hfr, ?_⟩
      have w := check_sound he
      simp only [List.toFinset_append] at w
      refine Wf.cast ?_ w
      simp only [Branch.binders, Binder.owned_eq]
      ms_abel
    · exact checkD_sound hbs b hb
end

/-- A successful check of a function proves it well-formed (`deffun`). -/
theorem FunDef.check_sound {sig : Sig} {fd : FunDef} (h : fd.check sig = true) :
    fd.Wf sig := by
  simp only [FunDef.check, Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨h.1, ?_⟩
  have w := FIPNamed.check_sound h.2
  rw [List.toFinset_append, ← Binder.scalars_eq, ← Binder.scalars_eq, ← Binder.ownedSet_eq] at w
  refine Wf.cast ?_ w
  simp [FunDef.ownedCtx, ctxOf_eq, Binder.owned_eq]

/-- A successful check of a signature proves `⊩ Σ`. -/
theorem Sig.check_sound {sig : Sig} (h : sig.check = true) : sig.Wf := by
  intro fd hfd hne
  have := List.all_eq_true.mp h fd hfd
  simp only [Bool.or_eq_true, beq_iff_eq] at this
  rcases this with h' | h'
  · exact absurd h' hne
  · exact FunDef.check_sound h'

end FIPNamed
