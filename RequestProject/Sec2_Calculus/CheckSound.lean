module

public import RequestProject.Sec2_Calculus.Check

@[expose] public section

/- ══════════════════ PAPER sec. 2.2 START: FIP: Fully In-Place: an executable checker for the rules (the paper describes the check only in prose) (PDF pp. 9-11) ══════════════════
   `Sig.check_sound`: if the checker accepts a signature, then `||- Sigma` holds. -/

/-!
# Soundness of the FIP checker

`check_sound`: if `check cfg U Δ V C A e = true` then `Δ | V, C, ⋄^A ⊢ e` is derivable.
Consequently `FunDef.check_sound` and `Sig.check_sound` turn a successful (decidable)
check into a proof of `FunDef.Wf` / `Sig.Wf`.
-/

namespace FIP

variable {n : Nat}

/-- The reuse credits `C` as an environment. -/
def creditsCtx {n : Nat} (C : List Nat) : Ctx n :=
  ((C.map Res.credit : List (Res n)) : Multiset (Res n))

/-- The variables `V` as an environment. -/
def varsCtx {n : Nat} (V : List (Var n)) : Ctx n :=
  ((V.map Res.var : List (Res n)) : Multiset (Res n))

@[simp] theorem creditsCtx_nil : creditsCtx (n := n) [] = 0 := rfl
@[simp] theorem creditsCtx_cons (c : Nat) (C : List Nat) :
    creditsCtx (n := n) (c :: C) = {Res.credit c} + creditsCtx C := by
  simp [creditsCtx, ← Multiset.cons_coe, Multiset.singleton_add]
@[simp] theorem creditsCtx_append (C D : List Nat) :
    creditsCtx (n := n) (C ++ D) = creditsCtx C + creditsCtx D := by
  simp [creditsCtx]
@[simp] theorem varsCtx_nil : varsCtx (n := n) [] = 0 := rfl
@[simp] theorem varsCtx_cons (x : Var n) (V : List (Var n)) :
    varsCtx (x :: V) = {Res.var x} + varsCtx V := by
  simp [varsCtx, ← Multiset.cons_coe, Multiset.singleton_add]
@[simp] theorem varsCtx_append (V W : List (Var n)) :
    varsCtx (V ++ W) = varsCtx V + varsCtx W := by
  simp [varsCtx]
theorem creditsCtx_perm {C D : List Nat} (h : C.Perm D) :
    creditsCtx (n := n) C = creditsCtx D :=
  Multiset.coe_eq_coe.mpr (h.map _)
theorem varsCtx_perm {V W : List (Var n)} (h : V.Perm W) : varsCtx V = varsCtx W :=
  Multiset.coe_eq_coe.mpr (h.map _)

theorem ctxOf_eq (V : List (Var n)) (C : List Nat) (A : Nat) :
    ctxOf V C A = varsCtx V + creditsCtx C + Multiset.replicate A Res.alloc := rfl

/-- Normalize an equation between environments and close it by commutativity. -/
macro "ms_abel" : tactic =>
  `(tactic| (
    simp only [creditsCtx_cons, creditsCtx_append, creditsCtx_nil, varsCtx_cons,
      varsCtx_append, varsCtx_nil, ctxOf_eq, Multiset.replicate_succ,
      ← Multiset.singleton_add, Multiset.cons_zero, add_zero, zero_add]
    abel))

/-! ## Weakening of environments -/

theorem Ctx.shift_add (k : Nat) (Γ Δ : Ctx n) : (Γ + Δ).shift k = Γ.shift k + Δ.shift k :=
  Multiset.map_add _ _ _

@[simp] theorem varsCtx_shiftL (k : Nat) (V : List (Var n)) :
    varsCtx (Vars.shiftL k V) = (varsCtx V).shift k := by
  simp [varsCtx, Ctx.shift, Res.shift, Function.comp_def]

@[simp] theorem creditsCtx_shift (k : Nat) (C : List Nat) :
    (creditsCtx (n := n) C).shift k = creditsCtx C := by
  simp [creditsCtx, Ctx.shift, Res.shift, Function.comp_def]

@[simp] theorem replicate_alloc_shift (k A : Nat) :
    Ctx.shift k (Multiset.replicate A (Res.alloc : Res n)) = Multiset.replicate A Res.alloc := by
  simp [Ctx.shift, Res.shift, Multiset.map_replicate]

theorem toFinset_shiftL (k : Nat) (l : List (Var n)) :
    (Vars.shiftL k l).toFinset = Vars.shift k l.toFinset := by
  ext x
  simp [Vars.shift, Var.shiftEmb]

theorem varsCtx_select {N : Nat} (xs : List Bool) (f : Fin xs.length → Var N) :
    varsCtx (Binder.select xs false f) = Binder.ownedAt xs f := rfl

/-! ## Casting and credits -/

theorem Wf.cast {cfg : Cfg} {U Δ : Finset (Var n)} {Γ Γ' : Ctx n} {e : Expr n} (h : Γ = Γ')
    (w : Wf cfg U Δ Γ e) : Wf cfg U Δ Γ' e := h ▸ w

theorem Wf.weakenN {cfg : Cfg} {U Δ : Finset (Var n)} {Γ : Ctx n} {e : Expr n} (A : Nat)
    (w : Wf cfg U Δ Γ e) : Wf cfg U Δ (Γ + Multiset.replicate A Res.alloc) e := by
  induction A with
  | zero => simpa using w
  | succ n ih =>
    refine Wf.cast ?_ (Wf.weaken ih)
    rw [Multiset.replicate_succ, ← Multiset.singleton_add]
    abel

/-- Paying for demanded reuse credits `D` with available credits `C` and `A` allocation
    credits. -/
theorem Wf.supply {cfg : Cfg} {U Δ : Finset (Var n)} {e : Expr n} :
    ∀ (C D : List Nat) (A : Nat) (Γ : Ctx n), creditsOk C D A = true →
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

theorem WfVal.cast {U Δ : Finset (Var n)} {Γ Γ' : Ctx n} {v : Val n} (h : Γ = Γ')
    (w : WfVal U Δ Γ v) : WfVal U Δ Γ' v := h ▸ w

theorem WfVals.cast' {U Δ : Finset (Var n)} {Γ : Ctx n} {vs : List (Val n)}
    (w : WfVals U Δ Γ vs) {Γ' : Ctx n} (h : Γ = Γ') : WfVals U Δ Γ' vs := h ▸ w

mutual
theorem val_sound (U Δ : List (Var n)) : ∀ v : Val n, Val.plain v = true →
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
  | .lit k, _ => by simpa [Val.ownedUses, Val.credits] using WfVal.lit k
  | .fn f, h => by simp [Val.plain] at h
theorem vals_sound (U Δ : List (Var n)) :
    ∀ vs : List (Val n), Val.plainList vs = true →
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

theorem creditsCtx_eq_map (C : List Nat) :
    creditsCtx (n := n) C = Multiset.map Res.credit (C : Multiset Nat) := by
  simp [creditsCtx]

theorem creditsCtx_split (C D : List Nat) :
    creditsCtx (n := n) C =
      creditsCtx (C.bagInter D) + creditsCtx (C.diff (C.bagInter D)) := by
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

@[simp] theorem Ctx.vars_varsCtx (V : List (Var n)) :
    Ctx.vars (varsCtx V) = (V : Multiset (Var n)) := by
  simp [Ctx.vars, varsCtx, Multiset.filterMap_coe, List.filterMap_map, Function.comp_def]

theorem creditsOk_zeros : ∀ (C : List Nat) (A : Nat), (∀ c ∈ C, c = 0) → creditsOk C [] A = true
  | [], A, _ => by simp [creditsOk]
  | c :: C, A, h => by
    obtain rfl : c = 0 := h c (by simp)
    simp only [creditsOk]
    exact creditsOk_zeros C A (fun c hc => h c (by simp [hc]))

theorem borrowArgB_sound {cfg : Cfg} {U Δ : List (Var n)} {v : Val n}
    (h : borrowArgB cfg U Δ v = true) : BorrowArg cfg U.toFinset Δ.toFinset v := by
  cases v <;> simp_all [borrowArgB, BorrowArg]

theorem scalarArgB_sound {U Δ : List (Var n)} {v : Val n} (h : scalarArgB U Δ v = true) :
    ScalarArg U.toFinset Δ.toFinset v := by
  cases v <;> simp_all [scalarArgB, ScalarArg]

/-- The scalar environment of a body under binders `xs`. -/
theorem toFinset_scalars (xs : List Bool) (U : List (Var n)) :
    (Vars.shiftL xs.length U ++ Binder.scalarList xs).toFinset =
      Vars.shift xs.length U.toFinset ∪ Binder.scalars xs := by
  rw [List.toFinset_append, toFinset_shiftL]
  rfl

theorem toFinset_ownedB (xs : List Bool) (Δ : List (Var n)) :
    (Vars.shiftL xs.length Δ ++ Binder.ownedList xs).toFinset =
      Vars.shift xs.length Δ.toFinset ∪ Binder.ownedSet xs := by
  rw [List.toFinset_append, toFinset_shiftL]
  rfl

theorem ctxOf_shift (xs : List Bool) (V : List (Var n)) (C : List Nat) (A : Nat) :
    ctxOf (Vars.shiftL xs.length V ++ Binder.ownedList xs) C A =
      (ctxOf V C A).shift xs.length + Binder.owned xs := by
  rw [ctxOf_eq, ctxOf_eq, varsCtx_append, varsCtx_shiftL, varsCtx_select, Ctx.shift_add,
    Ctx.shift_add, creditsCtx_shift, replicate_alloc_shift]
  abel

mutual
theorem check_sound {cfg : Cfg} : ∀ {n : Nat} {U Δ V : List (Var n)} {C : List Nat} {A : Nat}
    {e : Expr n}, check cfg U Δ V C A e = true → Wf cfg U.toFinset Δ.toFinset (ctxOf V C A) e
  | n, U, Δ, V, C, A, e, h => by
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
      obtain ⟨⟨hA, h1⟩, h2⟩ := h
      have w1 := check_sound h1
      have w2 := check_sound h2
      set f2 := (e2.fv).filterMap (Var.unshift xs.length)
      have hV : V.Perm (V.filter (fun x => e1.fv.contains x && !f2.contains x) ++
          V.filter (fun x => e1.fv.contains x && f2.contains x) ++
          V.filter (fun x => !e1.fv.contains x)) :=
        perm_filter3 (fun x => e1.fv.contains x) (fun x => f2.contains x) V
      have hΓ2 : (varsCtx (V.filter (fun x => e1.fv.contains x && f2.contains x))).OnlyVars := by
        intro r hr
        simp only [varsCtx, Multiset.mem_coe, List.mem_map] at hr
        obtain ⟨x, _, rfl⟩ := hr
        exact ⟨x, rfl⟩
      have p1 : Wf cfg U.toFinset (Δ.toFinset ∪ (varsCtx (V.filter
          (fun x => e1.fv.contains x && f2.contains x))).vars.toFinset)
          (ctxOf (V.filter (fun x => e1.fv.contains x && !f2.contains x))
            (C.bagInter (e1.demand cfg).1)
            ((e1.demand cfg).2 + ((e1.demand cfg).1.diff (C.bagInter (e1.demand cfg).1)).length))
          e1 := by
        convert w1 using 2
        simp [List.toFinset_append]
      rw [toFinset_scalars xs, toFinset_shiftL, ctxOf_shift] at w2
      have p2' := Wf.cast (Γ' := (varsCtx (V.filter (fun x => e1.fv.contains x && f2.contains x))
        + ctxOf (V.filter (fun x => !e1.fv.contains x)) _ _).shift xs.length + Binder.owned xs)
        (by congr 1; congr 1; ms_abel) w2
      have := Wf.letIn _ _ _ xs e1 e2 hΓ2 p1 p2'
      refine Wf.cast ?_ this
      conv_rhs => rw [ctxOf_eq V, varsCtx_perm hV, creditsCtx_split C (e1.demand cfg).1]
      rw [← Nat.add_sub_cancel' hA, Multiset.replicate_add]
      simp only [Nat.add_sub_cancel_left]
      ms_abel
    · -- bmatch
      rename_i y bs
      simp only [Bool.and_eq_true, Bool.or_eq_true, List.contains_iff_mem] at h
      have hb := checkB_sound h.2
      refine Wf.bmatch y bs ?_ (fun b hb' => hb b hb')
      simpa using h.1
    · -- dmatch
      rename_i x bs
      simp only [Bool.and_eq_true, List.contains_iff_mem] at h
      have hb := checkD_sound h.2
      have w := Wf.dmatch (cfg := cfg) (U := U.toFinset) (Δ := Δ.toFinset) x bs
        (fun b hb' => hb b hb')
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
    ∀ {n : Nat} {U Δ V : List (Var n)} {C : List Nat} {A : Nat} {bs : Branches n},
    checkB cfg U Δ V C A bs = true → ∀ b ∈ bs.toList,
      Wf cfg (Vars.shift b.binders.length U.toFinset ∪ Binder.scalars b.binders)
        (Vars.shift b.binders.length Δ.toFinset ∪ Binder.ownedSet b.binders)
        ((ctxOf V C A).shift b.binders.length) b.body
  | _, _, _, _, _, _, .nil, _ => by simp
  | n, U, Δ, V, C, A, .cons c xs e bs, h => by
    simp only [checkB, Bool.and_eq_true] at h
    obtain ⟨he, hbs⟩ := h
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · have w := check_sound he
      rw [toFinset_scalars xs, toFinset_ownedB] at w
      refine Wf.cast ?_ w
      rw [ctxOf_eq, ctxOf_eq, varsCtx_shiftL, Ctx.shift_add, Ctx.shift_add, creditsCtx_shift,
        replicate_alloc_shift]
    · exact checkB_sound hbs b hb
theorem checkD_sound {cfg : Cfg} :
    ∀ {n : Nat} {U Δ V : List (Var n)} {C : List Nat} {A : Nat} {bs : Branches n},
    checkD cfg U Δ V C A bs = true → ∀ b ∈ bs.toList,
      Wf cfg (Vars.shift b.binders.length U.toFinset ∪ Binder.scalars b.binders)
        (Vars.shift b.binders.length Δ.toFinset)
        ((ctxOf V C A).shift b.binders.length + Binder.owned b.binders +
          {Res.credit b.binders.length}) b.body
  | _, _, _, _, _, _, .nil, _ => by simp
  | n, U, Δ, V, C, A, .cons c xs e bs, h => by
    simp only [checkD, Bool.and_eq_true] at h
    obtain ⟨he, hbs⟩ := h
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · have w := check_sound he
      rw [toFinset_scalars xs, toFinset_shiftL] at w
      refine Wf.cast ?_ w
      rw [ctxOf_eq, ctxOf_eq, varsCtx_append, varsCtx_shiftL, varsCtx_select, Ctx.shift_add,
        Ctx.shift_add, creditsCtx_shift, replicate_alloc_shift, creditsCtx_append]
      simp only [creditsCtx_cons, creditsCtx_nil, add_zero]
      abel
    · exact checkD_sound hbs b hb
end

/-- A successful check of a function proves it well-formed (`deffun`). -/
theorem FunDef.check_sound {sig : Sig} {fd : FunDef} (h : fd.check sig = true) :
    fd.Wf sig := by
  have w := FIP.check_sound h
  rw [List.toFinset_append] at w
  refine Wf.cast ?_ w
  simp [FunDef.ownedCtx, ctxOf_eq, varsCtx_select]

/-- A successful check of a signature proves `⊩ Σ`. -/
theorem Sig.check_sound {sig : Sig} (h : sig.check = true) : sig.Wf := by
  intro fd hfd hne
  have := List.all_eq_true.mp h fd hfd
  simp only [Bool.or_eq_true, beq_iff_eq] at this
  rcases this with h' | h'
  · exact absurd h' hne
  · exact FunDef.check_sound h'

end FIP

/- ══════════════════ PAPER sec. 2.2 END: FIP: Fully In-Place: an executable checker for the rules (the paper describes the check only in prose) ══════════════════ -/
