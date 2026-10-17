module

public import RequestProject.AppC_StackBound.StackRank

@[expose] public section

/-!
# Frames of the store semantics (Appendix C)

`Frame groups D i M e` says that `e` is the current state of an activation of a function of
rank `i` in which all function values have rank `< M`: its stack depth is at most `D`,
function values only occur in borrowed positions, calls to the own group are tail calls,
and all called functions have rank `≤ i`.

Steps of the store semantics other than calls keep an expression a frame
(`Frame.head_step`, `Frame.val_step`; **Lemmas 28 and 32**), and a call yields a frame for
the body of the callee (`Frame.call`, `Frame.app`).
-/

namespace FIP

variable {sig : Sig} {fbip : Bool}

/-- The store contains no function values, and its fields are atomic (as in the paper's
    stores, whose fields are locations). -/
def Store.NoFn (S : Store) : Prop :=
  ∀ x c as, Cell.bind x c as ∈ S → ∀ a ∈ as, a.Atomic ∧ Val.funs a = []

/-- The state `e` of an activation of a function of rank `i` in which every function value
    has rank `< M`. -/
structure Frame (groups : List (List FName)) (D i M : Nat) (e : Expr 0) : Prop where
  lt : i < groups.length
  le : M ≤ groups.length
  sdepth : e.sdepth ≤ D
  bp : Expr.BP (fun _ => False) e
  tail : Expr.TailC (fun g => rank groups g = i) e
  calls : ∀ g ∈ e.calls, rank groups g ≤ i
  fns : ∀ g ∈ e.fns, rank groups g < M

/-! ## Auxiliary facts -/

theorem Val.mem_funsList {g : FName} {vs : List (Val 0)} :
    g ∈ Val.funsList vs ↔ ∃ v ∈ vs, g ∈ Val.funs v := by
  induction vs with
  | nil => simp [Val.funsList]
  | cons v vs ih => simp [Val.funsList, ih]

theorem Subst.inst_ids_mem {k : Nat} {as : List (Val 0)} (hl : as.length = k)
    (i : Fin (0 + k)) : Subst.inst k as (Subst.ids 0) i ∈ as := by
  rw [Subst.inst_lt _ _ _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
  exact List.getElem_mem _

theorem Expr.atomArgs_ret {r : Expr 0} (h : r.AtomArgs) : ∃ vs, r = .ret vs := by
  cases r with
  | ret vs => exact ⟨vs, rfl⟩
  | _ => simp [Expr.AtomArgs] at h

theorem VCtx.plug_ctor (V : VCtx) (c : CName) (as : List (Val 0)) :
    ∃ c' as', V.plug (.ctor c as) = .ctor c' as' := by
  cases V with
  | hole => exact ⟨c, as, rfl⟩
  | ctor c' done V rest => exact ⟨c', _, rfl⟩

theorem VCtx.funs_plug_sub (V : VCtx) (v w : Val 0) :
    ∀ g ∈ Val.funs (V.plug w), g ∈ Val.funs (V.plug v) ∨ g ∈ Val.funs w := by
  induction V with
  | hole => intro g hg; exact .inr hg
  | ctor c done V rest ih =>
    intro g hg
    simp only [VCtx.plug, Val.funs, Val.mem_funsList, List.mem_append, List.mem_cons] at hg ⊢
    obtain ⟨u, hu, hg⟩ := hg
    rcases hu with hu | rfl | hu
    · exact .inl ⟨u, .inl hu, hg⟩
    · rcases ih g hg with h | h
      · exact .inl ⟨_, .inr (.inl rfl), h⟩
      · exact .inr h
    · exact .inl ⟨u, .inr (.inr hu), hg⟩

theorem VCtx.funs_eq_nil (V : VCtx) (v : Val 0) (h : Val.funs (V.plug v) = []) :
    Val.funs v = [] := by
  induction V with
  | hole => exact h
  | ctor c done V rest ih =>
    apply ih
    simp only [VCtx.plug, Val.funs] at h
    exact Val.funsList_eq_nil.mp h _ (by simp)

theorem Expr.bp_nil_of_plug {E : ECtx 0} {r : Expr 0} (h : Expr.BP (fun _ => False) (E.plug r))
    (hr : ∀ vs, r ≠ .ret vs) : Expr.BP (fun _ => False) r := by
  rcases ECtx.bp_plug_inv E r h with h | h
  · exact h
  · obtain ⟨vs, rfl⟩ := Expr.atomArgs_ret h
    exact absurd rfl (hr vs)

/-! ## Steps other than calls (Lemmas 28 and 32) -/

/-- What a head reduction other than a call does to the measures of a frame. -/
theorem SHead.local_facts {S S' : Store} {r r' : Expr 0} (h : SHead sig fbip S r S' r')
    (hS : S.NoFn) (hc : ∀ f a b, r ≠ .call f a b) (ha : ∀ a b, r ≠ .app a b) :
    r'.sdepth ≤ r.sdepth ∧ (∀ g ∈ r'.calls, g ∈ r.calls) ∧ (∀ g ∈ r'.fns, g ∈ r.fns) ∧
      (Expr.BP (fun _ => False) r → Expr.BP (fun _ => False) r') ∧ (∀ P, Expr.TailC P r → Expr.TailC P r') ∧
      (∀ vs, r ≠ .ret vs) := by
  cases h with
  | letIn S xs as e hat hlen =>
    simp only [Expr.inst]
    refine ⟨?_, ?_, ?_, ?_, ?_, by simp⟩
    · rw [Expr.sdepth_subst]; simp only [Expr.sdepth]; omega
    · intro g hg; rw [Expr.calls_subst] at hg; simp [Expr.calls, hg]
    · intro g hg
      rcases Expr.fns_subst _ _ g hg with hg | hg
      · simp [Expr.fns, hg]
      · obtain ⟨i, hg⟩ := Subst.mem_fns.mp hg
        simp only [Expr.fns, List.mem_append, Val.mem_funsList]
        exact .inl ⟨_, Subst.inst_ids_mem hlen.symm i, hg⟩
    · intro hb
      simp only [Expr.BP] at hb
      refine Expr.bp_subst _ _ _ (fun i => hat _ (Subst.inst_ids_mem hlen.symm i))
        (fun i _ => (hb.1 _ (Subst.inst_ids_mem hlen.symm i)).1) hb.2
    · intro P ht
      cases ht with
      | base _ hb =>
        exact .base _ fun g hg => hb g (by rw [Expr.calls_subst] at hg; simp [Expr.calls, hg])
      | letIn _ _ _ _ ht => exact ht.subst _
  | call => exact absurd rfl (hc _ _ _)
  | app => exact absurd rfl (ha _ _)
  | bmatch S y c zs bs b hmem hfind =>
    have hb := (Branches.find_mem hfind).1
    have hlenb := (Branches.find_mem hfind).2.2.symm
    simp only [Expr.inst]
    have hz : ∀ z ∈ zs, z.Atomic ∧ Val.funs z = [] := hS _ _ _ hmem
    refine ⟨?_, ?_, ?_, ?_, ?_, by simp⟩
    · rw [Expr.sdepth_subst]
      have := Expr.sdepthB_mem hb
      simp only [Expr.sdepth] at this ⊢; omega
    · intro g hg; rw [Expr.calls_subst] at hg
      simp only [Expr.calls, List.mem_append]
      exact .inr (Expr.callsB_mem hb g hg)
    · intro g hg
      rcases Expr.fns_subst _ _ g hg with hg | hg
      · simp only [Expr.fns, List.mem_append]; exact .inr (Expr.fnsB_mem hb g hg)
      · obtain ⟨i, hg⟩ := Subst.mem_fns.mp hg
        rw [(hz _ (Subst.inst_ids_mem hlenb i)).2] at hg; simp at hg
    · intro hbp
      simp only [Expr.BP] at hbp
      have := Expr.BPB_iff.mp hbp.2 _ hb
      exact Expr.bp_subst _ _ _ (fun i => (hz _ (Subst.inst_ids_mem hlenb i)).1)
        (fun i _ => (hz _ (Subst.inst_ids_mem hlenb i)).2) this
    · intro P ht
      cases ht with
      | base _ hb' =>
        refine .base _ fun g hg => hb' g ?_
        rw [Expr.calls_subst] at hg
        simp only [Expr.calls, List.mem_append]
        exact .inr (Expr.callsB_mem hb g hg)
      | bmatch _ _ _ ht => exact (ht _ hb).subst _
  | dmatch S x c zs bs b hfind =>
    have hb := (Branches.find_mem hfind).1
    have hlenb := (Branches.find_mem hfind).2.2.symm
    simp only [Expr.inst]
    have hz : ∀ z ∈ zs, z.Atomic ∧ Val.funs z = [] := hS x c zs (by simp)
    refine ⟨?_, ?_, ?_, ?_, ?_, by simp⟩
    · rw [Expr.sdepth_subst]
      have := Expr.sdepthB_mem hb
      simp only [Expr.sdepth] at this ⊢; omega
    · intro g hg; rw [Expr.calls_subst] at hg
      simp only [Expr.calls, List.mem_append]
      exact .inr (Expr.callsB_mem hb g hg)
    · intro g hg
      rcases Expr.fns_subst _ _ g hg with hg | hg
      · simp only [Expr.fns, List.mem_append]; exact .inr (Expr.fnsB_mem hb g hg)
      · obtain ⟨i, hg⟩ := Subst.mem_fns.mp hg
        rw [(hz _ (Subst.inst_ids_mem hlenb i)).2] at hg; simp at hg
    · intro hbp
      simp only [Expr.BP] at hbp
      have := Expr.BPB_iff.mp hbp.2 _ hb
      exact Expr.bp_subst _ _ _ (fun i => (hz _ (Subst.inst_ids_mem hlenb i)).1)
        (fun i _ => (hz _ (Subst.inst_ids_mem hlenb i)).2) this
    · intro P ht
      cases ht with
      | base _ hb' =>
        refine .base _ fun g hg => hb' g ?_
        rw [Expr.calls_subst] at hg
        simp only [Expr.calls, List.mem_append]
        exact .inr (Expr.callsB_mem hb g hg)
      | dmatch _ _ _ ht => exact (ht _ hb).subst _
  | drop S x c zs e _ =>
    have hz : ∀ z ∈ zs, z.Atomic ∧ Val.funs z = [] := hS x c zs (by simp)
    refine ⟨?_, ?_, ?_, ?_, ?_, by simp⟩
    · rw [Expr.sdepth_drops]; simp [Expr.sdepth]
    · intro g hg; rw [Expr.calls_drops] at hg; simpa [Expr.calls] using hg
    · intro g hg; rw [Expr.fns_drops] at hg; simpa [Expr.fns] using hg
    · intro hbp
      simp only [Expr.BP] at hbp
      exact Expr.bp_drops zs (fun z hz' => ⟨(hz z hz').2, by simp⟩) hbp.2
    · intro P ht
      cases ht with
      | base _ hb' =>
        exact .base _ fun g hg => hb' g (by rw [Expr.calls_drops] at hg; simpa [Expr.calls] using hg)
      | drop _ _ ht => exact ht.drops zs
  | free S k e _ =>
    refine ⟨by simp [Expr.sdepth], by simp [Expr.calls], by simp [Expr.fns],
      fun h => by simpa [Expr.BP] using h, ?_, by simp⟩
    intro P ht
    cases ht with
    | base _ hb' => exact .base _ (by simpa [Expr.calls] using hb')
    | free _ _ ht => exact ht
  | prim S op a b =>
    refine ⟨by simp [Expr.sdepth], by simp [Expr.calls], ?_, ?_, ?_, by simp⟩
    · intro g hg; simp [Expr.fns, Val.funsList, boolVal, Val.funs] at hg
    · intro _; simp [Expr.BP, Val.NoB, boolVal, Val.funs, Val.funsList]
    · intro P _; exact .base _ (by simp [Expr.calls])

/-- **Lemmas 28 and 32**: a head reduction other than a call keeps a frame. -/
theorem Frame.head_step {groups : List (List FName)} {D i M : Nat} {E : ECtx 0} {S S' : Store}
    {r r' : Expr 0} (hf : Frame groups D i M (E.plug r)) (hS : S.NoFn)
    (h : SHead sig fbip S r S' r') (hc : ∀ f a b, r ≠ .call f a b) (ha : ∀ a b, r ≠ .app a b) :
    Frame groups D i M (E.plug r') := by
  obtain ⟨hsd, hcl, hfn, hbp, htl, hnr⟩ := h.local_facts hS hc ha
  refine ⟨hf.lt, hf.le, le_trans (ECtx.sdepth_plug_mono E hsd) hf.sdepth, ?_, ?_, ?_, ?_⟩
  · exact ECtx.bp_plug_repl E r r' hf.bp (hbp (Expr.bp_nil_of_plug hf.bp hnr))
  · rcases Expr.TailC.plug_avoid hf.tail with rfl | hav
    · exact htl _ hf.tail
    · exact hf.tail.plug_repl fun g hg => hav g (hcl g hg)
  · intro g hg
    rcases ECtx.calls_plug E r r' g hg with hg | hg
    · exact hf.calls g hg
    · exact hf.calls g (ECtx.calls_sub E r g (hcl g hg))
  · intro g hg
    rcases ECtx.fns_plug E r r' g hg with hg | hg
    · exact hf.fns g hg
    · exact hf.fns g (ECtx.fns_sub E r g (hfn g hg))

theorem SValHead.shape {S S' : Store} {v v' : Val 0} (h : SValHead S v S' v') :
    (∃ c as, v = .ctor c as) ∧ ∃ x, v' = .var (.loc x) := by
  cases h <;> exact ⟨⟨_, _, rfl⟩, ⟨_, rfl⟩⟩

/-- An allocation inside a tuple keeps a frame. -/
theorem Frame.val_step {groups : List (List FName)} {D i M : Nat} {E : ECtx 0} {S S' : Store}
    {r r' : Expr 0} (hf : Frame groups D i M (E.plug r)) (h : ValRed S r S' r') :
    Frame groups D i M (E.plug r') := by
  obtain ⟨done, V, rest, v, v', _, _, hv, rfl, rfl⟩ := h
  obtain ⟨⟨c, as, rfl⟩, ⟨x, rfl⟩⟩ := hv.shape
  have hsub : ∀ g ∈ Val.funsList (done ++ V.plug (.var (.loc x)) :: rest),
      g ∈ Val.funsList (done ++ V.plug (.ctor c as) :: rest) := by
    intro g hg
    simp only [Val.mem_funsList, List.mem_append, List.mem_cons] at hg ⊢
    obtain ⟨u, hu, hg⟩ := hg
    rcases hu with hu | rfl | hu
    · exact ⟨u, .inl hu, hg⟩
    · rcases VCtx.funs_plug_sub V (.ctor c as) _ g hg with h | h
      · exact ⟨_, .inr (.inl rfl), h⟩
      · simp [Val.funs] at h
    · exact ⟨u, .inr (.inr hu), hg⟩
  refine ⟨hf.lt, hf.le, le_trans (ECtx.sdepth_plug_mono E (by simp [Expr.sdepth])) hf.sdepth,
    ?_, hf.tail.plug_repl (by simp [Expr.calls]), ?_, ?_⟩
  · refine ECtx.bp_plug_repl E _ _ hf.bp ?_
    rcases ECtx.bp_plug_inv E _ hf.bp with hb | hb
    · intro u hu
      refine ⟨Val.funsList_eq_nil.mp ?_ u hu, by simp⟩
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro g hg
      obtain ⟨w, hw, hg'⟩ := Val.mem_funsList.mp (hsub g hg)
      rw [(hb w hw).1] at hg'; simp at hg'
    · obtain ⟨c', as', he⟩ := VCtx.plug_ctor V c as
      have := hb (V.plug (.ctor c as)) (by simp)
      rw [he] at this
      exact this.elim
  · intro g hg
    rcases ECtx.calls_plug E _ _ g hg with hg | hg
    · exact hf.calls g hg
    · simp [Expr.calls] at hg
  · intro g hg
    rcases ECtx.fns_plug E (.ret (done ++ V.plug (.ctor c as) :: rest)) _ g hg with hg | hg
    · exact hf.fns g hg
    · exact hf.fns g (ECtx.fns_sub E _ g (by simpa [Expr.fns] using hsub g (by simpa [Expr.fns] using hg)))

/-- Returning a tuple without functions to a frame. -/
theorem Frame.ret {groups : List (List FName)} {D i M : Nat} {F : ECtx 0} {c : Expr 0}
    {vs : List (Val 0)} (hf : Frame groups D i M (F.plug c)) (hvs : ∀ v ∈ vs, Val.funs v = []) :
    Frame groups D i M (F.plug (.ret vs)) := by
  refine ⟨hf.lt, hf.le, le_trans (ECtx.sdepth_plug_mono F (by simp [Expr.sdepth])) hf.sdepth,
    ECtx.bp_plug_repl F c _ hf.bp (fun v hv => ⟨hvs v hv, by simp⟩),
    hf.tail.plug_repl (by simp [Expr.calls]), ?_, ?_⟩
  · intro g hg
    rcases ECtx.calls_plug F c _ g hg with hg | hg
    · exact hf.calls g hg
    · simp [Expr.calls] at hg
  · intro g hg
    rcases ECtx.fns_plug F c _ g hg with hg | hg
    · exact hf.fns g hg
    · simp only [Expr.fns] at hg
      obtain ⟨v, hv, hg⟩ := Val.mem_funsList.mp hg
      rw [hvs v hv] at hg; simp at hg

/-! ## The store has no functions -/

theorem Store.NoFn.step {S S' : Store} {e e' : Expr 0} (hS : S.NoFn) (hbp : Expr.BP (fun _ => False) e)
    (h : SStep sig fbip S e S' e') : S'.NoFn := by
  cases h with
  | head E hh =>
    cases hh with
    | dmatch S0 x c zs bs b hfind =>
      intro y c' as hm
      rcases Multiset.mem_add.mp hm with hm | hm
      · simp at hm
      · exact hS y c' as (Multiset.mem_add.mpr (.inr hm))
    | drop S0 x c zs e _ =>
      intro y c' as hm
      exact hS y c' as (Multiset.mem_add.mpr (.inr hm))
    | free S0 k e _ =>
      intro y c' as hm
      exact hS y c' as (Multiset.mem_add.mpr (.inr hm))
    | _ => exact hS
  | val E done V rest hd hV hv =>
    cases hv with
    | reuse S0 c as x _ hat _ =>
      have hV' : Val.funs (V.plug (.ctor c as)) = [] := by
        rcases ECtx.bp_plug_inv E _ hbp with hb | hb
        · exact (hb (V.plug (.ctor c as)) (by simp)).1
        · obtain ⟨c', as', he⟩ := VCtx.plug_ctor V c as
          have := hb (V.plug (.ctor c as)) (by simp)
          rw [he] at this
          exact this.elim
      have hf := VCtx.funs_eq_nil V _ hV'
      simp only [Val.funs] at hf
      intro y c' as' hm
      rcases Multiset.mem_add.mp hm with hm | hm
      · simp only [Multiset.mem_singleton, Cell.bind.injEq] at hm
        obtain ⟨-, -, rfl⟩ := hm
        exact fun a ha => ⟨hat a ha, Val.funsList_eq_nil.mp hf a ha⟩
      · exact hS y c' as' (Multiset.mem_add.mpr (.inr hm))
    | atom S0 c x _ =>
      intro y c' as' hm
      rcases Multiset.mem_add.mp hm with hm | hm
      · simp only [Multiset.mem_singleton, Cell.bind.injEq] at hm
        obtain ⟨-, -, rfl⟩ := hm
        simp
      · exact hS y c' as' hm

end FIP
