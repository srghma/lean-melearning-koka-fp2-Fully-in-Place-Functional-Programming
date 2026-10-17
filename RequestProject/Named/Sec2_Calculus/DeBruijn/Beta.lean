module

public import RequestProject.Named.Sec2_Calculus.DeBruijn.SimLemmas

@[expose] public section

/-!
# The β-like reducts of the two semantics agree

Instantiating the binders of a closed `let`, branch or function body by closed values
gives the same result in the named and in the de Bruijn representation.  Also: a
resolved signature resolves every function, and finding a branch commutes with
resolution.
-/

namespace FIPNamed

theorem Val.closed_of_mem_toTVals {vs : List Val} {ts : List (TVal 0)}
    (h : Val.toTVals Scope.empty vs = some ts) {v : Val} (hv : v ∈ vs) :
    ∀ s, Var.name s ∉ v.fv := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hv
  have hl := Val.toTVals_length _ _ _ h
  exact Val.closed_of_toTVal_empty (Val.toTVals_getElem _ _ _ h i hi (by omega))

theorem List.lookup_append' {β : Type} (s : String) :
    ∀ (l1 l2 : List (String × β)), (l1 ++ l2).lookup s = (l1.lookup s).or (l2.lookup s)
  | [], l2 => by simp
  | (a, b) :: l1, l2 => by
    simp only [List.cons_append, List.lookup]
    split
    · rfl
    · exact List.lookup_append' s l1 l2

/-- Instantiating the binders of a closed body (of a `let` or of a branch). -/
theorem Expr.toTerm_subst_inst {xs : List Binder} {vs : List Val} {ts : List (TVal 0)}
    {e : Expr} {te : Term (0 + (Binder.flags xs).length)}
    (hvs : Val.toTVals Scope.empty vs = some ts)
    (he : e.toTerm (Scope.empty.extend xs) = some te) (h : ts.length = (Binder.flags xs).length) :
    (e.subst (zipSubst xs vs)).toTerm Scope.empty = some (te.subst (Subst.inst ts h TVal.bvar)) := by
  refine Expr.toTerm_subst ?_ ?_ e te he
  · intro s v hv
    exact Val.closed_of_mem_toTVals hvs (zipSubst_lookup_mem xs vs s v hv)
  · intro s i hi
    rcases Scope.extend_some Scope.empty xs s i hi with ⟨hi', _, _⟩ | ⟨_, _, hΓ⟩
    · have hl := Val.toTVals_length _ _ _ hvs
      have hlk := zipSubst_lookup_of_extend xs vs s Scope.empty i hi hi'
      rw [List.getElem?_eq_getElem (by omega)] at hlk
      simp only [Val.subst, hlk, Option.getD_some, Subst.inst, hi', dif_pos]
      exact Val.toTVals_getElem _ _ _ hvs i _ _
    · simp [Scope.empty] at hΓ

/-- Instantiating the parameters of a function body. -/
theorem Expr.toTerm_subst_args {b o : List Binder} {vs1 vs2 : List Val}
    {ts1 ts2 : List (TVal 0)} {e : Expr}
    {te : Term ((Binder.flags o).length + (Binder.flags b).length)}
    (h1 : Val.toTVals Scope.empty vs1 = some ts1) (h2 : Val.toTVals Scope.empty vs2 = some ts2)
    (he : e.toTerm ((Scope.ofBinders o).extend b) = some te)
    (hl1 : ts1.length = (Binder.flags b).length) (hl2 : ts2.length = (Binder.flags o).length) :
    (e.subst (zipSubst b vs1 ++ zipSubst o vs2)).toTerm Scope.empty =
      some (te.subst (Subst.args ts1 ts2 hl1 hl2)) := by
  have hv1 := Val.toTVals_length _ _ _ h1
  have hv2 := Val.toTVals_length _ _ _ h2
  refine Expr.toTerm_subst ?_ ?_ e te he
  · intro s v hv
    rw [List.lookup_append'] at hv
    cases hl : (zipSubst b vs1).lookup s with
    | some w =>
      rw [hl] at hv; cases hv
      exact Val.closed_of_mem_toTVals h1 (zipSubst_lookup_mem b vs1 s _ hl)
    | none =>
      rw [hl] at hv
      exact Val.closed_of_mem_toTVals h2 (zipSubst_lookup_mem o vs2 s v hv)
  · intro s i hi
    rcases Scope.extend_some (Scope.ofBinders o) b s i hi with ⟨hi', _, _⟩ | ⟨hi', hs, hΓ⟩
    · have hlk := zipSubst_lookup_of_extend b vs1 s (Scope.ofBinders o) i hi hi'
      rw [List.getElem?_eq_getElem (by omega)] at hlk
      simp only [Val.subst, List.lookup_append', hlk, Option.some_or, Option.getD_some,
        Subst.args, Subst.inst, hi', dif_pos]
      exact Val.toTVals_getElem _ _ _ h1 i _ _
    · simp only [Scope.ofBinders, Option.map_eq_some_iff] at hΓ
      obtain ⟨j, hj, hji⟩ := hΓ
      have hjv : j.val = i.val - (Binder.flags b).length := by
        have := congrArg Fin.val hji; simpa using this
      have hjlt : j.val < (Binder.flags o).length := by have := j.isLt; omega
      have hlk := zipSubst_lookup_of_extend o vs2 s Scope.empty j hj hjlt
      rw [List.getElem?_eq_getElem (by simp at hjlt; omega)] at hlk
      simp only [Val.subst, List.lookup_append', zipSubst_lookup_not_mem b vs1 s hs, hlk,
        Option.none_or, Option.getD_some, Subst.args, Subst.inst, Nat.not_lt.mpr hi',
        dif_neg, not_false_eq_true]
      rw [Val.toTVals_getElem _ _ _ h2 j _ (by omega)]
      simp [hjv]

/-! ## Signatures and branches -/

theorem Sig.toTSig_isSome_of_mem :
    ∀ {sig : Sig} {tsig : TSig}, sig.toTSig = some tsig → ∀ fd ∈ sig, fd.toTFunDef.isSome
  | [], _, _, fd, hfd => by simp at hfd
  | fd' :: sig, tsig, h, fd, hfd => by
    simp only [Sig.toTSig, List.mapM_cons] at h
    obtain ⟨tfd, tsig', htfd, htsig', rfl⟩ := bind2_eq_some' h
    rcases List.mem_cons.mp hfd with rfl | hfd
    · simp [htfd]
    · exact Sig.toTSig_isSome_of_mem (sig := sig) htsig' fd hfd

theorem Sig.toTSig_lookup_some {sig : Sig} {tsig : TSig} (hsig : sig.toTSig = some tsig)
    {f : FName} {fd : FunDef} (h : sig.lookup f = some fd) :
    ∃ tfd, fd.toTFunDef = some tfd ∧ tsig.lookup f = some tfd := by
  have hmem : fd ∈ sig := List.mem_of_find?_eq_some h
  obtain ⟨tfd, htfd⟩ := Option.isSome_iff_exists.mp (Sig.toTSig_isSome_of_mem hsig fd hmem)
  exact ⟨tfd, htfd, by rw [Sig.toTSig_lookup hsig, h]; exact htfd⟩

theorem Sig.toTSig_lookup_some' {sig : Sig} {tsig : TSig} (hsig : sig.toTSig = some tsig)
    {f : FName} {tfd : TFunDef} (h : tsig.lookup f = some tfd) :
    ∃ fd, sig.lookup f = some fd ∧ fd.toTFunDef = some tfd := by
  rw [Sig.toTSig_lookup hsig] at h
  exact Option.bind_eq_some_iff.mp h

/-- The branch found by `findBranch` is found, resolved, by `TBranches.find`. -/
theorem Expr.toBranches_find_some {n : Nat} (Δ : Scope n) (c : CName) (k : Nat) :
    ∀ {bs : List Branch} {tbs : TBranches n}, Expr.toBranches Δ bs = some tbs →
      ∀ {c' : CName} {xs : List Binder} {e : Expr}, findBranch bs c k = some (.mk c' xs e) →
        ∃ te, e.toTerm (Δ.extend xs) = some te ∧ tbs.find c k = some ⟨Binder.flags xs, te⟩
  | [], _, _, _, _, _, hf => by simp [findBranch] at hf
  | .mk c'' ys e' :: bs, tbs, h, c', xs, e, hf => by
    obtain ⟨te, tbs', h1, h2, rfl⟩ := bind2_eq_some' h
    simp only [findBranch, List.find?_cons, Branch.ctor, Branch.binders] at hf
    simp only [TBranches.find, Binder.flags, List.length_map]
    by_cases hc : c'' = c ∧ ys.length = k
    · obtain ⟨rfl, rfl⟩ := hc
      simp only [beq_self_eq_true, Bool.and_self] at hf
      cases hf
      exact ⟨te, h1, by simp⟩
    · have : (c'' == c && ys.length == k) = false := by
        simpa [Bool.and_eq_false_iff] using fun h1 => fun h2 => hc ⟨h1, h2⟩
      rw [this] at hf
      rw [if_neg hc]
      exact Expr.toBranches_find_some Δ c k h2 hf

theorem findBranch_ctor {bs : List Branch} {c c' : CName} {k : Nat} {xs : List Binder} {e : Expr}
    (h : findBranch bs c k = some (.mk c' xs e)) : c' = c ∧ xs.length = k := by
  have := List.find?_some h
  simpa [Branch.ctor, Branch.binders] using this

end FIPNamed
