module

public import RequestProject.Named.AppE_HeapSoundness.LamDeBruijnSubst

@[expose] public section

/-!
# The β-like reducts of the two presentations of `λfip` agree

Instantiating the binders of a closed `let`, branch, lambda or function body by closed
values gives the same result in the named presentation (`LExpr.subst` with `lzip`) and in
the de Bruijn one (`LTerm.isubst` with `LSubst'.inst`).  These are the instances of
`LExpr.toLTerm_subst` used by the simulation theorems of
`RequestProject/AppE_HeapSoundness/LamDeBruijnSim.lean`.
-/

namespace FIPNamed.Lam

/-! ## `lzip` -/

theorem lzip_of_extend :
    ∀ (xs : List Binder) (vs : List LVal) (s : String) {n : Nat} (Γ : Scope n)
      (i : Fin (n + (Binder.flags xs).length)),
      Γ.extend xs s = some i → i.val < (Binder.flags xs).length →
      lzip xs vs (.name s) = vs[i.val]?
  | [], _, _, _, _, i, _, hi => by simp at hi
  | x :: xs, [], s, _, Γ, i, _, _ => by simp [lzip]
  | x :: xs, v :: vs, s, _, Γ, i, h, hi => by
    by_cases hx : x.name = s
    · simp only [Scope.extend, hx, if_true, Option.some.injEq] at h
      subst h
      simp [lzip, hx]
    · simp only [Scope.extend, hx, if_false] at h
      obtain ⟨i', hi', rfl⟩ := Option.map_eq_some_iff.mp h
      have hne : (Var.name s == Var.name x.name) = false := by
        simpa using fun e => hx e.symm
      have := lzip_of_extend xs vs s Γ i' hi' (by simp at hi ⊢; omega)
      simp only [lzip, List.map_cons, List.zip_cons_cons, List.lookup, hne] at this ⊢
      simpa using this

theorem lzip_name_not_mem :
    ∀ (xs : List Binder) (vs : List LVal) (s : String), s ∉ xs.map (·.name) →
      lzip xs vs (.name s) = none
  | [], _, _, _ => by simp [lzip]
  | x :: xs, [], s, _ => by simp [lzip]
  | x :: xs, v :: vs, s, h => by
    simp only [List.map_cons, List.mem_cons, not_or] at h
    have hne : (Var.name s == Var.name x.name) = false := by simpa using h.1
    have := lzip_name_not_mem xs vs s h.2
    simp only [lzip, List.map_cons, List.zip_cons_cons, List.lookup, hne] at this ⊢
    exact this

theorem lzip_val_mem :
    ∀ (xs : List Binder) (vs : List LVal) (y : Var) (v : LVal), lzip xs vs y = some v → v ∈ vs
  | [], _, _, _, h => by simp [lzip] at h
  | x :: xs, [], _, _, h => by simp [lzip] at h
  | x :: xs, w :: vs, y, v, h => by
    simp only [lzip, List.map_cons, List.zip_cons_cons, List.lookup] at h
    split at h
    · cases h; simp
    · exact List.mem_cons_of_mem _ (lzip_val_mem xs vs y v h)

theorem lzip_loc_none : ∀ (xs : List Binder) (vs : List LVal) (l : Nat), lzip xs vs (.loc l) = none
  | [], _, _ => by simp [lzip]
  | x :: xs, [], _ => by simp [lzip]
  | x :: xs, v :: vs, l => by
    have hne : (Var.loc l == Var.name x.name) = false := by simp
    have := lzip_loc_none xs vs l
    simp only [lzip, List.map_cons, List.zip_cons_cons, List.lookup, hne] at this ⊢
    exact this

theorem lzip_append_or :
    ∀ (b o : List Binder) (vs1 vs2 : List LVal), b.length = vs1.length → ∀ y : Var,
      lzip (b ++ o) (vs1 ++ vs2) y = (lzip b vs1 y).or (lzip o vs2 y)
  | [], o, [], vs2, _, y => by simp [lzip]
  | [], _, _ :: _, _, h, _ => by simp at h
  | _ :: _, _, [], _, h, _ => by simp at h
  | x :: b, o, v :: vs1, vs2, h, y => by
    have ih := lzip_append_or b o vs1 vs2 (by simpa using h) y
    simp only [lzip, List.cons_append, List.map_cons, List.zip_cons_cons, List.lookup] at ih ⊢
    split
    · rfl
    · exact ih

/-! ## Closed values -/

theorem LVal.closed_of_mem {vs : List LVal} {ts : LTVals 0 vs.length}
    (h : LVal.toLTVals Scope.empty vs = some ts) {v : LVal} (hv : v ∈ vs) :
    ∃ c, v.toLTVal Scope.empty = some c := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hv
  exact ⟨_, LVal.toLTVals_get _ vs ts h ⟨i, hi⟩⟩

theorem mem_capturedNames_scoped {P : String → Prop} :
    ∀ {zs : List LVal}, LVal.ScopedList P zs → ∀ s, s ∈ capturedNames zs → P s
  | [], _, s, hs => by simp [capturedNames] at hs
  | z :: zs, h, s, hs => by
    cases z with
    | var x =>
      cases x with
      | name s' =>
        simp only [capturedNames, List.mem_cons] at hs
        rcases hs with rfl | hs
        · exact h.1
        · exact mem_capturedNames_scoped h.2 s hs
      | loc l => exact mem_capturedNames_scoped h.2 s (by simpa [capturedNames] using hs)
    | fn f => exact mem_capturedNames_scoped h.2 s (by simpa [capturedNames] using hs)
    | ctor c vs => exact mem_capturedNames_scoped h.2 s (by simpa [capturedNames] using hs)
    | lam zs' xs e => exact mem_capturedNames_scoped h.2 s (by simpa [capturedNames] using hs)

/-- The recorded variables of a closed lambda bind no name. -/
theorem Scope.ofCaptured_closed {zs : List LVal} {ts : LTVals 0 zs.length}
    (h : LVal.toLTVals Scope.empty zs = some ts) (s : String) : Scope.ofCaptured zs s = none := by
  have hs : (LVal.toLTVals Scope.empty zs).isSome := by simp [h]
  rw [LVal.toLTVals_isSome_iff] at hs
  cases hc : Scope.ofCaptured zs s with
  | none => rfl
  | some i =>
    have : (Scope.ofCaptured zs s).isSome := by simp [hc]
    rw [Scope.ofCaptured_isSome] at this
    have := mem_capturedNames_scoped hs s this
    simp [Scope.empty] at this

/-! ## Instantiation -/

/-- Instantiating the binders `x̄` of a closed body (of a `let`, a branch or a lambda), in a
    scope `Γ₀.extend x̄` where `Γ₀` binds no name. -/
theorem LExpr.toLTerm_subst_inst {k : Nat} {Γ₀ : Scope k} (hΓ₀ : ∀ s, Γ₀ s = none)
    (ρ : Fin k → LTVal 0) {xs : List Binder} {vs : List LVal} {ts : LTVals 0 vs.length}
    {e : LExpr} {te : LTerm (k + (Binder.flags xs).length)}
    (hvs : LVal.toLTVals Scope.empty vs = some ts) (he : e.toLTerm (Γ₀.extend xs) = some te)
    (h : vs.length = (Binder.flags xs).length) :
    (e.subst (lzip xs vs)).toLTerm Scope.empty = some (te.isubst (LSubst'.inst ts h ρ)) := by
  refine LExpr.toLTerm_subst ?_ (lzip_loc_none xs vs) ?_ e te he
  · intro x v hv
    exact LVal.closed_of_mem hvs (lzip_val_mem xs vs x v hv)
  · intro s i hi
    rcases Scope.extend_some Γ₀ xs s i hi with ⟨hi', _, _⟩ | ⟨_, _, hΓ⟩
    · have hlk := lzip_of_extend xs vs s Γ₀ i hi hi'
      rw [List.getElem?_eq_getElem (by omega)] at hlk
      simp only [LVal.subst, hlk, Option.getD_some, LSubst'.inst, hi', dif_pos]
      exact LVal.toLTVals_get _ vs ts hvs ⟨i.val, by omega⟩
    · rw [hΓ₀] at hΓ; cases hΓ

/-- Instantiating the parameters of a function body. -/
theorem LExpr.toLTerm_subst_args {b o : List Binder} {vs1 vs2 : List LVal}
    {ts1 : LTVals 0 vs1.length} {ts2 : LTVals 0 vs2.length} {e : LExpr}
    {te : LTerm ((Binder.flags o).length + (Binder.flags b).length)}
    (h1 : LVal.toLTVals Scope.empty vs1 = some ts1) (h2 : LVal.toLTVals Scope.empty vs2 = some ts2)
    (he : e.toLTerm ((Scope.ofBinders o).extend b) = some te)
    (hl1 : vs1.length = (Binder.flags b).length) (hl2 : vs2.length = (Binder.flags o).length) :
    (e.subst (lzip (b ++ o) (vs1 ++ vs2))).toLTerm Scope.empty =
      some (te.isubst (LSubst'.inst ts1 hl1 fun i => ts2.get ⟨i.val, by omega⟩)) := by
  have hb : b.length = vs1.length := by simp at hl1; omega
  refine LExpr.toLTerm_subst ?_ ?_ ?_ e te he
  · intro x v hv
    rw [lzip_append_or b o vs1 vs2 hb] at hv
    cases hl : lzip b vs1 x with
    | some w =>
      rw [hl] at hv; cases hv
      exact LVal.closed_of_mem h1 (lzip_val_mem b vs1 x _ hl)
    | none =>
      rw [hl] at hv
      exact LVal.closed_of_mem h2 (lzip_val_mem o vs2 x v (by simpa using hv))
  · intro l; rw [lzip_append_or b o vs1 vs2 hb, lzip_loc_none, lzip_loc_none]; rfl
  · intro s i hi
    rcases Scope.extend_some (Scope.ofBinders o) b s i hi with ⟨hi', _, _⟩ | ⟨hi', hs, hΓ⟩
    · have hlk := lzip_of_extend b vs1 s (Scope.ofBinders o) i hi hi'
      rw [List.getElem?_eq_getElem (by omega)] at hlk
      simp only [LVal.subst, lzip_append_or b o vs1 vs2 hb, hlk, Option.some_or, Option.getD_some,
        LSubst'.inst, hi', dif_pos]
      exact LVal.toLTVals_get _ vs1 ts1 h1 ⟨i.val, by omega⟩
    · simp only [Scope.ofBinders, Option.map_eq_some_iff] at hΓ
      obtain ⟨j, hj, hji⟩ := hΓ
      have hjv : j.val = i.val - (Binder.flags b).length := by
        have := congrArg Fin.val hji; simpa using this
      have hjlt : j.val < (Binder.flags o).length := by have := j.isLt; omega
      have hlk := lzip_of_extend o vs2 s Scope.empty j hj hjlt
      rw [List.getElem?_eq_getElem (by omega)] at hlk
      simp only [LVal.subst, lzip_append_or b o vs1 vs2 hb, lzip_name_not_mem b vs1 s hs, hlk,
        Option.none_or, Option.getD_some, LSubst'.inst, Nat.not_lt.mpr hi', dif_neg,
        not_false_eq_true]
      have hg := LVal.toLTVals_get _ vs2 ts2 h2 ⟨j.val, by omega⟩
      simp only [Fin.getElem_fin] at hg
      rw [hg]
      simp [hjv]

end FIPNamed.Lam
