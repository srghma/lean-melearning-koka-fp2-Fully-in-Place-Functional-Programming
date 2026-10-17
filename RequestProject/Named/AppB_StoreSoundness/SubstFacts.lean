module

public import RequestProject.Named.AppB_StoreSoundness.StoreSound

@[expose] public section

/-!
# Syntactic facts about substitution

Auxiliary lemmas for the proof of Theorem 1: substituting values without program names
commutes with further substitutions, substituting locations commutes with substituting
names, and matching commutes with substitution.
-/

namespace FIPNamed

/-! ## Lookups -/

theorem lookup_remove (ρ : Subst) (xs : List Binder) (s : String) :
    (ρ.remove xs).lookup s = if s ∈ xs.map (·.name) then none else ρ.lookup s := by
  induction ρ with
  | nil => simp [Subst.remove]
  | cons p ρ ih =>
    obtain ⟨t, v⟩ := p
    unfold Subst.remove at ih ⊢
    by_cases ht : t ∈ xs.map (·.name)
    · have : (!(xs.map (·.name)).contains t) = false := by simpa using ht
      rw [List.filter_cons_of_neg (by simpa using ht), ih]
      by_cases hs : s ∈ xs.map (·.name)
      · simp [hs]
      · have hst : (s == t) = false := by
          simp only [beq_eq_false_iff_ne]; rintro rfl; exact hs ht
        simp [hs, List.lookup_cons, hst]
    · rw [List.filter_cons_of_pos (by simpa using ht)]
      by_cases hst : s = t
      · subst hst; simp [ht]
      · have : (s == t) = false := by simpa using hst
        simp only [List.lookup_cons, this]
        exact ih

theorem Subst.remove_append (ρ1 ρ2 : Subst) (xs : List Binder) :
    (ρ1 ++ ρ2).remove xs = ρ1.remove xs ++ ρ2.remove xs := by
  simp [Subst.remove, List.filter_append]

theorem Subst.remove_nil (xs : List Binder) : Subst.remove [] xs = [] := rfl

/-! ## Values without names -/

/-- A substitution whose values mention no program names. -/
def Subst.NoName (ρ : Subst) : Prop := ∀ p ∈ ρ, ∀ s, Var.name s ∉ Val.fv p.2

theorem Subst.NoName.remove {ρ : Subst} (h : ρ.NoName) (xs : List Binder) :
    (ρ.remove xs).NoName := fun p hp => h p (List.mem_of_mem_filter hp)

theorem Subst.NoName.append {ρ1 ρ2 : Subst} (h1 : ρ1.NoName) (h2 : ρ2.NoName) :
    (ρ1 ++ ρ2).NoName := by
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · exact h1 p hp
  · exact h2 p hp

mutual
theorem Val.subst_noName (τ : Subst) :
    ∀ v : Val, (∀ s, Var.name s ∉ Val.fv v) → v.subst τ = v
  | .var (.name s), h => absurd (by simp [Val.fv]) (h s)
  | .var (.loc _), _ => rfl
  | .fn _, _ => rfl
  | .lit _, _ => rfl
  | .ctor c vs, h => by
    simp only [Val.subst, Val.fv] at h ⊢
    rw [Val.substList_noName τ vs h]
theorem Val.substList_noName (τ : Subst) :
    ∀ vs : List Val, (∀ s, Var.name s ∉ Val.fvList vs) → Val.substList τ vs = vs
  | [], _ => rfl
  | v :: vs, h => by
    simp only [Val.substList]
    rw [Val.subst_noName τ v (fun s hs => h s (by simp [Val.fvList, hs])),
      Val.substList_noName τ vs (fun s hs => h s (by simp [Val.fvList, hs]))]
end

/-! ## The empty substitution -/

mutual
theorem Val.subst_nil : ∀ v : Val, v.subst [] = v
  | .var (.name s) => rfl
  | .var (.loc _) => rfl
  | .fn _ => rfl
  | .lit _ => rfl
  | .ctor c vs => by simp only [Val.subst]; rw [Val.substList_nil vs]
theorem Val.substList_nil : ∀ vs : List Val, Val.substList [] vs = vs
  | [] => rfl
  | v :: vs => by simp only [Val.substList]; rw [Val.subst_nil v, Val.substList_nil vs]
end

mutual
theorem Expr.subst_nil : ∀ e : Expr, e.subst [] = e
  | .ret vs => by simp only [Expr.subst]; rw [Val.substList_nil]
  | .app e1 e2 => by simp only [Expr.subst]; rw [Expr.subst_nil e1, Expr.subst_nil e2]
  | .call f e1 e2 => by simp only [Expr.subst]; rw [Expr.subst_nil e1, Expr.subst_nil e2]
  | .letIn xs e1 e2 => by
    simp only [Expr.subst, Subst.remove_nil]; rw [Expr.subst_nil e1, Expr.subst_nil e2]
  | .bmatch e bs => by simp only [Expr.subst]; rw [Expr.subst_nil e, Expr.substBranches_nil bs]
  | .dmatch e bs => by simp only [Expr.subst]; rw [Expr.subst_nil e, Expr.substBranches_nil bs]
  | .drop x e => by simp only [Expr.subst]; rw [Val.subst_nil x, Expr.subst_nil e]
  | .free k e => by simp only [Expr.subst]; rw [Expr.subst_nil e]
  | .prim op vs => by simp only [Expr.subst]; rw [Val.substList_nil]
theorem Expr.substBranches_nil : ∀ bs : List Branch, Expr.substBranches [] bs = bs
  | [] => rfl
  | .mk c xs e :: bs => by
    simp only [Expr.substBranches, Subst.remove_nil]
    rw [Expr.subst_nil e, Expr.substBranches_nil bs]
end

/-! ## Composing substitutions -/

theorem Val.subst_var_append {ρ1 : Subst} (h1 : ρ1.NoName) (ρ2 : Subst) (x : Var) :
    (Val.subst ρ1 (.var x)).subst ρ2 = Val.subst (ρ1 ++ ρ2) (.var x) := by
  cases x with
  | loc n => rfl
  | name s =>
    simp only [Val.subst, List.lookup_append]
    cases h : ρ1.lookup s with
    | none => simp [Val.subst]
    | some w =>
      simp only [Option.getD_some, Option.some_or]
      apply Val.subst_noName
      obtain ⟨p, hp, hp'⟩ : ∃ p ∈ ρ1, p.2 = w := by
        induction ρ1 with
        | nil => simp at h
        | cons q ρ ih =>
          obtain ⟨t, u⟩ := q
          by_cases hst : s = t
          · subst hst; simp at h; exact ⟨_, List.mem_cons_self, h⟩
          · have : (s == t) = false := by simpa using hst
            simp only [List.lookup_cons, this] at h
            obtain ⟨p, hp, hp'⟩ := ih (fun p hp => h1 p (List.mem_cons_of_mem _ hp)) h
            exact ⟨p, List.mem_cons_of_mem _ hp, hp'⟩
      exact hp' ▸ h1 p hp

mutual
theorem Val.subst_append {ρ1 : Subst} (h1 : ρ1.NoName) (ρ2 : Subst) :
    ∀ v : Val, (v.subst ρ1).subst ρ2 = v.subst (ρ1 ++ ρ2)
  | .var x => Val.subst_var_append h1 ρ2 x
  | .fn _ => rfl
  | .lit _ => rfl
  | .ctor c vs => by
    simp only [Val.subst]; rw [Val.substList_append h1 ρ2 vs]
theorem Val.substList_append {ρ1 : Subst} (h1 : ρ1.NoName) (ρ2 : Subst) :
    ∀ vs : List Val, Val.substList ρ2 (Val.substList ρ1 vs) = Val.substList (ρ1 ++ ρ2) vs
  | [] => rfl
  | v :: vs => by
    simp only [Val.substList]; rw [Val.subst_append h1 ρ2 v, Val.substList_append h1 ρ2 vs]
end

mutual
theorem Expr.subst_append {ρ1 : Subst} (h1 : ρ1.NoName) (ρ2 : Subst) :
    ∀ e : Expr, (e.subst ρ1).subst ρ2 = e.subst (ρ1 ++ ρ2)
  | .ret vs => by simp only [Expr.subst]; rw [Val.substList_append h1]
  | .app e1 e2 => by
    simp only [Expr.subst]; rw [Expr.subst_append h1 ρ2 e1, Expr.subst_append h1 ρ2 e2]
  | .call f e1 e2 => by
    simp only [Expr.subst]; rw [Expr.subst_append h1 ρ2 e1, Expr.subst_append h1 ρ2 e2]
  | .letIn xs e1 e2 => by
    simp only [Expr.subst]
    rw [Expr.subst_append h1 ρ2 e1, Expr.subst_append (h1.remove xs) _ e2,
      Subst.remove_append]
  | .bmatch e bs => by
    simp only [Expr.subst]; rw [Expr.subst_append h1 ρ2 e, Expr.substBranches_append h1 ρ2 bs]
  | .dmatch e bs => by
    simp only [Expr.subst]; rw [Expr.subst_append h1 ρ2 e, Expr.substBranches_append h1 ρ2 bs]
  | .drop x e => by
    simp only [Expr.subst]; rw [Val.subst_append h1 ρ2 x, Expr.subst_append h1 ρ2 e]
  | .free k e => by simp only [Expr.subst]; rw [Expr.subst_append h1 ρ2 e]
  | .prim op vs => by simp only [Expr.subst]; rw [Val.substList_append h1]
theorem Expr.substBranches_append {ρ1 : Subst} (h1 : ρ1.NoName) (ρ2 : Subst) :
    ∀ bs : List Branch,
      Expr.substBranches ρ2 (Expr.substBranches ρ1 bs) = Expr.substBranches (ρ1 ++ ρ2) bs
  | [] => rfl
  | .mk c xs e :: bs => by
    simp only [Expr.substBranches]
    rw [Expr.subst_append (h1.remove xs) _ e, Subst.remove_append,
      Expr.substBranches_append h1 ρ2 bs]
end

/-! ## Substituting locations and names -/

/-- Every value of `σ` is closed. -/
def LocClosed (σ : Nat → Option Val) : Prop := ∀ n w, σ n = some w → Val.fv w = []

/-- Apply a location substitution to the values of a name substitution. -/
def Subst.mapLoc (σ : Nat → Option Val) (τ : Subst) : Subst :=
  τ.map fun p => (p.1, p.2.substLoc σ)

theorem Subst.mapLoc_remove (σ : Nat → Option Val) (τ : Subst) (xs : List Binder) :
    (τ.remove xs).mapLoc σ = (τ.mapLoc σ).remove xs := by
  simp [Subst.mapLoc, Subst.remove, List.filter_map, Function.comp_def]

theorem Subst.lookup_mapLoc (σ : Nat → Option Val) (τ : Subst) (s : String) :
    (τ.mapLoc σ).lookup s = (τ.lookup s).map (Val.substLoc σ) := by
  induction τ with
  | nil => rfl
  | cons p τ ih =>
    obtain ⟨t, v⟩ := p
    by_cases hst : s = t
    · subst hst; simp [Subst.mapLoc]
    · have : (s == t) = false := by simpa using hst
      simp only [Subst.mapLoc, List.map_cons, List.lookup_cons, this] at ih ⊢
      exact ih

mutual
theorem Val.substLoc_subst {σ : Nat → Option Val} (hσ : LocClosed σ) (τ : Subst) :
    ∀ v : Val, (v.subst τ).substLoc σ = (v.substLoc σ).subst (τ.mapLoc σ)
  | .var (.name s) => by
    simp only [Val.subst, Val.substLoc, Subst.lookup_mapLoc]
    cases τ.lookup s <;> rfl
  | .var (.loc n) => by
    simp only [Val.subst, Val.substLoc]
    cases h : σ n with
    | none => rfl
    | some w =>
      simp only [Option.getD_some]
      exact (Val.subst_noName _ w (by simp [hσ n w h])).symm
  | .fn _ => rfl
  | .lit _ => rfl
  | .ctor c vs => by
    simp only [Val.subst, Val.substLoc]; rw [Val.substLocList_subst hσ τ vs]
theorem Val.substLocList_subst {σ : Nat → Option Val} (hσ : LocClosed σ) (τ : Subst) :
    ∀ vs : List Val, Val.substLocList σ (Val.substList τ vs) =
      Val.substList (τ.mapLoc σ) (Val.substLocList σ vs)
  | [] => rfl
  | v :: vs => by
    simp only [Val.substList, Val.substLocList]
    rw [Val.substLoc_subst hσ τ v, Val.substLocList_subst hσ τ vs]
end

mutual
theorem Expr.substLoc_subst {σ : Nat → Option Val} (hσ : LocClosed σ) (τ : Subst) :
    ∀ e : Expr, (e.subst τ).substLoc σ = (e.substLoc σ).subst (τ.mapLoc σ)
  | .ret vs => by simp only [Expr.subst, Expr.substLoc]; rw [Val.substLocList_subst hσ]
  | .app e1 e2 => by
    simp only [Expr.subst, Expr.substLoc]
    rw [Expr.substLoc_subst hσ τ e1, Expr.substLoc_subst hσ τ e2]
  | .call f e1 e2 => by
    simp only [Expr.subst, Expr.substLoc]
    rw [Expr.substLoc_subst hσ τ e1, Expr.substLoc_subst hσ τ e2]
  | .letIn xs e1 e2 => by
    simp only [Expr.subst, Expr.substLoc]
    rw [Expr.substLoc_subst hσ τ e1, Expr.substLoc_subst hσ _ e2, Subst.mapLoc_remove]
  | .bmatch e bs => by
    simp only [Expr.subst, Expr.substLoc]
    rw [Expr.substLoc_subst hσ τ e, Expr.substLocB_subst hσ τ bs]
  | .dmatch e bs => by
    simp only [Expr.subst, Expr.substLoc]
    rw [Expr.substLoc_subst hσ τ e, Expr.substLocB_subst hσ τ bs]
  | .drop x e => by
    simp only [Expr.subst, Expr.substLoc]
    rw [Val.substLoc_subst hσ τ x, Expr.substLoc_subst hσ τ e]
  | .free k e => by
    simp only [Expr.subst, Expr.substLoc]; rw [Expr.substLoc_subst hσ τ e]
  | .prim op vs => by simp only [Expr.subst, Expr.substLoc]; rw [Val.substLocList_subst hσ]
theorem Expr.substLocB_subst {σ : Nat → Option Val} (hσ : LocClosed σ) (τ : Subst) :
    ∀ bs : List Branch, Expr.substLocB σ (Expr.substBranches τ bs) =
      Expr.substBranches (τ.mapLoc σ) (Expr.substLocB σ bs)
  | [] => rfl
  | .mk c xs e :: bs => by
    simp only [Expr.substBranches, Expr.substLocB]
    rw [Expr.substLoc_subst hσ _ e, Subst.mapLoc_remove, Expr.substLocB_subst hσ τ bs]
end

/-! ## Congruence of location substitution -/

mutual
theorem Val.substLoc_congr {σ σ' : Nat → Option Val} :
    ∀ v : Val, (∀ n, Var.loc n ∈ Val.fv v → σ n = σ' n) → v.substLoc σ = v.substLoc σ'
  | .var (.loc n), h => by simp only [Val.substLoc]; rw [h n (by simp [Val.fv])]
  | .var (.name _), _ => rfl
  | .fn _, _ => rfl
  | .lit _, _ => rfl
  | .ctor c vs, h => by
    simp only [Val.substLoc, Val.fv] at h ⊢; rw [Val.substLocList_congr vs h]
theorem Val.substLocList_congr {σ σ' : Nat → Option Val} :
    ∀ vs : List Val, (∀ n, Var.loc n ∈ Val.fvList vs → σ n = σ' n) →
      Val.substLocList σ vs = Val.substLocList σ' vs
  | [], _ => rfl
  | v :: vs, h => by
    simp only [Val.substLocList]
    rw [Val.substLoc_congr v (fun n hn => h n (by simp [Val.fvList, hn])),
      Val.substLocList_congr vs (fun n hn => h n (by simp [Val.fvList, hn]))]
end

mutual
theorem Expr.substLoc_congr {σ σ' : Nat → Option Val} :
    ∀ e : Expr, (∀ n, Var.loc n ∈ e.fv → σ n = σ' n) → e.substLoc σ = e.substLoc σ'
  | .ret vs, h => by
    simp only [Expr.substLoc, Expr.fv] at h ⊢; rw [Val.substLocList_congr vs h]
  | .app e1 e2, h => by
    simp only [Expr.substLoc]
    rw [Expr.substLoc_congr e1 (fun n hn => h n (by simp [Expr.fv, hn])),
      Expr.substLoc_congr e2 (fun n hn => h n (by simp [Expr.fv, hn]))]
  | .call f e1 e2, h => by
    simp only [Expr.substLoc]
    rw [Expr.substLoc_congr e1 (fun n hn => h n (by simp [Expr.fv, hn])),
      Expr.substLoc_congr e2 (fun n hn => h n (by simp [Expr.fv, hn]))]
  | .letIn xs e1 e2, h => by
    simp only [Expr.substLoc]
    rw [Expr.substLoc_congr e1 (fun n hn => h n (by simp [Expr.fv, hn])),
      Expr.substLoc_congr e2 (fun n hn => h n (by
        simp [Expr.fv, hn, loc_not_mem_binderVars]))]
  | .bmatch e bs, h => by
    simp only [Expr.substLoc]
    rw [Expr.substLoc_congr e (fun n hn => h n (by simp [Expr.fv, hn])),
      Expr.substLocB_congr bs (fun n hn => h n (by simp [Expr.fv, hn]))]
  | .dmatch e bs, h => by
    simp only [Expr.substLoc]
    rw [Expr.substLoc_congr e (fun n hn => h n (by simp [Expr.fv, hn])),
      Expr.substLocB_congr bs (fun n hn => h n (by simp [Expr.fv, hn]))]
  | .drop x e, h => by
    simp only [Expr.substLoc]
    rw [Val.substLoc_congr x (fun n hn => h n (by simp [Expr.fv, hn])),
      Expr.substLoc_congr e (fun n hn => h n (by simp [Expr.fv, hn]))]
  | .free k e, h => by
    simp only [Expr.substLoc]
    rw [Expr.substLoc_congr e (fun n hn => h n (by simp [Expr.fv, hn]))]
  | .prim op vs, h => by
    simp only [Expr.substLoc, Expr.fv] at h ⊢; rw [Val.substLocList_congr vs h]
theorem Expr.substLocB_congr {σ σ' : Nat → Option Val} :
    ∀ bs : List Branch, (∀ n, Var.loc n ∈ Expr.fvBranches bs → σ n = σ' n) →
      Expr.substLocB σ bs = Expr.substLocB σ' bs
  | [], _ => rfl
  | .mk c xs e :: bs, h => by
    simp only [Expr.substLocB]
    rw [Expr.substLoc_congr e (fun n hn => h n (by
        simp [Expr.fvBranches, hn, loc_not_mem_binderVars])),
      Expr.substLocB_congr bs (fun n hn => h n (by simp [Expr.fvBranches, hn]))]
end

/-! ## Free locations of a substituted expression -/

theorem Val.subst_var_remove (ρ : Subst) (xs : List Binder) (x : Var)
    (hx : x ∉ Binder.vars xs) : Val.subst (ρ.remove xs) (.var x) = Val.subst ρ (.var x) := by
  cases x with
  | loc n => rfl
  | name s =>
    have : s ∉ xs.map (·.name) := by
      intro h; apply hx; simp only [Binder.vars, List.mem_map] at h ⊢
      obtain ⟨b, hb, rfl⟩ := h; exact ⟨b, hb, rfl⟩
    simp [Val.subst, lookup_remove, this]

theorem Val.subst_var_remove_mem (ρ : Subst) (xs : List Binder) (x : Var)
    (hx : x ∈ Binder.vars xs) : Val.subst (ρ.remove xs) (.var x) = .var x := by
  simp only [Binder.vars, List.mem_map] at hx
  obtain ⟨b, hb, rfl⟩ := hx
  have : b.name ∈ xs.map (·.name) := List.mem_map_of_mem hb
  simp [Val.subst, lookup_remove, this]

mutual
theorem Val.fv_subst (ρ : Subst) (y : Var) :
    ∀ v : Val, y ∈ Val.fv (v.subst ρ) → ∃ x ∈ Val.fv v, y ∈ Val.fv (Val.subst ρ (.var x))
  | .var x, h => ⟨x, by simp [Val.fv], h⟩
  | .fn _, h => by simp [Val.subst, Val.fv] at h
  | .lit _, h => by simp [Val.subst, Val.fv] at h
  | .ctor c vs, h => by
    simp only [Val.subst, Val.fv] at h ⊢
    exact Val.fvList_subst ρ y vs h
theorem Val.fvList_subst (ρ : Subst) (y : Var) :
    ∀ vs : List Val, y ∈ Val.fvList (Val.substList ρ vs) →
      ∃ x ∈ Val.fvList vs, y ∈ Val.fv (Val.subst ρ (.var x))
  | [], h => by simp [Val.substList, Val.fvList] at h
  | v :: vs, h => by
    simp only [Val.substList, Val.fvList, List.mem_append] at h
    rcases h with h | h
    · obtain ⟨x, hx, h'⟩ := Val.fv_subst ρ y v h
      exact ⟨x, by simp [Val.fvList, hx], h'⟩
    · obtain ⟨x, hx, h'⟩ := Val.fvList_subst ρ y vs h
      exact ⟨x, by simp [Val.fvList, hx], h'⟩
end

theorem fv_subst_binders {ρ : Subst} {xs : List Binder} {y : Var} {x : Var}
    (hy : ∀ s, y ≠ Var.name s) (h : y ∈ Val.fv (Val.subst (ρ.remove xs) (.var x))) :
    x ∉ Binder.vars xs ∧ y ∈ Val.fv (Val.subst ρ (.var x)) := by
  by_cases hx : x ∈ Binder.vars xs
  · rw [Val.subst_var_remove_mem ρ xs x hx] at h
    simp only [Binder.vars, List.mem_map] at hx
    obtain ⟨b, -, rfl⟩ := hx
    simp only [Val.fv, List.mem_singleton] at h
    exact absurd h (hy b.name)
  · exact ⟨hx, Val.subst_var_remove ρ xs x hx ▸ h⟩

mutual
theorem Expr.fv_subst (ρ : Subst) (y : Var) (hy : ∀ s, y ≠ Var.name s) :
    ∀ e : Expr, y ∈ (e.subst ρ).fv → ∃ x ∈ e.fv, y ∈ Val.fv (Val.subst ρ (.var x))
  | .ret vs, h => by
    simp only [Expr.subst, Expr.fv] at h ⊢; exact Val.fvList_subst ρ y vs h
  | .app e1 e2, h => by
    simp only [Expr.subst, Expr.fv, List.mem_append] at h ⊢
    rcases h with h | h
    · obtain ⟨x, hx, h'⟩ := Expr.fv_subst ρ y hy e1 h; exact ⟨x, .inl hx, h'⟩
    · obtain ⟨x, hx, h'⟩ := Expr.fv_subst ρ y hy e2 h; exact ⟨x, .inr hx, h'⟩
  | .call f e1 e2, h => by
    simp only [Expr.subst, Expr.fv, List.mem_append] at h ⊢
    rcases h with h | h
    · obtain ⟨x, hx, h'⟩ := Expr.fv_subst ρ y hy e1 h; exact ⟨x, .inl hx, h'⟩
    · obtain ⟨x, hx, h'⟩ := Expr.fv_subst ρ y hy e2 h; exact ⟨x, .inr hx, h'⟩
  | .letIn xs e1 e2, h => by
    simp only [Expr.subst, Expr.fv, List.mem_append, List.mem_filter, decide_eq_true_eq] at h ⊢
    rcases h with h | ⟨h, -⟩
    · obtain ⟨x, hx, h'⟩ := Expr.fv_subst ρ y hy e1 h; exact ⟨x, .inl hx, h'⟩
    · obtain ⟨x, hx, h'⟩ := Expr.fv_subst _ y hy e2 h
      obtain ⟨hx', h''⟩ := fv_subst_binders hy h'
      exact ⟨x, .inr ⟨hx, hx'⟩, h''⟩
  | .bmatch e bs, h => by
    simp only [Expr.subst, Expr.fv, List.mem_append] at h ⊢
    rcases h with h | h
    · obtain ⟨x, hx, h'⟩ := Expr.fv_subst ρ y hy e h; exact ⟨x, .inl hx, h'⟩
    · obtain ⟨x, hx, h'⟩ := Expr.fvBranches_subst ρ y hy bs h; exact ⟨x, .inr hx, h'⟩
  | .dmatch e bs, h => by
    simp only [Expr.subst, Expr.fv, List.mem_append] at h ⊢
    rcases h with h | h
    · obtain ⟨x, hx, h'⟩ := Expr.fv_subst ρ y hy e h; exact ⟨x, .inl hx, h'⟩
    · obtain ⟨x, hx, h'⟩ := Expr.fvBranches_subst ρ y hy bs h; exact ⟨x, .inr hx, h'⟩
  | .drop v e, h => by
    simp only [Expr.subst, Expr.fv, List.mem_append] at h ⊢
    rcases h with h | h
    · obtain ⟨x, hx, h'⟩ := Val.fv_subst ρ y v h; exact ⟨x, .inl hx, h'⟩
    · obtain ⟨x, hx, h'⟩ := Expr.fv_subst ρ y hy e h; exact ⟨x, .inr hx, h'⟩
  | .free k e, h => by
    simp only [Expr.subst, Expr.fv] at h ⊢; exact Expr.fv_subst ρ y hy e h
  | .prim op vs, h => by
    simp only [Expr.subst, Expr.fv] at h ⊢; exact Val.fvList_subst ρ y vs h
theorem Expr.fvBranches_subst (ρ : Subst) (y : Var) (hy : ∀ s, y ≠ Var.name s) :
    ∀ bs : List Branch, y ∈ Expr.fvBranches (Expr.substBranches ρ bs) →
      ∃ x ∈ Expr.fvBranches bs, y ∈ Val.fv (Val.subst ρ (.var x))
  | [], h => by simp [Expr.substBranches, Expr.fvBranches] at h
  | .mk c xs e :: bs, h => by
    simp only [Expr.substBranches, Expr.fvBranches, List.mem_append, List.mem_filter,
      decide_eq_true_eq] at h ⊢
    rcases h with ⟨h, -⟩ | h
    · obtain ⟨x, hx, h'⟩ := Expr.fv_subst _ y hy e h
      obtain ⟨hx', h''⟩ := fv_subst_binders hy h'
      exact ⟨x, .inl ⟨hx, hx'⟩, h''⟩
    · obtain ⟨x, hx, h'⟩ := Expr.fvBranches_subst ρ y hy bs h; exact ⟨x, .inr hx, h'⟩
end

/-! ## Matching commutes with substitution -/

theorem findBranch_mem {bs : List Branch} {c : CName} {k : Nat} {b : Branch}
    (h : findBranch bs c k = some b) : b ∈ bs ∧ b.ctor = c ∧ b.binders.length = k := by
  unfold findBranch at h
  have h1 := List.mem_of_find?_eq_some h
  have h2 := List.find?_some h
  simp only [Bool.and_eq_true, beq_iff_eq] at h2
  exact ⟨h1, h2.1, h2.2⟩

theorem findBranch_substBranches (ρ : Subst) (bs : List Branch) (c : CName) (k : Nat) :
    findBranch (Expr.substBranches ρ bs) c k =
      (findBranch bs c k).map fun b => .mk b.ctor b.binders (b.body.subst (ρ.remove b.binders)) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    obtain ⟨c', xs, e⟩ := b
    unfold findBranch at ih ⊢
    simp only [Expr.substBranches]
    rw [List.find?_cons, List.find?_cons]
    by_cases hp : (c' == c && xs.length == k) = true
    · simp only [Branch.ctor, Branch.binders, hp]; rfl
    · simp only [Bool.not_eq_true] at hp
      simp only [Branch.ctor, Branch.binders, hp]; exact ih

theorem findBranch_substLocB (σ : Nat → Option Val) (bs : List Branch) (c : CName) (k : Nat) :
    findBranch (Expr.substLocB σ bs) c k =
      (findBranch bs c k).map fun b => .mk b.ctor b.binders (b.body.substLoc σ) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    obtain ⟨c', xs, e⟩ := b
    unfold findBranch at ih ⊢
    simp only [Expr.substLocB]
    rw [List.find?_cons, List.find?_cons]
    by_cases hp : (c' == c && xs.length == k) = true
    · simp only [Branch.ctor, Branch.binders, hp]; rfl
    · simp only [Bool.not_eq_true] at hp
      simp only [Branch.ctor, Branch.binders, hp]; exact ih

/-! ## Simultaneous substitutions -/

theorem lookup_zipSubst_of_mem {xs : List Binder} {vs : List Val} (hn : (xs.map (·.name)).Nodup)
    (hl : xs.length = vs.length) {i : Nat} (hi : i < xs.length) :
    (zipSubst xs vs).lookup (xs[i]).name = some (vs[i]'(hl ▸ hi)) := by
  induction xs generalizing vs i with
  | nil => simp at hi
  | cons b xs ih =>
    cases vs with
    | nil => simp at hl
    | cons v vs =>
      simp only [List.map_cons, List.nodup_cons] at hn
      cases i with
      | zero => simp [zipSubst]
      | succ i =>
        simp only [List.length_cons, Nat.add_lt_add_iff_right] at hi
        have hne : (xs[i].name == b.name) = false := by
          simp only [beq_eq_false_iff_ne]
          intro h; apply hn.1; rw [← h]; exact List.mem_map_of_mem (List.getElem_mem hi)
        simp only [zipSubst, List.map_cons, List.zip_cons_cons, List.getElem_cons_succ,
          List.lookup_cons, hne]
        exact ih hn.2 (by simpa using hl) hi

theorem lookup_zipSubst_of_not_mem {xs : List Binder} {vs : List Val} {s : String}
    (h : s ∉ xs.map (·.name)) : (zipSubst xs vs).lookup s = none := by
  induction xs generalizing vs with
  | nil => simp [zipSubst]
  | cons b xs ih =>
    cases vs with
    | nil => simp [zipSubst]
    | cons v vs =>
      simp only [List.map_cons, List.mem_cons, not_or] at h
      have : (s == b.name) = false := by simpa using h.1
      simp only [zipSubst, List.map_cons, List.zip_cons_cons, List.lookup_cons, this]
      exact ih h.2

theorem zipSubst_mapLoc (σ : Nat → Option Val) (xs : List Binder) (vs : List Val) :
    (zipSubst xs vs).mapLoc σ = zipSubst xs (vs.map (Val.substLoc σ)) := by
  induction xs generalizing vs with
  | nil => simp [zipSubst, Subst.mapLoc]
  | cons b xs ih =>
    cases vs with
    | nil => simp [zipSubst, Subst.mapLoc]
    | cons v vs =>
      have := ih vs
      simp only [zipSubst, Subst.mapLoc] at this ⊢
      simp [this]

theorem Subst.mapLoc_append (σ : Nat → Option Val) (τ1 τ2 : Subst) :
    (τ1 ++ τ2).mapLoc σ = τ1.mapLoc σ ++ τ2.mapLoc σ := by
  simp [Subst.mapLoc]

end FIPNamed
