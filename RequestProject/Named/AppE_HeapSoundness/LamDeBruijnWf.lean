module

public import RequestProject.Named.AppE_HeapSoundness.LamDeBruijnClosed

@[expose] public section

/-!
# Well-formed `λfip` programs are well scoped

If `Δ | Γ ⊢ e` (Fig. 9) then every free name of `e` is in `Δ, Γ` and every lambda of `e`
is correctly annotated, so `e` has a de Bruijn representation in any scope binding
`Δ, Γ` (`LWf.scoped`).  Hence every well-formed closed program `∅ | ∅ ⊢ e` is an
`LTerm 0` (`LWf.toLTerm_closed`), and every well-formed signature `⊩ Σ` has a
well-scoped version in which each body is an `LTerm (|x̄| + |ȳ|)` (`LSig.Wf.toLTSig`).
-/

namespace FIPNamed.Lam

mutual
theorem LVal.Scoped.mono {P Q : String → Prop} (hPQ : ∀ s, P s → Q s) :
    ∀ {v : LVal}, LVal.Scoped P v → LVal.Scoped Q v
  | .var (.name s), h => hPQ s h
  | .var (.loc _), _ => trivial
  | .fn _, _ => trivial
  | .ctor _ vs, h => LVal.ScopedList.mono hPQ (v := vs) h
  | .lam zs _ _, h => ⟨LVal.ScopedList.mono hPQ (v := zs) h.1, h.2⟩
theorem LVal.ScopedList.mono {P Q : String → Prop} (hPQ : ∀ s, P s → Q s) :
    ∀ {v : List LVal}, LVal.ScopedList P v → LVal.ScopedList Q v
  | [], _ => trivial
  | _ :: _, h => ⟨LVal.Scoped.mono hPQ h.1, LVal.ScopedList.mono hPQ h.2⟩
end

mutual
theorem LExpr.Scoped.mono {P Q : String → Prop} (hPQ : ∀ s, P s → Q s) :
    ∀ {e : LExpr}, LExpr.Scoped P e → LExpr.Scoped Q e
  | .ret vs, h => LVal.ScopedList.mono hPQ (v := vs) h
  | .app _ _, h => ⟨LExpr.Scoped.mono hPQ h.1, LExpr.Scoped.mono hPQ h.2⟩
  | .call _ _ _, h => ⟨LExpr.Scoped.mono hPQ h.1, LExpr.Scoped.mono hPQ h.2⟩
  | .letIn _ _ _, h =>
    ⟨LExpr.Scoped.mono hPQ h.1,
      LExpr.Scoped.mono (fun s hs => hs.imp id (hPQ s)) h.2⟩
  | .match _ _, h => ⟨LVal.Scoped.mono hPQ h.1, LExpr.ScopedB.mono hPQ h.2⟩
  | .dup _ _, h => ⟨LVal.Scoped.mono hPQ h.1, LExpr.Scoped.mono hPQ h.2⟩
  | .drop _ _, h => ⟨LVal.Scoped.mono hPQ h.1, LExpr.Scoped.mono hPQ h.2⟩
  | .dropru _ _ _, h => ⟨LVal.Scoped.mono hPQ h.1, LExpr.Scoped.mono hPQ h.2⟩
  | .free _ e, h => LExpr.Scoped.mono hPQ (e := e) h
  | .alloc _ e, h => LExpr.Scoped.mono hPQ (e := e) h
theorem LExpr.ScopedB.mono {P Q : String → Prop} (hPQ : ∀ s, P s → Q s) :
    ∀ {bs : List LBranch}, LExpr.ScopedB P bs → LExpr.ScopedB Q bs
  | [], _ => trivial
  | .mk _ _ _ :: _, h =>
    ⟨LExpr.Scoped.mono (fun s hs => hs.imp id (hPQ s)) h.1, LExpr.ScopedB.mono hPQ h.2⟩
end

theorem LVal.ScopedList.of_forall {P : String → Prop} :
    ∀ {vs : List LVal}, (∀ v ∈ vs, LVal.Scoped P v) → LVal.ScopedList P vs
  | [], _ => trivial
  | v :: _, h => ⟨h v (List.mem_cons_self ..), LVal.ScopedList.of_forall fun w hw =>
      h w (List.mem_cons_of_mem _ hw)⟩

theorem LExpr.ScopedB.of_forall {P : String → Prop} :
    ∀ {bs : List LBranch},
      (∀ b ∈ bs, LExpr.Scoped (fun s => s ∈ b.binders.map (·.name) ∨ P s) b.body) →
        LExpr.ScopedB P bs
  | [], _ => trivial
  | .mk _ _ _ :: _, h => ⟨h _ (List.mem_cons_self ..), LExpr.ScopedB.of_forall fun b hb =>
      h b (List.mem_cons_of_mem _ hb)⟩

theorem LExpr.Scoped.dups {P : String → Prop} :
    ∀ {vs : List LVal} {e : LExpr}, (∀ v ∈ vs, LVal.Scoped P v) → LExpr.Scoped P e →
      LExpr.Scoped P (FIPNamed.Lam.dups vs e)
  | [], _, _, he => he
  | _ :: _, _, hv, he => ⟨hv _ (List.mem_cons_self ..),
      LExpr.Scoped.dups (fun w hw => hv w (List.mem_cons_of_mem _ hw)) he⟩

theorem mem_capturedNames {s : String} : ∀ {zs : List Var}, Var.name s ∈ zs →
    s ∈ capturedNames (zs.map LVal.var)
  | [], h => by simp at h
  | z :: zs, h => by
    rcases List.mem_cons.mp h with rfl | h
    · simp [capturedNames]
    · have := mem_capturedNames h
      cases z with
      | name s' => simp [capturedNames, this]
      | loc l => simpa [capturedNames] using this

theorem mem_Binder_ctx {s : String} {xs : List Binder} (h : Res.var (.name s) ∈ Binder.ctx xs) :
    s ∈ xs.map (·.name) := by
  simpa [Binder.ctx] using h

theorem mem_varCtx {x : Var} {zs : List Var} (h : Res.var x ∈ varCtx zs) : x ∈ zs := by
  simpa [varCtx] using h

theorem mem_Ctx_vars {x : Var} {Γ : Ctx} (h : x ∈ Γ.vars) : Res.var x ∈ Γ := by
  simp only [Ctx.vars, Multiset.mem_filterMap] at h
  obtain ⟨r, hr, hx⟩ := h
  cases r <;> simp_all

/-- The predicate "bound by `Δ, Γ`". -/
def LInEnv (Δ : Finset Var) (Γ : Ctx) (s : String) : Prop :=
  Var.name s ∈ Δ ∨ Res.var (.name s) ∈ Γ

theorem LInEnv.add_left {Δ : Finset Var} {Γ₁ Γ₂ : Ctx} {s : String} (h : LInEnv Δ Γ₁ s) :
    LInEnv Δ (Γ₁ + Γ₂) s := h.imp id fun h => Multiset.mem_add.mpr (.inl h)

theorem LInEnv.add_right {Δ : Finset Var} {Γ₁ Γ₂ : Ctx} {s : String} (h : LInEnv Δ Γ₂ s) :
    LInEnv Δ (Γ₁ + Γ₂) s := h.imp id fun h => Multiset.mem_add.mpr (.inr h)

theorem LInEnv.of_add_credit {Δ : Finset Var} {Γ : Ctx} {k : Nat} {s : String}
    (h : LInEnv Δ (Γ + {Res.credit k}) s) : LInEnv Δ Γ s := by
  rcases h with h | h
  · exact .inl h
  · rcases Multiset.mem_add.mp h with h | h
    · exact .inr h
    · simp at h

theorem scoped_var {Δ : Finset Var} {Γ : Ctx} {x : Var} (h : x ∈ Δ ∨ Res.var x ∈ Γ) :
    LVal.Scoped (LInEnv Δ Γ) (.var x) := by
  cases x with
  | name s => exact h
  | loc _ => trivial

mutual
theorem LWfVal.scoped {funs : List FName} :
    ∀ {Δ : Finset Var} {Γ : Ctx} {v : LVal}, LWfVal funs Δ Γ v → LVal.Scoped (LInEnv Δ Γ) v
  | _, _, _, .var x => scoped_var (.inr (Multiset.mem_singleton_self _))
  | _, _, _, .atom _ => trivial
  | _, _, _, .reuse _ _ _ _ h => LVal.ScopedList.mono (fun _ hs => hs.add_left) (LWfVals.scoped h)
  | _, _, _, .lam zs xs e h _ => by
    refine ⟨LVal.ScopedList.of_forall fun v hv => ?_, ?_⟩
    · obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hv
      exact scoped_var (.inr (by simpa [varCtx] using hz))
    · refine LExpr.Scoped.mono (fun s hs => ?_) (LWf.scoped h)
      rcases hs with hs | hs
      · simp at hs
      · rcases Multiset.mem_add.mp hs with hs | hs
        · exact .inr (mem_capturedNames (mem_varCtx hs))
        · exact .inl (mem_Binder_ctx hs)
theorem LWfVals.scoped {funs : List FName} :
    ∀ {Δ : Finset Var} {Γ : Ctx} {vs : List LVal}, LWfVals funs Δ Γ vs →
      LVal.ScopedList (LInEnv Δ Γ) vs
  | _, _, _, .nil => trivial
  | _, _, _, .cons _ _ _ _ h1 h2 =>
    ⟨LVal.Scoped.mono (fun _ hs => hs.add_left) (LWfVal.scoped h1),
      LVal.ScopedList.mono (fun _ hs => hs.add_right) (LWfVals.scoped h2)⟩
/-- **Well-formed `λfip` expressions are well scoped.** -/
theorem LWf.scoped {funs : List FName} :
    ∀ {Δ : Finset Var} {Γ : Ctx} {e : LExpr}, LWf funs Δ Γ e → LExpr.Scoped (LInEnv Δ Γ) e
  | _, _, _, .tuple h => LWfVals.scoped h
  | _, _, _, .call _ ys _ _ hys h => by
    refine ⟨LVal.ScopedList.of_forall fun y hy => ?_, LWf.scoped h⟩
    have := hys y hy
    cases y with
    | var x => exact scoped_var (.inl this)
    | fn _ => trivial
    | _ => exact this.elim
  | _, _, _, .app _ _ _ _ h1 h2 =>
    ⟨LExpr.Scoped.mono (fun _ hs => hs.add_left) (LWf.scoped h1),
      LExpr.Scoped.mono (fun _ hs => hs.add_right) (LWf.scoped h2)⟩
  | _, _, _, .letIn Γ₁ Γ₂ Γ₃ xs _ _ _ h1 h2 _ => by
    refine ⟨LExpr.Scoped.mono (fun s hs => ?_) (LWf.scoped h1),
      LExpr.Scoped.mono (fun s hs => ?_) (LWf.scoped h2)⟩
    · rcases hs with hs | hs
      · rcases Finset.mem_union.mp hs with hs | hs
        · exact .inl hs
        · have := mem_Ctx_vars (Multiset.mem_toFinset.mp hs)
          exact Or.inr (Multiset.mem_add.mpr (.inl (Multiset.mem_add.mpr (.inr this))))
      · exact LInEnv.add_left (Γ₂ := Γ₃) (LInEnv.add_left (Γ₂ := Γ₂) (Or.inr hs))
    · rcases hs with hs | hs
      · exact .inr (Or.inl hs)
      · rcases Multiset.mem_add.mp hs with hs | hs
        · refine .inr (Or.inr ?_)
          rcases Multiset.mem_add.mp hs with hs | hs
          · exact Multiset.mem_add.mpr (.inl (Multiset.mem_add.mpr (.inr hs)))
          · exact Multiset.mem_add.mpr (.inr hs)
        · exact .inl (mem_Binder_ctx hs)
  | _, _, _, .match x bs hx _ es hes hwf => by
    refine ⟨scoped_var hx, LExpr.ScopedB.of_forall fun b hb => ?_⟩
    rw [hes b hb]
    refine LExpr.Scoped.dups (fun v hv => ?_) (LExpr.Scoped.mono (fun s hs => ?_) (LWf.scoped (hwf b hb)))
    · obtain ⟨b', hb', rfl⟩ := List.mem_map.mp hv
      exact .inl (List.mem_map_of_mem hb')
    · rcases hs with hs | hs
      · exact .inr (.inl hs)
      · rcases Multiset.mem_add.mp hs with hs | hs
        · exact .inr (.inr hs)
        · exact .inl (mem_Binder_ctx hs)
  | _, _, _, .dup x hx h => by
    refine ⟨scoped_var hx, LExpr.Scoped.mono (fun s hs => ?_) (LWf.scoped h)⟩
    rcases hs with hs | hs
    · exact .inl hs
    · rcases Multiset.mem_add.mp hs with hs | hs
      · exact .inr hs
      · rw [Multiset.mem_singleton, Res.var.injEq] at hs
        subst hs; exact hx
  | _, _, _, .drop x h =>
    ⟨scoped_var (.inr (Multiset.mem_add.mpr (.inr (Multiset.mem_singleton_self _)))),
      LExpr.Scoped.mono (fun _ hs => hs.add_left) (LWf.scoped h)⟩
  | _, _, _, .dropru x _ h => by
    have ih := LWf.scoped h
    exact ⟨scoped_var (.inr (Multiset.mem_add.mpr (.inr (Multiset.mem_singleton_self _)))),
      LExpr.Scoped.mono (fun _ hs => hs.of_add_credit.add_left) ih⟩
  | _, _, _, .free _ _ h => by
    have ih := LWf.scoped h
    exact LExpr.Scoped.mono (fun _ hs => hs.add_left) ih
  | _, _, _, .alloc _ _ h => by
    have ih := LWf.scoped h
    exact LExpr.Scoped.mono (fun _ hs => hs.of_add_credit) ih
  | _, _, _, .empty h => LExpr.Scoped.mono (fun _ hs => hs.add_left) (LWf.scoped h)
end

/-- **Every well-formed closed `λfip` program is an `LTerm 0`.** -/
theorem LWf.toLTerm_closed {funs : List FName} {e : LExpr} (h : LWf funs ∅ 0 e) :
    (e.toLTerm Scope.empty).isSome := by
  rw [LExpr.toLTerm_empty_isSome_iff]
  refine LExpr.Scoped.mono (fun s hs => ?_) (LWf.scoped h)
  rcases hs with hs | hs <;> simp at hs

/-- Every function of a well-formed signature has a well-scoped body. -/
theorem LSig.Wf.toLTFunDef {sig : LSig} (h : sig.Wf) {fd : LFunDef} (hfd : fd ∈ sig) :
    fd.toLTFunDef.isSome := by
  rw [LFunDef.toLTFunDef, Option.isSome_map, LExpr.toLTerm_isSome_iff]
  refine LExpr.Scoped.mono (fun s hs => ?_) (LWf.scoped (h fd hfd).2)
  rw [FIPNamed.Scope.extend_isSome]
  simp only [FIPNamed.Scope.ofBinders, Option.isSome_map, FIPNamed.Scope.extend_isSome,
    FIPNamed.Scope.empty_isSome, Bool.false_eq_true, or_false]
  rcases hs with hs | hs
  · left; simpa [Binder.vars] using hs
  · right; exact mem_Binder_ctx hs

/-- **Every well-formed `λfip` signature `⊩ Σ` has a well-scoped version.** -/
theorem LSig.Wf.toLTSig {sig : LSig} (h : sig.Wf) : sig.toLTSig.isSome := by
  suffices ∀ l : LSig, (∀ fd ∈ l, fd ∈ sig) → (l.mapM LFunDef.toLTFunDef).isSome from
    this sig fun _ h => h
  intro l
  induction l with
  | nil => intro _; rfl
  | cons fd l ih =>
    intro hl
    have h1 := LSig.Wf.toLTFunDef h (hl fd (List.mem_cons_self ..))
    have h2 := ih (fun fd' hfd' => hl fd' (List.mem_cons_of_mem _ hfd'))
    obtain ⟨tfd, htfd⟩ := Option.isSome_iff_exists.mp h1
    obtain ⟨tsig, htsig⟩ := Option.isSome_iff_exists.mp h2
    simp [List.mapM_cons, htfd, htsig]

end FIPNamed.Lam
