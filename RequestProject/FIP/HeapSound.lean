module

public import RequestProject.FIP.HeapMatch

@[expose] public section

/-!
# Theorem 6: soundness of the heap semantics (corrected statement)

The main invariant is proved by strong induction on the length of the functional
reduction and, inside it, by recursion on the derivation of `Δ | Γ ⊢ e`.
-/

namespace FIP.Lam

variable {sig : LSig}

theorem hmain_step (hsig : sig.Wf) (hsigA : sig.Adm) {n : Nat} (IH : ∀ m < n, HMainClaim sig m) :
    ∀ {Δ : Finset Var} {Γ : Ctx} {e : LExpr}, LWf sig.funs Δ Γ e → e.Adm →
    ∀ {H : Heap} {R : Multiset Var} {RC : Multiset Nat} {σ : Nat → Option LVal}
      {vs : List LVal}, HInv sig.funs H R RC Γ σ → (∀ x ∈ Δ, x ∈ R) →
      LStepsN sig n (e.subst (locS σ)) (.ret vs) → HeapResult sig H R RC e σ vs
  | _, _, _, .tuple hvs, hadm, _, _, _, _, _, h, _, hev => case_tuple hvs hadm h hev
  | _, _, _, .call _ _ _ _ hys he, hadm, _, _, _, _, _, h, hΔ, hev =>
    case_call IH hsig hsigA hys he hadm h hΔ hev
  | _, _, _, .app _ _ _ _ he₁ he₂, hadm, _, _, _, _, _, h, hΔ, hev =>
    case_app IH he₁ he₂ hadm h hΔ hev
  | _, _, _, .letIn _ _ _ _ _ _ _ he₁ he₂ hfr, hadm, _, _, _, _, _, h, hΔ, hev =>
    case_letIn IH he₁ he₂ hfr hadm h hΔ hev
  | _, _, _, .match _ _ hx hfr es hes hwf, hadm, _, _, _, _, _, h, hΔ, hev =>
    case_match IH hx hfr es hes hwf hadm h hΔ hev
  | _, _, _, .dup _ hx he, hadm, _, _, _, _, _, h, hΔ, hev => case_dup IH hx he hadm h hΔ hev
  | _, _, _, .drop _ he, hadm, _, _, _, _, _, h, hΔ, hev => case_drop IH he hadm h hΔ hev
  | _, _, _, .dropru _ _ _, hadm, _, _, _, _, _, _, _, _ => by cases hadm
  | _, _, _, .free _ hk he, hadm, _, _, _, _, _, h, hΔ, hev => case_free IH hk he hadm h hΔ hev
  | _, _, _, .alloc _ _ he, hadm, _, _, _, _, _, h, hΔ, hev => case_alloc IH he hadm h hΔ hev
  | _, _, _, .empty he, hadm, _, _, _, _, _, h, hΔ, hev =>
    hmain_step hsig hsigA IH he hadm h.of_empty hΔ hev

theorem hmain (hsig : sig.Wf) (hsigA : sig.Adm) : ∀ n, HMainClaim sig n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH => exact fun hwf hadm => hmain_step hsig hsigA IH hwf hadm

end FIP.Lam
