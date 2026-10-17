module

public import RequestProject.Named.AppE_HeapSoundness.LamDeBruijnSim

@[expose] public section

/-!
# Why the de Bruijn semantics of `λfip` substitutes into closures

The body `(λ^z x. z) D` of `let z = C in (λ^z x. z) D`, before and after the
substitution `z := C` of the `let` step.  The named substitution turns the lambda into
`λ^C x. C`: the captured value **and the body** now mention `C`.  The plain de Bruijn
substitution `LTerm.subst` only rewrites the captured value, so the result is not the
resolution of the named reduct (`plain_subst_does_not_commute`), while the
closure-instantiating substitution `LTerm.isubst` of the semantics gives exactly that
resolution (`isubst_commutes_example`), as `LExpr.toLTerm_subst` proves in general.
-/

namespace FIPNamed.Lam

/-- `(λ^z x. z) D`, with `z` free. -/
def closureExample : LExpr :=
  .app (.ret [.lam [.var (.name "z")] [{ name := "x" }] (.ret [.var (.name "z")])])
    (.ret [.ctor "D" []])

/-- Its de Bruijn representation in the scope of `z`. -/
def closureExampleT : LTerm (0 + 1) :=
  .app (.ret (.one (.lam (.one (.bvar ⟨0, by decide⟩)) [false] (.ret (.one (.bvar ⟨1, by decide⟩))))))
    (.ret (.one (.ctor "D" .nil)))

theorem closureExample_toLTerm :
    closureExample.toLTerm (Scope.empty.extend [{ name := "z" }]) = some closureExampleT := rfl

/-- `[z := C]` on the de Bruijn side. -/
def closureExampleInst : Fin (0 + 1) → LTVal 0 :=
  LSubst'.inst (LTVals.one (.ctor "C" .nil)) rfl LTVal.bvar

/-- The named reduct: `C` replaces `z` in the captured values and in the body. -/
theorem closureExample_subst :
    closureExample.subst (lzip [{ name := "z" }] [.ctor "C" []]) =
      .app (.ret [.lam [.ctor "C" []] [{ name := "x" }] (.ret [.ctor "C" []])])
        (.ret [.ctor "D" []]) := by
  simp [closureExample, LExpr.subst, LVal.substList, LVal.subst, LSubst.remove_name, lzip]

/-- With the plain substitution, name resolution does **not** commute with substitution. -/
theorem plain_subst_does_not_commute :
    (closureExample.subst (lzip [{ name := "z" }] [.ctor "C" []])).toLTerm Scope.empty ≠
      some (closureExampleT.subst closureExampleInst) := by
  intro h
  have h' : (closureExample.subst (lzip [{ name := "z" }] [.ctor "C" []])).toLTerm Scope.empty =
      some (.app (.ret (.one (.lam (.one (.ctor "C" .nil)) [false]
        (.ret (.one (.ctor "C" .nil)))))) (.ret (.one (.ctor "D" .nil)))) := by
    rw [closureExample_subst]; rfl
  rw [h'] at h
  simp [closureExampleT, closureExampleInst, LTerm.subst, LTVal.subst, LTVals.subst] at h

/-- With the closure-instantiating substitution, it does. -/
theorem isubst_commutes_example :
    (closureExample.subst (lzip [{ name := "z" }] [.ctor "C" []])).toLTerm Scope.empty =
      some (closureExampleT.isubst closureExampleInst) := by
  rw [closureExample_subst]; rfl

end FIPNamed.Lam
