module

public import RequestProject.Frontend.Compile
public import RequestProject.Sec2_Calculus.Eval
public import RequestProject.Sec2_Calculus.CheckSound

@[expose] public section

/-!
# Koka modules, indexed by the names they define

A compiled Koka module is a `Koka.Module F C`, where

* `F : Finset FName` is the set of its **top-level functions**, and
* `C : Finset CName` is the set of its **constructors** (those of its own type
  declarations and the built-in `list`, `bool` and `maybe`).

The structure carries the proofs that tie the indices to the code: `F` is exactly the set
of names of the signature, these names are distinct, `C` is exactly the set of declared
constructors, and the module is **closed**: every function called or passed as a value,
and every constructor built or matched on, in any function body, belongs to `F` resp. `C`;
moreover every call passes as many borrowed and owned arguments as the function has
parameters, and every constructor is used with as many fields as it is declared with
(`Module.call_arity`, `Module.ctor_arity`).
The `[KOKA| … ]` / `[KOKA_FIP| … ]` elaborators compute `F` and `C` and prove all of this
by evaluation, so a reference to an unknown function or constructor is a compile-time
error.

Because the names are in the type, the operations of a module can demand membership
proofs, discharged by `decide` at the call site:

* `Module.fn m f hf` — *the* definition of `f ∈ F` (no `Option`);
* `Module.eval m f b o` — the result of the call `f(b; o)`, which needs `f ∈ F` and a
  proof that the call terminates (`FIP.Expr.Halts`), and **no fuel**;
* `Module.con m c args` — the value `c(args)`, which needs `c ∈ C` and the right number of
  arguments; `Module.fnVal m f` — the function `f ∈ F` as a value.
-/

namespace FIP

/-- A reference from code to a top-level name: a function passed as a value, a call of a
    function (with the numbers of borrowed and owned arguments, when the arguments are
    tuples of values), or a constructor applied to (or matched with) `arity` fields. -/
inductive Ref where
  | fn (f : FName)
  | call (f : FName) (arity : Option (Nat × Nat))
  | ctor (c : CName) (arity : Nat)
  deriving DecidableEq, Repr

/-- The numbers of borrowed and owned arguments of a call `f(e₁; e₂)`, when `e₁` and `e₂`
    are tuples of values. -/
def callArity {n : Nat} : Expr n → Expr n → Option (Nat × Nat)
  | .ret b, .ret o => some (b.length, o.length)
  | _, _ => none

mutual
/-- The functions and constructors a value mentions. -/
def Val.refs {n : Nat} : Val n → List Ref
  | .var _ => []
  | .fn f => [.fn f]
  | .ctor c vs => .ctor c vs.length :: Val.refsList vs
  | .lit _ => []
/-- The functions and constructors a list of values mentions. -/
def Val.refsList {n : Nat} : List (Val n) → List Ref
  | [] => []
  | v :: vs => Val.refs v ++ Val.refsList vs
end

mutual
/-- The functions (called or passed as values) and the constructors (built or matched on)
    an expression mentions. -/
def Expr.refs {n : Nat} : Expr n → List Ref
  | .ret vs => Val.refsList vs
  | .app e1 e2 => Expr.refs e1 ++ Expr.refs e2
  | .call f e1 e2 => .call f (callArity e1 e2) :: (Expr.refs e1 ++ Expr.refs e2)
  | .letIn _ e1 e2 => Expr.refs e1 ++ Expr.refs e2
  | .bmatch e bs => Expr.refs e ++ Branches.refs bs
  | .dmatch e bs => Expr.refs e ++ Branches.refs bs
  | .drop x e => Val.refs x ++ Expr.refs e
  | .free _ e => Expr.refs e
  | .prim _ vs => Val.refsList vs
/-- The functions and constructors the branches of a match mention. -/
def Branches.refs {n : Nat} : Branches n → List Ref
  | .nil => []
  | .cons c xs e bs => .ctor c xs.length :: (Expr.refs e ++ Branches.refs bs)
end

/-- The functions and constructors the bodies of a signature mention. -/
def Sig.refs (sig : Sig) : List Ref := sig.flatMap (·.body.refs)

end FIP

namespace Koka

open FIP

/-- The constructors in scope for the type declarations `types`: theirs and those of the
    built-in types, in order. -/
def ctorDecls (types : List TypeDecl) : List CtorDecl :=
  (types ++ builtinTypes).flatMap (·.ctors)

/-- The names of the constructors in scope for the type declarations `types`. -/
def ctorNames (types : List TypeDecl) : List CName := (ctorDecls types).map (·.name)

/-- The number of fields of the constructor `c`, if it is in scope for `types`. -/
def ctorArity? (types : List TypeDecl) (c : CName) : Option Nat :=
  ((ctorDecls types).find? (·.name == c)).map (·.fields.length)

/-- A reference is *valid* in a module with functions `F`, constructors `C`, signature
    `sig` and type declarations `types`: it names a function of `F` (called with as many
    borrowed and owned arguments as it has parameters) or a constructor of `C` (with as
    many fields as it is declared with). -/
def _root_.FIP.Ref.valid (F : Finset FName) (C : Finset CName) (sig : Sig) (types : List TypeDecl) :
    Ref → Bool
  | .fn f => decide (f ∈ F)
  | .call f none => decide (f ∈ F)
  | .call f (some (b, o)) =>
    decide (f ∈ F) && match sig.lookup f with
      | some fd => fd.borrowed.length == b && fd.owned.length == o
      | none => false
  | .ctor c k => decide (c ∈ C) && ctorArity? types c == some k

/-- A compiled Koka module defining the functions `F` and the constructors `C`. -/
structure Module (F : Finset FName) (C : Finset CName) where
  /-- The type declarations of the module. -/
  types : List TypeDecl
  /-- The compiled functions: the signature `Σ` of the calculus. -/
  sig : Sig
  /-- `F` is the set of functions of the module. -/
  funs_eq : sig.names.toFinset = F
  /-- The functions of the module have distinct names. -/
  names_nodup : sig.names.Nodup
  /-- `C` is the set of constructors in scope (the module's and the built-in ones). -/
  ctors_eq : (ctorNames types).toFinset = C
  /-- The module is closed and arities agree: its code mentions only functions of `F`
      and constructors of `C`, every call passes as many borrowed and owned arguments as
      the function has parameters, and every constructor is built or matched with as
      many fields as it is declared with. -/
  closed : ∀ r ∈ sig.refs, r.valid F C sig types = true

/-- `koka_arity` proves that a list of arguments has the length a constructor expects:
    `decide`, after computing the length of the list literal (whose elements may depend on
    a variable scope). -/
macro "koka_arity" : tactic =>
  `(tactic| first | decide | (simp only [List.length_cons, List.length_nil]; decide))

/-- A Koka module whose annotated functions are proved fully in-place (`fip`) or
    functional but in-place (`fbip`): `⊩ Σ`. -/
structure FipModule (F : Finset FName) (C : Finset CName) extends Module F C where
  wf : sig.Wf

namespace Module

variable {F : Finset FName} {C : Finset CName} (m : Module F C)

theorem mem_funs_iff {f : FName} : f ∈ F ↔ f ∈ m.sig.names := by
  rw [← List.mem_toFinset, m.funs_eq]

theorem lookup_isSome {f : FName} (hf : f ∈ F) : (m.sig.lookup f).isSome :=
  Sig.lookup_isSome_of_mem_names ((m.mem_funs_iff).mp hf)

/-- The definition of the function `f` of the module. -/
def fn (f : FName) (hf : f ∈ F) : FunDef := (m.sig.lookup f).get (m.lookup_isSome hf)

theorem lookup_fn {f : FName} (hf : f ∈ F) : m.sig.lookup f = some (m.fn f hf) := by
  simp [fn]

@[simp] theorem fn_name {f : FName} (hf : f ∈ F) : (m.fn f hf).name = f :=
  (Sig.lookup_mem (m.lookup_fn hf)).2

theorem fn_mem {f : FName} (hf : f ∈ F) : m.fn f hf ∈ m.sig :=
  (Sig.lookup_mem (m.lookup_fn hf)).1

/-- A function of the module, as a value (to be passed to a second-order function). -/
def fnVal {n : Nat} (f : FName) (hf : f ∈ F := by decide) : Val n := .fn (m.fn f hf).name

/-- The declaration of the constructor `c` of the module. -/
def ctorDecl (c : CName) (hc : c ∈ C) : CtorDecl :=
  ((ctorDecls m.types).find? (·.name == c)).get (by
    rw [← m.ctors_eq, List.mem_toFinset] at hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    exact List.find?_isSome.mpr ⟨d, hd, by simp⟩)

/-- The number of fields of the constructor `c`. -/
def arity (c : CName) (hc : c ∈ C) : Nat := (m.ctorDecl c hc).fields.length

/-- The value `c(args)`, for a constructor `c` of the module applied to as many arguments
    as it has fields. -/
def con {n : Nat} (c : CName) (args : List (Val n)) (hc : c ∈ C := by decide)
    (_ha : args.length = m.arity c hc := by koka_arity) : Val n :=
  .ctor (m.ctorDecl c hc).name args

/-- The atom `c`, for a constructor `c` of the module without fields. -/
def atom {n : Nat} (c : CName) (hc : c ∈ C := by decide)
    (ha : 0 = m.arity c hc := by decide) : Val n :=
  m.con c [] hc ha

/-! ## What closedness guarantees -/

/-- A function the code mentions (called or passed as a value) is a function of `F`. -/
theorem fn_mem_of_refs {f : FName} (h : Ref.fn f ∈ m.sig.refs) : f ∈ F := by
  simpa [Ref.valid] using m.closed _ h

/-- A call in the code passes as many borrowed and owned arguments as the function
    called has parameters. -/
theorem call_arity {f : FName} {b o : Nat} (h : Ref.call f (some (b, o)) ∈ m.sig.refs) :
    ∃ hf : f ∈ F, (m.fn f hf).borrowed.length = b ∧ (m.fn f hf).owned.length = o := by
  have hv := m.closed _ h
  simp only [Ref.valid, Bool.and_eq_true, decide_eq_true_eq] at hv
  obtain ⟨hf, hl⟩ := hv
  refine ⟨hf, ?_⟩
  rw [m.lookup_fn hf] at hl
  simpa using hl

/-- A constructor the code builds or matches on is a constructor of `C`, with as many
    fields as it is declared with. -/
theorem ctor_arity {c : CName} {k : Nat} (h : Ref.ctor c k ∈ m.sig.refs) :
    ∃ hc : c ∈ C, m.arity c hc = k := by
  have hv := m.closed _ h
  simp only [Ref.valid, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hv
  obtain ⟨hc, ha⟩ := hv
  refine ⟨hc, ?_⟩
  unfold arity ctorDecl
  unfold ctorArity? at ha
  obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.mp ha
  simp [hd]

/-! ## Evaluation -/

/-- The call `f(e₁; e₂)` of the function `f` of the module. -/
def call {n : Nat} (f : FName) (e1 e2 : FIP.Expr n) (hf : f ∈ F := by decide) : FIP.Expr n :=
  .call (m.fn f hf).name e1 e2

@[simp] theorem call_eq {n : Nat} {f : FName} (e1 e2 : FIP.Expr n) (hf : f ∈ F) :
    m.call f e1 e2 hf = .call f e1 e2 := by
  simp [call]

/-- The call `f(b; o)` of the function `f` of the module, on values. -/
def callE (f : FName) (hf : f ∈ F) (b o : List (Val 0)) : FIP.Expr 0 :=
  m.call f (.ret b) (.ret o) hf

@[simp] theorem callE_eq {f : FName} (hf : f ∈ F) (b o : List (Val 0)) :
    m.callE f hf b o = .call f (.ret b) (.ret o) := by
  simp [callE]

/-- The result of the call `f(b; o)` of a function `f ∈ F`, given a proof that the call
    terminates.  There is no fuel: by default the proof of termination is found by running
    the interpreter (`fip_halts`). -/
def eval (f : FName) (b o : List (Val 0)) (hf : f ∈ F := by decide)
    (h : (m.callE f hf b o).Halts m.sig := by fip_halts) : List (Val 0) :=
  (m.callE f hf b o).evalTotal m.sig h

/-- `Module.eval` is sound: the call reduces to the computed values. -/
theorem eval_sound {f : FName} {b o : List (Val 0)} {hf : f ∈ F}
    {h : (m.callE f hf b o).Halts m.sig} :
    Steps m.sig (.call f (.ret b) (.ret o)) (.ret (m.eval f b o hf h)) := by
  convert Expr.evalTotal_sound h using 1
  simp

/-- `Module.eval` gives the only possible result of the call. -/
theorem eval_unique {f : FName} {b o vs : List (Val 0)} {hf : f ∈ F}
    {h : (m.callE f hf b o).Halts m.sig} (hs : Steps m.sig (.call f (.ret b) (.ret o)) (.ret vs)) :
    m.eval f b o hf h = vs :=
  Expr.evalTotal_unique h (by simpa using hs)

/-- The result of an arbitrary closed expression, given a proof that it terminates. -/
def evalExpr (e : FIP.Expr 0) (h : e.Halts m.sig := by fip_halts) : List (Val 0) :=
  e.evalTotal m.sig h

theorem evalExpr_sound {e : FIP.Expr 0} {h : e.Halts m.sig} :
    Steps m.sig e (.ret (m.evalExpr e h)) :=
  Expr.evalTotal_sound h

end Module

end Koka
