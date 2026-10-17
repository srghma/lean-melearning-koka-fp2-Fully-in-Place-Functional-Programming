module

public import RequestProject.Named.Sec2_Calculus.Rules

@[expose] public section

/-!
# An algorithmic FIPNamed checker

The paper remarks that "implementing the check algorithmically is straightforward
where the owned environment becomes synthesized".  `check` decides (a sound
approximation of) `Δ | Γ ⊢ e`:

* the owned *variables* are split syntactically (by free variables) at `let`;
* the reuse and allocation credits needed by the bound expression of a `let` are
  synthesized by `demand`, and taken from the available credits (exact reuse credits
  first, then allocation credits via rule `inst`);
* leftover credits of size zero are discarded (`empty`), leftover allocation credits
  are discarded (`weaken`).

`check_sound` (in `RequestProject/Sec2_Calculus/CheckSound.lean`) proves that a successful check
yields a derivation of `Wf`, so `check … = true` can be established by `decide` and
turned into a proof that a function is fully in-place.
-/

namespace FIPNamed

/-- The owned environment consisting of the variables `V`, reuse credits `C` and `A`
    allocation credits. -/
def ctxOf (V : List Var) (C : List Nat) (A : Nat) : Ctx :=
  ((V.map Res.var : List Res) : Multiset Res) + ((C.map Res.credit : List Res) : Multiset Res)
    + Multiset.replicate A Res.alloc

/-! ## Demands of values -/

mutual
/-- The owned variables a value consumes (those not scalar). -/
def Val.ownedUses (U : List Var) : Val → List Var
  | .var x => if x ∈ U then [] else [x]
  | .ctor _ vs => Val.ownedUsesList U vs
  | _ => []
/-- The owned variables a list of values consumes. -/
def Val.ownedUsesList (U : List Var) : List Val → List Var
  | [] => []
  | v :: vs => Val.ownedUses U v ++ Val.ownedUsesList U vs
end

mutual
/-- The reuse credits a value needs: one of size `k` per constructor of arity `k ≥ 1`. -/
def Val.credits : Val → List Nat
  | .ctor _ [] => []
  | .ctor _ vs => vs.length :: Val.creditsList vs
  | _ => []
/-- The reuse credits a list of values needs. -/
def Val.creditsList : List Val → List Nat
  | [] => []
  | v :: vs => Val.credits v ++ Val.creditsList vs
end

mutual
/-- Is the value built only from variables, constructors and literals? -/
def Val.plain : Val → Bool
  | .var _ => true
  | .ctor _ vs => Val.plainList vs
  | .lit _ => true
  | .fn _ => false
/-- `Val.plain` for lists. -/
def Val.plainList : List Val → Bool
  | [] => true
  | v :: vs => Val.plain v && Val.plainList vs
end

/-- Can the reuse credits `C` and `A` allocation credits pay exactly for the demanded
    reuse credits `D` (discarding zero-size credits and unused allocation credits)? -/
def creditsOk : List Nat → List Nat → Nat → Bool
  | [], D, A => D.all (1 ≤ ·) && decide (D.length ≤ A)
  | 0 :: C, D, A => creditsOk C D A
  | c :: C, D, A => D.contains c && creditsOk C (D.erase c) A

/-! ## Synthesized credit demands -/

/-- Combine the demands of the branches of a match: the reuse credits demanded by all
    branches, plus enough allocation credits for the rest. -/
def combineDemands : List (List Nat × Nat) → List Nat × Nat
  | [] => ([], 0)
  | d :: ds =>
    let common := ds.foldl (fun acc d' => acc.bagInter d'.1) d.1
    (common, (d :: ds).foldl (fun m d' => max m (d'.2 + (d'.1.diff common).length)) 0)

mutual
/-- The reuse credits and allocation credits an expression needs from its context. -/
def Expr.demand (cfg : Cfg) : Expr → List Nat × Nat
  | .ret vs => (Val.creditsList vs, 0)
  | .call f (.ret ys) e =>
    let d := Expr.demand cfg e
    (d.1, d.2 + cfg.budget f + (ys.map (fnBudget cfg)).sum)
  | .call _ _ e => Expr.demand cfg e
  | .app _ e => Expr.demand cfg e
  | .letIn _ e1 e2 =>
    let d1 := Expr.demand cfg e1
    let d2 := Expr.demand cfg e2
    (d1.1 ++ d2.1, d1.2 + d2.2)
  | .bmatch _ bs => combineDemands (Expr.demandB cfg false bs)
  | .dmatch _ bs => combineDemands (Expr.demandB cfg true bs)
  | .drop _ e => Expr.demand cfg e
  | .free k e => let d := Expr.demand cfg e; (k :: d.1, d.2)
  | .prim _ _ => ([], 0)
/-- The demands of the branches of a match (a destructive match provides a credit). -/
def Expr.demandB (cfg : Cfg) (destr : Bool) : List Branch → List (List Nat × Nat)
  | [] => []
  | .mk _ xs e :: bs =>
    let d := Expr.demand cfg e
    (if destr then (d.1.erase xs.length, d.2) else d) :: Expr.demandB cfg destr bs
end

/-! ## The checker -/

/-- The variables bound by the non-scalar binders. -/
def Binder.ownedList (xs : List Binder) : List Var :=
  (xs.filter (fun b => !b.scalar)).map (fun b => Var.name b.name)

/-- The variables bound by the scalar binders. -/
def Binder.scalarList (xs : List Binder) : List Var :=
  (xs.filter (fun b => b.scalar)).map (fun b => Var.name b.name)

/-- Decide `Binder.Fresh` for an environment with owned variables `V`. -/
def Binder.freshB (xs : List Binder) (U Δ V : List Var) : Bool :=
  decide (xs.map (·.name)).Nodup &&
  xs.all (fun b => !(U.contains (.name b.name)) && !(Δ.contains (.name b.name)) &&
    !(V.contains (.name b.name)))

/-- Decide `BorrowArg`. -/
def borrowArgB (cfg : Cfg) (U Δ : List Var) : Val → Bool
  | .var y => Δ.contains y || U.contains y
  | .fn g => cfg.funs.contains g
  | _ => false

/-- Decide `ScalarArg`. -/
def scalarArgB (U Δ : List Var) : Val → Bool
  | .var y => Δ.contains y || U.contains y
  | .lit _ => true
  | _ => false

mutual
/-- The FIPNamed checker: does `Δ | V, C, ⋄^A ⊢ e` hold (with scalar variables `U`)? -/
def check (cfg : Cfg) (U Δ V : List Var) (C : List Nat) (A : Nat) : Expr → Bool
  | .ret vs =>
    Val.plainList vs && decide (List.Perm V (Val.ownedUsesList U vs)) &&
      creditsOk C (Val.creditsList vs) A
  | .call f (.ret ys) e =>
    let n := cfg.budget f + (ys.map (fnBudget cfg)).sum
    cfg.funs.contains f && ys.all (borrowArgB cfg U Δ) && decide (n ≤ A) &&
      check cfg U Δ V C (A - n) e
  | .app (.ret [.var y]) e => Δ.contains y && check cfg U Δ V C A e
  | .letIn xs e1 e2 =>
    let f1 := e1.fv
    let f2 := e2.fv
    let V1 := V.filter (fun x => f1.contains x && !f2.contains x)
    let V2 := V.filter (fun x => f1.contains x && f2.contains x)
    let V3 := V.filter (fun x => !f1.contains x)
    let d := e1.demand cfg
    let C1 := C.bagInter d.1
    let A1 := d.2 + (d.1.diff C1).length
    decide (A1 ≤ A) &&
      Binder.freshB xs U Δ (V2 ++ V3) &&
      check cfg U (Δ ++ V2) V1 C1 A1 e1 &&
      check cfg (U ++ Binder.scalarList xs) Δ (V2 ++ V3 ++ Binder.ownedList xs)
        (C.diff C1) (A - A1) e2
  | .bmatch (.ret [.var y]) bs =>
    (Δ.contains y || U.contains y) && checkB cfg U Δ V C A bs
  | .dmatch (.ret [.var x]) bs =>
    V.contains x && checkD cfg U Δ (V.erase x) C A bs
  | .drop (.var x) e =>
    cfg.fbip && V.contains x && check cfg U Δ (V.erase x) C A e
  | .free k e =>
    cfg.fbip && decide (1 ≤ k) && C.contains k && check cfg U Δ V (C.erase k) A e
  | .prim _ vs =>
    vs.all (scalarArgB U Δ) && V.isEmpty && C.all (· == 0)
  | _ => false
/-- Check the branches of a borrowing match. -/
def checkB (cfg : Cfg) (U Δ V : List Var) (C : List Nat) (A : Nat) : List Branch → Bool
  | [] => true
  | .mk _ xs e :: bs =>
    Binder.freshB xs U Δ V &&
    check cfg (U ++ Binder.scalarList xs) (Δ ++ Binder.ownedList xs) V C A e &&
    checkB cfg U Δ V C A bs
/-- Check the branches of a destructive match. -/
def checkD (cfg : Cfg) (U Δ V : List Var) (C : List Nat) (A : Nat) : List Branch → Bool
  | [] => true
  | .mk _ xs e :: bs =>
    Binder.freshB xs U Δ V &&
    check cfg (U ++ Binder.scalarList xs) Δ (V ++ Binder.ownedList xs) (C ++ [xs.length])
      A e &&
    checkD cfg U Δ V C A bs
end

/-- Check a top-level function against the signature. -/
def FunDef.check (sig : Sig) (fd : FunDef) : Bool :=
  decide ((fd.borrowed ++ fd.owned).map (·.name)).Nodup &&
  FIPNamed.check (sig.cfg fd.annot) (Binder.scalarList fd.borrowed ++ Binder.scalarList fd.owned)
    (Binder.ownedList fd.borrowed) (Binder.ownedList fd.owned) [] fd.annot.budget fd.body

/-- Check every annotated function of a signature. -/
def Sig.check (sig : Sig) : Bool :=
  sig.all (fun fd => fd.annot == .plain || fd.check sig)

end FIPNamed
