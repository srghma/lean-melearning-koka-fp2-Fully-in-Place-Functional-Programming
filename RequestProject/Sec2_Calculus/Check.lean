module

public import RequestProject.Sec2_Calculus.Rules

@[expose] public section

/- ══════════════════ PAPER sec. 2.2 START: FIP: Fully In-Place: an executable checker for the rules (the paper describes the check only in prose) (PDF pp. 9-11) ══════════════════
   `check` / `Sig.check` decide the FIP/FBIP rules; this is what `[KOKA_FIP| ... ]` runs. -/

/-!
# An algorithmic FIP checker

The paper remarks that "implementing the check algorithmically is straightforward
where the owned environment becomes synthesized".  `check` decides (a sound
approximation of) `Δ | Γ ⊢ e`:

* the owned *variables* are split syntactically (by free variables) at `let`;
* the reuse and allocation credits needed by the bound expression of a `let` are
  synthesized by `demand`, and taken from the available credits (exact reuse credits
  first, then allocation credits via rule `inst`);
* leftover credits of size zero are discarded (`empty`), leftover allocation credits
  are discarded (`weaken`).

Under a binder the environments are weakened (`Var.shift`) and the new variables are
added; no freshness check is needed with de Bruijn indices.

`check_sound` (in `RequestProject/Sec2_Calculus/CheckSound.lean`) proves that a successful
check yields a derivation of `Wf`, so `check … = true` can be established by `decide` and
turned into a proof that a function is fully in-place.
-/

namespace FIP

/-- The owned environment consisting of the variables `V`, reuse credits `C` and `A`
    allocation credits. -/
def ctxOf {n : Nat} (V : List (Var n)) (C : List Nat) (A : Nat) : Ctx n :=
  ((V.map Res.var : List (Res n)) : Multiset (Res n)) +
    ((C.map Res.credit : List (Res n)) : Multiset (Res n)) + Multiset.replicate A Res.alloc

/-! ## Demands of values -/

mutual
/-- The owned variables a value consumes (those not scalar). -/
def Val.ownedUses {n : Nat} (U : List (Var n)) : Val n → List (Var n)
  | .var x => if x ∈ U then [] else [x]
  | .ctor _ vs => Val.ownedUsesList U vs
  | _ => []
/-- The owned variables a list of values consumes. -/
def Val.ownedUsesList {n : Nat} (U : List (Var n)) : List (Val n) → List (Var n)
  | [] => []
  | v :: vs => Val.ownedUses U v ++ Val.ownedUsesList U vs
end

mutual
/-- The reuse credits a value needs: one of size `k` per constructor of arity `k ≥ 1`. -/
def Val.credits {n : Nat} : Val n → List Nat
  | .ctor _ [] => []
  | .ctor _ vs => vs.length :: Val.creditsList vs
  | _ => []
/-- The reuse credits a list of values needs. -/
def Val.creditsList {n : Nat} : List (Val n) → List Nat
  | [] => []
  | v :: vs => Val.credits v ++ Val.creditsList vs
end

mutual
/-- Is the value built only from variables, constructors and literals? -/
def Val.plain {n : Nat} : Val n → Bool
  | .var _ => true
  | .ctor _ vs => Val.plainList vs
  | .lit _ => true
  | .fn _ => false
/-- `Val.plain` for lists. -/
def Val.plainList {n : Nat} : List (Val n) → Bool
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
def Expr.demand (cfg : Cfg) {n : Nat} : Expr n → List Nat × Nat
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
  | .bmatch _ bs => combineDemands (Branches.demand cfg false bs)
  | .dmatch _ bs => combineDemands (Branches.demand cfg true bs)
  | .drop _ e => Expr.demand cfg e
  | .free k e => let d := Expr.demand cfg e; (k :: d.1, d.2)
  | .prim _ _ => ([], 0)
/-- The demands of the branches of a match (a destructive match provides a credit). -/
def Branches.demand (cfg : Cfg) (destr : Bool) {n : Nat} : Branches n → List (List Nat × Nat)
  | .nil => []
  | .cons _ xs e bs =>
    let d := Expr.demand cfg e
    (if destr then (d.1.erase xs.length, d.2) else d) :: Branches.demand cfg destr bs
end

/-! ## The checker -/

/-- The variables bound by the non-scalar binders (the innermost variables). -/
abbrev Binder.ownedList {n : Nat} (xs : List Bool) : List (Var (n + xs.length)) :=
  Binder.select xs false Var.newB

/-- The variables bound by the scalar binders. -/
abbrev Binder.scalarList {n : Nat} (xs : List Bool) : List (Var (n + xs.length)) :=
  Binder.select xs true Var.newB

/-- Weaken a list of variables past `k` new binders. -/
abbrev Vars.shiftL {n : Nat} (k : Nat) (l : List (Var n)) : List (Var (n + k)) :=
  l.map (Var.shift k)

/-- Decide `BorrowArg`. -/
def borrowArgB {n : Nat} (cfg : Cfg) (U Δ : List (Var n)) : Val n → Bool
  | .var y => Δ.contains y || U.contains y
  | .fn g => cfg.funs.contains g
  | _ => false

/-- Decide `ScalarArg`. -/
def scalarArgB {n : Nat} (U Δ : List (Var n)) : Val n → Bool
  | .var y => Δ.contains y || U.contains y
  | .lit _ => true
  | _ => false

mutual
/-- The FIP checker: does `Δ | V, C, ⋄^A ⊢ e` hold (with scalar variables `U`)? -/
def check (cfg : Cfg) {n : Nat} (U Δ V : List (Var n)) (C : List Nat) (A : Nat) :
    Expr n → Bool
  | .ret vs =>
    Val.plainList vs && decide (List.Perm V (Val.ownedUsesList U vs)) &&
      creditsOk C (Val.creditsList vs) A
  | .call f (.ret ys) e =>
    let k := cfg.budget f + (ys.map (fnBudget cfg)).sum
    cfg.funs.contains f && ys.all (borrowArgB cfg U Δ) && decide (k ≤ A) &&
      check cfg U Δ V C (A - k) e
  | .app (.ret [.var y]) e => Δ.contains y && check cfg U Δ V C A e
  | .letIn xs e1 e2 =>
    let f1 := e1.fv
    let f2 := (e2.fv).filterMap (Var.unshift xs.length)
    let V1 := V.filter (fun x => f1.contains x && !f2.contains x)
    let V2 := V.filter (fun x => f1.contains x && f2.contains x)
    let V3 := V.filter (fun x => !f1.contains x)
    let d := e1.demand cfg
    let C1 := C.bagInter d.1
    let A1 := d.2 + (d.1.diff C1).length
    decide (A1 ≤ A) &&
      check cfg U (Δ ++ V2) V1 C1 A1 e1 &&
      check cfg (Vars.shiftL xs.length U ++ Binder.scalarList xs) (Vars.shiftL xs.length Δ)
        (Vars.shiftL xs.length (V2 ++ V3) ++ Binder.ownedList xs) (C.diff C1) (A - A1) e2
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
def checkB (cfg : Cfg) {n : Nat} (U Δ V : List (Var n)) (C : List Nat) (A : Nat) :
    Branches n → Bool
  | .nil => true
  | .cons _ xs e bs =>
    check cfg (Vars.shiftL xs.length U ++ Binder.scalarList xs)
      (Vars.shiftL xs.length Δ ++ Binder.ownedList xs) (Vars.shiftL xs.length V) C A e &&
    checkB cfg U Δ V C A bs
/-- Check the branches of a destructive match. -/
def checkD (cfg : Cfg) {n : Nat} (U Δ V : List (Var n)) (C : List Nat) (A : Nat) :
    Branches n → Bool
  | .nil => true
  | .cons _ xs e bs =>
    check cfg (Vars.shiftL xs.length U ++ Binder.scalarList xs) (Vars.shiftL xs.length Δ)
      (Vars.shiftL xs.length V ++ Binder.ownedList xs) (C ++ [xs.length]) A e &&
    checkD cfg U Δ V C A bs
end

/-- Check a top-level function against the signature. -/
def FunDef.check (sig : Sig) (fd : FunDef) : Bool :=
  FIP.check (sig.cfg fd.annot)
    (Binder.select fd.borrowed true fd.bParam ++ Binder.select fd.owned true fd.oParam)
    (Binder.select fd.borrowed false fd.bParam) (Binder.select fd.owned false fd.oParam)
    [] fd.annot.budget fd.body

/-- Check every annotated function of a signature. -/
def Sig.check (sig : Sig) : Bool :=
  sig.all (fun fd => fd.annot == .plain || fd.check sig)

end FIP

/- ══════════════════ PAPER sec. 2.2 END: FIP: Fully In-Place: an executable checker for the rules (the paper describes the check only in prose) ══════════════════ -/
