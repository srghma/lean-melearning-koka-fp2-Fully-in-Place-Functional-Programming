module

public import RequestProject.AppE_HeapSoundness.HeapCex

@[expose] public section

/- ══════════════════ PAPER sec. 5.3, App. E START: Soundness of the Heap Semantics: the admissible fragment (PDF pp. 25-26; App. E.2-E.6 on pp. 75-85) ══════════════════
   The two restrictions under which Theorem 6 holds (`LExpr.Adm`), renaming substitutions by
   locations, and composition of substitutions. -/

/-!
# The admissible fragment of `λfip`

`HeapCex.lean` shows that Theorem 6 fails for two features of `λfip`.  The corrected
theorem (`HeapSound.lean`) is stated for the **admissible** expressions, `LExpr.Adm`:

* **no function values**: `LVal.fn` does not occur (in particular a borrowed argument of a
  call is a variable);
* **`dropru x; e` only with the size of `x`**: the size `k` recorded in `dropru x k` must be
  the number of fields of the constructor `x` was matched against.  This is tracked by a
  *size environment* `sz : Fin n → Option Nat`: in the branch `C x̄ ↦ e` (with `k` fields) of
  `match x`, the environment records that `x` has size `k` (`SzEnv.branch`), and
  `dropru x k'` is admissible only if `sz x = some k'`.  This is exactly the shape produced by
  the translation of a destructive match (`LWf.dmatch_translation`, see
  `dmatchBranches_adm`).

The file also introduces the substitutions used in the proof: a substitution
`ρ : Fin m → Nat` of locations for the variables in scope (`LSubst.locs ρ`) and its action
on variables (`Var.ren`) and environments (`Ctx.ren`).
-/

namespace FIP.Lam

/-! ## Size environments -/

/-- A size environment under `k` new binders (which have no known size). -/
def SzEnv.up {m : Nat} (k : Nat) (sz : Fin m → Option Nat) : Fin (m + k) → Option Nat :=
  fun i => if h : i.val < k then none else sz ⟨i.val - k, by omega⟩

/-- The size environment of a branch of `match x` binding `k` fields: `x` has size `k`. -/
def SzEnv.branch {m : Nat} (sz : Fin m → Option Nat) (x : LVal m) (k : Nat) :
    Fin (m + k) → Option Nat :=
  match x with
  | .var (.bvar j) => fun i => if i.val = k + j.val then some k else SzEnv.up k sz i
  | _ => SzEnv.up k sz

/-! ## Admissible expressions -/

mutual
/-- An admissible value: no function values. -/
def LVal.Adm {n : Nat} : LVal n → Prop
  | .var _ => True
  | .fn _ => False
  | .ctor _ vs => LVals.Adm vs
  | .lam zs _ _ b => LVals.Adm zs ∧ LExpr.Adm (fun _ => none) b
/-- Admissible values. -/
def LVals.Adm {n : Nat} : LVals n → Prop
  | .nil => True
  | .cons v vs => LVal.Adm v ∧ LVals.Adm vs
/-- An admissible expression, for the size environment `sz`: no function values, and
    `dropru x k` only for a variable `x` of known size `k`. -/
def LExpr.Adm {n : Nat} (sz : Fin n → Option Nat) : LExpr n → Prop
  | .ret vs => LVals.Adm vs
  | .app e1 e2 => LExpr.Adm sz e1 ∧ LExpr.Adm sz e2
  | .call _ e1 e2 => LExpr.Adm sz e1 ∧ LExpr.Adm sz e2
  | .letIn k e1 e2 => LExpr.Adm sz e1 ∧ LExpr.Adm (SzEnv.up k sz) e2
  | .match x bs => LVal.Adm x ∧ LBranches.Adm sz x bs
  | .dup x e => LVal.Adm x ∧ LExpr.Adm sz e
  | .drop x e => LVal.Adm x ∧ LExpr.Adm sz e
  | .dropru x k e => (∃ i, x = .var (.bvar i) ∧ sz i = some k) ∧ LExpr.Adm sz e
  | .free _ e => LExpr.Adm sz e
  | .alloc _ e => LExpr.Adm sz e
/-- Admissible branches of `match x`. -/
def LBranches.Adm {n : Nat} (sz : Fin n → Option Nat) (x : LVal n) : LBranches n → Prop
  | .nil => True
  | .cons _ k e bs => LExpr.Adm (SzEnv.branch sz x k) e ∧ LBranches.Adm sz x bs
end

/-- An admissible signature: every function body is admissible. -/
def LSig.Adm (sig : LSig) : Prop := ∀ fd ∈ sig, fd.body.Adm (fun _ => none)

theorem LVals.adm_iff {n : Nat} : ∀ vs : LVals n, vs.Adm ↔ ∀ v ∈ vs.toList, v.Adm
  | .nil => by simp [LVals.Adm]
  | .cons v vs => by simp [LVals.Adm, LVals.adm_iff vs]

theorem LBranches.adm_mem {n : Nat} {sz : Fin n → Option Nat} {x : LVal n} :
    ∀ {bs : LBranches n}, bs.Adm sz x → ∀ b ∈ bs.toList, b.body.Adm (SzEnv.branch sz x b.k)
  | .nil, _, b, hb => by simp at hb
  | .cons c k e bs, h, b, hb => by
    simp only [LBranches.toList_cons, List.mem_cons] at hb
    rcases hb with rfl | hb
    · exact h.1
    · exact LBranches.adm_mem h.2 b hb

theorem LExpr.adm_dups {n : Nat} {sz : Fin n → Option Nat} :
    ∀ (vs : List (LVal n)) {e : LExpr n}, (dups vs e).Adm sz → e.Adm sz
  | [], _, h => h
  | _ :: vs, _, h => LExpr.adm_dups vs h.2

theorem LExpr.adm_dups_iff {n : Nat} {sz : Fin n → Option Nat} :
    ∀ (vs : List (LVal n)) (e : LExpr n), (dups vs e).Adm sz ↔ (∀ v ∈ vs, v.Adm) ∧ e.Adm sz
  | [], e => by simp [dups]
  | v :: vs, e => by
    simp only [dups, LExpr.Adm, LExpr.adm_dups_iff vs e, List.mem_cons, forall_eq_or_imp]
    tauto

/-- The translation of a destructive match is admissible: in each branch, the `dropru x`
    has the size of the branch. -/
theorem dmatchBranches_adm {n : Nat} (sz : Fin n → Option Nat) (i : Fin n) :
    ∀ (bs : LBranches n),
      (∀ b ∈ bs.toList, b.body.Adm (SzEnv.branch sz (.var (.bvar i)) b.k)) →
      (dmatchBranches (.bvar i) bs).Adm sz (.var (.bvar i))
  | .nil, _ => trivial
  | .cons c k e r, h => by
    refine ⟨?_, dmatchBranches_adm sz i r (fun b hb => h b (by simp [hb]))⟩
    rw [LExpr.adm_dups_iff]
    refine ⟨fun v hv => ?_, ⟨⟨k + i.val, by omega⟩, rfl, ?_⟩, h ⟨c, k, e⟩ (by simp)⟩
    · simp only [bvals, List.mem_map] at hv
      obtain ⟨_, _, rfl⟩ := hv; exact trivial
    · simp [SzEnv.branch]

/-! ## Substitutions of locations for variables -/

/-- The substitution of the locations `ρ i` for the variables `i` in scope. -/
def LSubst.locs {m : Nat} (ρ : Fin m → Nat) : Fin m → LVal 0 := fun i => .var (.loc (ρ i))

/-- A location, as a value. -/
abbrev locV (l : Nat) : LVal 0 := .var (.loc l)

/-- The value of a location, as a value of any scope. -/
abbrev locVn {n : Nat} (l : Nat) : LVal n := .var (.loc l)

/-- The action of `ρ` on a variable. -/
def _root_.FIP.Var.ren {m : Nat} (ρ : Fin m → Nat) : Var m → Var 0
  | .bvar i => .loc (ρ i)
  | .loc l => .loc l

/-- The action of `ρ` on a resource. -/
def _root_.FIP.Res.ren {m : Nat} (ρ : Fin m → Nat) : Res m → Res 0
  | .var x => .var (x.ren ρ)
  | .credit k => .credit k
  | .alloc => .alloc

/-- The action of `ρ` on an environment. -/
def Ctx.ren {m : Nat} (ρ : Fin m → Nat) (Γ : Ctx m) : Ctx 0 := Γ.map (Res.ren ρ)

/-- Discard the reuse credits of size `0`, which occupy no memory. -/
def nzCtx (Γ : Ctx 0) : Ctx 0 := Γ.filter (· ≠ Res.credit 0)

/-- `ρ` extended by the `k` locations `xs` for `k` new binders. -/
def instN {m : Nat} (k : Nat) (xs : List Nat) (ρ : Fin m → Nat) : Fin (m + k) → Nat :=
  fun i => if h : i.val < k then xs.getD i.val 0 else ρ ⟨i.val - k, by omega⟩

/-- The locations `xs` for a scope of `k` variables. -/
def ofListN (k : Nat) (xs : List Nat) : Fin k → Nat := fun i => xs.getD i.val 0

@[simp] theorem Ctx.ren_add {m : Nat} (ρ : Fin m → Nat) (Γ Γ' : Ctx m) :
    Ctx.ren ρ (Γ + Γ') = Ctx.ren ρ Γ + Ctx.ren ρ Γ' := by simp [Ctx.ren]

@[simp] theorem Ctx.ren_singleton {m : Nat} (ρ : Fin m → Nat) (r : Res m) :
    Ctx.ren ρ {r} = {r.ren ρ} := by simp [Ctx.ren]

@[simp] theorem Ctx.ren_zero {m : Nat} (ρ : Fin m → Nat) : Ctx.ren ρ 0 = 0 := by simp [Ctx.ren]

@[simp] theorem nzCtx_add (Γ Γ' : Ctx 0) : nzCtx (Γ + Γ') = nzCtx Γ + nzCtx Γ' := by
  simp [nzCtx, Multiset.filter_add]

@[simp] theorem nzCtx_zero : nzCtx 0 = 0 := by simp [nzCtx]

@[simp] theorem nzCtx_var (x : Var 0) : nzCtx {Res.var x} = {Res.var x} := by
  simp [nzCtx]

@[simp] theorem nzCtx_credit_zero : nzCtx {Res.credit 0} = 0 := by simp [nzCtx]

theorem nzCtx_credit {k : Nat} (hk : k ≠ 0) : nzCtx {Res.credit k} = {Res.credit k} := by
  simp [nzCtx, hk]

theorem LVal.subst_locs_var {m : Nat} (ρ : Fin m → Nat) (x : Var m) :
    (LVal.var x).subst (LSubst.locs ρ) = .var (x.ren ρ) := by
  cases x <;> rfl

theorem Var.ren_shift {m : Nat} (k : Nat) (xs : List Nat) (ρ : Fin m → Nat) (x : Var m) :
    (x.shift k).ren (instN k xs ρ) = x.ren ρ := by
  cases x with
  | loc l => rfl
  | bvar i =>
    simp only [Var.shift, Var.ren, instN, show ¬ (k + i.val < k) by omega, dite_false]
    congr 2; ext; simp

theorem Var.ren_newB {m k : Nat} (xs : List Nat) (ρ : Fin m → Nat) (j : Fin k) :
    (Var.newB j : Var (m + k)).ren (instN k xs ρ) = .loc (xs.getD j.val 0) := by
  simp [Var.newB, Var.ren, instN]

theorem Res.ren_shift {m : Nat} (k : Nat) (xs : List Nat) (ρ : Fin m → Nat) (r : Res m) :
    (r.shift k).ren (instN k xs ρ) = r.ren ρ := by
  cases r <;> simp [Res.shift, Res.ren, Var.ren_shift]

theorem Ctx.ren_shift {m : Nat} (k : Nat) (xs : List Nat) (ρ : Fin m → Nat) (Γ : Ctx m) :
    Ctx.ren (instN k xs ρ) (Ctx.shift k Γ) = Ctx.ren ρ Γ := by
  simp [Ctx.ren, Ctx.shift, Multiset.map_map, Res.ren_shift]

/-- The locations `xs`, as owned resources. -/
def locsCtx (xs : List Nat) : Ctx 0 := ((xs.map fun l => Res.var (.loc l) : List (Res 0)))

@[simp] theorem locsCtx_nil : locsCtx [] = 0 := rfl

@[simp] theorem locsCtx_cons (l : Nat) (xs : List Nat) :
    locsCtx (l :: xs) = {Res.var (.loc l)} + locsCtx xs := by
  simp [locsCtx, Multiset.singleton_add]

@[simp] theorem locsCtx_append (xs ys : List Nat) :
    locsCtx (xs ++ ys) = locsCtx xs + locsCtx ys := by
  simp [locsCtx]

theorem nzCtx_locsCtx (xs : List Nat) : nzCtx (locsCtx xs) = locsCtx xs := by
  unfold nzCtx locsCtx
  rw [Multiset.filter_eq_self]
  intro a ha; simp at ha; obtain ⟨_, _, rfl⟩ := ha; simp

theorem Ctx.ren_bCtx {m : Nat} (k : Nat) (xs : List Nat) (ρ : Fin m → Nat)
    (hl : xs.length = k) : Ctx.ren (instN k xs ρ) (bCtx m k) = locsCtx xs := by
  subst hl
  simp only [bCtx, Ctx.ren, Multiset.map_coe, List.map_map, locsCtx]
  congr 1
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.length_map] at h2
  simp [Res.ren, Var.ren_newB, List.getElem?_eq_getElem h2]

theorem Ctx.ren_allCtx (k : Nat) (xs : List Nat) (hl : xs.length = k) :
    Ctx.ren (ofListN k xs) (allCtx k) = locsCtx xs := by
  subst hl
  simp only [allCtx, Ctx.ren, Multiset.map_coe, List.map_map, locsCtx]
  congr 1
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.length_map] at h2
  simp [Res.ren, Var.ren, ofListN, List.getElem?_eq_getElem h2]

/-! ## Composition of substitutions -/

theorem LVal.shift_subst_up {n m : Nat} (k : Nat) (τ : Fin m → LVal n) (v : LVal m) :
    (v.shift k).subst (fun i => LSubst.up k τ i) = (v.subst τ).shift k := by
  unfold LVal.shift
  rw [LVal.subst_subst, LVal.subst_subst]
  apply LVal.subst_congr
  intro i
  simp only [LVal.subst_bvar, LSubst.up, show ¬ (k + i.val < k) by omega, dite_false]
  congr 2; ext; simp

theorem LSubst.up_comp {n m p : Nat} (k : Nat) (τ : Fin n → LVal m) (σ : Fin m → LVal p)
    (i : Fin (n + k)) :
    (LSubst.up k τ i).subst (LSubst.up k σ) = LSubst.up k (fun j => (τ j).subst σ) i := by
  simp only [LSubst.up]
  split
  · rename_i h; simp [LSubst.up, h]
  · exact LVal.shift_subst_up k σ _

mutual
theorem LExpr.subst_subst {n m p : Nat} (τ : Fin n → LVal m) (σ : Fin m → LVal p) :
    ∀ e : LExpr n, (e.subst τ).subst σ = e.subst (fun i => (τ i).subst σ)
  | .ret vs => by simp only [LExpr.subst]; rw [LVals.subst_subst]
  | .app e1 e2 => by
    simp only [LExpr.subst]; rw [LExpr.subst_subst τ σ e1, LExpr.subst_subst τ σ e2]
  | .call f e1 e2 => by
    simp only [LExpr.subst]; rw [LExpr.subst_subst τ σ e1, LExpr.subst_subst τ σ e2]
  | .letIn k e1 e2 => by
    simp only [LExpr.subst]
    rw [LExpr.subst_subst τ σ e1, LExpr.subst_subst _ _ e2,
      LExpr.subst_congr (LSubst.up_comp k τ σ)]
  | .match x bs => by
    simp only [LExpr.subst]; rw [LVal.subst_subst, LBranches.subst_subst τ σ bs]
  | .dup x e => by simp only [LExpr.subst]; rw [LVal.subst_subst, LExpr.subst_subst τ σ e]
  | .drop x e => by simp only [LExpr.subst]; rw [LVal.subst_subst, LExpr.subst_subst τ σ e]
  | .dropru x k e => by
    simp only [LExpr.subst]; rw [LVal.subst_subst, LExpr.subst_subst τ σ e]
  | .free k e => by simp only [LExpr.subst]; rw [LExpr.subst_subst τ σ e]
  | .alloc k e => by simp only [LExpr.subst]; rw [LExpr.subst_subst τ σ e]
theorem LBranches.subst_subst {n m p : Nat} (τ : Fin n → LVal m) (σ : Fin m → LVal p) :
    ∀ bs : LBranches n, (bs.subst τ).subst σ = bs.subst (fun i => (τ i).subst σ)
  | .nil => rfl
  | .cons c k e bs => by
    simp only [LBranches.subst]
    rw [LExpr.subst_subst _ _ e, LExpr.subst_congr (LSubst.up_comp k τ σ),
      LBranches.subst_subst τ σ bs]
end

/-- Substituting under `k` binders and then instantiating them with the locations `xs` is
    substituting `instN k xs ρ`. -/
theorem LExpr.subst_up_inst0 {m k : Nat} (ρ : Fin m → Nat) (xs : List Nat) (hl : xs.length = k)
    (e : LExpr (m + k)) :
    (e.subst (LSubst.up k (LSubst.locs ρ))).subst (LSubst.inst k (xs.map locV) Fin.elim0) =
      e.subst (LSubst.locs (instN k xs ρ)) := by
  rw [LExpr.subst_subst]
  apply LExpr.subst_congr
  intro i
  simp only [LSubst.up, LSubst.locs, instN]
  split
  · rename_i h
    simp only [LVal.subst_bvar, LSubst.inst, h, dite_true]
    by_cases hl : i.val < xs.length
    · rw [List.getD_eq_getElem _ _ (by simpa using hl), List.getD_eq_getElem _ _ hl]; simp
    · exact absurd hl (by omega)
  · rfl

/-- `inst0` of a closed binder with locations. -/
theorem LExpr.inst0_locs {k : Nat} (e : LExpr (0 + k)) (xs : List Nat) (hl : xs.length = k) :
    e.inst0 (xs.map locV) = e.subst (LSubst.locs (instN k xs Fin.elim0)) := by
  unfold LExpr.inst0
  apply LExpr.subst_congr
  intro i
  simp only [LSubst.inst, LSubst.locs, instN]
  split
  · rename_i h
    by_cases hl : i.val < xs.length
    · rw [List.getD_eq_getElem _ _ (by simpa using hl), List.getD_eq_getElem _ _ hl]; simp
    · exact absurd hl (by omega)
  · rename_i h; exact absurd i.isLt (by omega)

end FIP.Lam

/- ══════════════════ PAPER sec. 5.3, App. E END: Soundness of the Heap Semantics: the admissible fragment ══════════════════ -/
