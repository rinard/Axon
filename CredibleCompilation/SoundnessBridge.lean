-- Copyright (c) 2026 Martin Rinard
import CredibleCompilation.ExecChecker
import Mathlib.Tactic

/-!
# Soundness Bridge: Executable Checker → Prop-based Checker

We prove that if the executable `checkCertificateExec` returns `true`,
then `PCertificateValid` holds for the corresponding `PCertificate`.

## Structure

1. **Translation**: `toPCertificate` lifts a `ECertificate` to a `PCertificate`
2. **Per-condition soundness**: each Bool check implies its Prop counterpart
3. **Main theorem**: `soundness_bridge`

## On the converse (completeness)

An iff is **not possible** in general:
- The Prop-based `PCertificate` uses `PInvariantMap := Label → Store → Prop`
  (arbitrary predicates on stores)
- The executable `ECertificate` uses `EInv := List (Var × Expr)`
  (only `var = expr` atoms, where `expr` is built from literals, variables, and binops)

Any `PCertificateValid` proof using invariants beyond `var = expr`
(e.g., inequalities like `x < y`) cannot be captured by `checkCertificateExec`.
The executable checker is **sound but incomplete**.
-/

set_option maxRecDepth 2048

/-- Helper: BEq on TAC derived instance implies equality.
    TAC derives both BEq and DecidableEq; they agree but are separate instances. -/
private theorem tac_beq_eq {a b : TAC} (h : (a == b) = true) : a = b := by
  exact of_decide_eq_true h

/-- Helper: extract orig[pc]? = some instr from the BEq check in checkOrigPath. -/
private theorem orig_eq_of_beq {orig : Prog} {pc : Label} {instr : TAC}
    (h : (orig[pc]? == some instr) = true) : orig[pc]? = some instr := by
  match horig : orig[pc]? with
  | none =>
    rw [horig] at h; exact nomatch h
  | some i =>
    rw [horig] at h
    exact congrArg some (tac_beq_eq h)

-- ============================================================
-- § 1. Lifting EInv to Prop
-- ============================================================

/-- A `EInv` as a proposition: every atom `(x, e)` asserts `σ x = e.eval σ am`. -/
def EInv.toProp (inv : EInv) : PInvariant :=
  fun σ am => ∀ p ∈ inv, σ p.1 = p.2.eval σ am

theorem EInv.toProp_nil : EInv.toProp [] = fun _ _ => True := by
  funext σ am; simp [EInv.toProp]

theorem EInv.toProp_cons (x : Var) (e : Expr) (rest : EInv) :
    EInv.toProp ((x, e) :: rest) = fun σ am => σ x = e.eval σ am ∧ EInv.toProp rest σ am := by
  funext σ am; simp [EInv.toProp]

/-- If all invariant atoms are arrRead-free, the invariant holds at any array memory. -/
theorem EInv.toProp_am_indep (inv : EInv) (σ : Store) (am₁ am₂ : ArrayMem)
    (hnoarr : inv.all (fun (_, e) => !e.hasArrRead) = true)
    (hinv : EInv.toProp inv σ am₁) :
    EInv.toProp inv σ am₂ := by
  intro p hp
  have := hinv p hp
  rw [List.all_eq_true] at hnoarr
  have hna := hnoarr p hp
  simp at hna
  rw [this, Expr.eval_noArrRead p.2 σ am₁ am₂ hna]

/-- SamCoherent relates the symbolic array memory to the runtime array memory
    via a chain of writes.  Most-recent write is at the head.
    Type-agnostic: uses `.toBits` so it works for int, bool, and float values. -/
inductive SamCoherent : SymArrayMem → Store → ArrayMem → ArrayMem → Prop where
  | nil {σ₀ : Store} {am : ArrayMem} : SamCoherent [] σ₀ am am
  | cons {rest : SymArrayMem} {σ₀ : Store} {am₀ am_prev am : ArrayMem}
         (arr : ArrayName) (idx_e val_e : Expr) (bv : BitVec 64)
         (hprev : SamCoherent rest σ₀ am₀ am_prev)
         (hval : (val_e.eval σ₀ am₀).toBits = bv)
         (hwrite : am = am_prev.write arr (idx_e.eval σ₀ am₀).toInt bv) :
    SamCoherent ((arr, idx_e, val_e) :: rest) σ₀ am₀ am

theorem samCoherent_nil (σ₀ : Store) (am : ArrayMem) :
    SamCoherent [] σ₀ am am := .nil

private theorem samGet_cons (arr_h : ArrayName) (idx_h val_h : Expr) (rest : SymArrayMem)
    (arr : ArrayName) (idx : Expr) (ty : VarTy) :
    samGet ((arr_h, idx_h, val_h) :: rest) arr idx ty =
    if arr_h == arr && idx_h == idx then val_h else samGet rest arr idx ty := by
  simp only [samGet, List.find?]
  cases arr_h == arr && idx_h == idx <;> simp

/-- samGet_sound: under a no-alias condition, `samGet` at am₀ equals
    `Value.ofBitVec ty` of the runtime array read.
    The `htype` hypothesis ensures matching SAM entries have the correct type. -/
theorem samGet_sound (sam : SymArrayMem) (σ₀ : Store) (am₀ am : ArrayMem)
    (hcoh : SamCoherent sam σ₀ am₀ am)
    (arr : ArrayName) (idx_expr : Expr) (ty : VarTy)
    (hnoalias : ∀ a i v, (a, i, v) ∈ sam → a = arr → ¬(i == idx_expr) →
      (i.eval σ₀ am₀).toInt ≠ (idx_expr.eval σ₀ am₀).toInt)
    (htype : ∀ a i v, (a, i, v) ∈ sam → a = arr → (i == idx_expr) = true →
      (v.eval σ₀ am₀).typeOf = ty) :
    (samGet sam arr idx_expr ty).eval σ₀ am₀ =
    Value.ofBitVec ty (am.read arr (idx_expr.eval σ₀ am₀).toInt) := by
  induction sam generalizing am with
  | nil => cases hcoh; cases ty <;> simp [samGet, List.find?, Expr.eval, Value.ofBitVec, CmpOp.eval]
  | cons entry rest ih =>
    obtain ⟨arr_h, idx_h, val_h⟩ := entry
    match hcoh with
    | .cons _ _ _ bv hprev hval hwrite =>
    rw [samGet_cons]
    by_cases hmatch : (arr_h == arr && idx_h == idx_expr) = true
    · -- Match case: head entry matches — use htype + roundtrip
      simp [hmatch]
      simp [Bool.and_eq_true] at hmatch
      have harr : arr_h = arr := hmatch.1
      have hidx : idx_h = idx_expr := hmatch.2
      have hvalTy := htype arr_h idx_h val_h (List.Mem.head _) harr (by rw [hidx]; simp)
      rw [hwrite, harr, hidx, ArrayMem.read_write_same]
      exact Value.ofBitVec_toBits hvalTy ▸ congrArg (Value.ofBitVec ty) hval
    · -- Non-match case: recurse into rest
      simp [hmatch]
      have ih_noalias : ∀ a i v, (a, i, v) ∈ rest → a = arr → ¬(i == idx_expr) →
          (i.eval σ₀ am₀).toInt ≠ (idx_expr.eval σ₀ am₀).toInt :=
        fun a i v hmem ha hi => hnoalias a i v (List.Mem.tail _ hmem) ha hi
      have ih_type : ∀ a i v, (a, i, v) ∈ rest → a = arr → (i == idx_expr) = true →
          (v.eval σ₀ am₀).typeOf = ty :=
        fun a i v hmem ha hi => htype a i v (List.Mem.tail _ hmem) ha hi
      rw [ih _ hprev ih_noalias ih_type, hwrite]
      congr 1
      by_cases harr : arr_h = arr
      · have hidx_ne : ¬(idx_h == idx_expr) := by
          intro h; exact hmatch (by simp [beq_iff_eq.mpr harr, h])
        have hsem_ne := hnoalias arr_h idx_h val_h (List.Mem.head _) harr hidx_ne
        subst harr
        exact (ArrayMem.read_write_ne_idx _ _ _ _ _ hsem_ne.symm).symm
      · exact (ArrayMem.read_write_ne_arr _ _ _ _ _ _ (fun h => harr h.symm)).symm

-- ============================================================
-- § 2. Translation: ECertificate → PCertificate
-- ============================================================

/-- Convert an executable expression relation to a Prop-level store relation.
    For every pair `(e_o, .var v) ∈ rel`, `σ_t v = e_o.eval σ_o am_o`.
    Only claims the relation for variables explicitly mapped in `rel`. -/
def eRelToStoreRel (rel : EExprRel) : PStoreRel :=
  fun σ_o am_o σ_t _am_t =>
    ∀ e_o v, (e_o, .var v) ∈ rel → σ_t v = e_o.eval σ_o am_o

/-- Lift an executable certificate to a Prop-based certificate. -/
def toPCertificate (dc : ECertificate) : PCertificate :=
  { orig       := dc.orig
    trans      := dc.trans
    tyCtx      := dc.tyCtx
    inv_orig   := fun l => (dc.inv_orig.getD l ([] : EInv)).toProp
    inv_trans  := fun l => (dc.inv_trans.getD l ([] : EInv)).toProp
    instrCerts := fun l =>
      let dic := dc.instrCerts.getD l default
      { pc_orig    := dic.pc_orig
        storeRel   := eRelToStoreRel dic.rel
        transitions := dic.transitions.map fun dtc =>
          { origLabels   := dtc.origLabels
            storeRel     := eRelToStoreRel dtc.rel
            storeRel_next := eRelToStoreRel dtc.rel_next }
      }
    haltCerts := fun l =>
      let dhc := dc.haltCerts.getD l default
      { pc_orig := dhc.pc_orig
        storeRel := eRelToStoreRel dhc.rel }
    measure := fun l _ => dc.measure.getD l 0
  }

@[simp] theorem toCertificate_orig (dc : ECertificate) :
    (toPCertificate dc).orig = dc.orig := rfl

@[simp] theorem toCertificate_trans (dc : ECertificate) :
    (toPCertificate dc).trans = dc.trans := rfl

@[simp] theorem toCertificate_tyCtx (dc : ECertificate) :
    (toPCertificate dc).tyCtx = dc.tyCtx := rfl

@[simp] theorem toCertificate_observable (dc : ECertificate) :
    (toPCertificate dc).observable = dc.observable := by
  simp [PCertificate.observable, ECertificate.observable, toPCertificate]

-- ============================================================
-- § 3. lookupExpr soundness
-- ============================================================

theorem lookupExpr_sound (inv : EInv) (v : Var) (e : Expr) (σ : Store) (am : ArrayMem)
    (hlook : lookupExpr inv v = some e)
    (hinv : EInv.toProp inv σ am) :
    σ v = e.eval σ am := by
  induction inv with
  | nil => simp [lookupExpr] at hlook
  | cons p rest ih =>
    obtain ⟨x, expr⟩ := p
    rw [EInv.toProp_cons] at hinv
    simp only [lookupExpr, List.find?, Option.map] at hlook
    by_cases hxv : x == v
    · simp [hxv] at hlook
      rw [← hlook, ← beq_iff_eq.mp hxv]
      exact hinv.1
    · simp [hxv] at hlook
      exact ih hlook hinv.2


-- ============================================================
-- § 4. Expr.simplify soundness
-- ============================================================

/-- Reassociation preserves semantics. -/
private theorem Expr.reassoc_sound (op : BinOp) (a b : Expr) (σ : Store) (am : ArrayMem) :
    (Expr.reassoc op a b).eval σ am = (Expr.bin op a b).eval σ am := by
  unfold Expr.reassoc
  split
  · -- (na - x) + nb → (na + nb) - x
    rename_i na x nb
    simp only [Expr.eval, BinOp.eval, Value.toInt]; congr 1; bv_omega
  · -- (na - x) - nb → (na - nb) - x
    rename_i na x nb
    simp only [Expr.eval, BinOp.eval, Value.toInt]; congr 1; bv_omega
  · rename_i na x nb
    simp only [Expr.eval, BinOp.eval, Value.toInt]; congr 1; bv_omega
  · rename_i na nb x
    simp only [Expr.eval, BinOp.eval, Value.toInt]; congr 1; bv_omega
  · -- na - (x - nb) → (na + nb) - x
    rename_i na x nb
    simp only [Expr.eval, BinOp.eval, Value.toInt]; congr 1; bv_omega
  · rfl

/-- Simplification preserves semantics: evaluating `e.simplify inv` in `σ`
    gives the same result as evaluating `e` in `σ`, provided `σ` satisfies `inv`. -/
theorem Expr.simplify_sound (inv : EInv) (e : Expr) (σ : Store) (am : ArrayMem)
    (hinv : EInv.toProp inv σ am) :
    (e.simplify inv).eval σ am = e.eval σ am := by
  induction e with
  | lit n => simp [Expr.simplify, Expr.eval]
  | blit b => simp [Expr.simplify, Expr.eval]
  | var v =>
    simp only [Expr.simplify]
    split
    · case h_1 e hlook =>
      simp only [Expr.eval]
      have h := lookupExpr_sound inv v e σ am hlook hinv
      exact h.symm
    · case h_2 =>
      simp [Expr.eval]
  | bin op a b iha ihb =>
    simp only [Expr.simplify, Expr.eval]
    split
    · case h_1 na nb heqa heqb =>
      simp only [Expr.eval]
      rw [heqa] at iha; rw [heqb] at ihb
      simp only [Expr.eval] at iha ihb
      congr 1
      rw [show (a.eval σ am).toInt = na from by rw [← iha]; rfl,
          show (b.eval σ am).toInt = nb from by rw [← ihb]; rfl]
    · case h_2 =>
      rw [Expr.reassoc_sound]
      simp only [Expr.eval]
      rw [iha, ihb]
  | tobool e ih => simp only [Expr.simplify, Expr.eval]; rw [ih]
  | cmpE op a b iha ihb => simp only [Expr.simplify, Expr.eval]; rw [iha, ihb]
  | cmpLitE op a n ih => simp only [Expr.simplify, Expr.eval]; rw [ih]
  | notE e ih => simp only [Expr.simplify, Expr.eval]; rw [ih]
  | andE a b iha ihb => simp only [Expr.simplify, Expr.eval]; rw [iha, ihb]
  | orE a b iha ihb => simp only [Expr.simplify, Expr.eval]; rw [iha, ihb]
  | arrRead arr idx ih =>
    simp only [Expr.simplify, Expr.eval]
    rw [ih]
  | flit _ => rfl
  | fbin op _ _ iha ihb =>
    simp only [Expr.simplify]
    split
    · -- fadd, both operands fmul → kept in original order (no swap)
      simp only [Expr.eval]
      rw [iha, ihb]
    · -- fadd with a lone fmul on left → swapped by normalization
      simp only [Expr.eval]
      rw [iha, ihb, FloatBinOp.fadd_comm]
    · -- all other cases → unchanged
      simp only [Expr.eval]
      rw [iha, ihb]
  | fcmpE _ _ _ iha ihb =>
    simp only [Expr.simplify, Expr.eval]
    rw [iha, ihb]
  | intToFloat _ ih =>
    simp only [Expr.simplify, Expr.eval]
    rw [ih]
  | floatToInt _ ih =>
    simp only [Expr.simplify, Expr.eval]
    rw [ih]
  | floatUnary _ _ ih =>
    simp only [Expr.simplify, Expr.eval]
    rw [ih]
  | ftern op _ _ _ iha ihb ihc =>
    cases op <;> simp only [Expr.simplify, Expr.eval, FloatTernOp.eval, Value.toFloat_float] <;>
      rw [iha, ihb, ihc]
  | farrRead arr idx ih =>
    simp only [Expr.simplify, Expr.eval]
    rw [ih]

/-- Deep simplification preserves semantics: iterating `simplify` is sound
    because each application preserves eval. -/
theorem Expr.simplifyDeep_sound (n : Nat) (inv : EInv) (e : Expr) (σ : Store) (am : ArrayMem)
    (hinv : EInv.toProp inv σ am) :
    (e.simplifyDeep n inv).eval σ am = e.eval σ am := by
  induction n generalizing e with
  | zero =>
    show (e.simplify inv).eval σ am = e.eval σ am
    exact Expr.simplify_sound inv e σ am hinv
  | succ n ih =>
    show ((e.simplify inv).simplifyDeep n inv).eval σ am = e.eval σ am
    rw [ih]
    exact Expr.simplify_sound inv e σ am hinv

-- ============================================================
-- § 5. Easy soundness lemmas
-- ============================================================

/-- **Condition 1**: checkStartCorrespondenceExec → checkStartCorrespondenceProp -/
theorem checkStartCorrespondenceExec_sound (dc : ECertificate)
    (h : checkStartCorrespondenceExec dc = true)
    (hrel0 : (dc.instrCerts.getD 0 default).rel.all (fun (e_o, e_t) => e_o == e_t) = true) :
    checkStartCorrespondenceProp (toPCertificate dc) := by
  simp [checkStartCorrespondenceExec] at h
  split at h
  · rename_i ic hic
    have hbound := bound_of_getElem? hic
    have hget : dc.instrCerts[0] = ic := (Array.getElem?_eq_some_iff.mp hic).2
    have hpc : ic.pc_orig = 0 := beq_iff_eq.mp h
    constructor
    · -- (instrCerts 0).pc_orig = 0
      simp only [toPCertificate, Array.getD, dif_pos hbound]
      rw [show dc.instrCerts.getInternal 0 hbound = ic from hget]
      exact hpc
    · -- ∀ σ am, storeRel σ am σ am
      have hrel_all : ic.rel.all (fun (e_o, e_t) => e_o == e_t) = true := by
        have : (dc.instrCerts.getD 0 default).rel = ic.rel := by
          simp [Array.getD, dif_pos hbound, hget]
        rw [this] at hrel0; exact hrel0
      intro σ am
      simp only [toPCertificate, Array.getD, dif_pos hbound]
      rw [show dc.instrCerts.getInternal 0 hbound = ic from hget]
      show eRelToStoreRel ic.rel σ am σ am
      -- All pairs are identity: (e_o, e_t) with e_o = e_t
      intro e_o v hmem
      rw [List.all_eq_true] at hrel_all
      have hid := hrel_all (e_o, .var v) hmem
      simp at hid; rw [hid]; simp [Expr.eval]
  · contradiction

/-- **Condition 2a**: checkInvariantsAtStartExec → checkInvariantsAtStartProp -/
theorem checkInvariantsAtStartExec_sound (dc : ECertificate)
    (h : checkInvariantsAtStartExec dc = true) :
    checkInvariantsAtStartProp (toPCertificate dc) := by
  unfold checkInvariantsAtStartExec at h
  have h1 : (dc.inv_orig.getD 0 ([] : EInv)).isEmpty = true := by
    revert h; cases (dc.inv_orig.getD 0 ([] : EInv)).isEmpty <;> simp
  have h2 : (dc.inv_trans.getD 0 ([] : EInv)).isEmpty = true := by
    revert h; cases (dc.inv_trans.getD 0 ([] : EInv)).isEmpty <;> simp
  have horig_nil : dc.inv_orig.getD 0 ([] : EInv) = [] := by
    revert h1; cases dc.inv_orig.getD 0 ([] : EInv) <;> simp [List.isEmpty]
  have htrans_nil : dc.inv_trans.getD 0 ([] : EInv) = [] := by
    revert h2; cases dc.inv_trans.getD 0 ([] : EInv) <;> simp [List.isEmpty]
  refine ⟨fun σ am => ?_, fun σ am => ?_⟩
  · change (dc.inv_trans.getD 0 ([] : EInv)).toProp σ am
    rw [htrans_nil]; simp [EInv.toProp]
  · change (dc.inv_orig.getD 0 ([] : EInv)).toProp σ am
    rw [horig_nil]; simp [EInv.toProp]

/-- **Condition 4a**: checkHaltCorrespondenceExec → checkHaltCorrespondenceProp -/
theorem checkHaltCorrespondenceExec_sound (dc : ECertificate)
    (h : checkHaltCorrespondenceExec dc = true) :
    checkHaltCorrespondenceProp (toPCertificate dc) := by
  intro pc_t
  dsimp only [toPCertificate]
  intro hhalt
  have hbound : pc_t < dc.trans.size := bound_of_getElem? hhalt
  unfold checkHaltCorrespondenceExec at h
  rw [List.all_eq_true] at h
  have hpc := h pc_t (List.mem_range.mpr hbound)
  simp only [hhalt] at hpc
  revert hpc
  generalize dc.orig[(dc.instrCerts.getD pc_t default).pc_orig]? = opt
  cases opt with
  | none => simp
  | some instr => cases instr <;> simp

/-- If `(.var v, .var v) ∈ rel` and the membership-based relation holds,
    then `σ_t v = σ_o v`. -/
private theorem eRelToStoreRel_identity_pair {rel : EExprRel} {σ_o σ_t : Store} {am_o am_t : ArrayMem}
    (hcons : eRelToStoreRel rel σ_o am_o σ_t am_t)
    (v : Var) (hmem : (.var v, .var v) ∈ rel) :
    σ_t v = σ_o v := by
  have := hcons (.var v) v hmem
  simp [Expr.eval] at this
  exact this

/-- **Condition 4b**: checkHaltObservableExec → checkHaltObservableProp -/
theorem checkHaltObservableExec_sound (dc : ECertificate)
    (h : checkHaltObservableExec dc = true) :
    checkHaltObservableProp (toPCertificate dc) := by
  intro pc_t σ_t σ_o am_t am_o hhalt
  dsimp only [toPCertificate]
  intro hcons v hv
  -- From checker: ic.rel has an identity pair (.var v, .var v) for observable v at halt
  have hhalt' : dc.trans[pc_t]? = some .halt := hhalt
  unfold checkHaltObservableExec at h; rw [List.all_eq_true] at h
  have hpc := h pc_t (List.mem_range.mpr (bound_of_getElem? hhalt'))
  rw [hhalt'] at hpc; rw [List.all_eq_true] at hpc
  have hany := hpc v hv
  -- hany : ic.rel.any (fun (e_o, e_t) => e_t == .var v && e_o == .var v) = true
  rw [List.any_eq_true] at hany
  obtain ⟨⟨e_o, e_t⟩, hmem, hcheck⟩ := hany
  rw [Bool.and_eq_true] at hcheck
  have het := beq_iff_eq.mp hcheck.1
  have heo := beq_iff_eq.mp hcheck.2
  subst het; subst heo
  exact eRelToStoreRel_identity_pair hcons v hmem

-- ============================================================
-- § 6. Symbolic execution infrastructure
-- ============================================================

/-- find? on filtered list equals find? on original when predicates are compatible. -/
private theorem find_filter_ne (ss : SymStore) (x y : Var) (hne : y ≠ x) :
    (ss.filter (fun p => !(p.1 == x))).find? (fun p => p.1 == y) =
    ss.find? (fun p => p.1 == y) := by
  induction ss with
  | nil => rfl
  | cons p rest ih =>
    by_cases hpx : p.1 == x <;> by_cases hpy : p.1 == y
    · exfalso; exact hne (beq_iff_eq.mp hpy ▸ beq_iff_eq.mp hpx)
    · simp [List.filter, List.find?, hpx, hpy, ih]
    · simp [List.filter, List.find?, hpx, hpy]
    · simp [List.filter, List.find?, hpx, hpy, ih]

theorem ssGet_ssSet_same (ss : SymStore) (x : Var) (e : Expr) :
    ssGet (ssSet ss x e) x = e := by
  simp [ssGet, ssSet]

theorem ssGet_ssSet_other (ss : SymStore) (x y : Var) (e : Expr) (hne : y ≠ x) :
    ssGet (ssSet ss x e) y = ssGet ss y := by
  unfold ssGet ssSet
  have hxy : (x == y) = false := beq_eq_false_iff_ne.mpr (Ne.symm hne)
  have step1 : ((x, e) :: ss.filter (fun p => !(p.1 == x))).find? (fun p => p.1 == y) =
      (ss.filter (fun p => !(p.1 == x))).find? (fun p => p.1 == y) := by
    simp [List.find?, hxy]
  rw [step1, find_filter_ne ss x y hne]

-- ============================================================
-- § 6b. Expr.substSym soundness
-- ============================================================

/-- Substituting variables in `e` with their symbolic post-values and evaluating
    at the initial store `σ₀` equals evaluating `e` at the post-store `σ'`. -/
theorem Expr.substSym_sound (ss : SymStore) (e : Expr) (σ₀ σ' : Store)
    (am : ArrayMem)
    (hrepr : ∀ v, (ssGet ss v).eval σ₀ am = σ' v) :
    (e.substSym ss).eval σ₀ am = e.eval σ' am := by
  induction e with
  | lit n => simp [Expr.substSym, Expr.eval]
  | blit b => simp [Expr.substSym, Expr.eval]
  | var v => simp [Expr.substSym, Expr.eval]; exact hrepr v
  | bin op a b iha ihb =>
    simp only [Expr.substSym, Expr.eval]; rw [iha, ihb]
  | tobool e ih =>
    simp only [Expr.substSym, Expr.eval]; rw [ih]
  | cmpE op a b iha ihb =>
    simp only [Expr.substSym, Expr.eval]; rw [iha, ihb]
  | cmpLitE op a n ih =>
    simp only [Expr.substSym, Expr.eval]; rw [ih]
  | notE e ih =>
    simp only [Expr.substSym, Expr.eval]; rw [ih]
  | andE a b iha ihb =>
    simp only [Expr.substSym, Expr.eval]; rw [iha, ihb]
  | orE a b iha ihb =>
    simp only [Expr.substSym, Expr.eval]; rw [iha, ihb]
  | arrRead arr idx ih =>
    simp only [Expr.substSym, Expr.eval]; rw [ih]
  | flit _ => simp [Expr.substSym, Expr.eval]
  | fbin op a b iha ihb =>
    simp only [Expr.substSym, Expr.eval]; rw [iha, ihb]
  | fcmpE op a b iha ihb =>
    simp only [Expr.substSym, Expr.eval]; rw [iha, ihb]
  | intToFloat e ih =>
    simp only [Expr.substSym, Expr.eval]; rw [ih]
  | floatToInt e ih =>
    simp only [Expr.substSym, Expr.eval]; rw [ih]
  | floatUnary op e ih =>
    simp only [Expr.substSym, Expr.eval]; rw [ih]
  | ftern op a b c iha ihb ihc =>
    simp only [Expr.substSym, Expr.eval]; rw [iha, ihb, ihc]
  | farrRead arr idx ih =>
    simp only [Expr.substSym, Expr.eval]; rw [ih]

private theorem BoolExpr.toSymExpr_sound (be : BoolExpr) (ss : SymStore) (σ₀ σ : Store)
    (am : ArrayMem)
    (hrepr : ∀ v, (ssGet ss v).eval σ₀ am = σ v) :
    (be.toSymExpr ss).eval σ₀ am = .bool (be.eval σ am) := by
  induction be with
  | lit b => simp [BoolExpr.toSymExpr, BoolExpr.eval, Expr.eval]
  | bvar x => simp [BoolExpr.toSymExpr, BoolExpr.eval, Expr.eval, hrepr]
  | cmp op a b =>
    simp only [BoolExpr.toSymExpr, BoolExpr.eval, Expr.eval,
               Expr.substSym'_eq_substSym,
               Expr.substSym_sound ss a σ₀ σ am hrepr,
               Expr.substSym_sound ss b σ₀ σ am hrepr]
  | not e ih =>
    simp only [BoolExpr.toSymExpr, BoolExpr.eval, Expr.eval]
    have h := ih; rw [h]; simp [Value.toBool]
  | bexpr e => simp [BoolExpr.toSymExpr, BoolExpr.eval, Expr.eval, Expr.substSym'_eq_substSym,
                     Expr.substSym_sound ss e σ₀ σ am hrepr]
  | fcmp op a b =>
    simp only [BoolExpr.toSymExpr, BoolExpr.eval, Expr.eval,
               Expr.substSym'_eq_substSym,
               Expr.substSym_sound ss a σ₀ σ am hrepr,
               Expr.substSym_sound ss b σ₀ σ am hrepr]

/-- Symbolic execution soundness: if the symbolic store `ss` correctly represents
    the relationship between an initial store `σ₀` and a current store `σ`,
    then after executing `instr`, the updated symbolic store correctly represents
    the relationship with the post-store `σ'`. -/
theorem execSymbolic_sound (ss : SymStore) (sam : SymArrayMem) (instr : TAC)
    (σ₀ σ σ' : Store) (pc pc' : Label) (prog : Prog) (am : ArrayMem)
    (hrepr : ∀ v, (ssGet ss v).eval σ₀ am = σ v)
    (hstep : Step prog (Cfg.run pc σ am) (Cfg.run pc' σ' _sbam'))
    (hinstr : prog[pc]? = some instr)
    (hscalar : instr.isScalar = true) :
    ∀ v, (ssGet (execSymbolic ss sam instr).1 v).eval σ₀ am = σ' v := by
  have step_det : ∀ c, Step prog (Cfg.run pc σ am) c → c = Cfg.run pc' σ' _sbam' :=
    fun c hc => Step.deterministic hc hstep
  intro v
  cases instr with
  | const dest val =>
    -- execSymbolic splits on val's constructor, so we case-split on val
    cases val with
    | int n =>
      simp only [execSymbolic]
      have := step_det _ (Step.const hinstr)
      have hσ' : σ' = σ[dest ↦ .int n] := (Cfg.run.inj this).2.1.symm
      rw [hσ']
      by_cases hvd : v = dest
      · rw [hvd, ssGet_ssSet_same]; simp [Expr.eval, Store.update_self]
      · rw [ssGet_ssSet_other _ _ _ _ hvd, hrepr]
        exact (Store.update_other σ dest v _ hvd).symm
    | bool b =>
      simp only [execSymbolic]
      have := step_det _ (Step.const hinstr)
      have hσ' : σ' = σ[dest ↦ .bool b] := (Cfg.run.inj this).2.1.symm
      rw [hσ']
      by_cases hvd : v = dest
      · rw [hvd, ssGet_ssSet_same]; simp [Expr.eval, Store.update_self]
      · rw [ssGet_ssSet_other _ _ _ _ hvd, hrepr]
        exact (Store.update_other σ dest v _ hvd).symm
    | float f =>
      simp only [execSymbolic]
      have := step_det _ (Step.const hinstr)
      have hσ' : σ' = σ[dest ↦ .float f] := (Cfg.run.inj this).2.1.symm
      rw [hσ']
      by_cases hvd : v = dest
      · rw [hvd, ssGet_ssSet_same]; simp [Expr.eval, Store.update_self]
      · rw [ssGet_ssSet_other _ _ _ _ hvd, hrepr]
        exact (Store.update_other σ dest v _ hvd).symm
  | copy dest src =>
    simp only [execSymbolic]
    have := step_det _ (Step.copy hinstr)
    have hσ' : σ' = σ[dest ↦ σ src] := (Cfg.run.inj this).2.1.symm
    rw [hσ']
    by_cases hvd : v = dest
    · rw [hvd, ssGet_ssSet_same, hrepr]; exact (Store.update_self σ dest (σ src)).symm
    · rw [ssGet_ssSet_other _ _ _ _ hvd, hrepr]
      exact (Store.update_other σ dest v _ hvd).symm
  | binop dest op a b =>
    simp only [execSymbolic]
    -- Extract int witnesses from hstep (Step.binop requires σ a = .int _ and σ b = .int _)
    obtain ⟨ia, ib, hia, hib, hsafe⟩ : ∃ ia ib : BitVec 64, σ a = .int ia ∧ σ b = .int ib ∧ op.safe ia ib := by
      generalize _sbam' = am' at hstep; cases hstep <;> simp_all
    have hstep' : Step prog (Cfg.run pc σ am) (Cfg.run (pc + 1) (σ[dest ↦ .int (op.eval ia ib)]) am) :=
      Step.binop hinstr hia hib hsafe
    have := step_det _ hstep'
    have hσ' : σ' = σ[dest ↦ .int (op.eval ia ib)] := (Cfg.run.inj this).2.1.symm
    rw [hσ']
    by_cases hvd : v = dest
    · rw [hvd, ssGet_ssSet_same]
      simp only [Expr.eval, Store.update_self]
      have ha : ((ssGet ss a).eval σ₀ am).toInt = ia := by
        rw [hrepr a, hia]; rfl
      have hb : ((ssGet ss b).eval σ₀ am).toInt = ib := by
        rw [hrepr b, hib]; rfl
      rw [ha, hb]
    · rw [ssGet_ssSet_other _ _ _ _ hvd, hrepr]
      exact (Store.update_other σ dest v _ hvd).symm
  | boolop dest be =>
    simp only [execSymbolic]
    have := step_det _ (Step.boolop hinstr)
    have hσ' : σ' = σ[dest ↦ .bool (be.eval σ am)] := (Cfg.run.inj this).2.1.symm
    rw [hσ']
    by_cases hvd : v = dest
    · rw [hvd, ssGet_ssSet_same]
      simp only [Store.update_self]
      exact BoolExpr.toSymExpr_sound be ss σ₀ σ am hrepr
    · rw [ssGet_ssSet_other _ _ _ _ hvd, hrepr]
      exact (Store.update_other σ dest v _ hvd).symm
  | goto l =>
    simp only [execSymbolic]
    have := step_det _ (Step.goto hinstr)
    have hσ' : σ' = σ := (Cfg.run.inj this).2.1.symm
    rw [hσ']; exact hrepr v
  | ifgoto b l =>
    simp only [execSymbolic]
    by_cases hb : b.eval σ am = true
    · have := step_det _ (Step.iftrue hinstr hb)
      have hσ' : σ' = σ := (Cfg.run.inj this).2.1.symm
      rw [hσ']; exact hrepr v
    · have := step_det _ (Step.iffall hinstr (Bool.eq_false_iff.mpr hb))
      have hσ' : σ' = σ := (Cfg.run.inj this).2.1.symm
      rw [hσ']; exact hrepr v
  | halt  =>
    exfalso
    have := step_det _ (Step.halt hinstr)
    exact Cfg.noConfusion this
  | arrLoad dest arr idx _ =>
    exact absurd hscalar (by simp [TAC.isScalar])
  | arrStore arr idx val ty =>
    simp only [execSymbolic]
    -- arrStore only changes ArrayMem, not Store: σ' = σ
    obtain ⟨idxVal, hv⟩ : ∃ idxVal : BitVec 64, σ idx = .int idxVal := by
      revert hstep; generalize _sbam' = am'; intro hstep; cases hstep <;> simp_all
    have hty : (σ val).typeOf = ty := by
      revert hstep; generalize _sbam' = am'; intro hstep; cases hstep <;> simp_all
    have hbnd : idxVal < prog.arraySizeBv arr := by
      revert hstep; generalize _sbam' = am'; intro hstep; cases hstep <;> simp_all
    have := step_det _ (Step.arrStore hinstr hv hty hbnd)
    have hσ' : σ' = σ := (Cfg.run.inj this).2.1.symm
    rw [hσ']; exact hrepr v
  | fbinop dest fop y z =>
    simp only [execSymbolic]
    obtain ⟨fa, fb, hfa, hfb⟩ : ∃ fa fb : BitVec 64, σ y = .float fa ∧ σ z = .float fb := by
      revert hstep; generalize _sbam' = am'; intro hstep; cases hstep <;> simp_all
    have hstep' : Step prog (Cfg.run pc σ am) (Cfg.run (pc + 1) (σ[dest ↦ .float (fop.eval fa fb)]) am) :=
      Step.fbinop hinstr hfa hfb
    have := step_det _ hstep'
    have hσ' : σ' = σ[dest ↦ .float (fop.eval fa fb)] := (Cfg.run.inj this).2.1.symm
    rw [hσ']
    by_cases hvd : v = dest
    · rw [hvd, ssGet_ssSet_same]
      simp only [Expr.eval, Store.update_self]
      have ha : ((ssGet ss y).eval σ₀ am).toFloat = fa := by
        rw [hrepr y, hfa]; rfl
      have hb : ((ssGet ss z).eval σ₀ am).toFloat = fb := by
        rw [hrepr z, hfb]; rfl
      rw [ha, hb]
    · rw [ssGet_ssSet_other _ _ _ _ hvd, hrepr]
      exact (Store.update_other σ dest v _ hvd).symm
  | intToFloat dest src =>
    simp only [execSymbolic]
    obtain ⟨n, hn⟩ : ∃ n : BitVec 64, σ src = .int n := by
      revert hstep; generalize _sbam' = am'; intro hstep; cases hstep <;> simp_all
    have hstep' : Step prog (Cfg.run pc σ am) (Cfg.run (pc + 1) (σ[dest ↦ .float (intToFloatBv n)]) am) :=
      Step.intToFloat hinstr hn
    have := step_det _ hstep'
    have hσ' : σ' = σ[dest ↦ .float (intToFloatBv n)] := (Cfg.run.inj this).2.1.symm
    rw [hσ']
    by_cases hvd : v = dest
    · rw [hvd, ssGet_ssSet_same]
      simp only [Expr.eval, Store.update_self]
      have hsrc : ((ssGet ss src).eval σ₀ am).toInt = n := by
        rw [hrepr src, hn]; rfl
      rw [hsrc]
    · rw [ssGet_ssSet_other _ _ _ _ hvd, hrepr]
      exact (Store.update_other σ dest v _ hvd).symm
  | floatToInt dest src =>
    simp only [execSymbolic]
    obtain ⟨f, hf⟩ : ∃ f : BitVec 64, σ src = .float f := by
      revert hstep; generalize _sbam' = am'; intro hstep; cases hstep <;> simp_all
    have hstep' : Step prog (Cfg.run pc σ am) (Cfg.run (pc + 1) (σ[dest ↦ .int (floatToIntBv f)]) am) :=
      Step.floatToInt hinstr hf
    have := step_det _ hstep'
    have hσ' : σ' = σ[dest ↦ .int (floatToIntBv f)] := (Cfg.run.inj this).2.1.symm
    rw [hσ']
    by_cases hvd : v = dest
    · rw [hvd, ssGet_ssSet_same]
      simp only [Expr.eval, Store.update_self]
      have hsrc : ((ssGet ss src).eval σ₀ am).toFloat = f := by
        rw [hrepr src, hf]; rfl
      rw [hsrc]
    · rw [ssGet_ssSet_other _ _ _ _ hvd, hrepr]
      exact (Store.update_other σ dest v _ hvd).symm
  | floatUnary dest op src =>
    simp only [execSymbolic]
    obtain ⟨f, hf⟩ : ∃ f : BitVec 64, σ src = .float f := by
      revert hstep; generalize _sbam' = am'; intro hstep; cases hstep <;> simp_all
    have hstep' : Step prog (Cfg.run pc σ am) (Cfg.run (pc + 1) (σ[dest ↦ .float (op.eval f)]) am) :=
      Step.floatUnary hinstr hf
    have := step_det _ hstep'
    have hσ' : σ' = σ[dest ↦ .float (op.eval f)] := (Cfg.run.inj this).2.1.symm
    rw [hσ']
    by_cases hvd : v = dest
    · rw [hvd, ssGet_ssSet_same]
      simp only [Expr.eval, Store.update_self]
      have hsrc : ((ssGet ss src).eval σ₀ am).toFloat = f := by
        rw [hrepr src, hf]; rfl
      rw [hsrc]
    · rw [ssGet_ssSet_other _ _ _ _ hvd, hrepr]
      exact (Store.update_other σ dest v _ hvd).symm
  | fternop dest op y z w =>
    simp only [execSymbolic]
    obtain ⟨fa, fb, fc, hfa, hfb, hfc⟩ : ∃ fa fb fc : BitVec 64, σ y = .float fa ∧ σ z = .float fb ∧ σ w = .float fc := by
      revert hstep; generalize _sbam' = am'; intro hstep; cases hstep <;> simp_all
    have hstep' : Step prog (Cfg.run pc σ am) (Cfg.run (pc + 1) (σ[dest ↦ .float (FloatTernOp.eval op fa fb fc)]) am) :=
      Step.fternop hinstr hfa hfb hfc
    have := step_det _ hstep'
    have hσ' : σ' = σ[dest ↦ .float (FloatTernOp.eval op fa fb fc)] := (Cfg.run.inj this).2.1.symm
    rw [hσ']
    by_cases hvd : v = dest
    · rw [hvd, ssGet_ssSet_same]
      simp only [Expr.eval, Store.update_self]
      have ha : ((ssGet ss y).eval σ₀ am).toFloat = fa := by
        rw [hrepr y, hfa]; rfl
      have hb : ((ssGet ss z).eval σ₀ am).toFloat = fb := by
        rw [hrepr z, hfb]; rfl
      have hc : ((ssGet ss w).eval σ₀ am).toFloat = fc := by
        rw [hrepr w, hfc]; rfl
      rw [ha, hb, hc]
    · rw [ssGet_ssSet_other _ _ _ _ hvd, hrepr]
      exact (Store.update_other σ dest v _ hvd).symm
  | print _ _ =>
    simp only [execSymbolic]
    have := step_det _ (Step.print hinstr)
    have hσ' : σ' = σ := (Cfg.run.inj this).2.1.symm
    rw [hσ']; exact hrepr v
  | printInt _ =>
    simp only [execSymbolic]
    have := step_det _ (Step.printInt hinstr)
    have hσ' : σ' = σ := (Cfg.run.inj this).2.1.symm
    rw [hσ']; exact hrepr v
  | printBool _ =>
    simp only [execSymbolic]
    have := step_det _ (Step.printBool hinstr)
    have hσ' : σ' = σ := (Cfg.run.inj this).2.1.symm
    rw [hσ']; exact hrepr v
  | printFloat _ =>
    simp only [execSymbolic]
    have := step_det _ (Step.printFloat hinstr)
    have hσ' : σ' = σ := (Cfg.run.inj this).2.1.symm
    rw [hσ']; exact hrepr v
  | printString _ =>
    simp only [execSymbolic]
    have := step_det _ (Step.printString hinstr)
    have hσ' : σ' = σ := (Cfg.run.inj this).2.1.symm
    rw [hσ']; exact hrepr v

/-- Empty expression relation is vacuously true (no pairs to satisfy). -/
private theorem eRelToStoreRel_nil :
    eRelToStoreRel [] = fun _ _ _ _ => True := by
  funext σ_o am_o σ_t am_t; simp [eRelToStoreRel]

/-- Empty expression relation is trivially satisfied. -/
private theorem eRelToStoreRel_nil_triv {σ : Store} {am₁ am₂ : ArrayMem} :
    eRelToStoreRel [] σ am₁ σ am₂ := by
  intro _ _ h; simp at h

/-- Initial symbolic store represents identity: ssGet [] v evaluates to σ v. -/
private theorem ssGet_nil (σ : Store) (am : ArrayMem) (v : Var) :
    (ssGet ([] : SymStore) v).eval σ am = σ v := by
  simp [ssGet, List.find?, Expr.eval]

/-- ssGet on empty store returns .var v. -/
private theorem ssGet_nil_var (v : Var) : ssGet ([] : SymStore) v = .var v := by
  simp [ssGet, List.find?]

/-- If `v` is not a key in the symbolic store, `ssGet` returns `.var v`. -/
private theorem ssGet_not_key {ss : SymStore} {v : Var}
    (h : v ∉ ss.map Prod.fst) : ssGet ss v = .var v := by
  simp only [ssGet]
  induction ss with
  | nil => simp [List.find?]
  | cons p rest ih =>
    simp only [List.map, List.mem_cons, not_or] at h
    have hne : ¬(p.1 = v) := fun heq => h.1 (heq ▸ rfl)
    have hrest : v ∉ rest.map Prod.fst := h.2
    simp only [List.find?, beq_eq_false_iff_ne.mpr hne]
    exact ih hrest

/-- substSym with empty store is identity. -/
private theorem Expr.substSym_nil : ∀ (e : Expr), e.substSym ([] : SymStore) = e := by
  intro e; induction e with
  | lit _ => simp [Expr.substSym]
  | blit _ => simp [Expr.substSym]
  | var v => simp [Expr.substSym, ssGet_nil_var]
  | bin op a b iha ihb => simp [Expr.substSym, iha, ihb]
  | tobool e ih => simp [Expr.substSym, ih]
  | cmpE op a b iha ihb => simp [Expr.substSym, iha, ihb]
  | cmpLitE op a n ih => simp [Expr.substSym, ih]
  | notE e ih => simp [Expr.substSym, ih]
  | andE a b iha ihb => simp [Expr.substSym, iha, ihb]
  | orE a b iha ihb => simp [Expr.substSym, iha, ihb]
  | arrRead arr idx ih => simp [Expr.substSym, ih]
  | flit _ => simp [Expr.substSym]
  | fbin op a b iha ihb => simp [Expr.substSym, iha, ihb]
  | fcmpE op a b iha ihb => simp [Expr.substSym, iha, ihb]
  | intToFloat e ih => simp [Expr.substSym, ih]
  | floatToInt e ih => simp [Expr.substSym, ih]
  | floatUnary op e ih => simp [Expr.substSym, ih]
  | ftern op a b c iha ihb ihc => simp [Expr.substSym, iha, ihb, ihc]
  | farrRead arr idx ih => simp [Expr.substSym, ih]


/-- Free-variable-restricted variant of `substSym_sound`.
    Only requires `hrepr` for variables that actually appear in `e`. -/
theorem Expr.substSym_sound_fv (ss : SymStore) (e : Expr) (σ₀ σ' : Store)
    (am : ArrayMem)
    (hrepr : ∀ v, v ∈ e.freeVars → (ssGet ss v).eval σ₀ am = σ' v) :
    (e.substSym ss).eval σ₀ am = e.eval σ' am := by
  induction e with
  | lit n => simp [Expr.substSym, Expr.eval]
  | blit b => simp [Expr.substSym, Expr.eval]
  | var v =>
    simp [Expr.substSym, Expr.eval]
    exact hrepr v (List.mem_singleton.mpr rfl)
  | bin op a b iha ihb =>
    simp only [Expr.substSym, Expr.eval]
    rw [iha (fun v hv => hrepr v (List.mem_append_left _ hv)),
        ihb (fun v hv => hrepr v (List.mem_append_right _ hv))]
  | tobool e ih =>
    simp only [Expr.substSym, Expr.eval]; rw [ih (fun v hv => hrepr v hv)]
  | cmpE op a b iha ihb =>
    simp only [Expr.substSym, Expr.eval]
    rw [iha (fun v hv => hrepr v (List.mem_append_left _ hv)),
        ihb (fun v hv => hrepr v (List.mem_append_right _ hv))]
  | cmpLitE op a n ih =>
    simp only [Expr.substSym, Expr.eval]; rw [ih (fun v hv => hrepr v hv)]
  | notE e ih =>
    simp only [Expr.substSym, Expr.eval]; rw [ih (fun v hv => hrepr v hv)]
  | andE a b iha ihb =>
    simp only [Expr.substSym, Expr.eval]
    rw [iha (fun v hv => hrepr v (List.mem_append_left _ hv)),
        ihb (fun v hv => hrepr v (List.mem_append_right _ hv))]
  | orE a b iha ihb =>
    simp only [Expr.substSym, Expr.eval]
    rw [iha (fun v hv => hrepr v (List.mem_append_left _ hv)),
        ihb (fun v hv => hrepr v (List.mem_append_right _ hv))]
  | arrRead arr idx ih =>
    simp only [Expr.substSym, Expr.eval]; rw [ih (fun v hv => hrepr v hv)]
  | flit _ => simp [Expr.substSym, Expr.eval]
  | fbin op a b iha ihb =>
    simp only [Expr.substSym, Expr.eval]
    rw [iha (fun v hv => hrepr v (List.mem_append_left _ hv)),
        ihb (fun v hv => hrepr v (List.mem_append_right _ hv))]
  | fcmpE op a b iha ihb =>
    simp only [Expr.substSym, Expr.eval]
    rw [iha (fun v hv => hrepr v (List.mem_append_left _ hv)),
        ihb (fun v hv => hrepr v (List.mem_append_right _ hv))]
  | intToFloat e ih =>
    simp only [Expr.substSym, Expr.eval]; rw [ih (fun v hv => hrepr v hv)]
  | floatToInt e ih =>
    simp only [Expr.substSym, Expr.eval]; rw [ih (fun v hv => hrepr v hv)]
  | floatUnary op e ih =>
    simp only [Expr.substSym, Expr.eval]; rw [ih (fun v hv => hrepr v hv)]
  | ftern op a b c iha ihb ihc =>
    simp only [Expr.substSym, Expr.eval]
    rw [iha (fun v hv => hrepr v (List.mem_append_left _ (List.mem_append_left _ hv))),
        ihb (fun v hv => hrepr v (List.mem_append_left _ (List.mem_append_right _ hv))),
        ihc (fun v hv => hrepr v (List.mem_append_right _ hv))]
  | farrRead arr idx ih =>
    simp only [Expr.substSym, Expr.eval]; rw [ih (fun v hv => hrepr v hv)]

-- ============================================================
-- § 6b. PInvariant preservation soundness
-- ============================================================

/-- Key lemma: checkInvAtom soundness.
    If checkInvAtom succeeds, then for any store satisfying inv_pre,
    after executing `instr`, the atom holds in the post-store.
    Uses symbolic execution: the checker verifies that the simplified
    post-value of `x` equals the simplified post-value of `e`
    (with variables substituted by their symbolic post-values). -/
theorem checkInvAtom_sound (inv_pre : EInv) (instr : TAC) (atom : Var × Expr)
    (σ σ' : Store) (pc pc' : Label) (prog : Prog) {am am' : ArrayMem}
    (hcheck : checkInvAtom inv_pre instr atom = true)
    (hinv : EInv.toProp inv_pre σ am)
    (hstep : Step prog (Cfg.run pc σ am) (Cfg.run pc' σ' am'))
    (hinstr : prog[pc]? = some instr)
    (hnoarr : atom.2.hasArrRead = false) :
    σ' atom.1 = atom.2.eval σ' am' := by
  obtain ⟨x, e⟩ := atom; simp only
  -- checkInvAtom gives us BEq equality of simplified expressions
  simp only [checkInvAtom] at hcheck
  have hbeq := beq_iff_eq.mp hcheck
  -- Build hrepr with runtime am: symbolic store tracks the step
  have hrepr : ∀ v, (ssGet ((execSymbolic ([] : SymStore) ([] : SymArrayMem) instr).1) v).eval σ am = σ' v := by
    by_cases hscalar : instr.isScalar = true
    · exact execSymbolic_sound ([] : SymStore) ([] : SymArrayMem) instr σ σ σ' pc pc' prog am
        (ssGet_nil σ am) hstep hinstr hscalar
    · cases instr with
      | arrStore arr idx val ty =>
        simp only [execSymbolic]
        have step_det : ∀ c, Step prog (Cfg.run pc σ am) c → c = Cfg.run pc' σ' am' :=
          fun c hc => Step.deterministic hc hstep
        obtain ⟨idxVal, hv⟩ : ∃ idxVal : BitVec 64, σ idx = .int idxVal := by
          revert hstep; intro hstep; cases hstep <;> simp_all
        have hty : (σ val).typeOf = ty := by
          revert hstep; intro hstep; cases hstep <;> simp_all
        have hbnd : idxVal < prog.arraySizeBv arr := by
          revert hstep; intro hstep; cases hstep <;> simp_all
        have := step_det _ (Step.arrStore hinstr hv hty hbnd)
        have hσ' : σ' = σ := (Cfg.run.inj this).2.1.symm
        rw [hσ']; exact ssGet_nil σ am
      | arrLoad dest arr idx ty =>
        simp only [execSymbolic]
        have step_det : ∀ c, Step prog (Cfg.run pc σ am) c → c = Cfg.run pc' σ' am' :=
          fun c hc => Step.deterministic hc hstep
        obtain ⟨idxVal, hidx⟩ : ∃ idxVal : BitVec 64, σ idx = .int idxVal := by
          revert hstep; intro hstep; cases hstep <;> simp_all
        have hbnd : idxVal < prog.arraySizeBv arr := by
          revert hstep; intro hstep; cases hstep <;> simp_all
        have := step_det _ (Step.arrLoad hinstr hidx hbnd)
        have hσ' : σ' = σ[dest ↦ Value.ofBitVec ty (am.read arr idxVal)] :=
          (Cfg.run.inj this).2.1.symm
        intro v
        by_cases hvd : v = dest
        · rw [hvd, ssGet_ssSet_same, hσ']
          simp only [Store.update_self]
          -- samGet with empty SAM returns type-specific fallback matching Value.ofBitVec
          cases ty <;> simp [samGet, List.find?, Expr.eval, ssGet, Value.ofBitVec,
            CmpOp.eval, hidx, Value.toInt]
        · rw [ssGet_ssSet_other _ _ _ _ hvd, hσ', ssGet_nil]
          exact (Store.update_other σ dest v _ hvd).symm
      | _ => exact absurd rfl hscalar
  -- Build the chain using am, then bridge to am'.
  let fuel := sdFuel inv_pre
  have hlhs := Expr.simplifyDeep_sound fuel inv_pre
    (ssGet ((execSymbolic ([] : SymStore) ([] : SymArrayMem) instr).1) x) σ am hinv
  have hrhs := Expr.simplifyDeep_sound fuel inv_pre
    (e.substSym ((execSymbolic ([] : SymStore) ([] : SymArrayMem) instr).1)) σ am hinv
  have hsub := Expr.substSym_sound ((execSymbolic ([] : SymStore) ([] : SymArrayMem) instr).1) e σ σ'
    am hrepr
  -- Chain: σ' x = ... = e.eval σ' am
  have hchain : σ' x = e.eval σ' am :=
    calc σ' x
        = (ssGet ((execSymbolic ([] : SymStore) ([] : SymArrayMem) instr).1) x).eval σ am := (hrepr x).symm
      _ = ((ssGet ((execSymbolic ([] : SymStore) ([] : SymArrayMem) instr).1) x).simplifyDeep fuel inv_pre).eval σ am := hlhs.symm
      _ = ((e.substSym ((execSymbolic ([] : SymStore) ([] : SymArrayMem) instr).1)).simplifyDeep fuel inv_pre).eval σ am := by
            rw [hbeq]
      _ = (e.substSym ((execSymbolic ([] : SymStore) ([] : SymArrayMem) instr).1)).eval σ am := hrhs
      _ = e.eval σ' am := hsub
  -- Bridge: e.eval σ' am = e.eval σ' am' via arrRead-free
  rw [hchain]
  exact Expr.eval_noArrRead e σ' am am' hnoarr

/-- Extract instruction from a step to a run configuration. -/
theorem step_run_instr {p : Prog} {pc pc' : Label} {σ σ' : Store} {am am' : ArrayMem}
    (hstep : Step p (Cfg.run pc σ am) (Cfg.run pc' σ' am')) :
    ∃ instr, p[pc]? = some instr := by
  cases hstep with
  | const h => exact ⟨_, h⟩
  | copy h => exact ⟨_, h⟩
  | binop h => exact ⟨_, h⟩
  | boolop h => exact ⟨_, h⟩
  | goto h => exact ⟨_, h⟩
  | iftrue h _ => exact ⟨_, h⟩
  | iffall h _ => exact ⟨_, h⟩
  | arrLoad h _ _ => exact ⟨_, h⟩
  | arrStore h _ _ _ => exact ⟨_, h⟩
  | fbinop h _ _ => exact ⟨_, h⟩
  | fternop h _ _ _ => exact ⟨_, h⟩
  | intToFloat h _ => exact ⟨_, h⟩
  | floatToInt h _ => exact ⟨_, h⟩
  | floatUnary h _ => exact ⟨_, h⟩
  | print h => exact ⟨_, h⟩
  | printInt h => exact ⟨_, h⟩
  | printBool h => exact ⟨_, h⟩
  | printFloat h => exact ⟨_, h⟩
  | printString h => exact ⟨_, h⟩

/-- A step target is always in the successors list. -/
theorem step_successor {p : Prog} {pc pc' : Label} {σ σ' : Store} {am am' : ArrayMem}
    (hstep : Step p (Cfg.run pc σ am) (Cfg.run pc' σ' am'))
    {instr : TAC} (hinstr : p[pc]? = some instr) :
    pc' ∈ instr.successors pc := by
  have instr_eq {i : TAC} (h : p[pc]? = some i) : instr = i :=
    Option.some.inj (hinstr.symm.trans h)
  cases hstep with
  | const h => have := instr_eq h; subst this; simp [TAC.successors]
  | copy h => have := instr_eq h; subst this; simp [TAC.successors]
  | binop h => have := instr_eq h; subst this; simp [TAC.successors]
  | boolop h => have := instr_eq h; subst this; simp [TAC.successors]
  | goto h => have := instr_eq h; subst this; simp [TAC.successors]
  | iftrue h _ => have := instr_eq h; subst this; simp [TAC.successors]
  | iffall h _ => have := instr_eq h; subst this; simp [TAC.successors]
  | arrLoad h _ _ => have := instr_eq h; subst this; simp [TAC.successors]
  | arrStore h _ _ _ => have := instr_eq h; subst this; simp [TAC.successors]
  | fbinop h _ _ => have := instr_eq h; subst this; simp [TAC.successors]
  | fternop h _ _ _ => have := instr_eq h; subst this; simp [TAC.successors]
  | intToFloat h _ => have := instr_eq h; subst this; simp [TAC.successors]
  | floatToInt h _ => have := instr_eq h; subst this; simp [TAC.successors]
  | floatUnary h _ => have := instr_eq h; subst this; simp [TAC.successors]
  | print h => have := instr_eq h; subst this; simp [TAC.successors]
  | printInt h => have := instr_eq h; subst this; simp [TAC.successors]
  | printBool h => have := instr_eq h; subst this; simp [TAC.successors]
  | printFloat h => have := instr_eq h; subst this; simp [TAC.successors]
  | printString h => have := instr_eq h; subst this; simp [TAC.successors]

private theorem and_true_split {a b : Bool} (h : (a && b) = true) :
    a = true ∧ b = true := by
  simp [Bool.and_eq_true] at h; exact h

/-- Helper: checkProg soundness for one program/invariant pair. -/
private theorem noArrRead_of_inv_all (inv : Array EInv)
    (hnoarr : checkNoArrReadInInvs inv = true)
    (l : Nat) :
    (inv.getD l ([] : EInv)).all (fun (_, e) => !e.hasArrRead) = true := by
  unfold checkNoArrReadInInvs at hnoarr
  by_cases hlt : l < inv.size
  · have hgetD : inv.getD l ([] : EInv) = inv[l] := by simp [Array.getD, hlt]
    rw [hgetD]; exact (Array.all_eq_true.mp hnoarr) l hlt
  · have hgetD : inv.getD l ([] : EInv) = [] := by simp [Array.getD, Nat.not_lt.mp hlt]
    rw [hgetD]; rfl

private theorem noArrRead_of_inv (inv : Array EInv)
    (hnoarr : checkNoArrReadInInvs inv = true)
    (l : Nat) (atom : Var × Expr) (hmem : atom ∈ inv.getD l ([] : EInv)) :
    atom.2.hasArrRead = false := by
  unfold checkNoArrReadInInvs at hnoarr
  by_cases hlt : l < inv.size
  · -- inv.getD l [] = inv[l] when l < inv.size
    have hgetD : inv.getD l ([] : EInv) = inv[l] := by simp [Array.getD, hlt]
    rw [hgetD] at hmem
    -- Extract from inv.all
    have hall : (inv[l]).all (fun x => !x.2.hasArrRead) = true :=
      (Array.all_eq_true.mp hnoarr) l hlt
    rw [List.all_eq_true] at hall
    have := hall atom hmem
    simp at this
    exact this
  · -- l ≥ inv.size → inv.getD l [] = []
    have hgetD : inv.getD l ([] : EInv) = [] := by simp [Array.getD, Nat.not_lt.mp hlt]
    rw [hgetD] at hmem; exact absurd hmem (by simp)

private theorem checkProg_sound (prog : Prog) (inv : Array EInv)
    (h : (List.range prog.size).all (fun pc =>
      match prog[pc]? with
      | some instr =>
        (instr.successors pc).all fun pc' =>
          (inv.getD pc' ([] : EInv)).all (checkInvAtom (inv.getD pc ([] : EInv)) instr)
      | none => true) = true)
    (hnoarr : checkNoArrReadInInvs inv = true) :
    PInvariantMap.preserved (fun l => (inv.getD l ([] : EInv)).toProp) prog := by
  intro pc σ am hinvpc pc' σ' am' hstep
  obtain ⟨instr, hinstr⟩ := step_run_instr hstep
  have hbound := bound_of_getElem? hinstr
  rw [List.all_eq_true] at h
  have hpc := h pc (List.mem_range.mpr hbound)
  simp only [hinstr] at hpc
  rw [List.all_eq_true] at hpc
  have hsucc := step_successor hstep hinstr
  have hpc' := hpc pc' hsucc
  rw [List.all_eq_true] at hpc'
  intro atom hatom
  exact checkInvAtom_sound (inv.getD pc ([] : EInv)) instr atom σ σ' pc pc' prog
    (hpc' atom hatom) hinvpc hstep hinstr (noArrRead_of_inv inv hnoarr pc' atom hatom)

/-- **Condition 2b**: checkInvariantsPreservedExec → checkInvariantsPreservedProp -/
theorem checkInvariantsPreservedExec_sound (dc : ECertificate)
    (h : checkInvariantsPreservedExec dc = true)
    (hnoarr_orig : checkNoArrReadInInvs dc.inv_orig = true)
    (hnoarr_trans : checkNoArrReadInInvs dc.inv_trans = true) :
    checkInvariantsPreservedProp (toPCertificate dc) := by
  unfold checkInvariantsPreservedExec at h
  simp only [checkInvAtomFast_eq_checkInvAtom_fn] at h
  have ⟨h1, h2⟩ := and_true_split h
  exact ⟨checkProg_sound dc.orig dc.inv_orig h1 hnoarr_orig,
         checkProg_sound dc.trans dc.inv_trans h2 hnoarr_trans⟩

/-- Variable names appearing in an instruction (matching collectAllVars.extract). -/
private def instrDests (instr : TAC) : List Var :=
  match instr with
  | .const x _     => [x]
  | .copy x y      => [x, y]
  | .binop x _ y z => [x, y, z]
  | .boolop x _    => [x]
  | .fbinop x _ y z => [x, y, z]
  | .intToFloat x y => [x, y]
  | .floatToInt x y => [x, y]
  | .floatUnary x _ y => [x, y]
  | .fternop x _ a b c => [x, a, b, c]
  | .arrLoad x _ idx _ => [x, idx]
  | .arrStore _ idx val _ => [idx, val]
  | .print _ vs   => vs
  | .ifgoto b _    => b.vars
  | _              => []

/-- Elements already in the accumulator survive foldl. -/
private theorem mem_foldl_init (xs : List TAC) (init : List Var)
    {v : Var} (hv : v ∈ init) :
    v ∈ xs.foldl (fun acc i => acc ++ instrDests i) init := by
  induction xs generalizing init with
  | nil => exact hv
  | cons _ tl ih => exact ih (init ++ instrDests _) (List.mem_append_left _ hv)

/-- Elements from any member's instrDests end up in the foldl result. -/
private theorem mem_foldl_elem (xs : List TAC) (init : List Var)
    {x : TAC} (hx : x ∈ xs) {v : Var} (hv : v ∈ instrDests x) :
    v ∈ xs.foldl (fun acc i => acc ++ instrDests i) init := by
  induction xs generalizing init with
  | nil => simp at hx
  | cons hd tl ih =>
    cases List.mem_cons.mp hx with
    | inl heq => subst heq; exact mem_foldl_init tl _ (List.mem_append_right init hv)
    | inr htl => exact ih _ htl

/-- If v ∈ instrDests of an instruction in p1, then v ∈ collectAllVars p1 p2. -/
private theorem instrDests_sub_collectAllVars_left (p1 p2 : Prog) (instr : TAC)
    (hmem : instr ∈ p1.code.toList) (v : Var) (hv : v ∈ instrDests instr) :
    v ∈ collectAllVars p1 p2 := by
  unfold collectAllVars
  apply List.mem_append_left
  exact mem_foldl_elem p1.code.toList ([] : List Var) hmem hv

/-- If v ∈ instrDests of an instruction in p2, then v ∈ collectAllVars p1 p2. -/
private theorem instrDests_sub_collectAllVars_right (p1 p2 : Prog) (instr : TAC)
    (hmem : instr ∈ p2.code.toList) (v : Var) (hv : v ∈ instrDests instr) :
    v ∈ collectAllVars p1 p2 := by
  unfold collectAllVars
  apply List.mem_append_right
  exact mem_foldl_elem p2.code.toList ([] : List Var) hmem hv

/-- Array getElem? to toList membership. -/
private theorem getElem?_mem_toList {arr : Prog} {i : Nat} {x : TAC}
    (h : arr[i]? = some x) : x ∈ arr.code.toList := by
  rw [Prog.getElem?_code] at h
  have hb := bound_of_getElem? h
  have heq := (Array.getElem?_eq_some_iff.mp h).2
  exact heq ▸ Array.getElem_mem_toList (h := hb)

/-- If v is not the dest of instr, execSymbolic preserves ssGet v. -/
private theorem execSymbolic_preserves_var (ss : SymStore) (sam : SymArrayMem)
    (instr : TAC) (v : Var)
    (hv : v ∉ instrDests instr) :
    ssGet (execSymbolic ss sam instr).1 v = ssGet ss v := by
  cases instr with
  | const x n =>
    simp [instrDests] at hv
    cases n with
    | int k => simp only [execSymbolic]; exact ssGet_ssSet_other ss x v _ hv
    | bool b => simp only [execSymbolic]; exact ssGet_ssSet_other ss x v _ hv
    | float f => simp only [execSymbolic]; exact ssGet_ssSet_other ss x v _ hv
  | copy x y =>
    simp [instrDests] at hv; simp only [execSymbolic]; exact ssGet_ssSet_other ss x v _ hv.1
  | binop x op y z =>
    simp [instrDests] at hv; simp only [execSymbolic]; exact ssGet_ssSet_other ss x v _ hv.1
  | fbinop x fop y z =>
    simp [instrDests] at hv; simp only [execSymbolic]; exact ssGet_ssSet_other ss x v _ hv.1
  | fternop x op a b c =>
    simp [instrDests] at hv; simp only [execSymbolic]; exact ssGet_ssSet_other ss x v _ hv.1
  | intToFloat x y =>
    simp [instrDests] at hv; simp only [execSymbolic]; exact ssGet_ssSet_other ss x v _ hv.1
  | floatToInt x y =>
    simp [instrDests] at hv; simp only [execSymbolic]; exact ssGet_ssSet_other ss x v _ hv.1
  | floatUnary x op y =>
    simp [instrDests] at hv; simp only [execSymbolic]; exact ssGet_ssSet_other ss x v _ hv.1
  | boolop x _ =>
    simp [instrDests] at hv; simp only [execSymbolic]; exact ssGet_ssSet_other ss x v _ hv
  | goto _ => rfl
  | ifgoto _ _ => simp only [execSymbolic]
  | halt => rfl
  | arrLoad x _ idx _ =>
    simp [instrDests] at hv; simp only [execSymbolic]; exact ssGet_ssSet_other ss x v _ hv.1
  | arrStore _ _ _ _ => rfl
  | print _ _ => rfl
  | printInt _ => rfl
  | printBool _ => rfl
  | printFloat _ => rfl
  | printString _ => rfl

/-- If v is not the dest of any instruction in the program, execPath preserves ssGet v. -/
private theorem execPath_preserves_var (orig : Prog) (ss : SymStore) (sam : SymArrayMem)
    (pc : Label) (labels : List Label) (v : Var)
    (hv : ∀ (l : Label) (instr : TAC), orig[l]? = some instr → v ∉ instrDests instr) :
    ssGet (execPath orig ss sam pc labels).1 v = ssGet ss v := by
  induction labels generalizing ss sam pc with
  | nil => rfl
  | cons nextPC rest ih =>
    simp only [execPath]
    cases horig : orig[pc]? with
    | none => rfl
    | some instr =>
      have h1 := execSymbolic_preserves_var ss sam instr v (hv pc instr horig)
      have h2 := ih (execSymbolic ss sam instr).1 (execSymbolic ss sam instr).2 nextPC
      exact h2.trans h1

/-- If `isNonZeroLit e = true`, then either `e = .lit n` for some `n ≠ 0`,
    or `e = .blit true`. -/
private theorem isNonZeroLit_sound {e : Expr} (h : e.isNonZeroLit = true) :
    (∃ n, e = .lit n ∧ n ≠ 0) ∨ e = .blit true := by
  cases e with
  | lit n =>
    left; refine ⟨n, rfl, ?_⟩
    intro heq; subst heq; simp [Expr.isNonZeroLit] at h
  | blit b =>
    cases b with
    | true  => right; rfl
    | false => simp [Expr.isNonZeroLit] at h
  | var => simp [Expr.isNonZeroLit] at h
  | bin => simp [Expr.isNonZeroLit] at h
  | tobool _ | cmpE _ _ _ | cmpLitE _ _ _ | notE _ | andE _ _ | orE _ _ | arrRead _ _ => simp [Expr.isNonZeroLit] at h
  | flit _ | fbin _ _ _ | fcmpE _ _ _ | intToFloat _ | floatToInt _ | floatUnary _ _ | ftern _ _ _ _ | farrRead _ _ => simp [Expr.isNonZeroLit] at h

/-- Soundness of `BoolExpr.symEval`: if symbolic evaluation returns a result,
    it agrees with runtime evaluation. -/
private theorem BoolExpr.symEval_sound (b : BoolExpr) (ss : SymStore) (inv : EInv)
    (σ₀ σ : Store) (am : ArrayMem)
    (hrepr : ∀ v, (ssGet ss v).eval σ₀ am = σ v)
    (hinv : EInv.toProp inv σ₀ am) :
    ∀ r, b.symEval ss inv = some r → b.eval σ am = r := by
  induction b with
  | lit b => intro r heval; simp [BoolExpr.symEval] at heval; simp [BoolExpr.eval, heval]
  | bvar x =>
    intro r heval
    simp only [BoolExpr.symEval] at heval
    split at heval <;> simp at heval
    rename_i b heq
    have hsimpl := Expr.simplifyDeep_sound (sdFuel inv) inv (ssGet ss x) σ₀ am hinv
    rw [heq, Expr.eval] at hsimpl
    simp only [BoolExpr.eval]
    rw [← hrepr x, ← hsimpl]; simp [heval]
  | cmp op a b =>
    intro r heval
    simp only [BoolExpr.symEval] at heval
    split at heval <;> simp at heval
    rename_i va vb ha hb
    simp only [BoolExpr.eval]
    have hsa := Expr.simplifyDeep_sound (sdFuel inv) inv (a.substSym' ss) σ₀ am hinv
    have hsb := Expr.simplifyDeep_sound (sdFuel inv) inv (b.substSym' ss) σ₀ am hinv
    rw [ha, Expr.eval] at hsa; rw [hb, Expr.eval] at hsb
    simp only [Expr.substSym'_eq_substSym] at hsa hsb
    rw [Expr.substSym_sound ss a σ₀ σ am hrepr] at hsa
    rw [Expr.substSym_sound ss b σ₀ σ am hrepr] at hsb
    rw [← hsa, ← hsb]; simp [heval]
  | not e ih =>
    intro r heval
    simp only [BoolExpr.symEval] at heval
    cases he : e.symEval ss inv with
    | none => simp [he, Option.map] at heval
    | some val =>
      simp [he, Option.map] at heval
      simp only [BoolExpr.eval, ih val he, heval, Bool.not_not]
  | fcmp op a b =>
    intro r heval; simp [BoolExpr.symEval] at heval
  | bexpr e =>
    intro r heval
    simp only [BoolExpr.symEval] at heval
    split at heval <;> simp at heval
    rename_i b heq
    have hs := Expr.simplifyDeep_sound (sdFuel inv) inv (e.substSym' ss) σ₀ am hinv
    rw [heq, Expr.eval] at hs
    simp only [Expr.substSym'_eq_substSym] at hs
    rw [Expr.substSym_sound ss e σ₀ σ am hrepr] at hs
    simp only [BoolExpr.eval]; rw [← hs]; simp [heval]

/-- Normalization preserves BoolExpr evaluation (under the symbolic store / invariant).
    The normalized expression is evaluated at `σ₀ am₀` (the initial store/memory
    where hrepr/hinv hold), and the original at `σ am` (the post-store).
    The chain: simplify_sound ∘ substSym_sound ∘ eval_noArrRead bridges them. -/
private theorem BoolExpr.normalize_eval (b : BoolExpr) (ss : SymStore) (inv : EInv)
    (σ₀ σ : Store) (am₀ am : ArrayMem)
    (hrepr : ∀ v, (ssGet ss v).eval σ₀ am₀ = σ v)
    (hinv : EInv.toProp inv σ₀ am₀)
    (hnoarr : b.hasArrRead = false) :
    (b.normalize ss inv).eval σ₀ am₀ = b.eval σ am := by
  induction b with
  | lit _ => simp [BoolExpr.normalize, BoolExpr.eval]
  | bvar x =>
    unfold BoolExpr.normalize
    split
    · rename_i b_val heq
      have hsimpl := Expr.simplifyDeep_sound (sdFuel inv) inv (ssGet ss x) σ₀ am₀ hinv
      rw [heq, Expr.eval] at hsimpl
      simp only [BoolExpr.eval]; rw [← hrepr x, ← hsimpl]; rfl
    · -- bvar fallback: normalize returns .bexpr e' where e' = (ssGet ss x).simplifyDeep
      rename_i e' heq
      simp only [BoolExpr.eval]
      have hsimpl := Expr.simplifyDeep_sound (sdFuel inv) inv (ssGet ss x) σ₀ am₀ hinv
      rw [hsimpl, hrepr x]
  | cmp op a b_e =>
    simp only [BoolExpr.hasArrRead, Bool.or_eq_false_iff] at hnoarr
    simp only [BoolExpr.normalize]
    split
    next va vb ha hb =>
      simp only [BoolExpr.eval]
      have hsa := Expr.simplifyDeep_sound (sdFuel inv) inv (a.substSym' ss) σ₀ am₀ hinv
      have hsb := Expr.simplifyDeep_sound (sdFuel inv) inv (b_e.substSym' ss) σ₀ am₀ hinv
      rw [ha, Expr.eval] at hsa; rw [hb, Expr.eval] at hsb
      simp only [Expr.substSym'_eq_substSym] at hsa hsb
      rw [Expr.substSym_sound ss a σ₀ σ am₀ hrepr] at hsa
      rw [Expr.substSym_sound ss b_e σ₀ σ am₀ hrepr] at hsb
      rw [← Expr.eval_noArrRead a σ am₀ am hnoarr.1,
          ← Expr.eval_noArrRead b_e σ am₀ am hnoarr.2,
          ← hsa, ← hsb]; simp [Value.toInt]
    next a' b' _ =>
      -- Same chain as the lit case: simplifyDeep_sound ∘ substSym_sound ∘ eval_noArrRead
      simp only [BoolExpr.eval, Expr.substSym'_eq_substSym]
      have hsa := Expr.simplifyDeep_sound (sdFuel inv) inv (a.substSym' ss) σ₀ am₀ hinv
      have hsb := Expr.simplifyDeep_sound (sdFuel inv) inv (b_e.substSym' ss) σ₀ am₀ hinv
      simp only [Expr.substSym'_eq_substSym] at hsa hsb
      rw [Expr.substSym_sound ss a σ₀ σ am₀ hrepr] at hsa
      rw [Expr.substSym_sound ss b_e σ₀ σ am₀ hrepr] at hsb
      rw [hsa, hsb, Expr.eval_noArrRead a σ am₀ am hnoarr.1,
          Expr.eval_noArrRead b_e σ am₀ am hnoarr.2]
  | not e ih =>
    simp only [BoolExpr.hasArrRead] at hnoarr
    have hih := ih hnoarr
    simp only [BoolExpr.eval]
    show (match e.normalize ss inv with
      | BoolExpr.lit b => BoolExpr.lit (!b) | BoolExpr.not inner => inner | e' => BoolExpr.not e').eval σ₀ am₀ = !(e.eval σ am)
    generalize hgen : e.normalize ss inv = enorm
    rw [hgen] at hih
    cases enorm with
    | lit b_val => simp only [BoolExpr.eval] at hih ⊢; rw [hih]
    | not inner => simp only [BoolExpr.eval] at hih ⊢; rw [← hih, Bool.not_not]
    | bvar x => simp only [BoolExpr.eval] at hih ⊢; rw [hih]
    | cmp op' a' b' => simp only [BoolExpr.eval] at hih ⊢; rw [hih]
    | fcmp op' a' b' => simp only [BoolExpr.eval] at hih ⊢; rw [hih]
    | bexpr e' => simp only [BoolExpr.eval] at hih ⊢; rw [hih]
  | fcmp op a b_e =>
    simp only [BoolExpr.hasArrRead, Bool.or_eq_false_iff] at hnoarr
    simp only [BoolExpr.normalize]
    split
    next va vb ha hb =>
      simp only [BoolExpr.eval]
      have hsa := Expr.simplifyDeep_sound (sdFuel inv) inv (a.substSym' ss) σ₀ am₀ hinv
      have hsb := Expr.simplifyDeep_sound (sdFuel inv) inv (b_e.substSym' ss) σ₀ am₀ hinv
      rw [ha, Expr.eval] at hsa; rw [hb, Expr.eval] at hsb
      simp only [Expr.substSym'_eq_substSym] at hsa hsb
      rw [Expr.substSym_sound ss a σ₀ σ am₀ hrepr] at hsa
      rw [Expr.substSym_sound ss b_e σ₀ σ am₀ hrepr] at hsb
      rw [← Expr.eval_noArrRead a σ am₀ am hnoarr.1,
          ← Expr.eval_noArrRead b_e σ am₀ am hnoarr.2,
          ← hsa, ← hsb]; simp [Value.toFloat]
    next a' b' _ =>
      -- Same chain as the lit case: simplifyDeep_sound ∘ substSym_sound ∘ eval_noArrRead
      simp only [BoolExpr.eval, Expr.substSym'_eq_substSym]
      have hsa := Expr.simplifyDeep_sound (sdFuel inv) inv (a.substSym' ss) σ₀ am₀ hinv
      have hsb := Expr.simplifyDeep_sound (sdFuel inv) inv (b_e.substSym' ss) σ₀ am₀ hinv
      simp only [Expr.substSym'_eq_substSym] at hsa hsb
      rw [Expr.substSym_sound ss a σ₀ σ am₀ hrepr] at hsa
      rw [Expr.substSym_sound ss b_e σ₀ σ am₀ hrepr] at hsb
      rw [hsa, hsb, Expr.eval_noArrRead a σ am₀ am hnoarr.1,
          Expr.eval_noArrRead b_e σ am₀ am hnoarr.2]
  | bexpr e =>
    simp only [BoolExpr.hasArrRead] at hnoarr
    unfold BoolExpr.normalize
    split
    · -- simplifies to .blit b → .lit b
      rename_i b_val heq
      simp only [BoolExpr.eval]
      have hs := Expr.simplifyDeep_sound (sdFuel inv) inv (e.substSym' ss) σ₀ am₀ hinv
      rw [heq, Expr.eval] at hs
      simp only [Expr.substSym'_eq_substSym] at hs
      rw [Expr.substSym_sound ss e σ₀ σ am₀ hrepr] at hs
      rw [← Expr.eval_noArrRead e σ am₀ am hnoarr, ← hs]; rfl
    · -- fallback: .bexpr e' — same chain as cmp/fcmp
      rename_i e' heq
      simp only [BoolExpr.eval, Expr.substSym'_eq_substSym]
      have hs := Expr.simplifyDeep_sound (sdFuel inv) inv (e.substSym' ss) σ₀ am₀ hinv
      simp only [Expr.substSym'_eq_substSym] at hs
      rw [Expr.substSym_sound ss e σ₀ σ am₀ hrepr] at hs
      rw [hs, Expr.eval_noArrRead e σ am₀ am hnoarr]

/-- From checkInstrAliasOk for arrLoad, derive the no-alias condition for samGet_sound. -/
private theorem checkInstrAliasOk_arrLoad_noalias
    (ss : SymStore) (sam : SymArrayMem) (inv : EInv)
    (x : Var) (arr : ArrayName) (idx : Var) {ty : VarTy}
    (σ₀ : Store) (am₀ : ArrayMem)
    (hinv : EInv.toProp inv σ₀ am₀)
    (halias : checkInstrAliasOk (.arrLoad x arr idx ty) ss sam inv = true) :
    ∀ a i v, (a, i, v) ∈ sam → a = arr → ¬(i == ssGet ss idx) →
      (i.eval σ₀ am₀).toInt ≠ ((ssGet ss idx).eval σ₀ am₀).toInt := by
  intro a ie ve hmem ha hne
  simp only [checkInstrAliasOk, List.all_eq_true] at halias
  have hentry := halias (a, ie, ve) hmem
  simp only [ha, beq_self_eq_true, Bool.not_true, Bool.false_or] at hentry
  -- hentry now: (ie == ssGet ss idx || match ...) = true
  rw [show (ie == ssGet ss idx) = false from Bool.eq_false_iff.mpr hne] at hentry
  simp only [Bool.false_or] at hentry
  -- hentry: match ie.simplifyDeep .. inv, (ssGet ss idx).simplifyDeep .. inv with | .lit n, .lit m => !(n==m) | _ => false = true
  generalize hsi : ie.simplifyDeep (sdFuel inv) inv = si at hentry
  generalize hsk : (ssGet ss idx).simplifyDeep (sdFuel inv) inv = sk at hentry
  match si, sk, hentry with
  | .lit n, .lit m, hlit =>
    simp only [Bool.not_eq_true', beq_eq_false_iff_ne] at hlit
    have hs1 := (Expr.simplifyDeep_sound (sdFuel inv) inv ie σ₀ am₀ hinv).symm
    have hs2 := (Expr.simplifyDeep_sound (sdFuel inv) inv (ssGet ss idx) σ₀ am₀ hinv).symm
    rw [hsi, Expr.eval] at hs1; rw [hsk, Expr.eval] at hs2
    rw [hs1, hs2]; simp [Value.toInt]
    exact fun h => hlit h

/-- If `simplifyDeep` returns `.lit n`, then the variable's runtime value is `.int n`. -/
private theorem simplify_lit_val {ss : SymStore} {inv : EInv} {v : Var} {n : BitVec 64}
    {σ₀ σ : Store} {am₀ : ArrayMem}
    (hsx : (ssGet ss v).simplifyDeep (sdFuel inv) inv = .lit n)
    (hrepr : ∀ w, (ssGet ss w).eval σ₀ am₀ = σ w)
    (hinv : EInv.toProp inv σ₀ am₀) : (σ v).toInt = n := by
  have h := Expr.simplifyDeep_sound (sdFuel inv) inv (ssGet ss v) σ₀ am₀ hinv
  rw [hsx, Expr.eval] at h
  rw [hrepr v] at h; rw [← h]; rfl

/-- If `simplifyDeep` returns `.blit b`, then the variable's runtime toBool is `b`. -/
private theorem simplify_blit_val {ss : SymStore} {inv : EInv} {v : Var} {b : Bool}
    {σ₀ σ : Store} {am₀ : ArrayMem}
    (hsx : (ssGet ss v).simplifyDeep (sdFuel inv) inv = .blit b)
    (hrepr : ∀ w, (ssGet ss w).eval σ₀ am₀ = σ w)
    (hinv : EInv.toProp inv σ₀ am₀) : (σ v).toBool = b := by
  have h := Expr.simplifyDeep_sound (sdFuel inv) inv (ssGet ss v) σ₀ am₀ hinv
  rw [hsx, Expr.eval] at h
  rw [hrepr v] at h; rw [← h]; rfl

/-- If `simplifyDeep` returns `.flit f`, then the variable's runtime toFloat is `f`. -/
private theorem simplify_flit_val {ss : SymStore} {inv : EInv} {v : Var} {f : BitVec 64}
    {σ₀ σ : Store} {am₀ : ArrayMem}
    (hsx : (ssGet ss v).simplifyDeep (sdFuel inv) inv = .flit f)
    (hrepr : ∀ w, (ssGet ss w).eval σ₀ am₀ = σ w)
    (hinv : EInv.toProp inv σ₀ am₀) : (σ v).toFloat = f := by
  have h := Expr.simplifyDeep_sound (sdFuel inv) inv (ssGet ss v) σ₀ am₀ hinv
  rw [hsx, Expr.eval] at h
  rw [hrepr v] at h; rw [← h]; rfl


/-- Generalized path execution soundness with arbitrary initial symbolic store.
    `hDivSafe` provides div-safety for the first binop on the path.
    `hRestNoDivMod` guarantees no div/mod at intermediate labels. -/
private theorem execPath_sound_gen (orig : Prog) (ss : SymStore) (sam : SymArrayMem) (inv : EInv)
    (σ₀ σ : Store) (pc : Label) (labels : List Label) (pc' : Label)
    (branchInfo : Option (BoolExpr × Bool))
    (am₀ am : ArrayMem)
    (Γ : TyCtx) (hwtp : WellTypedProg Γ orig) (hts : TypedStore Γ σ)
    (hrepr : ∀ v, (ssGet ss v).eval σ₀ am₀ = σ v)
    (hinv : EInv.toProp inv σ₀ am₀)
    (hsamCoh : SamCoherent sam σ₀ am₀ am)
    (hsamTyped : ∀ a i v, (a, i, v) ∈ sam → (v.eval σ₀ am₀).typeOf = arrayElemTy orig.arrayDecls a)
    (_hInvNoArrRead : inv.all (fun (_, e) => !e.hasArrRead) = true)
    (hpath : checkOrigPath orig ss sam inv pc labels pc' branchInfo = true)
    (hbranch : ∀ cond taken, branchInfo = some (cond, taken) →
        cond.eval σ am = taken)
    (hbranchNoArr : ∀ cond taken, branchInfo = some (cond, taken) →
        cond.hasArrRead = false)
    (hOrigBounds : labels ≠ [] → ∀ arr idx (idxVal : BitVec 64) ty,
        ((∃ x, orig[pc]? = some (.arrLoad x arr idx ty)) ∨
         (∃ val, orig[pc]? = some (.arrStore arr idx val ty))) →
        σ idx = .int idxVal → idxVal < orig.arraySizeBv arr)
    (hRestScalar : ∀ l ∈ labels.dropLast, ∀ instr, orig[l]? = some instr → instr.isScalar = true)
    (hDivSafe : labels ≠ [] → ∀ x (op : BinOp) y z (a b : BitVec 64),
        orig[pc]? = some (.binop x op y z) →
        σ y = .int a → σ z = .int b → op.safe a b)
    (hRestNoDivMod : ∀ l ∈ labels.dropLast, ∀ x y z,
        orig[l]? ≠ some (.binop x .div y z) ∧ orig[l]? ≠ some (.binop x .mod y z))
    (hBoolNoArr : ∀ (pc' : Nat) instr, orig[pc']? = some instr →
        (∀ x be, instr = TAC.boolop x be → be.hasArrRead = false) ∧
        (∀ b l, instr = TAC.ifgoto b l → b.hasArrRead = false)) :
    ∃ σ' am', Steps orig (Cfg.run pc σ am) (Cfg.run pc' σ' am') ∧
          (∀ v, (ssGet (execPath orig ss sam pc labels).1 v).eval σ₀ am₀ = σ' v) ∧
          SamCoherent (execPath orig ss sam pc labels).2 σ₀ am₀ am' := by
  induction labels generalizing pc σ ss sam branchInfo am with
  | nil =>
    simp only [checkOrigPath, beq_iff_eq] at hpath
    simp only [execPath]
    exact ⟨σ, am, hpath ▸ Steps.refl, hrepr, hsamCoh⟩
  | cons nextPC rest ih =>
    unfold checkOrigPath at hpath
    -- Extract the instruction at pc
    generalize horig_opt : orig[pc]? = opt_instr at hpath
    cases opt_instr with
    | none => simp at hpath
    | some instr =>
      rw [Bool.and_eq_true] at hpath
      have ⟨h12, hpath_inner⟩ := hpath
      rw [Bool.and_eq_true] at h12
      have ⟨hnext_eq, halias_check⟩ := h12
      -- Extract computeNextPC result
      generalize hnext_opt : computeNextPC instr pc ss inv = opt_next at hnext_eq
      -- Construct the step + symbolic tracking (hrepr'/hinv at am₀, hsamCoh₁ for new am₁)
      have ⟨σ₁, am₁, hstep_orig, hrepr', hinv₁, hsamCoh₁, hsamTyped₁⟩ : ∃ σ₁ am₁,
          Step orig (Cfg.run pc σ am) (Cfg.run nextPC σ₁ am₁) ∧
          (∀ v, (ssGet (execSymbolic ss sam instr).1 v).eval σ₀ am₀ = σ₁ v) ∧
          EInv.toProp inv σ₀ am₀ ∧
          SamCoherent (execSymbolic ss sam instr).2 σ₀ am₀ am₁ ∧
          (∀ a i v, (a, i, v) ∈ (execSymbolic ss sam instr).2 → (v.eval σ₀ am₀).typeOf = arrayElemTy orig.arrayDecls a) := by
        cases opt_next with
        | some nextPC' =>
          have hpc_eq : nextPC = nextPC' := (beq_iff_eq.mp hnext_eq).symm
          subst hpc_eq
          cases instr with
          | const x n =>
            simp [computeNextPC] at hnext_opt
            rw [hnext_opt.symm]
            have hs : Step orig (.run pc σ am) (.run (pc + 1) (σ[x ↦ n]) am) := Step.const horig_opt
            cases n with
            | int k =>
              exact ⟨σ[x ↦ .int k], am, hs, (fun v => by
                simp only [execSymbolic]
                by_cases hvd : v = x
                · rw [hvd, ssGet_ssSet_same]; simp [Expr.eval, Store.update_self]
                · rw [ssGet_ssSet_other _ _ _ _ hvd, hrepr]
                  exact (Store.update_other σ x v _ hvd).symm), hinv, hsamCoh, hsamTyped⟩
            | bool b =>
              exact ⟨σ[x ↦ .bool b], am, hs, (fun v => by
                simp only [execSymbolic]
                by_cases hvd : v = x
                · rw [hvd, ssGet_ssSet_same]; simp [Expr.eval, Store.update_self]
                · rw [ssGet_ssSet_other _ _ _ _ hvd, hrepr]
                  exact (Store.update_other σ x v _ hvd).symm), hinv, hsamCoh, hsamTyped⟩
            | float f =>
              exact ⟨σ[x ↦ .float f], am, hs, (fun v => by
                simp only [execSymbolic]
                by_cases hvd : v = x
                · rw [hvd, ssGet_ssSet_same]; simp [Expr.eval, Store.update_self]
                · rw [ssGet_ssSet_other _ _ _ _ hvd, hrepr]
                  exact (Store.update_other σ x v _ hvd).symm), hinv, hsamCoh, hsamTyped⟩
          | copy x y =>
            simp [computeNextPC] at hnext_opt
            rw [hnext_opt.symm]
            have hs : Step orig (.run pc σ am) (.run (pc + 1) (σ[x ↦ σ y]) am) := Step.copy horig_opt
            exact ⟨σ[x ↦ σ y], am, hs, (fun v => by
              simp only [execSymbolic]
              by_cases hvd : v = x
              · rw [hvd, ssGet_ssSet_same, hrepr]; exact (Store.update_self σ x (σ y)).symm
              · rw [ssGet_ssSet_other _ _ _ _ hvd, hrepr]
                exact (Store.update_other σ x v _ hvd).symm), hinv, hsamCoh, hsamTyped⟩
          | binop x op y z =>
            simp [computeNextPC] at hnext_opt
            rw [hnext_opt.symm]
            have hpc_lt : pc < orig.size := bound_of_getElem? horig_opt
            have hwti := hwtp pc hpc_lt
            have hinstr_eq : orig[pc] = .binop x op y z :=
              Option.some.inj ((Array.getElem?_eq_getElem hpc_lt).symm.trans horig_opt)
            rw [hinstr_eq] at hwti
            obtain ⟨a, hya⟩ : ∃ a : BitVec 64, σ y = .int a := by
              cases hwti with | binop _ hy _ =>
              exact Value.int_of_typeOf_int (by rw [hts y]; exact hy)
            obtain ⟨b, hzb⟩ : ∃ b : BitVec 64, σ z = .int b := by
              cases hwti with | binop _ _ hz =>
              exact Value.int_of_typeOf_int (by rw [hts z]; exact hz)
            have hsafe : op.safe a b :=
              hDivSafe (List.cons_ne_nil _ _) x op y z a b horig_opt hya hzb
            have hs : Step orig (.run pc σ am) (.run (pc + 1) (σ[x ↦ .int (op.eval a b)]) am) :=
              Step.binop horig_opt hya hzb hsafe
            exact ⟨σ[x ↦ .int (op.eval a b)], am, hs, (fun v => by
              simp only [execSymbolic]
              by_cases hvd : v = x
              · rw [hvd, ssGet_ssSet_same]
                simp only [Expr.eval, Store.update_self]
                have ha : ((ssGet ss y).eval σ₀ am₀).toInt = a := by
                  rw [hrepr y, hya]; rfl
                have hb : ((ssGet ss z).eval σ₀ am₀).toInt = b := by
                  rw [hrepr z, hzb]; rfl
                rw [ha, hb]
              · rw [ssGet_ssSet_other _ _ _ _ hvd, hrepr]
                exact (Store.update_other σ x v _ hvd).symm), hinv, hsamCoh, hsamTyped⟩
          | boolop x be =>
            simp [computeNextPC] at hnext_opt
            rw [hnext_opt.symm]
            have hs : Step orig (.run pc σ am) (.run (pc + 1) (σ[x ↦ .bool (be.eval σ am)]) am) := Step.boolop horig_opt
            exact ⟨σ[x ↦ .bool (be.eval σ am)], am, hs, (fun v => by
              simp only [execSymbolic]
              by_cases hvd : v = x
              · rw [hvd, ssGet_ssSet_same]; simp only [Store.update_self]
                have hnoarr := (hBoolNoArr pc _ horig_opt).1 x be rfl
                rw [BoolExpr.toSymExpr_sound be ss σ₀ σ am₀ hrepr,
                    BoolExpr.eval_noArrRead be σ am₀ am hnoarr]
              · rw [ssGet_ssSet_other _ _ _ _ hvd, hrepr]
                exact (Store.update_other σ x v _ hvd).symm), hinv, hsamCoh, hsamTyped⟩
          | goto l =>
            simp [computeNextPC] at hnext_opt
            rw [hnext_opt.symm]
            have hs : Step orig (.run pc σ am) (.run l σ am) := Step.goto horig_opt
            exact ⟨σ, am, hs, (fun v => by simp only [execSymbolic]; exact hrepr v), hinv, hsamCoh, hsamTyped⟩
          | ifgoto b l =>
            have hexec_id : (execSymbolic ss sam (.ifgoto b l)).1 = ss := rfl
            simp only [computeNextPC] at hnext_opt
            cases hsym : b.symEval ss inv <;> simp [hsym] at hnext_opt
            case some r =>
              cases r with
              | true =>
                simp at hnext_opt
                have hpc_eq : nextPC = l := hnext_opt.symm
                rw [hpc_eq]
                have heval₀ := BoolExpr.symEval_sound b ss inv σ₀ σ am₀ hrepr hinv true hsym
                have hnoarr := (hBoolNoArr pc _ horig_opt).2 b l rfl
                have heval : b.eval σ am = true := by
                  rw [← BoolExpr.eval_noArrRead b σ am₀ am hnoarr]; exact heval₀
                exact ⟨σ, am, Step.iftrue horig_opt heval, hexec_id ▸ hrepr, hinv, hsamCoh, hsamTyped⟩
              | false =>
                simp at hnext_opt
                have hpc_eq : nextPC = pc + 1 := hnext_opt.symm
                rw [hpc_eq]
                have heval₀ := BoolExpr.symEval_sound b ss inv σ₀ σ am₀ hrepr hinv false hsym
                have hnoarr := (hBoolNoArr pc _ horig_opt).2 b l rfl
                have heval : b.eval σ am = false := by
                  rw [← BoolExpr.eval_noArrRead b σ am₀ am hnoarr]; exact heval₀
                exact ⟨σ, am, Step.iffall horig_opt heval, hexec_id ▸ hrepr, hinv, hsamCoh, hsamTyped⟩
          | halt =>
            simp [computeNextPC] at hnext_opt
          | arrLoad x arr idx ty =>
            simp [computeNextPC] at hnext_opt
            rw [hnext_opt.symm]
            have hpc_lt : pc < orig.size := bound_of_getElem? horig_opt
            have hwti := hwtp pc hpc_lt
            have hinstr_eq : orig[pc] = .arrLoad x arr idx ty :=
              Option.some.inj ((Array.getElem?_eq_getElem hpc_lt).symm.trans horig_opt)
            rw [hinstr_eq] at hwti
            obtain ⟨idxVal, hidxVal⟩ : ∃ idxVal : BitVec 64, σ idx = .int idxVal := by
              cases hwti with | arrLoad _ hidx _ =>
              exact Value.int_of_typeOf_int (by rw [hts idx]; exact hidx)
            have hbnd : idxVal < orig.arraySizeBv arr :=
              hOrigBounds (List.cons_ne_nil _ _) arr idx idxVal ty (Or.inl ⟨x, horig_opt⟩) hidxVal
            have hs : Step orig (.run pc σ am) (.run (pc + 1) (σ[x ↦ Value.ofBitVec ty (am.read arr idxVal)]) am) :=
              Step.arrLoad horig_opt hidxVal hbnd
            -- arrLoad: execSymbolic returns ssSet ss x (samGet sam arr (ssGet ss idx) ty)
            exact ⟨σ[x ↦ Value.ofBitVec ty (am.read arr idxVal)], am, hs, (fun v => by
              show (ssGet (ssSet ss x (samGet sam arr (ssGet ss idx) ty)) v).eval σ₀ am₀ = _
              by_cases hvx : v = x
              · rw [hvx, ssGet_ssSet_same]
                simp only [Store.update_self]
                have hety : ty = arrayElemTy orig.arrayDecls arr := by
                  cases hwti with | arrLoad _ _ h => exact h
                have hsc := samGet_sound sam σ₀ am₀ am hsamCoh arr (ssGet ss idx) ty
                  (checkInstrAliasOk_arrLoad_noalias ss sam inv x arr idx σ₀ am₀ hinv halias_check)
                  (fun a i v hmem harr _ => by rw [hsamTyped a i v hmem, harr, hety])
                rw [hsc]
                congr 1
                have hidx_eq := hrepr idx; rw [hidxVal] at hidx_eq
                rw [hidx_eq]; rfl
              · rw [ssGet_ssSet_other _ _ _ _ hvx]
                have hupd := Store.update_other σ x v (Value.ofBitVec ty (am.read arr idxVal)) hvx
                rw [hupd]; exact hrepr v), hinv, hsamCoh, hsamTyped⟩
          | arrStore arr idx val ty =>
            simp [computeNextPC] at hnext_opt
            rw [hnext_opt.symm]
            have hpc_lt : pc < orig.size := bound_of_getElem? horig_opt
            have hwti := hwtp pc hpc_lt
            have hinstr_eq : orig[pc] = .arrStore arr idx val ty :=
              Option.some.inj ((Array.getElem?_eq_getElem hpc_lt).symm.trans horig_opt)
            rw [hinstr_eq] at hwti
            obtain ⟨idxVal, hidxVal⟩ : ∃ idxVal : BitVec 64, σ idx = .int idxVal := by
              cases hwti with | arrStore hidx _ _ =>
              exact Value.int_of_typeOf_int (by rw [hts idx]; exact hidx)
            have hty : (σ val).typeOf = ty := by
              cases hwti with | arrStore _ hval _ =>
              rw [hts val]; exact hval
            have hety : ty = arrayElemTy orig.arrayDecls arr := by
              cases hwti with | arrStore _ _ h => exact h
            have hbnd : idxVal < orig.arraySizeBv arr :=
              hOrigBounds (List.cons_ne_nil _ _) arr idx idxVal ty (Or.inr ⟨val, horig_opt⟩) hidxVal
            have hs : Step orig (.run pc σ am) (.run (pc + 1) σ (am.write arr idxVal (σ val).toBits)) :=
              Step.arrStore horig_opt hidxVal hty hbnd
            -- arrStore: ss unchanged, σ unchanged. hrepr at am₀ transfers trivially.
            have hexec : (execSymbolic ss sam (.arrStore arr idx val ty)).1 = ss := rfl
            exact ⟨σ, am.write arr idxVal (σ val).toBits, hs,
              (fun v => by rw [hexec]; exact hrepr v), hinv,
              SamCoherent.cons arr (ssGet ss idx) (ssGet ss val) (σ val).toBits hsamCoh
                (by rw [hrepr val])
                (by congr 1
                    have hidx_eq := hrepr idx; rw [hidxVal] at hidx_eq
                    rw [hidx_eq]; rfl),
              fun a i v hmem => by
                simp [execSymbolic, List.mem_cons] at hmem
                rcases hmem with ⟨rfl, rfl, rfl⟩ | htl
                · rw [hrepr val, hty, hety]
                · exact hsamTyped a i v htl⟩
          | fbinop x fop y z =>
            simp [computeNextPC] at hnext_opt
            rw [hnext_opt.symm]
            have hpc_lt : pc < orig.size := bound_of_getElem? horig_opt
            have hwti := hwtp pc hpc_lt
            have hinstr_eq : orig[pc] = .fbinop x fop y z :=
              Option.some.inj ((Array.getElem?_eq_getElem hpc_lt).symm.trans horig_opt)
            rw [hinstr_eq] at hwti
            obtain ⟨fa, hfa⟩ : ∃ fa : BitVec 64, σ y = .float fa := by
              cases hwti with | fbinop _ hy _ =>
              exact Value.float_of_typeOf_float (by rw [hts y]; exact hy)
            obtain ⟨fb, hfb⟩ : ∃ fb : BitVec 64, σ z = .float fb := by
              cases hwti with | fbinop _ _ hz =>
              exact Value.float_of_typeOf_float (by rw [hts z]; exact hz)
            have hs : Step orig (.run pc σ am) (.run (pc + 1) (σ[x ↦ .float (fop.eval fa fb)]) am) :=
              Step.fbinop horig_opt hfa hfb
            exact ⟨σ[x ↦ .float (fop.eval fa fb)], am, hs, (fun v => by
              simp only [execSymbolic]
              by_cases hvd : v = x
              · rw [hvd, ssGet_ssSet_same]
                simp only [Expr.eval, Store.update_self]
                have ha : ((ssGet ss y).eval σ₀ am₀).toFloat = fa := by
                  rw [hrepr y, hfa]; rfl
                have hb : ((ssGet ss z).eval σ₀ am₀).toFloat = fb := by
                  rw [hrepr z, hfb]; rfl
                rw [ha, hb]
              · rw [ssGet_ssSet_other _ _ _ _ hvd, hrepr]
                exact (Store.update_other σ x v _ hvd).symm), hinv, hsamCoh, hsamTyped⟩
          | fternop x op y z w =>
            simp [computeNextPC] at hnext_opt
            rw [hnext_opt.symm]
            have hpc_lt : pc < orig.size := bound_of_getElem? horig_opt
            have hwti := hwtp pc hpc_lt
            have hinstr_eq : orig[pc] = .fternop x op y z w :=
              Option.some.inj ((Array.getElem?_eq_getElem hpc_lt).symm.trans horig_opt)
            rw [hinstr_eq] at hwti
            obtain ⟨fa, hfa⟩ : ∃ fa : BitVec 64, σ y = .float fa := by
              cases hwti with | fternop _ hy _ _ =>
              exact Value.float_of_typeOf_float (by rw [hts y]; exact hy)
            obtain ⟨fb, hfb⟩ : ∃ fb : BitVec 64, σ z = .float fb := by
              cases hwti with | fternop _ _ hz _ =>
              exact Value.float_of_typeOf_float (by rw [hts z]; exact hz)
            obtain ⟨fc, hfc⟩ : ∃ fc : BitVec 64, σ w = .float fc := by
              cases hwti with | fternop _ _ _ hw =>
              exact Value.float_of_typeOf_float (by rw [hts w]; exact hw)
            have hs : Step orig (.run pc σ am) (.run (pc + 1) (σ[x ↦ .float (FloatTernOp.eval op fa fb fc)]) am) :=
              Step.fternop horig_opt hfa hfb hfc
            exact ⟨σ[x ↦ .float (FloatTernOp.eval op fa fb fc)], am, hs, (fun v => by
              simp only [execSymbolic]
              by_cases hvd : v = x
              · rw [hvd, ssGet_ssSet_same]
                simp only [Expr.eval, Store.update_self]
                have ha : ((ssGet ss y).eval σ₀ am₀).toFloat = fa := by
                  rw [hrepr y, hfa]; rfl
                have hb : ((ssGet ss z).eval σ₀ am₀).toFloat = fb := by
                  rw [hrepr z, hfb]; rfl
                have hc : ((ssGet ss w).eval σ₀ am₀).toFloat = fc := by
                  rw [hrepr w, hfc]; rfl
                rw [ha, hb, hc]
              · rw [ssGet_ssSet_other _ _ _ _ hvd, hrepr]
                exact (Store.update_other σ x v _ hvd).symm), hinv, hsamCoh, hsamTyped⟩
          | intToFloat x y =>
            simp [computeNextPC] at hnext_opt
            rw [hnext_opt.symm]
            have hpc_lt : pc < orig.size := bound_of_getElem? horig_opt
            have hwti := hwtp pc hpc_lt
            have hinstr_eq : orig[pc] = .intToFloat x y :=
              Option.some.inj ((Array.getElem?_eq_getElem hpc_lt).symm.trans horig_opt)
            rw [hinstr_eq] at hwti
            obtain ⟨n, hn⟩ : ∃ n : BitVec 64, σ y = .int n := by
              cases hwti with | intToFloat _ hy =>
              exact Value.int_of_typeOf_int (by rw [hts y]; exact hy)
            have hs : Step orig (.run pc σ am) (.run (pc + 1) (σ[x ↦ .float (intToFloatBv n)]) am) :=
              Step.intToFloat horig_opt hn
            exact ⟨σ[x ↦ .float (intToFloatBv n)], am, hs, (fun v => by
              simp only [execSymbolic]
              by_cases hvd : v = x
              · rw [hvd, ssGet_ssSet_same]
                simp only [Expr.eval, Store.update_self]
                have hsrc : ((ssGet ss y).eval σ₀ am₀).toInt = n := by
                  rw [hrepr y, hn]; rfl
                rw [hsrc]
              · rw [ssGet_ssSet_other _ _ _ _ hvd, hrepr]
                exact (Store.update_other σ x v _ hvd).symm), hinv, hsamCoh, hsamTyped⟩
          | floatToInt x y =>
            simp [computeNextPC] at hnext_opt
            rw [hnext_opt.symm]
            have hpc_lt : pc < orig.size := bound_of_getElem? horig_opt
            have hwti := hwtp pc hpc_lt
            have hinstr_eq : orig[pc] = .floatToInt x y :=
              Option.some.inj ((Array.getElem?_eq_getElem hpc_lt).symm.trans horig_opt)
            rw [hinstr_eq] at hwti
            obtain ⟨f, hf⟩ : ∃ f : BitVec 64, σ y = .float f := by
              cases hwti with | floatToInt _ hy =>
              exact Value.float_of_typeOf_float (by rw [hts y]; exact hy)
            have hs : Step orig (.run pc σ am) (.run (pc + 1) (σ[x ↦ .int (floatToIntBv f)]) am) :=
              Step.floatToInt horig_opt hf
            exact ⟨σ[x ↦ .int (floatToIntBv f)], am, hs, (fun v => by
              simp only [execSymbolic]
              by_cases hvd : v = x
              · rw [hvd, ssGet_ssSet_same]
                simp only [Expr.eval, Store.update_self]
                have hsrc : ((ssGet ss y).eval σ₀ am₀).toFloat = f := by
                  rw [hrepr y, hf]; rfl
                rw [hsrc]
              · rw [ssGet_ssSet_other _ _ _ _ hvd, hrepr]
                exact (Store.update_other σ x v _ hvd).symm), hinv, hsamCoh, hsamTyped⟩
          | floatUnary x op y =>
            simp [computeNextPC] at hnext_opt
            rw [hnext_opt.symm]
            have hpc_lt : pc < orig.size := bound_of_getElem? horig_opt
            have hwti := hwtp pc hpc_lt
            have hinstr_eq : orig[pc] = .floatUnary x op y :=
              Option.some.inj ((Array.getElem?_eq_getElem hpc_lt).symm.trans horig_opt)
            rw [hinstr_eq] at hwti
            obtain ⟨f, hf⟩ : ∃ f : BitVec 64, σ y = .float f := by
              cases hwti with | floatUnary _ hy =>
              exact Value.float_of_typeOf_float (by rw [hts y]; exact hy)
            have hs : Step orig (.run pc σ am) (.run (pc + 1) (σ[x ↦ .float (op.eval f)]) am) :=
              Step.floatUnary horig_opt hf
            exact ⟨σ[x ↦ .float (op.eval f)], am, hs, (fun v => by
              simp only [execSymbolic]
              by_cases hvd : v = x
              · rw [hvd, ssGet_ssSet_same]
                simp only [Expr.eval, Store.update_self]
                have hsrc : ((ssGet ss y).eval σ₀ am₀).toFloat = f := by
                  rw [hrepr y, hf]; rfl
                rw [hsrc]
              · rw [ssGet_ssSet_other _ _ _ _ hvd, hrepr]
                exact (Store.update_other σ x v _ hvd).symm), hinv, hsamCoh, hsamTyped⟩
          | print _ _ =>
            simp [computeNextPC] at hnext_opt
            rw [hnext_opt.symm]
            exact ⟨σ, am, Step.print horig_opt,
              (fun v => by simp only [execSymbolic]; exact hrepr v),
              hinv, hsamCoh, hsamTyped⟩
          | printInt _ =>
            simp [computeNextPC] at hnext_opt
            rw [hnext_opt.symm]
            exact ⟨σ, am, Step.printInt horig_opt,
              (fun v => by simp only [execSymbolic]; exact hrepr v),
              hinv, hsamCoh, hsamTyped⟩
          | printBool _ =>
            simp [computeNextPC] at hnext_opt
            rw [hnext_opt.symm]
            exact ⟨σ, am, Step.printBool horig_opt,
              (fun v => by simp only [execSymbolic]; exact hrepr v),
              hinv, hsamCoh, hsamTyped⟩
          | printFloat _ =>
            simp [computeNextPC] at hnext_opt
            rw [hnext_opt.symm]
            exact ⟨σ, am, Step.printFloat horig_opt,
              (fun v => by simp only [execSymbolic]; exact hrepr v),
              hinv, hsamCoh, hsamTyped⟩
          | printString _ =>
            simp [computeNextPC] at hnext_opt
            rw [hnext_opt.symm]
            exact ⟨σ, am, Step.printString horig_opt,
              (fun v => by simp only [execSymbolic]; exact hrepr v),
              hinv, hsamCoh, hsamTyped⟩
        | none =>
          -- computeNextPC returned none; use branchInfo fallback
          cases hbi : branchInfo with
          | none =>
            exfalso; revert hnext_eq; rw [hbi]; simp
          | some bi =>
            obtain ⟨origCond, taken⟩ := bi
            cases instr with
            | ifgoto b l_orig =>
              have hexec_id : (execSymbolic ss sam (.ifgoto b l_orig)).1 = ss := rfl
              cases taken with
              | true =>
                have hfb : (b.normalize ss inv == origCond.normalize ss inv && nextPC == l_orig) = true := by
                  revert hnext_eq; rw [hbi]; simp
                have ⟨hbeq, hpc_eq⟩ := and_true_split hfb
                have hbnorm := beq_iff_eq.mp hbeq
                have hpc_eq := beq_iff_eq.mp hpc_eq; subst hpc_eq
                -- normalize preserves eval; derive b.eval σ = origCond.eval σ
                have hnoarr_b := (hBoolNoArr pc _ horig_opt).2 _ _ rfl
                have hnoarr_oc := hbranchNoArr origCond true hbi
                have heval : b.eval σ am = true := by
                  have hne := BoolExpr.normalize_eval b ss inv σ₀ σ am₀ am hrepr hinv hnoarr_b
                  have hne_oc := BoolExpr.normalize_eval origCond ss inv σ₀ σ am₀ am hrepr hinv hnoarr_oc
                  rw [← hne, hbnorm, hne_oc]
                  exact hbranch origCond true hbi
                exact ⟨σ, am, Step.iftrue horig_opt heval, hexec_id ▸ hrepr, hinv, hsamCoh, hsamTyped⟩
              | false =>
                have hfb : (b.normalize ss inv == origCond.normalize ss inv && nextPC == pc + 1) = true := by
                  revert hnext_eq; rw [hbi]; simp
                have ⟨hbeq, hpc_eq⟩ := and_true_split hfb
                have hbnorm := beq_iff_eq.mp hbeq
                have hpc_eq := beq_iff_eq.mp hpc_eq; subst hpc_eq
                have hnoarr_b := (hBoolNoArr pc _ horig_opt).2 _ _ rfl
                have hnoarr_oc := hbranchNoArr origCond false hbi
                have heval : b.eval σ am = false := by
                  have hne := BoolExpr.normalize_eval b ss inv σ₀ σ am₀ am hrepr hinv hnoarr_b
                  have hne_oc := BoolExpr.normalize_eval origCond ss inv σ₀ σ am₀ am hrepr hinv hnoarr_oc
                  rw [← hne, hbnorm, hne_oc]
                  exact hbranch origCond false hbi
                exact ⟨σ, am, Step.iffall horig_opt heval, hexec_id ▸ hrepr, hinv, hsamCoh, hsamTyped⟩
            | _ =>
              exfalso; revert hnext_eq; rw [hbi]; cases taken <;> simp
      -- Recursive step (branchInfo = none for rest)
      have hexec : ∀ v, ssGet (execPath orig ss sam pc (nextPC :: rest)).1 v =
          ssGet (execPath orig (execSymbolic ss sam instr).1 (execSymbolic ss sam instr).2 nextPC rest).1 v := by
        intro v; simp [execPath, horig_opt]
      have hts₁ : TypedStore Γ σ₁ :=
        type_preservation hwtp hts (bound_of_getElem? horig_opt) hstep_orig
      -- Derive hOrigBounds₁ for the IH at nextPC:
      -- When rest = [], the condition rest ≠ [] is false, so hOrigBounds₁ is vacuously true.
      -- When rest ≠ [], nextPC ∈ (nextPC :: rest).dropLast, so hRestScalar says
      -- the instruction at nextPC is scalar, contradicting any arrLoad/arrStore hypothesis.
      have hOrigBounds₁ : rest ≠ [] → ∀ arr idx (idxVal : BitVec 64) ty,
          ((∃ x, orig[nextPC]? = some (.arrLoad x arr idx ty)) ∨
           (∃ val, orig[nextPC]? = some (.arrStore arr idx val ty))) →
          σ₁ idx = .int idxVal → idxVal < orig.arraySizeBv arr := by
        intro hne arr idx idxVal ty hinstr_arr hidxVal
        -- nextPC is in (nextPC :: rest).dropLast since rest ≠ []
        have hmem : nextPC ∈ (nextPC :: rest).dropLast := by
          cases rest with
          | nil => exact absurd rfl hne
          | cons h t => simp [List.dropLast]
        have hscalar := hRestScalar nextPC hmem
        -- The instruction at nextPC is scalar, contradicting arrLoad/arrStore
        cases hinstr_arr with
        | inl h => obtain ⟨x, hload⟩ := h; exact absurd (hscalar _ hload) (by simp [TAC.isScalar])
        | inr h => obtain ⟨val, hstore⟩ := h; exact absurd (hscalar _ hstore) (by simp [TAC.isScalar])
      -- Derive hRestScalar₁ : ∀ l ∈ rest.dropLast, ...
      have hRestScalar₁ : ∀ l ∈ rest.dropLast, ∀ instr, orig[l]? = some instr → instr.isScalar = true := by
        intro l hmem
        cases rest with
        | nil => simp [List.dropLast] at hmem
        | cons h t =>
          -- (nextPC :: h :: t).dropLast = nextPC :: (h :: t).dropLast
          have hdr : (nextPC :: h :: t).dropLast = nextPC :: (h :: t).dropLast := by
            simp [List.dropLast]
          exact hRestScalar l (hdr ▸ List.mem_cons_of_mem _ hmem)
      -- Derive hDivSafe₁ for the recursive call: intermediate labels can't be div/mod
      have hDivSafe₁ : rest ≠ [] → ∀ x (op : BinOp) y z (a b : BitVec 64),
          orig[nextPC]? = some (.binop x op y z) →
          σ₁ y = .int a → σ₁ z = .int b → op.safe a b := by
        intro hne x_l op_l y_l z_l a_l b_l horig_l _hy_l _hz_l
        have hmem : nextPC ∈ (nextPC :: rest).dropLast := by
          cases rest with
          | nil => exact absurd rfl hne
          | cons _ _ => simp [List.dropLast]
        have ⟨hnd, hnm⟩ := hRestNoDivMod nextPC hmem x_l y_l z_l
        cases op_l with
        | add | sub | mul | band | bor | bxor | shl | shr => exact True.intro
        | div => exact absurd horig_l hnd
        | mod => exact absurd horig_l hnm
      -- Derive hRestNoDivMod₁ for the recursive call
      have hRestNoDivMod₁ : ∀ l ∈ rest.dropLast, ∀ x y z,
          orig[l]? ≠ some (.binop x .div y z) ∧ orig[l]? ≠ some (.binop x .mod y z) := by
        intro l hmem
        cases rest with
        | nil => simp [List.dropLast] at hmem
        | cons h t =>
          have hdr : (nextPC :: h :: t).dropLast = nextPC :: (h :: t).dropLast := by
            simp [List.dropLast]
          exact hRestNoDivMod l (hdr ▸ List.mem_cons_of_mem _ hmem)
      obtain ⟨σ', am', hsteps_rest, hrepr_final, hsamCoh'⟩ :=
        ih (execSymbolic ss sam instr).1 (execSymbolic ss sam instr).2 σ₁ nextPC none am₁ hts₁ hrepr'
          hsamCoh₁ hsamTyped₁ hpath_inner (fun _ _ h => by simp at h)
          (fun _ _ h => by simp at h)
          hOrigBounds₁ hRestScalar₁
          hDivSafe₁ hRestNoDivMod₁
      have hexec_sam : (execPath orig ss sam pc (nextPC :: rest)).2 =
          (execPath orig (execSymbolic ss sam instr).1 (execSymbolic ss sam instr).2 nextPC rest).2 := by
        simp [execPath, horig_opt]
      refine ⟨σ', am', Steps.step hstep_orig hsteps_rest, fun v => ?_, hexec_sam ▸ hsamCoh'⟩
      rw [hexec v]; exact hrepr_final v

/-- Path execution soundness: specialization with empty initial symbolic store.
    With empty ss/sam and am₀ = am, the conclusion evaluates at the initial am. -/
private theorem execPath_sound (orig : Prog) (inv : EInv) (σ : Store)
    (pc : Label) (labels : List Label) (pc' : Label)
    (branchInfo : Option (BoolExpr × Bool))
    (am : ArrayMem)
    (Γ : TyCtx) (hwtp : WellTypedProg Γ orig) (hts : TypedStore Γ σ)
    (hrepr : ∀ v, (ssGet ([] : SymStore) v).eval σ am = σ v)
    (hinv : EInv.toProp inv σ am)
    (hInvNoArrRead : inv.all (fun (_, e) => !e.hasArrRead) = true)
    (hpath : checkOrigPath orig ([] : SymStore) ([] : SymArrayMem) inv pc labels pc' branchInfo = true)
    (hbranch : ∀ cond taken, branchInfo = some (cond, taken) →
        cond.eval σ am = taken)
    (hbranchNoArr : ∀ cond taken, branchInfo = some (cond, taken) →
        cond.hasArrRead = false)
    (hOrigBounds : labels ≠ [] → ∀ arr idx (idxVal : BitVec 64) ty,
        ((∃ x, orig[pc]? = some (.arrLoad x arr idx ty)) ∨
         (∃ val, orig[pc]? = some (.arrStore arr idx val ty))) →
        σ idx = .int idxVal → idxVal < orig.arraySizeBv arr)
    (hRestScalar : ∀ l ∈ labels.dropLast, ∀ instr, orig[l]? = some instr → instr.isScalar = true)
    (hDivSafe : labels ≠ [] → ∀ x (op : BinOp) y z (a b : BitVec 64),
        orig[pc]? = some (.binop x op y z) →
        σ y = .int a → σ z = .int b → op.safe a b)
    (hRestNoDivMod : ∀ l ∈ labels.dropLast, ∀ x y z,
        orig[l]? ≠ some (.binop x .div y z) ∧ orig[l]? ≠ some (.binop x .mod y z))
    (hBoolNoArr : ∀ (pc' : Nat) instr, orig[pc']? = some instr →
        (∀ x be, instr = TAC.boolop x be → be.hasArrRead = false) ∧
        (∀ b l, instr = TAC.ifgoto b l → b.hasArrRead = false)) :
    ∃ σ' am', Steps orig (Cfg.run pc σ am) (Cfg.run pc' σ' am') ∧
          (∀ v, (ssGet (execPath orig ([] : SymStore) ([] : SymArrayMem) pc labels).1 v).eval σ am = σ' v) ∧
          SamCoherent (execPath orig ([] : SymStore) ([] : SymArrayMem) pc labels).2 σ am am' :=
  execPath_sound_gen orig ([] : SymStore) ([] : SymArrayMem) inv σ σ pc labels pc' branchInfo am am
    Γ hwtp hts hrepr hinv (samCoherent_nil σ am) (fun _ _ _ h => by simp at h)
    hInvNoArrRead hpath hbranch hbranchNoArr hOrigBounds hRestScalar hDivSafe hRestNoDivMod hBoolNoArr

/-- If the store relation holds (∀ x, σ_t x = (ssGet ss x).eval σ_o), then evaluating
    `e` at `σ_t` equals evaluating `e.substSym ss` at `σ_o`. Follows from `substSym_sound`. -/
theorem Expr.substSym_consistent (ss : SymStore) (e : Expr) (σ_o σ_t : Store) (am : ArrayMem)
    (hcons : ∀ x, σ_t x = (ssGet ss x).eval σ_o am) :
    e.eval σ_t am = (e.substSym ss).eval σ_o am :=
  (Expr.substSym_sound ss e σ_o σ_t am (fun v => (hcons v).symm)).symm

/-- BEq on Expr implies equality. -/
private theorem expr_beq_eq {e₁ e₂ : Expr} (h : (e₁ == e₂) = true) : e₁ = e₂ :=
  beq_iff_eq.mp h

/-- Array.getD on empty array returns the default. -/
private theorem Array_getD_empty {α : Type} (n : Nat) (d : α) :
    Array.getD #[] n d = d := by
  simp [Array.getD]

/-- `relGetOrigExpr` and `ssGet (buildSubstMap ...)` agree: both find the first
    pair `(e_o, .var x)` in `rel` and return `e_o`, or default to `.var x`. -/
private theorem relGetOrigExpr_eq_ssGet_buildSubstMap (rel : EExprRel) (x : Var) :
    relGetOrigExpr rel x = ssGet (buildSubstMap rel) x := by
  induction rel with
  | nil => simp [relGetOrigExpr, buildSubstMap, ssGet, List.find?, List.filterMap]
  | cons p rest ih =>
    obtain ⟨e_o, e_t⟩ := p
    cases e_t with
    | var w =>
      simp only [relGetOrigExpr, List.find?, buildSubstMap, List.filterMap, ssGet]
      by_cases hwx : w = x
      · subst hwx
        simp [BEq.beq]
      · have hbeq_expr : (Expr.var w == Expr.var x) = false := by
          rw [beq_eq_false_iff_ne]; intro h; exact hwx (Expr.var.inj h)
        have hbeq_var : (w == x) = false := beq_eq_false_iff_ne.mpr hwx
        simp only [hbeq_expr, hbeq_var]
        exact ih
    | lit n =>
      have hbeq : (Expr.lit n == Expr.var x) = false := by
        rw [beq_eq_false_iff_ne]; exact Expr.noConfusion
      simp only [relGetOrigExpr, List.find?, buildSubstMap, List.filterMap, hbeq]
      exact ih
    | blit b =>
      have hbeq : (Expr.blit b == Expr.var x) = false := by
        rw [beq_eq_false_iff_ne]; exact Expr.noConfusion
      simp only [relGetOrigExpr, List.find?, buildSubstMap, List.filterMap, hbeq]
      exact ih
    | bin op a b =>
      have hbeq : (Expr.bin op a b == Expr.var x) = false := by
        rw [beq_eq_false_iff_ne]; exact Expr.noConfusion
      simp only [relGetOrigExpr, List.find?, buildSubstMap, List.filterMap, hbeq]
      exact ih
    | tobool e =>
      have hbeq : (Expr.tobool e == Expr.var x) = false := by
        rw [beq_eq_false_iff_ne]; exact Expr.noConfusion
      simp only [relGetOrigExpr, List.find?, buildSubstMap, List.filterMap, hbeq]
      exact ih
    | cmpE op a b =>
      have hbeq : (Expr.cmpE op a b == Expr.var x) = false := by
        rw [beq_eq_false_iff_ne]; exact Expr.noConfusion
      simp only [relGetOrigExpr, List.find?, buildSubstMap, List.filterMap, hbeq]
      exact ih
    | cmpLitE op a n =>
      have hbeq : (Expr.cmpLitE op a n == Expr.var x) = false := by
        rw [beq_eq_false_iff_ne]; exact Expr.noConfusion
      simp only [relGetOrigExpr, List.find?, buildSubstMap, List.filterMap, hbeq]
      exact ih
    | notE e =>
      have hbeq : (Expr.notE e == Expr.var x) = false := by
        rw [beq_eq_false_iff_ne]; exact Expr.noConfusion
      simp only [relGetOrigExpr, List.find?, buildSubstMap, List.filterMap, hbeq]
      exact ih
    | andE a b =>
      have hbeq : (Expr.andE a b == Expr.var x) = false := by
        rw [beq_eq_false_iff_ne]; exact Expr.noConfusion
      simp only [relGetOrigExpr, List.find?, buildSubstMap, List.filterMap, hbeq]
      exact ih
    | orE a b =>
      have hbeq : (Expr.orE a b == Expr.var x) = false := by
        rw [beq_eq_false_iff_ne]; exact Expr.noConfusion
      simp only [relGetOrigExpr, List.find?, buildSubstMap, List.filterMap, hbeq]
      exact ih
    | arrRead arr idx =>
      have hbeq : (Expr.arrRead arr idx == Expr.var x) = false := by
        rw [beq_eq_false_iff_ne]; exact Expr.noConfusion
      simp only [relGetOrigExpr, List.find?, buildSubstMap, List.filterMap, hbeq]
      exact ih
    | flit n =>
      have hbeq : (Expr.flit n == Expr.var x) = false := by
        rw [beq_eq_false_iff_ne]; exact Expr.noConfusion
      simp only [relGetOrigExpr, List.find?, buildSubstMap, List.filterMap, hbeq]
      exact ih
    | fbin op a b =>
      have hbeq : (Expr.fbin op a b == Expr.var x) = false := by
        rw [beq_eq_false_iff_ne]; exact Expr.noConfusion
      simp only [relGetOrigExpr, List.find?, buildSubstMap, List.filterMap, hbeq]
      exact ih
    | fcmpE op a b =>
      have hbeq : (Expr.fcmpE op a b == Expr.var x) = false := by
        rw [beq_eq_false_iff_ne]; exact Expr.noConfusion
      simp only [relGetOrigExpr, List.find?, buildSubstMap, List.filterMap, hbeq]
      exact ih
    | intToFloat e =>
      have hbeq : (Expr.intToFloat e == Expr.var x) = false := by
        rw [beq_eq_false_iff_ne]; exact Expr.noConfusion
      simp only [relGetOrigExpr, List.find?, buildSubstMap, List.filterMap, hbeq]
      exact ih
    | floatToInt e =>
      have hbeq : (Expr.floatToInt e == Expr.var x) = false := by
        rw [beq_eq_false_iff_ne]; exact Expr.noConfusion
      simp only [relGetOrigExpr, List.find?, buildSubstMap, List.filterMap, hbeq]
      exact ih
    | floatUnary op e =>
      have hbeq : (Expr.floatUnary op e == Expr.var x) = false := by
        rw [beq_eq_false_iff_ne]; exact Expr.noConfusion
      simp only [relGetOrigExpr, List.find?, buildSubstMap, List.filterMap, hbeq]
      exact ih
    | ftern op a b c =>
      have hbeq : (Expr.ftern op a b c == Expr.var x) = false := by
        rw [beq_eq_false_iff_ne]; exact Expr.noConfusion
      simp only [relGetOrigExpr, List.find?, buildSubstMap, List.filterMap, hbeq]
      exact ih
    | farrRead arr idx =>
      have hbeq : (Expr.farrRead arr idx == Expr.var x) = false := by
        rw [beq_eq_false_iff_ne]; exact Expr.noConfusion
      simp only [relGetOrigExpr, List.find?, buildSubstMap, List.filterMap, hbeq]
      exact ih

/-- If `relFindOrigVar rel x = some x'`, then `(.var x', .var x) ∈ rel`. -/
private theorem relFindOrigVar_mem {rel : EExprRel} {x x' : Var}
    (h : relFindOrigVar rel x = some x') :
    (.var x', .var x) ∈ rel := by
  simp only [relFindOrigVar] at h
  induction rel with
  | nil => simp [List.find?] at h
  | cons p rest ih =>
    simp only [List.find?] at h
    by_cases hp : p.2 == .var x
    · simp [hp] at h
      obtain ⟨e_o, e_t⟩ := p
      simp at hp; subst hp
      cases e_o with
      | var v => simp at h; subst h; exact List.Mem.head _
      | _ => simp at h
    · simp [hp] at h; exact List.Mem.tail _ (ih h)

/-- If `relFindOrigExpr rel x = some e`, then `(e, .var x) ∈ rel`. -/
private theorem relFindOrigExpr_mem {rel : EExprRel} {x : Var} {e : Expr}
    (h : relFindOrigExpr rel x = some e) :
    (e, .var x) ∈ rel := by
  simp only [relFindOrigExpr] at h
  induction rel with
  | nil => simp [List.find?] at h
  | cons p rest ih =>
    simp only [List.find?] at h
    by_cases hp : p.2 == .var x
    · simp [hp] at h
      obtain ⟨e_o, e_t⟩ := p
      simp at hp; subst hp
      simp at h; subst h; exact List.Mem.head _
    · simp [hp] at h; exact List.Mem.tail _ (ih h)

/-- Helper: `relFindOrigVar` result implies `σ_t v = σ_o v'` from the store relation. -/
private theorem store_eq_of_relFindOrigVar {rel : EExprRel} {v v' : Var}
    {σ_t σ_o : Store} {am : ArrayMem}
    (hfind : relFindOrigVar rel v = some v')
    (hcons : ∀ e_o w, (e_o, .var w) ∈ rel → σ_t w = e_o.eval σ_o am) :
    σ_t v = σ_o v' := by
  have hmem := relFindOrigVar_mem hfind
  rw [hcons (.var v') v hmem]; simp [Expr.eval]


/-- Branch direction info from the transformed program's ifgoto instruction.
    For `ifgoto b l` with `l ≠ pc + 1`, returns `some (b, pc' == l)` indicating
    the condition and whether the branch was taken. -/
@[reducible] private def transBranchInfo (instr : TAC) (pc_t pc_t' : Label) : Option (BoolExpr × Bool) :=
  match instr with
  | .ifgoto b l => if !(l == pc_t + 1) then some (b, pc_t' == l) else none
  | _ => none

/-- Compute branchInfo from an instruction and an expression relation.
    Maps the condition's variables through the relation. -/
@[reducible] private def branchInfoWithRel (instr : TAC) (rel : EExprRel) (pc_t pc_t' : Label)
    : Option (BoolExpr × Bool) :=
  match instr with
  | .ifgoto b l =>
    match b.mapVarsRel rel with
    | some origCond => if !(l == pc_t + 1) then some (origCond, pc_t' == l) else none
    | none => none
  | _ => none


/-- When `transBranchInfo` returns `some (cond, taken)`,
    we can derive `cond.eval σ = taken` from any step. -/
private theorem branchInfo_of_step {prog : Prog} {pc pc' : Label} {σ σ' : Store} {am am' : ArrayMem}
    {instr : TAC} (hinstr : prog[pc]? = some instr)
    (hstep : Step prog (Cfg.run pc σ am) (Cfg.run pc' σ' am'))
    {cond : BoolExpr} {taken : Bool}
    (hbi : transBranchInfo instr pc pc' = some (cond, taken)) :
    cond.eval σ am = taken := by
  cases instr with
  | ifgoto b l =>
    simp only [transBranchInfo] at hbi
    by_cases hguard : (!(l == pc + 1))
    · simp only [hguard, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hbi
      obtain ⟨rfl, rfl⟩ := hbi
      -- cond = b, taken = (pc' == l)
      cases hstep with
      | iftrue h heval =>
        have heq := Option.some.inj (hinstr.symm.trans h)
        simp only [TAC.ifgoto.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        simp [heval]
      | iffall h heval =>
        have heq := Option.some.inj (hinstr.symm.trans h)
        simp only [TAC.ifgoto.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        have : ¬(l = pc + 1) := by simpa using hguard
        have : ¬(pc + 1 = l) := fun h => this h.symm
        simp [beq_eq_false_iff_ne.mpr this, heval]
      | const h => exact absurd (hinstr.symm.trans h) (by simp)
      | copy h => exact absurd (hinstr.symm.trans h) (by simp)
      | binop h => exact absurd (hinstr.symm.trans h) (by simp)
      | boolop h => exact absurd (hinstr.symm.trans h) (by simp)
      | goto h => exact absurd (hinstr.symm.trans h) (by simp)
      | arrLoad h _ _ => exact absurd (hinstr.symm.trans h) (by simp)
      | arrStore h _ _ _ => exact absurd (hinstr.symm.trans h) (by simp)
      | fbinop h _ _ => exact absurd (hinstr.symm.trans h) (by simp)
      | fternop h _ _ _ => exact absurd (hinstr.symm.trans h) (by simp)
      | intToFloat h _ => exact absurd (hinstr.symm.trans h) (by simp)
      | floatToInt h _ => exact absurd (hinstr.symm.trans h) (by simp)
      | floatUnary h _ => exact absurd (hinstr.symm.trans h) (by simp)
      | print h => exact absurd (hinstr.symm.trans h) (by simp)
      | printInt h => exact absurd (hinstr.symm.trans h) (by simp)
      | printBool h => exact absurd (hinstr.symm.trans h) (by simp)
      | printFloat h => exact absurd (hinstr.symm.trans h) (by simp)
      | printString h => exact absurd (hinstr.symm.trans h) (by simp)
    · simp [hguard] at hbi
  | _ => simp [transBranchInfo] at hbi

/-- Soundness of `checkBoolVarsCoveredExec`: for each ifgoto in the transformed program,
    every free variable in the BoolExpr operands has a pair in the relation. -/
private theorem checkBoolVarsCoveredExec_sound (cert : ECertificate)
    (h : checkBoolVarsCoveredExec cert = true)
    (pc : Nat) (b : BoolExpr) (l : Label)
    (hinstr : cert.trans[pc]? = some (.ifgoto b l)) :
    ∀ v, v ∈ b.exprFreeVars → ∃ e_o, (e_o, .var v) ∈ (cert.instrCerts.getD pc default).rel := by
  intro v hv
  unfold checkBoolVarsCoveredExec at h
  have hbound : pc < cert.trans.code.size := bound_of_getElem? hinstr
  rw [List.all_eq_true] at h
  have hall := h pc (List.mem_range.mpr hbound)
  simp only [Prog.getElem?_code] at hinstr
  have hget : cert.trans.code[pc] = .ifgoto b l :=
    Option.some.inj ((Array.getElem?_eq_getElem hbound).symm.trans hinstr)
  -- Rewrite the match in hall with the concrete instruction and instrCerts lookup
  rw [Array.getElem?_eq_getElem hbound, hget] at hall
  -- Now hall matches on `(some (.ifgoto b l), cert.instrCerts[pc]?)`
  cases hic : cert.instrCerts[pc]? with
  | none => rw [hic] at hall; simp at hall
  | some ic =>
    rw [hic] at hall
    simp (config := { decide := false }) only [] at hall
    rw [List.all_eq_true] at hall
    have hfv := hall v hv
    rw [List.any_eq_true] at hfv
    obtain ⟨⟨e_o, e_t⟩, hmem, hbeq⟩ := hfv
    have htv : e_t = .var v := beq_iff_eq.mp hbeq
    subst htv
    have hpc_bound : pc < cert.instrCerts.size := by
      rw [Array.getElem?_eq_some_iff] at hic; exact hic.1
    have hgetD : cert.instrCerts.getD pc default = ic := by
      simp only [Array.getD, hpc_bound, ↓reduceDIte]
      exact Option.some.inj (Array.getElem?_eq_getElem hpc_bound ▸ hic)
    rw [hgetD]
    exact ⟨e_o, hmem⟩

/-- ssGet from an arrRead-free SymStore returns arrRead-free expressions. -/
private theorem ssGet_noArrRead_of_all (ss : SymStore) (v : Var)
    (hall : ss.all (fun (_, e) => !e.hasArrRead) = true) :
    (ssGet ss v).hasArrRead = false := by
  unfold ssGet
  generalize hfind : ss.find? (fun p => p.1 == v) = result
  cases result with
  | none => simp [Expr.hasArrRead]
  | some entry =>
    have hmem : entry ∈ ss := List.mem_of_find?_eq_some hfind
    rw [List.all_eq_true] at hall
    have h := hall entry hmem; simp at h; exact h

/-- buildSubstMap preserves arrRead-freeness from the original-side expressions. -/
private theorem buildSubstMap_noArrRead (rel : EExprRel)
    (hnoarr : rel.all (fun (e, _) => !e.hasArrRead) = true) :
    (buildSubstMap rel).all (fun (_, e) => !e.hasArrRead) = true := by
  rw [List.all_eq_true]; intro ⟨w, e⟩ hmem
  simp only [buildSubstMap, List.mem_filterMap] at hmem
  obtain ⟨⟨e_o, e_t⟩, hmem_rel, hsome⟩ := hmem
  rw [List.all_eq_true] at hnoarr
  cases e_t with
  | var x => simp at hsome; obtain ⟨rfl, rfl⟩ := hsome; exact hnoarr _ hmem_rel
  | _ => simp at hsome

/-- If all original-side expressions in a relation are arrRead-free,
    then ssGet of the corresponding buildSubstMap is arrRead-free for any variable. -/
private theorem ssGet_buildSubstMap_noArrRead (rel : EExprRel) (v : Var)
    (hnoarr : rel.all (fun (e, _) => !e.hasArrRead) = true) :
    (ssGet (buildSubstMap rel) v).hasArrRead = false :=
  ssGet_noArrRead_of_all _ v (buildSubstMap_noArrRead rel hnoarr)


/-- substSym preserves arrRead-freeness: if the expression and all SymStore entries
    are arrRead-free, so is the substituted expression. -/
private theorem Expr.substSym_noArrRead (e : Expr) (ss : SymStore)
    (he : e.hasArrRead = false)
    (hss : ss.all (fun (_, e) => !e.hasArrRead) = true) :
    (e.substSym ss).hasArrRead = false := by
  induction e with
  | lit _ | blit _ | flit _ => simp [Expr.substSym, Expr.hasArrRead]
  | var v => simp only [Expr.substSym]; exact ssGet_noArrRead_of_all ss v hss
  | bin _ a b iha ihb =>
    simp only [Expr.hasArrRead, Bool.or_eq_false_iff] at he
    simp only [Expr.substSym, Expr.hasArrRead, Bool.or_eq_false_iff]
    exact ⟨iha he.1, ihb he.2⟩
  | tobool e ih =>
    simp only [Expr.hasArrRead] at he; simp only [Expr.substSym, Expr.hasArrRead]; exact ih he
  | cmpE _ a b iha ihb =>
    simp only [Expr.hasArrRead, Bool.or_eq_false_iff] at he
    simp only [Expr.substSym, Expr.hasArrRead, Bool.or_eq_false_iff]
    exact ⟨iha he.1, ihb he.2⟩
  | cmpLitE _ a _ ih =>
    simp only [Expr.hasArrRead] at he; simp only [Expr.substSym, Expr.hasArrRead]; exact ih he
  | notE e ih =>
    simp only [Expr.hasArrRead] at he; simp only [Expr.substSym, Expr.hasArrRead]; exact ih he
  | andE a b iha ihb =>
    simp only [Expr.hasArrRead, Bool.or_eq_false_iff] at he
    simp only [Expr.substSym, Expr.hasArrRead, Bool.or_eq_false_iff]
    exact ⟨iha he.1, ihb he.2⟩
  | orE a b iha ihb =>
    simp only [Expr.hasArrRead, Bool.or_eq_false_iff] at he
    simp only [Expr.substSym, Expr.hasArrRead, Bool.or_eq_false_iff]
    exact ⟨iha he.1, ihb he.2⟩
  | arrRead _ _ => simp [Expr.hasArrRead] at he
  | fbin _ a b iha ihb =>
    simp only [Expr.hasArrRead, Bool.or_eq_false_iff] at he
    simp only [Expr.substSym, Expr.hasArrRead, Bool.or_eq_false_iff]
    exact ⟨iha he.1, ihb he.2⟩
  | fcmpE _ a b iha ihb =>
    simp only [Expr.hasArrRead, Bool.or_eq_false_iff] at he
    simp only [Expr.substSym, Expr.hasArrRead, Bool.or_eq_false_iff]
    exact ⟨iha he.1, ihb he.2⟩
  | intToFloat e ih =>
    simp only [Expr.hasArrRead] at he; simp only [Expr.substSym, Expr.hasArrRead]; exact ih he
  | floatToInt e ih =>
    simp only [Expr.hasArrRead] at he; simp only [Expr.substSym, Expr.hasArrRead]; exact ih he
  | floatUnary _ e ih =>
    simp only [Expr.hasArrRead] at he; simp only [Expr.substSym, Expr.hasArrRead]; exact ih he
  | ftern _ a b c iha ihb ihc =>
    simp only [Expr.hasArrRead, Bool.or_eq_false_iff] at he
    simp only [Expr.substSym, Expr.hasArrRead, Bool.or_eq_false_iff]
    exact ⟨⟨iha he.1.1, ihb he.1.2⟩, ihc he.2⟩
  | farrRead _ _ => simp [Expr.hasArrRead] at he

/-- mapVarsRel preserves arrRead-freeness when the BoolExpr and relation are arrRead-free. -/
private theorem mapVarsRel_noArrRead (b : BoolExpr) (rel : EExprRel) (origCond : BoolExpr)
    (hmap : b.mapVarsRel rel = some origCond)
    (hb : b.hasArrRead = false)
    (hrel : rel.all (fun (e, _) => !e.hasArrRead) = true) :
    origCond.hasArrRead = false := by
  cases b with
  | lit b_val => simp [BoolExpr.mapVarsRel] at hmap; subst hmap; simp [BoolExpr.hasArrRead]
  | bvar x =>
    simp only [BoolExpr.mapVarsRel, bind, Option.bind] at hmap
    split at hmap <;> simp at hmap
    rename_i e _
    split at hmap <;> simp at hmap
    subst hmap; simp [BoolExpr.hasArrRead]
  | cmp op a b_e =>
    simp only [BoolExpr.hasArrRead, Bool.or_eq_false_iff] at hb
    simp only [BoolExpr.mapVarsRel] at hmap; cases hmap
    simp only [BoolExpr.hasArrRead, Bool.or_eq_false_iff]
    have hss := buildSubstMap_noArrRead rel hrel
    rw [Expr.substSym'_eq_substSym, Expr.substSym'_eq_substSym]
    exact ⟨Expr.substSym_noArrRead a _ hb.1 hss, Expr.substSym_noArrRead b_e _ hb.2 hss⟩
  | not e =>
    simp only [BoolExpr.hasArrRead] at hb
    simp only [BoolExpr.mapVarsRel, Option.map] at hmap
    cases hm : e.mapVarsRel rel with
    | none => simp [hm] at hmap
    | some e' =>
      simp [hm] at hmap
      have ih := mapVarsRel_noArrRead e rel e' hm hb hrel
      match e' with
      | .not inner => cases hmap; exact ih
      | .lit _ => cases hmap; simp [BoolExpr.hasArrRead]
      | .bvar _ => cases hmap; exact ih
      | .cmp _ _ _ => cases hmap; simp only [BoolExpr.hasArrRead]; exact ih
      | .fcmp _ _ _ => cases hmap; simp only [BoolExpr.hasArrRead]; exact ih
      | .bexpr _ => cases hmap; simp only [BoolExpr.hasArrRead]; exact ih
  | fcmp op a b_e =>
    simp only [BoolExpr.hasArrRead, Bool.or_eq_false_iff] at hb
    simp only [BoolExpr.mapVarsRel] at hmap; cases hmap
    simp only [BoolExpr.hasArrRead, Bool.or_eq_false_iff]
    have hss := buildSubstMap_noArrRead rel hrel
    rw [Expr.substSym'_eq_substSym, Expr.substSym'_eq_substSym]
    exact ⟨Expr.substSym_noArrRead a _ hb.1 hss, Expr.substSym_noArrRead b_e _ hb.2 hss⟩
  | bexpr e =>
    simp only [BoolExpr.hasArrRead] at hb
    simp only [BoolExpr.mapVarsRel] at hmap; cases hmap
    simp only [BoolExpr.hasArrRead]
    have hss := buildSubstMap_noArrRead rel hrel
    rw [Expr.substSym'_eq_substSym]
    exact Expr.substSym_noArrRead e _ hb hss

/-- ssGet from ssSet on [] is arrRead-free when the stored expression is. -/
private theorem ssGet_ssSet_nil_noArrRead (x : Var) (e : Expr) (v : Var)
    (he : e.hasArrRead = false) :
    (ssGet (ssSet ([] : SymStore) x e) v).hasArrRead = false := by
  by_cases hv : v = x
  · subst hv; rw [ssGet_ssSet_same]; exact he
  · rw [ssGet_ssSet_other _ _ _ _ hv, ssGet_nil_var]; simp [Expr.hasArrRead]

/-- If SamCoherent relates the empty SAM, the array memory is unchanged. -/
private theorem samCoherent_nil_am_eq {σ : Store} {am am' : ArrayMem}
    (h : SamCoherent [] σ am am') : am' = am := by
  cases h; rfl

/-- If SamCoherent relates a singleton SAM, the result is a single write. -/
private theorem samCoherent_singleton {σ : Store} {am am' : ArrayMem}
    {arr : ArrayName} {idx_e val_e : Expr}
    (h : SamCoherent [(arr, idx_e, val_e)] σ am am') :
    ∃ bv, (val_e.eval σ am).toBits = bv ∧
      am' = am.write arr (idx_e.eval σ am).toInt bv := by
  cases h
  next h_eval h_coh h_am =>
    exact ⟨_, h_eval, (samCoherent_nil_am_eq h_coh) ▸ h_am⟩

/-- Extract operand values from a binop step producing Cfg.run. -/
private theorem binop_step_values {p : Prog} {pc pc' : Nat} {σ σ' : Store} {am am' : ArrayMem}
    {x : Var} {op : BinOp} {y z : Var}
    (hinstr : p[pc]? = some (.binop x op y z))
    (hstep : Step p (Cfg.run pc σ am) (Cfg.run pc' σ' am')) :
    ∃ a b : BitVec 64, σ y = .int a ∧ σ z = .int b ∧ op.safe a b := by
  cases hstep with
  | binop h => rw [hinstr] at h; cases h; exact ⟨_, _, ‹_›, ‹_›, ‹_›⟩
  | _ => all_goals simp_all

/-- Extract index value and bounds from an arrLoad step producing Cfg.run. -/
private theorem arrLoad_step_values {p : Prog} {pc pc' : Nat} {σ σ' : Store} {am am' : ArrayMem}
    {x : Var} {arr : ArrayName} {idx : Var} {ty : VarTy}
    (hinstr : p[pc]? = some (.arrLoad x arr idx ty))
    (hstep : Step p (Cfg.run pc σ am) (Cfg.run pc' σ' am')) :
    ∃ iv : BitVec 64, σ idx = .int iv ∧ iv < p.arraySizeBv arr := by
  cases hstep with
  | arrLoad h => rw [hinstr] at h; cases h; exact ⟨_, ‹_›, ‹_›⟩
  | _ => all_goals simp_all

/-- Extract index/value types from an arrStore step that produces Cfg.run. -/
private theorem arrStore_step_values {p : Prog} {pc pc' : Nat} {σ σ' : Store} {am am' : ArrayMem}
    {arr : ArrayName} {idx val : Var}
    (hinstr : p[pc]? = some (.arrStore arr idx val ty))
    (hstep : Step p (Cfg.run pc σ am) (Cfg.run pc' σ' am')) :
    ∃ iv : BitVec 64, σ idx = .int iv ∧
      am' = am.write arr iv (σ val).toBits ∧ σ' = σ := by
  cases hstep with
  | arrStore h hidx hty =>
    rw [hinstr] at h; cases h; exact ⟨_, hidx, rfl, rfl⟩
  | _ => all_goals simp_all

/-- Extract index value, type check, and bounds from an arrStore step producing Cfg.run. -/
private theorem arrStore_step_full {p : Prog} {pc pc' : Nat} {σ σ' : Store} {am am' : ArrayMem}
    {arr : ArrayName} {idx val : Var} {ty : VarTy}
    (hinstr : p[pc]? = some (.arrStore arr idx val ty))
    (hstep : Step p (Cfg.run pc σ am) (Cfg.run pc' σ' am')) :
    ∃ iv : BitVec 64, σ idx = .int iv ∧ (σ val).typeOf = ty ∧ iv < p.arraySizeBv arr := by
  cases hstep with
  | arrStore h hidx hty hbnd =>
    rw [hinstr] at h; cases h; exact ⟨_, hidx, hty, hbnd⟩
  | _ => all_goals simp_all

/-- A non-arrStore step preserves array memory. -/
private theorem step_am_preserved {p : Prog} {pc pc' : Nat} {σ σ' : Store} {am am' : ArrayMem}
    (hstep : Step p (Cfg.run pc σ am) (Cfg.run pc' σ' am'))
    (h : ∀ arr idx val ty, p[pc]? ≠ some (.arrStore arr idx val ty)) : am' = am := by
  cases hstep with
  | arrStore hinstr _ _ _ => exact absurd hinstr (h _ _ _ _)
  | _ => rfl

/-- Convert Array.getElem? = some to Array.getD equality. -/
private theorem getElem?_to_getD {a : Array α} {i : Nat} {v : α} {d : α}
    (h : a[i]? = some v) : a.getD i d = v := by
  simp only [Array.getD]; split
  · simp_all
  · exfalso; simp_all

/-- If every pair `(e_o, .var v)` in `rel` satisfies `f e_o` and `f (.var v)` holds
    when no pair targets `v`, then `f (ssGet (buildSubstMap rel) v)` holds. -/
private theorem ssGet_buildSubstMap_of_all_rel (rel : EExprRel) (v : Var)
    (f : Expr → Prop)
    (hdefault : (∀ e_o, (e_o, Expr.var v) ∉ rel) → f (.var v))
    (hall : ∀ e_o, (e_o, Expr.var v) ∈ rel → f e_o) :
    f (ssGet (buildSubstMap rel) v) := by
  -- Auxiliary: ssGet (buildSubstMap rel) v is either .var v (when no pair targets v)
  -- or e_o from some (e_o, .var v) ∈ rel (the first such pair).
  suffices h : (ssGet (buildSubstMap rel) v = .var v ∧ ∀ e_o, (e_o, Expr.var v) ∉ rel) ∨
      (∃ e_o, (e_o, Expr.var v) ∈ rel ∧ ssGet (buildSubstMap rel) v = e_o) by
    rcases h with ⟨heq, hnotin⟩ | ⟨e_o, hmem, heq⟩
    · rw [heq]; exact hdefault hnotin
    · rw [heq]; exact hall e_o hmem
  clear hdefault hall f
  induction rel with
  | nil => left; exact ⟨by simp [buildSubstMap, ssGet, List.filterMap], fun _ h => nomatch h⟩
  | cons p rest ih =>
    obtain ⟨e_o, e_t⟩ := p
    by_cases het : e_t = Expr.var v
    · subst het
      right; exact ⟨e_o, List.Mem.head _, by simp [buildSubstMap, List.filterMap, ssGet]⟩
    · -- e_t ≠ .var v: buildSubstMap either skips this pair or maps a different key
      have hskip : ssGet (buildSubstMap ((e_o, e_t) :: rest)) v = ssGet (buildSubstMap rest) v := by
        simp only [buildSubstMap, List.filterMap]
        cases e_t with
        | var w =>
          simp only [ssGet, List.find?]
          have hne : w ≠ v := fun h => het (congrArg Expr.var h)
          simp [beq_eq_false_iff_ne.mpr hne]
        | _ => rfl
      rcases ih with ⟨heq_rest, hnotin_rest⟩ | ⟨e_o', hmem_rest, heq_rest⟩
      · left; rw [hskip]; exact ⟨heq_rest, fun e hmem => by
          cases hmem with
          | head => exact het rfl
          | tail _ htail => exact hnotin_rest e htail⟩
      · right; exact ⟨e_o', List.mem_cons_of_mem _ hmem_rest, hskip ▸ heq_rest⟩

/-- Bridge: when all free vars of an Expr are mapped in the relation and `hcons` holds,
    `substSym` produces an expression that evaluates equivalently. -/
private theorem substSym_bridge (ss : SymStore) (e : Expr) (rel : EExprRel)
    (σ_o σ_t : Store) (am : ArrayMem)
    (hss_eq : ss = buildSubstMap rel)
    (hcons : ∀ e_o v, (e_o, .var v) ∈ rel → σ_t v = e_o.eval σ_o am)
    (hfv : ∀ v, v ∈ e.freeVars → ∃ e_o, (e_o, .var v) ∈ rel) :
    (e.substSym ss).eval σ_o am = e.eval σ_t am := by
  subst hss_eq
  exact Expr.substSym_sound_fv (buildSubstMap rel) e σ_o σ_t am (fun v hv => by
    obtain ⟨e_o, hmem⟩ := hfv v hv
    exact (ssGet_buildSubstMap_of_all_rel rel v (fun e => e.eval σ_o am = σ_t v)
      (fun hnotin => absurd hmem (hnotin e_o))
      (fun e_o' he => (hcons e_o' v he).symm)))

/-- Core bridge: `mapVarsRel` output evaluates at `(σ_o, am_o)` the same as
    the original BoolExpr at `(σ_t, am_t)`, given the store relation,
    arrRead-freeness, and free-variable coverage. -/
private theorem eval_mapVarsRel (b : BoolExpr) (rel : EExprRel)
    (origCond : BoolExpr) (hmap : b.mapVarsRel rel = some origCond)
    (σ_o σ_t : Store) (am_o am_t : ArrayMem)
    (hcons : ∀ e_o v, (e_o, .var v) ∈ rel → σ_t v = e_o.eval σ_o am_o)
    (hnoarr : b.hasArrRead = false)
    (hfv : ∀ v, v ∈ b.exprFreeVars → ∃ e_o, (e_o, .var v) ∈ rel) :
    origCond.eval σ_o am_o = b.eval σ_t am_t := by
  induction b generalizing origCond with
  | lit b_val =>
    simp only [BoolExpr.mapVarsRel] at hmap; cases hmap; simp [BoolExpr.eval]
  | bvar x =>
    simp only [BoolExpr.mapVarsRel, bind, Option.bind] at hmap
    cases hfind : relFindOrigExpr rel x with
    | none => simp [hfind] at hmap
    | some e_found =>
      simp [hfind] at hmap
      cases e_found with
      | var w =>
        simp at hmap; subst hmap
        simp only [BoolExpr.eval]
        have hmem := relFindOrigExpr_mem hfind
        have hcv := hcons (.var w) x hmem
        simp [Expr.eval] at hcv; rw [hcv]
      | _ => simp at hmap
  | cmp op a b_e =>
    simp only [BoolExpr.mapVarsRel] at hmap; cases hmap
    simp only [BoolExpr.eval, Expr.substSym'_eq_substSym]
    simp only [BoolExpr.hasArrRead, Bool.or_eq_false_iff] at hnoarr
    simp only [BoolExpr.exprFreeVars] at hfv
    rw [substSym_bridge _ a rel σ_o σ_t am_o rfl hcons
          (fun v hv => hfv v (List.mem_append_left _ hv)),
        substSym_bridge _ b_e rel σ_o σ_t am_o rfl hcons
          (fun v hv => hfv v (List.mem_append_right _ hv)),
        Expr.eval_noArrRead a σ_t am_o am_t hnoarr.1,
        Expr.eval_noArrRead b_e σ_t am_o am_t hnoarr.2]
  | not e ih =>
    simp only [BoolExpr.mapVarsRel, Option.map] at hmap
    cases hm : e.mapVarsRel rel with
    | none => simp [hm] at hmap
    | some e' =>
      simp [hm] at hmap
      simp only [BoolExpr.hasArrRead] at hnoarr
      simp only [BoolExpr.exprFreeVars] at hfv
      have ih_e := ih e' hm hnoarr hfv
      -- origCond = match e' with | .not inner => inner | _ => .not e'
      -- (.not e).eval σ_t am_t = !(e.eval σ_t am_t)
      cases e' with
      | not inner =>
        -- double negation: origCond = inner
        simp at hmap; subst hmap
        simp only [BoolExpr.eval] at ih_e ⊢
        rw [← ih_e, Bool.not_not]
      | lit _ | bvar _ | cmp _ _ _ | fcmp _ _ _ | bexpr _ =>
        simp at hmap; subst hmap; exact congrArg (! ·) ih_e
  | fcmp op a b_e =>
    simp only [BoolExpr.mapVarsRel] at hmap; cases hmap
    simp only [BoolExpr.eval, Expr.substSym'_eq_substSym]
    simp only [BoolExpr.hasArrRead, Bool.or_eq_false_iff] at hnoarr
    simp only [BoolExpr.exprFreeVars] at hfv
    rw [substSym_bridge _ a rel σ_o σ_t am_o rfl hcons
          (fun v hv => hfv v (List.mem_append_left _ hv)),
        substSym_bridge _ b_e rel σ_o σ_t am_o rfl hcons
          (fun v hv => hfv v (List.mem_append_right _ hv)),
        Expr.eval_noArrRead a σ_t am_o am_t hnoarr.1,
        Expr.eval_noArrRead b_e σ_t am_o am_t hnoarr.2]
  | bexpr e =>
    simp only [BoolExpr.mapVarsRel] at hmap; cases hmap
    simp only [BoolExpr.eval, Expr.substSym'_eq_substSym]
    simp only [BoolExpr.hasArrRead] at hnoarr
    simp only [BoolExpr.exprFreeVars] at hfv
    rw [substSym_bridge _ e rel σ_o σ_t am_o rfl hcons hfv,
        Expr.eval_noArrRead e σ_t am_o am_t hnoarr]

/-- When `branchInfoWithRel` returns `some (origCond, taken)`, a step on the
    transformed program implies `origCond.eval σ_o = taken`
    via the store relation and `eval_mapVarsRel`. -/
private theorem branchInfo_of_step_with_rel {prog : Prog} {pc pc' : Label} {σ_t σ_t' : Store} {am_t am_t' : ArrayMem}
    {instr : TAC} (hinstr : prog[pc]? = some instr)
    (hstep : Step prog (Cfg.run pc σ_t am_t) (Cfg.run pc' σ_t' am_t'))
    {rel : EExprRel} {σ_o : Store} {am_o : ArrayMem}
    (hcons : ∀ e_o v, (e_o, .var v) ∈ rel → σ_t v = e_o.eval σ_o am_o)
    (hnoarr_b : ∀ b l, instr = .ifgoto b l → b.hasArrRead = false)
    (hfvCov : ∀ b l, instr = .ifgoto b l → ∀ v, v ∈ b.exprFreeVars → ∃ e_o, (e_o, .var v) ∈ rel)
    {origCond : BoolExpr} {taken : Bool}
    (hbi : branchInfoWithRel instr rel pc pc' = some (origCond, taken)) :
    origCond.eval σ_o am_o = taken := by
  cases instr with
  | ifgoto b l =>
    simp only [branchInfoWithRel] at hbi
    cases hmap : b.mapVarsRel rel with
    | none => simp [hmap] at hbi
    | some origCond' =>
      simp only [hmap] at hbi
      by_cases hguard : (!(l == pc + 1))
      · simp only [hguard, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hbi
        obtain ⟨rfl, rfl⟩ := hbi
        have hnoarr := hnoarr_b b l rfl
        have hfv := hfvCov b l rfl
        have heval_bridge := eval_mapVarsRel b rel origCond' hmap σ_o σ_t am_o am_t hcons hnoarr hfv
        -- Case split on the step; unify the ifgoto instruction first
        cases hstep with
        | iftrue hinstr' heval =>
          have heq := Option.some.inj (hinstr.symm.trans hinstr')
          cases heq; simp only [beq_self_eq_true]; rw [heval_bridge, heval]
        | iffall hinstr' heval =>
          have heq := Option.some.inj (hinstr.symm.trans hinstr')
          cases heq
          simp only [Bool.not_eq_true'] at hguard
          have hne : ¬(l = pc + 1) := fun h => by simp [h] at hguard
          simp [beq_eq_false_iff_ne.mpr (Ne.symm hne)]
          rw [heval_bridge, heval]
        | const h => exact absurd (hinstr.symm.trans h) (by simp)
        | copy h => exact absurd (hinstr.symm.trans h) (by simp)
        | binop h _ _ _ => exact absurd (hinstr.symm.trans h) (by simp)
        | boolop h => exact absurd (hinstr.symm.trans h) (by simp)
        | goto h => exact absurd (hinstr.symm.trans h) (by simp)
        | arrLoad h _ _ => exact absurd (hinstr.symm.trans h) (by simp)
        | arrStore h _ _ _ => exact absurd (hinstr.symm.trans h) (by simp)
        | fbinop h _ _ => exact absurd (hinstr.symm.trans h) (by simp)
        | fternop h _ _ _ => exact absurd (hinstr.symm.trans h) (by simp)
        | intToFloat h _ => exact absurd (hinstr.symm.trans h) (by simp)
        | floatToInt h _ => exact absurd (hinstr.symm.trans h) (by simp)
        | floatUnary h _ => exact absurd (hinstr.symm.trans h) (by simp)
        | print h => exact absurd (hinstr.symm.trans h) (by simp)
        | printInt h => exact absurd (hinstr.symm.trans h) (by simp)
        | printBool h => exact absurd (hinstr.symm.trans h) (by simp)
        | printFloat h => exact absurd (hinstr.symm.trans h) (by simp)
        | printString h => exact absurd (hinstr.symm.trans h) (by simp)
      · simp [hguard] at hbi
  | _ => simp [branchInfoWithRel] at hbi

/-- Extract the pairCheck from checkRelConsistency. -/
private theorem checkRelConsistency_pairCheck
    (orig : Prog) (pc_orig : Label) (origLabels : List Label) (transInstr : TAC)
    (inv_orig : EInv) (rel_pre rel_post : EExprRel)
    (h : checkRelConsistency orig pc_orig origLabels transInstr inv_orig rel_pre rel_post = true) :
    rel_post.all (fun (e_o, e_t) =>
      (e_o.substSym (execPath orig ([] : SymStore) ([] : SymArrayMem) pc_orig origLabels).1).simplifyDeep (sdFuel inv_orig) inv_orig ==
      ((e_t.substSym (execSymbolic ([] : SymStore) ([] : SymArrayMem) transInstr).1).substSym
        (buildSubstMap rel_pre)).simplifyDeep (sdFuel inv_orig) inv_orig) = true := by
  simp only [← Expr.substSymFast_eq_substSym, ← Expr.simplifyDeepFastEarly_eq_simplifyDeep]
  simp only [checkRelConsistency, Bool.and_eq_true] at h
  exact h.1.1.1

/-- Free-variable coverage: all free vars of substSym'd expressions are in rel_pre. -/
private theorem checkRelConsistency_fvCheck
    (orig : Prog) (pc_orig : Label) (origLabels : List Label) (transInstr : TAC)
    (inv_orig : EInv) (rel_pre rel_post : EExprRel)
    (h : checkRelConsistency orig pc_orig origLabels transInstr inv_orig rel_pre rel_post = true) :
    let transSS := (execSymbolic ([] : SymStore) ([] : SymArrayMem) transInstr).1
    rel_post.all (fun (_, e_t) =>
      (e_t.substSym transSS).freeVars.all fun w =>
        rel_pre.any fun (_, e_t') => e_t' == .var w) = true := by
  simp only [← Expr.substSymFast_eq_substSym, ← relVarSet_contains_eq_any]
  simp only [checkRelConsistency, Bool.and_eq_true] at h
  exact h.1.1.2

/-- Array memory free-variable coverage: all free vars of AM expressions are in rel_pre. -/
private theorem checkRelConsistency_amFvCheck
    (orig : Prog) (pc_orig : Label) (origLabels : List Label) (transInstr : TAC)
    (inv_orig : EInv) (rel_pre rel_post : EExprRel)
    (h : checkRelConsistency orig pc_orig origLabels transInstr inv_orig rel_pre rel_post = true) :
    let transSAM := (execSymbolic ([] : SymStore) ([] : SymArrayMem) transInstr).2
    transSAM.all (fun (_, i_t, v_t) =>
      (i_t.freeVars.all fun w => rel_pre.any fun (_, e_t') => e_t' == .var w) &&
      (v_t.freeVars.all fun w => rel_pre.any fun (_, e_t') => e_t' == .var w)) = true := by
  simp only [← relVarSet_contains_eq_any]
  simp only [checkRelConsistency, Bool.and_eq_true] at h
  exact h.1.2

private theorem checkRelConsistency_amCheck
    (orig : Prog) (pc_orig : Label) (origLabels : List Label) (transInstr : TAC)
    (inv_orig : EInv) (rel_pre rel_post : EExprRel)
    (h : checkRelConsistency orig pc_orig origLabels transInstr inv_orig rel_pre rel_post = true) :
    (execPath orig ([] : SymStore) ([] : SymArrayMem) pc_orig origLabels).2.length =
      (execSymbolic ([] : SymStore) ([] : SymArrayMem) transInstr).2.length ∧
    ((execPath orig ([] : SymStore) ([] : SymArrayMem) pc_orig origLabels).2.zip
      (execSymbolic ([] : SymStore) ([] : SymArrayMem) transInstr).2).all
      (fun ((a_o, i_o, v_o), (a_t, i_t, v_t)) =>
        a_o == a_t &&
        i_o.simplifyDeep (sdFuel inv_orig) inv_orig == (i_t.substSym (buildSubstMap rel_pre)).simplifyDeep (sdFuel inv_orig) inv_orig &&
        v_o.simplifyDeep (sdFuel inv_orig) inv_orig == (v_t.substSym (buildSubstMap rel_pre)).simplifyDeep (sdFuel inv_orig) inv_orig) = true := by
  simp only [← Expr.substSymFast_eq_substSym, ← Expr.simplifyDeepFastEarly_eq_simplifyDeep]
  simp only [checkRelConsistency, Bool.and_eq_true] at h
  obtain ⟨_, hamCheck⟩ := h
  simp only [beq_iff_eq] at hamCheck
  exact hamCheck

/-- Bridge: when a variable has a pair in the relation, the ssGet-based form follows. -/
private theorem eRelToStoreRel_ssGet {rel : EExprRel} {σ_o σ_t : Store} {am_o am_t : ArrayMem}
    (hcons : eRelToStoreRel rel σ_o am_o σ_t am_t)
    (v : Var) (hmem : ∃ e_o, (e_o, .var v) ∈ rel) :
    σ_t v = (ssGet (buildSubstMap rel) v).eval σ_o am_o := by
  apply ssGet_buildSubstMap_of_all_rel rel v (fun e => σ_t v = e.eval σ_o am_o)
  · intro hnotin; obtain ⟨e_o, he⟩ := hmem; exact absurd he (hnotin e_o)
  · intro e_o he; exact hcons e_o v he

/-- Bridge: convert relFindOrigVar success to membership-based store fact. -/
private theorem eRelToStoreRel_of_relFindOrigVar {rel : EExprRel} {σ_o σ_t : Store} {am_o am_t : ArrayMem}
    (hcons : eRelToStoreRel rel σ_o am_o σ_t am_t)
    {v v' : Var} (hfind : relFindOrigVar rel v = some v') :
    σ_t v = σ_o v' :=
  store_eq_of_relFindOrigVar hfind hcons

/-- Transfer index equality `σ_t idx_t = σ_o idx_o` when both map to the same
    literal constant: the invariant says `σ_o idx_o = c` and the relation says
    `σ_t idx_t = c'` with `c = c'`. -/
private theorem idx_transfer_via_inv
    {dc : ECertificate} {idx_t idx_o : Var} {σ_t σ_o : Store} {am_o : ArrayMem}
    {dic : EInstrCert} {pc_t : Nat}
    (hinv_case : (match (dc.inv_orig.getD dic.pc_orig ([] : EInv)).find? (fun (v, _) => v == idx_o) with
       | some (_, .lit c) =>
         match relFindOrigExpr dic.rel idx_t with
         | some (.lit c') => c == c'
         | _ => false
       | _ => false) = true)
    (hcons : ∀ e_o v, (e_o, .var v) ∈ dic.rel → σ_t v = e_o.eval σ_o am_o)
    (hinv_o : EInv.toProp (dc.inv_orig.getD dic.pc_orig ([] : EInv)) σ_o am_o)
    (_hic_def : dic = dc.instrCerts.getD pc_t default) :
    σ_t idx_t = σ_o idx_o := by
  generalize hfi : (dc.inv_orig.getD dic.pc_orig ([] : EInv)).find? (fun (v, _) => v == idx_o) = fi at hinv_case
  cases fi with
  | none => simp at hinv_case
  | some p =>
    obtain ⟨v, e⟩ := p
    cases e with
    | lit c =>
      generalize hfr : relFindOrigExpr dic.rel idx_t = fr at hinv_case
      cases fr with
      | none => simp at hinv_case
      | some e'  =>
        cases e' with
        | lit c' =>
          simp at hinv_case
          have hpred := List.find?_some hfi; simp at hpred
          symm at hpred; subst hpred
          have hmem := List.mem_of_find?_eq_some hfi
          have hinv_entry := hinv_o (idx_o, .lit c) hmem
          simp [Expr.eval] at hinv_entry
          have hmem_rel := relFindOrigExpr_mem hfr
          have hσt := hcons _ _ hmem_rel
          simp [Expr.eval] at hσt
          rw [hσt, hinv_entry, hinv_case]
        | _ => simp at hinv_case
    | _ => simp at hinv_case

set_option maxHeartbeats 400000 in
/-- Soundness of checkTransitionRelProp from the Bool checks.
    Given: checkOrigPath and checkRelConsistency both pass, the original path
    produces steps reaching the target with store relation preserved.
    Supports non-trivial expression relations with pair-based store relations. -/
private theorem transRel_sound (dc : ECertificate)
    (hwtp : WellTypedProg dc.tyCtx dc.orig)
    (hnoarr_orig : checkNoArrReadInInvs dc.inv_orig = true)
    (hbndpres : checkBoundsPreservationExec dc = true)
    (harrsize : checkArraySizesExec dc = true)
    (hdivpres : checkDivPreservationExec dc = true)
    (pc_t pc_t' : Label)
    (dic : EInstrCert) (dtc : ETransCorr) (instr : TAC)
    (pc_o' : Label)
    (hdic : dc.instrCerts[pc_t]? = some dic)
    (hnoarr_rel : dtc.rel.all (fun (e, _) => !e.hasArrRead) = true)
    (hnoarr_rel_next : dtc.rel_next.all (fun (e, _) => !e.hasArrRead) = true)
    (hinstr : dc.trans[pc_t]? = some instr)
    -- orig at dic.pc_orig is scalar, OR trans at pc_t is an array op
    (hOrigFirstOk : (∀ i, dc.orig[dic.pc_orig]? = some i → i.isScalar = true) ∨
        (∃ x arr idx ty, instr = .arrLoad x arr idx ty) ∨
        (∃ arr idx val ty, instr = .arrStore arr idx val ty))
    (hrel_eq : dtc.rel = dic.rel)
    (hRestScalar : ∀ l ∈ dtc.origLabels.dropLast,
        ∀ i, dc.orig[l]? = some i → i.isScalar = true)
    (hRestNoDivMod : ∀ l ∈ dtc.origLabels.dropLast, ∀ x y z,
        dc.orig[l]? ≠ some (.binop x .div y z) ∧ dc.orig[l]? ≠ some (.binop x .mod y z))
    (hBoolNoArr : ∀ (pc' : Nat) instr, dc.orig[pc']? = some instr →
        (∀ x be, instr = TAC.boolop x be → be.hasArrRead = false) ∧
        (∀ b l, instr = TAC.ifgoto b l → b.hasArrRead = false))
    (hBoolNoArrTrans : ∀ (pc' : Nat) instr, dc.trans[pc']? = some instr →
        (∀ x be, instr = TAC.boolop x be → be.hasArrRead = false) ∧
        (∀ b l, instr = TAC.ifgoto b l → b.hasArrRead = false))
    (hBoolVarsCov : ∀ b l, instr = .ifgoto b l →
        ∀ v, v ∈ b.exprFreeVars → ∃ e_o, (e_o, .var v) ∈ dtc.rel)
    (hpath : checkOrigPath dc.orig ([] : SymStore) ([] : SymArrayMem) (dc.inv_orig.getD dic.pc_orig ([] : EInv))
      dic.pc_orig dtc.origLabels pc_o'
      (branchInfoWithRel instr dtc.rel pc_t pc_t') = true)
    (hrelcheck : checkRelConsistency
      dc.orig dic.pc_orig dtc.origLabels instr
      (dc.inv_orig.getD dic.pc_orig ([] : EInv))
      dtc.rel dtc.rel_next = true) :
    checkTransitionRelProp dc.tyCtx dc.orig dc.trans
      (fun l => (dc.inv_orig.getD l ([] : EInv)).toProp)
      (fun l => (dc.inv_trans.getD l ([] : EInv)).toProp)
      pc_t pc_t' dic.pc_orig pc_o'
      { origLabels := dtc.origLabels
        storeRel := eRelToStoreRel dtc.rel
        storeRel_next := eRelToStoreRel dtc.rel_next } := by
  -- Unfold checkTransitionRelProp and introduce all quantified variables
  intro σ_t σ_t' σ_o am_t am_t' am_o hinv_t hinv_o hstorerel ham_eq htyped hstep
  subst ham_eq  -- am_o is replaced by am_t everywhere
  -- The store relation gives us: ∀ e_o v, (e_o, .var v) ∈ dtc.rel → σ_t v = e_o.eval σ_o am_t
  have hcons : ∀ e_o v, (e_o, .var v) ∈ dtc.rel → σ_t v = e_o.eval σ_o am_t := hstorerel
  -- Derive hDivSafe for the first instruction on the original path
  have hDivSafe : dtc.origLabels ≠ [] → ∀ x (op : BinOp) y_o z_o (a b : BitVec 64),
      dc.orig[dic.pc_orig]? = some (.binop x op y_o z_o) →
      σ_o y_o = .int a → σ_o z_o = .int b → op.safe a b := by
    intro _hne x_o op_o y_o z_o a_o b_o horig hya hzb
    cases op_o with
    | add | sub | mul | band | bor | bxor | shl | shr => exact True.intro
    | div | mod =>
      -- Extract div-preservation info for pc_t
      simp only [checkDivPreservationExec, List.all_eq_true, List.mem_range] at hdivpres
      have hpc_bound := bound_of_getElem? hinstr
      have hpc_check := hdivpres pc_t hpc_bound
      -- Case split on the transformed instruction
      revert hstep hpc_check; cases instr with
      | binop x_t op_t y_t z_t =>
        intro hstep hpc_check
        rw [hinstr] at hpc_check
        have hgetD : dc.instrCerts.getD pc_t default = dic := getElem?_to_getD hdic
        rw [hgetD] at hpc_check; rw [horig] at hpc_check
        -- Extract op == op' (checked for all binops)
        rw [Bool.and_eq_true] at hpc_check; obtain ⟨hop_eq, hrest⟩ := hpc_check
        have hop := beq_iff_eq.mp hop_eq
        -- Resolve the match on op_t in hrest (op_t = div or mod)
        rw [hop] at hrest
        -- From the step: extract a_t, b_t and op_t.safe a_t b_t
        have ⟨a_t, b_t, hya_t, hzb_t, hsafe_t⟩ := binop_step_values hinstr hstep
        rw [Bool.and_eq_true] at hrest
        -- The dividend check is irrelevant to div/mod safety (`BinOp.safe` depends
        -- only on the divisor), so we ignore it and use only the divisor part.
        obtain ⟨_, hz_rel⟩ := hrest
        -- Case split: either relFindOrigVar succeeds, or conjunction fallback
        rw [Bool.or_eq_true] at hz_rel
        rcases hz_rel with hz_var | hz_conj
        · -- relFindOrigVar succeeds: transfer safety via store equality
          have hz_find : relFindOrigVar dic.rel z_t = some z_o := beq_iff_eq.mp hz_var
          have hσt_z : σ_t z_t = σ_o z_o := by
            rw [← hrel_eq] at hz_find
            exact store_eq_of_relFindOrigVar hz_find hcons
          have hb_eq : b_o = b_t := Value.int.inj ((hzb).symm.trans (hσt_z ▸ hzb_t))
          subst hb_eq
          simp only [BinOp.safe]; rw [hop] at hsafe_t; exact hsafe_t
        · -- Conjunction fallback: use orig invariant for walkability
          rw [Bool.and_eq_true] at hz_conj
          obtain ⟨_, hz_inv⟩ := hz_conj
          set inv := dc.inv_orig.getD dic.pc_orig ([] : EInv) with hinv_def
          cases hfind : inv.find? (fun (w, _) => w == z_o) with
          | none => simp [hfind] at hz_inv
          | some p =>
            obtain ⟨v, e⟩ := p
            have hmem := List.mem_of_find?_eq_some hfind
            have hpred : v = z_o := by
              have hfs := List.find?_some hfind
              simp only at hfs; exact beq_iff_eq.mp hfs
            cases e with
            | lit c =>
              simp [hfind] at hz_inv
              rw [hpred] at hmem
              have hinv_z := hinv_o (z_o, .lit c) hmem
              simp [Expr.eval] at hinv_z
              rw [hinv_z] at hzb; cases hzb
              simp only [BinOp.safe]; exact hz_inv
            | _ => simp [hfind] at hz_inv
      | _ =>
        intro hstep hpc_check
        rw [hinstr] at hpc_check
        have hgetD : dc.instrCerts.getD pc_t default = dic := getElem?_to_getD hdic
        rw [hgetD] at hpc_check; rw [horig] at hpc_check
        simp only at hpc_check
        set inv := dc.inv_orig.getD dic.pc_orig ([] : EInv) with hinv_def
        cases hfind : inv.find? (fun (w, _) => w == z_o) with
        | none => simp [hfind] at hpc_check
        | some p =>
          obtain ⟨v, e⟩ := p
          have hmem := List.mem_of_find?_eq_some hfind
          have hpred : v = z_o := by
            have hfs := List.find?_some hfind
            simp only at hfs; exact beq_iff_eq.mp hfs
          cases e with
          | lit c =>
            simp [hfind] at hpc_check
            rw [hpred] at hmem
            have hinv_z := hinv_o (z_o, .lit c) hmem
            simp [Expr.eval] at hinv_z
            rw [hinv_z] at hzb; cases hzb
            simp only [BinOp.safe]; exact hpc_check
          | _ => simp [hfind] at hpc_check
  -- Derive arguments for execPath_sound
  set inv_o := dc.inv_orig.getD dic.pc_orig ([] : EInv) with hinv_o_def
  have hrepr_nil : ∀ v, (ssGet ([] : SymStore) v).eval σ_o am_t = σ_o v :=
    ssGet_nil σ_o am_t
  have hInvNoArrRead : inv_o.all (fun (_, e) => !e.hasArrRead) = true := by
    simp only [inv_o]
    exact noArrRead_of_inv_all dc.inv_orig hnoarr_orig dic.pc_orig
  have hbranch : ∀ cond taken, branchInfoWithRel instr dtc.rel pc_t pc_t' = some (cond, taken) →
      cond.eval σ_o am_t = taken := by
    intro cond taken hbi
    exact branchInfo_of_step_with_rel hinstr hstep hstorerel
      (fun b l heq => (hBoolNoArrTrans pc_t _ hinstr).2 b l heq)
      hBoolVarsCov hbi
  have hbranchNoArr : ∀ cond taken, branchInfoWithRel instr dtc.rel pc_t pc_t' = some (cond, taken) →
      cond.hasArrRead = false := by
    intro cond taken hbi
    simp only [branchInfoWithRel] at hbi
    cases instr with
    | ifgoto b l =>
      simp only at hbi
      cases hmap : b.mapVarsRel dtc.rel with
      | none => simp [hmap] at hbi
      | some origCond =>
        simp only [hmap] at hbi
        split at hbi <;> simp at hbi
        obtain ⟨rfl, _⟩ := hbi
        -- origCond = b.mapVarsRel dtc.rel = some origCond
        -- b is arrRead-free (from hBoolNoArrTrans + hinstr)
        have hb_noarr := (hBoolNoArrTrans pc_t _ hinstr).2 b l rfl
        exact mapVarsRel_noArrRead b dtc.rel origCond hmap hb_noarr hnoarr_rel
    | _ => simp at hbi
  -- Array bounds for the first instruction
  have hOrigBounds : dtc.origLabels ≠ [] → ∀ arr idx (idxVal : BitVec 64) ty,
      ((∃ x, dc.orig[dic.pc_orig]? = some (.arrLoad x arr idx ty)) ∨
       (∃ val, dc.orig[dic.pc_orig]? = some (.arrStore arr idx val ty))) →
      σ_o idx = .int idxVal → idxVal < dc.orig.arraySizeBv arr := by
    intro _hne arr_o idx_o idxVal_o ty_o hinstr_arr hidxVal_o
    -- From hOrigFirstOk: either the first orig instruction is scalar (contradiction with
    -- arrLoad/arrStore since isScalar = false for those), or the trans instr is an array op
    cases hOrigFirstOk with
    | inl hscalar =>
      -- Original instruction is scalar, but arrLoad/arrStore is not scalar → contradiction
      cases hinstr_arr with
      | inl h => obtain ⟨x, hload⟩ := h; exact absurd (hscalar _ hload) (by simp [TAC.isScalar])
      | inr h => obtain ⟨val, hstore⟩ := h; exact absurd (hscalar _ hstore) (by simp [TAC.isScalar])
    | inr harray =>
      -- Trans instruction is an array op. Extract bounds from the transformed step
      -- and transfer via bounds-preservation + store relation + array sizes
      simp only [checkBoundsPreservationExec, List.all_eq_true, List.mem_range] at hbndpres
      have hpc_bound := bound_of_getElem? hinstr
      have hpc_check := hbndpres pc_t hpc_bound; rw [hinstr] at hpc_check
      have hgetD : dc.instrCerts.getD pc_t default = dic := getElem?_to_getD hdic
      rw [hgetD] at hpc_check
      simp only [checkArraySizesExec, beq_iff_eq] at harrsize
      -- Case-split on whether trans is arrLoad or arrStore
      cases harray with
      | inl h =>
        obtain ⟨x_t, arr_t, idx_t, ty_t, htrans_eq⟩ := h
        subst htrans_eq
        -- bounds-pres check gives: matching arrLoad in orig with same array and related index
        cases hinstr_arr with
        | inl h =>
          obtain ⟨x_o, horig⟩ := h; rw [horig] at hpc_check
          rw [Bool.and_eq_true] at hpc_check; obtain ⟨harr_eq, hidx_eq⟩ := hpc_check
          have harr : arr_t = arr_o := beq_iff_eq.mp harr_eq
          rw [Bool.or_eq_true] at hidx_eq
          -- From the step, extract the index value and bounds
          have ⟨idxVal_t, hidx_t, hbnd_t⟩ := arrLoad_step_values hinstr hstep
          -- Transfer index via store relation or invariant
          have hσt_idx : σ_t idx_t = σ_o idx_o := by
            rcases hidx_eq with hvar | hinv
            · have hf := beq_iff_eq.mp hvar; rw [← hrel_eq] at hf
              exact store_eq_of_relFindOrigVar hf hcons
            · exact idx_transfer_via_inv hinv (hrel_eq ▸ hcons) hinv_o (getElem?_to_getD hdic).symm
          have : idxVal_o = idxVal_t := Value.int.inj (hidxVal_o.symm.trans (hσt_idx ▸ hidx_t))
          subst this
          rw [← harr]; simp [Prog.arraySizeBv, harrsize]; exact hbnd_t
        | inr h =>
          obtain ⟨val_o, horig⟩ := h; rw [horig] at hpc_check; simp at hpc_check
      | inr h =>
        obtain ⟨arr_t, idx_t, val_t, ty_t, htrans_eq⟩ := h
        subst htrans_eq
        cases hinstr_arr with
        | inl h =>
          obtain ⟨x_o, horig⟩ := h; rw [horig] at hpc_check; simp at hpc_check
        | inr h =>
          obtain ⟨val_o, horig⟩ := h; rw [horig] at hpc_check
          rw [Bool.and_eq_true] at hpc_check; obtain ⟨harr_eq, hidx_eq⟩ := hpc_check
          have harr : arr_t = arr_o := beq_iff_eq.mp harr_eq
          rw [Bool.or_eq_true] at hidx_eq
          have ⟨idxVal_t, hidx_t, _, hbnd_t⟩ := arrStore_step_full hinstr hstep
          have hσt_idx : σ_t idx_t = σ_o idx_o := by
            rcases hidx_eq with hvar | hinv
            · have hf := beq_iff_eq.mp hvar; rw [← hrel_eq] at hf
              exact store_eq_of_relFindOrigVar hf hcons
            · exact idx_transfer_via_inv hinv (hrel_eq ▸ hcons) hinv_o (getElem?_to_getD hdic).symm
          have : idxVal_o = idxVal_t := Value.int.inj (hidxVal_o.symm.trans (hσt_idx ▸ hidx_t))
          subst this
          rw [← harr]; simp [Prog.arraySizeBv, harrsize]; exact hbnd_t
  -- Execute the original path
  obtain ⟨σ_o', am_o', hsteps_orig, hrepr_final, hsamCoh_final⟩ :=
    execPath_sound dc.orig inv_o σ_o dic.pc_orig dtc.origLabels pc_o'
      (branchInfoWithRel instr dtc.rel pc_t pc_t') am_t
      dc.tyCtx hwtp htyped hrepr_nil hinv_o hInvNoArrRead
      hpath hbranch hbranchNoArr hOrigBounds hRestScalar hDivSafe hRestNoDivMod hBoolNoArr
  -- Construct the result
  refine ⟨σ_o', am_o', hsteps_orig, ?_, ?_⟩
  · -- Post-state store relation: eRelToStoreRel dtc.rel_next σ_o' am_o' σ_t' am_t'
    -- Abbreviations for the symbolic stores
    set origSS := (execPath dc.orig ([] : SymStore) ([] : SymArrayMem) dic.pc_orig dtc.origLabels).1
    set transSS := (execSymbolic ([] : SymStore) ([] : SymArrayMem) instr).1
    set preSubst := buildSubstMap dtc.rel
    -- Step 1: Extract pairCheck from hrelcheck
    have hpairCheck := checkRelConsistency_pairCheck dc.orig dic.pc_orig dtc.origLabels instr
      inv_o dtc.rel dtc.rel_next hrelcheck
    -- Step 2: Build hrepr_trans (symbolic execution of the transformed step)
    have hrepr_trans : ∀ v, (ssGet transSS v).eval σ_t am_t = σ_t' v := by
      by_cases hscalar : instr.isScalar = true
      · exact execSymbolic_sound ([] : SymStore) ([] : SymArrayMem) instr σ_t σ_t σ_t' pc_t pc_t'
          dc.trans am_t (ssGet_nil σ_t am_t) hstep hinstr hscalar
      · cases instr with
        | arrStore arr idx val ty =>
          change ∀ v, (ssGet (execSymbolic ([] : SymStore) ([] : SymArrayMem)
            (TAC.arrStore arr idx val ty)).1 v).eval σ_t am_t = σ_t' v
          simp only [execSymbolic]
          have step_det : ∀ c, Step dc.trans (Cfg.run pc_t σ_t am_t) c →
              c = Cfg.run pc_t' σ_t' am_t' :=
            fun c hc => Step.deterministic hc hstep
          obtain ⟨idxVal, hv, hty, hbnd⟩ := arrStore_step_full hinstr hstep
          have := step_det _ (Step.arrStore hinstr hv hty hbnd)
          have hσ' : σ_t' = σ_t := (Cfg.run.inj this).2.1.symm
          rw [hσ']; exact ssGet_nil σ_t am_t
        | arrLoad dest arr idx ty =>
          change ∀ v, (ssGet (execSymbolic ([] : SymStore) ([] : SymArrayMem)
            (TAC.arrLoad dest arr idx ty)).1 v).eval σ_t am_t = σ_t' v
          simp only [execSymbolic]
          have step_det : ∀ c, Step dc.trans (Cfg.run pc_t σ_t am_t) c →
              c = Cfg.run pc_t' σ_t' am_t' :=
            fun c hc => Step.deterministic hc hstep
          obtain ⟨idxVal, hidx, hbnd⟩ := arrLoad_step_values hinstr hstep
          have := step_det _ (Step.arrLoad hinstr hidx hbnd)
          have hσ' : σ_t' = σ_t[dest ↦ Value.ofBitVec ty (am_t.read arr idxVal)] :=
            (Cfg.run.inj this).2.1.symm
          intro v
          by_cases hvd : v = dest
          · rw [hvd, ssGet_ssSet_same, hσ']
            simp only [Store.update_self]
            -- samGet with empty SAM returns type-specific fallback matching Value.ofBitVec
            cases ty <;> simp [samGet, List.find?, Expr.eval, ssGet, Value.ofBitVec,
              CmpOp.eval, hidx, Value.toInt]
          · rw [ssGet_ssSet_other _ _ _ _ hvd, hσ', ssGet_nil]
            exact (Store.update_other σ_t dest v _ hvd).symm
        | _ => exact absurd rfl hscalar
    -- Step 3: For each (e_o, .var v) ∈ rel_next, prove σ_t' v = e_o.eval σ_o' am_o'
    -- Extract fvCheck from hrelcheck
    have hfvCheck := checkRelConsistency_fvCheck dc.orig dic.pc_orig dtc.origLabels instr
      inv_o dtc.rel dtc.rel_next hrelcheck
    -- For each (e_o, e_t) pair in rel_next, the pairCheck gives semantic equality
    have hpair_sound : ∀ e_o e_t, (e_o, e_t) ∈ dtc.rel_next →
        e_o.eval σ_o' am_t = e_t.eval σ_t' am_t := by
      intro e_o e_t hmem
      rw [List.all_eq_true] at hpairCheck
      have hcheck := hpairCheck (e_o, e_t) hmem
      have hcheck_eq := beq_iff_eq.mp hcheck
      -- Evaluate both simplified sides at (σ_o, am_t) under inv_o
      have hlhs := Expr.simplifyDeep_sound (sdFuel inv_o) inv_o (e_o.substSym origSS) σ_o am_t hinv_o
      have hrhs := Expr.simplifyDeep_sound (sdFuel inv_o) inv_o
        ((e_t.substSym transSS).substSym preSubst) σ_o am_t hinv_o
      have heval_eq : (e_o.substSym origSS).eval σ_o am_t =
          ((e_t.substSym transSS).substSym preSubst).eval σ_o am_t := by
        rw [← hlhs, ← hrhs, hcheck_eq]
      -- LHS: (e_o.substSym origSS).eval σ_o am_t = e_o.eval σ_o' am_t
      have horig_sub := Expr.substSym_sound origSS e_o σ_o σ_o' am_t hrepr_final
      -- RHS: use substSym_sound_fv with free-variable coverage from fvCheck
      --     ((e_t.substSym transSS).substSym preSubst).eval σ_o am_t
      --     = (e_t.substSym transSS).eval σ_t am_t  (by substSym_sound_fv with fvCheck)
      --     = e_t.eval σ_t' am_t  (by substSym_sound with hrepr_trans)
      have hpre_sub := Expr.substSym_sound_fv preSubst (e_t.substSym transSS) σ_o σ_t am_t
        (fun w hw => by
          -- From fvCheck: w has a pair in dtc.rel
          rw [List.all_eq_true] at hfvCheck
          have hfv := hfvCheck (e_o, e_t) hmem
          rw [List.all_eq_true] at hfv
          have hany := hfv w hw
          rw [List.any_eq_true] at hany
          obtain ⟨⟨e_w, e_tw⟩, hmem_w, hbeq⟩ := hany
          have htw : e_tw = .var w := beq_iff_eq.mp hbeq
          subst htw
          -- w has a pair in dtc.rel, use ssGet bridge
          apply (ssGet_buildSubstMap_of_all_rel dtc.rel w
            (fun e => e.eval σ_o am_t = σ_t w)
            (fun hnotin => absurd hmem_w (hnotin e_w))
            (fun e_o' he => (hcons e_o' w he).symm)))
      have htrans_sub := Expr.substSym_sound transSS e_t σ_t σ_t' am_t
        (fun w => hrepr_trans w)
      calc e_o.eval σ_o' am_t
          = (e_o.substSym origSS).eval σ_o am_t := horig_sub.symm
        _ = ((e_t.substSym transSS).substSym preSubst).eval σ_o am_t := heval_eq
        _ = (e_t.substSym transSS).eval σ_t am_t := hpre_sub
        _ = e_t.eval σ_t' am_t := htrans_sub
    -- Directly prove membership-based goal
    intro e_o v hmem
    -- hpair_sound gives: e_o.eval σ_o' am_t = (.var v).eval σ_t' am_t = σ_t' v
    have hpair := hpair_sound e_o (.var v) hmem
    simp only [Expr.eval] at hpair
    -- Bridge am_t to am_o' using eval_noArrRead
    have hnoarr_eo : e_o.hasArrRead = false := by
      rw [List.all_eq_true] at hnoarr_rel_next
      have := hnoarr_rel_next (e_o, Expr.var v) hmem
      simp at this; exact this
    rw [hpair.symm]
    exact Expr.eval_noArrRead e_o σ_o' am_t am_o' hnoarr_eo
  · -- Array memory equality: am_t' = am_o'
    obtain ⟨hlen_eq, ham_pairs⟩ := checkRelConsistency_amCheck dc.orig dic.pc_orig
      dtc.origLabels instr (dc.inv_orig.getD dic.pc_orig ([] : EInv)) dtc.rel dtc.rel_next hrelcheck
    by_cases harrst : ∃ arr idx val ty, instr = .arrStore arr idx val ty
    · -- arrStore: both sides write the same array at the same index with the same value
      obtain ⟨arr_t, idx_t, val_t, ty_t, rfl⟩ := harrst
      obtain ⟨iv_t, hidx_t, ham_t'_eq, hσ_eq⟩ := arrStore_step_values hinstr hstep
      -- transSAM = [(arr_t, .var idx_t, .var val_t)], origSAM has length 1
      simp only [execSymbolic] at hlen_eq ham_pairs
      -- Extract the single origSAM entry
      obtain ⟨⟨arr_o, idx_o, val_o⟩, horigSAM_eq⟩ : ∃ e,
          (execPath dc.orig ([] : SymStore) ([] : SymArrayMem) dic.pc_orig dtc.origLabels).2 = [e] := by
        match hsam : (execPath dc.orig ([] : SymStore) ([] : SymArrayMem) dic.pc_orig dtc.origLabels).2 with
        | [e] => exact ⟨e, rfl⟩
        | [] => rw [hsam] at hlen_eq; simp at hlen_eq
        | _ :: _ :: _ => rw [hsam] at hlen_eq; simp at hlen_eq
      rw [horigSAM_eq] at hsamCoh_final ham_pairs
      -- Decompose SamCoherent singleton into a single write
      obtain ⟨bv, hval_eval, ham_o'_eq⟩ := samCoherent_singleton hsamCoh_final
      rw [ham_t'_eq, ham_o'_eq]
      -- Extract matching conditions from ham_pairs
      simp only [List.zip, List.zipWith, List.all, Bool.and_eq_true] at ham_pairs
      obtain ⟨⟨⟨harr_eq, hidx_match⟩, hval_match⟩, _⟩ := ham_pairs
      -- arr_o = arr_t
      have harr := beq_iff_eq.mp harr_eq
      rw [harr]; congr 1
      · -- Index: idx_o.eval σ_o am_t = .int iv_t, so .toInt matches iv_t
        have h_idx_simp := beq_iff_eq.mp hidx_match
        have hlhs := Expr.simplifyDeep_sound (sdFuel inv_o) inv_o idx_o σ_o am_t hinv_o
        have hrhs := Expr.simplifyDeep_sound (sdFuel inv_o) inv_o
          ((ssGet ([] : SymStore) idx_t).substSym (buildSubstMap dtc.rel)) σ_o am_t hinv_o
        rw [h_idx_simp] at hlhs
        have heq_eval : idx_o.eval σ_o am_t =
            ((ssGet ([] : SymStore) idx_t).substSym (buildSubstMap dtc.rel)).eval σ_o am_t :=
          hlhs.symm.trans hrhs
        -- Relate substSym eval to σ_t via amFvCheck membership
        have hamFv := checkRelConsistency_amFvCheck dc.orig dic.pc_orig dtc.origLabels _
          inv_o dtc.rel dtc.rel_next hrelcheck
        have hsubst_eq : ((ssGet ([] : SymStore) idx_t).substSym (buildSubstMap dtc.rel)).eval σ_o am_t =
            σ_t idx_t := by
          change (ssGet (buildSubstMap dtc.rel) idx_t).eval σ_o am_t = σ_t idx_t
          -- From amFvCheck: idx_t has a pair in dtc.rel (since .var idx_t has freeVar [idx_t])
          simp only [execSymbolic] at hamFv
          rw [List.all_eq_true] at hamFv
          have hentry := hamFv (arr_t, .var idx_t, .var val_t) (List.mem_singleton.mpr rfl)
          rw [Bool.and_eq_true] at hentry
          obtain ⟨hidx_all, _⟩ := hentry
          rw [List.all_eq_true] at hidx_all
          have hidx_cov := hidx_all idx_t (List.mem_singleton.mpr rfl)
          rw [List.any_eq_true] at hidx_cov
          obtain ⟨⟨e_w, e_tw⟩, hmem_w, hbeq⟩ := hidx_cov
          have htw : e_tw = .var idx_t := beq_iff_eq.mp hbeq; subst htw
          exact (ssGet_buildSubstMap_of_all_rel dtc.rel idx_t
            (fun e => e.eval σ_o am_t = σ_t idx_t)
            (fun hnotin => absurd hmem_w (hnotin e_w))
            (fun e_o' he => (hcons e_o' idx_t he).symm))
        rw [heq_eval, hsubst_eq, hidx_t]; rfl
      · -- Value: val_o.eval σ_o am_t = .int bv, and (σ_t val_t).toBits matches bv
        have h_val_simp := beq_iff_eq.mp hval_match
        have hlhs := Expr.simplifyDeep_sound (sdFuel inv_o) inv_o val_o σ_o am_t hinv_o
        have hrhs := Expr.simplifyDeep_sound (sdFuel inv_o) inv_o
          ((ssGet ([] : SymStore) val_t).substSym (buildSubstMap dtc.rel)) σ_o am_t hinv_o
        rw [h_val_simp] at hlhs
        have heq_eval : val_o.eval σ_o am_t =
            ((ssGet ([] : SymStore) val_t).substSym (buildSubstMap dtc.rel)).eval σ_o am_t :=
          hlhs.symm.trans hrhs
        have hamFv := checkRelConsistency_amFvCheck dc.orig dic.pc_orig dtc.origLabels _
          inv_o dtc.rel dtc.rel_next hrelcheck
        have hsubst_eq : ((ssGet ([] : SymStore) val_t).substSym (buildSubstMap dtc.rel)).eval σ_o am_t =
            σ_t val_t := by
          change (ssGet (buildSubstMap dtc.rel) val_t).eval σ_o am_t = σ_t val_t
          simp only [execSymbolic] at hamFv
          rw [List.all_eq_true] at hamFv
          have hentry := hamFv (arr_t, .var idx_t, .var val_t) (List.mem_singleton.mpr rfl)
          rw [Bool.and_eq_true] at hentry
          obtain ⟨_, hval_all⟩ := hentry
          rw [List.all_eq_true] at hval_all
          have hval_cov := hval_all val_t (List.mem_singleton.mpr rfl)
          rw [List.any_eq_true] at hval_cov
          obtain ⟨⟨e_w, e_tw⟩, hmem_w, hbeq⟩ := hval_cov
          have htw : e_tw = .var val_t := beq_iff_eq.mp hbeq; subst htw
          exact (ssGet_buildSubstMap_of_all_rel dtc.rel val_t
            (fun e => e.eval σ_o am_t = σ_t val_t)
            (fun hnotin => absurd hmem_w (hnotin e_w))
            (fun e_o' he => (hcons e_o' val_t he).symm))
        -- Goal: (σ_t val_t).toBits = bv
        rw [← hsubst_eq, ← heq_eval]; exact hval_eval
    · -- non-arrStore: am unchanged on both sides
      push_neg at harrst
      have ham_t'_eq : am_t' = am_t := step_am_preserved hstep
        (fun arr idx val ty h => harrst arr idx val ty (by rw [hinstr] at h; exact Option.some.inj h))
      have htransSAM_nil : (execSymbolic ([] : SymStore) ([] : SymArrayMem) instr).2 = [] := by
        cases instr with
        | arrStore => exact absurd rfl (harrst _ _ _ _)
        | const x v => cases v <;> rfl
        | _ => rfl
      have horigSAM_nil : (execPath dc.orig ([] : SymStore) ([] : SymArrayMem) dic.pc_orig dtc.origLabels).2 = [] := by
        have hlen0 : (execPath dc.orig ([] : SymStore) ([] : SymArrayMem) dic.pc_orig dtc.origLabels).2.length = 0 := by
          rw [hlen_eq, htransSAM_nil]; rfl
        match h : (execPath dc.orig ([] : SymStore) ([] : SymArrayMem) dic.pc_orig dtc.origLabels).2 with
        | [] => rfl
        | _ :: _ => rw [h] at hlen0; simp at hlen0
      rw [horigSAM_nil] at hsamCoh_final
      rw [ham_t'_eq, samCoherent_nil_am_eq hsamCoh_final]

/-- Extract Bool information from checkAllTransitionsExec for a specific step.
    Either the successor edge is statically dead (its transition is skipped) or a
    satisfying transition certificate exists. -/
private theorem extractTransCheck (dc : ECertificate)
    (h : checkAllTransitionsExec dc = true)
    (pc_t pc_t' : Label) (instr : TAC)
    (hinstr : dc.trans[pc_t]? = some instr)
    (hne : instr ≠ .halt)
    (hsucc : pc_t' ∈ instr.successors pc_t) :
    (isDeadSuccExec instr pc_t pc_t'
        (FastVarMap.ofList (dc.inv_trans.getD pc_t ([] : EInv)))
        (sdFuel (dc.inv_trans.getD pc_t ([] : EInv))) = true) ∨
    (∃ dic, dc.instrCerts[pc_t]? = some dic ∧
    ∃ dtc ∈ dic.transitions,
      dtc.rel = dic.rel ∧
      dtc.rel_next = (dc.instrCerts.getD pc_t' default).rel ∧
      checkOrigPath dc.orig ([] : SymStore) ([] : SymArrayMem) (dc.inv_orig.getD dic.pc_orig ([] : EInv))
        dic.pc_orig dtc.origLabels (dc.instrCerts.getD pc_t' default).pc_orig
        (branchInfoWithRel instr dic.rel pc_t pc_t') = true ∧
      checkRelConsistency
        dc.orig dic.pc_orig dtc.origLabels instr
        (dc.inv_orig.getD dic.pc_orig ([] : EInv))
        dtc.rel dtc.rel_next = true) := by
  have hbound := bound_of_getElem? hinstr
  unfold checkAllTransitionsExec at h; rw [List.all_eq_true] at h
  have hpc := h pc_t (List.mem_range.mpr hbound)
  rw [hinstr] at hpc
  -- Case split on instr to reduce the outer match on `some instr`
  revert hpc; cases instr with
  | halt => exact absurd rfl hne
  | ifgoto x l =>
    intro hpc
    cases hdic : dc.instrCerts[pc_t]? with
    | none => simp only [hdic] at hpc; exact absurd hpc (by decide)
    | some dic =>
      simp only [hdic] at hpc; rw [List.all_eq_true] at hpc
      have hitem := hpc pc_t' hsucc
      rcases Bool.or_eq_true _ _ |>.mp hitem with hdead | hany
      · exact Or.inl hdead
      · rw [List.any_eq_true] at hany
        obtain ⟨dtc, hdtc_mem, hdtc_check⟩ := hany
        rw [Bool.and_eq_true] at hdtc_check
        obtain ⟨h123, hrel_check⟩ := hdtc_check
        rw [Bool.and_eq_true] at h123
        obtain ⟨h12, hpath⟩ := h123
        rw [Bool.and_eq_true] at h12
        obtain ⟨hrel_eq, hrel_next_eq⟩ := h12
        rw [checkOrigPathFast_eq_checkOrigPath] at hpath
        exact Or.inr ⟨dic, rfl, dtc, hdtc_mem,
          beq_iff_eq.mp hrel_eq, beq_iff_eq.mp hrel_next_eq, hpath, hrel_check⟩
  | _ =>
    intro hpc
    cases hdic : dc.instrCerts[pc_t]? with
    | none => simp only [hdic] at hpc; exact absurd hpc (by decide)
    | some dic =>
      simp only [hdic] at hpc; rw [List.all_eq_true] at hpc
      have hitem := hpc pc_t' hsucc
      rcases Bool.or_eq_true _ _ |>.mp hitem with hdead | hany
      · exact Or.inl hdead
      · rw [List.any_eq_true] at hany
        obtain ⟨dtc, hdtc_mem, hdtc_check⟩ := hany
        rw [Bool.and_eq_true] at hdtc_check
        obtain ⟨h123, hrel_check⟩ := hdtc_check
        rw [Bool.and_eq_true] at h123
        obtain ⟨h12, hpath⟩ := h123
        rw [Bool.and_eq_true] at h12
        obtain ⟨hrel_eq, hrel_next_eq⟩ := h12
        rw [checkOrigPathFast_eq_checkOrigPath] at hpath
        exact Or.inr ⟨dic, rfl, dtc, hdtc_mem,
          beq_iff_eq.mp hrel_eq, beq_iff_eq.mp hrel_next_eq, hpath, hrel_check⟩

/-- Relate getD to getElem? for arrays. -/
private theorem array_getD_of_getElem? {α : Type} {arr : Array α} {n : Nat} {val d : α}
    (h : arr[n]? = some val) : arr.getD n d = val := by
  have hb := bound_of_getElem? h
  have heq := (getElem?_eq_some_iff.mp h).2
  simp [Array.getD, dif_pos hb, heq]

/-- Extract per-pc info from checkOrigPathBoundsOk:
    if orig at dic.pc_orig is an array op, then trans at pc_t must be an array op;
    and all intermediate orig path labels have scalar instructions. -/
private theorem checkOrigPathBoundsOk_extract (dc : ECertificate)
    (h : checkOrigPathBoundsOk dc = true)
    (pc_t : Label) (hpc : pc_t < dc.trans.size)
    (hinstr : dc.trans[pc_t]? = some instr) (hne : instr ≠ .halt)
    (hdic : dc.instrCerts[pc_t]? = some dic) :
    -- Part 1: orig scalar or trans is array op
    ((∀ i, dc.orig[dic.pc_orig]? = some i → i.isScalar = true) ∨
     (∃ x arr idx ty, instr = .arrLoad x arr idx ty) ∨
     (∃ arr idx val ty, instr = .arrStore arr idx val ty)) ∧
    -- Part 2: intermediate orig path labels are scalar and non-div/mod
    (∀ dtc ∈ dic.transitions, ∀ l ∈ dtc.origLabels.dropLast,
        (∀ i, dc.orig[l]? = some i → i.isScalar = true) ∧
        (∀ x y z, dc.orig[l]? ≠ some (.binop x .div y z) ∧
                   dc.orig[l]? ≠ some (.binop x .mod y z))) := by
  unfold checkOrigPathBoundsOk at h
  have hpb := (List.all_eq_true.mp h) pc_t (List.mem_range.mpr hpc)
  simp only [hinstr] at hpb
  simp only [hdic] at hpb
  rw [Bool.and_eq_true] at hpb
  obtain ⟨hfirst, hrest⟩ := hpb
  constructor
  · -- Part 1: orig scalar or trans is array op
    cases instr with
    | arrLoad x arr idx ty => exact Or.inr (Or.inl ⟨x, arr, idx, ty, rfl⟩)
    | arrStore arr idx val ty => exact Or.inr (Or.inr ⟨arr, idx, val, ty, rfl⟩)
    | halt => exact absurd rfl hne
    | _ =>
      left; intro i hi; revert hfirst; rw [hi]
      cases i <;> simp [TAC.isScalar]
  · -- Part 2: intermediate labels are scalar and non-div/mod
    intro dtc hmem l hmem_l
    have htc := (List.all_eq_true.mp hrest) dtc hmem
    have hcheck := List.all_eq_true.mp htc l hmem_l
    constructor
    · intro i hi; revert hcheck; rw [hi]
      cases i with
      | binop x op y z => cases op <;> simp [TAC.isScalar]
      | _ => simp [TAC.isScalar]
    · intro x y z; constructor <;> (intro heq; have := List.all_eq_true.mp htc l hmem_l; rw [heq] at this; simp at this)

/-- When `computeNextPC` statically resolves an instruction's successor (the branch
    guard is constant under `inv`, or the instruction is unconditional), any actual
    run-step from a state satisfying `inv` lands at exactly that successor. Used to
    show no run takes a statically-dead `ifgoto` edge. -/
private theorem step_target_eq_computeNextPC {p : Prog} {pc pc' : Label}
    {σ σ' : Store} {am am' : ArrayMem} {instr : TAC} {inv : EInv} {pc_det : Label}
    (hinstr : p[pc]? = some instr)
    (hstep : Step p (Cfg.run pc σ am) (Cfg.run pc' σ' am'))
    (hinv : EInv.toProp inv σ am)
    (hcn : computeNextPC instr pc ([] : SymStore) inv = some pc_det) :
    pc' = pc_det := by
  have hrepr : ∀ v, (ssGet ([] : SymStore) v).eval σ am = σ v := fun _ => rfl
  cases hstep with
  | const h => rw [hinstr] at h; injection h with he; subst he
               simp only [computeNextPC, Option.some.injEq] at hcn; omega
  | copy h => rw [hinstr] at h; injection h with he; subst he
              simp only [computeNextPC, Option.some.injEq] at hcn; omega
  | binop h _ _ _ => rw [hinstr] at h; injection h with he; subst he
                     simp only [computeNextPC, Option.some.injEq] at hcn; omega
  | boolop h => rw [hinstr] at h; injection h with he; subst he
                simp only [computeNextPC, Option.some.injEq] at hcn; omega
  | goto h => rw [hinstr] at h; injection h with he; subst he
              simp only [computeNextPC, Option.some.injEq] at hcn; omega
  | arrLoad h _ _ => rw [hinstr] at h; injection h with he; subst he
                     simp only [computeNextPC, Option.some.injEq] at hcn; omega
  | arrStore h _ _ _ => rw [hinstr] at h; injection h with he; subst he
                        simp only [computeNextPC, Option.some.injEq] at hcn; omega
  | fbinop h _ _ => rw [hinstr] at h; injection h with he; subst he
                    simp only [computeNextPC, Option.some.injEq] at hcn; omega
  | intToFloat h _ => rw [hinstr] at h; injection h with he; subst he
                      simp only [computeNextPC, Option.some.injEq] at hcn; omega
  | floatToInt h _ => rw [hinstr] at h; injection h with he; subst he
                      simp only [computeNextPC, Option.some.injEq] at hcn; omega
  | floatUnary h _ => rw [hinstr] at h; injection h with he; subst he
                      simp only [computeNextPC, Option.some.injEq] at hcn; omega
  | fternop h _ _ _ => rw [hinstr] at h; injection h with he; subst he
                       simp only [computeNextPC, Option.some.injEq] at hcn; omega
  | print h => rw [hinstr] at h; injection h with he; subst he
               simp only [computeNextPC, Option.some.injEq] at hcn; omega
  | printInt h => rw [hinstr] at h; injection h with he; subst he
                  simp only [computeNextPC, Option.some.injEq] at hcn; omega
  | printBool h => rw [hinstr] at h; injection h with he; subst he
                   simp only [computeNextPC, Option.some.injEq] at hcn; omega
  | printFloat h => rw [hinstr] at h; injection h with he; subst he
                    simp only [computeNextPC, Option.some.injEq] at hcn; omega
  | printString h => rw [hinstr] at h; injection h with he; subst he
                     simp only [computeNextPC, Option.some.injEq] at hcn; omega
  | iftrue h hb =>
    rw [hinstr] at h; injection h with he; subst he
    simp only [computeNextPC] at hcn
    split at hcn <;>
      first
      | (simp only [Option.some.injEq] at hcn; omega)
      | (rename_i heq
         have hs := BoolExpr.symEval_sound _ ([] : SymStore) inv σ σ am hrepr hinv true heq
         rw [hb] at hs; exact absurd hs (by decide))
      | (rename_i heq
         have hs := BoolExpr.symEval_sound _ ([] : SymStore) inv σ σ am hrepr hinv false heq
         rw [hb] at hs; exact absurd hs (by decide))
      | simp at hcn
  | iffall h hb =>
    rw [hinstr] at h; injection h with he; subst he
    simp only [computeNextPC] at hcn
    split at hcn <;>
      first
      | (simp only [Option.some.injEq] at hcn; omega)
      | (rename_i heq
         have hs := BoolExpr.symEval_sound _ ([] : SymStore) inv σ σ am hrepr hinv true heq
         rw [hb] at hs; exact absurd hs (by decide))
      | (rename_i heq
         have hs := BoolExpr.symEval_sound _ ([] : SymStore) inv σ σ am hrepr hinv false heq
         rw [hb] at hs; exact absurd hs (by decide))
      | simp at hcn

/-- **Condition 3**: checkAllTransitionsExec → checkAllTransitionsProp -/
theorem checkAllTransitionsExec_sound (dc : ECertificate)
    (hwtp : WellTypedProg dc.tyCtx dc.orig)
    (hnoarr_orig : checkNoArrReadInInvs dc.inv_orig = true)
    (hnoarr_rels : checkNoArrReadInRels dc.instrCerts = true)
    (hbndpres : checkBoundsPreservationExec dc = true)
    (harrsize : checkArraySizesExec dc = true)
    (hdivpres : checkDivPreservationExec dc = true)
    (hpathbounds : checkOrigPathBoundsOk dc = true)
    (hboolnoarr_orig : checkBoolExprNoArrRead dc.orig = true)
    (hboolnoarr_trans : checkBoolExprNoArrRead dc.trans = true)
    (hboolvarscov : checkBoolVarsCoveredExec dc = true)
    (h : checkAllTransitionsExec dc = true) :
    checkAllTransitionsProp dc.tyCtx (toPCertificate dc) := by
  intro pc_t σ_t σ_t' pc_t' am_t am_t' hinv_t hstep
  obtain ⟨instr, hinstr⟩ := step_run_instr hstep
  have hne_halt : instr ≠ .halt := by
    intro heq; subst heq
    exact Cfg.noConfusion (Step.deterministic (Step.halt hinstr) hstep)
  have hsucc := step_successor hstep hinstr
  -- Extract Bool-level information; either the edge is statically dead (skipped) or
  -- a transition certificate exists. A dead edge is vacuous: `inv_trans` determines
  -- control elsewhere, so no run from `σ_t ⊨ inv_trans` takes it.
  rcases extractTransCheck dc h pc_t pc_t' instr hinstr hne_halt hsucc with hdead | hex
  · exfalso
    unfold isDeadSuccExec at hdead
    rw [computeNextPCFast_eq_computeNextPC] at hdead
    cases hcn : computeNextPC instr pc_t ([] : SymStore) (dc.inv_trans.getD pc_t ([] : EInv)) with
    | none => rw [hcn] at hdead; simp at hdead
    | some pc_det =>
      rw [hcn] at hdead
      have hne' : pc_det ≠ pc_t' := by simpa using hdead
      have hinv_t' : EInv.toProp (dc.inv_trans.getD pc_t ([] : EInv)) σ_t am_t := hinv_t
      exact hne' (step_target_eq_computeNextPC hinstr hstep hinv_t' hcn).symm
  obtain ⟨dic, hdic, dtc, hdtc_mem, hrel_eq, hrel_next_eq, hpath, hrelcheck⟩ := hex
  -- The tc in toPCertificate's transitions that corresponds to dtc
  let tc : PTransCorr :=
    { origLabels := dtc.origLabels
      storeRel := eRelToStoreRel dtc.rel
      storeRel_next := eRelToStoreRel dtc.rel_next }
  -- Show tc is in (toPCertificate dc).instrCerts pc_t).transitions
  have hgetD : dc.instrCerts.getD pc_t default = dic := array_getD_of_getElem? hdic
  have htc_mem : tc ∈ ((toPCertificate dc).instrCerts pc_t).transitions := by
    simp only [toPCertificate, hgetD]
    show tc ∈ dic.transitions.map _
    exact List.mem_map.mpr ⟨dtc, hdtc_mem, rfl⟩
  refine ⟨tc, htc_mem, ?_, ?_, ?_⟩
  -- 1. tc.storeRel = ic.storeRel
  · simp only [toPCertificate, hgetD, tc]
    exact congrArg eRelToStoreRel hrel_eq
  -- 2. tc.storeRel_next = ic'.storeRel
  · simp only [toPCertificate, tc]
    exact congrArg eRelToStoreRel hrel_next_eq
  -- 3. checkTransitionRelProp
  · -- Use the branchInfo with the actual rel (dtc.rel = dic.rel)
    have hpath' : checkOrigPath dc.orig ([] : SymStore) ([] : SymArrayMem) (dc.inv_orig.getD dic.pc_orig ([] : EInv))
        dic.pc_orig dtc.origLabels (dc.instrCerts.getD pc_t' default).pc_orig
        (branchInfoWithRel instr dtc.rel pc_t pc_t') = true := by
      rw [hrel_eq]; exact hpath
    simp only [toPCertificate, hgetD]
    -- Extract arrRead-free conditions for dtc's relations from hnoarr_rels
    have hnoarr_dtc : dtc.rel.all (fun (e, _) => !e.hasArrRead) = true ∧
        dtc.rel_next.all (fun (e, _) => !e.hasArrRead) = true := by
      unfold checkNoArrReadInRels at hnoarr_rels
      have hbound := bound_of_getElem? hdic
      have hget := (Array.getElem?_eq_some_iff.mp hdic).2
      have hic := (Array.all_eq_true.mp hnoarr_rels) pc_t hbound
      rw [hget, Bool.and_eq_true] at hic
      have htrans_all := List.all_eq_true.mp hic.2 dtc hdtc_mem
      rw [Bool.and_eq_true] at htrans_all
      exact htrans_all
    have hnoarr_dtc_rel := hnoarr_dtc.1
    have hnoarr_dtc_rel_next := hnoarr_dtc.2
    -- Extract per-pc info from checkOrigPathBoundsOk
    have ⟨hOrigFirstOk, hRestAll⟩ := checkOrigPathBoundsOk_extract dc hpathbounds
      pc_t (bound_of_getElem? hinstr) hinstr hne_halt hdic
    -- hRestScalar and hRestNoDivMod for this specific dtc
    have hRestScalar : ∀ l ∈ dtc.origLabels.dropLast,
        ∀ i, dc.orig[l]? = some i → i.isScalar = true :=
      fun l hmem => (hRestAll dtc hdtc_mem l hmem).1
    have hRestNoDivMod : ∀ l ∈ dtc.origLabels.dropLast, ∀ x y z,
        dc.orig[l]? ≠ some (.binop x .div y z) ∧ dc.orig[l]? ≠ some (.binop x .mod y z) :=
      fun l hmem => (hRestAll dtc hdtc_mem l hmem).2
    -- Extract rel equality
    have hrel_eq_dtc : dtc.rel = dic.rel := hrel_eq
    -- BoolExpr free-variable coverage: from checkBoolVarsCoveredExec + dtc.rel = dic.rel
    have hBoolVarsCov : ∀ b l, instr = .ifgoto b l →
        ∀ v, v ∈ b.exprFreeVars → ∃ e_o, (e_o, .var v) ∈ dtc.rel := by
      intro b l heq v hv
      have hcov := checkBoolVarsCoveredExec_sound dc hboolvarscov pc_t b l (by
        simp only [toPCertificate] at hinstr; rw [hinstr, heq])
      -- hcov uses (dc.instrCerts.getD pc_t default).rel = dic.rel = dtc.rel
      rw [array_getD_of_getElem? hdic] at hcov
      rw [← hrel_eq_dtc] at hcov
      exact hcov v hv
    exact transRel_sound dc hwtp hnoarr_orig hbndpres harrsize hdivpres
      pc_t pc_t' dic dtc _ ((dc.instrCerts.getD pc_t' default).pc_orig) hdic
      hnoarr_dtc_rel hnoarr_dtc_rel_next hinstr hOrigFirstOk hrel_eq_dtc hRestScalar hRestNoDivMod
      (checkBoolExprNoArrRead_sound dc.orig hboolnoarr_orig)
      (checkBoolExprNoArrRead_sound dc.trans hboolnoarr_trans)
      hBoolVarsCov
      hpath' hrelcheck

-- ============================================================
-- § 8. Non-termination soundness
-- ============================================================

/-- Helper: extract inner check from checkNonterminationExec for a non-halt instruction.
    Uses definitional equality (match reduction) to convert between the full
    match form and the instrCerts-level check. -/
private theorem nonterm_inner (dc : ECertificate)
    (h : checkNonterminationExec dc = true) (pc_t pc_t' : Label)
    (instr : TAC) (hinstr : dc.trans[pc_t]? = some instr) (hne : instr ≠ .halt)
    (hsucc : pc_t' ∈ instr.successors pc_t)
    (horig_eq : (dc.instrCerts.getD pc_t default).pc_orig =
                (dc.instrCerts.getD pc_t' default).pc_orig) :
    dc.measure.getD pc_t' 0 < dc.measure.getD pc_t 0 := by
  have hbound := bound_of_getElem? hinstr
  unfold checkNonterminationExec at h; rw [List.all_eq_true] at h
  have hpc := h pc_t (List.mem_range.mpr hbound)
  rw [hinstr] at hpc
  -- hpc has: (match some instr with | some .halt => ... | some i => body i | none => ...) = true
  -- For each non-halt constructor, Lean definitionally reduces match some (.const/copy/...)
  -- to the non-halt branch. Use `cases instr` + `exact hpc` to let the kernel reduce.
  -- First extract the body for the instrCerts match:
  suffices h_inner : ∀ pc_t' ∈ instr.successors pc_t,
      (match dc.instrCerts[pc_t]? with
       | some ic =>
         let ic' := dc.instrCerts.getD pc_t' default
         if ic.pc_orig == ic'.pc_orig then
           decide (dc.measure.getD pc_t' 0 < dc.measure.getD pc_t 0)
         else true
       | none => false) = true by
    have hitem := h_inner pc_t' hsucc
    revert hitem
    cases hic : dc.instrCerts[pc_t]? with
    | none => simp
    | some ic =>
      have hgetD : dc.instrCerts.getD pc_t default = ic := by
        simp [Array.getD, dif_pos (bound_of_getElem? hic)]
        exact (Array.getElem?_eq_some_iff.mp hic).2
      rw [hgetD] at horig_eq
      simp only [beq_iff_eq.mpr horig_eq, ↓reduceIte]
      exact of_decide_eq_true
  -- Prove h_inner: extract from hpc via List.all and match reduction
  intro pc_t'' hmem
  -- hpc has the full match on some instr; after cases on instr, it reduces
  -- definitionally to the instrCerts-level check
  revert hpc; cases instr with
  | halt => exact absurd rfl hne
  | _ =>
    intro hpc
    -- For non-halt constructors, the kernel reduces the match on some (.const/copy/...)
    -- Use `generalize` to abstract the instrCerts lookup, then `exact` uses definitional eq
    revert hmem
    generalize dc.instrCerts[pc_t]? = opt_ic at hpc ⊢
    cases opt_ic with
    | none => simp at hpc
    | some ic =>
      rw [List.all_eq_true] at hpc
      exact hpc pc_t''

/-- **Condition 5**: checkNonterminationExec → checkNonterminationProp -/
theorem checkNonterminationExec_sound (dc : ECertificate)
    (h : checkNonterminationExec dc = true) :
    checkNonterminationProp (toPCertificate dc) := by
  intro pc_t pc_t' σ_t σ_t' σ_o am_t am_o _ _ _ hexec horig_eq
  obtain ⟨c', hstep, am_t', hc'⟩ := hexec; subst hc'
  dsimp only [toPCertificate] at horig_eq ⊢
  obtain ⟨instr, hinstr⟩ := step_run_instr hstep
  have hinstr' : dc.trans[pc_t]? = some instr := hinstr
  have not_halt : instr ≠ .halt := by
    intro heq; subst heq
    exact Cfg.noConfusion (Step.deterministic hstep (Step.halt hinstr))
  exact nonterm_inner dc h pc_t pc_t' instr hinstr' not_halt
    (step_successor hstep hinstr) horig_eq

-- ============================================================
-- § 8b. Div-preservation soundness
-- ============================================================

theorem checkDivPreservationExec_sound (dc : ECertificate)
    (h : checkDivPreservationExec dc = true)
    (hbndpres : checkBoundsPreservationExec dc = true)
    (harrsize : checkArraySizesExec dc = true)
    (hwtp : WellTypedProg dc.tyCtx dc.orig) :
    checkErrorPreservationProp (toPCertificate dc) := by
  intro pc_t σ_t σ_o am_t am_o hpc_bound hrel _hinv_t hinv_o htyped
  -- Normalize toPCertificate projections
  simp only [toCertificate_trans] at hpc_bound
  simp only [toCertificate_tyCtx] at htyped
  simp only [toPCertificate] at hrel
  set ic := dc.instrCerts.getD pc_t default with hic_def
  refine ⟨?divBranch, ?boundsBranch⟩
  case divBranch =>
    intro hstep
    simp only [toCertificate_trans] at hstep
    simp only [toPCertificate]
    cases hstep with
    | binop_divByZero hinstr hya hzb hunsafe =>
      rename_i _ op y z a b
      -- Extract div-preservation checker info for pc_t
      simp only [checkDivPreservationExec, List.all_eq_true, List.mem_range] at h
      have hpc := h pc_t hpc_bound; rw [hinstr] at hpc
      generalize horig : dc.orig[ic.pc_orig]? = oi at hpc
      cases oi with
      | none => simp at hpc
      | some instr_o =>
        cases instr_o with
        | binop x' op' y' z' =>
          rw [Bool.and_eq_true] at hpc; obtain ⟨hop_eq, hrest⟩ := hpc
          have hop : op = op' := beq_iff_eq.mp hop_eq
          have : op = .div ∨ op = .mod := by
            cases op with
            | add | sub | mul | band | bor | bxor | shl | shr => exact absurd True.intro hunsafe
            | div => exact Or.inl rfl
            | mod => exact Or.inr rfl
          rcases this with rfl | rfl <;> (
            rw [Bool.and_eq_true] at hrest; obtain ⟨hy_eq, hz_eq⟩ := hrest
            rw [Bool.or_eq_true] at hy_eq
            -- Dividend correspondence: σ_o y' = .int a, from relFindOrigVar OR the
            -- hoisted-constant fallback (orig invariant + relation literals agree).
            have hya' : σ_o y' = .int a := by
              rcases hy_eq with hy_var | hinv_case
              · have hy_find := beq_iff_eq.mp hy_var
                have hσt_y := store_eq_of_relFindOrigVar hy_find hrel
                rw [← hσt_y]; exact hya
              · generalize hfind_inv : (dc.inv_orig.getD ic.pc_orig ([] : EInv)).find?
                    (fun (v, _) => v == y') = fi at hinv_case
                cases fi with
                | none => simp at hinv_case
                | some p =>
                  obtain ⟨v, e⟩ := p
                  cases e with
                  | lit c =>
                    generalize hfind_rel : relFindOrigExpr ic.rel y = fr at hinv_case
                    cases fr with
                    | none => simp at hinv_case
                    | some e' =>
                      cases e' with
                      | lit c' =>
                        simp at hinv_case
                        have hpred := List.find?_some hfind_inv
                        simp at hpred; symm at hpred; subst hpred
                        have hmem := List.mem_of_find?_eq_some hfind_inv
                        simp only [toPCertificate] at hinv_o
                        have hinv_entry := hinv_o (y', .lit c) hmem
                        simp [Expr.eval] at hinv_entry
                        have hmem_rel := relFindOrigExpr_mem hfind_rel
                        have hσt := hrel _ _ hmem_rel
                        simp [Expr.eval] at hσt
                        have hac : a = c' := Value.int.inj (hya.symm.trans hσt)
                        rw [hinv_entry, hac, hinv_case]
                      | _ => simp at hinv_case
                  | _ => simp at hinv_case
            rw [Bool.or_eq_true] at hz_eq
            rcases hz_eq with hz_var | hz_conj
            · -- relFindOrigVar succeeds: same as before
              have hz_find : relFindOrigVar ic.rel z = some z' := beq_iff_eq.mp hz_var
              have hσt_z := store_eq_of_relFindOrigVar hz_find hrel
              have hzb' : σ_o z' = .int b := by rw [← hσt_z]; exact hzb
              exact ⟨σ_o, am_o, Steps.single (Step.binop_divByZero horig hya' hzb' (hop ▸ hunsafe))⟩
            · -- Conjunction fallback: relFindOrigExpr gives contradiction
              rw [Bool.and_eq_true] at hz_conj
              obtain ⟨hz_rel_lit, _⟩ := hz_conj
              -- Extract the literal from relFindOrigExpr
              generalize hfre : relFindOrigExpr ic.rel z = fre at hz_rel_lit
              cases fre with
              | none => simp at hz_rel_lit
              | some e =>
                cases e with
                | lit c =>
                  -- (.lit c, .var z) ∈ rel, so σ_t z = .int c
                  have hmem := relFindOrigExpr_mem hfre
                  have hσt_z := hrel _ _ hmem
                  simp [Expr.eval] at hσt_z  -- hσt_z : σ_t z = .int c
                  -- But σ_t z = .int b from the step, so b = c
                  have hbc : b = c := Value.int.inj (hzb.symm.trans hσt_z)
                  -- And c ≠ 0 from the checker
                  simp at hz_rel_lit  -- hz_rel_lit : c ≠ 0
                  -- So b ≠ 0, meaning op.safe a b = true, contradicting hunsafe
                  subst hbc; simp [BinOp.safe] at hunsafe; exact absurd hunsafe hz_rel_lit
                | _ => simp at hz_rel_lit)
        | const => simp at hpc
        | copy => simp at hpc
        | boolop => simp at hpc
        | goto => simp at hpc
        | ifgoto => simp at hpc
        | halt => simp at hpc
        | arrLoad => simp at hpc
        | arrStore => simp at hpc
        | fbinop => simp at hpc
        | fternop => simp at hpc
        | intToFloat => simp at hpc
        | floatToInt => simp at hpc
        | floatUnary => simp at hpc
        | print => simp at hpc
        | printInt => simp at hpc
        | printBool => simp at hpc
        | printFloat => simp at hpc
        | printString => simp at hpc
  case boundsBranch =>
    intro hstep
    simp only [toCertificate_trans] at hstep
    simp only [toPCertificate]
    cases hstep with
    | arrLoad_boundsError hinstr hidx_val hbnd_fail =>
      rename_i idxVal arr _ idx _
      -- Extract bounds-preservation checker info for pc_t
      simp only [checkBoundsPreservationExec, List.all_eq_true, List.mem_range] at hbndpres
      have hpc := hbndpres pc_t hpc_bound; rw [hinstr] at hpc
      generalize horig : dc.orig[ic.pc_orig]? = oi at hpc
      cases oi with
      | none => simp at hpc
      | some instr_o =>
        cases instr_o with
        | arrLoad x' arr' idx' ty' =>
          rw [Bool.and_eq_true] at hpc; obtain ⟨harr_eq, hidx_eq⟩ := hpc
          have harr : arr = arr' := beq_iff_eq.mp harr_eq
          -- Index mapping: either relFindOrigVar or invariant-based constant match
          rw [Bool.or_eq_true] at hidx_eq
          have hidx' : σ_o idx' = .int idxVal := by
            rcases hidx_eq with hvar | hinv_case
            · have hidx_find : relFindOrigVar ic.rel idx = some idx' := beq_iff_eq.mp hvar
              have hσt_idx := store_eq_of_relFindOrigVar hidx_find hrel
              rw [← hσt_idx]; exact hidx_val
            · -- Both indices are the same constant from invariant and relation
              generalize hfind_inv : (dc.inv_orig.getD ic.pc_orig ([] : EInv)).find?
                (fun (v, _) => v == idx') = fi at hinv_case
              cases fi with
              | none => simp at hinv_case
              | some p =>
                obtain ⟨v, e⟩ := p
                cases e with
                | lit c =>
                  generalize hfind_rel : relFindOrigExpr ic.rel idx = fr at hinv_case
                  cases fr with
                  | none => simp at hinv_case
                  | some e' =>
                    cases e' with
                    | lit c' =>
                      simp at hinv_case
                      -- From invariant: σ_o idx' = .int c
                      have hpred := List.find?_some hfind_inv
                      simp at hpred; symm at hpred; subst hpred
                      have hmem := List.mem_of_find?_eq_some hfind_inv
                      simp only [toPCertificate] at hinv_o
                      have hinv_entry := hinv_o (idx', .lit c) hmem
                      simp [Expr.eval] at hinv_entry
                      -- From relation: σ_t idx = .int c'
                      have hmem_rel := relFindOrigExpr_mem hfind_rel
                      have hσt := hrel _ _ hmem_rel
                      simp [Expr.eval] at hσt  -- hσt : σ_t idx = .int c'
                      -- Combine: idxVal = c' = c, σ_o idx' = .int c
                      have : idxVal = c' := Value.int.inj (hidx_val.symm.trans hσt)
                      rw [hinv_entry, this, hinv_case]
                    | _ => simp at hinv_case
                | _ => simp at hinv_case
          -- Transfer bounds failure via equal array sizes
          simp only [checkArraySizesExec, beq_iff_eq] at harrsize
          have hsize_eq : dc.orig.arraySizeBv arr' = dc.trans.arraySizeBv arr := by
            simp [Prog.arraySizeBv, harr, harrsize]
          have hbnd_fail' : ¬ (idxVal < dc.orig.arraySizeBv arr') := hsize_eq ▸ hbnd_fail
          exact ⟨σ_o, am_o, Steps.single (Step.arrLoad_boundsError horig hidx' hbnd_fail')⟩
        | _ => simp at hpc
    | arrStore_boundsError hinstr hidx_val hty_val hbnd_fail =>
      rename_i _ idxVal arr idx val
      -- Extract bounds-preservation checker info for pc_t
      simp only [checkBoundsPreservationExec, List.all_eq_true, List.mem_range] at hbndpres
      have hpc := hbndpres pc_t hpc_bound; rw [hinstr] at hpc
      generalize horig : dc.orig[ic.pc_orig]? = oi at hpc
      cases oi with
      | none => simp at hpc
      | some instr_o =>
        cases instr_o with
        | arrStore arr' idx' val' ty' =>
          rw [Bool.and_eq_true] at hpc; obtain ⟨harr_eq, hidx_eq⟩ := hpc
          have harr : arr = arr' := beq_iff_eq.mp harr_eq
          -- Index mapping: either relFindOrigVar or invariant-based constant match
          rw [Bool.or_eq_true] at hidx_eq
          have hidx' : σ_o idx' = .int idxVal := by
            rcases hidx_eq with hvar | hinv_case
            · have hidx_find : relFindOrigVar ic.rel idx = some idx' := beq_iff_eq.mp hvar
              have hσt_idx := store_eq_of_relFindOrigVar hidx_find hrel
              rw [← hσt_idx]; exact hidx_val
            · generalize hfind_inv : (dc.inv_orig.getD ic.pc_orig ([] : EInv)).find?
                (fun (v, _) => v == idx') = fi at hinv_case
              cases fi with
              | none => simp at hinv_case
              | some p =>
                obtain ⟨v, e⟩ := p
                cases e with
                | lit c =>
                  generalize hfind_rel : relFindOrigExpr ic.rel idx = fr at hinv_case
                  cases fr with
                  | none => simp at hinv_case
                  | some e' =>
                    cases e' with
                    | lit c' =>
                      simp at hinv_case
                      have hpred := List.find?_some hfind_inv
                      simp at hpred; symm at hpred; subst hpred
                      have hmem := List.mem_of_find?_eq_some hfind_inv
                      simp only [toPCertificate] at hinv_o
                      have hinv_entry := hinv_o (idx', .lit c) hmem
                      simp [Expr.eval] at hinv_entry
                      have hmem_rel := relFindOrigExpr_mem hfind_rel
                      have hσt := hrel _ _ hmem_rel
                      simp [Expr.eval] at hσt
                      have : idxVal = c' := Value.int.inj (hidx_val.symm.trans hσt)
                      rw [hinv_entry, this, hinv_case]
                    | _ => simp at hinv_case
                | _ => simp at hinv_case
          -- Transfer bounds failure via equal array sizes
          simp only [checkArraySizesExec, beq_iff_eq] at harrsize
          have hsize_eq : dc.orig.arraySizeBv arr' = dc.trans.arraySizeBv arr := by
            simp [Prog.arraySizeBv, harr, harrsize]
          have hbnd_fail' : ¬ (idxVal < dc.orig.arraySizeBv arr') := hsize_eq ▸ hbnd_fail
          -- Get (σ_o val').typeOf = ty' from WellTypedProg + TypedStore
          have hpc_lt : ic.pc_orig < dc.orig.size := bound_of_getElem? horig
          have hwti := hwtp ic.pc_orig hpc_lt
          have hinstr_eq : dc.orig[ic.pc_orig] = .arrStore arr' idx' val' ty' :=
            Option.some.inj ((Array.getElem?_eq_getElem hpc_lt).symm.trans horig)
          rw [hinstr_eq] at hwti
          have ⟨_hidx_ty, hval_ty⟩ : dc.tyCtx idx' = .int ∧ dc.tyCtx val' = ty' := by
            cases hwti with | arrStore h1 h2 _ => exact ⟨h1, h2⟩
          have hty' : (σ_o val').typeOf = ty' := by rw [htyped val']; exact hval_ty
          exact ⟨σ_o, am_o, Steps.single (Step.arrStore_boundsError horig hidx' hty' hbnd_fail')⟩
        | _ => simp at hpc

-- ============================================================
-- § 9. Main soundness theorem
-- ============================================================

/-- **Main Theorem**: If the executable checker accepts a certificate,
    then `PCertificateValid` holds for the corresponding Prop-based certificate.

    This connects the executable world (`Bool`) to the proof world (`Prop`):
    running `checkCertificateExec dc = true` is sufficient to guarantee
    that the transformation preserves all program behaviors. -/
-- Helper: decompose a chain of Bool.and into individual conjuncts
private theorem and_true_of_and_eq_true {a b : Bool} (h : (a && b) = true) :
    a = true ∧ b = true := by
  simp [Bool.and_eq_true] at h; exact h

/-- **Condition 9 soundness**: If `checkSuccessorsInBounds` passes, then
    the transformed program is step-closed in bounds. -/
theorem checkSuccessorsInBounds_sound (dc : ECertificate)
    (h : checkSuccessorsInBounds dc = true) :
    StepClosedInBounds dc.trans :=
  checkStepClosed_sound h

theorem soundness_bridge
    (dc : ECertificate) (h : checkCertificateExec dc = true) :
    PCertificateValid (toPCertificate dc) := by
  -- checkCertificateExec is: wt_orig && wt_trans && same_obs && c1..c16
  --   && bool_no_arr_{orig,trans} && bool_simple_{orig,trans}
  --   && reg_convention_{orig,trans} && reg_collision_{orig,trans} && bool_vars_cov
  -- && is left-associative, so decompose from right to left (30 conjuncts, 29 steps)
  unfold checkCertificateExec at h
  have ⟨h29, _h_codegenpreq_t⟩    := and_true_of_and_eq_true h
  have ⟨h28, _h_codegenpreq_o⟩    := and_true_of_and_eq_true h29
  have ⟨h27, h_boolvarscov⟩       := and_true_of_and_eq_true h28
  have ⟨h26, _h_regcoll_t⟩        := and_true_of_and_eq_true h27
  have ⟨h25, _h_regcoll_o⟩        := and_true_of_and_eq_true h26
  have ⟨h24, _h_noscratch_t⟩      := and_true_of_and_eq_true h25
  have ⟨h23, _h_noscratch_o⟩      := and_true_of_and_eq_true h24
  have ⟨h22, _h_boolsimple_t⟩     := and_true_of_and_eq_true h23
  have ⟨h21, _h_boolsimple_o⟩     := and_true_of_and_eq_true h22
  have ⟨h20, h_boolnoarr_t⟩       := and_true_of_and_eq_true h21
  have ⟨h19, h_boolnoarr_o⟩       := and_true_of_and_eq_true h20
  have ⟨h18, h_step_bounds⟩  := and_true_of_and_eq_true h19
  have ⟨h17, h_pathbounds⟩   := and_true_of_and_eq_true h18
  have ⟨h16, h_arrsize⟩      := and_true_of_and_eq_true h17
  have ⟨h15, h_bndpres⟩      := and_true_of_and_eq_true h16
  have ⟨h14, h_div⟩          := and_true_of_and_eq_true h15
  have ⟨h13, h_nonterm⟩      := and_true_of_and_eq_true h14
  have ⟨h12, h_haltobs⟩      := and_true_of_and_eq_true h13
  have ⟨h11, h_haltcorr⟩     := and_true_of_and_eq_true h12
  have ⟨h10, h_trans⟩        := and_true_of_and_eq_true h11
  have ⟨h9, h_noarr_rels⟩    := and_true_of_and_eq_true h10
  have ⟨h8, h_noarr_t⟩       := and_true_of_and_eq_true h9
  have ⟨h7, h_noarr_o⟩       := and_true_of_and_eq_true h8
  have ⟨h6, h_invpres⟩       := and_true_of_and_eq_true h7
  have ⟨h5, h_relstart⟩      := and_true_of_and_eq_true h6
  have ⟨h4, h_invstart⟩      := and_true_of_and_eq_true h5
  have ⟨h3, h_startcorr⟩     := and_true_of_and_eq_true h4
  have ⟨h2, hobs_eq⟩         := and_true_of_and_eq_true h3
  have ⟨hwt_orig, hwt_trans⟩ := and_true_of_and_eq_true h2
  -- Derive identity-pair condition from checkRelAtStartExec
  have hrel0 : (dc.instrCerts.getD 0 default).rel.all (fun (e_o, e_t) => e_o == e_t) = true := by
    unfold checkRelAtStartExec at h_relstart; exact h_relstart
  -- Convert FromMaps-form hypotheses (from the per-cert FastVarMap cache used
  -- by checkCertificateExec for performance) back to the original-form
  -- hypotheses that the soundness theorems expect.
  rw [checkInvariantsPreservedFromMaps_eq] at h_invpres
  rw [checkAllTransitionsFromMaps_eq] at h_trans
  rw [checkDivPreservationFromMaps_eq] at h_div
  rw [checkBoundsPreservationFromMaps_eq] at h_bndpres
  exact {
    well_typed_orig  := by simp [toPCertificate]; exact checkWellTypedProg_sound hwt_orig
    well_typed_trans := by simp [toPCertificate]; exact checkWellTypedProg_sound hwt_trans
    same_observable  := by
      simp [toPCertificate]
      exact beq_iff_eq.mp hobs_eq
    start_corr    := checkStartCorrespondenceExec_sound dc h_startcorr hrel0
    start_inv     := checkInvariantsAtStartExec_sound dc h_invstart
    inv_preserved := checkInvariantsPreservedExec_sound dc h_invpres h_noarr_o h_noarr_t
    transitions   := checkAllTransitionsExec_sound dc (checkWellTypedProg_sound hwt_orig) h_noarr_o h_noarr_rels h_bndpres h_arrsize h_div h_pathbounds h_boolnoarr_o h_boolnoarr_t h_boolvarscov h_trans
    halt_corr     := checkHaltCorrespondenceExec_sound dc h_haltcorr
    halt_obs      := checkHaltObservableExec_sound dc h_haltobs
    nonterm       := checkNonterminationExec_sound dc h_nonterm
    error_pres    := checkDivPreservationExec_sound dc h_div h_bndpres h_arrsize (checkWellTypedProg_sound hwt_orig)
    step_closed   := checkSuccessorsInBounds_sound dc h_step_bounds
  }

-- ============================================================
-- § 10. Why not iff?
-- ============================================================

/-!
## The converse does NOT hold

`PCertificateValid cert` does **not** imply `checkCertificateExec dc = true`
for several reasons:

1. **Expressiveness gap**: The Prop-based system supports arbitrary invariants
   (`Store → Prop`), while the executable system only supports `var = val` atoms.
   A certificate using `x < y` as an invariant is valid in the Prop world
   but has no representation in `ECertificate`.

2. **Store relation generality**: The Prop system supports arbitrary `PStoreRel`s
   (`Store → Store → Prop`), while the executable system supports `EExprRel` (finite
   lists of expression pairs). The soundness proof handles non-trivial relations,
   but the executable representation is still less general.

3. **Information loss**: `toPCertificate` maps every `ECertificate` to a
   `PCertificate` with `eRelToStoreRel` store relations and `EInv.toProp` invariants.
   Many different `PCertificate`s could satisfy `PCertificateValid` for the
   same programs, but only those expressible as `toPCertificate dc` for some `dc`
   are in the image of the translation.

The relationship is:

```
  checkCertificateExec dc = true
        ⟹
  PCertificateValid (toPCertificate dc)
        ⟹
  ∀ σ₀ b, program_behavior dc.trans σ₀ b →
    ∃ b', program_behavior dc.orig σ₀ b' ∧ ...
```

The executable checker is a **sufficient** but not **necessary** condition
for semantic preservation. It is a practical tool for certifying common
compiler optimizations (constant propagation, dead code elimination,
redundant assignment removal).
-/

-- ============================================================
-- § 11. End-to-end theorem
-- ============================================================


/-- **Totality**: If the executable checker accepts, the transformed program
    has a behavior for every well-typed initial store. -/
theorem trans_has_behavior
    (dc : ECertificate) (h : checkCertificateExec dc = true)
    (σ₀ : Store) :
    ∃ b, program_behavior dc.trans σ₀ b :=
  has_behavior dc.trans σ₀ (soundness_bridge dc h).step_closed

/-- **End-to-end correctness**: If the executable checker accepts,
    then every behavior of the transformed program has a corresponding
    behavior in the original program (with observable equivalence at halt).

    This is the composition of `soundness_bridge` and
    `credible_compilation_soundness` — the complete pipeline from
    `checkCertificateExec dc = true` to semantic preservation. -/
theorem exec_checker_correct
    (dc : ECertificate) (h : checkCertificateExec dc = true)
    (σ₀ : Store) (hts₀ : TypedStore dc.tyCtx σ₀) (b : Behavior)
    (htrans : program_behavior dc.trans σ₀ b) :
    ∃ b', program_behavior dc.orig σ₀ b' ∧
      match b, b' with
      | .halts σ_t, .halts σ_o =>
          (∃ am_f, (∃ am, haltsWithResult dc.orig 0 σ₀ σ_o am am_f) ∧
            (∃ am, haltsWithResult dc.trans 0 σ₀ σ_t am am_f)) ∧
          ∀ v ∈ dc.observable, σ_t v = σ_o v
      | .errorDiv _, .errorDiv _ => True
      | .errorBounds _, .errorBounds _ => True
      | .typeErrors _, _ => True
      | .diverges, .diverges => True
      | _, _ => False := by
  have hvalid := soundness_bridge dc h
  cases b with
  | halts σ_t' =>
    obtain ⟨am₀, am', htrans'⟩ := htrans
    have hsound := soundness_halt
      (toPCertificate dc) hvalid σ₀ σ_t' hts₀ (am₀ := am₀) ⟨am', htrans'⟩
    obtain ⟨σ_o', am_f, hconj⟩ := hsound
    have ho := hconj.1
    have ht := hconj.2.1
    have hobs := hconj.2.2
    exact ⟨.halts σ_o', ⟨am₀, am_f, ho⟩, ⟨am_f, ⟨am₀, ho⟩, am₀, ht⟩, hobs⟩
  | errorDiv σ_e =>
    obtain ⟨am₀, am_e, hreach⟩ := htrans
    obtain ⟨σ_o, am_o', ho⟩ := errorDiv_preservation
      (toPCertificate dc) hvalid σ₀ hts₀ hreach
    exact ⟨.errorDiv σ_o, ⟨am₀, am_o', ho⟩, trivial⟩
  | errorBounds σ_e =>
    obtain ⟨am₀, am_e, hreach⟩ := htrans
    obtain ⟨σ_o, am_o', ho⟩ := errorBounds_preservation
      (toPCertificate dc) hvalid σ₀ hts₀ hreach
    exact ⟨.errorBounds σ_o, ⟨am₀, am_o', ho⟩, trivial⟩
  | typeErrors σ_e =>
    obtain ⟨am₀, am_e, hreach⟩ := htrans
    exact absurd hreach (type_safety hvalid.well_typed_trans hts₀ hvalid.step_closed)
  | diverges =>
    obtain ⟨f, hinf, hf0⟩ := htrans
    obtain ⟨g, hg, hg0⟩ := soundness_diverge
      (toPCertificate dc) hvalid f σ₀ hts₀ hinf hf0
    exact ⟨.diverges, ⟨g, hg, hg0⟩, trivial⟩

/-- **Complete end-to-end**: checker accepts → every initial store has a behavior
    in the transformed program, and that behavior is matched by the original. -/
theorem exec_checker_total
    (dc : ECertificate) (h : checkCertificateExec dc = true)
    (σ₀ : Store) (hts₀ : TypedStore dc.tyCtx σ₀) :
    ∃ b, program_behavior dc.trans σ₀ b ∧
      ∃ b', program_behavior dc.orig σ₀ b' ∧
        match b, b' with
        | .halts σ_t, .halts σ_o =>
            (∃ am_f, (∃ am, haltsWithResult dc.orig 0 σ₀ σ_o am am_f) ∧
              (∃ am, haltsWithResult dc.trans 0 σ₀ σ_t am am_f)) ∧
            ∀ v ∈ dc.observable, σ_t v = σ_o v
        | .errorDiv _, .errorDiv _ => True
        | .errorBounds _, .errorBounds _ => True
        | .typeErrors _, _ => True
        | .diverges, .diverges => True
        | _, _ => False := by
  obtain ⟨b, hb⟩ := trans_has_behavior dc h σ₀
  have hvalid := soundness_bridge dc h
  cases b with
  | halts σ_t =>
    obtain ⟨am₀, am', hb'⟩ := hb
    have hsound := soundness_halt (toPCertificate dc) hvalid σ₀ σ_t hts₀ (am₀ := am₀) ⟨am', hb'⟩
    obtain ⟨σ_o', am_f, hconj⟩ := hsound
    have ho := hconj.1; have ht := hconj.2.1; have hobs := hconj.2.2
    exact ⟨.halts σ_t, ⟨am₀, am', hb'⟩, .halts σ_o', ⟨am₀, am_f, ho⟩, ⟨am_f, ⟨am₀, ho⟩, am₀, ht⟩, hobs⟩
  | errorDiv σ_e =>
    obtain ⟨am₀, am_e, hreach⟩ := hb
    obtain ⟨σ_o, am_o', ho⟩ := errorDiv_preservation
      (toPCertificate dc) hvalid σ₀ hts₀ hreach
    exact ⟨.errorDiv σ_e, ⟨am₀, am_e, hreach⟩, .errorDiv σ_o, ⟨am₀, am_o', ho⟩, trivial⟩
  | errorBounds σ_e =>
    obtain ⟨am₀, am_e, hreach⟩ := hb
    obtain ⟨σ_o, am_o', ho⟩ := errorBounds_preservation
      (toPCertificate dc) hvalid σ₀ hts₀ hreach
    exact ⟨.errorBounds σ_e, ⟨am₀, am_e, hreach⟩, .errorBounds σ_o, ⟨am₀, am_o', ho⟩, trivial⟩
  | typeErrors σ_e =>
    obtain ⟨am₀, am_e, hreach⟩ := hb
    exact absurd hreach (type_safety hvalid.well_typed_trans hts₀ hvalid.step_closed)
  | diverges =>
    obtain ⟨f, hinf, hf0⟩ := hb
    obtain ⟨g, hg, hg0⟩ := soundness_diverge
      (toPCertificate dc) hvalid f σ₀ hts₀ hinf hf0
    exact ⟨.diverges, ⟨f, hinf, hf0⟩, .diverges, ⟨g, hg, hg0⟩, trivial⟩

-- ============================================================
-- § 15. Per-behavior preservation for ECertificates
-- ============================================================

/-- **Halt preservation (executable)**: If the executable checker accepts and
    the transformed program halts, the original halts with the same
    observable values. -/
theorem exec_halt_preservation
    (dc : ECertificate) (h : checkCertificateExec dc = true)
    (σ₀ σ_t' : Store) (hts₀ : TypedStore dc.tyCtx σ₀)
    {am₀ : ArrayMem} (hexec : ∃ am', haltsWithResult dc.trans 0 σ₀ σ_t' am₀ am') :
    ∃ σ_o' am_f, haltsWithResult dc.orig 0 σ₀ σ_o' am₀ am_f ∧
      haltsWithResult dc.trans 0 σ₀ σ_t' am₀ am_f ∧
      ∀ v ∈ dc.observable, σ_t' v = σ_o' v :=
  soundness_halt (toPCertificate dc) (soundness_bridge dc h) σ₀ σ_t' hts₀ hexec

/-- **Error preservation (executable)**: If the executable checker accepts and
    the transformed program reaches an error state (div or bounds), the original
    program also reaches an error state of the same kind. -/
theorem exec_error_preservation
    (dc : ECertificate) (h : checkCertificateExec dc = true)
    (σ₀ : Store) (hts₀ : TypedStore dc.tyCtx σ₀) {σ_e : Store} {am₀ am_e : ArrayMem}
    (hreach : (dc.trans ⊩ Cfg.run 0 σ₀ am₀ ⟶* Cfg.errorDiv σ_e am_e) ∨
              (dc.trans ⊩ Cfg.run 0 σ₀ am₀ ⟶* Cfg.errorBounds σ_e am_e)) :
    ∃ σ_o am_o', (dc.orig ⊩ Cfg.run 0 σ₀ am₀ ⟶* Cfg.errorDiv σ_o am_o') ∨
                 (dc.orig ⊩ Cfg.run 0 σ₀ am₀ ⟶* Cfg.errorBounds σ_o am_o') :=
  error_preservation (toPCertificate dc) (soundness_bridge dc h) σ₀ hts₀ hreach

/-- **Divergence preservation (executable)**: If the executable checker accepts
    and the transformed program diverges, the original program also diverges. -/
theorem exec_diverge_preservation
    (dc : ECertificate) (h : checkCertificateExec dc = true)
    (f : Nat → Cfg) (σ₀ : Store) (hts₀ : TypedStore dc.tyCtx σ₀)
    (hinf : IsInfiniteExec dc.trans f)
    (hf0 : f 0 = Cfg.run 0 σ₀ ArrayMem.init) :
    ∃ g : Nat → Cfg, IsInfiniteExec dc.orig g ∧ g 0 = Cfg.run 0 σ₀ ArrayMem.init :=
  soundness_diverge (toPCertificate dc) (soundness_bridge dc h) f σ₀ hts₀ hinf hf0
