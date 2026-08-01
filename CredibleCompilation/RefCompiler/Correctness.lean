-- Copyright (c) 2026 Martin Rinard
import CredibleCompilation.RefCompiler.Defs

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

/-- Extract value from `if c then some (a, b) else none = some (a', b')`. -/
private theorem ite_some_eq_some_pair {c : Bool} {a₁ b₁ : α} {a₂ b₂ : β}
    (h : (if c then some (a₁, a₂) else none) = some (b₁, b₂)) : c = true ∧ a₁ = b₁ ∧ a₂ = b₂ := by
  cases c <;> simp_all

/-!
# Reference Compiler: Correctness Proofs

Monotonicity bounds, expression/boolean/statement compilation correctness,
top-level correctness theorem, and determinism infrastructure.
-/

-- ============================================================
-- § 8. Monotonicity and result bounds
-- ============================================================

theorem compileExpr_nextTmp_ge (e : SExpr) (offset nextTmp : Nat) :
    nextTmp ≤ (compileExpr e offset nextTmp).2.2 := by
  induction e generalizing offset nextTmp with
  | lit _ => show nextTmp ≤ nextTmp + 1; omega
  | var _ => exact Nat.le_refl _
  | arrRead arr idx ih =>
    dsimp only [compileExpr]
    have hi := ih offset nextTmp
    generalize compileExpr idx offset nextTmp = ri at hi ⊢
    obtain ⟨codeIdx, vIdx, tmp1⟩ := ri; simp at hi ⊢
    omega
  | bin op a b iha ihb =>
    dsimp only [compileExpr]
    have ha := iha offset nextTmp
    generalize compileExpr a offset nextTmp = ra at ha ⊢
    obtain ⟨codeA, va, tmp1⟩ := ra; simp at ha ⊢
    have hb := ihb (offset + codeA.length) tmp1
    generalize compileExpr b (offset + codeA.length) tmp1 = rb at hb ⊢
    obtain ⟨codeB, vb, tmp2⟩ := rb; simp at hb ⊢
    omega
  | flit _ => show nextTmp ≤ nextTmp + 1; omega
  | fbin _ a b iha ihb =>
    dsimp only [compileExpr]
    have ha := iha offset nextTmp
    generalize compileExpr a offset nextTmp = ra at ha ⊢
    obtain ⟨codeA, va, tmp1⟩ := ra; simp at ha ⊢
    have hb := ihb (offset + codeA.length) tmp1
    generalize compileExpr b (offset + codeA.length) tmp1 = rb at hb ⊢
    obtain ⟨codeB, vb, tmp2⟩ := rb; simp at hb ⊢
    omega
  | intToFloat _ ih =>
    dsimp only [compileExpr]
    have hi := ih offset nextTmp
    generalize compileExpr _ offset nextTmp = ri at hi ⊢
    obtain ⟨codeE, ve, tmp1⟩ := ri; simp at hi ⊢
    omega
  | floatToInt _ ih =>
    dsimp only [compileExpr]
    have hi := ih offset nextTmp
    generalize compileExpr _ offset nextTmp = ri at hi ⊢
    obtain ⟨codeE, ve, tmp1⟩ := ri; simp at hi ⊢
    omega
  | floatUnary _ _ ih =>
    dsimp only [compileExpr]
    have hi := ih offset nextTmp
    generalize compileExpr _ offset nextTmp = ri at hi ⊢
    obtain ⟨codeE, ve, tmp1⟩ := ri; simp at hi ⊢
    omega
  | farrRead _ _ ih =>
    dsimp only [compileExpr]
    have hi := ih offset nextTmp
    generalize compileExpr _ offset nextTmp = ri at hi ⊢
    obtain ⟨codeIdx, vIdx, tmp1⟩ := ri; simp at hi ⊢
    omega

theorem compileBool_nextTmp_ge (sb : SBool) (offset nextTmp : Nat) :
    nextTmp ≤ (compileBool sb offset nextTmp).2.2 := by
  induction sb generalizing offset nextTmp with
  | lit _ => simp [compileBool]
  | bvar x => simp [compileBool]
  | cmp _ a b =>
    dsimp only [compileBool]
    have ha := compileExpr_nextTmp_ge a offset nextTmp
    generalize compileExpr a offset nextTmp = ra at ha ⊢
    obtain ⟨codeA, va, tmp1⟩ := ra; simp at ha ⊢
    exact Nat.le_trans ha (compileExpr_nextTmp_ge b _ _)
  | not e ih => exact ih offset nextTmp
  | and a b iha ihb =>
    dsimp only [compileBool]
    have ha := iha offset nextTmp
    generalize compileBool a offset nextTmp = ra at ha ⊢
    obtain ⟨codeA, ba, tmp1⟩ := ra; simp at ha ⊢
    have hb := ihb (offset + codeA.length + 1) (tmp1 + 1)
    generalize compileBool b (offset + codeA.length + 1) (tmp1 + 1) = rb at hb ⊢
    obtain ⟨codeB, bb, tmp2⟩ := rb; simp at hb ⊢
    omega
  | or a b iha ihb =>
    dsimp only [compileBool]
    have ha := iha offset nextTmp
    generalize compileBool a offset nextTmp = ra at ha ⊢
    obtain ⟨codeA, ba, tmp1⟩ := ra; simp at ha ⊢
    have hb := ihb (offset + codeA.length + 1) (tmp1 + 1)
    generalize compileBool b (offset + codeA.length + 1) (tmp1 + 1) = rb at hb ⊢
    obtain ⟨codeB, bb, tmp2⟩ := rb; simp at hb ⊢
    omega
  | barrRead arr idx =>
    dsimp only [compileBool]
    have hi := compileExpr_nextTmp_ge idx offset nextTmp
    generalize compileExpr idx offset nextTmp = ri at hi ⊢
    obtain ⟨codeIdx, vIdx, tmp1⟩ := ri; simp at hi ⊢
    omega
  | fcmp _ a b =>
    dsimp only [compileBool]
    have ha := compileExpr_nextTmp_ge a offset nextTmp
    generalize compileExpr a offset nextTmp = ra at ha ⊢
    obtain ⟨codeA, va, tmp1⟩ := ra; simp at ha ⊢
    exact Nat.le_trans ha (compileExpr_nextTmp_ge b _ _)

theorem compileExpr_result_bound (e : SExpr) (offset nextTmp : Nat)
    (htf : ∀ v ∈ e.freeVars, v.isTmp = false) :
    let r := compileExpr e offset nextTmp
    (r.2.1.isTmp = false) ∨ (∃ k, nextTmp ≤ k ∧ k < r.2.2 ∧ r.2.1 = tmpName k) := by
  induction e generalizing offset nextTmp with
  | lit _ => right; exact ⟨nextTmp, Nat.le_refl _, by show nextTmp < nextTmp + 1; omega, rfl⟩
  | var x => left; exact htf x (by simp [SExpr.freeVars])
  | arrRead arr idx ih =>
    right
    dsimp only [compileExpr]
    have hge := compileExpr_nextTmp_ge idx offset nextTmp
    generalize compileExpr idx offset nextTmp = ri at hge ⊢
    obtain ⟨codeIdx, vIdx, tmp1⟩ := ri; simp at hge ⊢
    exact ⟨tmp1, hge, by omega, rfl⟩
  | bin op a b _ _ =>
    right
    dsimp only [compileExpr]
    have hge_a := compileExpr_nextTmp_ge a offset nextTmp
    generalize compileExpr a offset nextTmp = ra at hge_a ⊢
    obtain ⟨codeA, va, tmp1⟩ := ra; simp at hge_a ⊢
    have hge_b := compileExpr_nextTmp_ge b (offset + codeA.length) tmp1
    generalize compileExpr b (offset + codeA.length) tmp1 = rb at hge_b ⊢
    obtain ⟨codeB, vb, tmp2⟩ := rb; simp at hge_b ⊢
    exact ⟨tmp2, Nat.le_trans hge_a hge_b, by omega, rfl⟩
  | flit _ => left; exact ftmpName_not_isTmp nextTmp
  | fbin _ a b _ _ =>
    left
    dsimp only [compileExpr]
    have hge_a := compileExpr_nextTmp_ge a offset nextTmp
    generalize compileExpr a offset nextTmp = ra at hge_a ⊢
    obtain ⟨codeA, va, tmp1⟩ := ra; simp at hge_a ⊢
    have hge_b := compileExpr_nextTmp_ge b (offset + codeA.length) tmp1
    generalize compileExpr b (offset + codeA.length) tmp1 = rb at hge_b ⊢
    obtain ⟨codeB, vb, tmp2⟩ := rb; simp at hge_b ⊢
    exact ftmpName_not_isTmp tmp2
  | intToFloat e _ =>
    left
    dsimp only [compileExpr]
    have hge := compileExpr_nextTmp_ge e offset nextTmp
    generalize compileExpr e offset nextTmp = ri at hge ⊢
    obtain ⟨codeE, ve, tmp1⟩ := ri; simp at hge ⊢
    exact ftmpName_not_isTmp tmp1
  | floatToInt e _ =>
    right
    dsimp only [compileExpr]
    have hge := compileExpr_nextTmp_ge e offset nextTmp
    generalize compileExpr e offset nextTmp = ri at hge ⊢
    obtain ⟨codeE, ve, tmp1⟩ := ri; simp at hge ⊢
    exact ⟨tmp1, hge, by omega, rfl⟩
  | floatUnary _ e _ =>
    left
    dsimp only [compileExpr]
    have hge := compileExpr_nextTmp_ge e offset nextTmp
    generalize compileExpr e offset nextTmp = ri at hge ⊢
    obtain ⟨codeE, ve, tmp1⟩ := ri; simp at hge ⊢
    exact ftmpName_not_isTmp tmp1
  | farrRead arr idx _ =>
    left
    dsimp only [compileExpr]
    have hge := compileExpr_nextTmp_ge idx offset nextTmp
    generalize compileExpr idx offset nextTmp = ri at hge ⊢
    obtain ⟨codeIdx, vIdx, tmp1⟩ := ri; simp at hge ⊢
    exact ftmpName_not_isTmp tmp1

theorem compileExpr_result_ftmp_bound (e : SExpr) (offset nextTmp : Nat)
    (hftf : ∀ v ∈ e.freeVars, v.isFTmp = false) :
    let r := compileExpr e offset nextTmp
    (r.2.1.isFTmp = false) ∨ (∃ k, nextTmp ≤ k ∧ k < r.2.2 ∧ r.2.1 = ftmpName k) := by
  induction e generalizing offset nextTmp with
  | lit _ => left; exact tmpName_not_isFTmp nextTmp
  | var x => left; exact hftf x (by simp [SExpr.freeVars])
  | arrRead arr idx ih =>
    left
    dsimp only [compileExpr]
    have hge := compileExpr_nextTmp_ge idx offset nextTmp
    generalize compileExpr idx offset nextTmp = ri at hge ⊢
    obtain ⟨codeIdx, vIdx, tmp1⟩ := ri; simp at hge ⊢
    exact tmpName_not_isFTmp tmp1
  | bin op a b _ _ =>
    left
    dsimp only [compileExpr]
    have hge_a := compileExpr_nextTmp_ge a offset nextTmp
    generalize compileExpr a offset nextTmp = ra at hge_a ⊢
    obtain ⟨codeA, va, tmp1⟩ := ra; simp at hge_a ⊢
    have hge_b := compileExpr_nextTmp_ge b (offset + codeA.length) tmp1
    generalize compileExpr b (offset + codeA.length) tmp1 = rb at hge_b ⊢
    obtain ⟨codeB, vb, tmp2⟩ := rb; simp at hge_b ⊢
    exact tmpName_not_isFTmp tmp2
  | flit _ => right; exact ⟨nextTmp, Nat.le_refl _, by show nextTmp < nextTmp + 1; omega, rfl⟩
  | fbin _ a b _ _ =>
    right
    dsimp only [compileExpr]
    have hge_a := compileExpr_nextTmp_ge a offset nextTmp
    generalize compileExpr a offset nextTmp = ra at hge_a ⊢
    obtain ⟨codeA, va, tmp1⟩ := ra; simp at hge_a ⊢
    have hge_b := compileExpr_nextTmp_ge b (offset + codeA.length) tmp1
    generalize compileExpr b (offset + codeA.length) tmp1 = rb at hge_b ⊢
    obtain ⟨codeB, vb, tmp2⟩ := rb; simp at hge_b ⊢
    exact ⟨tmp2, Nat.le_trans hge_a hge_b, by omega, rfl⟩
  | intToFloat e _ =>
    right
    dsimp only [compileExpr]
    have hge := compileExpr_nextTmp_ge e offset nextTmp
    generalize compileExpr e offset nextTmp = ri at hge ⊢
    obtain ⟨codeE, ve, tmp1⟩ := ri; simp at hge ⊢
    exact ⟨tmp1, hge, by omega, rfl⟩
  | floatToInt e _ =>
    left
    dsimp only [compileExpr]
    have hge := compileExpr_nextTmp_ge e offset nextTmp
    generalize compileExpr e offset nextTmp = ri at hge ⊢
    obtain ⟨codeE, ve, tmp1⟩ := ri; simp at hge ⊢
    exact tmpName_not_isFTmp tmp1
  | floatUnary _ e _ =>
    right
    dsimp only [compileExpr]
    have hge := compileExpr_nextTmp_ge e offset nextTmp
    generalize compileExpr e offset nextTmp = ri at hge ⊢
    obtain ⟨codeE, ve, tmp1⟩ := ri; simp at hge ⊢
    exact ⟨tmp1, hge, by omega, rfl⟩
  | farrRead arr idx _ =>
    right
    dsimp only [compileExpr]
    have hge := compileExpr_nextTmp_ge idx offset nextTmp
    generalize compileExpr idx offset nextTmp = ri at hge ⊢
    obtain ⟨codeIdx, vIdx, tmp1⟩ := ri; simp at hge ⊢
    exact ⟨tmp1, hge, by omega, rfl⟩

/-- The result variable of `compileExpr` is never a bool temporary
    (`__bt`-prefixed), provided the source expression's free variables
    aren't.  Used by surrounding boolean/statement proofs to discharge
    the third arm of the new ternary `agree`/`hntmp` relations. -/
theorem compileExpr_result_isBTmp_false (e : SExpr) (offset nextTmp : Nat)
    (htbf : ∀ v ∈ e.freeVars, v.isBTmp = false) :
    (compileExpr e offset nextTmp).2.1.isBTmp = false := by
  induction e generalizing offset nextTmp with
  | lit _ => exact tmpName_not_isBTmp _
  | var x => exact htbf x (by simp [SExpr.freeVars])
  | arrRead arr idx ih =>
    dsimp only [compileExpr]
    generalize compileExpr idx offset nextTmp = ri
    obtain ⟨codeIdx, vIdx, tmp1⟩ := ri
    exact tmpName_not_isBTmp _
  | bin op a b _ _ =>
    dsimp only [compileExpr]
    generalize compileExpr a offset nextTmp = ra
    obtain ⟨codeA, va, tmp1⟩ := ra
    generalize compileExpr b (offset + codeA.length) tmp1 = rb
    obtain ⟨codeB, vb, tmp2⟩ := rb
    exact tmpName_not_isBTmp _
  | flit _ => exact ftmpName_not_isBTmp _
  | fbin _ a b _ _ =>
    dsimp only [compileExpr]
    generalize compileExpr a offset nextTmp = ra
    obtain ⟨codeA, va, tmp1⟩ := ra
    generalize compileExpr b (offset + codeA.length) tmp1 = rb
    obtain ⟨codeB, vb, tmp2⟩ := rb
    exact ftmpName_not_isBTmp _
  | intToFloat e _ =>
    dsimp only [compileExpr]
    generalize compileExpr e offset nextTmp = ri
    obtain ⟨codeE, ve, tmp1⟩ := ri
    exact ftmpName_not_isBTmp _
  | floatToInt e _ =>
    dsimp only [compileExpr]
    generalize compileExpr e offset nextTmp = ri
    obtain ⟨codeE, ve, tmp1⟩ := ri
    exact tmpName_not_isBTmp _
  | floatUnary _ e _ =>
    dsimp only [compileExpr]
    generalize compileExpr e offset nextTmp = ri
    obtain ⟨codeE, ve, tmp1⟩ := ri
    exact ftmpName_not_isBTmp _
  | farrRead arr idx _ =>
    dsimp only [compileExpr]
    generalize compileExpr idx offset nextTmp = ri
    obtain ⟨codeIdx, vIdx, tmp1⟩ := ri
    exact ftmpName_not_isBTmp _


-- ============================================================
-- § 9. Expression compilation correctness
-- ============================================================

theorem compileExpr_correct (e : SExpr) (offset nextTmp : Nat)
    (σ σ_tac : Store) (am : ArrayMem) (p : Prog)
    (htf : ∀ v ∈ e.freeVars, v.isTmp = false)
    (hftf : ∀ v ∈ e.freeVars, v.isFTmp = false)
    (htbf : ∀ v ∈ e.freeVars, v.isBTmp = false)
    (htypedv : e.typedVars σ am)
    (hsafe : e.safe σ am p.arrayDecls)
    (hagree : ∀ v, v.isTmp = false → v.isFTmp = false → v.isBTmp = false → σ_tac v = σ v)
    (hcode : RC.CodeAt (compileExpr e offset nextTmp).1 p offset) :
    let r := compileExpr e offset nextTmp
    ∃ σ', FragExec p offset σ_tac (offset + r.1.length) σ' am am ∧
      σ' r.2.1 = e.wrapEval σ am ∧
      (∀ w, w.isTmp = false → w.isFTmp = false → w.isBTmp = false → σ' w = σ_tac w) ∧
      (∀ k, k < nextTmp → σ' (tmpName k) = σ_tac (tmpName k)) ∧
      (∀ k, k < nextTmp → σ' (ftmpName k) = σ_tac (ftmpName k)) ∧
      (∀ k, k < nextTmp → σ' (btmpName k) = σ_tac (btmpName k)) := by
  induction e generalizing offset nextTmp σ_tac with
  | lit n =>
    simp only [compileExpr] at hcode ⊢
    refine ⟨σ_tac[tmpName nextTmp ↦ .int (BitVec.ofInt 64 n)], FragExec.single_const (am := am) hcode.head, ?_, ?_, ?_, ?_, ?_⟩
    · exact Store.update_self _ _ _
    · intro w hw1 _ _; exact Store.update_isTmp_ne (tmpName_isTmp nextTmp) hw1
    · intro k _; exact Store.update_tmpName_ne (by omega)
    · intro k _
      exact Store.update_other _ _ _ _ (Ne.symm tmpName_ne_ftmpName)
    · intro k _
      exact Store.update_other _ _ _ _ (Ne.symm tmpName_ne_btmpName)
  | var x =>
    simp only [compileExpr] at hcode ⊢
    refine ⟨σ_tac, FragExec.rfl' _ _ _ _, ?_, fun w _ _ _ => rfl, fun k _ => rfl, fun k _ => rfl, fun k _ => rfl⟩
    simp only [SExpr.wrapEval]
    exact hagree x (htf x (by simp [SExpr.freeVars])) (hftf x (by simp [SExpr.freeVars])) (htbf x (by simp [SExpr.freeVars]))
  | bin op a b iha ihb =>
    have htf_a : ∀ v ∈ a.freeVars, v.isTmp = false :=
      fun v hv => htf v (List.mem_append_left _ hv)
    have htf_b : ∀ v ∈ b.freeVars, v.isTmp = false :=
      fun v hv => htf v (List.mem_append_right _ hv)
    have hftf_a : ∀ v ∈ a.freeVars, v.isFTmp = false :=
      fun v hv => hftf v (List.mem_append_left _ hv)
    have hftf_b : ∀ v ∈ b.freeVars, v.isFTmp = false :=
      fun v hv => hftf v (List.mem_append_right _ hv)
    have htbf_a : ∀ v ∈ a.freeVars, v.isBTmp = false :=
      fun v hv => htbf v (List.mem_append_left _ hv)
    have htbf_b : ∀ v ∈ b.freeVars, v.isBTmp = false :=
      fun v hv => htbf v (List.mem_append_right _ hv)
    obtain ⟨hwrap_a, hwrap_b, htv_a, htv_b⟩ :=
      show a.wrapEval σ am = .int (a.eval σ am) ∧ b.wrapEval σ am = .int (b.eval σ am) ∧
           a.typedVars σ am ∧ b.typedVars σ am from htypedv
    dsimp only [compileExpr] at hcode ⊢
    generalize hra : compileExpr a offset nextTmp = ra at hcode ⊢
    obtain ⟨codeA, va, tmp1⟩ := ra
    generalize hrb : compileExpr b (offset + codeA.length) tmp1 = rb at hcode ⊢
    obtain ⟨codeB, vb, tmp2⟩ := rb
    simp only [] at hcode ⊢
    have hcodeA : RC.CodeAt (compileExpr a offset nextTmp).1 p offset := by
      rw [hra]; exact hcode.left.left
    have hcodeB : RC.CodeAt (compileExpr b (offset + codeA.length) tmp1).1 p
        (offset + codeA.length) := by rw [hrb]; exact hcode.left.right
    have hbinop : p[offset + codeA.length + codeB.length]? =
        some (.binop (tmpName tmp2) op va vb) := by
      have := hcode.right.head
      simp only [List.length_append] at this
      rwa [show offset + (codeA.length + codeB.length) =
          offset + codeA.length + codeB.length from by omega] at this
    obtain ⟨σ_a, hexec_a, hval_a, hntmp_a, hprev_a, hfprev_a, hbprev_a⟩ :=
      iha offset nextTmp σ_tac htf_a hftf_a htbf_a htv_a (SExpr.safe_bin_left hsafe) hagree hcodeA
    rw [hra] at hexec_a hval_a; simp at hexec_a hval_a
    have hagree_a : ∀ v, v.isTmp = false → v.isFTmp = false → v.isBTmp = false → σ_a v = σ v := by
      intro v hv1 hv2 hv3; rw [hntmp_a v hv1 hv2 hv3]; exact hagree v hv1 hv2 hv3
    have hge_a := compileExpr_nextTmp_ge a offset nextTmp
    rw [hra] at hge_a; simp at hge_a
    obtain ⟨σ_b, hexec_b, hval_b, hntmp_b, hprev_b, hfprev_b, hbprev_b⟩ :=
      ihb (offset + codeA.length) tmp1 σ_a htf_b hftf_b htbf_b htv_b (SExpr.safe_bin_right hsafe) hagree_a hcodeB
    rw [hrb] at hexec_b hval_b; simp at hexec_b hval_b
    have hva_b : σ_b va = σ_a va := by
      rcases compileExpr_result_bound a offset nextTmp htf_a with h | ⟨k, _, hlt, heq⟩
      · rw [hra] at h; simp at h
        rcases compileExpr_result_ftmp_bound a offset nextTmp hftf_a with h2 | ⟨j, _, hlt2, heq2⟩
        · rw [hra] at h2; simp at h2
          have h3 : va.isBTmp = false := by
            have := compileExpr_result_isBTmp_false a offset nextTmp htbf_a
            rw [hra] at this; simpa using this
          exact hntmp_b va h h2 h3
        · rw [hra] at hlt2 heq2; simp at hlt2 heq2; rw [heq2, hfprev_b j (by omega)]
      · rw [hra] at hlt heq; simp at hlt heq
        rw [heq, hprev_b k (by omega)]
    -- Extract int values for Step.binop
    have hva : σ_b va = .int (a.eval σ am) := by rw [hva_b, hval_a, hwrap_a]
    have hvb : σ_b vb = .int (b.eval σ am) := by rw [hval_b, hwrap_b]
    have hbsafe : op.safe (a.eval σ am) (b.eval σ am) := SExpr.safe_bin_safe hsafe
    have hexec_binop := FragExec.single_binop (am := am) hbinop hva hvb hbsafe
    refine ⟨σ_b[tmpName tmp2 ↦ .int (op.eval (a.eval σ am) (b.eval σ am))],
            ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have h123 := FragExec.trans' (FragExec.trans' hexec_a hexec_b) hexec_binop
      have hlen : offset + (codeA ++ codeB ++ [TAC.binop (tmpName tmp2) op va vb]).length =
          offset + codeA.length + codeB.length + 1 := by
        simp only [List.length_append, List.length_cons, List.length_nil]; omega
      rw [hlen]; exact h123
    · simp only [SExpr.wrapEval]; rw [Store.update_self]
    · intro w hw1 hw2 hw3
      rw [Store.update_isTmp_ne (tmpName_isTmp tmp2) hw1, hntmp_b w hw1 hw2 hw3, hntmp_a w hw1 hw2 hw3]
    · intro k hk
      have hle_a : nextTmp ≤ tmp1 := by
        have := compileExpr_nextTmp_ge a offset nextTmp; rw [hra] at this; simpa using this
      have hle_b : tmp1 ≤ tmp2 := by
        have := compileExpr_nextTmp_ge b (offset + codeA.length) tmp1; rw [hrb] at this; simpa using this
      rw [Store.update_tmpName_ne (by omega)]
      rw [hprev_b k (by omega), hprev_a k hk]
    · intro k hk
      have hle_a : nextTmp ≤ tmp1 := by
        have := compileExpr_nextTmp_ge a offset nextTmp; rw [hra] at this; simpa using this
      have hle_b : tmp1 ≤ tmp2 := by
        have := compileExpr_nextTmp_ge b (offset + codeA.length) tmp1; rw [hrb] at this; simpa using this
      rw [Store.update_other _ _ _ _ (Ne.symm tmpName_ne_ftmpName)]
      rw [hfprev_b k (by omega), hfprev_a k hk]
    · intro k hk
      have hle_a : nextTmp ≤ tmp1 := by
        have := compileExpr_nextTmp_ge a offset nextTmp; rw [hra] at this; simpa using this
      have hle_b : tmp1 ≤ tmp2 := by
        have := compileExpr_nextTmp_ge b (offset + codeA.length) tmp1; rw [hrb] at this; simpa using this
      rw [Store.update_other _ _ _ _ (Ne.symm tmpName_ne_btmpName)]
      rw [hbprev_b k (by omega), hbprev_a k hk]
  | arrRead arr idx ih =>
    have hsafe_idx : idx.safe σ am p.arrayDecls := by
      simp [SExpr.safe] at hsafe; exact hsafe.1
    obtain ⟨hwrap_idx, htv_idx⟩ :=
      show idx.wrapEval σ am = .int (idx.eval σ am) ∧ idx.typedVars σ am from htypedv
    have hftf_idx : ∀ v ∈ idx.freeVars, v.isFTmp = false := hftf
    have htbf_idx : ∀ v ∈ idx.freeVars, v.isBTmp = false := htbf
    dsimp only [compileExpr] at hcode ⊢
    generalize hri : compileExpr idx offset nextTmp = ri at hcode ⊢
    obtain ⟨codeIdx, vIdx, tmp1⟩ := ri
    simp only [] at hcode ⊢
    have hcodeIdx : RC.CodeAt (compileExpr idx offset nextTmp).1 p offset := by
      rw [hri]; exact hcode.left
    have harrLoad : p[offset + codeIdx.length]? = some (.arrLoad (tmpName tmp1) arr vIdx .int) := by
      have := hcode.right.head; simpa using this
    obtain ⟨σ_idx, hexec_idx, hval_idx, hntmp_idx, hprev_idx, hfprev_idx, hbprev_idx⟩ :=
      ih offset nextTmp σ_tac htf hftf_idx htbf_idx htv_idx hsafe_idx hagree hcodeIdx
    rw [hri] at hexec_idx hval_idx; simp at hexec_idx hval_idx
    have hval_idx_int : σ_idx vIdx = .int (idx.eval σ am) := by rw [hval_idx, hwrap_idx]
    have hbounds : (SExpr.eval σ am idx) < p.arraySizeBv arr := by
      simp only [SExpr.safe] at hsafe; exact hsafe.2
    have hexec_arrLoad := FragExec.single_arrLoad (am := am) harrLoad hval_idx_int hbounds
    refine ⟨σ_idx[tmpName tmp1 ↦ .int (am.read arr (idx.eval σ am))],
            ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have h12 := FragExec.trans' hexec_idx hexec_arrLoad
      simp only [List.length_append, List.length_cons, List.length_nil] at h12 ⊢
      exact h12
    · simp only [SExpr.wrapEval]; rw [Store.update_self]
    · intro w hw1 hw2 hw3
      rw [Store.update_isTmp_ne (tmpName_isTmp tmp1) hw1, hntmp_idx w hw1 hw2 hw3]
    · intro k hk
      have hge := compileExpr_nextTmp_ge idx offset nextTmp
      rw [hri] at hge; simp at hge
      rw [Store.update_tmpName_ne (by omega), hprev_idx k hk]
    · intro k hk
      have hge := compileExpr_nextTmp_ge idx offset nextTmp
      rw [hri] at hge; simp at hge
      rw [Store.update_other _ _ _ _ (Ne.symm tmpName_ne_ftmpName)]
      exact hfprev_idx k hk
    · intro k hk
      have hge := compileExpr_nextTmp_ge idx offset nextTmp
      rw [hri] at hge; simp at hge
      rw [Store.update_other _ _ _ _ (Ne.symm tmpName_ne_btmpName)]
      exact hbprev_idx k hk
  | flit f =>
    simp only [compileExpr] at hcode ⊢
    refine ⟨σ_tac[ftmpName nextTmp ↦ .float (floatToBits f)], FragExec.single_const (am := am) hcode.head, ?_, ?_, ?_, ?_, ?_⟩
    · exact Store.update_self _ _ _
    · intro w _ hw2 _; exact Store.update_isFTmp_ne (ftmpName_isFTmp nextTmp) hw2
    · intro k _
      exact Store.update_other _ _ _ _ (tmpName_ne_ftmpName)
    · intro k _; exact Store.update_ftmpName_ne (by omega)
    · intro k _
      exact Store.update_other _ _ _ _ (Ne.symm ftmpName_ne_btmpName)
  | fbin fop a b iha ihb =>
    obtain ⟨hwrap_a, hwrap_b, htv_a, htv_b⟩ :=
      show a.wrapEval σ am = .float (a.eval σ am) ∧ b.wrapEval σ am = .float (b.eval σ am) ∧
           a.typedVars σ am ∧ b.typedVars σ am from htypedv
    have htf_a : ∀ v ∈ a.freeVars, v.isTmp = false :=
      fun v hv => htf v (List.mem_append_left _ hv)
    have htf_b : ∀ v ∈ b.freeVars, v.isTmp = false :=
      fun v hv => htf v (List.mem_append_right _ hv)
    have hftf_a : ∀ v ∈ a.freeVars, v.isFTmp = false :=
      fun v hv => hftf v (List.mem_append_left _ hv)
    have hftf_b : ∀ v ∈ b.freeVars, v.isFTmp = false :=
      fun v hv => hftf v (List.mem_append_right _ hv)
    have htbf_a : ∀ v ∈ a.freeVars, v.isBTmp = false :=
      fun v hv => htbf v (List.mem_append_left _ hv)
    have htbf_b : ∀ v ∈ b.freeVars, v.isBTmp = false :=
      fun v hv => htbf v (List.mem_append_right _ hv)
    dsimp only [compileExpr] at hcode ⊢
    generalize hra : compileExpr a offset nextTmp = ra at hcode ⊢
    obtain ⟨codeA, va, tmp1⟩ := ra
    generalize hrb : compileExpr b (offset + codeA.length) tmp1 = rb at hcode ⊢
    obtain ⟨codeB, vb, tmp2⟩ := rb
    simp only [] at hcode ⊢
    have hcodeA : RC.CodeAt (compileExpr a offset nextTmp).1 p offset := by
      rw [hra]; exact hcode.left.left
    have hcodeB : RC.CodeAt (compileExpr b (offset + codeA.length) tmp1).1 p
        (offset + codeA.length) := by rw [hrb]; exact hcode.left.right
    have hfbinop : p[offset + codeA.length + codeB.length]? =
        some (.fbinop (ftmpName tmp2) fop va vb) := by
      have := hcode.right.head
      simp only [List.length_append] at this
      rwa [show offset + (codeA.length + codeB.length) =
          offset + codeA.length + codeB.length from by omega] at this
    obtain ⟨σ_a, hexec_a, hval_a, hntmp_a, hprev_a, hfprev_a, hbprev_a⟩ :=
      iha offset nextTmp σ_tac htf_a hftf_a htbf_a htv_a (SExpr.safe_fbin_left hsafe) hagree hcodeA
    rw [hra] at hexec_a hval_a; simp at hexec_a hval_a
    have hagree_a : ∀ v, v.isTmp = false → v.isFTmp = false → v.isBTmp = false → σ_a v = σ v := by
      intro v hv1 hv2 hv3; rw [hntmp_a v hv1 hv2 hv3]; exact hagree v hv1 hv2 hv3
    have hge_a := compileExpr_nextTmp_ge a offset nextTmp
    rw [hra] at hge_a; simp at hge_a
    obtain ⟨σ_b, hexec_b, hval_b, hntmp_b, hprev_b, hfprev_b, hbprev_b⟩ :=
      ihb (offset + codeA.length) tmp1 σ_a htf_b hftf_b htbf_b htv_b (SExpr.safe_fbin_right hsafe) hagree_a hcodeB
    rw [hrb] at hexec_b hval_b; simp at hexec_b hval_b
    -- Preserve a's result through b's execution
    have hva_b : σ_b va = σ_a va := by
      rcases compileExpr_result_ftmp_bound a offset nextTmp hftf_a with h | ⟨k, _, hlt, heq⟩
      · rw [hra] at h; simp at h
        rcases compileExpr_result_bound a offset nextTmp htf_a with h2 | ⟨j, _, hlt2, heq2⟩
        · rw [hra] at h2; simp at h2
          have h3 : va.isBTmp = false := by
            have := compileExpr_result_isBTmp_false a offset nextTmp htbf_a
            rw [hra] at this; simpa using this
          exact hntmp_b va h2 h h3
        · rw [hra] at hlt2 heq2; simp at hlt2 heq2; rw [heq2, hprev_b j (by omega)]
      · rw [hra] at hlt heq; simp at hlt heq; rw [heq, hfprev_b k (by omega)]
    have hva : σ_b va = .float (a.eval σ am) := by rw [hva_b, hval_a, hwrap_a]
    have hvb : σ_b vb = .float (b.eval σ am) := by rw [hval_b, hwrap_b]
    have hexec_fbinop := FragExec.single_fbinop (am := am) hfbinop hva hvb
    refine ⟨σ_b[ftmpName tmp2 ↦ .float (fop.eval (a.eval σ am) (b.eval σ am))],
            ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have h123 := FragExec.trans' (FragExec.trans' hexec_a hexec_b) hexec_fbinop
      have hlen : offset + (codeA ++ codeB ++ [TAC.fbinop (ftmpName tmp2) fop va vb]).length =
          offset + codeA.length + codeB.length + 1 := by
        simp only [List.length_append, List.length_cons, List.length_nil]; omega
      rw [hlen]; exact h123
    · simp only [SExpr.wrapEval]; rw [Store.update_self]
    · intro w hw1 hw2 hw3
      rw [Store.update_isFTmp_ne (ftmpName_isFTmp tmp2) hw2, hntmp_b w hw1 hw2 hw3, hntmp_a w hw1 hw2 hw3]
    · intro k hk
      have hle_a : nextTmp ≤ tmp1 := by
        have := compileExpr_nextTmp_ge a offset nextTmp; rw [hra] at this; simpa using this
      have hle_b : tmp1 ≤ tmp2 := by
        have := compileExpr_nextTmp_ge b (offset + codeA.length) tmp1; rw [hrb] at this; simpa using this
      rw [Store.update_other _ _ _ _ (tmpName_ne_ftmpName)]
      rw [hprev_b k (by omega), hprev_a k hk]
    · intro k hk
      have hle_a : nextTmp ≤ tmp1 := by
        have := compileExpr_nextTmp_ge a offset nextTmp; rw [hra] at this; simpa using this
      have hle_b : tmp1 ≤ tmp2 := by
        have := compileExpr_nextTmp_ge b (offset + codeA.length) tmp1; rw [hrb] at this; simpa using this
      rw [Store.update_ftmpName_ne (by omega)]
      rw [hfprev_b k (by omega), hfprev_a k hk]
    · intro k hk
      have hle_a : nextTmp ≤ tmp1 := by
        have := compileExpr_nextTmp_ge a offset nextTmp; rw [hra] at this; simpa using this
      have hle_b : tmp1 ≤ tmp2 := by
        have := compileExpr_nextTmp_ge b (offset + codeA.length) tmp1; rw [hrb] at this; simpa using this
      rw [Store.update_other _ _ _ _ (Ne.symm ftmpName_ne_btmpName)]
      rw [hbprev_b k (by omega), hbprev_a k hk]
  | intToFloat e ih =>
    obtain ⟨hwrap_e, htv_e⟩ :=
      show e.wrapEval σ am = .int (e.eval σ am) ∧ e.typedVars σ am from htypedv
    dsimp only [compileExpr] at hcode ⊢
    generalize hri : compileExpr e offset nextTmp = ri at hcode ⊢
    obtain ⟨codeE, ve, tmp1⟩ := ri
    simp only [] at hcode ⊢
    have hcodeE : RC.CodeAt (compileExpr e offset nextTmp).1 p offset := by
      rw [hri]; exact hcode.left
    have hconv : p[offset + codeE.length]? = some (.intToFloat (ftmpName tmp1) ve) := by
      have := hcode.right.head; simpa using this
    obtain ⟨σ_e, hexec_e, hval_e, hntmp_e, hprev_e, hfprev_e, hbprev_e⟩ :=
      ih offset nextTmp σ_tac htf hftf htbf htv_e (by simp [SExpr.safe] at hsafe ⊢; exact hsafe) hagree hcodeE
    rw [hri] at hexec_e hval_e; simp at hexec_e hval_e
    have hval_e_int : σ_e ve = .int (e.eval σ am) := by rw [hval_e, hwrap_e]
    have hexec_conv := FragExec.single_intToFloat (am := am) hconv hval_e_int
    refine ⟨σ_e[ftmpName tmp1 ↦ .float (intToFloatBv (e.eval σ am))],
            ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have h12 := FragExec.trans' hexec_e hexec_conv
      simp only [List.length_append, List.length_cons, List.length_nil] at h12 ⊢
      exact h12
    · simp only [SExpr.wrapEval]; rw [Store.update_self]
    · intro w hw1 hw2 hw3
      rw [Store.update_isFTmp_ne (ftmpName_isFTmp tmp1) hw2, hntmp_e w hw1 hw2 hw3]
    · intro k hk
      have hge := compileExpr_nextTmp_ge e offset nextTmp
      rw [hri] at hge; simp at hge
      rw [Store.update_other _ _ _ _ (tmpName_ne_ftmpName)]
      exact hprev_e k hk
    · intro k hk
      have hge := compileExpr_nextTmp_ge e offset nextTmp
      rw [hri] at hge; simp at hge
      rw [Store.update_ftmpName_ne (by omega)]
      exact hfprev_e k hk
    · intro k hk
      have hge := compileExpr_nextTmp_ge e offset nextTmp
      rw [hri] at hge; simp at hge
      rw [Store.update_other _ _ _ _ (Ne.symm ftmpName_ne_btmpName)]
      exact hbprev_e k hk
  | floatToInt e ih =>
    obtain ⟨hwrap_e, htv_e⟩ :=
      show e.wrapEval σ am = .float (e.eval σ am) ∧ e.typedVars σ am from htypedv
    dsimp only [compileExpr] at hcode ⊢
    generalize hri : compileExpr e offset nextTmp = ri at hcode ⊢
    obtain ⟨codeE, ve, tmp1⟩ := ri
    simp only [] at hcode ⊢
    have hcodeE : RC.CodeAt (compileExpr e offset nextTmp).1 p offset := by
      rw [hri]; exact hcode.left
    have hconv : p[offset + codeE.length]? = some (.floatToInt (tmpName tmp1) ve) := by
      have := hcode.right.head; simpa using this
    obtain ⟨σ_e, hexec_e, hval_e, hntmp_e, hprev_e, hfprev_e, hbprev_e⟩ :=
      ih offset nextTmp σ_tac htf hftf htbf htv_e (by simp [SExpr.safe] at hsafe ⊢; exact hsafe) hagree hcodeE
    rw [hri] at hexec_e hval_e; simp at hexec_e hval_e
    have hval_e_float : σ_e ve = .float (e.eval σ am) := by rw [hval_e, hwrap_e]
    have hexec_conv := FragExec.single_floatToInt (am := am) hconv hval_e_float
    refine ⟨σ_e[tmpName tmp1 ↦ .int (floatToIntBv (e.eval σ am))],
            ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have h12 := FragExec.trans' hexec_e hexec_conv
      simp only [List.length_append, List.length_cons, List.length_nil] at h12 ⊢
      exact h12
    · simp only [SExpr.wrapEval]; rw [Store.update_self]
    · intro w hw1 hw2 hw3
      rw [Store.update_isTmp_ne (tmpName_isTmp tmp1) hw1, hntmp_e w hw1 hw2 hw3]
    · intro k hk
      have hge := compileExpr_nextTmp_ge e offset nextTmp
      rw [hri] at hge; simp at hge
      rw [Store.update_tmpName_ne (by omega)]
      exact hprev_e k hk
    · intro k hk
      have hge := compileExpr_nextTmp_ge e offset nextTmp
      rw [hri] at hge; simp at hge
      rw [Store.update_other _ _ _ _ (Ne.symm tmpName_ne_ftmpName)]
      exact hfprev_e k hk
    · intro k hk
      have hge := compileExpr_nextTmp_ge e offset nextTmp
      rw [hri] at hge; simp at hge
      rw [Store.update_other _ _ _ _ (Ne.symm tmpName_ne_btmpName)]
      exact hbprev_e k hk
  | floatUnary op e ih =>
    obtain ⟨hwrap_e, htv_e⟩ :=
      show e.wrapEval σ am = .float (e.eval σ am) ∧ e.typedVars σ am from htypedv
    dsimp only [compileExpr] at hcode ⊢
    generalize hri : compileExpr e offset nextTmp = ri at hcode ⊢
    obtain ⟨codeE, ve, tmp1⟩ := ri
    simp only [] at hcode ⊢
    have hcodeE : RC.CodeAt (compileExpr e offset nextTmp).1 p offset := by
      rw [hri]; exact hcode.left
    have hconv : p[offset + codeE.length]? = some (.floatUnary (ftmpName tmp1) op ve) := by
      have := hcode.right.head; simpa using this
    obtain ⟨σ_e, hexec_e, hval_e, hntmp_e, hprev_e, hfprev_e, hbprev_e⟩ :=
      ih offset nextTmp σ_tac htf hftf htbf htv_e (by simp [SExpr.safe] at hsafe ⊢; exact hsafe) hagree hcodeE
    rw [hri] at hexec_e hval_e; simp at hexec_e hval_e
    have hval_e_float : σ_e ve = .float (e.eval σ am) := by rw [hval_e, hwrap_e]
    have hexec_conv := FragExec.single_floatUnary (am := am) hconv hval_e_float
    refine ⟨σ_e[ftmpName tmp1 ↦ .float (op.eval (e.eval σ am))],
            ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have h12 := FragExec.trans' hexec_e hexec_conv
      simp only [List.length_append, List.length_cons, List.length_nil] at h12 ⊢
      exact h12
    · simp only [SExpr.wrapEval]; rw [Store.update_self]
    · intro w hw1 hw2 hw3
      rw [Store.update_isFTmp_ne (ftmpName_isFTmp tmp1) hw2, hntmp_e w hw1 hw2 hw3]
    · intro k hk
      have hge := compileExpr_nextTmp_ge e offset nextTmp
      rw [hri] at hge; simp at hge
      rw [Store.update_other _ _ _ _ (tmpName_ne_ftmpName)]
      exact hprev_e k hk
    · intro k hk
      have hge := compileExpr_nextTmp_ge e offset nextTmp
      rw [hri] at hge; simp at hge
      rw [Store.update_ftmpName_ne (by omega)]
      exact hfprev_e k hk
    · intro k hk
      have hge := compileExpr_nextTmp_ge e offset nextTmp
      rw [hri] at hge; simp at hge
      rw [Store.update_other _ _ _ _ (Ne.symm ftmpName_ne_btmpName)]
      exact hbprev_e k hk
  | farrRead arr idx ih =>
    have hsafe_idx : idx.safe σ am p.arrayDecls := by
      simp [SExpr.safe] at hsafe; exact hsafe.1
    obtain ⟨hwrap_idx, htv_idx⟩ :=
      show idx.wrapEval σ am = .int (idx.eval σ am) ∧ idx.typedVars σ am from htypedv
    have hftf_idx : ∀ v ∈ idx.freeVars, v.isFTmp = false := hftf
    have htbf_idx : ∀ v ∈ idx.freeVars, v.isBTmp = false := htbf
    dsimp only [compileExpr] at hcode ⊢
    generalize hri : compileExpr idx offset nextTmp = ri at hcode ⊢
    obtain ⟨codeIdx, vIdx, tmp1⟩ := ri
    simp only [] at hcode ⊢
    have hcodeIdx : RC.CodeAt (compileExpr idx offset nextTmp).1 p offset := by
      rw [hri]; exact hcode.left
    have harrLoad : p[offset + codeIdx.length]? = some (.arrLoad (ftmpName tmp1) arr vIdx .float) := by
      have := hcode.right.head; simpa using this
    obtain ⟨σ_idx, hexec_idx, hval_idx, hntmp_idx, hprev_idx, hfprev_idx, hbprev_idx⟩ :=
      ih offset nextTmp σ_tac htf hftf_idx htbf_idx htv_idx hsafe_idx hagree hcodeIdx
    rw [hri] at hexec_idx hval_idx; simp at hexec_idx hval_idx
    have hval_idx_int : σ_idx vIdx = .int (idx.eval σ am) := by rw [hval_idx, hwrap_idx]
    have hbounds : (SExpr.eval σ am idx) < p.arraySizeBv arr := by
      simp only [SExpr.safe] at hsafe; exact hsafe.2
    have hexec_arrLoad := FragExec.single_arrLoad_float (am := am) harrLoad hval_idx_int hbounds
    refine ⟨σ_idx[ftmpName tmp1 ↦ .float (am.read arr (idx.eval σ am))],
            ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have h12 := FragExec.trans' hexec_idx hexec_arrLoad
      simp only [List.length_append, List.length_cons, List.length_nil] at h12 ⊢
      exact h12
    · simp only [SExpr.wrapEval]; rw [Store.update_self]
    · intro w hw1 hw2 hw3
      rw [Store.update_isFTmp_ne (ftmpName_isFTmp tmp1) hw2, hntmp_idx w hw1 hw2 hw3]
    · intro k hk
      have hge := compileExpr_nextTmp_ge idx offset nextTmp
      rw [hri] at hge; simp at hge
      rw [Store.update_other _ _ _ _ (tmpName_ne_ftmpName)]
      exact hprev_idx k hk
    · intro k hk
      have hge := compileExpr_nextTmp_ge idx offset nextTmp
      rw [hri] at hge; simp at hge
      rw [Store.update_ftmpName_ne (by omega)]
      exact hfprev_idx k hk
    · intro k hk
      have hge := compileExpr_nextTmp_ge idx offset nextTmp
      rw [hri] at hge; simp at hge
      rw [Store.update_other _ _ _ _ (Ne.symm ftmpName_ne_btmpName)]
      exact hbprev_idx k hk

-- ============================================================
-- § 10. Boolean expression compilation correctness
-- ============================================================

theorem compileBool_correct (sb : SBool) (offset nextTmp : Nat) (σ σ_tac : Store) (am : ArrayMem) (p : Prog)
    (htf : ∀ v ∈ sb.freeVars, v.isTmp = false)
    (hftf : ∀ v ∈ sb.freeVars, v.isFTmp = false)
    (htbf : ∀ v ∈ sb.freeVars, v.isBTmp = false)
    (htypedv : sb.typedVars σ am)
    (hbsafe : sb.safe σ am p.arrayDecls)
    (hagree : ∀ v, v.isTmp = false → v.isFTmp = false → v.isBTmp = false → σ_tac v = σ v)
    (hcode : RC.CodeAt (compileBool sb offset nextTmp).1 p offset) :
    let r := compileBool sb offset nextTmp
    ∃ σ', FragExec p offset σ_tac (offset + r.1.length) σ' am am ∧
      r.2.1.eval σ' am = sb.eval σ am ∧
      (∀ w, w.isTmp = false → w.isFTmp = false → w.isBTmp = false → σ' w = σ_tac w) ∧
      (∀ k, k < nextTmp → σ' (tmpName k) = σ_tac (tmpName k)) ∧
      (∀ k, k < nextTmp → σ' (ftmpName k) = σ_tac (ftmpName k)) ∧
      (∀ k, k < nextTmp → σ' (btmpName k) = σ_tac (btmpName k)) := by
  induction sb generalizing offset nextTmp σ_tac with
  | lit b =>
    simp only [compileBool] at hcode ⊢
    exact ⟨σ_tac, FragExec.rfl' _ _ _ _, by simp [BoolExpr.eval, SBool.eval],
           fun w _ _ _ => rfl, fun k _ => rfl, fun k _ => rfl, fun k _ => rfl⟩
  | bvar x =>
    simp only [compileBool] at hcode ⊢
    refine ⟨σ_tac, FragExec.rfl' _ _ _ _, ?_,
            fun w _ _ _ => rfl, fun k _ => rfl, fun k _ => rfl, fun k _ => rfl⟩
    simp only [BoolExpr.eval, SBool.eval]
    rw [hagree x (htf x (by simp [SBool.freeVars])) (hftf x (by simp [SBool.freeVars]))
        (htbf x (by simp [SBool.freeVars]))]
  | cmp cop a b =>
    have htf_a : ∀ v ∈ a.freeVars, v.isTmp = false :=
      fun v hv => htf v (List.mem_append_left _ hv)
    have htf_b : ∀ v ∈ b.freeVars, v.isTmp = false :=
      fun v hv => htf v (List.mem_append_right _ hv)
    have hftf_a : ∀ v ∈ a.freeVars, v.isFTmp = false :=
      fun v hv => hftf v (List.mem_append_left _ hv)
    have hftf_b : ∀ v ∈ b.freeVars, v.isFTmp = false :=
      fun v hv => hftf v (List.mem_append_right _ hv)
    have htbf_a : ∀ v ∈ a.freeVars, v.isBTmp = false :=
      fun v hv => htbf v (List.mem_append_left _ hv)
    have htbf_b : ∀ v ∈ b.freeVars, v.isBTmp = false :=
      fun v hv => htbf v (List.mem_append_right _ hv)
    obtain ⟨htv_a, htv_b, hwrap_a, hwrap_b⟩ :=
      show a.typedVars σ am ∧ b.typedVars σ am ∧
           a.wrapEval σ am = .int (a.eval σ am) ∧ b.wrapEval σ am = .int (b.eval σ am) from htypedv
    simp only [SBool.safe] at hbsafe; obtain ⟨hsa, hsb⟩ := hbsafe
    dsimp only [compileBool] at hcode ⊢
    generalize hra : compileExpr a offset nextTmp = ra at hcode ⊢
    obtain ⟨codeA, va, tmp1⟩ := ra
    generalize hrb : compileExpr b (offset + codeA.length) tmp1 = rb at hcode ⊢
    obtain ⟨codeB, vb, tmp2⟩ := rb
    simp only [] at hcode ⊢
    have hcodeA : RC.CodeAt (compileExpr a offset nextTmp).1 p offset := by
      rw [hra]; exact hcode.left
    have hcodeB : RC.CodeAt (compileExpr b (offset + codeA.length) tmp1).1 p
        (offset + codeA.length) := by rw [hrb]; exact hcode.right
    obtain ⟨σ_a, hexec_a, hval_a, hntmp_a, hprev_a, hfprev_a, hbprev_a⟩ :=
      compileExpr_correct a offset nextTmp σ σ_tac am p htf_a hftf_a htbf_a htv_a hsa hagree hcodeA
    rw [hra] at hexec_a hval_a; simp at hexec_a hval_a
    have hagree_a : ∀ v, v.isTmp = false → v.isFTmp = false → v.isBTmp = false → σ_a v = σ v := by
      intro v hv1 hv2 hv3; rw [hntmp_a v hv1 hv2 hv3]; exact hagree v hv1 hv2 hv3
    have hge_a := compileExpr_nextTmp_ge a offset nextTmp
    rw [hra] at hge_a; simp at hge_a
    obtain ⟨σ_b, hexec_b, hval_b, hntmp_b, hprev_b, hfprev_b, hbprev_b⟩ :=
      compileExpr_correct b (offset + codeA.length) tmp1 σ σ_a am p htf_b hftf_b htbf_b htv_b hsb hagree_a hcodeB
    rw [hrb] at hexec_b hval_b; simp at hexec_b hval_b
    -- va preserved through b's execution
    have hva_b : σ_b va = σ_a va := by
      rcases compileExpr_result_bound a offset nextTmp htf_a with h | ⟨k, _, hlt, heq⟩
      · rw [hra] at h; simp at h
        rcases compileExpr_result_ftmp_bound a offset nextTmp hftf_a with h2 | ⟨k, _, hlt2, heq2⟩
        · rw [hra] at h2; simp at h2
          have h3 : va.isBTmp = false := by
            have := compileExpr_result_isBTmp_false a offset nextTmp htbf_a
            rw [hra] at this; simpa using this
          exact hntmp_b va h h2 h3
        · rw [hra] at hlt2 heq2; simp at hlt2 heq2
          rw [heq2, hfprev_b k (by omega)]
      · rw [hra] at hlt heq; simp at hlt heq
        rw [heq, hprev_b k (by omega)]
    refine ⟨σ_b, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have := FragExec.trans' hexec_a hexec_b
      simp only [List.length_append] at this ⊢; rwa [Nat.add_assoc] at this
    · simp only [BoolExpr.eval, Expr.eval, SBool.eval]
      have hva : σ_b va = .int (a.eval σ am) := by rw [hva_b, hval_a, hwrap_a]
      have hvb : σ_b vb = .int (b.eval σ am) := by rw [hval_b, hwrap_b]
      rw [hva, hvb]; simp [Value.toInt]
    · intro w hw1 hw2 hw3; rw [hntmp_b w hw1 hw2 hw3, hntmp_a w hw1 hw2 hw3]
    · intro k hk
      have hle_b : tmp1 ≤ tmp2 := by
        have := compileExpr_nextTmp_ge b (offset + codeA.length) tmp1; rw [hrb] at this; simpa using this
      rw [hprev_b k (by omega), hprev_a k hk]
    · intro k hk
      have hle_b : tmp1 ≤ tmp2 := by
        have := compileExpr_nextTmp_ge b (offset + codeA.length) tmp1; rw [hrb] at this; simpa using this
      rw [hfprev_b k (by omega), hfprev_a k hk]
    · intro k hk
      have hle_b : tmp1 ≤ tmp2 := by
        have := compileExpr_nextTmp_ge b (offset + codeA.length) tmp1; rw [hrb] at this; simpa using this
      rw [hbprev_b k (by omega), hbprev_a k hk]
  | not e ih =>
    simp only [SBool.safe] at hbsafe
    dsimp only [compileBool] at hcode ⊢
    generalize hrc : compileBool e offset nextTmp = rc at hcode ⊢
    obtain ⟨code, be, tmp'⟩ := rc
    simp only [] at hcode ⊢
    have hcodeE : RC.CodeAt (compileBool e offset nextTmp).1 p offset := by
      rw [hrc]; exact hcode
    obtain ⟨σ', hexec, heval, hntmp, hprev, hfprev, hbprev⟩ :=
      ih offset nextTmp σ_tac htf hftf htbf htypedv hbsafe hagree hcodeE
    rw [hrc] at hexec heval; simp at hexec heval
    exact ⟨σ', hexec, by simp [BoolExpr.eval, SBool.eval, heval], hntmp, hprev, hfprev, hbprev⟩
  | and a b iha ihb =>
    have htf_a : ∀ v ∈ a.freeVars, v.isTmp = false :=
      fun v hv => htf v (List.mem_append_left _ hv)
    have htf_b : ∀ v ∈ b.freeVars, v.isTmp = false :=
      fun v hv => htf v (List.mem_append_right _ hv)
    have hftf_a : ∀ v ∈ a.freeVars, v.isFTmp = false :=
      fun v hv => hftf v (List.mem_append_left _ hv)
    have hftf_b : ∀ v ∈ b.freeVars, v.isFTmp = false :=
      fun v hv => hftf v (List.mem_append_right _ hv)
    have htbf_a : ∀ v ∈ a.freeVars, v.isBTmp = false :=
      fun v hv => htbf v (List.mem_append_left _ hv)
    have htbf_b : ∀ v ∈ b.freeVars, v.isBTmp = false :=
      fun v hv => htbf v (List.mem_append_right _ hv)
    have ⟨htypedv_a, htypedv_b⟩ : a.typedVars σ am ∧ b.typedVars σ am := htypedv
    unfold SBool.safe at hbsafe
    obtain ⟨hbsafe_a, hbsafe_b_imp⟩ := hbsafe
    dsimp only [compileBool] at hcode ⊢
    generalize hra : compileBool a offset nextTmp = ra at hcode ⊢
    obtain ⟨codeA, ba, tmp1⟩ := ra
    generalize hrb : compileBool b (offset + codeA.length + 1) (tmp1 + 1) = rb at hcode ⊢
    obtain ⟨codeB, bb, tmp2⟩ := rb
    simp only [] at hcode ⊢
    have hcodeA : RC.CodeAt (compileBool a offset nextTmp).1 p offset := by
      rw [hra]; exact hcode.left.left.left
    have hifgA : p[offset + codeA.length]? = some (TAC.ifgoto (.not ba) (offset + codeA.length + 1 + codeB.length + 3)) := by
      exact hcode.left.left.right.head
    have hcodeB : RC.CodeAt (compileBool b (offset + codeA.length + 1) (tmp1 + 1)).1 p
        (offset + codeA.length + 1) := by
      rw [hrb]
      have h := hcode.left.right
      simp only [List.length_append, List.length_cons, List.length_nil] at h
      rwa [show offset + (codeA.length + 1) = offset + codeA.length + 1 from by omega] at h
    have htail := hcode.right
    simp only [List.length_append, List.length_cons, List.length_nil] at htail
    have hifgB : p[offset + codeA.length + 1 + codeB.length]? =
        some (TAC.ifgoto (.not bb) (offset + codeA.length + 1 + codeB.length + 3)) := by
      have h := htail 0 (by simp)
      simp only [List.getElem?_cons_zero] at h
      rwa [show offset + (codeA.length + 1 + codeB.length) + 0 = offset + codeA.length + 1 + codeB.length from by omega] at h
    have hconst1 : p[offset + codeA.length + 1 + codeB.length + 1]? =
        some (TAC.const (tmpName tmp1) (.int 1)) := by
      have h := htail 1 (by simp)
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at h
      rwa [show offset + (codeA.length + 1 + codeB.length) + 1 = offset + codeA.length + 1 + codeB.length + 1 from by omega] at h
    have hgoto_end : p[offset + codeA.length + 1 + codeB.length + 2]? =
        some (TAC.goto (offset + codeA.length + 1 + codeB.length + 3 + 1)) := by
      have h := htail 2 (by simp)
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at h
      rwa [show offset + (codeA.length + 1 + codeB.length) + 2 = offset + codeA.length + 1 + codeB.length + 2 from by omega] at h
    have hconst0 : p[offset + codeA.length + 1 + codeB.length + 3]? =
        some (TAC.const (tmpName tmp1) (.int 0)) := by
      have h := htail 3 (by simp)
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, List.getElem?_nil] at h
      rwa [show offset + (codeA.length + 1 + codeB.length) + 3 = offset + codeA.length + 1 + codeB.length + 3 from by omega] at h
    have hge_a : nextTmp ≤ tmp1 := by
      have := compileBool_nextTmp_ge a offset nextTmp; rw [hra] at this; simpa using this
    have hge_b : tmp1 + 1 ≤ tmp2 := by
      have := compileBool_nextTmp_ge b (offset + codeA.length + 1) (tmp1 + 1)
      rw [hrb] at this; simpa using this
    obtain ⟨σ_a, hexec_a, heval_a, hntmp_a, hprev_a, hfprev_a, hbprev_a⟩ :=
      iha offset nextTmp σ_tac htf_a hftf_a htbf_a htypedv_a hbsafe_a hagree hcodeA
    rw [hra] at hexec_a heval_a; simp at hexec_a heval_a
    have hagree_a : ∀ v, v.isTmp = false → v.isFTmp = false → v.isBTmp = false → σ_a v = σ v := by
      intro v hv1 hv2 hv3; rw [hntmp_a v hv1 hv2 hv3]; exact hagree v hv1 hv2 hv3
    by_cases ha_eval : a.eval σ am = true
    · have hbsafe_b : b.safe σ am p.arrayDecls := hbsafe_b_imp ha_eval
      have hba_true : ba.eval σ_a am = true := by rw [heval_a, ha_eval]
      have hnot_ba_false : (BoolExpr.not ba).eval σ_a am = false := by
        simp [BoolExpr.eval, hba_true]
      have hexec_ifA := FragExec.single_iffalse (am := am) hifgA hnot_ba_false
      obtain ⟨σ_b, hexec_b, heval_b, hntmp_b, hprev_b, hfprev_b, hbprev_b⟩ :=
        ihb (offset + codeA.length + 1) (tmp1 + 1) σ_a htf_b hftf_b htbf_b htypedv_b hbsafe_b hagree_a hcodeB
      rw [hrb] at hexec_b heval_b; simp at hexec_b heval_b
      by_cases hb_eval : b.eval σ am = true
      · have hbb_true : bb.eval σ_b am = true := by rw [heval_b, hb_eval]
        have hnot_bb_false : (BoolExpr.not bb).eval σ_b am = false := by
          simp [BoolExpr.eval, hbb_true]
        have hexec_ifB := FragExec.single_iffalse (am := am) hifgB hnot_bb_false
        have hexec_c1 : FragExec p _ σ_b _ (σ_b[tmpName tmp1 ↦ .int 1]) am am :=
          FragExec.single_const (am := am) hconst1
        have hexec_goto : FragExec p _ (σ_b[tmpName tmp1 ↦ .int 1]) _ (σ_b[tmpName tmp1 ↦ .int 1]) am am :=
          FragExec.single_goto (am := am) hgoto_end
        let σ_final := σ_b[tmpName tmp1 ↦ .int 1]
        refine ⟨σ_final, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · have h := FragExec.trans' (FragExec.trans' (FragExec.trans' (FragExec.trans' hexec_a hexec_ifA) hexec_b) hexec_ifB) (FragExec.trans' hexec_c1 hexec_goto)
          simp only [List.length_append, List.length_cons, List.length_nil] at h ⊢
          convert h using 1; omega
        · simp only [BoolExpr.eval, Expr.eval, CmpOp.eval, σ_final, Store.update_self, Value.toInt]
          simp [SBool.eval, ha_eval, hb_eval]
        · intro w hw1 hw2 hw3
          simp only [σ_final]
          rw [Store.update_isTmp_ne (tmpName_isTmp tmp1) hw1, hntmp_b w hw1 hw2 hw3, hntmp_a w hw1 hw2 hw3]
        · intro k hk
          simp only [σ_final]
          rw [Store.update_tmpName_ne (by omega), hprev_b k (by omega), hprev_a k hk]
        · intro k hk
          simp only [σ_final]
          rw [Store.update_other _ _ _ _ (Ne.symm tmpName_ne_ftmpName), hfprev_b k (by omega), hfprev_a k hk]
        · intro k hk
          simp only [σ_final]
          rw [Store.update_other _ _ _ _ (Ne.symm tmpName_ne_btmpName), hbprev_b k (by omega), hbprev_a k hk]
      · have hb_false : b.eval σ am = false := Bool.eq_false_iff.mpr hb_eval
        have hbb_false : bb.eval σ_b am = false := by rw [heval_b, hb_false]
        have hnot_bb_true : (BoolExpr.not bb).eval σ_b am = true := by
          simp [BoolExpr.eval, hbb_false]
        have hexec_ifB := FragExec.single_iftrue (am := am) hifgB hnot_bb_true
        have hexec_c0 : FragExec p _ σ_b _ (σ_b[tmpName tmp1 ↦ .int 0]) am am :=
          FragExec.single_const (am := am) hconst0
        let σ_final := σ_b[tmpName tmp1 ↦ .int 0]
        refine ⟨σ_final, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · have h := FragExec.trans' (FragExec.trans' (FragExec.trans' (FragExec.trans' hexec_a hexec_ifA) hexec_b) hexec_ifB) hexec_c0
          simp only [List.length_append, List.length_cons, List.length_nil] at h ⊢
          convert h using 1; omega
        · simp only [BoolExpr.eval, Expr.eval, CmpOp.eval, σ_final, Store.update_self, Value.toInt]
          simp [SBool.eval, ha_eval, hb_false]
        · intro w hw1 hw2 hw3
          simp only [σ_final]
          rw [Store.update_isTmp_ne (tmpName_isTmp tmp1) hw1, hntmp_b w hw1 hw2 hw3, hntmp_a w hw1 hw2 hw3]
        · intro k hk
          simp only [σ_final]
          rw [Store.update_tmpName_ne (by omega), hprev_b k (by omega), hprev_a k hk]
        · intro k hk
          simp only [σ_final]
          rw [Store.update_other _ _ _ _ (Ne.symm tmpName_ne_ftmpName), hfprev_b k (by omega), hfprev_a k hk]
        · intro k hk
          simp only [σ_final]
          rw [Store.update_other _ _ _ _ (Ne.symm tmpName_ne_btmpName), hbprev_b k (by omega), hbprev_a k hk]
    · have ha_false : a.eval σ am = false := Bool.eq_false_iff.mpr ha_eval
      have hba_false : ba.eval σ_a am = false := by rw [heval_a, ha_false]
      have hnot_ba_true : (BoolExpr.not ba).eval σ_a am = true := by
        simp [BoolExpr.eval, hba_false]
      have hexec_ifA := FragExec.single_iftrue (am := am) hifgA hnot_ba_true
      have hexec_c0 : FragExec p _ σ_a _ (σ_a[tmpName tmp1 ↦ .int 0]) am am :=
        FragExec.single_const (am := am) hconst0
      let σ_final := σ_a[tmpName tmp1 ↦ .int 0]
      refine ⟨σ_final, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · have h := FragExec.trans' (FragExec.trans' hexec_a hexec_ifA) hexec_c0
        simp only [List.length_append, List.length_cons, List.length_nil] at h ⊢
        convert h using 1; omega
      · simp only [BoolExpr.eval, Expr.eval, CmpOp.eval, σ_final, Store.update_self, Value.toInt]
        simp [SBool.eval, ha_false]
      · intro w hw1 hw2 hw3
        simp only [σ_final]
        rw [Store.update_isTmp_ne (tmpName_isTmp tmp1) hw1, hntmp_a w hw1 hw2 hw3]
      · intro k hk
        simp only [σ_final]
        rw [Store.update_tmpName_ne (by omega), hprev_a k hk]
      · intro k hk
        simp only [σ_final]
        rw [Store.update_other _ _ _ _ (Ne.symm tmpName_ne_ftmpName), hfprev_a k hk]
      · intro k hk
        simp only [σ_final]
        rw [Store.update_other _ _ _ _ (Ne.symm tmpName_ne_btmpName), hbprev_a k hk]
  | or a b iha ihb =>
    have htf_a : ∀ v ∈ a.freeVars, v.isTmp = false :=
      fun v hv => htf v (List.mem_append_left _ hv)
    have htf_b : ∀ v ∈ b.freeVars, v.isTmp = false :=
      fun v hv => htf v (List.mem_append_right _ hv)
    have hftf_a : ∀ v ∈ a.freeVars, v.isFTmp = false :=
      fun v hv => hftf v (List.mem_append_left _ hv)
    have hftf_b : ∀ v ∈ b.freeVars, v.isFTmp = false :=
      fun v hv => hftf v (List.mem_append_right _ hv)
    have htbf_a : ∀ v ∈ a.freeVars, v.isBTmp = false :=
      fun v hv => htbf v (List.mem_append_left _ hv)
    have htbf_b : ∀ v ∈ b.freeVars, v.isBTmp = false :=
      fun v hv => htbf v (List.mem_append_right _ hv)
    have ⟨htypedv_a, htypedv_b⟩ : a.typedVars σ am ∧ b.typedVars σ am := htypedv
    unfold SBool.safe at hbsafe
    obtain ⟨hbsafe_a, hbsafe_b_imp⟩ := hbsafe
    dsimp only [compileBool] at hcode ⊢
    generalize hra : compileBool a offset nextTmp = ra at hcode ⊢
    obtain ⟨codeA, ba, tmp1⟩ := ra
    generalize hrb : compileBool b (offset + codeA.length + 1) (tmp1 + 1) = rb at hcode ⊢
    obtain ⟨codeB, bb, tmp2⟩ := rb
    simp only [] at hcode ⊢
    have hcodeA : RC.CodeAt (compileBool a offset nextTmp).1 p offset := by
      rw [hra]; exact hcode.left.left.left
    have hifgA : p[offset + codeA.length]? = some (TAC.ifgoto ba (offset + codeA.length + 1 + codeB.length + 3)) := by
      exact hcode.left.left.right.head
    have hcodeB : RC.CodeAt (compileBool b (offset + codeA.length + 1) (tmp1 + 1)).1 p
        (offset + codeA.length + 1) := by
      rw [hrb]
      have h := hcode.left.right
      simp only [List.length_append, List.length_cons, List.length_nil] at h
      rwa [show offset + (codeA.length + 1) = offset + codeA.length + 1 from by omega] at h
    have htail := hcode.right
    simp only [List.length_append, List.length_cons, List.length_nil] at htail
    have hifgB : p[offset + codeA.length + 1 + codeB.length]? =
        some (TAC.ifgoto bb (offset + codeA.length + 1 + codeB.length + 3)) := by
      have h := htail 0 (by simp)
      simp only [List.getElem?_cons_zero] at h
      rwa [show offset + (codeA.length + 1 + codeB.length) + 0 = offset + codeA.length + 1 + codeB.length from by omega] at h
    have hconst0 : p[offset + codeA.length + 1 + codeB.length + 1]? =
        some (TAC.const (tmpName tmp1) (.int 0)) := by
      have h := htail 1 (by simp)
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at h
      rwa [show offset + (codeA.length + 1 + codeB.length) + 1 = offset + codeA.length + 1 + codeB.length + 1 from by omega] at h
    have hgoto_end : p[offset + codeA.length + 1 + codeB.length + 2]? =
        some (TAC.goto (offset + codeA.length + 1 + codeB.length + 3 + 1)) := by
      have h := htail 2 (by simp)
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at h
      rwa [show offset + (codeA.length + 1 + codeB.length) + 2 = offset + codeA.length + 1 + codeB.length + 2 from by omega] at h
    have hconst1 : p[offset + codeA.length + 1 + codeB.length + 3]? =
        some (TAC.const (tmpName tmp1) (.int 1)) := by
      have h := htail 3 (by simp)
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, List.getElem?_nil] at h
      rwa [show offset + (codeA.length + 1 + codeB.length) + 3 = offset + codeA.length + 1 + codeB.length + 3 from by omega] at h
    have hge_a : nextTmp ≤ tmp1 := by
      have := compileBool_nextTmp_ge a offset nextTmp; rw [hra] at this; simpa using this
    have hge_b : tmp1 + 1 ≤ tmp2 := by
      have := compileBool_nextTmp_ge b (offset + codeA.length + 1) (tmp1 + 1)
      rw [hrb] at this; simpa using this
    obtain ⟨σ_a, hexec_a, heval_a, hntmp_a, hprev_a, hfprev_a, hbprev_a⟩ :=
      iha offset nextTmp σ_tac htf_a hftf_a htbf_a htypedv_a hbsafe_a hagree hcodeA
    rw [hra] at hexec_a heval_a; simp at hexec_a heval_a
    have hagree_a : ∀ v, v.isTmp = false → v.isFTmp = false → v.isBTmp = false → σ_a v = σ v := by
      intro v hv1 hv2 hv3; rw [hntmp_a v hv1 hv2 hv3]; exact hagree v hv1 hv2 hv3
    by_cases ha_eval : a.eval σ am = true
    · have hba_true : ba.eval σ_a am = true := by rw [heval_a, ha_eval]
      have hexec_ifA := FragExec.single_iftrue (am := am) hifgA hba_true
      have hexec_c1 : FragExec p _ σ_a _ (σ_a[tmpName tmp1 ↦ .int 1]) am am :=
        FragExec.single_const (am := am) hconst1
      let σ_final := σ_a[tmpName tmp1 ↦ .int 1]
      refine ⟨σ_final, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · have h := FragExec.trans' (FragExec.trans' hexec_a hexec_ifA) hexec_c1
        simp only [List.length_append, List.length_cons, List.length_nil] at h ⊢
        convert h using 1; omega
      · simp only [BoolExpr.eval, Expr.eval, CmpOp.eval, σ_final, Store.update_self, Value.toInt]
        simp [SBool.eval, ha_eval]
      · intro w hw1 hw2 hw3
        simp only [σ_final]
        rw [Store.update_isTmp_ne (tmpName_isTmp tmp1) hw1, hntmp_a w hw1 hw2 hw3]
      · intro k hk
        simp only [σ_final]
        rw [Store.update_tmpName_ne (by omega), hprev_a k hk]
      · intro k hk
        simp only [σ_final]
        rw [Store.update_other _ _ _ _ (Ne.symm tmpName_ne_ftmpName), hfprev_a k hk]
      · intro k hk
        simp only [σ_final]
        rw [Store.update_other _ _ _ _ (Ne.symm tmpName_ne_btmpName), hbprev_a k hk]
    · have ha_false : a.eval σ am = false := Bool.eq_false_iff.mpr ha_eval
      have hbsafe_b : b.safe σ am p.arrayDecls := hbsafe_b_imp ha_false
      have hba_false : ba.eval σ_a am = false := by rw [heval_a, ha_false]
      have hexec_ifA := FragExec.single_iffalse (am := am) hifgA hba_false
      obtain ⟨σ_b, hexec_b, heval_b, hntmp_b, hprev_b, hfprev_b, hbprev_b⟩ :=
        ihb (offset + codeA.length + 1) (tmp1 + 1) σ_a htf_b hftf_b htbf_b htypedv_b hbsafe_b hagree_a hcodeB
      rw [hrb] at hexec_b heval_b; simp at hexec_b heval_b
      by_cases hb_eval : b.eval σ am = true
      · have hbb_true : bb.eval σ_b am = true := by rw [heval_b, hb_eval]
        have hexec_ifB := FragExec.single_iftrue (am := am) hifgB hbb_true
        have hexec_c1 : FragExec p _ σ_b _ (σ_b[tmpName tmp1 ↦ .int 1]) am am :=
          FragExec.single_const (am := am) hconst1
        let σ_final := σ_b[tmpName tmp1 ↦ .int 1]
        refine ⟨σ_final, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · have h := FragExec.trans' (FragExec.trans' (FragExec.trans' (FragExec.trans' hexec_a hexec_ifA) hexec_b) hexec_ifB) hexec_c1
          simp only [List.length_append, List.length_cons, List.length_nil] at h ⊢
          convert h using 1; omega
        · simp only [BoolExpr.eval, Expr.eval, CmpOp.eval, σ_final, Store.update_self, Value.toInt]
          simp [SBool.eval, ha_false, hb_eval]
        · intro w hw1 hw2 hw3
          simp only [σ_final]
          rw [Store.update_isTmp_ne (tmpName_isTmp tmp1) hw1, hntmp_b w hw1 hw2 hw3, hntmp_a w hw1 hw2 hw3]
        · intro k hk
          simp only [σ_final]
          rw [Store.update_tmpName_ne (by omega), hprev_b k (by omega), hprev_a k hk]
        · intro k hk
          simp only [σ_final]
          rw [Store.update_other _ _ _ _ (Ne.symm tmpName_ne_ftmpName), hfprev_b k (by omega), hfprev_a k hk]
        · intro k hk
          simp only [σ_final]
          rw [Store.update_other _ _ _ _ (Ne.symm tmpName_ne_btmpName), hbprev_b k (by omega), hbprev_a k hk]
      · have hb_false : b.eval σ am = false := Bool.eq_false_iff.mpr hb_eval
        have hbb_false : bb.eval σ_b am = false := by rw [heval_b, hb_false]
        have hexec_ifB := FragExec.single_iffalse (am := am) hifgB hbb_false
        have hexec_c0 : FragExec p _ σ_b _ (σ_b[tmpName tmp1 ↦ .int 0]) am am :=
          FragExec.single_const (am := am) hconst0
        have hexec_goto : FragExec p _ (σ_b[tmpName tmp1 ↦ .int 0]) _ (σ_b[tmpName tmp1 ↦ .int 0]) am am :=
          FragExec.single_goto (am := am) hgoto_end
        let σ_final := σ_b[tmpName tmp1 ↦ .int 0]
        refine ⟨σ_final, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · have h := FragExec.trans' (FragExec.trans' (FragExec.trans' (FragExec.trans' hexec_a hexec_ifA) hexec_b) hexec_ifB) (FragExec.trans' hexec_c0 hexec_goto)
          simp only [List.length_append, List.length_cons, List.length_nil] at h ⊢
          convert h using 1; omega
        · simp only [BoolExpr.eval, Expr.eval, CmpOp.eval, σ_final, Store.update_self, Value.toInt]
          simp [SBool.eval, ha_false, hb_false]
        · intro w hw1 hw2 hw3
          simp only [σ_final]
          rw [Store.update_isTmp_ne (tmpName_isTmp tmp1) hw1, hntmp_b w hw1 hw2 hw3, hntmp_a w hw1 hw2 hw3]
        · intro k hk
          simp only [σ_final]
          rw [Store.update_tmpName_ne (by omega), hprev_b k (by omega), hprev_a k hk]
        · intro k hk
          simp only [σ_final]
          rw [Store.update_other _ _ _ _ (Ne.symm tmpName_ne_ftmpName), hfprev_b k (by omega), hfprev_a k hk]
        · intro k hk
          simp only [σ_final]
          rw [Store.update_other _ _ _ _ (Ne.symm tmpName_ne_btmpName), hbprev_b k (by omega), hbprev_a k hk]
  | barrRead arr idx =>
    have htf_idx : ∀ v ∈ idx.freeVars, v.isTmp = false :=
      fun v hv => htf v hv
    have hftf_idx : ∀ v ∈ idx.freeVars, v.isFTmp = false :=
      fun v hv => hftf v hv
    have htbf_idx : ∀ v ∈ idx.freeVars, v.isBTmp = false :=
      fun v hv => htbf v hv
    obtain ⟨htv_idx, hwrap_idx⟩ : idx.typedVars σ am ∧ idx.wrapEval σ am = .int (idx.eval σ am) := htypedv
    have hsafe_idx : idx.safe σ am p.arrayDecls := hbsafe.1
    dsimp only [compileBool] at hcode ⊢
    generalize hri : compileExpr idx offset nextTmp = ri at hcode ⊢
    obtain ⟨codeIdx, vIdx, tmp1⟩ := ri
    simp only [] at hcode ⊢
    have hcodeIdx : RC.CodeAt (compileExpr idx offset nextTmp).1 p offset := by
      rw [hri]; exact hcode.left
    have harrLoad : p[offset + codeIdx.length]? = some (.arrLoad (btmpName tmp1) arr vIdx .bool) := by
      have := hcode.right.head; simpa using this
    obtain ⟨σ_idx, hexec_idx, hval_idx, hntmp_idx, hprev_idx, hfprev_idx, hbprev_idx⟩ :=
      compileExpr_correct idx offset nextTmp σ σ_tac am p htf_idx hftf_idx htbf_idx htv_idx hsafe_idx hagree hcodeIdx
    rw [hri] at hexec_idx hval_idx; simp at hexec_idx hval_idx
    rw [hwrap_idx] at hval_idx
    have hbounds : (SExpr.eval σ am idx) < p.arraySizeBv arr := by
      simp only [SBool.safe] at hbsafe; exact hbsafe.2
    have hexec_arrLoad := FragExec.single_arrLoad_bool (am := am) harrLoad hval_idx hbounds
    set σ_load := σ_idx[btmpName tmp1 ↦ .bool (am.read arr (idx.eval σ am) != 0)]
    have hge := compileExpr_nextTmp_ge idx offset nextTmp
    rw [hri] at hge; simp at hge
    refine ⟨σ_load, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have h12 := FragExec.trans' hexec_idx hexec_arrLoad
      simp only [List.length_append, List.length_cons, List.length_nil] at h12 ⊢
      exact h12
    · -- BoolExpr.bvar (btmpName tmp1) evaluates via σ_load to (σ_load (btmpName tmp1)).toBool
      simp only [BoolExpr.eval, σ_load, Store.update_self, Value.toBool, SBool.eval]
    · intro w hw1 hw2 hw3
      simp only [σ_load]
      rw [Store.update_isBTmp_ne (btmpName_isBTmp tmp1) hw3, hntmp_idx w hw1 hw2 hw3]
    · intro k hk
      simp only [σ_load]
      rw [Store.update_other _ _ _ _ tmpName_ne_btmpName, hprev_idx k hk]
    · intro k hk
      simp only [σ_load]
      rw [Store.update_other _ _ _ _ ftmpName_ne_btmpName, hfprev_idx k hk]
    · intro k hk
      simp only [σ_load]
      rw [Store.update_btmpName_ne (by omega), hbprev_idx k hk]
  | fcmp cop a b =>
    have htf_a : ∀ v ∈ a.freeVars, v.isTmp = false :=
      fun v hv => htf v (List.mem_append_left _ hv)
    have htf_b : ∀ v ∈ b.freeVars, v.isTmp = false :=
      fun v hv => htf v (List.mem_append_right _ hv)
    have hftf_a : ∀ v ∈ a.freeVars, v.isFTmp = false :=
      fun v hv => hftf v (List.mem_append_left _ hv)
    have hftf_b : ∀ v ∈ b.freeVars, v.isFTmp = false :=
      fun v hv => hftf v (List.mem_append_right _ hv)
    have htbf_a : ∀ v ∈ a.freeVars, v.isBTmp = false :=
      fun v hv => htbf v (List.mem_append_left _ hv)
    have htbf_b : ∀ v ∈ b.freeVars, v.isBTmp = false :=
      fun v hv => htbf v (List.mem_append_right _ hv)
    obtain ⟨htv_a, htv_b, hwrap_a, hwrap_b⟩ :=
      show a.typedVars σ am ∧ b.typedVars σ am ∧
           a.wrapEval σ am = .float (a.eval σ am) ∧ b.wrapEval σ am = .float (b.eval σ am) from htypedv
    simp only [SBool.safe] at hbsafe; obtain ⟨hsa, hsb⟩ := hbsafe
    dsimp only [compileBool] at hcode ⊢
    generalize hra : compileExpr a offset nextTmp = ra at hcode ⊢
    obtain ⟨codeA, va, tmp1⟩ := ra
    generalize hrb : compileExpr b (offset + codeA.length) tmp1 = rb at hcode ⊢
    obtain ⟨codeB, vb, tmp2⟩ := rb
    simp only [] at hcode ⊢
    have hcodeA : RC.CodeAt (compileExpr a offset nextTmp).1 p offset := by
      rw [hra]; exact hcode.left
    have hcodeB : RC.CodeAt (compileExpr b (offset + codeA.length) tmp1).1 p
        (offset + codeA.length) := by rw [hrb]; exact hcode.right
    obtain ⟨σ_a, hexec_a, hval_a, hntmp_a, hprev_a, hfprev_a, hbprev_a⟩ :=
      compileExpr_correct a offset nextTmp σ σ_tac am p htf_a hftf_a htbf_a htv_a hsa hagree hcodeA
    rw [hra] at hexec_a hval_a; simp at hexec_a hval_a
    have hagree_a : ∀ v, v.isTmp = false → v.isFTmp = false → v.isBTmp = false → σ_a v = σ v := by
      intro v hv1 hv2 hv3; rw [hntmp_a v hv1 hv2 hv3]; exact hagree v hv1 hv2 hv3
    have hge_a := compileExpr_nextTmp_ge a offset nextTmp
    rw [hra] at hge_a; simp at hge_a
    obtain ⟨σ_b, hexec_b, hval_b, hntmp_b, hprev_b, hfprev_b, hbprev_b⟩ :=
      compileExpr_correct b (offset + codeA.length) tmp1 σ σ_a am p htf_b hftf_b htbf_b htv_b hsb hagree_a hcodeB
    rw [hrb] at hexec_b hval_b; simp at hexec_b hval_b
    -- va preserved through b's execution (va may be source var, tmpName, or ftmpName)
    have hva_b : σ_b va = σ_a va := by
      rcases compileExpr_result_bound a offset nextTmp htf_a with h | ⟨k, _, hlt, heq⟩
      · rw [hra] at h; simp at h
        rcases compileExpr_result_ftmp_bound a offset nextTmp hftf_a with h2 | ⟨k, _, hlt2, heq2⟩
        · rw [hra] at h2; simp at h2
          have h3 : va.isBTmp = false := by
            have := compileExpr_result_isBTmp_false a offset nextTmp htbf_a
            rw [hra] at this; simpa using this
          exact hntmp_b va h h2 h3
        · rw [hra] at hlt2 heq2; simp at hlt2 heq2
          rw [heq2, hfprev_b k (by omega)]
      · rw [hra] at hlt heq; simp at hlt heq
        rw [heq, hprev_b k (by omega)]
    refine ⟨σ_b, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have := FragExec.trans' hexec_a hexec_b
      simp only [List.length_append] at this ⊢; rwa [Nat.add_assoc] at this
    · simp only [BoolExpr.eval, Expr.eval, SBool.eval]
      have hva : σ_b va = .float (a.eval σ am) := by rw [hva_b, hval_a, hwrap_a]
      have hvb : σ_b vb = .float (b.eval σ am) := by rw [hval_b, hwrap_b]
      rw [hva, hvb]; simp [Value.toFloat]
    · intro w hw1 hw2 hw3; rw [hntmp_b w hw1 hw2 hw3, hntmp_a w hw1 hw2 hw3]
    · intro k hk
      have hle_b : tmp1 ≤ tmp2 := by
        have := compileExpr_nextTmp_ge b (offset + codeA.length) tmp1; rw [hrb] at this; simpa using this
      rw [hprev_b k (by omega), hprev_a k hk]
    · intro k hk
      have hle_b : tmp1 ≤ tmp2 := by
        have := compileExpr_nextTmp_ge b (offset + codeA.length) tmp1; rw [hrb] at this; simpa using this
      rw [hfprev_b k (by omega), hfprev_a k hk]
    · intro k hk
      have hle_b : tmp1 ≤ tmp2 := by
        have := compileExpr_nextTmp_ge b (offset + codeA.length) tmp1; rw [hrb] at this; simpa using this
      rw [hbprev_b k (by omega), hbprev_a k hk]

-- ============================================================
-- § 10a. safe → isSafe bridges (local copies, needed before Metatheory import)
-- ============================================================

private theorem isSafe_of_safe_expr (e : SExpr) (σ : Store) (am : ArrayMem) (decls)
    (h : e.safe σ am decls) : e.isSafe σ am decls = true := by
  induction e with
  | lit _ => simp [SExpr.isSafe]
  | var _ => simp [SExpr.isSafe]
  | bin op a b iha ihb => cases op <;> simp_all [SExpr.safe, SExpr.isSafe, decide_eq_true_eq]
  | arrRead arr idx ih => simp [SExpr.safe] at h; simp [SExpr.isSafe, ih h.1, decide_eq_true_eq, h.2]
  | flit _ => simp [SExpr.isSafe]
  | fbin _ a b iha ihb => simp [SExpr.safe] at h; simp [SExpr.isSafe, iha h.1, ihb h.2]
  | intToFloat e ih => simp [SExpr.safe] at h; simp [SExpr.isSafe, ih h]
  | floatToInt e ih => simp [SExpr.safe] at h; simp [SExpr.isSafe, ih h]
  | floatUnary op e ih => simp [SExpr.safe] at h; simp [SExpr.isSafe, ih h]
  | farrRead arr idx ih => simp [SExpr.safe] at h; simp [SExpr.isSafe, ih h.1, decide_eq_true_eq, h.2]

private theorem isSafe_of_safe_bool (sb : SBool) (σ : Store) (am : ArrayMem) (decls)
    (h : sb.safe σ am decls) : sb.isSafe σ am decls = true := by
  induction sb with
  | lit _ => simp [SBool.isSafe]
  | bvar _ => simp [SBool.isSafe]
  | cmp _ a b => simp [SBool.safe] at h; simp [SBool.isSafe, isSafe_of_safe_expr a σ am decls h.1, isSafe_of_safe_expr b σ am decls h.2]
  | not e ih => simp [SBool.safe] at h; simp [SBool.isSafe, ih h]
  | and a b iha ihb => simp [SBool.safe] at h; simp only [SBool.isSafe, iha h.1, Bool.true_and]; split <;> simp_all
  | or a b iha ihb => simp [SBool.safe] at h; simp only [SBool.isSafe, iha h.1, Bool.true_and]; split <;> simp_all
  | barrRead arr idx => simp [SBool.safe] at h; simp [SBool.isSafe, isSafe_of_safe_expr idx σ am decls h.1, decide_eq_true_eq, h.2]
  | fcmp _ a b => simp [SBool.safe] at h; simp [SBool.isSafe, isSafe_of_safe_expr a σ am decls h.1, isSafe_of_safe_expr b σ am decls h.2]

-- ============================================================
-- § 10b. compileExprs helpers (for print statement)
-- ============================================================

/-- All expressions in a list compile correctly: the generated code executes as a
    `FragExec`. The final store agrees with `σ_tac` on non-temp vars and on
    temp indices below `nextTmp`. -/
private theorem compileExprs_correct (args : List SExpr) (offset nextTmp : Nat)
    (σ σ_tac : Store) (am : ArrayMem) (p : Prog)
    (htf : ∀ v ∈ args.flatMap SExpr.freeVars, v.isTmp = false)
    (hftf : ∀ v ∈ args.flatMap SExpr.freeVars, v.isFTmp = false)
    (htbf : ∀ v ∈ args.flatMap SExpr.freeVars, v.isBTmp = false)
    (htypedv : ∀ e ∈ args, e.typedVars σ am)
    (hsafe : ∀ e ∈ args, e.safe σ am p.arrayDecls)
    (hagree : ∀ v, v.isTmp = false → v.isFTmp = false → v.isBTmp = false → σ_tac v = σ v)
    (hcode : RC.CodeAt (compileExprs args offset nextTmp).1 p offset) :
    ∃ σ', FragExec p offset σ_tac (offset + (compileExprs args offset nextTmp).1.length) σ' am am ∧
      (∀ v, v.isTmp = false → v.isFTmp = false → v.isBTmp = false → σ' v = σ_tac v) ∧
      (∀ k, k < nextTmp → σ' (tmpName k) = σ_tac (tmpName k)) ∧
      (∀ k, k < nextTmp → σ' (ftmpName k) = σ_tac (ftmpName k)) ∧
      (∀ k, k < nextTmp → σ' (btmpName k) = σ_tac (btmpName k)) := by
  induction args generalizing offset nextTmp σ_tac with
  | nil =>
    simp only [compileExprs, List.length_nil, Nat.add_zero]
    exact ⟨σ_tac, FragExec.rfl' _ _ _ _, fun _ _ _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  | cons e rest ih =>
    simp only [compileExprs] at hcode ⊢
    generalize hre : compileExpr e offset nextTmp = re at hcode ⊢
    obtain ⟨codeE, ve, tmp1⟩ := re
    generalize hrrest : compileExprs rest (offset + codeE.length) tmp1 = rrest at hcode ⊢
    obtain ⟨codeRest, vsRest, tmp2⟩ := rrest
    simp only [] at hcode ⊢
    have htf_e : ∀ v ∈ e.freeVars, v.isTmp = false :=
      fun v hv => htf v (List.mem_flatMap.mpr ⟨e, .head rest, hv⟩)
    have hftf_e : ∀ v ∈ e.freeVars, v.isFTmp = false :=
      fun v hv => hftf v (List.mem_flatMap.mpr ⟨e, .head rest, hv⟩)
    have htbf_e : ∀ v ∈ e.freeVars, v.isBTmp = false :=
      fun v hv => htbf v (List.mem_flatMap.mpr ⟨e, .head rest, hv⟩)
    have htf_rest : ∀ v ∈ (rest.flatMap SExpr.freeVars), v.isTmp = false :=
      fun v hv => htf v (List.mem_flatMap.mpr
        (let ⟨e', he', hv'⟩ := List.mem_flatMap.mp hv; ⟨e', .tail e he', hv'⟩))
    have hftf_rest : ∀ v ∈ (rest.flatMap SExpr.freeVars), v.isFTmp = false :=
      fun v hv => hftf v (List.mem_flatMap.mpr
        (let ⟨e', he', hv'⟩ := List.mem_flatMap.mp hv; ⟨e', .tail e he', hv'⟩))
    have htbf_rest : ∀ v ∈ (rest.flatMap SExpr.freeVars), v.isBTmp = false :=
      fun v hv => htbf v (List.mem_flatMap.mpr
        (let ⟨e', he', hv'⟩ := List.mem_flatMap.mp hv; ⟨e', .tail e he', hv'⟩))
    have hcodeE : RC.CodeAt (compileExpr e offset nextTmp).1 p offset := by
      rw [hre]; exact hcode.left
    have hcodeRest : RC.CodeAt (compileExprs rest (offset + codeE.length) tmp1).1 p
        (offset + codeE.length) := by rw [hrrest]; exact hcode.right
    obtain ⟨σ_e, hexec_e, _, hntmp_e, hprev_e, hfprev_e, hbprev_e⟩ :=
      compileExpr_correct e offset nextTmp σ σ_tac am p htf_e hftf_e htbf_e
        (htypedv e (.head rest))
        (hsafe e (.head rest))
        hagree hcodeE
    rw [hre] at hexec_e; simp at hexec_e
    -- σ_e agrees with σ on source vars
    have hagree_e : ∀ v, v.isTmp = false → v.isFTmp = false → v.isBTmp = false → σ_e v = σ v := by
      intro v hv1 hv2 hv3; rw [hntmp_e v hv1 hv2 hv3]; exact hagree v hv1 hv2 hv3
    have htypedv_rest : ∀ e' ∈ rest, e'.typedVars σ am :=
      fun e' he' => htypedv e' (.tail e he')
    have hsafe_rest : ∀ e' ∈ rest, e'.safe σ am p.arrayDecls :=
      fun e' he' => hsafe e' (.tail e he')
    have hge : nextTmp ≤ tmp1 := by
      have := compileExpr_nextTmp_ge e offset nextTmp; rw [hre] at this; simpa using this
    obtain ⟨σ_rest, hexec_rest, hntmp_rest, hprev_rest, hfprev_rest, hbprev_rest⟩ :=
      ih (offset + codeE.length) tmp1 σ_e htf_rest hftf_rest htbf_rest htypedv_rest hsafe_rest
        hagree_e hcodeRest
    rw [hrrest] at hexec_rest; simp at hexec_rest
    refine ⟨σ_rest, ?_, ?_, ?_, ?_, ?_⟩
    · -- FragExec: chain e-block and rest-block
      have htrans := FragExec.trans' hexec_e hexec_rest
      show FragExec p offset σ_tac (offset + (codeE ++ codeRest).length) σ_rest am am
      rw [List.length_append, ← Nat.add_assoc]; exact htrans
    · -- Non-temp vars: chain hntmp_rest ∘ hntmp_e
      intro v hv1 hv2 hv3
      rw [hntmp_rest v hv1 hv2 hv3, hntmp_e v hv1 hv2 hv3]
    · -- tmpName k preserved for k < nextTmp
      intro k hk
      rw [hprev_rest k (by omega), hprev_e k hk]
    · -- ftmpName k preserved for k < nextTmp
      intro k hk
      rw [hfprev_rest k (by omega), hfprev_e k hk]
    · -- btmpName k preserved for k < nextTmp
      intro k hk
      rw [hbprev_rest k (by omega), hbprev_e k hk]

-- ============================================================
-- § 11. Statement compilation correctness
-- ============================================================

theorem compileStmt_correct (s : Stmt) (fuel : Nat) (σ σ' : Store) (am am' : ArrayMem)
    (offset nextTmp : Nat) (p : Prog) (σ_tac : Store)
    (hinterp : s.interp fuel σ am p.arrayDecls = some (σ', am'))
    (htmpfree : s.tmpFree)
    (hftmpfree : s.ftmpFree)
    (hbtmpfree : s.btmpFree)
    (hNoGoto : s.noGoto)
    (hsafe : s.safe fuel σ am p.arrayDecls)
    (htypedv : s.typedVars fuel σ am p.arrayDecls)
    (hagree : ∀ v, v.isTmp = false → v.isFTmp = false → v.isBTmp = false → σ_tac v = σ v)
    (labels : List (String × Nat) := [])
    (hcode : RC.CodeAt (compileStmt s offset nextTmp labels).1 p offset) :
    ∃ σ_tac', FragExec p offset σ_tac
        (offset + (compileStmt s offset nextTmp labels).1.length) σ_tac' am am' ∧
      (∀ v, v.isTmp = false → v.isFTmp = false → v.isBTmp = false → σ_tac' v = σ' v) := by
  induction s generalizing fuel σ σ' am am' offset nextTmp σ_tac with
  | skip =>
    simp only [Stmt.interp] at hinterp
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hinterp)
    simp only [compileStmt, List.length_nil, Nat.add_zero]
    exact ⟨σ_tac, FragExec.rfl' _ _ _ _, hagree⟩
  | label _ =>
    simp only [Stmt.interp] at hinterp
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hinterp)
    simp only [compileStmt, List.length_nil, Nat.add_zero]
    exact ⟨σ_tac, FragExec.rfl' _ _ _ _, hagree⟩
  | goto _ => exact absurd hNoGoto (by simp [Stmt.noGoto])
  | ifgoto b _ => exact absurd hNoGoto (by simp [Stmt.noGoto])
  | print fmt args =>
    simp only [Stmt.interp] at hinterp
    split at hinterp
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hinterp)
      simp only [Stmt.safe] at hsafe
      simp only [Stmt.typedVars] at htypedv
      dsimp only [compileStmt] at hcode ⊢
      generalize hrc : compileExprs args offset nextTmp = rc at hcode ⊢
      obtain ⟨allCode, allVars, tmp'⟩ := rc; simp only [] at hcode ⊢
      have hcodeExprs : RC.CodeAt (compileExprs args offset nextTmp).1 p offset := by
        rw [hrc]; exact hcode.left
      obtain ⟨σ_exprs, hexec_exprs, hntmp, _, _, _⟩ :=
        compileExprs_correct args offset nextTmp σ σ_tac am p htmpfree hftmpfree hbtmpfree htypedv hsafe hagree hcodeExprs
      rw [hrc] at hexec_exprs; simp only [] at hexec_exprs
      have hprint_instr : p[offset + allCode.length]? = some (.print fmt allVars) :=
        hcode.right.head
      have hexec_print := FragExec.single_print (am := am) hprint_instr (σ := σ_exprs)
      refine ⟨σ_exprs, ?_, fun v hv1 hv2 hv3 => by rw [hntmp v hv1 hv2 hv3]; exact hagree v hv1 hv2 hv3⟩
      have htrans := FragExec.trans' hexec_exprs hexec_print
      show FragExec p offset σ_tac (offset + (allCode ++ [TAC.print fmt allVars]).length) σ_exprs am am
      simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_zero]
      exact htrans
    · simp at hinterp
  | printInt e =>
    simp only [Stmt.interp] at hinterp
    split at hinterp
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hinterp)
      simp only [Stmt.safe] at hsafe
      simp only [Stmt.typedVars] at htypedv
      have htf_e : ∀ v ∈ e.freeVars, v.isTmp = false :=
        fun v hv => htmpfree v (by simp only [Stmt.allVars]; exact hv)
      have hftf_e : ∀ v ∈ e.freeVars, v.isFTmp = false :=
        fun v hv => hftmpfree v (by simp only [Stmt.allVars]; exact hv)
      have htbf_e : ∀ v ∈ e.freeVars, v.isBTmp = false :=
        fun v hv => hbtmpfree v (by simp only [Stmt.allVars]; exact hv)
      dsimp only [compileStmt] at hcode ⊢
      generalize hre : compileExpr e offset nextTmp = re at hcode ⊢
      obtain ⟨codeE, ve, tmp1⟩ := re; simp only [] at hcode ⊢
      have hcodeE : RC.CodeAt (compileExpr e offset nextTmp).1 p offset := by
        rw [hre]; exact hcode.left
      obtain ⟨σ_e, hexec_e, _, hntmp, _, _, _⟩ :=
        compileExpr_correct e offset nextTmp σ σ_tac am p htf_e hftf_e htbf_e htypedv hsafe hagree hcodeE
      rw [hre] at hexec_e; simp only [] at hexec_e
      have hpi_instr : p[offset + codeE.length]? = some (.printInt ve) := hcode.right.head
      have hexec_pi := FragExec.single_printInt (am := am) hpi_instr (σ := σ_e)
      refine ⟨σ_e, ?_, fun v hv1 hv2 hv3 => by rw [hntmp v hv1 hv2 hv3]; exact hagree v hv1 hv2 hv3⟩
      have htrans := FragExec.trans' hexec_e hexec_pi
      show FragExec p offset σ_tac (offset + (codeE ++ [TAC.printInt ve]).length) σ_e am am
      simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_zero]
      exact htrans
    · simp at hinterp
  | printFloat e =>
    simp only [Stmt.interp] at hinterp
    split at hinterp
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hinterp)
      simp only [Stmt.safe] at hsafe
      simp only [Stmt.typedVars] at htypedv
      have htf_e : ∀ v ∈ e.freeVars, v.isTmp = false :=
        fun v hv => htmpfree v (by simp only [Stmt.allVars]; exact hv)
      have hftf_e : ∀ v ∈ e.freeVars, v.isFTmp = false :=
        fun v hv => hftmpfree v (by simp only [Stmt.allVars]; exact hv)
      have htbf_e : ∀ v ∈ e.freeVars, v.isBTmp = false :=
        fun v hv => hbtmpfree v (by simp only [Stmt.allVars]; exact hv)
      dsimp only [compileStmt] at hcode ⊢
      generalize hre : compileExpr e offset nextTmp = re at hcode ⊢
      obtain ⟨codeE, ve, tmp1⟩ := re; simp only [] at hcode ⊢
      have hcodeE : RC.CodeAt (compileExpr e offset nextTmp).1 p offset := by
        rw [hre]; exact hcode.left
      obtain ⟨σ_e, hexec_e, _, hntmp, _, _, _⟩ :=
        compileExpr_correct e offset nextTmp σ σ_tac am p htf_e hftf_e htbf_e htypedv hsafe hagree hcodeE
      rw [hre] at hexec_e; simp only [] at hexec_e
      have hpf_instr : p[offset + codeE.length]? = some (.printFloat ve) := hcode.right.head
      have hexec_pf := FragExec.single_printFloat (am := am) hpf_instr (σ := σ_e)
      refine ⟨σ_e, ?_, fun v hv1 hv2 hv3 => by rw [hntmp v hv1 hv2 hv3]; exact hagree v hv1 hv2 hv3⟩
      have htrans := FragExec.trans' hexec_e hexec_pf
      show FragExec p offset σ_tac (offset + (codeE ++ [TAC.printFloat ve]).length) σ_e am am
      simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_zero]
      exact htrans
    · simp at hinterp
  | printString lit =>
    simp only [Stmt.interp] at hinterp
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hinterp)
    dsimp only [compileStmt] at hcode ⊢
    have hps_instr : p[offset]? = some (.printString lit) := hcode.head
    refine ⟨σ_tac, ?_, hagree⟩
    have hexec_ps := FragExec.single_printString (am := am) hps_instr (σ := σ_tac)
    show FragExec p offset σ_tac (offset + [TAC.printString lit].length) σ_tac am am
    simp only [List.length_cons, List.length_nil, Nat.add_zero]
    exact hexec_ps
  | printBool b =>
    simp only [Stmt.safe] at hsafe
    simp only [Stmt.typedVars] at htypedv
    have htf_b : ∀ v ∈ b.freeVars, v.isTmp = false :=
      fun v hv => htmpfree v (by simp only [Stmt.allVars]; exact hv)
    have hftf_b : ∀ v ∈ b.freeVars, v.isFTmp = false :=
      fun v hv => hftmpfree v (by simp only [Stmt.allVars]; exact hv)
    have htbf_b : ∀ v ∈ b.freeVars, v.isBTmp = false :=
      fun v hv => hbtmpfree v (by simp only [Stmt.allVars]; exact hv)
    simp only [Stmt.interp] at hinterp
    split at hinterp <;> [skip; simp at hinterp]
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hinterp)
    dsimp only [compileStmt] at hcode ⊢
    generalize hrcb : compileBool b offset nextTmp = rcb at hcode ⊢
    obtain ⟨codeB, be, tmpB⟩ := rcb
    simp only [] at hcode ⊢
    -- Execute compileBool b
    obtain ⟨σ_b, hexec_b, heval_b, hntmp_b, hprev_b, hfprev_b, hbprev_b⟩ :=
      compileBool_correct b offset nextTmp σ σ_tac am p htf_b hftf_b htbf_b
        htypedv hsafe hagree (by rw [hrcb]; exact hcode.left.left)
    rw [hrcb] at hexec_b heval_b; simp at hexec_b heval_b
    set tInt := tmpName tmpB with tInt_def
    -- Conv code at offset + codeB.length
    have hconv_adj : RC.CodeAt [TAC.ifgoto be (offset + codeB.length + 3),
        TAC.const tInt (.int 0),
        TAC.goto (offset + codeB.length + 3 + 1),
        TAC.const tInt (.int 1)] p (offset + codeB.length) := hcode.left.right
    have h_ifg : p[offset + codeB.length]? = some (.ifgoto be (offset + codeB.length + 3)) :=
      hconv_adj.head
    have h_const0 : p[offset + codeB.length + 1]? = some (.const tInt (.int 0)) := by
      have := hconv_adj 1 (by simp); simpa using this
    have h_goto_end : p[offset + codeB.length + 2]? = some (.goto (offset + codeB.length + 4)) := by
      have := hconv_adj 2 (by simp)
      simpa [show offset + codeB.length + 3 + 1 = offset + codeB.length + 4 from by omega] using this
    have h_const1 : p[offset + codeB.length + 3]? = some (.const tInt (.int 1)) := by
      have := hconv_adj 3 (by simp); simpa using this
    have h_printBool : p[offset + codeB.length + 4]? = some (.printBool tInt) := by
      have := hcode.right.head
      simp only [List.length_append, List.length_cons, List.length_nil] at this
      rwa [show offset + (codeB.length + 4) = offset + codeB.length + 4 from by omega] at this
    -- Case split on bool value
    cases hbval : b.eval σ am
    · -- false → ifgoto falls through, const 0, goto endL, printBool
      have hexec_ifg := FragExec.single_iffalse (am := am) h_ifg (by rw [heval_b, hbval])
      have hexec_c0 := FragExec.single_const (am := am) h_const0 (σ := σ_b)
      have hexec_goto := FragExec.single_goto (am := am) h_goto_end (σ := σ_b[tInt ↦ .int 0])
      have hexec_pb := FragExec.single_printBool (am := am) h_printBool (σ := σ_b[tInt ↦ .int 0])
      refine ⟨σ_b[tInt ↦ .int (0 : BitVec 64)], ?_, ?_⟩
      · have h := FragExec.trans' (FragExec.trans' (FragExec.trans' (FragExec.trans'
            hexec_b hexec_ifg) hexec_c0) hexec_goto) hexec_pb
        simp only [List.length_append, List.length_cons, List.length_nil] at h ⊢
        convert h using 1
      · intro v hv1 hv2 hv3
        rw [Store.update_isTmp_ne (tmpName_isTmp tmpB) hv1,
            hntmp_b v hv1 hv2 hv3]; exact hagree v hv1 hv2 hv3
    · -- true → ifgoto jumps to trueL, const 1, printBool
      have hexec_ifg := FragExec.single_iftrue (am := am) h_ifg (by rw [heval_b, hbval])
      have hexec_c1 := FragExec.single_const (am := am) h_const1 (σ := σ_b)
      have hexec_pb := FragExec.single_printBool (am := am) h_printBool (σ := σ_b[tInt ↦ .int 1])
      refine ⟨σ_b[tInt ↦ .int (1 : BitVec 64)], ?_, ?_⟩
      · have h := FragExec.trans' (FragExec.trans' (FragExec.trans'
            hexec_b hexec_ifg) hexec_c1) hexec_pb
        simp only [List.length_append, List.length_cons, List.length_nil] at h ⊢
        convert h using 1
      · intro v hv1 hv2 hv3
        rw [Store.update_isTmp_ne (tmpName_isTmp tmpB) hv1,
            hntmp_b v hv1 hv2 hv3]; exact hagree v hv1 hv2 hv3
  | assign x e =>
    simp only [Stmt.safe] at hsafe
    simp only [Stmt.typedVars] at htypedv
    obtain ⟨htv_e, hwrap_e⟩ := htypedv
    have htf_e : ∀ v ∈ e.freeVars, v.isTmp = false :=
      fun v hv => htmpfree v (by simp only [Stmt.allVars]; exact List.mem_cons_of_mem x hv)
    have hftf_e : ∀ v ∈ e.freeVars, v.isFTmp = false :=
      fun v hv => hftmpfree v (by simp only [Stmt.allVars]; exact List.mem_cons_of_mem x hv)
    have htbf_e : ∀ v ∈ e.freeVars, v.isBTmp = false :=
      fun v hv => hbtmpfree v (by simp only [Stmt.allVars]; exact List.mem_cons_of_mem x hv)
    have hisSafe := isSafe_of_safe_expr e σ am p.arrayDecls hsafe
    simp only [Stmt.interp, hisSafe] at hinterp; simp at hinterp
    obtain ⟨rfl, rfl⟩ := hinterp
    cases e with
    | lit n =>
      dsimp only [compileStmt] at hcode ⊢
      refine ⟨σ_tac[x ↦ .int (BitVec.ofInt 64 n)],
              FragExec.single_const (am := am) hcode.head, ?_⟩
      intro v hv1 hv2 hv3; by_cases hvx : v = x
      · subst hvx; rw [Store.update_self, Store.update_self]; simp [SExpr.eval]
      · rw [Store.update_other _ x v _ hvx, Store.update_other _ x v _ hvx]; exact hagree v hv1 hv2 hv3
    | var y =>
      dsimp only [compileStmt] at hcode ⊢
      simp only [SExpr.wrapEval] at hwrap_e
      refine ⟨σ_tac[x ↦ σ_tac y], FragExec.single_copy (am := am) hcode.head, ?_⟩
      intro v hv1 hv2 hv3; by_cases hvx : v = x
      · subst hvx; rw [Store.update_self, Store.update_self]
        rw [hagree y (htf_e y (by simp [SExpr.freeVars])) (hftf_e y (by simp [SExpr.freeVars]))
            (htbf_e y (by simp [SExpr.freeVars]))]
        exact hwrap_e
      · rw [Store.update_other _ x v _ hvx, Store.update_other _ x v _ hvx]; exact hagree v hv1 hv2 hv3
    | bin op a b =>
      obtain ⟨hwrap_a, hwrap_b, htv_a, htv_b⟩ :=
        show a.wrapEval σ am = .int (a.eval σ am) ∧ b.wrapEval σ am = .int (b.eval σ am) ∧
             a.typedVars σ am ∧ b.typedVars σ am from htv_e
      have htf_a := fun v hv => htf_e v (List.mem_append_left _ hv)
      have htf_b := fun v hv => htf_e v (List.mem_append_right _ hv)
      have hftf_a := fun v hv => hftf_e v (List.mem_append_left _ hv)
      have hftf_b := fun v hv => hftf_e v (List.mem_append_right _ hv)
      have htbf_a := fun v hv => htbf_e v (List.mem_append_left _ hv)
      have htbf_b := fun v hv => htbf_e v (List.mem_append_right _ hv)
      dsimp only [compileStmt] at hcode ⊢
      generalize hra : compileExpr a offset nextTmp = ra at hcode ⊢
      obtain ⟨codeA, va, tmp1⟩ := ra
      generalize hrb : compileExpr b (offset + codeA.length) tmp1 = rb at hcode ⊢
      obtain ⟨codeB, vb, tmp2⟩ := rb
      simp only [] at hcode ⊢
      obtain ⟨σ_a, hexec_a, hval_a, hntmp_a, hprev_a, hfprev_a, hbprev_a⟩ :=
        compileExpr_correct a offset nextTmp σ σ_tac am p htf_a hftf_a htbf_a htv_a
          (SExpr.safe_bin_left hsafe) hagree (by rw [hra]; exact hcode.left.left)
      rw [hra] at hexec_a hval_a; simp at hexec_a hval_a
      have hagree_a : ∀ v, v.isTmp = false → v.isFTmp = false → v.isBTmp = false → σ_a v = σ v := by
        intro v hv1 hv2 hv3; rw [hntmp_a v hv1 hv2 hv3]; exact hagree v hv1 hv2 hv3
      obtain ⟨σ_b, hexec_b, hval_b, hntmp_b, hprev_b, hfprev_b, hbprev_b⟩ :=
        compileExpr_correct b (offset + codeA.length) tmp1 σ σ_a am p htf_b hftf_b htbf_b htv_b
          (SExpr.safe_bin_right hsafe) hagree_a (by rw [hrb]; exact hcode.left.right)
      rw [hrb] at hexec_b hval_b; simp at hexec_b hval_b
      have hva_b : σ_b va = σ_a va := by
        rcases compileExpr_result_bound a offset nextTmp htf_a with h | ⟨k, _, hlt, heq⟩
        · rw [hra] at h; simp at h
          rcases compileExpr_result_ftmp_bound a offset nextTmp hftf_a with h2 | ⟨j, _, hlt2, heq2⟩
          · rw [hra] at h2; simp at h2
            have h3 : va.isBTmp = false := by
              have := compileExpr_result_isBTmp_false a offset nextTmp htbf_a
              rw [hra] at this; simpa using this
            exact hntmp_b va h h2 h3
          · rw [hra] at hlt2 heq2; simp at hlt2 heq2; rw [heq2, hfprev_b j (by omega)]
        · rw [hra] at hlt heq; simp at hlt heq; rw [heq, hprev_b k (by omega)]
      have hva : σ_b va = .int (a.eval σ am) := by rw [hva_b, hval_a, hwrap_a]
      have hvb : σ_b vb = .int (b.eval σ am) := by rw [hval_b, hwrap_b]
      have hbinop_instr : p[offset + codeA.length + codeB.length]? = some (.binop x op va vb) := by
        have := hcode.right.head; simp only [List.length_append] at this
        rwa [show offset + (codeA.length + codeB.length) =
            offset + codeA.length + codeB.length from by omega] at this
      have hexec_binop := FragExec.single_binop (am := am) hbinop_instr hva hvb (SExpr.safe_bin_safe hsafe)
      refine ⟨σ_b[x ↦ .int (op.eval (a.eval σ am) (b.eval σ am))], ?_, ?_⟩
      · have h123 := FragExec.trans' (FragExec.trans' hexec_a hexec_b) hexec_binop
        have hlen : offset + (codeA ++ codeB ++ [TAC.binop x op va vb]).length =
            offset + codeA.length + codeB.length + 1 := by
          simp only [List.length_append, List.length_cons, List.length_nil]; omega
        rw [hlen]; exact h123
      · intro v hv1 hv2 hv3; by_cases hvx : v = x
        · subst hvx; rw [Store.update_self, Store.update_self]; simp [SExpr.eval]
        · rw [Store.update_other _ x v _ hvx, Store.update_other _ x v _ hvx,
              hntmp_b v hv1 hv2 hv3, hntmp_a v hv1 hv2 hv3]; exact hagree v hv1 hv2 hv3
    | arrRead arr idx =>
      obtain ⟨hwrap_idx, htv_idx⟩ :=
        show idx.wrapEval σ am = .int (idx.eval σ am) ∧ idx.typedVars σ am from htv_e
      dsimp only [compileStmt] at hcode ⊢
      generalize hri : compileExpr idx offset nextTmp = ri at hcode ⊢
      obtain ⟨codeIdx, vIdx, tmp1⟩ := ri
      simp only [] at hcode ⊢
      obtain ⟨σ_idx, hexec_idx, hval_idx, hntmp_idx, _, _, _⟩ :=
        compileExpr_correct idx offset nextTmp σ σ_tac am p htf_e hftf_e htbf_e htv_idx
          (by simp [SExpr.safe] at hsafe; exact hsafe.1) hagree (by rw [hri]; exact hcode.left)
      rw [hri] at hexec_idx hval_idx; simp at hexec_idx hval_idx
      have hval_idx_int : σ_idx vIdx = .int (idx.eval σ am) := by rw [hval_idx, hwrap_idx]
      have hbounds : (idx.eval σ am) < p.arraySizeBv arr := by
        simp only [SExpr.safe] at hsafe; exact hsafe.2
      have harrLoad_instr : p[offset + codeIdx.length]? = some (.arrLoad (tmpName tmp1) arr vIdx .int) := by
        have := hcode.right.head; simpa using this
      have harrLoad := FragExec.single_arrLoad (am := am) harrLoad_instr hval_idx_int hbounds
      set σ_load := σ_idx[tmpName tmp1 ↦ .int (am.read arr (idx.eval σ am))] with hσ_load_def
      have hcopy_instr : p[offset + codeIdx.length + 1]? = some (.copy x (tmpName tmp1)) := by
        have h2 := hcode.right 1 (by simp)
        simpa using h2
      have hexec_copy := FragExec.single_copy (am := am) hcopy_instr (σ := σ_load)
      have hcopy_val : σ_load (tmpName tmp1) = .int (am.read arr (idx.eval σ am)) := by
        rw [hσ_load_def]; exact Store.update_self _ _ _
      refine ⟨σ_load[x ↦ σ_load (tmpName tmp1)], ?_, ?_⟩
      · have h123 := FragExec.trans' (FragExec.trans' hexec_idx harrLoad) hexec_copy
        have hlen : offset + (codeIdx ++ [TAC.arrLoad (tmpName tmp1) arr vIdx VarTy.int,
            TAC.copy x (tmpName tmp1)]).length =
            offset + codeIdx.length + 1 + 1 := by
          simp only [List.length_append, List.length_cons, List.length_nil]; omega
        rw [hlen]; exact h123
      · rw [hcopy_val]
        intro v hv1 hv2 hv3; by_cases hvx : v = x
        · subst hvx; rw [Store.update_self, Store.update_self]; simp [SExpr.eval]
        · rw [Store.update_other _ x v _ hvx]; rw [hσ_load_def]
          rw [Store.update_other _ (tmpName tmp1) v _
              (fun h => by rw [h] at hv1; simp [tmpName_isTmp] at hv1)]
          rw [Store.update_other _ x v _ hvx]; rw [hntmp_idx v hv1 hv2 hv3]; exact hagree v hv1 hv2 hv3
    | floatToInt e' =>
      dsimp only [compileStmt] at hcode ⊢
      generalize hre : compileExpr (.floatToInt e') offset nextTmp = re at hcode ⊢
      obtain ⟨codeE, ve, tmp1⟩ := re
      simp only [] at hcode ⊢
      obtain ⟨σ_e, hexec_e, hval_e, hntmp_e, _, _, _⟩ :=
        compileExpr_correct (.floatToInt e') offset nextTmp σ σ_tac am p htf_e hftf_e htbf_e htv_e
          hsafe hagree (by rw [hre]; exact hcode.left)
      rw [hre] at hexec_e hval_e; simp at hexec_e hval_e
      have hexec_copy := FragExec.single_copy (am := am) hcode.right.head (σ := σ_e)
      refine ⟨σ_e[x ↦ σ_e ve], ?_, ?_⟩
      · have h12 := FragExec.trans' hexec_e hexec_copy
        have hlen : offset + (codeE ++ [TAC.copy x ve]).length =
            offset + codeE.length + 1 := by
          simp only [List.length_append, List.length_cons, List.length_nil]; omega
        rw [hlen]; exact h12
      · intro v hv1 hv2 hv3; by_cases hvx : v = x
        · subst hvx; rw [Store.update_self, Store.update_self, hval_e, hwrap_e]
        · rw [Store.update_other _ x v _ hvx, Store.update_other _ x v _ hvx,
              hntmp_e v hv1 hv2 hv3]; exact hagree v hv1 hv2 hv3
    -- Contradictory cases for assign (wrapEval gives .int but these are float-typed)
    | flit _ => exact absurd hwrap_e (by simp [SExpr.wrapEval, SExpr.eval])
    | fbin _ _ _ => exact absurd hwrap_e (by simp [SExpr.wrapEval, SExpr.eval])
    | intToFloat _ => exact absurd hwrap_e (by simp [SExpr.wrapEval, SExpr.eval])
    | floatUnary _ _ => exact absurd hwrap_e (by simp [SExpr.wrapEval, SExpr.eval])
    | farrRead _ _ => exact absurd hwrap_e (by simp [SExpr.wrapEval, SExpr.eval])
  | bassign x b =>
    simp only [Stmt.safe] at hsafe
    simp only [Stmt.typedVars] at htypedv
    have hisSafe := isSafe_of_safe_bool b σ am p.arrayDecls hsafe
    simp only [Stmt.interp, hisSafe] at hinterp; simp at hinterp
    obtain ⟨rfl, rfl⟩ := hinterp
    have htf_b : ∀ v ∈ b.freeVars, v.isTmp = false :=
      fun v hv => htmpfree v (by simp only [Stmt.allVars]; exact List.mem_cons_of_mem x hv)
    have hftf_b : ∀ v ∈ b.freeVars, v.isFTmp = false :=
      fun v hv => hftmpfree v (by simp only [Stmt.allVars]; exact List.mem_cons_of_mem x hv)
    have htbf_b : ∀ v ∈ b.freeVars, v.isBTmp = false :=
      fun v hv => hbtmpfree v (by simp only [Stmt.allVars]; exact List.mem_cons_of_mem x hv)
    dsimp only [compileStmt] at hcode ⊢
    generalize hrc : compileBool b offset nextTmp = rc at hcode ⊢
    obtain ⟨code, be, tmp'⟩ := rc
    simp only [] at hcode ⊢
    obtain ⟨σ_bool, hexec_bool, heval_bool, hntmp_bool, _, _, _⟩ :=
      compileBool_correct b offset nextTmp σ σ_tac am p htf_b hftf_b htbf_b htypedv hsafe hagree
        (by rw [hrc]; exact hcode.left)
    rw [hrc] at hexec_bool heval_bool; simp at hexec_bool heval_bool
    have hexec_boolop : FragExec p (offset + code.length) σ_bool (offset + code.length + 1)
        (σ_bool[x ↦ .bool (b.eval σ am)]) am am := by
      have := Steps.single (Step.boolop (am := am) hcode.right.head (σ := σ_bool))
      rwa [heval_bool] at this
    refine ⟨σ_bool[x ↦ .bool (b.eval σ am)], ?_, ?_⟩
    · have h12 := FragExec.trans' hexec_bool hexec_boolop
      have hlen : offset + (code ++ [TAC.boolop x be]).length =
          offset + code.length + 1 := by
        simp only [List.length_append, List.length_cons, List.length_nil]; omega
      rw [hlen]; exact h12
    · intro v hv1 hv2 hv3; by_cases hvx : v = x
      · subst hvx; rw [Store.update_self, Store.update_self]
      · rw [Store.update_other _ x v _ hvx, Store.update_other _ x v _ hvx,
            hntmp_bool v hv1 hv2 hv3]; exact hagree v hv1 hv2 hv3
  | arrWrite arr idx val =>
    simp only [Stmt.safe] at hsafe
    obtain ⟨hsafe_idx, hsafe_val, hbounds⟩ := hsafe
    simp only [Stmt.typedVars] at htypedv
    obtain ⟨⟨htv_idx, hwrap_idx⟩, htv_val, hwrap_val⟩ := htypedv
    have htf_idx := fun v hv => htmpfree v (by simp only [Stmt.allVars]; exact List.mem_append_left _ hv)
    have htf_val := fun v hv => htmpfree v (by simp only [Stmt.allVars]; exact List.mem_append_right _ hv)
    have hftf_idx := fun v hv => hftmpfree v (by simp only [Stmt.allVars]; exact List.mem_append_left _ hv)
    have hftf_val := fun v hv => hftmpfree v (by simp only [Stmt.allVars]; exact List.mem_append_right _ hv)
    have htbf_idx := fun v hv => hbtmpfree v (by simp only [Stmt.allVars]; exact List.mem_append_left _ hv)
    have htbf_val := fun v hv => hbtmpfree v (by simp only [Stmt.allVars]; exact List.mem_append_right _ hv)
    simp only [Stmt.interp, isSafe_of_safe_expr idx σ am p.arrayDecls hsafe_idx,
               isSafe_of_safe_expr val σ am p.arrayDecls hsafe_val,
               decide_eq_true_eq.mpr hbounds, Bool.and_self, Bool.true_and] at hinterp
    simp at hinterp; obtain ⟨rfl, rfl⟩ := hinterp
    dsimp only [compileStmt] at hcode ⊢
    generalize hri : compileExpr idx offset nextTmp = ri at hcode ⊢
    obtain ⟨codeIdx, vIdx, tmp1⟩ := ri
    generalize hrv : compileExpr val (offset + codeIdx.length) tmp1 = rv at hcode ⊢
    obtain ⟨codeVal, vVal, tmp2⟩ := rv
    simp only [] at hcode ⊢
    obtain ⟨σ_idx, hexec_idx, hval_idx, hntmp_idx, hprev_idx, hfprev_idx, hbprev_idx⟩ :=
      compileExpr_correct idx offset nextTmp σ σ_tac am p htf_idx hftf_idx htbf_idx htv_idx
        hsafe_idx hagree (by rw [hri]; exact hcode.left.left)
    rw [hri] at hexec_idx hval_idx; simp at hexec_idx hval_idx
    have hagree_idx : ∀ v, v.isTmp = false → v.isFTmp = false → v.isBTmp = false → σ_idx v = σ v := by
      intro v hv1 hv2 hv3; rw [hntmp_idx v hv1 hv2 hv3]; exact hagree v hv1 hv2 hv3
    obtain ⟨σ_val, hexec_val, hval_val, hntmp_val, hprev_val, hfprev_val, hbprev_val⟩ :=
      compileExpr_correct val (offset + codeIdx.length) tmp1 σ σ_idx am p htf_val hftf_val htbf_val htv_val
        hsafe_val hagree_idx (by rw [hrv]; exact hcode.left.right)
    rw [hrv] at hexec_val hval_val; simp at hexec_val hval_val
    have hvIdx_val : σ_val vIdx = σ_idx vIdx := by
      rcases compileExpr_result_bound idx offset nextTmp htf_idx with h | ⟨k, _, hlt, heq⟩
      · rw [hri] at h; simp at h
        rcases compileExpr_result_ftmp_bound idx offset nextTmp hftf_idx with h2 | ⟨j, _, hlt2, heq2⟩
        · rw [hri] at h2; simp at h2
          have h3 : vIdx.isBTmp = false := by
            have := compileExpr_result_isBTmp_false idx offset nextTmp htbf_idx
            rw [hri] at this; simpa using this
          exact hntmp_val vIdx h h2 h3
        · rw [hri] at hlt2 heq2; simp at hlt2 heq2; rw [heq2, hfprev_val j (by omega)]
      · rw [hri] at hlt heq; simp at hlt heq; rw [heq, hprev_val k (by omega)]
    have hidx_int : σ_val vIdx = .int (idx.eval σ am) := by rw [hvIdx_val, hval_idx, hwrap_idx]
    have hval_int : σ_val vVal = .int (val.eval σ am) := by rw [hval_val, hwrap_val]
    have hstore_instr : p[offset + codeIdx.length + codeVal.length]? =
        some (.arrStore arr vIdx vVal .int) := by
      have := hcode.right.head; simp only [List.length_append] at this
      rwa [show offset + (codeIdx.length + codeVal.length) =
          offset + codeIdx.length + codeVal.length from by omega] at this
    have hexec_store := FragExec.single_arrStore (am := am) hstore_instr hidx_int hval_int hbounds
    refine ⟨σ_val, ?_, ?_⟩
    · have h123 := FragExec.trans' (FragExec.trans' hexec_idx hexec_val) hexec_store
      have hlen : offset + (codeIdx ++ codeVal ++ [TAC.arrStore arr vIdx vVal VarTy.int]).length =
          offset + codeIdx.length + codeVal.length + 1 := by
        simp only [List.length_append, List.length_cons, List.length_nil]; omega
      rw [hlen]; exact h123
    · intro v hv1 hv2 hv3; rw [hntmp_val v hv1 hv2 hv3, hntmp_idx v hv1 hv2 hv3]; exact hagree v hv1 hv2 hv3
  | barrWrite arr idx bval =>
    simp only [Stmt.safe] at hsafe
    obtain ⟨hsafe_idx, hsafe_bval, hbounds⟩ := hsafe
    simp only [Stmt.typedVars] at htypedv
    obtain ⟨⟨htv_idx, hwrap_idx⟩, htv_bval⟩ := htypedv
    have htf_idx := fun v hv => htmpfree v (by simp only [Stmt.allVars]; exact List.mem_append_left _ hv)
    have htf_bval := fun v hv => htmpfree v (by simp only [Stmt.allVars]; exact List.mem_append_right _ hv)
    have hftf_idx := fun v hv => hftmpfree v (by simp only [Stmt.allVars]; exact List.mem_append_left _ hv)
    have hftf_bval := fun v hv => hftmpfree v (by simp only [Stmt.allVars]; exact List.mem_append_right _ hv)
    have htbf_idx := fun v hv => hbtmpfree v (by simp only [Stmt.allVars]; exact List.mem_append_left _ hv)
    have htbf_bval := fun v hv => hbtmpfree v (by simp only [Stmt.allVars]; exact List.mem_append_right _ hv)
    simp only [Stmt.interp] at hinterp
    split at hinterp <;> [skip; simp at hinterp]
    simp at hinterp; obtain ⟨rfl, rfl⟩ := hinterp
    dsimp only [compileStmt] at hcode ⊢
    generalize hri : compileExpr idx offset nextTmp = ri at hcode ⊢
    obtain ⟨codeIdx, vIdx, tmp1⟩ := ri
    generalize hrcb : compileBool bval (offset + codeIdx.length) tmp1 = rcb at hcode ⊢
    obtain ⟨codeBool, be, tmp2⟩ := rcb
    simp only [] at hcode ⊢
    -- Execute idx
    obtain ⟨σ_idx, hexec_idx, hval_idx, hntmp_idx, hprev_idx, hfprev_idx, hbprev_idx⟩ :=
      compileExpr_correct idx offset nextTmp σ σ_tac am p htf_idx hftf_idx htbf_idx htv_idx
        hsafe_idx hagree (by rw [hri]; exact hcode.left.left)
    rw [hri] at hexec_idx hval_idx; simp at hexec_idx hval_idx
    have hagree_idx : ∀ v, v.isTmp = false → v.isFTmp = false → v.isBTmp = false → σ_idx v = σ v := by
      intro v hv1 hv2 hv3; rw [hntmp_idx v hv1 hv2 hv3]; exact hagree v hv1 hv2 hv3
    -- Execute bval
    obtain ⟨σ_bool, hexec_bool, heval_bool, hntmp_bool, hprev_bool, hfprev_bool, hbprev_bool⟩ :=
      compileBool_correct bval (offset + codeIdx.length) tmp1 σ σ_idx am p htf_bval hftf_bval htbf_bval
        htv_bval hsafe_bval hagree_idx (by rw [hrcb]; exact hcode.left.right)
    rw [hrcb] at hexec_bool heval_bool; simp at hexec_bool heval_bool
    -- vIdx preserved through bool execution
    have hvIdx_bool : σ_bool vIdx = σ_idx vIdx := by
      rcases compileExpr_result_bound idx offset nextTmp htf_idx with h | ⟨k, _, hlt, heq⟩
      · rw [hri] at h; simp at h
        rcases compileExpr_result_ftmp_bound idx offset nextTmp hftf_idx with h2 | ⟨j, _, hlt2, heq2⟩
        · rw [hri] at h2; simp at h2
          have h3 : vIdx.isBTmp = false := by
            have := compileExpr_result_isBTmp_false idx offset nextTmp htbf_idx
            rw [hri] at this; simpa using this
          exact hntmp_bool vIdx h h2 h3
        · rw [hri] at hlt2 heq2; simp at hlt2 heq2; rw [heq2]; exact hfprev_bool j (by omega)
      · rw [hri] at hlt heq; simp at hlt heq; rw [heq]; exact hprev_bool k (by omega)
    have hvIdx_int : σ_bool vIdx = .int (idx.eval σ am) := by rw [hvIdx_bool, hval_idx, hwrap_idx]
    -- New 2-instr lowering: boolop + arrStore .bool
    set tBool := btmpName tmp2 with tBool_def
    -- Code positions
    set afterCB := offset + codeIdx.length + codeBool.length with afterCB_def
    have h_boolop : p[afterCB]? = some (.boolop tBool be) := by
      have := hcode.right.head
      simp only [List.length_append] at this
      rwa [show offset + (codeIdx.length + codeBool.length) = afterCB from by omega] at this
    have h_arrStore : p[afterCB + 1]? = some (.arrStore arr vIdx tBool .bool) := by
      have h := hcode.right 1 (by simp)
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, List.length_append] at h
      rwa [show offset + (codeIdx.length + codeBool.length) + 1 = afterCB + 1 from by omega] at h
    -- Execute boolop tBool be → σ_op
    have hexec_boolop : FragExec p afterCB σ_bool (afterCB + 1)
        (σ_bool[tBool ↦ .bool (bval.eval σ am)]) am am := by
      have := FragExec.single_boolop (am := am) h_boolop (σ := σ_bool)
      rwa [heval_bool] at this
    set σ_op := σ_bool[tBool ↦ .bool (bval.eval σ am)]
    -- vIdx preserved through boolop update (vIdx is not the btmp tBool)
    have hvIdx_op : σ_op vIdx = .int (idx.eval σ am) := by
      simp only [σ_op]
      have hvIdx_not_btmp : vIdx.isBTmp = false := by
        have := compileExpr_result_isBTmp_false idx offset nextTmp htbf_idx
        rw [hri] at this; simpa using this
      rw [Store.update_isBTmp_ne (btmpName_isBTmp tmp2) hvIdx_not_btmp]
      exact hvIdx_int
    have htBool : σ_op tBool = .bool (bval.eval σ am) := by
      simp only [σ_op, tBool_def]; exact Store.update_self _ _ _
    -- Execute arrStore arr vIdx tBool .bool → updates am
    have hexec_store := FragExec.single_arrStore_bool (am := am) h_arrStore hvIdx_op htBool hbounds
    refine ⟨σ_op, ?_, ?_⟩
    · -- FragExec chain: idx → bool → boolop → arrStore
      have h := FragExec.trans' (FragExec.trans' (FragExec.trans' hexec_idx hexec_bool)
                  hexec_boolop) hexec_store
      have hlen : offset + (codeIdx ++ codeBool ++ [TAC.boolop tBool be,
          TAC.arrStore arr vIdx tBool .bool]).length = afterCB + 1 + 1 := by
        simp only [afterCB_def, List.length_append, List.length_cons, List.length_nil]; omega
      rw [hlen]; exact h
    · -- σ_op preserves source vars (not isTmp/isFTmp/isBTmp)
      intro v hv1 hv2 hv3
      simp only [σ_op]
      rw [Store.update_isBTmp_ne (btmpName_isBTmp tmp2) hv3,
          hntmp_bool v hv1 hv2 hv3, hntmp_idx v hv1 hv2 hv3]
      exact hagree v hv1 hv2 hv3
  | seq s1 s2 ih1 ih2 =>
    simp only [Stmt.interp, bind, Option.bind] at hinterp
    cases h1 : s1.interp fuel σ am p.arrayDecls with
    | none => simp [h1] at hinterp
    | some p1 =>
      obtain ⟨σ₁, am₁⟩ := p1; simp [h1] at hinterp
      simp only [Stmt.safe] at hsafe; obtain ⟨hsafe1, hsafe2⟩ := hsafe; rw [h1] at hsafe2
      simp only [Stmt.typedVars] at htypedv; obtain ⟨htv1, htv2⟩ := htypedv; rw [h1] at htv2
      have htf1 : s1.tmpFree := fun v hv => htmpfree v (List.mem_append_left _ hv)
      have htf2 : s2.tmpFree := fun v hv => htmpfree v (List.mem_append_right _ hv)
      have hftf1 : s1.ftmpFree := fun v hv => hftmpfree v (List.mem_append_left _ hv)
      have hftf2 : s2.ftmpFree := fun v hv => hftmpfree v (List.mem_append_right _ hv)
      have hbtf1 : s1.btmpFree := fun v hv => hbtmpfree v (List.mem_append_left _ hv)
      have hbtf2 : s2.btmpFree := fun v hv => hbtmpfree v (List.mem_append_right _ hv)
      have hng1 : s1.noGoto := (hNoGoto : s1.noGoto ∧ s2.noGoto).1
      have hng2 : s2.noGoto := (hNoGoto : s1.noGoto ∧ s2.noGoto).2
      dsimp only [compileStmt] at hcode ⊢
      generalize hrc1 : compileStmt s1 offset nextTmp labels = rc1 at hcode ⊢
      obtain ⟨code1, tmp1⟩ := rc1
      generalize hrc2 : compileStmt s2 (offset + code1.length) tmp1 labels = rc2 at hcode ⊢
      obtain ⟨code2, tmp2⟩ := rc2
      simp only [] at hcode ⊢
      obtain ⟨σ_1, hexec_1, hagree_1⟩ :=
        ih1 fuel σ σ₁ am am₁ offset nextTmp σ_tac h1 htf1 hftf1 hbtf1 hng1 hsafe1 htv1 hagree
          (by rw [hrc1]; exact hcode.left)
      rw [hrc1] at hexec_1; simp at hexec_1
      obtain ⟨σ_2, hexec_2, hagree_2⟩ :=
        ih2 fuel σ₁ σ' am₁ am' (offset + code1.length) tmp1 σ_1 hinterp htf2 hftf2 hbtf2 hng2 hsafe2 htv2
          hagree_1 (by rw [hrc2]; exact hcode.right)
      rw [hrc2] at hexec_2; simp at hexec_2
      refine ⟨σ_2, ?_, hagree_2⟩
      have h12 := FragExec.trans' hexec_1 hexec_2
      simp only [List.length_append] at h12 ⊢
      rwa [Nat.add_assoc] at h12
  | ite b s1 s2 ih1 ih2 =>
    simp only [Stmt.interp] at hinterp
    split at hinterp
    · rename_i hbs
      simp only [Stmt.safe] at hsafe; obtain ⟨hbsafe, hbranch_safe⟩ := hsafe
      simp only [Stmt.typedVars] at htypedv; obtain ⟨htv_b, htv_branch⟩ := htypedv
      have htf_b := fun v hv => htmpfree v (by simp only [Stmt.allVars]; exact List.mem_append_left _ (List.mem_append_left _ hv))
      have hftf_b := fun v hv => hftmpfree v (by simp only [Stmt.allVars]; exact List.mem_append_left _ (List.mem_append_left _ hv))
      have htbf_b := fun v hv => hbtmpfree v (by simp only [Stmt.allVars]; exact List.mem_append_left _ (List.mem_append_left _ hv))
      have htf1 : s1.tmpFree := fun v hv => htmpfree v (by simp only [Stmt.allVars]; exact List.mem_append_left _ (List.mem_append_right _ hv))
      have htf2 : s2.tmpFree := fun v hv => htmpfree v (by simp only [Stmt.allVars]; exact List.mem_append_right _ hv)
      have hftf1 : s1.ftmpFree := fun v hv => hftmpfree v (by simp only [Stmt.allVars]; exact List.mem_append_left _ (List.mem_append_right _ hv))
      have hftf2 : s2.ftmpFree := fun v hv => hftmpfree v (by simp only [Stmt.allVars]; exact List.mem_append_right _ hv)
      have hbtf1 : s1.btmpFree := fun v hv => hbtmpfree v (by simp only [Stmt.allVars]; exact List.mem_append_left _ (List.mem_append_right _ hv))
      have hbtf2 : s2.btmpFree := fun v hv => hbtmpfree v (by simp only [Stmt.allVars]; exact List.mem_append_right _ hv)
      have hng1 : s1.noGoto := (hNoGoto : s1.noGoto ∧ s2.noGoto).1
      have hng2 : s2.noGoto := (hNoGoto : s1.noGoto ∧ s2.noGoto).2
      dsimp only [compileStmt] at hcode ⊢
      generalize hrcb : compileBool b offset nextTmp = rcb at hcode ⊢
      obtain ⟨codeBool, be, tmpB⟩ := rcb
      generalize hrce : compileStmt s2 (offset + codeBool.length + 1) tmpB labels = rce at hcode ⊢
      obtain ⟨codeElse, tmpElse⟩ := rce
      generalize hrct : compileStmt s1 (offset + codeBool.length + 1 + codeElse.length + 1) tmpElse labels = rct at hcode ⊢
      obtain ⟨codeThen, tmpThen⟩ := rct
      simp only [] at hcode ⊢
      obtain ⟨σ_bool, hexec_bool, heval_bool, hntmp_bool, _, _, _⟩ :=
        compileBool_correct b offset nextTmp σ σ_tac am p htf_b hftf_b htbf_b htv_b
          hbsafe hagree
          (by rw [hrcb]; exact hcode.left.left.left.left)
      rw [hrcb] at hexec_bool heval_bool; simp at hexec_bool heval_bool
      have hagree_bool : ∀ v, v.isTmp = false → v.isFTmp = false → v.isBTmp = false → σ_bool v = σ v := by
        intro v hv1 hv2 hv3; rw [hntmp_bool v hv1 hv2 hv3]; exact hagree v hv1 hv2 hv3
      have hifgoto_instr : p[offset + codeBool.length]? = some (.ifgoto be (offset + codeBool.length + 1 + codeElse.length + 1)) := by
        have := hcode.left.left.left.right.head; simpa using this
      cases heval : b.eval σ am
      · -- false → else branch: fall through to codeElse, then goto endLabel
        simp [heval] at hinterp hbranch_safe htv_branch
        have hexec_if := FragExec.single_iffalse (am := am) hifgoto_instr (by rw [heval_bool, heval])
        have hcode_else : RC.CodeAt (compileStmt s2 (offset + codeBool.length + 1) tmpB labels).1 p
            (offset + codeBool.length + 1) := by
          rw [hrce]; have := hcode.left.left.right
          simp only [List.length_append, List.length_cons, List.length_nil] at this
          rwa [show offset + (codeBool.length + 1) = offset + codeBool.length + 1 from by omega] at this
        obtain ⟨σ_else, hexec_else, hagree_else⟩ :=
          ih2 fuel σ σ' am am' (offset + codeBool.length + 1) tmpB σ_bool hinterp htf2 hftf2 hbtf2 hng2
            hbranch_safe htv_branch hagree_bool hcode_else
        rw [hrce] at hexec_else; simp at hexec_else
        have hgoto_instr : p[offset + codeBool.length + 1 + codeElse.length]? =
            some (.goto (offset + codeBool.length + 1 + codeElse.length + 1 + codeThen.length)) := by
          have := hcode.left.right.head
          simp only [List.length_append, List.length_cons, List.length_nil] at this
          rwa [show offset + (codeBool.length + 1 + codeElse.length) =
              offset + codeBool.length + 1 + codeElse.length from by omega] at this
        have hexec_goto := FragExec.single_goto (am := am') hgoto_instr (σ := σ_else)
        refine ⟨σ_else, ?_, hagree_else⟩
        have h1234 := FragExec.trans' (FragExec.trans' (FragExec.trans' hexec_bool hexec_if) hexec_else) hexec_goto
        simp only [List.length_append, List.length_cons, List.length_nil] at h1234 ⊢
        convert h1234 using 1; omega
      · -- true → then branch: jump to codeThen
        simp [heval] at hinterp hbranch_safe htv_branch
        have hexec_if := FragExec.single_iftrue (am := am) hifgoto_instr (by rw [heval_bool, heval])
        have hcode_then : RC.CodeAt (compileStmt s1 (offset + codeBool.length + 1 + codeElse.length + 1) tmpElse labels).1 p
            (offset + codeBool.length + 1 + codeElse.length + 1) := by
          rw [hrct]; have := hcode.right
          simp only [List.length_append, List.length_cons, List.length_nil] at this
          rwa [show offset + (codeBool.length + 1 + codeElse.length + 1) =
              offset + codeBool.length + 1 + codeElse.length + 1 from by omega] at this
        obtain ⟨σ_then, hexec_then, hagree_then⟩ :=
          ih1 fuel σ σ' am am' (offset + codeBool.length + 1 + codeElse.length + 1) tmpElse σ_bool
            hinterp htf1 hftf1 hbtf1 hng1 hbranch_safe htv_branch hagree_bool hcode_then
        rw [hrct] at hexec_then; simp at hexec_then
        refine ⟨σ_then, ?_, hagree_then⟩
        have h123 := FragExec.trans' (FragExec.trans' hexec_bool hexec_if) hexec_then
        simp only [List.length_append, List.length_cons, List.length_nil] at h123 ⊢
        convert h123 using 1; omega
    · simp at hinterp
  | loop b body ihb =>
    induction fuel generalizing σ am σ' am' σ_tac with
    | zero => simp [Stmt.interp] at hinterp
    | succ fuel' ih_fuel =>
      rw [Stmt.interp.eq_9] at hinterp
      rw [Stmt.safe.eq_9] at hsafe
      rw [Stmt.typedVars.eq_9] at htypedv
      split at hinterp
      · rename_i hbs
        obtain ⟨hbsafe, hbranch⟩ := hsafe
        obtain ⟨htv_bsafe, htv_branch⟩ := htypedv
        have htf_b := fun v hv => htmpfree v (List.mem_append_left _ hv)
        have hftf_b := fun v hv => hftmpfree v (List.mem_append_left _ hv)
        have htbf_b := fun v hv => hbtmpfree v (List.mem_append_left _ hv)
        have htf_body : body.tmpFree := fun v hv => htmpfree v (List.mem_append_right _ hv)
        have hftf_body : body.ftmpFree := fun v hv => hftmpfree v (List.mem_append_right _ hv)
        have hbtf_body : body.btmpFree := fun v hv => hbtmpfree v (List.mem_append_right _ hv)
        have hng_body : body.noGoto := hNoGoto
        dsimp only [compileStmt] at hcode ⊢
        generalize hrcb : compileBool b offset nextTmp = rcb at hcode ⊢
        obtain ⟨codeBool, be, tmpB⟩ := rcb
        generalize hrcbody : compileStmt body (offset + codeBool.length + 1) tmpB labels = rcbody at hcode ⊢
        obtain ⟨codeBody, tmpBody⟩ := rcbody
        simp only [] at hcode ⊢
        have hcode_bool : RC.CodeAt (compileBool b offset nextTmp).1 p offset := by
          rw [hrcb]; exact hcode.left.left.left
        obtain ⟨σ_bool, hexec_bool, heval_bool, hntmp_bool, _, _, _⟩ :=
          compileBool_correct b offset nextTmp σ σ_tac am p htf_b hftf_b htbf_b htv_bsafe hbsafe hagree hcode_bool
        rw [hrcb] at hexec_bool heval_bool; simp at hexec_bool heval_bool
        have hagree_bool : ∀ v, v.isTmp = false → v.isFTmp = false → v.isBTmp = false → σ_bool v = σ v := by
          intro v hv1 hv2 hv3; rw [hntmp_bool v hv1 hv2 hv3]; exact hagree v hv1 hv2 hv3
        have hifgoto_instr : p[offset + codeBool.length]? =
            some (.ifgoto (.not be) (offset + codeBool.length + 1 + codeBody.length + 1)) := by
          have := hcode.left.left.right.head
          simp only [List.length_append, List.length_cons, List.length_nil] at this; exact this
        cases heval : b.eval σ am
        · -- false: loop exits
          simp [heval] at hinterp
          obtain ⟨rfl, rfl⟩ := hinterp
          have hexec_if := FragExec.single_iftrue (am := am) hifgoto_instr
            (by simp only [BoolExpr.eval]; rw [heval_bool, heval]; decide)
          refine ⟨σ_bool, ?_, hagree_bool⟩
          have h12 := FragExec.trans' hexec_bool hexec_if
          simp only [List.length_append, List.length_cons, List.length_nil] at h12 ⊢
          convert h12 using 1; omega
        · -- true: execute body then recurse
          simp [heval] at hinterp hbranch htv_branch
          cases h_body : body.interp fuel' σ am p.arrayDecls with
          | none => simp [h_body] at hinterp
          | some p1 =>
            obtain ⟨σ₁, am₁⟩ := p1; simp [h_body] at hinterp hbranch htv_branch
            obtain ⟨hds_body, hsafe_rest⟩ := hbranch
            obtain ⟨htv_body, htv_rest⟩ := htv_branch
            have hexec_if := FragExec.single_iffalse (am := am) hifgoto_instr
              (by simp only [BoolExpr.eval]; rw [heval_bool, heval]; decide)
            have hcode_body : RC.CodeAt (compileStmt body (offset + codeBool.length + 1) tmpB labels).1 p
                (offset + codeBool.length + 1) := by
              rw [hrcbody]; have := hcode.left.right
              simp only [List.length_append, List.length_cons, List.length_nil] at this
              rwa [show offset + (codeBool.length + 1) = offset + codeBool.length + 1 from by omega] at this
            obtain ⟨σ_body, hexec_body, hagree_body⟩ :=
              ihb fuel' σ σ₁ am am₁ (offset + codeBool.length + 1) tmpB σ_bool h_body htf_body hftf_body hbtf_body hng_body
                hds_body htv_body hagree_bool hcode_body
            rw [hrcbody] at hexec_body; simp at hexec_body
            have hgoto_instr : p[offset + codeBool.length + 1 + codeBody.length]? = some (.goto offset) := by
              have := hcode.right.head
              simp only [List.length_append, List.length_cons, List.length_nil] at this
              rwa [show offset + (codeBool.length + 1 + codeBody.length) =
                  offset + codeBool.length + 1 + codeBody.length from by omega] at this
            have hexec_goto := FragExec.single_goto (am := am₁) hgoto_instr (σ := σ_body)
            -- Compose: bool + ifgoto + body + goto → back to offset
            have hexec_iter := FragExec.trans' (FragExec.trans' (FragExec.trans' hexec_bool hexec_if) hexec_body) hexec_goto
            -- Recurse on remaining loop iterations
            obtain ⟨σ_final, hexec_rest, hagree_final⟩ :=
              ih_fuel σ₁ σ' am₁ am' σ_body hinterp hsafe_rest htv_rest hagree_body
            refine ⟨σ_final, ?_, hagree_final⟩
            have h_total := FragExec.trans' hexec_iter hexec_rest
            simp only [List.length_append, List.length_cons, List.length_nil] at h_total ⊢
            convert h_total using 2
            simp only [compileStmt, hrcb, hrcbody, List.length_append, List.length_cons, List.length_nil]
      · simp at hinterp
  | fassign x e =>
    simp only [Stmt.safe] at hsafe
    simp only [Stmt.typedVars] at htypedv
    obtain ⟨htv_e, hwrap_e⟩ := htypedv
    have htf_e : ∀ v ∈ e.freeVars, v.isTmp = false :=
      fun v hv => htmpfree v (by simp only [Stmt.allVars]; exact List.mem_cons_of_mem x hv)
    have hftf_e : ∀ v ∈ e.freeVars, v.isFTmp = false :=
      fun v hv => hftmpfree v (by simp only [Stmt.allVars]; exact List.mem_cons_of_mem x hv)
    have htbf_e : ∀ v ∈ e.freeVars, v.isBTmp = false :=
      fun v hv => hbtmpfree v (by simp only [Stmt.allVars]; exact List.mem_cons_of_mem x hv)
    have hisSafe := isSafe_of_safe_expr e σ am p.arrayDecls hsafe
    simp only [Stmt.interp, hisSafe] at hinterp; simp at hinterp
    obtain ⟨rfl, rfl⟩ := hinterp
    cases e with
    | flit f =>
      dsimp only [compileStmt] at hcode ⊢
      refine ⟨σ_tac[x ↦ .float (floatToBits f)],
              FragExec.single_const (am := am) hcode.head, ?_⟩
      intro v hv1 hv2 hv3; by_cases hvx : v = x
      · subst hvx; rw [Store.update_self, Store.update_self]; simp [SExpr.eval]
      · rw [Store.update_other _ x v _ hvx, Store.update_other _ x v _ hvx]; exact hagree v hv1 hv2 hv3
    | var y =>
      dsimp only [compileStmt] at hcode ⊢
      simp only [SExpr.wrapEval] at hwrap_e
      refine ⟨σ_tac[x ↦ σ_tac y], FragExec.single_copy (am := am) hcode.head, ?_⟩
      intro v hv1 hv2 hv3; by_cases hvx : v = x
      · subst hvx; rw [Store.update_self, Store.update_self]
        rw [hagree y (htf_e y (by simp [SExpr.freeVars])) (hftf_e y (by simp [SExpr.freeVars]))
            (htbf_e y (by simp [SExpr.freeVars]))]
        exact hwrap_e
      · rw [Store.update_other _ x v _ hvx, Store.update_other _ x v _ hvx]; exact hagree v hv1 hv2 hv3
    | fbin fop a b =>
      obtain ⟨hwrap_a, hwrap_b, htv_a, htv_b⟩ :=
        show a.wrapEval σ am = .float (a.eval σ am) ∧ b.wrapEval σ am = .float (b.eval σ am) ∧
             a.typedVars σ am ∧ b.typedVars σ am from htv_e
      have htf_a := fun v hv => htf_e v (List.mem_append_left _ hv)
      have htf_b := fun v hv => htf_e v (List.mem_append_right _ hv)
      have hftf_a := fun v hv => hftf_e v (List.mem_append_left _ hv)
      have hftf_b := fun v hv => hftf_e v (List.mem_append_right _ hv)
      have htbf_a := fun v hv => htbf_e v (List.mem_append_left _ hv)
      have htbf_b := fun v hv => htbf_e v (List.mem_append_right _ hv)
      dsimp only [compileStmt] at hcode ⊢
      generalize hra : compileExpr a offset nextTmp = ra at hcode ⊢
      obtain ⟨codeA, va, tmp1⟩ := ra
      generalize hrb : compileExpr b (offset + codeA.length) tmp1 = rb at hcode ⊢
      obtain ⟨codeB, vb, tmp2⟩ := rb
      simp only [] at hcode ⊢
      obtain ⟨σ_a, hexec_a, hval_a, hntmp_a, hprev_a, hfprev_a, hbprev_a⟩ :=
        compileExpr_correct a offset nextTmp σ σ_tac am p htf_a hftf_a htbf_a htv_a
          (SExpr.safe_fbin_left hsafe) hagree (by rw [hra]; exact hcode.left.left)
      rw [hra] at hexec_a hval_a; simp at hexec_a hval_a
      have hagree_a : ∀ v, v.isTmp = false → v.isFTmp = false → v.isBTmp = false → σ_a v = σ v := by
        intro v hv1 hv2 hv3; rw [hntmp_a v hv1 hv2 hv3]; exact hagree v hv1 hv2 hv3
      obtain ⟨σ_b, hexec_b, hval_b, hntmp_b, hprev_b, hfprev_b, hbprev_b⟩ :=
        compileExpr_correct b (offset + codeA.length) tmp1 σ σ_a am p htf_b hftf_b htbf_b htv_b
          (SExpr.safe_fbin_right hsafe) hagree_a (by rw [hrb]; exact hcode.left.right)
      rw [hrb] at hexec_b hval_b; simp at hexec_b hval_b
      have hva_b : σ_b va = σ_a va := by
        rcases compileExpr_result_bound a offset nextTmp htf_a with h | ⟨k, _, hlt, heq⟩
        · rw [hra] at h; simp at h
          rcases compileExpr_result_ftmp_bound a offset nextTmp hftf_a with h2 | ⟨j, _, hlt2, heq2⟩
          · rw [hra] at h2; simp at h2
            have h3 : va.isBTmp = false := by
              have := compileExpr_result_isBTmp_false a offset nextTmp htbf_a
              rw [hra] at this; simpa using this
            exact hntmp_b va h h2 h3
          · rw [hra] at hlt2 heq2; simp at hlt2 heq2; rw [heq2, hfprev_b j (by omega)]
        · rw [hra] at hlt heq; simp at hlt heq; rw [heq, hprev_b k (by omega)]
      have hva : σ_b va = .float (a.eval σ am) := by rw [hva_b, hval_a, hwrap_a]
      have hvb : σ_b vb = .float (b.eval σ am) := by rw [hval_b, hwrap_b]
      have hfbinop_instr : p[offset + codeA.length + codeB.length]? = some (.fbinop x fop va vb) := by
        have := hcode.right.head; simp only [List.length_append] at this
        rwa [show offset + (codeA.length + codeB.length) =
            offset + codeA.length + codeB.length from by omega] at this
      have hexec_fbinop := FragExec.single_fbinop (am := am) hfbinop_instr hva hvb
      refine ⟨σ_b[x ↦ .float (fop.eval (a.eval σ am) (b.eval σ am))], ?_, ?_⟩
      · have h123 := FragExec.trans' (FragExec.trans' hexec_a hexec_b) hexec_fbinop
        have hlen : offset + (codeA ++ codeB ++ [TAC.fbinop x fop va vb]).length =
            offset + codeA.length + codeB.length + 1 := by
          simp only [List.length_append, List.length_cons, List.length_nil]; omega
        rw [hlen]; exact h123
      · intro v hv1 hv2 hv3; by_cases hvx : v = x
        · subst hvx; rw [Store.update_self, Store.update_self]; simp [SExpr.eval]
        · rw [Store.update_other _ x v _ hvx, Store.update_other _ x v _ hvx,
              hntmp_b v hv1 hv2 hv3, hntmp_a v hv1 hv2 hv3]; exact hagree v hv1 hv2 hv3
    | intToFloat e' =>
      obtain ⟨hwrap_inner, htv_inner⟩ :=
        show e'.wrapEval σ am = .int (e'.eval σ am) ∧ e'.typedVars σ am from htv_e
      dsimp only [compileStmt] at hcode ⊢
      generalize hre : compileExpr e' offset nextTmp = re at hcode ⊢
      obtain ⟨codeE, ve, tmp1⟩ := re
      simp only [] at hcode ⊢
      obtain ⟨σ_e, hexec_e, hval_e, hntmp_e, _, _, _⟩ :=
        compileExpr_correct e' offset nextTmp σ σ_tac am p htf_e hftf_e htbf_e htv_inner
          (by simp [SExpr.safe] at hsafe; exact hsafe) hagree (by rw [hre]; exact hcode.left)
      rw [hre] at hexec_e hval_e; simp at hexec_e hval_e
      have hval_int : σ_e ve = .int (e'.eval σ am) := by rw [hval_e, hwrap_inner]
      have hexec_op := FragExec.single_intToFloat (am := am) hcode.right.head hval_int
      refine ⟨σ_e[x ↦ .float (intToFloatBv (e'.eval σ am))], ?_, ?_⟩
      · have h12 := FragExec.trans' hexec_e hexec_op
        have hlen : offset + (codeE ++ [TAC.intToFloat x ve]).length =
            offset + codeE.length + 1 := by
          simp only [List.length_append, List.length_cons, List.length_nil]; omega
        rw [hlen]; exact h12
      · intro v hv1 hv2 hv3; by_cases hvx : v = x
        · subst hvx; rw [Store.update_self, Store.update_self]; simp [SExpr.eval]
        · rw [Store.update_other _ x v _ hvx, Store.update_other _ x v _ hvx,
              hntmp_e v hv1 hv2 hv3]; exact hagree v hv1 hv2 hv3
    | floatUnary op' e' =>
      obtain ⟨hwrap_inner, htv_inner⟩ :=
        show e'.wrapEval σ am = .float (e'.eval σ am) ∧ e'.typedVars σ am from htv_e
      dsimp only [compileStmt] at hcode ⊢
      generalize hre : compileExpr e' offset nextTmp = re at hcode ⊢
      obtain ⟨codeE, ve, tmp1⟩ := re
      simp only [] at hcode ⊢
      obtain ⟨σ_e, hexec_e, hval_e, hntmp_e, _, _, _⟩ :=
        compileExpr_correct e' offset nextTmp σ σ_tac am p htf_e hftf_e htbf_e htv_inner
          (by simp [SExpr.safe] at hsafe; exact hsafe) hagree (by rw [hre]; exact hcode.left)
      rw [hre] at hexec_e hval_e; simp at hexec_e hval_e
      have hval_float : σ_e ve = .float (e'.eval σ am) := by rw [hval_e, hwrap_inner]
      have hexec_op := FragExec.single_floatUnary (am := am) hcode.right.head hval_float
      refine ⟨σ_e[x ↦ .float (op'.eval (e'.eval σ am))], ?_, ?_⟩
      · have h12 := FragExec.trans' hexec_e hexec_op
        have hlen : offset + (codeE ++ [TAC.floatUnary x op' ve]).length =
            offset + codeE.length + 1 := by
          simp only [List.length_append, List.length_cons, List.length_nil]; omega
        rw [hlen]; exact h12
      · intro v hv1 hv2 hv3; by_cases hvx : v = x
        · subst hvx; rw [Store.update_self, Store.update_self]; simp [SExpr.eval]
        · rw [Store.update_other _ x v _ hvx, Store.update_other _ x v _ hvx,
              hntmp_e v hv1 hv2 hv3]; exact hagree v hv1 hv2 hv3
    | farrRead arr' idx =>
      obtain ⟨hwrap_idx, htv_idx⟩ :=
        show idx.wrapEval σ am = .int (idx.eval σ am) ∧ idx.typedVars σ am from htv_e
      dsimp only [compileStmt] at hcode ⊢
      generalize hri : compileExpr idx offset nextTmp = ri at hcode ⊢
      obtain ⟨codeIdx, vIdx, tmp1⟩ := ri
      simp only [] at hcode ⊢
      obtain ⟨σ_idx, hexec_idx, hval_idx, hntmp_idx, _, _, _⟩ :=
        compileExpr_correct idx offset nextTmp σ σ_tac am p htf_e hftf_e htbf_e htv_idx
          (by simp [SExpr.safe] at hsafe; exact hsafe.1) hagree (by rw [hri]; exact hcode.left)
      rw [hri] at hexec_idx hval_idx; simp at hexec_idx hval_idx
      have hval_idx_int : σ_idx vIdx = .int (idx.eval σ am) := by rw [hval_idx, hwrap_idx]
      have hbounds : (idx.eval σ am) < p.arraySizeBv arr' := by
        simp only [SExpr.safe] at hsafe; exact hsafe.2
      have harrLoad_instr : p[offset + codeIdx.length]? = some (.arrLoad (ftmpName tmp1) arr' vIdx .float) := by
        have := hcode.right.head; simpa using this
      have harrLoad := FragExec.single_arrLoad_float (am := am) harrLoad_instr hval_idx_int hbounds
      set σ_load := σ_idx[ftmpName tmp1 ↦ .float (am.read arr' (idx.eval σ am))] with hσ_load_def
      have hcopy_instr : p[offset + codeIdx.length + 1]? = some (.copy x (ftmpName tmp1)) := by
        have h2 := hcode.right 1 (by simp)
        simpa using h2
      have hexec_copy := FragExec.single_copy (am := am) hcopy_instr (σ := σ_load)
      have hcopy_val : σ_load (ftmpName tmp1) = .float (am.read arr' (idx.eval σ am)) := by
        rw [hσ_load_def]; exact Store.update_self _ _ _
      refine ⟨σ_load[x ↦ σ_load (ftmpName tmp1)], ?_, ?_⟩
      · have h123 := FragExec.trans' (FragExec.trans' hexec_idx harrLoad) hexec_copy
        have hlen : offset + (codeIdx ++ [TAC.arrLoad (ftmpName tmp1) arr' vIdx VarTy.float,
            TAC.copy x (ftmpName tmp1)]).length =
            offset + codeIdx.length + 1 + 1 := by
          simp only [List.length_append, List.length_cons, List.length_nil]; omega
        rw [hlen]; exact h123
      · rw [hcopy_val]
        intro v hv1 hv2 hv3; by_cases hvx : v = x
        · subst hvx; rw [Store.update_self, Store.update_self]; simp [SExpr.eval]
        · rw [Store.update_other _ x v _ hvx]; rw [hσ_load_def]
          rw [Store.update_other _ (ftmpName tmp1) v _
              (fun h => by rw [h] at hv2; simp [ftmpName_isFTmp] at hv2)]
          rw [Store.update_other _ x v _ hvx]; rw [hntmp_idx v hv1 hv2 hv3]; exact hagree v hv1 hv2 hv3
    -- Contradictory cases for fassign (wrapEval gives .float but these are int-typed)
    | lit _ => exact absurd hwrap_e (by simp [SExpr.wrapEval, SExpr.eval])
    | bin _ _ _ => exact absurd hwrap_e (by simp [SExpr.wrapEval, SExpr.eval])
    | arrRead _ _ => exact absurd hwrap_e (by simp [SExpr.wrapEval, SExpr.eval])
    | floatToInt _ => exact absurd hwrap_e (by simp [SExpr.wrapEval, SExpr.eval])
  | farrWrite arr idx val =>
    simp only [Stmt.safe] at hsafe
    obtain ⟨hsafe_idx, hsafe_val, hbounds⟩ := hsafe
    simp only [Stmt.typedVars] at htypedv
    obtain ⟨⟨htv_idx, hwrap_idx⟩, htv_val, hwrap_val⟩ := htypedv
    have htf_idx := fun v hv => htmpfree v (by simp only [Stmt.allVars]; exact List.mem_append_left _ hv)
    have htf_val := fun v hv => htmpfree v (by simp only [Stmt.allVars]; exact List.mem_append_right _ hv)
    have hftf_idx := fun v hv => hftmpfree v (by simp only [Stmt.allVars]; exact List.mem_append_left _ hv)
    have hftf_val := fun v hv => hftmpfree v (by simp only [Stmt.allVars]; exact List.mem_append_right _ hv)
    have htbf_idx := fun v hv => hbtmpfree v (by simp only [Stmt.allVars]; exact List.mem_append_left _ hv)
    have htbf_val := fun v hv => hbtmpfree v (by simp only [Stmt.allVars]; exact List.mem_append_right _ hv)
    simp only [Stmt.interp, isSafe_of_safe_expr idx σ am p.arrayDecls hsafe_idx,
               isSafe_of_safe_expr val σ am p.arrayDecls hsafe_val,
               decide_eq_true_eq.mpr hbounds, Bool.and_self, Bool.true_and] at hinterp
    simp at hinterp; obtain ⟨rfl, rfl⟩ := hinterp
    dsimp only [compileStmt] at hcode ⊢
    generalize hri : compileExpr idx offset nextTmp = ri at hcode ⊢
    obtain ⟨codeIdx, vIdx, tmp1⟩ := ri
    generalize hrv : compileExpr val (offset + codeIdx.length) tmp1 = rv at hcode ⊢
    obtain ⟨codeVal, vVal, tmp2⟩ := rv
    simp only [] at hcode ⊢
    obtain ⟨σ_idx, hexec_idx, hval_idx, hntmp_idx, hprev_idx, hfprev_idx, hbprev_idx⟩ :=
      compileExpr_correct idx offset nextTmp σ σ_tac am p htf_idx hftf_idx htbf_idx htv_idx
        hsafe_idx hagree (by rw [hri]; exact hcode.left.left)
    rw [hri] at hexec_idx hval_idx; simp at hexec_idx hval_idx
    have hagree_idx : ∀ v, v.isTmp = false → v.isFTmp = false → v.isBTmp = false → σ_idx v = σ v := by
      intro v hv1 hv2 hv3; rw [hntmp_idx v hv1 hv2 hv3]; exact hagree v hv1 hv2 hv3
    obtain ⟨σ_val, hexec_val, hval_val, hntmp_val, hprev_val, hfprev_val, hbprev_val⟩ :=
      compileExpr_correct val (offset + codeIdx.length) tmp1 σ σ_idx am p htf_val hftf_val htbf_val htv_val
        hsafe_val hagree_idx (by rw [hrv]; exact hcode.left.right)
    rw [hrv] at hexec_val hval_val; simp at hexec_val hval_val
    have hvIdx_val : σ_val vIdx = σ_idx vIdx := by
      rcases compileExpr_result_bound idx offset nextTmp htf_idx with h | ⟨k, _, hlt, heq⟩
      · rw [hri] at h; simp at h
        rcases compileExpr_result_ftmp_bound idx offset nextTmp hftf_idx with h2 | ⟨j, _, hlt2, heq2⟩
        · rw [hri] at h2; simp at h2
          have h3 : vIdx.isBTmp = false := by
            have := compileExpr_result_isBTmp_false idx offset nextTmp htbf_idx
            rw [hri] at this; simpa using this
          exact hntmp_val vIdx h h2 h3
        · rw [hri] at hlt2 heq2; simp at hlt2 heq2; rw [heq2, hfprev_val j (by omega)]
      · rw [hri] at hlt heq; simp at hlt heq; rw [heq, hprev_val k (by omega)]
    have hidx_int : σ_val vIdx = .int (idx.eval σ am) := by rw [hvIdx_val, hval_idx, hwrap_idx]
    have hval_float : σ_val vVal = .float (val.eval σ am) := by rw [hval_val, hwrap_val]
    have hstore_instr : p[offset + codeIdx.length + codeVal.length]? =
        some (.arrStore arr vIdx vVal .float) := by
      have := hcode.right.head; simp only [List.length_append] at this
      rwa [show offset + (codeIdx.length + codeVal.length) =
          offset + codeIdx.length + codeVal.length from by omega] at this
    have hexec_store := FragExec.single_arrStore_float (am := am) hstore_instr hidx_int hval_float hbounds
    refine ⟨σ_val, ?_, ?_⟩
    · have h123 := FragExec.trans' (FragExec.trans' hexec_idx hexec_val) hexec_store
      have hlen : offset + (codeIdx ++ codeVal ++ [TAC.arrStore arr vIdx vVal VarTy.float]).length =
          offset + codeIdx.length + codeVal.length + 1 := by
        simp only [List.length_append, List.length_cons, List.length_nil]; omega
      rw [hlen]; exact h123
    · intro v hv1 hv2 hv3; rw [hntmp_val v hv1 hv2 hv3, hntmp_idx v hv1 hv2 hv3]; exact hagree v hv1 hv2 hv3

-- ============================================================
-- § 12. Top-level correctness theorem
-- ============================================================

theorem compileStmtToProg_correct (s : Stmt) (fuel : Nat) (σ σ' : Store)
    (hinterp : s.interp fuel σ ArrayMem.init (compileStmtToProg s).arrayDecls = some (σ', ArrayMem.init))
    (htmpfree : s.tmpFree)
    (hftmpfree : s.ftmpFree)
    (hbtmpfree : s.btmpFree)
    (hNoGoto : s.noGoto)
    (hsafe : s.safe fuel σ ArrayMem.init (compileStmtToProg s).arrayDecls)
    (htypedv : s.typedVars fuel σ ArrayMem.init (compileStmtToProg s).arrayDecls) :
    ∃ σ_tac am_h am_h', haltsWithResult (compileStmtToProg s) 0 σ σ_tac am_h am_h' ∧
      (∀ v, v.isTmp = false → v.isFTmp = false → v.isBTmp = false → σ_tac v = σ' v) := by
  have hcode : RC.CodeAt (compileStmt s 0 0).1 (compileStmtToProg s) 0 := by
    intro i hi; unfold compileStmtToProg; simp only [Prog.ofCode, Prog.getElem?_code, List.getElem?_toArray, Nat.zero_add]
    exact List.getElem?_append_left hi
  obtain ⟨σ_tac, hexec, hagree⟩ :=
    compileStmt_correct s fuel σ σ' ArrayMem.init ArrayMem.init 0 0 (compileStmtToProg s) σ
      hinterp htmpfree hftmpfree hbtmpfree hNoGoto hsafe htypedv (fun _ _ _ _ => rfl) (labels := []) hcode
  simp only [Nat.zero_add] at hexec
  have hhalt : (compileStmtToProg s)[(compileStmt s 0 0).1.length]? = some .halt := by
    unfold compileStmtToProg; simp only [Prog.ofCode, Prog.getElem?_code, List.getElem?_toArray]
    rw [List.getElem?_append_right (by omega)]; simp
  exact ⟨σ_tac, ArrayMem.init, ArrayMem.init, FragExec.toHalt hexec hhalt, hagree⟩

-- ============================================================
-- § 13. Determinism and stuck-state infrastructure
-- ============================================================

/-- Any two multi-step executions from the same config have one as a prefix
    of the other (i.e. they follow the same deterministic path). -/
theorem Steps.deterministic_reach {p : Prog} {c c₁ c₂ : Cfg}
    (h₁ : p ⊩ c ⟶* c₁) (h₂ : p ⊩ c ⟶* c₂) :
    (p ⊩ c₁ ⟶* c₂) ∨ (p ⊩ c₂ ⟶* c₁) := by
  induction h₁ generalizing c₂ with
  | refl => exact Or.inl h₂
  | step s rest ih =>
    cases h₂ with
    | refl => exact Or.inr (.step s rest)
    | step s' rest' =>
      have := Step.deterministic s s'; subst this; exact ih rest'

/-- A stuck configuration is a terminal point — no further steps possible. -/
theorem Steps.stuck_terminal {p : Prog} {c c' : Cfg}
    (h : p ⊩ c ⟶* c') (hs : ∀ d, ¬ p ⊩ c ⟶ d) : c' = c := by
  cases h with
  | refl => rfl
  | step s _ => exact absurd s (hs _)

/-- Two executions from the same start that both reach stuck endpoints
    must reach the same endpoint. -/
theorem Steps.stuck_det {p : Prog} {c c₁ c₂ : Cfg}
    (h₁ : p ⊩ c ⟶* c₁) (h₂ : p ⊩ c ⟶* c₂)
    (hs₁ : ∀ d, ¬ p ⊩ c₁ ⟶ d) (hs₂ : ∀ d, ¬ p ⊩ c₂ ⟶ d) :
    c₁ = c₂ := by
  cases Steps.deterministic_reach h₁ h₂ with
  | inl h => exact (Steps.stuck_terminal h hs₁).symm
  | inr h => exact Steps.stuck_terminal h hs₂

/-- A (cause-agnostic) runtime-error configuration and a halt from the same
    start are contradictory. -/
theorem error_run_no_halt {p : Prog} {pc : Nat} {σ_start σ_err σ_halt : Store}
    {am₀ am₂ am₅ : ArrayMem} {c_err : Cfg}
    (h_run : p ⊩ Cfg.run 0 σ_start am₀ ⟶* Cfg.run pc σ_err am₂)
    (h_error : Step p (Cfg.run pc σ_err am₂) c_err) (h_isErr : c_err.isError)
    (h_halt : haltsWithResult p 0 σ_start σ_halt am₀ am₅) : False := by
  have herr_reach : p ⊩ Cfg.run 0 σ_start am₀ ⟶* c_err :=
    Steps.trans h_run (Steps.step h_error Steps.refl)
  have err_terminal : ∀ d, ¬ Step p c_err d := fun _ h => Step.no_step_from_isError h_isErr h
  have halt_terminal : ∀ d, ¬ Step p (Cfg.halt σ_halt am₅) d := fun _ h => Step.no_step_from_halt h
  have heq := Steps.stuck_det herr_reach h_halt err_terminal halt_terminal
  cases c_err <;> simp [Cfg.isError] at h_isErr <;> exact Cfg.noConfusion heq

/-- A binop instruction with an unsafe operation produces a div-error transition. -/
theorem unsafe_binop_errors {p : Prog} {pc : Nat} {σ : Store}
    {x : Var} {op : BinOp} {y z : Var} {a b : BitVec 64}
    (hinstr : p[pc]? = some (.binop x op y z))
    (hy : σ y = .int a) (hz : σ z = .int b)
    (hunsafe : ¬ op.safe a b) :
    Step p (Cfg.run pc σ _xam) (Cfg.errorDiv σ _xam) :=
  Step.binop_divByZero hinstr hy hz hunsafe
