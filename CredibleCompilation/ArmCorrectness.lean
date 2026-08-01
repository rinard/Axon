-- Copyright (c) 2026 Martin Rinard
import CredibleCompilation.ArmSemantics
import CredibleCompilation.BvLemmas
import CredibleCompilation.ExecChecker
import Std.Tactic.BVDecide

/-!
# ARM64 Correctness Proofs

Correctness theorems for the ARM64 code generation: loadImm64_correct,
Flags.condHolds_correct, verifiedGenBoolExpr_correct,
verifiedGenInstr_correct, and ext_backward_simulation.
-/

-- === Helpers for loadImm64_correct large case ===

private theorem uint64_nat_roundtrip (u : UInt64) : u.toNat.toUInt64 = u := by
  apply UInt64.eq_of_toBitVec_eq
  simp [Nat.toUInt64]
private theorem BitVec_ofNat_UInt64_toNat (u : UInt64) :
    BitVec.ofNat 64 u.toNat = u.toBitVec := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, UInt64.toNat_toBitVec]
  exact Nat.mod_eq_of_lt u.toBitVec.isLt
private theorem insertBits_unfold (bv : BitVec 64) (imm16 : UInt64) (shift : Nat) :
    insertBits bv imm16 shift =
    (bv &&& ~~~(0xFFFF#64 <<< shift)) ||| (BitVec.ofNat 64 imm16.toNat <<< shift) := by
  unfold insertBits; rfl
/-- Execute an optional movk instruction (present when w ≠ 0, skipped when w = 0).
    Returns an ArmStepsN-length-tracked witness: `k` equals the list length
    (1 if emitted, 0 if skipped). -/
private theorem optional_movk_step (prog : ArmProg) (rd : ArmReg) (w : UInt64) (shift : Nat)
    (s : ArmState) (pc0 : Nat) (hPC : s.pc = pc0)
    (hCode : CodeAt prog pc0 (if (w != 0) = true then [ArmInstr.movk rd w shift] else [])) :
    ∃ s' k, ArmStepsN prog s s' k ∧
      k = (if (w != 0) = true then [ArmInstr.movk rd w shift] else []).length ∧
      s'.regs rd = (if (w != 0) = true then insertBits (s.regs rd) w shift else s.regs rd) ∧
      s'.stack = s.stack ∧
      s'.pc = pc0 + (if (w != 0) = true then [ArmInstr.movk rd w shift] else []).length ∧
      (∀ r, r ≠ rd → s'.regs r = s.regs r) ∧
      s'.arrayMem = s.arrayMem := by
  by_cases hw : (w != 0) = true
  · -- w ≠ 0: one movk instruction (length 1)
    simp only [hw, ite_true] at hCode ⊢
    have hInstr := hCode.head
    rw [← hPC] at hInstr
    refine ⟨s.setReg rd (insertBits (s.regs rd) w shift) |>.nextPC, 1,
      ArmStepsN.single (.movk rd w shift hInstr), rfl, ?_, ?_, ?_, ?_, ?_⟩
    · simp [ArmState.setReg, ArmState.nextPC]
    · simp [ArmState.setReg, ArmState.nextPC]
    · simp [ArmState.setReg, ArmState.nextPC, hPC]
    · intro r hr; exact ArmState.setReg_regs_other _ _ _ _ hr
    · rfl
  · -- w = 0: no instruction (length 0), identity
    simp only [hw] at hCode ⊢
    simp only [Bool.false_eq_true, ite_false]
    exact ⟨s, 0, rfl, rfl, rfl, rfl, by simp [hPC], fun _ _ => rfl, rfl⟩
private theorem uint64_shl_zero (u : UInt64) : u <<< (0 : UInt64) = u := by
  apply UInt64.eq_of_toBitVec_eq; simp
private theorem uint64_eq_zero_toBitVec (u : UInt64) (h : u = 0) :
    u.toBitVec = 0 := by rw [h]; rfl
private theorem uint64_ne_zero_bne (u : UInt64) (h : ¬(u = 0)) :
    (u != 0) = true := by simp [bne, h]

-- Bridge: convert UInt64 .toBitVec expressions to pure BitVec for bv_reassemble
private theorem uint64_toBitVec_chunk0 (u : UInt64) :
    (u &&& (0xFFFF : UInt64)).toBitVec = u.toBitVec &&& 0xFFFF#64 := rfl
private theorem uint64_toBitVec_chunk16 (u : UInt64) :
    (u >>> (16:UInt64) &&& (0xFFFF:UInt64)).toBitVec = (u.toBitVec >>> 16) &&& 0xFFFF#64 := by
  apply BitVec.eq_of_toNat_eq; simp
private theorem uint64_toBitVec_chunk32 (u : UInt64) :
    (u >>> (32:UInt64) &&& (0xFFFF:UInt64)).toBitVec = (u.toBitVec >>> 32) &&& 0xFFFF#64 := by
  apply BitVec.eq_of_toNat_eq; simp
private theorem uint64_toBitVec_chunk48 (u : UInt64) :
    (u >>> (48:UInt64) &&& (0xFFFF:UInt64)).toBitVec = (u.toBitVec >>> 48) &&& 0xFFFF#64 := by
  apply BitVec.eq_of_toNat_eq; simp
private theorem uint64_bne_false_toBitVec (u : UInt64) (h : (u != 0) = false) :
    u.toBitVec = 0 := by
  simp [bne, beq_iff_eq] at h
  rw [h]; rfl
private theorem uint64_toBitVec_toNat_roundtrip (u : UInt64) :
    u.toBitVec.toNat.toUInt64 = u := uint64_nat_roundtrip u

set_option maxHeartbeats 40000000 in
theorem loadImm64_correct (prog : ArmProg) (rd : ArmReg) (n : BitVec 64)
    (s : ArmState) (startPC : Nat)
    (hCode : CodeAt prog startPC (formalLoadImm64 rd n))
    (hPC : s.pc = startPC) :
    ∃ s' k, ArmStepsN prog s s' k ∧
      k = (formalLoadImm64 rd n).length ∧
      s'.regs rd = n ∧
      s'.stack = s.stack ∧
      s'.pc = startPC + (formalLoadImm64 rd n).length ∧
      (∀ r, r ≠ rd → s'.regs r = s.regs r) ∧
      s'.arrayMem = s.arrayMem := by
  unfold formalLoadImm64 at hCode
  split at hCode
  case isTrue hSmall =>
    -- Small case: single mov instruction (length 1)
    have hMov := hCode.head
    rw [← hPC] at hMov
    refine ⟨s.setReg rd n |>.nextPC, 1, ArmStepsN.single (.mov rd n hMov),
      ?_,
      by simp [ArmState.setReg, ArmState.nextPC],
      by simp [ArmState.setReg, ArmState.nextPC],
      by simp [ArmState.setReg, ArmState.nextPC, hPC, formalLoadImm64, hSmall],
      fun r hr => ArmState.setReg_regs_other _ _ _ _ hr, rfl⟩
    -- k = 1 = (formalLoadImm64 rd n).length in small case
    unfold formalLoadImm64; simp [hSmall]
  case isFalse hLarge =>
    -- Large case: movz/movk sequence
    -- Beta-reduce the have-bindings from the unfolded let
    dsimp only at hCode
    -- Local abbreviations
    let bits : UInt64 := n.toNat.toUInt64
    let w0 : UInt64 := bits &&& 65535
    let w1 : UInt64 := bits >>> 16 &&& 65535
    let w2 : UInt64 := bits >>> 32 &&& 65535
    let w3 : UInt64 := bits >>> 48 &&& 65535
    -- Extract CodeAt for the base instruction and each optional movk
    have hCodeBase := hCode.append_left.append_left.append_left
    have hCodeK1rest := hCode.append_left.append_left.append_right
    -- hCodeK1rest : CodeAt prog (startPC + 1) (if (w1 != 0) = true then ...)
    -- We need to adjust the PC for k2 and k3
    have hCodeK1K2 := hCode.append_left
    have hCodeK2rest := hCodeK1K2.append_right
    have hCodeK3rest := hCode.append_right
    -- Step 1: Execute movz rd w0 0
    have hMovz := hCodeBase.head
    rw [← hPC] at hMovz
    let s0 := s.setReg rd (BitVec.ofNat 64 (w0 <<< (0 : UInt64)).toNat) |>.nextPC
    have hPC0 : s0.pc = startPC + 1 := by
      simp [s0, ArmState.setReg, ArmState.nextPC, hPC]
    have hw0_shift : (w0 <<< (0 : UInt64)) = w0 := uint64_shl_zero w0
    have hRd0 : s0.regs rd = BitVec.ofNat 64 w0.toNat := by
      simp [s0, ArmState.setReg, ArmState.nextPC, hw0_shift]
    -- Step 2: optional movk for w1 at shift 16
    obtain ⟨s1, k1, hStepsN1, hk1, hRd1, hStack1, hPC1, hRegs1, hAM1⟩ :=
      optional_movk_step prog rd w1 16 s0 (startPC + 1) hPC0 hCodeK1rest
    -- Step 3: optional movk for w2 at shift 32
    -- Need to show the PC for k2
    have hLenBase : [ArmInstr.movz rd w0 0].length = 1 := by simp
    have hLenK1K2 : hCodeK1K2.append_right = hCodeK2rest := rfl
    have hPC_k2 : startPC + ([ArmInstr.movz rd w0 0] ++
        (if (w1 != 0) = true then [ArmInstr.movk rd w1 16] else [])).length =
        startPC + 1 + (if (w1 != 0) = true then [ArmInstr.movk rd w1 16] else []).length := by
      simp; omega
    rw [hPC_k2] at hCodeK2rest
    obtain ⟨s2, k2, hStepsN2, hk2, hRd2, hStack2, hPC2, hRegs2, hAM2⟩ :=
      optional_movk_step prog rd w2 32 s1
        (startPC + 1 + (if (w1 != 0) = true then [ArmInstr.movk rd w1 16] else []).length)
        hPC1 hCodeK2rest
    -- Step 4: optional movk for w3 at shift 48
    have hPC_k3 : startPC + (([ArmInstr.movz rd w0 0] ++
        (if (w1 != 0) = true then [ArmInstr.movk rd w1 16] else [])) ++
        (if (w2 != 0) = true then [ArmInstr.movk rd w2 32] else [])).length =
        startPC + 1 +
        (if (w1 != 0) = true then [ArmInstr.movk rd w1 16] else []).length +
        (if (w2 != 0) = true then [ArmInstr.movk rd w2 32] else []).length := by
      simp; omega
    rw [hPC_k3] at hCodeK3rest
    obtain ⟨s3, k3, hStepsN3, hk3, hRd3, hStack3, hPC3, hRegs3, hAM3⟩ :=
      optional_movk_step prog rd w3 48 s2
        (startPC + 1 +
         (if (w1 != 0) = true then [ArmInstr.movk rd w1 16] else []).length +
         (if (w2 != 0) = true then [ArmInstr.movk rd w2 32] else []).length)
        hPC2 hCodeK3rest
    -- Chain: movz (1 step) + 3 optional movks (k1+k2+k3 steps)
    have hMovzN : ArmStepsN prog s s0 1 := ArmStepsN.single (.movz rd w0 0 hMovz)
    have hChain : ArmStepsN prog s s3 (1 + k1 + k2 + k3) := by
      have h01 : ArmStepsN prog s s1 (1 + k1) := ArmStepsN_trans hMovzN hStepsN1
      have h02 : ArmStepsN prog s s2 (1 + k1 + k2) :=
        (show 1 + k1 + k2 = (1 + k1) + k2 from by omega) ▸
          ArmStepsN_trans h01 hStepsN2
      exact (show 1 + k1 + k2 + k3 = (1 + k1 + k2) + k3 from by omega) ▸
        ArmStepsN_trans h02 hStepsN3
    refine ⟨s3, 1 + k1 + k2 + k3, hChain, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- k = (formalLoadImm64 rd n).length
      rw [hk1, hk2, hk3]
      unfold formalLoadImm64
      simp only [hLarge, ite_false]
      simp only [List.length_append, List.length_cons, List.length_nil]
      split <;> split <;> split <;> simp <;> omega
    · -- s3.regs rd = n
      -- Key fact: bits.toBitVec = n
      have hbits_bv : bits.toBitVec = n := by
        show n.toNat.toUInt64.toBitVec = n
        rw [UInt64.toBitVec]
        apply BitVec.eq_of_toNat_eq
        simp [Nat.toUInt64]
      -- Prepare chunk zero-facts
      have hc0 : w0.toBitVec = bits.toBitVec &&& 0xFFFF#64 := uint64_toBitVec_chunk0 bits
      have hc1 : w1.toBitVec = (bits.toBitVec >>> 16) &&& 0xFFFF#64 := uint64_toBitVec_chunk16 bits
      have hc2 : w2.toBitVec = (bits.toBitVec >>> 32) &&& 0xFFFF#64 := uint64_toBitVec_chunk32 bits
      have hc3 : w3.toBitVec = (bits.toBitVec >>> 48) &&& 0xFFFF#64 := uint64_toBitVec_chunk48 bits
      -- Case split on w1, w2, w3 being zero to resolve the ifs in hRd1/hRd2/hRd3
      by_cases hw1z : w1 = 0 <;> by_cases hw2z : w2 = 0 <;> by_cases hw3z : w3 = 0
      -- Simplify the if-then-else in each hRd
      all_goals simp only [show (w1 != 0) = true ↔ w1 ≠ 0 from by simp [bne]] at hRd1
      all_goals simp only [show (w2 != 0) = true ↔ w2 ≠ 0 from by simp [bne]] at hRd2
      all_goals simp only [show (w3 != 0) = true ↔ w3 ≠ 0 from by simp [bne]] at hRd3
      all_goals (try simp only [hw1z, ne_eq, not_true_eq_false, ite_false, not_false_eq_true, ite_true] at hRd1)
      all_goals (try simp only [hw2z, ne_eq, not_true_eq_false, ite_false, not_false_eq_true, ite_true] at hRd2)
      all_goals (try simp only [hw3z, ne_eq, not_true_eq_false, ite_false, not_false_eq_true, ite_true] at hRd3)
      -- Rewrite to get a concrete BitVec expression
      all_goals rw [hRd3]
      all_goals (try rw [insertBits_unfold])
      all_goals rw [hRd2]
      all_goals (try rw [insertBits_unfold])
      all_goals rw [hRd1]
      all_goals (try rw [insertBits_unfold])
      all_goals rw [hRd0]
      -- Convert BitVec.ofNat to .toBitVec
      all_goals simp only [BitVec_ofNat_UInt64_toNat]
      -- Convert .toBitVec of each chunk to the bits expression
      all_goals rw [hc0]
      all_goals try rw [hc1]
      all_goals try rw [hc2]
      all_goals try rw [hc3]
      all_goals rw [← hbits_bv]
      -- Now apply the appropriate bv_reassemble variant
      -- Order: w1=0/w2=0/w3=0, w1=0/w2=0/w3≠0, w1=0/w2≠0/w3=0, w1=0/w2≠0/w3≠0,
      --        w1≠0/w2=0/w3=0, w1≠0/w2=0/w3≠0, w1≠0/w2≠0/w3=0, w1≠0/w2≠0/w3≠0
      · exact bv_reassemble_000 bits.toBitVec (by rw [← hc1]; exact uint64_eq_zero_toBitVec w1 hw1z) (by rw [← hc2]; exact uint64_eq_zero_toBitVec w2 hw2z) (by rw [← hc3]; exact uint64_eq_zero_toBitVec w3 hw3z)
      · exact bv_reassemble_001 bits.toBitVec (by rw [← hc1]; exact uint64_eq_zero_toBitVec w1 hw1z) (by rw [← hc2]; exact uint64_eq_zero_toBitVec w2 hw2z)
      · exact bv_reassemble_010 bits.toBitVec (by rw [← hc1]; exact uint64_eq_zero_toBitVec w1 hw1z) (by rw [← hc3]; exact uint64_eq_zero_toBitVec w3 hw3z)
      · exact bv_reassemble_011 bits.toBitVec (by rw [← hc1]; exact uint64_eq_zero_toBitVec w1 hw1z)
      · exact bv_reassemble_100 bits.toBitVec (by rw [← hc2]; exact uint64_eq_zero_toBitVec w2 hw2z) (by rw [← hc3]; exact uint64_eq_zero_toBitVec w3 hw3z)
      · exact bv_reassemble_101 bits.toBitVec (by rw [← hc2]; exact uint64_eq_zero_toBitVec w2 hw2z)
      · exact bv_reassemble_110 bits.toBitVec (by rw [← hc3]; exact uint64_eq_zero_toBitVec w3 hw3z)
      · exact bv_reassemble bits.toBitVec
    · -- s3.stack = s.stack
      rw [hStack3, hStack2, hStack1]
      simp [s0, ArmState.setReg, ArmState.nextPC]
    · -- s3.pc = startPC + (formalLoadImm64 rd n).length
      rw [hPC3]
      unfold formalLoadImm64
      simp only [hLarge, ite_false]
      simp only [List.length_append, List.length_cons, List.length_nil]
      split <;> split <;> split <;> simp <;> omega
    · -- Other registers preserved
      intro r hr
      rw [hRegs3 r hr, hRegs2 r hr, hRegs1 r hr]
      simp [s0, ArmState.setReg, ArmState.nextPC]
      intro heq; exact absurd heq hr
    · -- arrayMem preserved
      rw [hAM3, hAM2, hAM1]; simp [s0, ArmState.setReg, ArmState.nextPC]
/-- Flags.condHolds matches CmpOp.eval — trivially, since both use slt/sle
    on the stored operands. No range restriction needed. -/
theorem Flags.condHolds_correct (op : CmpOp) (a b : BitVec 64) :
    (Flags.mk a b).condHolds
      (match op with | .eq => .eq | .ne => .ne | .lt => .lt | .le => .le)
    = op.eval a b := by
  cases op <;> simp [Flags.condHolds, CmpOp.eval, BEq.beq, bne]

/-- Floating-point flags from `fcmp` correctly implement `FloatCmpOp.eval`.
    Since FP semantics are opaque (uninterpreted bitvectors), this is an axiom
    asserting our flag model faithfully represents IEEE 754 comparison. -/
axiom Flags.condHolds_float_correct (op : FloatCmpOp) (a b : BitVec 64) :
    (fcmpFlags a b).condHolds
      (match op with | .feq => .eq | .fne => .ne | .flt => .lt | .fle => .le)
    = FloatCmpOp.eval op a b


-- ============================================================
-- § fregs preservation for integer-only instruction sequences
-- ============================================================

/-- optional_movk_step extended with fregs preservation. Length-tracked variant
    (Flavor A Phase A.3): returns `ArmStepsN prog s s' k` with `k` equal to the
    emitted list length (0 if skipped, 1 if emitted). -/
private theorem optional_movk_step' (prog : ArmProg) (rd : ArmReg) (w : UInt64) (shift : Nat)
    (s : ArmState) (pc0 : Nat) (hPC : s.pc = pc0)
    (hCode : CodeAt prog pc0 (if (w != 0) = true then [ArmInstr.movk rd w shift] else [])) :
    ∃ s' k, ArmStepsN prog s s' k ∧
      k = (if (w != 0) = true then [ArmInstr.movk rd w shift] else []).length ∧
      s'.regs rd = (if (w != 0) = true then insertBits (s.regs rd) w shift else s.regs rd) ∧
      s'.stack = s.stack ∧ s'.fregs = s.fregs ∧
      s'.pc = pc0 + (if (w != 0) = true then [ArmInstr.movk rd w shift] else []).length ∧
      (∀ r, r ≠ rd → s'.regs r = s.regs r) ∧
      s'.arrayMem = s.arrayMem := by
  by_cases hw : (w != 0) = true
  · simp only [hw, ite_true] at hCode ⊢
    have hInstr := hCode.head; rw [← hPC] at hInstr
    exact ⟨s.setReg rd (insertBits (s.regs rd) w shift) |>.nextPC, 1,
      ArmStepsN.single (.movk rd w shift hInstr), rfl,
      by simp, by simp, by simp, by simp [hPC],
      fun r hr => ArmState.setReg_regs_other _ _ _ _ hr, by simp⟩
  · simp only [hw] at hCode ⊢; simp only [Bool.false_eq_true, ite_false]
    exact ⟨s, 0, rfl, rfl, rfl, rfl, rfl, by simp [hPC], fun _ _ => rfl, rfl⟩

set_option maxHeartbeats 40000000 in
/-- Re-execute formalLoadImm64 tracking fregs. Since mov/movz/movk only use
    setReg+nextPC (which preserve fregs), the resulting state has s'.fregs = s.fregs.
    This is a standalone re-derivation — it doesn't depend on loadImm64_correct's witness.
    Length-tracked variant (Flavor A Phase A.4): returns `ArmStepsN prog s s' k` with
    `k = (formalLoadImm64 rd n).length`. -/
theorem loadImm64_fregs_preserved (prog : ArmProg) (rd : ArmReg) (n : BitVec 64)
    (s : ArmState) (startPC : Nat)
    (hCode : CodeAt prog startPC (formalLoadImm64 rd n))
    (hPC : s.pc = startPC) :
    ∃ s' k, ArmStepsN prog s s' k ∧
      k = (formalLoadImm64 rd n).length ∧
      s'.fregs = s.fregs ∧
      s'.regs rd = n ∧ s'.stack = s.stack ∧
      s'.pc = startPC + (formalLoadImm64 rd n).length ∧
      (∀ r, r ≠ rd → s'.regs r = s.regs r) ∧
      s'.arrayMem = s.arrayMem := by
  unfold formalLoadImm64 at hCode
  split at hCode
  case isTrue hSmall =>
    have hMov := hCode.head
    rw [← hPC] at hMov
    refine ⟨s.setReg rd n |>.nextPC, 1, ArmStepsN.single (.mov rd n hMov),
      ?_,
      by simp [ArmState.setReg, ArmState.nextPC],
      by simp [ArmState.setReg, ArmState.nextPC],
      by simp [ArmState.setReg, ArmState.nextPC],
      by simp [ArmState.setReg, ArmState.nextPC, hPC, formalLoadImm64, hSmall],
      fun r hr => ArmState.setReg_regs_other _ _ _ _ hr, rfl⟩
    unfold formalLoadImm64; simp [hSmall]
  case isFalse hLarge =>
    dsimp only at hCode
    let bits : UInt64 := n.toNat.toUInt64
    let w0 : UInt64 := bits &&& 65535
    let w1 : UInt64 := bits >>> 16 &&& 65535
    let w2 : UInt64 := bits >>> 32 &&& 65535
    let w3 : UInt64 := bits >>> 48 &&& 65535
    have hCodeBase := hCode.append_left.append_left.append_left
    have hCodeK1rest := hCode.append_left.append_left.append_right
    have hCodeK1K2 := hCode.append_left
    have hCodeK2rest := hCodeK1K2.append_right
    have hCodeK3rest := hCode.append_right
    have hMovz := hCodeBase.head
    rw [← hPC] at hMovz
    let s0 := s.setReg rd (BitVec.ofNat 64 (w0 <<< (0 : UInt64)).toNat) |>.nextPC
    have hPC0 : s0.pc = startPC + 1 := by
      simp [s0, ArmState.setReg, ArmState.nextPC, hPC]
    have hs0f : s0.fregs = s.fregs := by simp [s0]
    have hw0_shift : (w0 <<< (0 : UInt64)) = w0 := uint64_shl_zero w0
    have hRd0 : s0.regs rd = BitVec.ofNat 64 w0.toNat := by
      simp [s0, ArmState.setReg, ArmState.nextPC, hw0_shift]
    obtain ⟨s1, k1, hStepsN1, hk1, hRd1, hStack1, hFregs1, hPC1, hRegs1, hAM1⟩ :=
      optional_movk_step' prog rd w1 16 s0 (startPC + 1) hPC0 hCodeK1rest
    have hPC_k2 : startPC + ([ArmInstr.movz rd w0 0] ++
        (if (w1 != 0) = true then [ArmInstr.movk rd w1 16] else [])).length =
        startPC + 1 + (if (w1 != 0) = true then [ArmInstr.movk rd w1 16] else []).length := by
      simp; omega
    rw [hPC_k2] at hCodeK2rest
    obtain ⟨s2, k2, hStepsN2, hk2, hRd2, hStack2, hFregs2, hPC2, hRegs2, hAM2⟩ :=
      optional_movk_step' prog rd w2 32 s1
        (startPC + 1 + (if (w1 != 0) = true then [ArmInstr.movk rd w1 16] else []).length)
        hPC1 hCodeK2rest
    have hPC_k3 : startPC + (([ArmInstr.movz rd w0 0] ++
        (if (w1 != 0) = true then [ArmInstr.movk rd w1 16] else [])) ++
        (if (w2 != 0) = true then [ArmInstr.movk rd w2 32] else [])).length =
        startPC + 1 +
        (if (w1 != 0) = true then [ArmInstr.movk rd w1 16] else []).length +
        (if (w2 != 0) = true then [ArmInstr.movk rd w2 32] else []).length := by
      simp; omega
    rw [hPC_k3] at hCodeK3rest
    obtain ⟨s3, k3, hStepsN3, hk3, hRd3, hStack3, hFregs3, hPC3, hRegs3, hAM3⟩ :=
      optional_movk_step' prog rd w3 48 s2
        (startPC + 1 +
         (if (w1 != 0) = true then [ArmInstr.movk rd w1 16] else []).length +
         (if (w2 != 0) = true then [ArmInstr.movk rd w2 32] else []).length)
        hPC2 hCodeK3rest
    have hMovzN : ArmStepsN prog s s0 1 := ArmStepsN.single (.movz rd w0 0 hMovz)
    have hChain : ArmStepsN prog s s3 (1 + k1 + k2 + k3) := by
      have h01 : ArmStepsN prog s s1 (1 + k1) := ArmStepsN_trans hMovzN hStepsN1
      have h02 : ArmStepsN prog s s2 (1 + k1 + k2) :=
        (show 1 + k1 + k2 = (1 + k1) + k2 from by omega) ▸
          ArmStepsN_trans h01 hStepsN2
      exact (show 1 + k1 + k2 + k3 = (1 + k1 + k2) + k3 from by omega) ▸
        ArmStepsN_trans h02 hStepsN3
    refine ⟨s3, 1 + k1 + k2 + k3, hChain, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hk1, hk2, hk3]
      unfold formalLoadImm64
      simp only [hLarge, ite_false]
      simp only [List.length_append, List.length_cons, List.length_nil]
      split <;> split <;> split <;> simp <;> omega
    · rw [hFregs3, hFregs2, hFregs1, hs0f]
    · have hbits_bv : bits.toBitVec = n := by
        show n.toNat.toUInt64.toBitVec = n
        rw [UInt64.toBitVec]
        apply BitVec.eq_of_toNat_eq
        simp [Nat.toUInt64]
      have hc0 : w0.toBitVec = bits.toBitVec &&& 0xFFFF#64 := uint64_toBitVec_chunk0 bits
      have hc1 : w1.toBitVec = (bits.toBitVec >>> 16) &&& 0xFFFF#64 := uint64_toBitVec_chunk16 bits
      have hc2 : w2.toBitVec = (bits.toBitVec >>> 32) &&& 0xFFFF#64 := uint64_toBitVec_chunk32 bits
      have hc3 : w3.toBitVec = (bits.toBitVec >>> 48) &&& 0xFFFF#64 := uint64_toBitVec_chunk48 bits
      by_cases hw1z : w1 = 0 <;> by_cases hw2z : w2 = 0 <;> by_cases hw3z : w3 = 0
      all_goals simp only [show (w1 != 0) = true ↔ w1 ≠ 0 from by simp [bne]] at hRd1
      all_goals simp only [show (w2 != 0) = true ↔ w2 ≠ 0 from by simp [bne]] at hRd2
      all_goals simp only [show (w3 != 0) = true ↔ w3 ≠ 0 from by simp [bne]] at hRd3
      all_goals (try simp only [hw1z, ne_eq, not_true_eq_false, ite_false, not_false_eq_true, ite_true] at hRd1)
      all_goals (try simp only [hw2z, ne_eq, not_true_eq_false, ite_false, not_false_eq_true, ite_true] at hRd2)
      all_goals (try simp only [hw3z, ne_eq, not_true_eq_false, ite_false, not_false_eq_true, ite_true] at hRd3)
      all_goals rw [hRd3]
      all_goals (try rw [insertBits_unfold])
      all_goals rw [hRd2]
      all_goals (try rw [insertBits_unfold])
      all_goals rw [hRd1]
      all_goals (try rw [insertBits_unfold])
      all_goals rw [hRd0]
      all_goals simp only [BitVec_ofNat_UInt64_toNat]
      all_goals rw [hc0]
      all_goals try rw [hc1]
      all_goals try rw [hc2]
      all_goals try rw [hc3]
      all_goals rw [← hbits_bv]
      · exact bv_reassemble_000 bits.toBitVec (by rw [← hc1]; exact uint64_eq_zero_toBitVec w1 hw1z) (by rw [← hc2]; exact uint64_eq_zero_toBitVec w2 hw2z) (by rw [← hc3]; exact uint64_eq_zero_toBitVec w3 hw3z)
      · exact bv_reassemble_001 bits.toBitVec (by rw [← hc1]; exact uint64_eq_zero_toBitVec w1 hw1z) (by rw [← hc2]; exact uint64_eq_zero_toBitVec w2 hw2z)
      · exact bv_reassemble_010 bits.toBitVec (by rw [← hc1]; exact uint64_eq_zero_toBitVec w1 hw1z) (by rw [← hc3]; exact uint64_eq_zero_toBitVec w3 hw3z)
      · exact bv_reassemble_011 bits.toBitVec (by rw [← hc1]; exact uint64_eq_zero_toBitVec w1 hw1z)
      · exact bv_reassemble_100 bits.toBitVec (by rw [← hc2]; exact uint64_eq_zero_toBitVec w2 hw2z) (by rw [← hc3]; exact uint64_eq_zero_toBitVec w3 hw3z)
      · exact bv_reassemble_101 bits.toBitVec (by rw [← hc2]; exact uint64_eq_zero_toBitVec w2 hw2z)
      · exact bv_reassemble_110 bits.toBitVec (by rw [← hc3]; exact uint64_eq_zero_toBitVec w3 hw3z)
      · exact bv_reassemble bits.toBitVec
    · rw [hStack3, hStack2, hStack1]
      simp [s0, ArmState.setReg, ArmState.nextPC]
    · rw [hPC3]
      unfold formalLoadImm64
      simp only [hLarge, ite_false]
      simp only [List.length_append, List.length_cons, List.length_nil]
      split <;> split <;> split <;> simp <;> omega
    · intro r hr
      rw [hRegs3 r hr, hRegs2 r hr, hRegs1 r hr]
      simp [s0, ArmState.setReg, ArmState.nextPC]
      intro heq; exact absurd heq hr
    · rw [hAM3, hAM2, hAM1]; simp [s0, ArmState.setReg, ArmState.nextPC]


-- ============================================================
-- § Extended correctness: verifiedGenInstr with VarLayout
-- ============================================================

/-- vLoadVar from a stack variable. -/
theorem vLoadVar_stack (layout : VarLayout) (v : Var) (tmp : ArmReg) (off : Nat)
    (hv : layout v = some (.stack off)) :
    vLoadVar layout v tmp = [.ldr tmp off] := by
  simp [vLoadVar, hv]

/-- vLoadVar from an ireg that equals tmp. -/
theorem vLoadVar_ireg_same (layout : VarLayout) (v : Var) (r : ArmReg)
    (hv : layout v = some (.ireg r)) :
    vLoadVar layout v r = [] := by
  simp [vLoadVar, hv]

/-- vLoadVar from an ireg different from tmp. -/
theorem vLoadVar_ireg_diff (layout : VarLayout) (v : Var) (tmp r : ArmReg)
    (hv : layout v = some (.ireg r)) (hne : (r == tmp) = false) :
    vLoadVar layout v tmp = [.movR tmp r] := by
  simp [vLoadVar, hv, hne]

/-- vStoreVar to a stack variable. -/
theorem vStoreVar_stack (layout : VarLayout) (v : Var) (tmp : ArmReg) (off : Nat)
    (hv : layout v = some (.stack off)) :
    vStoreVar layout v tmp = [.str tmp off] := by
  simp [vStoreVar, hv]

/-- vStoreVar to an ireg different from tmp. -/
theorem vStoreVar_ireg_diff (layout : VarLayout) (v : Var) (tmp r : ArmReg)
    (hv : layout v = some (.ireg r)) (hne : (r == tmp) = false) :
    vStoreVar layout v tmp = [.movR r tmp] := by
  simp [vStoreVar, hv, hne]

/-- vLoadVarFP from a stack variable. -/
theorem vLoadVarFP_stack (layout : VarLayout) (v : Var) (tmp : ArmFReg) (off : Nat)
    (hv : layout v = some (.stack off)) :
    vLoadVarFP layout v tmp = [.fldr tmp off] := by
  simp [vLoadVarFP, hv]

/-- vStoreVarFP to a stack variable. -/
theorem vStoreVarFP_stack (layout : VarLayout) (v : Var) (tmp : ArmFReg) (off : Nat)
    (hv : layout v = some (.stack off)) :
    vStoreVarFP layout v tmp = [.fstr tmp off] := by
  simp [vStoreVarFP, hv]

-- ============================================================
-- § ExtStateRel preservation helpers for verifiedGenInstr
-- ============================================================

/-- ExtStateRel is preserved by any state change that only modifies
    a scratch integer register (x0, x1, or x2) — provided the layout
    satisfies RegConventionSafe. -/
theorem ExtStateRel.preserved_by_ireg_only
    {layout : VarLayout} {σ : Store} {s s' : ArmState}
    (hRel : ExtStateRel layout σ s) (hRegConv : RegConventionSafe layout)
    (hStack : s'.stack = s.stack) (hFregs : s'.fregs = s.fregs)
    (hRegsOther : ∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x2 → s'.regs r = s.regs r) :
    ExtStateRel layout σ s' := by
  intro v loc hv
  match loc with
  | .stack off => rw [hStack]; exact hRel v (.stack off) hv
  | .ireg r =>
    have h0 := hRegConv.not_x0 v; have h1 := hRegConv.not_x1 v
    have h2 := hRegConv.not_x2 v
    have hr0 : r ≠ .x0 := fun h => h0 (h ▸ hv)
    have hr1 : r ≠ .x1 := fun h => h1 (h ▸ hv)
    have hr2 : r ≠ .x2 := fun h => h2 (h ▸ hv)
    show s'.regs r = (σ v).encode
    rw [hRegsOther r hr0 hr1 hr2]; exact hRel v (.ireg r) hv
  | .freg r =>
    show s'.fregs r = (σ v).encode
    rw [hFregs]; exact hRel v (.freg r) hv

/-- loadImm64 preserves ExtStateRel (it only clobbers one integer scratch register). -/
theorem loadImm64_preserves_ExtStateRel (_prog : ArmProg) (layout : VarLayout)
    (rd : ArmReg) (_n : BitVec 64) (σ : Store) (s s' : ArmState)
    (hRel : ExtStateRel layout σ s) (hRegConv : RegConventionSafe layout)
    (hStack : s'.stack = s.stack) (hFregs : s'.fregs = s.fregs)
    (hRegs : ∀ r, r ≠ rd → s'.regs r = s.regs r)
    (_hAM : s'.arrayMem = s.arrayMem)
    (hRdScratch : rd = .x0 ∨ rd = .x1 ∨ rd = .x2) :
    ExtStateRel layout σ s' := by
  apply ExtStateRel.preserved_by_ireg_only hRel hRegConv hStack hFregs
  intro r h0 h1 h2
  apply hRegs
  rcases hRdScratch with rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2


/-- Execute vLoadVar: loads v into scratch register tmp, preserving ExtStateRel.
    Case-splits on layout to determine instruction sequence.
    Length-tracked variant (Flavor A Phase A.7): `k = (vLoadVar layout v tmp).length`. -/
theorem vLoadVar_exec (prog : ArmProg) (layout : VarLayout) (v : Var) (tmp : ArmReg)
    (σ : Store) (s : ArmState) (startPC : Nat)
    (hRel : ExtStateRel layout σ s) (hRegConv : RegConventionSafe layout)
    (hPC : s.pc = startPC)
    (hCode : CodeAt prog startPC (vLoadVar layout v tmp))
    (hTmpScratch : tmp = .x0 ∨ tmp = .x1 ∨ tmp = .x2)
    (hNotFreg : ∀ r, layout v ≠ some (.freg r))
    (hMapped : layout v ≠ none) :
    ∃ s' k, ArmStepsN prog s s' k ∧
        k = (vLoadVar layout v tmp).length ∧
        s'.regs tmp = (σ v).encode ∧
        ExtStateRel layout σ s' ∧
        s'.fregs = s.fregs ∧
        s'.pc = startPC + (vLoadVar layout v tmp).length ∧
        s'.arrayMem = s.arrayMem ∧
        (∀ r, r ≠ tmp → s'.regs r = s.regs r) := by
  match hv : layout v with
  | some (.stack off) =>
    have hEq := vLoadVar_stack layout v tmp off hv
    rw [hEq] at hCode ⊢
    have hInstr := hCode.head; rw [← hPC] at hInstr
    refine ⟨s.setReg tmp (s.stack off) |>.nextPC, 1,
      ArmStepsN.single (.ldr tmp off hInstr), rfl,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp; exact hRel.read_stack hv
    · exact (ExtStateRel.setReg_preserved hRel (fun w => by
        rcases hTmpScratch with rfl | rfl | rfl
        · exact hRegConv.not_x0 w
        · exact hRegConv.not_x1 w
        · exact hRegConv.not_x2 w)).nextPC
    · simp
    · simp [hPC]
    · simp
    · intro r hne; simp [ArmState.setReg, ArmState.nextPC]
      exact fun h => absurd h hne
  | some (.ireg r) =>
    by_cases heq : r = tmp
    · subst heq
      have hEq := vLoadVar_ireg_same layout v r hv
      rw [hEq] at hCode ⊢; simp
      exact ⟨s, 0, rfl, rfl, hRel.read_ireg hv, hRel, rfl, by omega, rfl, fun _ _ => rfl⟩
    · have hbeq : (r == tmp) = false := by
        cases h : r == tmp
        · rfl
        · simp [beq_iff_eq] at h; exact absurd h heq
      have hEq := vLoadVar_ireg_diff layout v tmp r hv hbeq
      rw [hEq] at hCode ⊢
      have hInstr := hCode.head; rw [← hPC] at hInstr
      refine ⟨s.setReg tmp (s.regs r) |>.nextPC, 1,
        ArmStepsN.single (.movR tmp r hInstr), rfl,
        ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp; exact hRel.read_ireg hv
      · exact (ExtStateRel.setReg_preserved hRel (fun w => by
          rcases hTmpScratch with rfl | rfl | rfl
          · exact hRegConv.not_x0 w
          · exact hRegConv.not_x1 w
          · exact hRegConv.not_x2 w)).nextPC
      · simp
      · simp [hPC]
      · simp
      · intro r' hne; simp [ArmState.setReg, ArmState.nextPC]
        exact fun h => absurd h hne
  | some (.freg r) => exact absurd hv (hNotFreg r)
  | none => exact absurd hv hMapped

/-- Execute vLoadVar with effective register: if v is in an ireg, use it directly (no-op);
    otherwise fall back to the scratch register. -/
theorem vLoadVar_eff_exec (prog : ArmProg) (layout : VarLayout) (v : Var)
    (σ : Store) (s : ArmState) (startPC : Nat) (fallback : ArmReg)
    (hRel : ExtStateRel layout σ s) (hRegConv : RegConventionSafe layout)
    (hPC : s.pc = startPC)
    (hNotFreg : ∀ r, layout v ≠ some (.freg r))
    (hFB : fallback = .x0 ∨ fallback = .x1 ∨ fallback = .x2)
    (hMapped : layout v ≠ none) :
    let eff := match layout v with | some (.ireg r) => r | _ => fallback
    ∀ (_hCode : CodeAt prog startPC (vLoadVar layout v eff)),
    ∃ s' k, ArmStepsN prog s s' k ∧
        k = (vLoadVar layout v eff).length ∧
        s'.regs eff = (σ v).encode ∧
        ExtStateRel layout σ s' ∧
        s'.fregs = s.fregs ∧
        s'.pc = startPC + (vLoadVar layout v eff).length ∧
        s'.arrayMem = s.arrayMem ∧
        (∀ r, r ≠ eff → s'.regs r = s.regs r) := by
  match hv : layout v with
  | some (.ireg r) =>
    simp [vLoadVar, hv]
    intro _
    exact ⟨s, 0, rfl, rfl, hRel.read_ireg hv, hRel, rfl, by omega, rfl, fun _ _ => rfl⟩
  | some (.stack off) =>
    simp only [show (match some (VarLoc.stack off) with | some (.ireg r) => r | _ => fallback) = fallback from rfl]
    exact fun hCode => vLoadVar_exec prog layout v fallback σ s startPC hRel hRegConv hPC hCode hFB hNotFreg hMapped
  | some (.freg r) => exact absurd hv (hNotFreg r)
  | none => exact absurd hv hMapped

/-- Execute vStoreVar from x0: stores result into v's location, updating ExtStateRel.
    Length-tracked variant (Flavor A Phase A.9): `k = (vStoreVar layout v .x0).length`. -/
theorem vStoreVar_exec (prog : ArmProg) (layout : VarLayout) (v : Var)
    (val : Value) (σ : Store) (s : ArmState) (startPC : Nat)
    (hRel : ExtStateRel layout σ s) (hInj : VarLayoutInjective layout)
    (hRegConv : RegConventionSafe layout)
    (hPC : s.pc = startPC) (hX0 : s.regs .x0 = val.encode)
    (hCode : CodeAt prog startPC (vStoreVar layout v .x0))
    (hNotFreg : ∀ r, layout v ≠ some (.freg r)) :
    ∃ s' k, ArmStepsN prog s s' k ∧
        k = (vStoreVar layout v .x0).length ∧
        ExtStateRel layout (σ[v ↦ val]) s' ∧
        s'.pc = startPC + (vStoreVar layout v .x0).length ∧
        s'.arrayMem = s.arrayMem := by
  match hv : layout v with
  | some (.stack off) =>
    have hEq := vStoreVar_stack layout v .x0 off hv
    rw [hEq] at hCode ⊢
    have hStr := hCode.head; rw [← hPC] at hStr
    refine ⟨s.setStack off (s.regs .x0) |>.nextPC, 1,
      ArmStepsN.single (.str .x0 off hStr), rfl, ?_, ?_, ?_⟩
    · rw [hX0]; exact (ExtStateRel.update_stack hRel hInj hv).nextPC
    · simp [hPC]
    · simp
  | some (.ireg r) =>
    have hne : (r == ArmReg.x0) = false := by
      cases hr : r == ArmReg.x0
      · rfl
      · simp [beq_iff_eq] at hr; exact absurd (hr ▸ hv) (hRegConv.not_x0 v)
    have hEq := vStoreVar_ireg_diff layout v .x0 r hv hne
    rw [hEq] at hCode ⊢
    have hMovR := hCode.head; rw [← hPC] at hMovR
    refine ⟨s.setReg r (s.regs .x0) |>.nextPC, 1,
      ArmStepsN.single (.movR r .x0 hMovR), rfl, ?_, ?_, ?_⟩
    · rw [hX0]; exact (ExtStateRel.update_ireg hRel hInj hv).nextPC
    · simp [hPC]
    · simp
  | some (.freg r) => exact absurd hv (hNotFreg r)
  | none =>
    simp [vStoreVar, hv]
    refine ⟨s, 0, rfl, rfl, ?_, by omega, rfl⟩
    intro w loc hw
    have hwv : w ≠ v := fun h => by subst h; simp [hv] at hw
    rw [Store.update_other σ v w val hwv]; exact hRel w loc hw

/-- Execute vStoreVarFP from d0: stores FP result into v's location.
    Length-tracked variant (Flavor A Phase A.10): `k = (vStoreVarFP layout v .d0).length`. -/
theorem vStoreVarFP_exec (prog : ArmProg) (layout : VarLayout) (v : Var)
    (val : Value) (σ : Store) (s : ArmState) (startPC : Nat)
    (hRel : ExtStateRel layout σ s) (hInj : VarLayoutInjective layout)
    (hRegConv : RegConventionSafe layout)
    (hPC : s.pc = startPC) (hD0 : s.fregs .d0 = val.encode)
    (hCode : CodeAt prog startPC (vStoreVarFP layout v .d0))
    (hNotIreg : ∀ r, layout v ≠ some (.ireg r))
    (hFregPrecond : ∀ r, layout v = some (.freg r) → s.fregs r = val.encode) :
    ∃ s' k, ArmStepsN prog s s' k ∧
        k = (vStoreVarFP layout v .d0).length ∧
        ExtStateRel layout (σ[v ↦ val]) s' ∧
        s'.pc = startPC + (vStoreVarFP layout v .d0).length ∧
        s'.arrayMem = s.arrayMem := by
  match hv : layout v with
  | some (.stack off) =>
    have hEq := vStoreVarFP_stack layout v .d0 off hv
    rw [hEq] at hCode ⊢
    have hFstr := hCode.head; rw [← hPC] at hFstr
    refine ⟨s.setStack off (s.fregs .d0) |>.nextPC, 1,
      ArmStepsN.single (.fstr .d0 off hFstr), rfl, ?_, ?_, ?_⟩
    · rw [hD0]; exact (ExtStateRel.update_stack hRel hInj hv).nextPC
    · simp [hPC]
    · simp
  | some (.ireg r) => exact absurd hv (hNotIreg r)
  | some (.freg r) =>
    have hne : (r == ArmFReg.d0) = false := by
      simp; exact fun h => absurd hv (h ▸ hRegConv.not_d0 v)
    simp only [vStoreVarFP, hv, hne] at hCode ⊢
    have hFmov := hCode.head; rw [← hPC] at hFmov
    refine ⟨(s.setFReg r (s.fregs .d0)).nextPC, 1,
      ArmStepsN.single (.fmovRR r .d0 hFmov), rfl, ?_, ?_, ?_⟩
    · rw [hD0]; exact (ExtStateRel.update_freg hRel hInj hv).nextPC
    · simp [ArmState.nextPC, ArmState.setFReg, hPC]
    · simp [ArmState.nextPC, ArmState.setFReg]
  | none =>
    simp [vStoreVarFP, hv]
    refine ⟨s, 0, rfl, rfl, ?_, by omega, rfl⟩
    intro w loc hw
    have hwv : w ≠ v := fun h => by subst h; simp [hv] at hw
    rw [Store.update_other σ v w val hwv]; exact hRel w loc hw

/-- Execute one FP instruction and store the result into a variable's location.
    Abstracts the common "op + store" pattern shared by fbinop, fternop, and
    floatUnary proofs. Length-tracked variant (Flavor A Phase A.11):
    `k = 1 + (vStoreVarFP layout x dst_reg).length`. -/
theorem fp_exec_and_store (prog : ArmProg) (layout : VarLayout) (pcMap : Nat → Nat)
    (divS boundsS : Nat)
    (pc : Nat) (σ : Store) (am : ArrayMem) (x : Var)
    (dst_reg : ArmFReg)
    (resultBv : BitVec 64) (resultVal : Value)
    (hResultEnc : resultBv = resultVal.encode)
    (s_pre : ArmState) (prePC : Nat)
    (hRelPre : ExtStateRel layout σ s_pre)
    (hInjective : VarLayoutInjective layout)
    (hRegConv : RegConventionSafe layout)
    (hPC_pre : s_pre.pc = prePC)
    (hAM_pre : s_pre.arrayMem = am)
    (hDstReg : dst_reg = match layout x with | some (.freg r) => r | _ => .d0)
    (hNotIregX : ∀ r, layout x ≠ some (.ireg r))
    (fpOp : ArmInstr)
    (hCodeOpStore : CodeAt prog prePC (fpOp :: vStoreVarFP layout x dst_reg))
    (hArmStep : ArmStep prog s_pre (s_pre.setFReg dst_reg resultBv |>.nextPC))
    (prefixLen : Nat)
    (hPrePC_eq : prePC = pcMap pc + prefixLen)
    (hPcNext : pcMap (pc + 1) = pcMap pc + prefixLen + 1 +
      (vStoreVarFP layout x dst_reg).length) :
    ∃ s' k, ArmStepsN prog s_pre s' k ∧
      k = 1 + (vStoreVarFP layout x dst_reg).length ∧
      ExtSimRel layout pcMap divS boundsS (.run (pc + 1) (σ[x ↦ resultVal]) am) s' := by
  let s_op := (s_pre.setFReg dst_reg resultBv).nextPC
  have hStepsOpN : ArmStepsN prog s_pre s_op 1 := ArmStepsN.single hArmStep
  have hPC_op : s_op.pc = prePC + 1 := by simp [s_op, ArmState.nextPC, ArmState.setFReg, hPC_pre]
  have hAM_op : s_op.arrayMem = am := by simp [s_op, hAM_pre]
  by_cases hXFR : ∃ r, layout x = some (.freg r)
  · obtain ⟨r_dst, hDst⟩ := hXFR
    have hDR : dst_reg = r_dst := by rw [hDstReg]; simp [hDst]
    have hStore : vStoreVarFP layout x dst_reg = [] := by simp [vStoreVarFP, hDst, hDR]
    have hRelPost : ExtStateRel layout (σ[x ↦ resultVal]) s_op := by
      show ExtStateRel layout (σ[x ↦ resultVal])
        (s_pre.setFReg dst_reg resultBv).nextPC
      rw [hDR, hResultEnc]
      exact (ExtStateRel.update_freg hRelPre hInjective hDst).nextPC
    refine ⟨s_op, 1, hStepsOpN, ?_, ⟨hRelPost, ?_, hAM_op⟩⟩
    · rw [hStore]; simp
    · show s_op.pc = pcMap (pc + 1)
      simp [hStore] at hPcNext
      simp [s_op, ArmState.nextPC, ArmState.setFReg, hPC_pre, hPrePC_eq]; omega
  · have hDR : dst_reg = .d0 := by
      rw [hDstReg]; split
      · next r h => exact absurd ⟨r, h⟩ hXFR
      · rfl
    have hRelOp : ExtStateRel layout σ s_op := by
      show ExtStateRel layout σ (s_pre.setFReg dst_reg resultBv).nextPC
      rw [hDR]; exact (ExtStateRel.setFReg_preserved hRelPre (fun v => hRegConv.not_d0 v)).nextPC
    have hD0 : s_op.fregs .d0 = resultVal.encode := by
      simp [s_op, hDR, ArmState.setFReg, ArmState.nextPC, hResultEnc]
    have hCodeStore : CodeAt prog (prePC + 1) (vStoreVarFP layout x .d0) := by
      rw [← hDR]; exact hCodeOpStore.tail
    obtain ⟨s_fin, k_fin, hStepsFinN, hk_fin, hRelFin, hPC_fin, hAM_fin⟩ :=
      vStoreVarFP_exec prog layout x resultVal σ s_op (prePC + 1)
        hRelOp hInjective hRegConv hPC_op hD0 hCodeStore hNotIregX
        (fun r h => absurd ⟨r, h⟩ hXFR)
    have hChain : ArmStepsN prog s_pre s_fin (1 + k_fin) :=
      ArmStepsN_trans hStepsOpN hStepsFinN
    have : dst_reg = .d0 := hDR
    refine ⟨s_fin, 1 + k_fin, hChain, ?_, ⟨hRelFin, ?_, by simp [hAM_fin, hAM_op]⟩⟩
    · rw [hk_fin]; rw [this]
    · show s_fin.pc = pcMap (pc + 1)
      simp [this] at hPcNext; omega

/-- Execute vLoadVarFP: loads float variable v into scratch FP register tmp,
    preserving ExtStateRel. Case-splits on layout.
    Length-tracked variant (Flavor A Phase A.12): `k = (vLoadVarFP layout v tmp).length`. -/
theorem vLoadVarFP_exec (prog : ArmProg) (layout : VarLayout) (v : Var) (tmp : ArmFReg)
    (σ : Store) (s : ArmState) (startPC : Nat)
    (hRel : ExtStateRel layout σ s) (hRegConv : RegConventionSafe layout)
    (hPC : s.pc = startPC)
    (hCode : CodeAt prog startPC (vLoadVarFP layout v tmp))
    (hTmpScratch : tmp = .d0 ∨ tmp = .d1 ∨ tmp = .d2)
    (hNotIreg : ∀ r, layout v ≠ some (.ireg r))
    (hMapped : layout v ≠ none) :
    ∃ s' k, ArmStepsN prog s s' k ∧
        k = (vLoadVarFP layout v tmp).length ∧
        s'.fregs tmp = (σ v).encode ∧
        ExtStateRel layout σ s' ∧
        s'.regs = s.regs ∧
        s'.pc = startPC + (vLoadVarFP layout v tmp).length ∧
        s'.arrayMem = s.arrayMem ∧
        (∀ r, r ≠ tmp → s'.fregs r = s.fregs r) ∧
        s'.stack = s.stack := by
  match hv : layout v with
  | some (.stack off) =>
    have hEq := vLoadVarFP_stack layout v tmp off hv
    rw [hEq] at hCode ⊢
    have hInstr := hCode.head; rw [← hPC] at hInstr
    refine ⟨s.setFReg tmp (s.stack off) |>.nextPC, 1,
      ArmStepsN.single (.fldr tmp off hInstr), rfl,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [ArmState.setFReg, ArmState.nextPC]; exact hRel.read_stack hv
    · exact (ExtStateRel.setFReg_preserved hRel (fun w => by
        rcases hTmpScratch with rfl | rfl | rfl
        · exact hRegConv.not_d0 w
        · exact hRegConv.not_d1 w
        · exact hRegConv.not_d2 w)).nextPC
    · simp
    · simp [hPC]
    · simp
    · intro r hr; simp [ArmState.setFReg, ArmState.nextPC, hr]
    · simp
  | some (.freg r) =>
    have hne : (r == tmp) = false := by
      simp
      rcases hTmpScratch with rfl | rfl | rfl
      · exact fun h => absurd hv (h ▸ hRegConv.not_d0 v)
      · exact fun h => absurd hv (h ▸ hRegConv.not_d1 v)
      · exact fun h => absurd hv (h ▸ hRegConv.not_d2 v)
    simp only [vLoadVarFP, hv, hne] at hCode ⊢
    have hFmov := hCode.head; rw [← hPC] at hFmov
    refine ⟨(s.setFReg tmp (s.fregs r)).nextPC, 1,
      ArmStepsN.single (.fmovRR tmp r hFmov), rfl,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [ArmState.setFReg, ArmState.nextPC]; exact hRel.read_freg hv
    · exact (ExtStateRel.setFReg_preserved hRel (fun w => by
        rcases hTmpScratch with rfl | rfl | rfl
        · exact hRegConv.not_d0 w
        · exact hRegConv.not_d1 w
        · exact hRegConv.not_d2 w)).nextPC
    · simp
    · simp [ArmState.setFReg, ArmState.nextPC, hPC]
    · simp
    · intro r' hr'; simp [ArmState.setFReg, ArmState.nextPC, hr']
    · simp
  | some (.ireg r) => exact absurd hv (hNotIreg r)
  | none => exact absurd hv hMapped

/-- Execute vLoadVarFP with effective register: if v is in a freg, uses that freg directly;
    otherwise falls back to a scratch register. Analogous to vLoadVar_eff_exec.
    Length-tracked variant (Flavor A Phase A.13): `k = (vLoadVarFP layout v eff).length`. -/
theorem vLoadVarFP_eff_exec (prog : ArmProg) (layout : VarLayout) (v : Var)
    (σ : Store) (s : ArmState) (startPC : Nat) (fallback : ArmFReg)
    (hRel : ExtStateRel layout σ s) (hRegConv : RegConventionSafe layout)
    (hPC : s.pc = startPC)
    (hNotIreg : ∀ r, layout v ≠ some (.ireg r))
    (hFB : fallback = .d0 ∨ fallback = .d1 ∨ fallback = .d2)
    (hMapped : layout v ≠ none) :
    let eff := match layout v with | some (.freg r) => r | _ => fallback
    ∀ (_hCode : CodeAt prog startPC (vLoadVarFP layout v eff)),
    ∃ s' k, ArmStepsN prog s s' k ∧
        k = (vLoadVarFP layout v eff).length ∧
        s'.fregs eff = (σ v).encode ∧
        ExtStateRel layout σ s' ∧
        s'.regs = s.regs ∧
        s'.pc = startPC + (vLoadVarFP layout v eff).length ∧
        s'.arrayMem = s.arrayMem ∧
        (∀ r, r ≠ eff → s'.fregs r = s.fregs r) ∧
        s'.stack = s.stack := by
  match hv : layout v with
  | some (.freg r) =>
    simp [vLoadVarFP, hv]
    intro _
    exact ⟨s, 0, rfl, rfl, hRel.read_freg hv, hRel, rfl, by omega, rfl, fun _ _ => rfl, rfl⟩
  | some (.stack off) =>
    simp only [show (match some (VarLoc.stack off) with | some (.freg r) => r | _ => fallback) = fallback from rfl]
    exact fun hCode => vLoadVarFP_exec prog layout v fallback σ s startPC hRel hRegConv hPC hCode
      hFB hNotIreg hMapped
  | some (.ireg r) => exact absurd hv (hNotIreg r)
  | none => exact absurd hv hMapped

-- ============================================================
-- § loadFloatExpr_exec: unified float operand loading
-- ============================================================

/-- Load a float expression operand (.var or .flit) into a float register.
    Unifies vLoadVarFP and loadImm64+fmovToFP into a single helper.
    Length-tracked variant (Flavor A Phase A.14): `k = <code-list>.length`. -/
theorem loadFloatExpr_exec (prog : ArmProg) (layout : VarLayout) (e : Expr) (dst : ArmFReg)
    (σ : Store) (am : ArrayMem) (s : ArmState) (startPC : Nat)
    (hRel : ExtStateRel layout σ s) (hRegConv : RegConventionSafe layout)
    (hPC : s.pc = startPC)
    (hSimple : (∃ v, e = .var v) ∨ (∃ n, e = .flit n))
    (Γ : TyCtx) (hTS : TypedStore Γ σ) (hTy : ExprHasTy Γ e .float)
    (hWTL : WellTypedLayout Γ layout)
    (hMapped : ∀ v, v ∈ e.freeVars → layout v ≠ none)
    (hDst : dst = .d0 ∨ dst = .d1 ∨ dst = .d2)
    (hCode : CodeAt prog startPC
      (match e with | .var v => vLoadVarFP layout v dst
                    | .flit n => formalLoadImm64 .x0 n ++ [.fmovToFP dst .x0]
                    | _ => [])) :
    ∃ s' k, ArmStepsN prog s s' k ∧
      k = (match e with | .var v => vLoadVarFP layout v dst
                        | .flit n => formalLoadImm64 .x0 n ++ [ArmInstr.fmovToFP dst .x0]
                        | _ => []).length ∧
      s'.fregs dst = (e.eval σ am).toFloat ∧
      ExtStateRel layout σ s' ∧
      s'.pc = startPC +
        (match e with | .var v => vLoadVarFP layout v dst
                      | .flit n => formalLoadImm64 .x0 n ++ [ArmInstr.fmovToFP dst .x0]
                      | _ => []).length ∧
      s'.arrayMem = s.arrayMem ∧
      (∀ r, r ≠ dst → s'.fregs r = s.fregs r) := by
  rcases hSimple with ⟨v, rfl⟩ | ⟨n, rfl⟩
  · simp only [] at hCode
    have hNotIreg : ∀ r, layout v ≠ some (.ireg r) := hWTL.float_not_ireg hTy
    have hMappedV : layout v ≠ none := hMapped v (by simp [Expr.freeVars])
    obtain ⟨s', k', hStepsN', hk', hFreg, hRel', _, hPC', hAM', hFregs', _⟩ :=
      vLoadVarFP_exec prog layout v dst σ s startPC hRel hRegConv hPC hCode hDst hNotIreg hMappedV
    have hTyV := hTS v; rw [hTy] at hTyV
    obtain ⟨fv, hfv⟩ := Value.float_of_typeOf_float hTyV
    refine ⟨s', k', hStepsN', hk', ?_, hRel', hPC', hAM', hFregs'⟩
    simp [Expr.eval, Value.toFloat, hFreg, hfv, Value.encode]
  · simp only [] at hCode
    have hCodeImm := hCode.append_left
    have hCodeFmov := hCode.append_right
    obtain ⟨s1, k1, hStepsN1, hk1, hFregs1, hX0, hStack1, hPC1, hRegs1, hAM1⟩ :=
      loadImm64_fregs_preserved prog .x0 n s startPC hCodeImm hPC
    have hRel1 : ExtStateRel layout σ s1 :=
      loadImm64_preserves_ExtStateRel prog layout .x0 n σ s s1
        hRel hRegConv hStack1 hFregs1 hRegs1 hAM1 (Or.inl rfl)
    have hFmov := hCodeFmov.head; rw [← hPC1] at hFmov
    let s2 := s1.setFReg dst (s1.regs .x0) |>.nextPC
    have hRel2 : ExtStateRel layout σ s2 := by
      have hNotDst : ∀ w, layout w ≠ some (.freg dst) := by
        cases hDst with
        | inl h => subst h; exact fun w => hRegConv.not_d0 w
        | inr h => cases h with
          | inl h => subst h; exact fun w => hRegConv.not_d1 w
          | inr h => subst h; exact fun w => hRegConv.not_d2 w
      exact (ExtStateRel.setFReg_preserved hRel1 hNotDst).nextPC
    have hStepsFmovN : ArmStepsN prog s1 s2 1 :=
      ArmStepsN.single (ArmStep.fmovToFP dst .x0 hFmov)
    have hChain : ArmStepsN prog s s2 (k1 + 1) :=
      ArmStepsN_trans hStepsN1 hStepsFmovN
    refine ⟨s2, k1 + 1, hChain, ?_, ?_, hRel2, ?_, ?_, ?_⟩
    · rw [hk1]; simp [List.length_append]
    · simp [s2, ArmState.setFReg, ArmState.nextPC, hX0, Expr.eval, Value.toFloat]
    · simp [s2, ArmState.setFReg, ArmState.nextPC, List.length_append, hPC1]; omega
    · simp [s2, ArmState.setFReg, ArmState.nextPC, hAM1]
    · intro r hr; simp [s2, ArmState.setFReg, ArmState.nextPC, hr, hFregs1]

-- ============================================================
-- § verifiedGenBoolExpr_correct
-- ============================================================

/-- Correctness of verifiedGenBoolExpr: after execution, x0 holds the boolean result
    encoded as 1 (true) or 0 (false), and ExtStateRel is preserved. -/
theorem verifiedGenBoolExpr_correct (prog : ArmProg) (layout : VarLayout)
    (be : BoolExpr) (σ : Store) (s : ArmState) (startPC : Nat)
    (hRel : ExtStateRel layout σ s) (hRegConv : RegConventionSafe layout)
    (hCode : CodeAt prog startPC (verifiedGenBoolExpr layout be))
    (hPC : s.pc = startPC)
    (Γ : TyCtx) (hTS : TypedStore Γ σ)
    (hWTBE : WellTypedBoolExpr Γ be)
    (hWTL : WellTypedLayout Γ layout)
    (hMapped : ∀ v, v ∈ be.vars → layout v ≠ none)
    (hSimple : be.hasSimpleOps = true)
    (am : ArrayMem) :
    ∃ s' k, ArmStepsN prog s s' k ∧
      k = (verifiedGenBoolExpr layout be).length ∧
      s'.regs .x0 = (if be.eval σ am then (1 : BitVec 64) else 0) ∧
      ExtStateRel layout σ s' ∧
      s'.pc = startPC + (verifiedGenBoolExpr layout be).length ∧
      s'.arrayMem = s.arrayMem := by
  cases hWTBE with
  | bexpr => simp [BoolExpr.hasSimpleOps] at hSimple
  | lit =>
    rename_i b_val
    simp only [verifiedGenBoolExpr] at hCode
    have hMov := hCode.head; rw [← hPC] at hMov
    refine ⟨_, 1, ArmStepsN.single (.mov .x0 _ hMov), ?_, ?_, ?_, ?_, ?_⟩
    · simp [verifiedGenBoolExpr]
    · simp [ArmState.setReg, ArmState.nextPC, BoolExpr.eval]
    · exact (ExtStateRel.setReg_preserved hRel (fun w => hRegConv.not_x0 w)).nextPC
    · simp [ArmState.setReg, ArmState.nextPC, verifiedGenBoolExpr, hPC]
    · simp [ArmState.setReg, ArmState.nextPC]
  | bvar hty =>
    rename_i x
    simp only [verifiedGenBoolExpr] at hCode
    have hCodeLoad := hCode.append_left
    have hCodeAnd := hCode.append_right
    have hTy := hTS x; rw [hty] at hTy
    obtain ⟨bv, hbv⟩ := Value.bool_of_typeOf_bool hTy
    have hNotFreg : ∀ r, layout x ≠ some (.freg r) := hWTL.bool_not_freg hty
    obtain ⟨s1, k1, hStepsN1, hk1, hX0_1, hRel1, _, hPC1, hAM1, _⟩ :=
      vLoadVar_exec prog layout x .x0 σ s startPC hRel hRegConv hPC hCodeLoad
        (Or.inl rfl) hNotFreg (hMapped x (by simp [BoolExpr.vars]))
    have hAnd := hCodeAnd.head; rw [← hPC1] at hAnd
    have hStepAndN : ArmStepsN prog s1 _ 1 := ArmStepsN.single (.andImm .x0 .x0 1 hAnd)
    have hChain : ArmStepsN prog s _ (k1 + 1) := ArmStepsN_trans hStepsN1 hStepAndN
    refine ⟨_, k1 + 1, hChain, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hk1]; simp [verifiedGenBoolExpr]
    · simp [ArmState.setReg, ArmState.nextPC, hX0_1, hbv, BoolExpr.eval, Value.toBool,
            Value.encode]
      cases bv <;> simp
    · exact (ExtStateRel.setReg_preserved hRel1 (fun w => hRegConv.not_x0 w)).nextPC
    · simp [ArmState.setReg, ArmState.nextPC, hPC1, verifiedGenBoolExpr]; omega
    · simp [ArmState.setReg, ArmState.nextPC, hAM1]
  | not hbe =>
    rename_i e
    simp only [verifiedGenBoolExpr] at hCode
    have hCodeE := hCode.append_left
    have hCodeEor := hCode.append_right
    have hSimpleE : e.hasSimpleOps = true := by
      simp [BoolExpr.hasSimpleOps] at hSimple; exact hSimple
    obtain ⟨s1, k1, hStepsN1, hk1, hX0_1, hRel1, hPC1, hAM1⟩ :=
      verifiedGenBoolExpr_correct prog layout e σ s startPC hRel hRegConv hCodeE hPC Γ hTS hbe
        hWTL (fun v hv => hMapped v (by simp [BoolExpr.vars]; exact hv)) hSimpleE am
    have hEor := hCodeEor.head; rw [← hPC1] at hEor
    have hStepEorN : ArmStepsN prog s1 _ 1 := ArmStepsN.single (.eorImm .x0 .x0 1 hEor)
    have hChain : ArmStepsN prog s _ (k1 + 1) := ArmStepsN_trans hStepsN1 hStepEorN
    refine ⟨_, k1 + 1, hChain, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hk1]; simp [verifiedGenBoolExpr]
    · simp [ArmState.setReg, ArmState.nextPC, hX0_1, BoolExpr.eval]
      cases h : BoolExpr.eval σ am e <;> simp <;> decide
    · exact (ExtStateRel.setReg_preserved hRel1 (fun w => hRegConv.not_x0 w)).nextPC
    · simp [ArmState.setReg, ArmState.nextPC, hPC1, verifiedGenBoolExpr]; omega
    · simp [ArmState.setReg, ArmState.nextPC, hAM1]
  | cmp ha hb =>
    rename_i a b op'
    obtain ⟨hSimpleA, hSimpleB⟩ := BoolExpr.hasSimpleOps_cmp hSimple
    cases a with
    | var va => cases b with
      | var vb =>
        simp only [verifiedGenBoolExpr] at hCode
        have hCodeLVRV := hCode.append_left
        have hCodeCmpCset := hCode.append_right
        have hCodeLV := hCodeLVRV.append_left
        have hCodeRV := hCodeLVRV.append_right
        have hTyL := hTS va; rw [ha] at hTyL
        have hTyR := hTS vb; rw [hb] at hTyR
        obtain ⟨nL, hnL⟩ := Value.int_of_typeOf_int hTyL
        obtain ⟨nR, hnR⟩ := Value.int_of_typeOf_int hTyR
        have hNotFregLV : ∀ r, layout va ≠ some (.freg r) := hWTL.int_not_freg ha
        have hNotFregRV : ∀ r, layout vb ≠ some (.freg r) := hWTL.int_not_freg hb
        obtain ⟨s1, k1, hStepsN1, hk1, hX1, hRel1, _, hPC1, hAM1, hRegs1⟩ :=
          vLoadVar_exec prog layout va .x1 σ s startPC hRel hRegConv hPC hCodeLV
            (Or.inr (Or.inl rfl)) hNotFregLV (hMapped va (by simp [BoolExpr.vars, Expr.freeVars]))
        obtain ⟨s2, k2, hStepsN2, hk2, hX2, hRel2, _, hPC2, hAM2, hRegs2⟩ :=
          vLoadVar_exec prog layout vb .x2 σ s1 _ hRel1 hRegConv hPC1 hCodeRV
            (Or.inr (Or.inr rfl)) hNotFregRV (hMapped vb (by simp [BoolExpr.vars, Expr.freeVars]))
        have hX1_s2 : s2.regs .x1 = (σ va).encode := by
          rw [hRegs2 .x1 (by decide)]; exact hX1
        have hCmp := hCodeCmpCset.head
        rw [show startPC + (vLoadVar layout va .x1 ++ vLoadVar layout vb .x2).length
            = s2.pc from by rw [List.length_append]; omega] at hCmp
        let s3 := { s2 with flags := Flags.mk (s2.regs .x1) (s2.regs .x2), pc := s2.pc + 1 }
        have hRelCmp : ExtStateRel layout σ s3 := fun v loc hv => hRel2 v loc hv
        have hCset := hCodeCmpCset.tail.head
        rw [show startPC + (vLoadVar layout va .x1 ++ vLoadVar layout vb .x2).length + 1
            = s3.pc from by simp [s3]; omega] at hCset
        have hStepCmpN : ArmStepsN prog s2 s3 1 := ArmStepsN.single (.cmpRR .x1 .x2 hCmp)
        have hStepCsetN : ArmStepsN prog s3 _ 1 := ArmStepsN.single (.cset .x0 _ hCset)
        have h12 : ArmStepsN prog s s2 (k1 + k2) := ArmStepsN_trans hStepsN1 hStepsN2
        have h23 : ArmStepsN prog s s3 (k1 + k2 + 1) := ArmStepsN_trans h12 hStepCmpN
        have hChain : ArmStepsN prog s _ ((k1 + k2 + 1) + 1) :=
          ArmStepsN_trans h23 hStepCsetN
        refine ⟨_, (k1 + k2 + 1) + 1, hChain, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hk1, hk2]; simp [verifiedGenBoolExpr, List.length_append]; omega
        · simp [s3, ArmState.setReg, ArmState.nextPC, hX1_s2, hX2, hnL, hnR,
                BoolExpr.eval, Expr.eval, Value.toInt]
          exact congrArg (fun b => if b = true then (1 : BitVec 64) else 0)
            (Flags.condHolds_correct op' nL nR)
        · exact (ExtStateRel.setReg_preserved hRelCmp (fun w => hRegConv.not_x0 w)).nextPC
        · simp [s3, ArmState.setReg, ArmState.nextPC, verifiedGenBoolExpr]; omega
        · simp [s3, ArmState.setReg, ArmState.nextPC, hAM2, hAM1]
      | lit nb =>
        simp only [verifiedGenBoolExpr] at hCode
        have hCodeLoadImm := hCode.append_left
        have hCodeCmpCset := hCode.append_right
        have hCodeLV := hCodeLoadImm.append_left
        have hCodeImm := hCodeLoadImm.append_right
        have hTyV := hTS va; rw [ha] at hTyV
        obtain ⟨nV, hnV⟩ := Value.int_of_typeOf_int hTyV
        have hNotFregV : ∀ r, layout va ≠ some (.freg r) := hWTL.int_not_freg ha
        obtain ⟨s1, k1, hStepsN1, hk1, hX1, hRel1, _, hPC1, hAM1, hRegs1⟩ :=
          vLoadVar_exec prog layout va .x1 σ s startPC hRel hRegConv hPC hCodeLV
            (Or.inr (Or.inl rfl)) hNotFregV (hMapped va (by simp [BoolExpr.vars, Expr.freeVars]))
        obtain ⟨s2, k2, hStepsN2, hk2, hFregs2, hX2, hStack2, hPC2, hRegs2, hAM2⟩ :=
          loadImm64_fregs_preserved prog .x2 nb s1 _ hCodeImm hPC1
        have hX1_s2 : s2.regs .x1 = (σ va).encode := by
          rw [hRegs2 .x1 (by decide)]; exact hX1
        have hRel2 : ExtStateRel layout σ s2 :=
          loadImm64_preserves_ExtStateRel prog layout .x2 nb σ s1 s2
            hRel1 hRegConv hStack2 hFregs2 hRegs2 hAM2 (Or.inr (Or.inr rfl))
        have hCmp := hCodeCmpCset.head
        rw [show startPC + (vLoadVar layout va .x1 ++ formalLoadImm64 .x2 nb).length
            = s2.pc from by rw [List.length_append]; omega] at hCmp
        let s3 := { s2 with flags := Flags.mk (s2.regs .x1) (s2.regs .x2), pc := s2.pc + 1 }
        have hRelCmp : ExtStateRel layout σ s3 := fun v loc hv => hRel2 v loc hv
        have hCset := hCodeCmpCset.tail.head
        rw [show startPC + (vLoadVar layout va .x1 ++ formalLoadImm64 .x2 nb).length + 1
            = s3.pc from by simp [s3]; omega] at hCset
        have hStepCmpN : ArmStepsN prog s2 s3 1 := ArmStepsN.single (.cmpRR .x1 .x2 hCmp)
        have hStepCsetN : ArmStepsN prog s3 _ 1 := ArmStepsN.single (.cset .x0 _ hCset)
        have h12 : ArmStepsN prog s s2 (k1 + k2) := ArmStepsN_trans hStepsN1 hStepsN2
        have h23 : ArmStepsN prog s s3 (k1 + k2 + 1) := ArmStepsN_trans h12 hStepCmpN
        have hChain : ArmStepsN prog s _ ((k1 + k2 + 1) + 1) :=
          ArmStepsN_trans h23 hStepCsetN
        refine ⟨_, (k1 + k2 + 1) + 1, hChain, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hk1, hk2]; simp [verifiedGenBoolExpr, List.length_append]; omega
        · simp [s3, ArmState.setReg, ArmState.nextPC, hX1_s2, hX2, hnV,
                BoolExpr.eval, Expr.eval, Value.toInt]
          exact congrArg (fun b => if b = true then (1 : BitVec 64) else 0)
            (Flags.condHolds_correct op' nV nb)
        · exact (ExtStateRel.setReg_preserved hRelCmp (fun w => hRegConv.not_x0 w)).nextPC
        · simp [s3, ArmState.setReg, ArmState.nextPC, verifiedGenBoolExpr]; omega
        · simp [s3, ArmState.setReg, ArmState.nextPC, hAM2, hAM1]
      | _ => rcases hSimpleB with ⟨_, h⟩ | ⟨_, h⟩ <;> simp at h
    | lit na => cases b with
      | var vb =>
        simp only [verifiedGenBoolExpr] at hCode
        have hCodeLoadImm := hCode.append_left
        have hCodeCmpCset := hCode.append_right
        have hCodeImm := hCodeLoadImm.append_left
        have hCodeRV := hCodeLoadImm.append_right
        have hTyV := hTS vb; rw [hb] at hTyV
        obtain ⟨nV, hnV⟩ := Value.int_of_typeOf_int hTyV
        have hNotFregV : ∀ r, layout vb ≠ some (.freg r) := hWTL.int_not_freg hb
        obtain ⟨s1, k1, hStepsN1, hk1, hFregs1, hX1, hStack1, hPC1, hRegs1, hAM1⟩ :=
          loadImm64_fregs_preserved prog .x1 na s _ hCodeImm hPC
        have hRel1 : ExtStateRel layout σ s1 :=
          loadImm64_preserves_ExtStateRel prog layout .x1 na σ s s1
            hRel hRegConv hStack1 hFregs1 hRegs1 hAM1 (Or.inr (Or.inl rfl))
        obtain ⟨s2, k2, hStepsN2, hk2, hX2, hRel2, _, hPC2, hAM2, hRegs2⟩ :=
          vLoadVar_exec prog layout vb .x2 σ s1 _ hRel1 hRegConv hPC1 hCodeRV
            (Or.inr (Or.inr rfl)) hNotFregV (hMapped vb (by simp [BoolExpr.vars, Expr.freeVars]))
        have hX1_s2 : s2.regs .x1 = na := by
          rw [hRegs2 .x1 (by decide)]; exact hX1
        have hCmp := hCodeCmpCset.head
        rw [show startPC + (formalLoadImm64 .x1 na ++ vLoadVar layout vb .x2).length
            = s2.pc from by rw [List.length_append]; omega] at hCmp
        let s3 := { s2 with flags := Flags.mk (s2.regs .x1) (s2.regs .x2), pc := s2.pc + 1 }
        have hRelCmp : ExtStateRel layout σ s3 := fun v loc hv => hRel2 v loc hv
        have hCset := hCodeCmpCset.tail.head
        rw [show startPC + (formalLoadImm64 .x1 na ++ vLoadVar layout vb .x2).length + 1
            = s3.pc from by simp [s3]; omega] at hCset
        have hStepCmpN : ArmStepsN prog s2 s3 1 := ArmStepsN.single (.cmpRR .x1 .x2 hCmp)
        have hStepCsetN : ArmStepsN prog s3 _ 1 := ArmStepsN.single (.cset .x0 _ hCset)
        have h12 : ArmStepsN prog s s2 (k1 + k2) := ArmStepsN_trans hStepsN1 hStepsN2
        have h23 : ArmStepsN prog s s3 (k1 + k2 + 1) := ArmStepsN_trans h12 hStepCmpN
        have hChain : ArmStepsN prog s _ ((k1 + k2 + 1) + 1) :=
          ArmStepsN_trans h23 hStepCsetN
        refine ⟨_, (k1 + k2 + 1) + 1, hChain, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hk1, hk2]; simp [verifiedGenBoolExpr, List.length_append]; omega
        · simp [s3, ArmState.setReg, ArmState.nextPC, hX1_s2, hX2, hnV,
                BoolExpr.eval, Expr.eval, Value.toInt]
          exact congrArg (fun b => if b = true then (1 : BitVec 64) else 0)
            (Flags.condHolds_correct op' na nV)
        · exact (ExtStateRel.setReg_preserved hRelCmp (fun w => hRegConv.not_x0 w)).nextPC
        · simp [s3, ArmState.setReg, ArmState.nextPC, verifiedGenBoolExpr]; omega
        · simp [s3, ArmState.setReg, ArmState.nextPC, hAM2, hAM1]
      | lit nb =>
        simp only [verifiedGenBoolExpr] at hCode
        have hCodeLoadImm := hCode.append_left
        have hCodeCmpCset := hCode.append_right
        have hCodeImmA := hCodeLoadImm.append_left
        have hCodeImmB := hCodeLoadImm.append_right
        obtain ⟨s1, k1, hStepsN1, hk1, hFregs1, hX1, hStack1, hPC1, hRegs1, hAM1⟩ :=
          loadImm64_fregs_preserved prog .x1 na s _ hCodeImmA hPC
        have hRel1 : ExtStateRel layout σ s1 :=
          loadImm64_preserves_ExtStateRel prog layout .x1 na σ s s1
            hRel hRegConv hStack1 hFregs1 hRegs1 hAM1 (Or.inr (Or.inl rfl))
        obtain ⟨s2, k2, hStepsN2, hk2, hFregs2, hX2, hStack2, hPC2, hRegs2, hAM2⟩ :=
          loadImm64_fregs_preserved prog .x2 nb s1 _ hCodeImmB hPC1
        have hRel2 : ExtStateRel layout σ s2 :=
          loadImm64_preserves_ExtStateRel prog layout .x2 nb σ s1 s2
            hRel1 hRegConv hStack2 hFregs2 hRegs2 hAM2 (Or.inr (Or.inr rfl))
        have hX1_s2 : s2.regs .x1 = na := by
          rw [hRegs2 .x1 (by decide)]; exact hX1
        have hCmp := hCodeCmpCset.head
        rw [show startPC + (formalLoadImm64 .x1 na ++ formalLoadImm64 .x2 nb).length
            = s2.pc from by rw [List.length_append]; omega] at hCmp
        let s3 := { s2 with flags := Flags.mk (s2.regs .x1) (s2.regs .x2), pc := s2.pc + 1 }
        have hRelCmp : ExtStateRel layout σ s3 := fun v loc hv => hRel2 v loc hv
        have hCset := hCodeCmpCset.tail.head
        rw [show startPC + (formalLoadImm64 .x1 na ++ formalLoadImm64 .x2 nb).length + 1
            = s3.pc from by simp [s3]; omega] at hCset
        have hStepCmpN : ArmStepsN prog s2 s3 1 := ArmStepsN.single (.cmpRR .x1 .x2 hCmp)
        have hStepCsetN : ArmStepsN prog s3 _ 1 := ArmStepsN.single (.cset .x0 _ hCset)
        have h12 : ArmStepsN prog s s2 (k1 + k2) := ArmStepsN_trans hStepsN1 hStepsN2
        have h23 : ArmStepsN prog s s3 (k1 + k2 + 1) := ArmStepsN_trans h12 hStepCmpN
        have hChain : ArmStepsN prog s _ ((k1 + k2 + 1) + 1) :=
          ArmStepsN_trans h23 hStepCsetN
        refine ⟨_, (k1 + k2 + 1) + 1, hChain, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hk1, hk2]; simp [verifiedGenBoolExpr, List.length_append]; omega
        · simp [s3, ArmState.setReg, ArmState.nextPC, hX1_s2, hX2,
                BoolExpr.eval, Expr.eval, Value.toInt]
          exact congrArg (fun b => if b = true then (1 : BitVec 64) else 0)
            (Flags.condHolds_correct op' na nb)
        · exact (ExtStateRel.setReg_preserved hRelCmp (fun w => hRegConv.not_x0 w)).nextPC
        · simp [s3, ArmState.setReg, ArmState.nextPC, verifiedGenBoolExpr]; omega
        · simp [s3, ArmState.setReg, ArmState.nextPC, hAM2, hAM1]
      | _ => rcases hSimpleB with ⟨_, h⟩ | ⟨_, h⟩ <;> simp at h
    | _ => rcases hSimpleA with ⟨_, h⟩ | ⟨_, h⟩ <;> simp at h
  | fcmp ha hb =>
    rename_i a b fop
    obtain ⟨hSimpleA, hSimpleB⟩ := BoolExpr.hasSimpleOps_fcmp hSimple
    cases a with
    | var va => cases b with
      | var vb =>
        simp only [verifiedGenBoolExpr] at hCode
        have hCodeLVRV := hCode.append_left
        have hCodeFcmpCset := hCode.append_right
        have hCodeLV := hCodeLVRV.append_left
        have hCodeRV := hCodeLVRV.append_right
        have hTyL := hTS va; rw [ha] at hTyL
        have hTyR := hTS vb; rw [hb] at hTyR
        obtain ⟨fL, hfL⟩ := Value.float_of_typeOf_float hTyL
        obtain ⟨fR, hfR⟩ := Value.float_of_typeOf_float hTyR
        have hNotIregLV : ∀ r, layout va ≠ some (.ireg r) := hWTL.float_not_ireg ha
        have hNotIregRV : ∀ r, layout vb ≠ some (.ireg r) := hWTL.float_not_ireg hb
        obtain ⟨s1, k1, hStepsN1, hk1, hD1, hRel1, hRegsI1, hPC1, hAM1, hFregs1, _⟩ :=
          vLoadVarFP_exec prog layout va .d1 σ s startPC hRel hRegConv hPC hCodeLV
            (Or.inr (Or.inl rfl)) hNotIregLV (hMapped va (by simp [BoolExpr.vars, Expr.freeVars]))
        obtain ⟨s2, k2, hStepsN2, hk2, hD2, hRel2, hRegsI2, hPC2, hAM2, hFregs2, _⟩ :=
          vLoadVarFP_exec prog layout vb .d2 σ s1 _ hRel1 hRegConv hPC1 hCodeRV
            (Or.inr (Or.inr rfl)) hNotIregRV (hMapped vb (by simp [BoolExpr.vars, Expr.freeVars]))
        have hD1_s2 : s2.fregs .d1 = (σ va).encode := by
          rw [hFregs2 .d1 (by decide)]; exact hD1
        have hFcmp := hCodeFcmpCset.head
        rw [show startPC + (vLoadVarFP layout va .d1 ++ vLoadVarFP layout vb .d2).length
            = s2.pc from by rw [List.length_append]; omega] at hFcmp
        let s3 := { s2 with flags := fcmpFlags (s2.fregs .d1) (s2.fregs .d2), pc := s2.pc + 1 }
        have hRelFcmp : ExtStateRel layout σ s3 := fun v loc hv => hRel2 v loc hv
        have hCset := hCodeFcmpCset.tail.head
        rw [show startPC + (vLoadVarFP layout va .d1 ++ vLoadVarFP layout vb .d2).length + 1
            = s3.pc from by simp [s3]; omega] at hCset
        have hStepFcmpN : ArmStepsN prog s2 s3 1 := ArmStepsN.single (.fcmpRR .d1 .d2 hFcmp)
        have hStepCsetN : ArmStepsN prog s3 _ 1 := ArmStepsN.single (.cset .x0 _ hCset)
        have h12 : ArmStepsN prog s s2 (k1 + k2) := ArmStepsN_trans hStepsN1 hStepsN2
        have h23 : ArmStepsN prog s s3 (k1 + k2 + 1) := ArmStepsN_trans h12 hStepFcmpN
        have hChain : ArmStepsN prog s _ ((k1 + k2 + 1) + 1) :=
          ArmStepsN_trans h23 hStepCsetN
        refine ⟨_, (k1 + k2 + 1) + 1, hChain, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hk1, hk2]; simp [verifiedGenBoolExpr, List.length_append]; omega
        · simp [s3, ArmState.setReg, ArmState.nextPC, hD1_s2, hD2, hfL, hfR,
                BoolExpr.eval, Expr.eval, Value.toFloat, Value.encode]
          exact congrArg (fun b => if b = true then (1 : BitVec 64) else 0)
            (Flags.condHolds_float_correct fop fL fR)
        · exact (ExtStateRel.setReg_preserved hRelFcmp (fun w => hRegConv.not_x0 w)).nextPC
        · simp [s3, ArmState.setReg, ArmState.nextPC, verifiedGenBoolExpr]; omega
        · simp [s3, ArmState.setReg, ArmState.nextPC, hAM2, hAM1]
      | flit fb =>
        simp only [verifiedGenBoolExpr] at hCode
        have hCodeLoadImm := hCode.append_left
        have hCodeFcmpCset := hCode.append_right
        have hCodeLV := hCodeLoadImm.append_left
        have hCodeImmFmov := hCodeLoadImm.append_right
        have hTyV := hTS va; rw [ha] at hTyV
        obtain ⟨fV, hfV⟩ := Value.float_of_typeOf_float hTyV
        have hNotIregV : ∀ r, layout va ≠ some (.ireg r) := hWTL.float_not_ireg ha
        obtain ⟨s1, k1, hStepsN1, hk1, hD1, hRel1, hRegsI1, hPC1, hAM1, hFregs1, _⟩ :=
          vLoadVarFP_exec prog layout va .d1 σ s startPC hRel hRegConv hPC hCodeLV
            (Or.inr (Or.inl rfl)) hNotIregV (hMapped va (by simp [BoolExpr.vars, Expr.freeVars]))
        have hCodeImm := hCodeImmFmov.append_left
        obtain ⟨s2, k2, hStepsN2, hk2, hFregs2, hX0, hStack2, hPC2, hRegs2, hAM2⟩ :=
          loadImm64_fregs_preserved prog .x0 fb s1 _ hCodeImm hPC1
        have hD1_s2 : s2.fregs .d1 = (σ va).encode := by rw [hFregs2]; exact hD1
        have hRel2 : ExtStateRel layout σ s2 :=
          loadImm64_preserves_ExtStateRel prog layout .x0 fb σ s1 s2
            hRel1 hRegConv hStack2 hFregs2 hRegs2 hAM2 (Or.inl rfl)
        have hFmov := hCodeImmFmov.append_right |>.head
        rw [← hPC2] at hFmov
        let s3 := s2.setFReg .d2 (s2.regs .x0) |>.nextPC
        have hRel3 : ExtStateRel layout σ s3 :=
          (ExtStateRel.setFReg_preserved hRel2 (fun w => hRegConv.not_d2 w)).nextPC
        have hD1_s3 : s3.fregs .d1 = (σ va).encode := by
          simp [s3, ArmState.setFReg, ArmState.nextPC]; exact hD1_s2
        have hFcmp := hCodeFcmpCset.head
        rw [show startPC + (vLoadVarFP layout va .d1 ++ (formalLoadImm64 .x0 fb ++ [ArmInstr.fmovToFP .d2 .x0])).length
            = s3.pc from by simp [s3, ArmState.setFReg, ArmState.nextPC, List.length_append]; omega] at hFcmp
        let s4 := { s3 with flags := fcmpFlags (s3.fregs .d1) (s3.fregs .d2), pc := s3.pc + 1 }
        have hRel4 : ExtStateRel layout σ s4 := fun v loc hv => hRel3 v loc hv
        have hCset := hCodeFcmpCset.tail.head
        rw [show startPC + (vLoadVarFP layout va .d1 ++ (formalLoadImm64 .x0 fb ++ [ArmInstr.fmovToFP .d2 .x0])).length + 1
            = s4.pc from by simp [s4, s3, ArmState.setFReg, ArmState.nextPC, List.length_append]; omega] at hCset
        have hStepFmovN : ArmStepsN prog s2 s3 1 := ArmStepsN.single (.fmovToFP .d2 .x0 hFmov)
        have hStepFcmpN : ArmStepsN prog s3 s4 1 := ArmStepsN.single (.fcmpRR .d1 .d2 hFcmp)
        have hStepCsetN : ArmStepsN prog s4 _ 1 := ArmStepsN.single (.cset .x0 _ hCset)
        have h12 : ArmStepsN prog s s2 (k1 + k2) := ArmStepsN_trans hStepsN1 hStepsN2
        have h23 : ArmStepsN prog s s3 (k1 + k2 + 1) := ArmStepsN_trans h12 hStepFmovN
        have h34 : ArmStepsN prog s s4 (k1 + k2 + 1 + 1) := ArmStepsN_trans h23 hStepFcmpN
        have hChain : ArmStepsN prog s _ (k1 + k2 + 1 + 1 + 1) :=
          ArmStepsN_trans h34 hStepCsetN
        refine ⟨_, k1 + k2 + 1 + 1 + 1, hChain, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hk1, hk2]; simp [verifiedGenBoolExpr, List.length_append]; omega
        · simp [s4, s3, ArmState.setReg, ArmState.setFReg, ArmState.nextPC,
                hD1_s2, hX0, hfV, Value.encode, BoolExpr.eval, Expr.eval, Value.toFloat]
          exact congrArg (fun b => if b = true then (1 : BitVec 64) else 0)
            (Flags.condHolds_float_correct fop fV fb)
        · exact (ExtStateRel.setReg_preserved hRel4 (fun w => hRegConv.not_x0 w)).nextPC
        · simp [s4, s3, ArmState.setReg, ArmState.setFReg, ArmState.nextPC, verifiedGenBoolExpr]; omega
        · simp [s4, s3, ArmState.setReg, ArmState.setFReg, ArmState.nextPC, hAM2, hAM1]
      | _ => rcases hSimpleB with ⟨_, h⟩ | ⟨_, h⟩ <;> simp at h
    | flit fa => cases b with
      | var vb =>
        simp only [verifiedGenBoolExpr] at hCode
        have hCodeLoadImm := hCode.append_left
        have hCodeFcmpCset := hCode.append_right
        have hCodeImmFmov := hCodeLoadImm.append_left
        have hCodeRV := hCodeLoadImm.append_right
        have hTyV := hTS vb; rw [hb] at hTyV
        obtain ⟨fV, hfV⟩ := Value.float_of_typeOf_float hTyV
        have hNotIregV : ∀ r, layout vb ≠ some (.ireg r) := hWTL.float_not_ireg hb
        have hCodeImm := hCodeImmFmov.append_left
        obtain ⟨s1, k1, hStepsN1, hk1, hFregs1, hX0_1, hStack1, hPC1, hRegs1, hAM1⟩ :=
          loadImm64_fregs_preserved prog .x0 fa s _ hCodeImm hPC
        have hRel1 : ExtStateRel layout σ s1 :=
          loadImm64_preserves_ExtStateRel prog layout .x0 fa σ s s1
            hRel hRegConv hStack1 hFregs1 hRegs1 hAM1 (Or.inl rfl)
        have hFmov := hCodeImmFmov.append_right |>.head
        rw [← hPC1] at hFmov
        let s2 := s1.setFReg .d1 (s1.regs .x0) |>.nextPC
        have hRel2 : ExtStateRel layout σ s2 :=
          (ExtStateRel.setFReg_preserved hRel1 (fun w => hRegConv.not_d1 w)).nextPC
        have hD1_s2 : s2.fregs .d1 = fa := by
          simp [s2, ArmState.setFReg, ArmState.nextPC, hX0_1]
        have hStepFmovN : ArmStepsN prog s1 s2 1 := ArmStepsN.single (.fmovToFP .d1 .x0 hFmov)
        obtain ⟨s3, k3, hStepsN3, hk3, hD2, hRel3, hRegsI3, hPC3, hAM3, hFregs3, _⟩ :=
          vLoadVarFP_exec prog layout vb .d2 σ s2 _ hRel2 hRegConv
            (by simp [s2, ArmState.setFReg, ArmState.nextPC, List.length_append]; omega)
            hCodeRV
            (Or.inr (Or.inr rfl)) hNotIregV (hMapped vb (by simp [BoolExpr.vars, Expr.freeVars]))
        have hD1_s3 : s3.fregs .d1 = fa := by
          rw [hFregs3 .d1 (by decide)]; exact hD1_s2
        have hFcmp := hCodeFcmpCset.head
        rw [show startPC + ((formalLoadImm64 .x0 fa ++ [ArmInstr.fmovToFP .d1 .x0]) ++ vLoadVarFP layout vb .d2).length
            = s3.pc from by simp [List.length_append] at hPC3 ⊢; omega] at hFcmp
        let s4 := { s3 with flags := fcmpFlags (s3.fregs .d1) (s3.fregs .d2), pc := s3.pc + 1 }
        have hRel4 : ExtStateRel layout σ s4 := fun v loc hv => hRel3 v loc hv
        have hCset := hCodeFcmpCset.tail.head
        rw [show startPC + ((formalLoadImm64 .x0 fa ++ [ArmInstr.fmovToFP .d1 .x0]) ++ vLoadVarFP layout vb .d2).length + 1
            = s4.pc from by simp [s4, List.length_append] at hPC3 ⊢; omega] at hCset
        have hStepFcmpN : ArmStepsN prog s3 s4 1 := ArmStepsN.single (.fcmpRR .d1 .d2 hFcmp)
        have hStepCsetN : ArmStepsN prog s4 _ 1 := ArmStepsN.single (.cset .x0 _ hCset)
        have h12 : ArmStepsN prog s s2 (k1 + 1) := ArmStepsN_trans hStepsN1 hStepFmovN
        have h23 : ArmStepsN prog s s3 (k1 + 1 + k3) := ArmStepsN_trans h12 hStepsN3
        have h34 : ArmStepsN prog s s4 (k1 + 1 + k3 + 1) := ArmStepsN_trans h23 hStepFcmpN
        have hChain : ArmStepsN prog s _ (k1 + 1 + k3 + 1 + 1) :=
          ArmStepsN_trans h34 hStepCsetN
        refine ⟨_, k1 + 1 + k3 + 1 + 1, hChain, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hk1, hk3]; simp [verifiedGenBoolExpr, List.length_append]; omega
        · simp [s4, s2, ArmState.setReg, ArmState.setFReg, ArmState.nextPC,
                hD1_s3, hD2, hfV, Value.encode, BoolExpr.eval, Expr.eval, Value.toFloat]
          exact congrArg (fun b => if b = true then (1 : BitVec 64) else 0)
            (Flags.condHolds_float_correct fop fa fV)
        · exact (ExtStateRel.setReg_preserved hRel4 (fun w => hRegConv.not_x0 w)).nextPC
        · simp [s4, ArmState.setReg, ArmState.setFReg, ArmState.nextPC, verifiedGenBoolExpr,
                List.length_append] at hPC3 ⊢; omega
        · simp [s4, s2, ArmState.setReg, ArmState.setFReg, ArmState.nextPC, hAM3, hAM1]
      | flit fb =>
        simp only [verifiedGenBoolExpr] at hCode
        have hCodeLoadImm := hCode.append_left
        have hCodeFcmpCset := hCode.append_right
        have hCodeImmFmovA := hCodeLoadImm.append_left
        have hCodeImmFmovB := hCodeLoadImm.append_right
        have hCodeImmA := hCodeImmFmovA.append_left
        obtain ⟨s1, k1, hStepsN1, hk1, hFregs1, hX0_1, hStack1, hPC1, hRegs1, hAM1⟩ :=
          loadImm64_fregs_preserved prog .x0 fa s _ hCodeImmA hPC
        have hRel1 : ExtStateRel layout σ s1 :=
          loadImm64_preserves_ExtStateRel prog layout .x0 fa σ s s1
            hRel hRegConv hStack1 hFregs1 hRegs1 hAM1 (Or.inl rfl)
        have hFmovA := hCodeImmFmovA.append_right |>.head
        rw [← hPC1] at hFmovA
        let s2 := s1.setFReg .d1 (s1.regs .x0) |>.nextPC
        have hRel2 : ExtStateRel layout σ s2 :=
          (ExtStateRel.setFReg_preserved hRel1 (fun w => hRegConv.not_d1 w)).nextPC
        have hD1_s2 : s2.fregs .d1 = fa := by
          simp [s2, ArmState.setFReg, ArmState.nextPC, hX0_1]
        have hStepFmovAN : ArmStepsN prog s1 s2 1 := ArmStepsN.single (.fmovToFP .d1 .x0 hFmovA)
        have hCodeImmB := hCodeImmFmovB.append_left
        obtain ⟨s3, k3, hStepsN3, hk3, hFregs3, hX0_3, hStack3, hPC3, hRegs3, hAM3⟩ :=
          loadImm64_fregs_preserved prog .x0 fb s2 _ hCodeImmB
            (by simp [s2, ArmState.setFReg, ArmState.nextPC, List.length_append]; omega)
        have hRel3 : ExtStateRel layout σ s3 :=
          loadImm64_preserves_ExtStateRel prog layout .x0 fb σ s2 s3
            hRel2 hRegConv hStack3 hFregs3 hRegs3 hAM3 (Or.inl rfl)
        have hD1_s3 : s3.fregs .d1 = fa := by rw [hFregs3]; exact hD1_s2
        have hFmovB := hCodeImmFmovB.append_right |>.head
        rw [← hPC3] at hFmovB
        let s4 := s3.setFReg .d2 (s3.regs .x0) |>.nextPC
        have hRel4 : ExtStateRel layout σ s4 :=
          (ExtStateRel.setFReg_preserved hRel3 (fun w => hRegConv.not_d2 w)).nextPC
        have hD1_s4 : s4.fregs .d1 = fa := by
          simp [s4, ArmState.setFReg, ArmState.nextPC]; exact hD1_s3
        have hD2_s4 : s4.fregs .d2 = fb := by
          simp [s4, ArmState.setFReg, ArmState.nextPC, hX0_3]
        have hStepFmovBN : ArmStepsN prog s3 s4 1 := ArmStepsN.single (.fmovToFP .d2 .x0 hFmovB)
        have hFcmp := hCodeFcmpCset.head
        rw [show startPC + ((formalLoadImm64 .x0 fa ++ [ArmInstr.fmovToFP .d1 .x0]) ++ (formalLoadImm64 .x0 fb ++ [ArmInstr.fmovToFP .d2 .x0])).length
            = s4.pc from by simp [s4, ArmState.setFReg, ArmState.nextPC, List.length_append] at hPC3 ⊢; omega] at hFcmp
        let s5 := { s4 with flags := fcmpFlags (s4.fregs .d1) (s4.fregs .d2), pc := s4.pc + 1 }
        have hRel5 : ExtStateRel layout σ s5 := fun v loc hv => hRel4 v loc hv
        have hCset := hCodeFcmpCset.tail.head
        rw [show startPC + ((formalLoadImm64 .x0 fa ++ [ArmInstr.fmovToFP .d1 .x0]) ++ (formalLoadImm64 .x0 fb ++ [ArmInstr.fmovToFP .d2 .x0])).length + 1
            = s5.pc from by simp [s5, s4, ArmState.setFReg, ArmState.nextPC, List.length_append] at hPC3 ⊢; omega] at hCset
        have hStepFcmpN : ArmStepsN prog s4 s5 1 := ArmStepsN.single (.fcmpRR .d1 .d2 hFcmp)
        have hStepCsetN : ArmStepsN prog s5 _ 1 := ArmStepsN.single (.cset .x0 _ hCset)
        have h12 : ArmStepsN prog s s2 (k1 + 1) := ArmStepsN_trans hStepsN1 hStepFmovAN
        have h23 : ArmStepsN prog s s3 (k1 + 1 + k3) := ArmStepsN_trans h12 hStepsN3
        have h34 : ArmStepsN prog s s4 (k1 + 1 + k3 + 1) := ArmStepsN_trans h23 hStepFmovBN
        have h45 : ArmStepsN prog s s5 (k1 + 1 + k3 + 1 + 1) := ArmStepsN_trans h34 hStepFcmpN
        have hChain : ArmStepsN prog s _ (k1 + 1 + k3 + 1 + 1 + 1) :=
          ArmStepsN_trans h45 hStepCsetN
        refine ⟨_, k1 + 1 + k3 + 1 + 1 + 1, hChain, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hk1, hk3]; simp [verifiedGenBoolExpr, List.length_append]; omega
        · simp only [s5, ArmState.setReg, ArmState.nextPC, hD1_s4, hD2_s4]
          simp [BoolExpr.eval, Expr.eval, Value.toFloat]
          exact congrArg (fun b => if b = true then (1 : BitVec 64) else 0)
            (Flags.condHolds_float_correct fop fa fb)
        · exact (ExtStateRel.setReg_preserved hRel5 (fun w => hRegConv.not_x0 w)).nextPC
        · simp [s5, s4, ArmState.setReg, ArmState.setFReg, ArmState.nextPC, verifiedGenBoolExpr,
                List.length_append] at hPC3 ⊢; omega
        · simp [s5, s4, s2, ArmState.setReg, ArmState.setFReg, ArmState.nextPC, hAM3, hAM1]
      | _ => rcases hSimpleB with ⟨_, h⟩ | ⟨_, h⟩ <;> simp at h
    | _ => rcases hSimpleA with ⟨_, h⟩ | ⟨_, h⟩ <;> simp at h

-- Old verifiedGenBoolExpr_correct proof body removed during BoolExpr Expr-operand refactor.
-- The `cmpLit`/`fcmpLit`/flip cases are eliminated; remaining cases need rebuilding.
/-  Old proof text preserved for reference:
  | bvar hty =>
    rename_i x
    simp only [verifiedGenBoolExpr] at hCode
    have hCodeLoad := hCode.append_left
    have hCodeAnd := hCode.append_right
    -- x is a bool variable; get its value
    have hTy := hTS x; rw [hty] at hTy
    obtain ⟨bv, hbv⟩ := Value.bool_of_typeOf_bool hTy
    -- Load x into x0 (x is a bool, so not in freg — from WellTypedLayout)
    have hNotFreg : ∀ r, layout x ≠ some (.freg r) := hWTL.bool_not_freg hty
    obtain ⟨s1, _, hSteps1N, _, hX0_1, hRel1, _, hPC1, hAM1, _⟩ :=
      vLoadVar_exec prog layout x .x0 σ s startPC hRel hRegConv hPC hCodeLoad
        (Or.inl rfl) hNotFreg (hMapped x (by simp [BoolExpr.vars]))
    have hSteps1 := ArmStepsN_to_ArmSteps hSteps1N
    -- andImm x0 x0 1
    have hAnd := hCodeAnd.head; rw [← hPC1] at hAnd
    refine ⟨_, hSteps1.trans (.single (.andImm .x0 .x0 1 hAnd)), ?_, ?_, ?_, ?_⟩
    · simp [ArmState.setReg, ArmState.nextPC, hX0_1, hbv, BoolExpr.eval, Value.toBool,
            Value.encode]
      cases bv <;> simp
    · exact (ExtStateRel.setReg_preserved hRel1 (fun w => hRegConv.not_x0 w)).nextPC
    · simp [ArmState.setReg, ArmState.nextPC, hPC1, verifiedGenBoolExpr]; omega
    · simp [ArmState.setReg, ArmState.nextPC, hAM1]
  | not hbe =>
    rename_i e
    simp only [verifiedGenBoolExpr] at hCode
    have hCodeE := hCode.append_left
    have hCodeEor := hCode.append_right
    -- Recursive call
    obtain ⟨s1, _, hSteps1N, _, hX0_1, hRel1, hPC1, hAM1⟩ :=
      verifiedGenBoolExpr_correct prog layout e σ s startPC hRel hRegConv hCodeE hPC Γ hTS hbe
        hWTL hMapped
    have hSteps1 := ArmStepsN_to_ArmSteps hSteps1N
    -- eorImm x0 x0 1
    have hEor := hCodeEor.head; rw [← hPC1] at hEor
    refine ⟨_, hSteps1.trans (.single (.eorImm .x0 .x0 1 hEor)), ?_, ?_, ?_, ?_⟩
    · simp [ArmState.setReg, ArmState.nextPC, hX0_1, BoolExpr.eval]
      cases h : BoolExpr.eval σ e <;> simp [h] <;> decide
    · exact (ExtStateRel.setReg_preserved hRel1 (fun w => hRegConv.not_x0 w)).nextPC
    · simp [ArmState.setReg, ArmState.nextPC, hPC1, verifiedGenBoolExpr]; omega
    · simp [ArmState.setReg, ArmState.nextPC, hAM1]
  | cmp htyL htyR =>
    rename_i lv rv op'
    simp only [verifiedGenBoolExpr] at hCode
    -- Split code: (vLoadVar lv .x1 ++ vLoadVar rv .x2) ++ [.cmp .x1 .x2, .cset .x0 cond]
    have hCodeLVRV := hCode.append_left
    have hCodeCmpCset := hCode.append_right
    have hCodeLV := hCodeLVRV.append_left
    have hCodeRV := hCodeLVRV.append_right
    -- Type info
    have hTyL := hTS lv; rw [htyL] at hTyL
    have hTyR := hTS rv; rw [htyR] at hTyR
    obtain ⟨nL, hnL⟩ := Value.int_of_typeOf_int hTyL
    obtain ⟨nR, hnR⟩ := Value.int_of_typeOf_int hTyR
    -- NotFreg from WellTypedLayout
    have hNotFregLV : ∀ r, layout lv ≠ some (.freg r) := hWTL.int_not_freg htyL
    have hNotFregRV : ∀ r, layout rv ≠ some (.freg r) := hWTL.int_not_freg htyR
    -- Step 1: vLoadVar lv into x1
    obtain ⟨s1, _, hSteps1N, _, hX1, hRel1, _, hPC1, hAM1, hRegs1⟩ :=
      vLoadVar_exec prog layout lv .x1 σ s startPC hRel hRegConv hPC hCodeLV
        (Or.inr (Or.inl rfl)) hNotFregLV (hMapped lv (by simp [BoolExpr.vars]))
    have hSteps1 := ArmStepsN_to_ArmSteps hSteps1N
    -- Step 2: vLoadVar rv into x2
    obtain ⟨s2, _, hSteps2N, _, hX2, hRel2, _, hPC2, hAM2, hRegs2⟩ :=
      vLoadVar_exec prog layout rv .x2 σ s1 _ hRel1 hRegConv hPC1 hCodeRV
        (Or.inr (Or.inr rfl)) hNotFregRV (hMapped rv (by simp [BoolExpr.vars]))
    have hSteps2 := ArmStepsN_to_ArmSteps hSteps2N
    -- x1 preserved through second vLoadVar (x2 ≠ x1)
    have hX1_s2 : s2.regs .x1 = (σ lv).encode := by
      rw [hRegs2 .x1 (by decide)]; exact hX1
    -- Step 3: cmp x1 x2 — sets flags
    have hCmp := hCodeCmpCset.head
    rw [show startPC + (vLoadVar layout lv .x1 ++ vLoadVar layout rv .x2).length
        = s2.pc from by rw [List.length_append]; omega] at hCmp
    let s3 := { s2 with flags := Flags.mk (s2.regs .x1) (s2.regs .x2), pc := s2.pc + 1 }
    have hRelCmp : ExtStateRel layout σ s3 := fun v loc hv => hRel2 v loc hv
    -- Step 4: cset x0 cond
    have hCset := hCodeCmpCset.tail.head
    rw [show startPC + (vLoadVar layout lv .x1 ++ vLoadVar layout rv .x2).length + 1
        = s3.pc from by simp [s3]; omega] at hCset
    refine ⟨_, (hSteps1.trans hSteps2).trans
      (.step (.cmpRR .x1 .x2 hCmp) (.single (.cset .x0 _ hCset))), ?_, ?_, ?_, ?_⟩
    · -- x0 = correct value
      simp [ArmState.setReg, ArmState.nextPC, hX1_s2, hX2, hnL, hnR,
            BoolExpr.eval, Value.toInt]
      exact congrArg (fun b => if b = true then (1 : BitVec 64) else 0)
        (Flags.condHolds_correct op' nL nR)
    · -- ExtStateRel preserved
      exact (ExtStateRel.setReg_preserved hRelCmp (fun w => hRegConv.not_x0 w)).nextPC
    · -- pc advanced
      simp [ArmState.setReg, ArmState.nextPC, verifiedGenBoolExpr]; omega
    · -- arrayMem preserved
      simp [ArmState.setReg, ArmState.nextPC, hAM2, hAM1]
  | cmpLit hty _hLB _hUB =>
    rename_i v op' n
    simp only [verifiedGenBoolExpr] at hCode
    -- Split code: (vLoadVar v .x1 ++ formalLoadImm64 .x2 n) ++ [.cmp .x1 .x2, .cset .x0 cond]
    have hCodeLoadImm := hCode.append_left
    have hCodeCmpCset := hCode.append_right
    have hCodeLV := hCodeLoadImm.append_left
    have hCodeImm := hCodeLoadImm.append_right
    -- Type info
    have hTyV := hTS v; rw [hty] at hTyV
    obtain ⟨nV, hnV⟩ := Value.int_of_typeOf_int hTyV
    -- NotFreg from WellTypedLayout
    have hNotFregV : ∀ r, layout v ≠ some (.freg r) := hWTL.int_not_freg hty
    -- Step 1: vLoadVar v into x1
    obtain ⟨s1, _, hSteps1N, _, hX1, hRel1, _, hPC1, hAM1, hRegs1⟩ :=
      vLoadVar_exec prog layout v .x1 σ s startPC hRel hRegConv hPC hCodeLV
        (Or.inr (Or.inl rfl)) hNotFregV (hMapped v (by simp [BoolExpr.vars]))
    have hSteps1 := ArmStepsN_to_ArmSteps hSteps1N
    -- Step 2: loadImm64 n into x2 (preserves x1 and fregs)
    obtain ⟨s2, _, hSteps2N, _, hFregs2, hX2, hStack2, hPC2, hRegs2, hAM2⟩ :=
      loadImm64_fregs_preserved prog .x2 n s1 _ hCodeImm hPC1
    have hSteps2 := ArmStepsN_to_ArmSteps hSteps2N
    -- x1 preserved through loadImm64 (x2 ≠ x1)
    have hX1_s2 : s2.regs .x1 = (σ v).encode := by
      rw [hRegs2 .x1 (by decide)]; exact hX1
    -- ExtStateRel preserved through loadImm64
    have hRel2 : ExtStateRel layout σ s2 :=
      loadImm64_preserves_ExtStateRel prog layout .x2 n σ s1 s2
        hRel1 hRegConv hStack2 hFregs2 hRegs2 hAM2 (Or.inr (Or.inr rfl))
    -- Step 3: cmp x1 x2 — sets flags
    have hCmp := hCodeCmpCset.head
    rw [show startPC + (vLoadVar layout v .x1 ++ formalLoadImm64 .x2 n).length
        = s2.pc from by rw [List.length_append]; omega] at hCmp
    let s3 := { s2 with flags := Flags.mk (s2.regs .x1) (s2.regs .x2), pc := s2.pc + 1 }
    have hRelCmp : ExtStateRel layout σ s3 := fun v loc hv => hRel2 v loc hv
    -- Step 4: cset x0 cond
    have hCset := hCodeCmpCset.tail.head
    rw [show startPC + (vLoadVar layout v .x1 ++ formalLoadImm64 .x2 n).length + 1
        = s3.pc from by simp [s3]; omega] at hCset
    refine ⟨_, (hSteps1.trans hSteps2).trans
      (.step (.cmpRR .x1 .x2 hCmp) (.single (.cset .x0 _ hCset))), ?_, ?_, ?_, ?_⟩
    · -- x0 = correct value
      simp [ArmState.setReg, ArmState.nextPC, s3, hX1_s2, hX2, hnV,
            BoolExpr.eval, Value.toInt]
      exact congrArg (fun b => if b = true then (1 : BitVec 64) else 0)
        (Flags.condHolds_correct op' nV n)
    · -- ExtStateRel preserved
      exact (ExtStateRel.setReg_preserved hRelCmp (fun w => hRegConv.not_x0 w)).nextPC
    · -- pc advanced
      simp [ArmState.setReg, ArmState.nextPC, verifiedGenBoolExpr]; omega
    · -- arrayMem preserved
      simp [ArmState.setReg, ArmState.nextPC, hAM2, hAM1]
  | fcmp htyL htyR =>
    rename_i lv rv fop
    simp only [verifiedGenBoolExpr] at hCode
    -- Split code: (vLoadVarFP lv .d1 ++ vLoadVarFP rv .d2) ++ [.fcmpR .d1 .d2, .cset .x0 cond]
    have hCodeLVRV := hCode.append_left
    have hCodeFcmpCset := hCode.append_right
    have hCodeLV := hCodeLVRV.append_left
    have hCodeRV := hCodeLVRV.append_right
    -- Type info
    have hTyL := hTS lv; rw [htyL] at hTyL
    have hTyR := hTS rv; rw [htyR] at hTyR
    obtain ⟨fL, hfL⟩ := Value.float_of_typeOf_float hTyL
    obtain ⟨fR, hfR⟩ := Value.float_of_typeOf_float hTyR
    -- NotIreg from WellTypedLayout
    have hNotIregLV : ∀ r, layout lv ≠ some (.ireg r) := hWTL.float_not_ireg htyL
    have hNotIregRV : ∀ r, layout rv ≠ some (.ireg r) := hWTL.float_not_ireg htyR
    -- Step 1: vLoadVarFP lv into d1
    obtain ⟨s1, _, hSteps1N, _, hD1, hRel1, hRegsI1, hPC1, hAM1, hFregs1, _⟩ :=
      vLoadVarFP_exec prog layout lv .d1 σ s startPC hRel hRegConv hPC hCodeLV
        (Or.inr (Or.inl rfl)) hNotIregLV (hMapped lv (by simp [BoolExpr.vars]))
    have hSteps1 := ArmStepsN_to_ArmSteps hSteps1N
    -- Step 2: vLoadVarFP rv into d2
    obtain ⟨s2, _, hSteps2N, _, hD2, hRel2, hRegsI2, hPC2, hAM2, hFregs2, _⟩ :=
      vLoadVarFP_exec prog layout rv .d2 σ s1 _ hRel1 hRegConv hPC1 hCodeRV
        (Or.inr (Or.inr rfl)) hNotIregRV (hMapped rv (by simp [BoolExpr.vars]))
    have hSteps2 := ArmStepsN_to_ArmSteps hSteps2N
    -- d1 preserved through second vLoadVarFP (d2 ≠ d1)
    have hD1_s2 : s2.fregs .d1 = (σ lv).encode := by
      rw [hFregs2 .d1 (by decide)]; exact hD1
    -- Step 3: fcmpR d1 d2 — sets flags
    have hFcmp := hCodeFcmpCset.head
    rw [show startPC + (vLoadVarFP layout lv .d1 ++ vLoadVarFP layout rv .d2).length
        = s2.pc from by rw [List.length_append]; omega] at hFcmp
    let s3 := { s2 with flags := fcmpFlags (s2.fregs .d1) (s2.fregs .d2), pc := s2.pc + 1 }
    have hRelFcmp : ExtStateRel layout σ s3 := fun v loc hv => hRel2 v loc hv
    -- Step 4: cset x0 cond
    have hCset := hCodeFcmpCset.tail.head
    rw [show startPC + (vLoadVarFP layout lv .d1 ++ vLoadVarFP layout rv .d2).length + 1
        = s3.pc from by simp [s3]; omega] at hCset
    refine ⟨_, (hSteps1.trans hSteps2).trans
      (.step (.fcmpRR .d1 .d2 hFcmp) (.single (.cset .x0 _ hCset))), ?_, ?_, ?_, ?_⟩
    · -- x0 = correct value
      simp [ArmState.setReg, ArmState.nextPC, hD1_s2, hD2, hfL, hfR,
            BoolExpr.eval, Value.toFloat, Value.encode]
      exact congrArg (fun b => if b = true then (1 : BitVec 64) else 0)
        (Flags.condHolds_float_correct fop fL fR)
    · -- ExtStateRel preserved
      exact (ExtStateRel.setReg_preserved hRelFcmp (fun w => hRegConv.not_x0 w)).nextPC
    · -- pc advanced
      simp [ArmState.setReg, ArmState.nextPC, verifiedGenBoolExpr]; omega
    · -- arrayMem preserved
      simp [ArmState.setReg, ArmState.nextPC, hAM2, hAM1]
  | fcmpLit hty =>
    rename_i v fop n
    simp only [verifiedGenBoolExpr] at hCode
    -- Split: (vLoadVarFP v .d1 ++ formalLoadImm64 .x0 n) ++ [fmovToFP .d2 .x0, fcmpR .d1 .d2, cset .x0 cond]
    have hCodeLoadImm := hCode.append_left
    have hCodeFmovFcmpCset := hCode.append_right
    have hCodeLV := hCodeLoadImm.append_left
    have hCodeImm := hCodeLoadImm.append_right
    -- Type info
    have hTyV := hTS v; rw [hty] at hTyV
    obtain ⟨fV, hfV⟩ := Value.float_of_typeOf_float hTyV
    -- NotIreg from WellTypedLayout
    have hNotIregV : ∀ r, layout v ≠ some (.ireg r) := hWTL.float_not_ireg hty
    -- Step 1: vLoadVarFP v into d1
    obtain ⟨s1, _, hSteps1N, _, hD1, hRel1, hRegsI1, hPC1, hAM1, hFregs1, _⟩ :=
      vLoadVarFP_exec prog layout v .d1 σ s startPC hRel hRegConv hPC hCodeLV
        (Or.inr (Or.inl rfl)) hNotIregV (hMapped v (by simp [BoolExpr.vars]))
    have hSteps1 := ArmStepsN_to_ArmSteps hSteps1N
    -- Step 2: loadImm64 n into x0 (preserves fregs)
    obtain ⟨s2, _, hSteps2N, _, hFregs2, hX0, hStack2, hPC2, hRegs2, hAM2⟩ :=
      loadImm64_fregs_preserved prog .x0 n s1 _ hCodeImm hPC1
    have hSteps2 := ArmStepsN_to_ArmSteps hSteps2N
    -- d1 preserved through loadImm64 (loadImm64 preserves fregs)
    have hD1_s2 : s2.fregs .d1 = (σ v).encode := by
      rw [hFregs2]; exact hD1
    -- ExtStateRel preserved through loadImm64
    have hRel2 : ExtStateRel layout σ s2 :=
      loadImm64_preserves_ExtStateRel prog layout .x0 n σ s1 s2
        hRel1 hRegConv hStack2 hFregs2 hRegs2 hAM2 (Or.inl rfl)
    -- Step 3: fmovToFP d2 x0
    have hFmov := hCodeFmovFcmpCset.head
    rw [show startPC + (vLoadVarFP layout v .d1 ++ formalLoadImm64 .x0 n).length
        = s2.pc from by rw [List.length_append]; omega] at hFmov
    let s3 := s2.setFReg .d2 (s2.regs .x0) |>.nextPC
    have hRel3 : ExtStateRel layout σ s3 :=
      (ExtStateRel.setFReg_preserved hRel2 (fun w => hRegConv.not_d2 w)).nextPC
    -- d1 preserved through fmovToFP (d2 ≠ d1)
    have hD1_s3 : s3.fregs .d1 = (σ v).encode := by
      simp [s3, ArmState.setFReg, ArmState.nextPC]; exact hD1_s2
    -- Step 4: fcmpR d1 d2 — sets flags
    have hFcmp := hCodeFmovFcmpCset.tail.head
    rw [show startPC + (vLoadVarFP layout v .d1 ++ formalLoadImm64 .x0 n).length + 1
        = s3.pc from by simp [s3, ArmState.setFReg, ArmState.nextPC]; omega] at hFcmp
    let s4 := { s3 with flags := fcmpFlags (s3.fregs .d1) (s3.fregs .d2), pc := s3.pc + 1 }
    have hRel4 : ExtStateRel layout σ s4 := fun v loc hv => hRel3 v loc hv
    -- Step 5: cset x0 cond
    have hCset := hCodeFmovFcmpCset.tail.tail.head
    rw [show startPC + (vLoadVarFP layout v .d1 ++ formalLoadImm64 .x0 n).length + 2
        = s4.pc from by simp [s4, s3, ArmState.setFReg, ArmState.nextPC]; omega] at hCset
    refine ⟨_, (hSteps1.trans hSteps2).trans
      (.step (.fmovToFP .d2 .x0 hFmov) (.step (.fcmpRR .d1 .d2 hFcmp) (.single (.cset .x0 _ hCset)))),
      ?_, ?_, ?_, ?_⟩
    · -- x0 = correct value
      have hD1_s2 : s2.fregs .d1 = (σ v).encode := by rw [hFregs2]; exact hD1
      simp [s4, s3, ArmState.setReg, ArmState.setFReg, ArmState.nextPC,
            hD1_s2, hX0, hfV, Value.encode, BoolExpr.eval, Value.toFloat]
      exact congrArg (fun b => if b = true then (1 : BitVec 64) else 0)
        (Flags.condHolds_float_correct fop fV n)
    · -- ExtStateRel preserved
      exact (ExtStateRel.setReg_preserved hRel4 (fun w => hRegConv.not_x0 w)).nextPC
    · -- pc advanced
      simp [ArmState.setReg, ArmState.setFReg, ArmState.nextPC, verifiedGenBoolExpr]; omega
    · -- arrayMem preserved
      simp [ArmState.setReg, ArmState.setFReg, ArmState.nextPC, hAM2, hAM1]
-/

/-- x1 ≠ effective ireg with x2 fallback. -/
theorem x1_ne_eff_x2 (layout : VarLayout) (v : Var)
    (hRegConv : RegConventionSafe layout) (hNotFreg : ∀ r, layout v ≠ some (.freg r)) :
    ArmReg.x1 ≠ (match layout v with | some (.ireg r) => r | _ => ArmReg.x2) := by
  match hv : layout v with
  | some (.ireg r) => intro h; exact (hRegConv.not_x1 v (h ▸ hv)).elim
  | some (.stack _) => exact (by decide : ArmReg.x1 ≠ ArmReg.x2)
  | none => exact (by decide : ArmReg.x1 ≠ ArmReg.x2)
  | some (.freg r) => exact absurd hv (hNotFreg r)

/-- Value in effective ireg preserved after state transition clobbering a different register. -/
theorem eff_ireg_val_preserved (layout : VarLayout) (v : Var) (σ : Store)
    (s2 : ArmState) (fallback clobbered : ArmReg)
    (hRel2 : ExtStateRel layout σ s2)
    (hNotFreg : ∀ r, layout v ≠ some (.freg r))
    {s1 : ArmState}
    (hRegs : ∀ r, r ≠ clobbered → s2.regs r = s1.regs r)
    (hVal1 : s1.regs (match layout v with | some (.ireg r) => r | _ => fallback) = (σ v).encode)
    (hFBneCl : fallback ≠ clobbered) :
    s2.regs (match layout v with | some (.ireg r) => r | _ => fallback) = (σ v).encode := by
  match hv : layout v with
  | some (.ireg r) => exact hRel2.read_ireg hv
  | some (.stack _) =>
    simp only [hv] at hVal1 ⊢; rw [hRegs _ hFBneCl]; exact hVal1
  | none =>
    simp only [hv] at hVal1 ⊢; rw [hRegs _ hFBneCl]; exact hVal1
  | some (.freg r) => exact absurd hv (hNotFreg r)

/-- d1 ≠ effective freg with d2 fallback. -/
theorem d1_ne_eff_d2 (layout : VarLayout) (v : Var)
    (hRegConv : RegConventionSafe layout) (hNotIreg : ∀ r, layout v ≠ some (.ireg r)) :
    ArmFReg.d1 ≠ (match layout v with | some (.freg r) => r | _ => ArmFReg.d2) := by
  match hv : layout v with
  | some (.freg r) => intro h; exact (hRegConv.not_d1 v (h ▸ hv)).elim
  | some (.stack _) => exact (by decide : ArmFReg.d1 ≠ ArmFReg.d2)
  | none => exact (by decide : ArmFReg.d1 ≠ ArmFReg.d2)
  | some (.ireg r) => exact absurd hv (hNotIreg r)

/-- Value in effective freg preserved after state change clobbering a different register. -/
theorem eff_freg_val_preserved (layout : VarLayout) (v : Var) (σ : Store)
    (s2 : ArmState) (fallback clobbered : ArmFReg)
    (hRel2 : ExtStateRel layout σ s2)
    (hNotIreg : ∀ r, layout v ≠ some (.ireg r))
    {s1 : ArmState}
    (hFregs : ∀ r, r ≠ clobbered → s2.fregs r = s1.fregs r)
    (hVal1 : s1.fregs (match layout v with | some (.freg r) => r | _ => fallback) = (σ v).encode)
    (hFBneCl : fallback ≠ clobbered) :
    s2.fregs (match layout v with | some (.freg r) => r | _ => fallback) = (σ v).encode := by
  match hv : layout v with
  | some (.freg r) => exact hRel2.read_freg hv
  | some (.stack _) =>
    simp only [hv] at hVal1 ⊢; rw [hFregs _ hFBneCl]; exact hVal1
  | none =>
    simp only [hv] at hVal1 ⊢; rw [hFregs _ hFBneCl]; exact hVal1
  | some (.ireg r) => exact absurd hv (hNotIreg r)

-- ============================================================
-- § cbnz fallback helpers (used by .iftrue / .iffall catch-alls)
-- ============================================================

/-- Forward-sim chain for `verifiedGenBoolExpr ++ [.cbnz .x0 (pcMap l_var)]`
    when `be.eval σ am = true` (cbnz taken: jumps to `pcMap l_var`).
    Used by .iftrue catch-alls. -/
theorem cbnz_taken_chain (prog : ArmProg) (layout : VarLayout) (pcMap : Nat → Nat)
    (be : BoolExpr) (l_var pc : Nat)
    (σ : Store) (am : ArrayMem) (s : ArmState)
    (hStateRel : ExtStateRel layout σ s)
    (hRegConv : RegConventionSafe layout)
    (hPcRel : s.pc = pcMap pc)
    (hCodeBE : CodeAt prog (pcMap pc) (verifiedGenBoolExpr layout be))
    (hCodeCbnz : CodeAt prog (pcMap pc + (verifiedGenBoolExpr layout be).length)
                  ([ArmInstr.cbnz .x0 (pcMap l_var)]))
    (tyCtx : TyCtx) (hTS : TypedStore tyCtx σ)
    (hWTbe : WellTypedBoolExpr tyCtx be) (hWTL : WellTypedLayout tyCtx layout)
    (hMapped_be : ∀ v, v ∈ be.vars → layout v ≠ none)
    (hSimple : be.hasSimpleOps = true)
    (hcond : be.eval σ am = true) :
    ∃ s' k, ArmStepsN prog s s' k ∧
      k = (verifiedGenBoolExpr layout be).length + 1 ∧
      ExtStateRel layout σ s' ∧
      s'.pc = pcMap l_var ∧
      s'.arrayMem = s.arrayMem := by
  obtain ⟨s1, k1, hSteps1N, hk1, hX0_1, hRel1, hPC1, hAM1⟩ :=
    verifiedGenBoolExpr_correct prog layout be σ s (pcMap pc)
      hStateRel hRegConv hCodeBE hPcRel tyCtx hTS hWTbe hWTL hMapped_be hSimple am
  have hCbnz := hCodeCbnz.head; rw [← hPC1] at hCbnz
  have hx0_ne : s1.regs .x0 ≠ 0 := by rw [hX0_1, hcond]; simp
  refine ⟨{ s1 with pc := pcMap l_var }, k1 + 1,
    ArmStepsN_trans hSteps1N (ArmStepsN.single (.cbnz_taken .x0 _ hCbnz hx0_ne)),
    by rw [hk1], hRel1, rfl, by simp [hAM1]⟩

/-- Forward-sim chain for `verifiedGenBoolExpr ++ [.cbnz .x0 (pcMap l_var)]`
    when `be.eval σ am = false` (cbnz falls through: PC advances by 1).
    Used by .iffall catch-alls. -/
theorem cbnz_fall_chain (prog : ArmProg) (layout : VarLayout) (pcMap : Nat → Nat)
    (be : BoolExpr) (l_var pc : Nat)
    (σ : Store) (am : ArrayMem) (s : ArmState)
    (hStateRel : ExtStateRel layout σ s)
    (hRegConv : RegConventionSafe layout)
    (hPcRel : s.pc = pcMap pc)
    (hCodeBE : CodeAt prog (pcMap pc) (verifiedGenBoolExpr layout be))
    (hCodeCbnz : CodeAt prog (pcMap pc + (verifiedGenBoolExpr layout be).length)
                  ([ArmInstr.cbnz .x0 (pcMap l_var)]))
    (tyCtx : TyCtx) (hTS : TypedStore tyCtx σ)
    (hWTbe : WellTypedBoolExpr tyCtx be) (hWTL : WellTypedLayout tyCtx layout)
    (hMapped_be : ∀ v, v ∈ be.vars → layout v ≠ none)
    (hSimple : be.hasSimpleOps = true)
    (hcond : be.eval σ am = false) :
    ∃ s' k, ArmStepsN prog s s' k ∧
      k = (verifiedGenBoolExpr layout be).length + 1 ∧
      ExtStateRel layout σ s' ∧
      s'.pc = pcMap pc + (verifiedGenBoolExpr layout be).length + 1 ∧
      s'.arrayMem = s.arrayMem := by
  obtain ⟨s1, k1, hSteps1N, hk1, hX0_1, hRel1, hPC1, hAM1⟩ :=
    verifiedGenBoolExpr_correct prog layout be σ s (pcMap pc)
      hStateRel hRegConv hCodeBE hPcRel tyCtx hTS hWTbe hWTL hMapped_be hSimple am
  have hCbnz := hCodeCbnz.head; rw [← hPC1] at hCbnz
  have hx0_eq : s1.regs .x0 = 0 := by rw [hX0_1, hcond]; simp
  refine ⟨s1.nextPC, k1 + 1,
    ArmStepsN_trans hSteps1N (ArmStepsN.single (.cbnz_fall .x0 _ hCbnz hx0_eq)),
    by rw [hk1], (ExtStateRel.nextPC hRel1), ?_, by simp [ArmState.nextPC, hAM1]⟩
  show s1.pc + 1 = _; rw [hPC1]

/-- Forward-sim chain for `formalLoadImm64 .x0 n ++ [.fmovToFP dst .x0]`
    from separately-supplied `hCodeImm` and `hFmov`.  Used when simp
    flattens `[fmov]` into a trailing list and the combined CodeAt
    isn't naturally available as one chunk. -/
theorem loadFlit_chain (prog : ArmProg) (layout : VarLayout)
    (dst : ArmFReg) (n : BitVec 64)
    (σ : Store) (s : ArmState) (startPC : Nat)
    (hRel : ExtStateRel layout σ s) (hRegConv : RegConventionSafe layout)
    (hPC : s.pc = startPC)
    (hCodeImm : CodeAt prog startPC (formalLoadImm64 .x0 n))
    (hFmov : prog[startPC + (formalLoadImm64 .x0 n).length]? = some (.fmovToFP dst .x0))
    (hDst : dst = .d0 ∨ dst = .d1 ∨ dst = .d2) :
    ∃ s' k, ArmStepsN prog s s' k ∧
      k = (formalLoadImm64 .x0 n).length + 1 ∧
      s'.fregs dst = n ∧
      ExtStateRel layout σ s' ∧
      s'.pc = startPC + (formalLoadImm64 .x0 n).length + 1 ∧
      s'.arrayMem = s.arrayMem ∧
      (∀ r, r ≠ dst → s'.fregs r = s.fregs r) := by
  obtain ⟨s1, k1, hSteps1N, hk1, hFregs1, hX0_1, hStack1, hPC1, hRegs1, hAM1⟩ :=
    loadImm64_fregs_preserved prog .x0 n s startPC hCodeImm hPC
  have hRel1 : ExtStateRel layout σ s1 :=
    loadImm64_preserves_ExtStateRel prog layout .x0 n σ s s1
      hRel hRegConv hStack1 hFregs1 hRegs1 hAM1 (Or.inl rfl)
  have hFmovAt : prog[s1.pc]? = some (.fmovToFP dst .x0) := by rw [hPC1]; exact hFmov
  have hNotDst : ∀ w, layout w ≠ some (.freg dst) := by
    rcases hDst with h | h | h
    · subst h; exact fun w => hRegConv.not_d0 w
    · subst h; exact fun w => hRegConv.not_d1 w
    · subst h; exact fun w => hRegConv.not_d2 w
  let s2 : ArmState := (s1.setFReg dst (s1.regs .x0)).nextPC
  refine ⟨s2, k1 + 1,
    ArmStepsN_trans hSteps1N (ArmStepsN.single (ArmStep.fmovToFP dst .x0 hFmovAt)),
    by rw [hk1], ?_,
    (ExtStateRel.setFReg_preserved hRel1 hNotDst).nextPC, ?_, ?_, ?_⟩
  · simp [s2, ArmState.setFReg, ArmState.nextPC, hX0_1]
  · simp [s2, ArmState.setFReg, ArmState.nextPC, hPC1]
  · simp [s2, ArmState.setFReg, ArmState.nextPC, hAM1]
  · intro r hr
    show (if r == dst then _ else s1.fregs r) = s.fregs r
    rw [if_neg (by simp [hr]), hFregs1]

-- § verifiedGenInstr_correct
-- ============================================================

set_option maxHeartbeats 500000 in
/-- Single TAC instruction backward simulation for the verified codegen.
    Analogous to `genInstr_correct` but uses `ExtStateRel`/`VarLayout`
    and supports register-allocated variables. -/
theorem verifiedGenInstr_correct (prog : ArmProg) (layout : VarLayout) (pcMap : Nat → Nat)
    (p : Prog) (pc : Nat) (σ : Store) (am : ArrayMem) (s : ArmState)
    (haltLabel divLabel boundsLabel : Nat)
    (arrayDecls : List (ArrayName × Nat × VarTy))
    (boundsSafe : Bool)
    (hBoundsSafeOracle : boundsSafe = true →
      (∀ dst arr idx ty, p[pc]? = some (.arrLoad dst arr idx ty) →
        ∀ idxVal, σ idx = .int idxVal → idxVal < arraySizeBv arrayDecls arr) ∧
      (∀ arr idx val ty, p[pc]? = some (.arrStore arr idx val ty) →
        ∀ idxVal, σ idx = .int idxVal → idxVal < arraySizeBv arrayDecls arr))
    (instr : TAC) (hInstr : p[pc]? = some instr)
    (hRel : ExtSimRel layout pcMap divLabel boundsLabel (.run pc σ am) s)
    (instrs : List ArmInstr)
    (hSome : verifiedGenInstr layout pcMap instr haltLabel divLabel boundsLabel arrayDecls boundsSafe = some instrs)
    -- Layout validity is now checked once by `verifiedGenerateAsm` and threaded in (the
    -- per-instruction guard was hoisted out of `verifiedGenInstr` to avoid an O(N³) compile).
    (hRC : layout.regConventionSafe = true)
    (hII : layout.isInjective = true)
    (hPC_bound : pc < p.size)
    (tyCtx : TyCtx)
    (hWT : WellTypedProg tyCtx p) (hTS : TypedStore tyCtx σ)
    (hWTL : WellTypedLayout tyCtx layout)
    (hMapped : ∀ v, v ∈ instr.vars → layout v ≠ none)
    (cfg' : Cfg) (hStep : p ⊩ Cfg.run pc σ am ⟶ cfg')
    (hCodeInstr : CodeAt prog (pcMap pc) instrs)
    (hPcNext : ∀ σ' am', cfg' = .run (pc + 1) σ' am' →
      pcMap (pc + 1) = pcMap pc + instrs.length)
    (hAD : arrayDecls = p.arrayDecls)
    (hNCSL : ∀ x op y, instr = .floatUnary x op y → op.isNative = false → NoCallerSavedLayout layout)
    (hNCSLBin : ∀ x y z, instr = .fbinop x .fpow y z → NoCallerSavedLayout layout)
    (hNCSLPrintInt : ∀ v, instr = .printInt v → NoCallerSavedLayout layout)
    (hNCSLPrintBool : ∀ v, instr = .printBool v → NoCallerSavedLayout layout)
    (hNCSLPrintFloat : ∀ v, instr = .printFloat v → NoCallerSavedLayout layout)
    (hNCSLPrintStr : ∀ lit, instr = .printString lit → NoCallerSavedLayout layout) :
    ∃ s' k, ArmStepsN prog s s' k ∧
        (∀ pc' σ' am', cfg' = .run pc' σ' am' → k = instrs.length) ∧
        ExtSimRel layout pcMap divLabel boundsLabel cfg' s' := by
  -- Phase B.0 (session 7): per-case sorries; bodies filled in B.1+.
  -- Sig is length-tracked: k tracks ArmStepsN; on .run targets, k = instrs.length.
  have hRegConv : RegConventionSafe layout := VarLayout.regConventionSafe_spec layout hRC
  have hInjective : VarLayoutInjective layout := VarLayout.isInjective_spec layout hII
  obtain ⟨hStateRel, hPcRel, hArrayMem⟩ := hRel
  cases hStep with
  | goto hinstr =>
    -- Block: [.b (pcMap l)]; k = 1 = instrs.length.
    have heq : instr = .goto _ := Option.some.inj (hInstr.symm.trans hinstr)
    rw [heq] at hSome; simp [verifiedGenInstr, hRC, hII] at hSome
    rw [← hSome] at hCodeInstr
    have hb := hCodeInstr.head
    rw [← hPcRel] at hb
    refine ⟨{ s with pc := pcMap _ }, 1, ArmStepsN.single (.branch _ hb), ?_,
      ⟨hStateRel, rfl, hArrayMem⟩⟩
    intro pc' σ' am' _hCfg
    rw [← hSome]; rfl
  | halt hinstr =>
    -- Block: [.b haltLabel]; k = 1, but cfg' = .halt so length-claim vacuous.
    have heq : instr = .halt := Option.some.inj (hInstr.symm.trans hinstr)
    rw [heq] at hSome; simp [verifiedGenInstr, hRC, hII] at hSome
    rw [← hSome] at hCodeInstr
    have hb := hCodeInstr.head
    rw [← hPcRel] at hb
    refine ⟨{ s with pc := haltLabel }, 1, ArmStepsN.single (.branch haltLabel hb), ?_,
      ⟨hStateRel, hArrayMem⟩⟩
    intro pc' σ' am' hCfg
    exact absurd hCfg (by simp)
  | binop_divByZero hinstr hy hz hs =>
    -- cfg' = .errorDiv σ am — length-claim vacuous; chain reaches divLabel sentinel.
    rename_i x op y z a b
    have heq : instr = .binop x op y z := Option.some.inj (hInstr.symm.trans hinstr)
    rw [heq] at hSome hMapped
    have hNotFregY : ∀ r, layout y ≠ some (.freg r) := by
      intro r h; have := hSome; simp [verifiedGenInstr, hRC, hII, h] at this
    have hNotFregZ : ∀ r, layout z ≠ some (.freg r) := by
      intro r h; have := hSome; simp [verifiedGenInstr, hRC, hII, h] at this
    have hNotFregX : ∀ r, layout x ≠ some (.freg r) := by
      intro r h; have := hSome; simp [verifiedGenInstr, hRC, hII, h] at this
    let lv_reg := match layout y with | some (.ireg r) => r | _ => ArmReg.x1
    let rv_reg := match layout z with | some (.ireg r) => r | _ => ArmReg.x2
    let dst_reg := match layout x with | some (.ireg r) => r | _ => ArmReg.x0
    have hb_ne0 : b = 0 := by
      cases op with
      | div => have := hs; simp [BinOp.safe] at this; exact this
      | mod => have := hs; simp [BinOp.safe] at this; exact this
      | add => exact absurd trivial hs
      | sub => exact absurd trivial hs
      | mul => exact absurd trivial hs
      | band => exact absurd trivial hs
      | bor => exact absurd trivial hs
      | bxor => exact absurd trivial hs
      | shl => exact absurd trivial hs
      | shr => exact absurd trivial hs
    have hDivMod : op = .div ∨ op = .mod := by
      cases op with
      | div => exact .inl rfl
      | mod => exact .inr rfl
      | _ => exact absurd trivial hs
    have hPrefix : ∃ rest, instrs = vLoadVar layout y lv_reg ++
        (vLoadVar layout z rv_reg ++ (.cbz rv_reg divLabel :: rest)) := by
      rcases hDivMod with h | h
      · subst h
        refine ⟨.sdivR dst_reg lv_reg rv_reg :: vStoreVar layout x dst_reg, ?_⟩
        have := hSome; simp [verifiedGenInstr, hRC, hII] at this; exact this.symm
      · subst h
        refine ⟨.sdivR .x0 lv_reg rv_reg :: .mulR .x0 .x0 rv_reg ::
                .subR dst_reg lv_reg .x0 :: vStoreVar layout x dst_reg, ?_⟩
        have := hSome; simp [verifiedGenInstr, hRC, hII] at this; exact this.symm
    obtain ⟨rest, hInstrs⟩ := hPrefix
    rw [hInstrs] at hCodeInstr
    have hCodeA := hCodeInstr.append_left
    have hCodeBcDE := hCodeInstr.append_right
    have hCodeB := hCodeBcDE.append_left
    have hCodecDE := hCodeBcDE.append_right
    obtain ⟨s1, k1, hSteps1N, _, hLV_1, hRel1, _, hPC1, hAM1, hRegs1⟩ :=
      vLoadVar_eff_exec prog layout y σ s (pcMap pc) .x1 hStateRel hRegConv hPcRel
        hNotFregY (Or.inr (Or.inl rfl)) (hMapped y (by simp [TAC.vars])) hCodeA
    obtain ⟨s2, k2, hSteps2N, _, hRV_2, hRel2, _, hPC2_, hAM2, hRegs2⟩ :=
      vLoadVar_eff_exec prog layout z σ s1
        (pcMap pc + (vLoadVar layout y lv_reg).length) .x2
        hRel1 hRegConv hPC1 hNotFregZ (Or.inr (Or.inr rfl)) (hMapped z (by simp [TAC.vars])) hCodeB
    have hPC2 : s2.pc = pcMap pc + (vLoadVar layout y lv_reg).length +
        (vLoadVar layout z rv_reg).length := hPC2_
    have hRV_eq : s2.regs rv_reg = b := by rw [hRV_2, hz]; simp [Value.encode]
    have hRV_zero : s2.regs rv_reg = (0 : BitVec 64) := by rw [hRV_eq, hb_ne0]
    have hCbz := hCodecDE.head; rw [← hPC2_] at hCbz
    let s3 : ArmState := { s2 with pc := divLabel }
    have hStepCbzN : ArmStepsN prog s2 s3 1 :=
      ArmStepsN.single (.cbz_taken rv_reg divLabel hCbz hRV_zero)
    have h12 : ArmStepsN prog s s2 (k1 + k2) := ArmStepsN_trans hSteps1N hSteps2N
    have hChain : ArmStepsN prog s s3 (k1 + k2 + 1) := ArmStepsN_trans h12 hStepCbzN
    refine ⟨s3, k1 + k2 + 1, hChain, ?_, ?_⟩
    · intro pc' σ' am' h; cases h
    · show s3.pc = divLabel; rfl
  | binop_typeError _ _ =>
    -- cfg' = .typeError σ am — length-claim vacuous; use k = 0 / .refl_zero.
    refine ⟨s, 0, ArmStepsN.refl_zero, ?_, trivial⟩
    intro pc' σ' am' h; cases h
  | arrLoad_typeError _ _ =>
    refine ⟨s, 0, ArmStepsN.refl_zero, ?_, trivial⟩
    intro pc' σ' am' h; cases h
  | arrStore_typeError _ _ =>
    refine ⟨s, 0, ArmStepsN.refl_zero, ?_, trivial⟩
    intro pc' σ' am' h; cases h
  | fbinop_typeError _ _ =>
    refine ⟨s, 0, ArmStepsN.refl_zero, ?_, trivial⟩
    intro pc' σ' am' h; cases h
  | intToFloat_typeError _ _ =>
    refine ⟨s, 0, ArmStepsN.refl_zero, ?_, trivial⟩
    intro pc' σ' am' h; cases h
  | floatToInt_typeError _ _ =>
    refine ⟨s, 0, ArmStepsN.refl_zero, ?_, trivial⟩
    intro pc' σ' am' h; cases h
  | floatUnary_typeError _ _ =>
    refine ⟨s, 0, ArmStepsN.refl_zero, ?_, trivial⟩
    intro pc' σ' am' h; cases h
  | fternop_typeError _ _ =>
    refine ⟨s, 0, ArmStepsN.refl_zero, ?_, trivial⟩
    intro pc' σ' am' h; cases h
  | arrLoad_boundsError hinstr hidx hbounds =>
    -- cfg' = .errorBounds σ am — length-claim vacuous; chain reaches boundsLabel.
    rename_i idxVal arr dst idx ty
    have heq : instr = .arrLoad dst arr idx ty := Option.some.inj (hInstr.symm.trans hinstr)
    rw [heq] at hSome hMapped
    have hPcArr : p[pc]? = some (.arrLoad dst arr idx ty) := heq ▸ hInstr
    have hNotFregIdx : ∀ r, layout idx ≠ some (.freg r) :=
      hWTL.int_not_freg (by have := hTS idx; rw [hidx] at this; exact this.symm)
    let idx_reg := match layout idx with | some (.ireg r) => r | _ => ArmReg.x1
    cases hBS : boundsSafe with
    | true =>
      have hBound := (hBoundsSafeOracle hBS).1 dst arr idx ty hPcArr idxVal hidx
      rw [hAD] at hBound
      exact absurd hBound hbounds
    | false =>
      have hBoundsAD : ¬ idxVal < arraySizeBv arrayDecls arr := by rw [hAD]; exact hbounds
      have hArg : ∃ tail, instrs = vLoadVar layout idx idx_reg ++
          ([.cmpImm idx_reg (arraySizeBv arrayDecls arr), .bCond .hs boundsLabel] ++ tail) := by
        cases ty
        · exact ⟨_, by simp [verifiedGenInstr, hRC, hII, hBS] at hSome; exact hSome.symm⟩
        · exact ⟨_, by simp [verifiedGenInstr, hRC, hII, hBS] at hSome; exact hSome.symm⟩
        · exact ⟨_, by simp [verifiedGenInstr, hRC, hII, hBS] at hSome; exact hSome.symm⟩
      obtain ⟨_tail, hInstrs⟩ := hArg
      rw [hInstrs] at hCodeInstr
      have hCodeA := hCodeInstr.append_left
      have hCodeBC := (hCodeInstr.append_right).append_left
      obtain ⟨s1, k1, hSteps1N, _, hIdx_1, _hRel1, _, hPC1, _, _⟩ :=
        vLoadVar_eff_exec prog layout idx σ s (pcMap pc) .x1 hStateRel hRegConv hPcRel
          hNotFregIdx (Or.inr (Or.inl rfl)) (hMapped idx (by simp [TAC.vars])) hCodeA
      have hIdxVal : s1.regs idx_reg = idxVal := by rw [hIdx_1, hidx]; simp [Value.encode]
      have hCmp := hCodeBC.head; rw [← hPC1] at hCmp
      let s2 := { s1 with flags := Flags.mk (s1.regs idx_reg) (arraySizeBv arrayDecls arr), pc := s1.pc + 1 }
      have hStepCmpN : ArmStepsN prog s1 s2 1 :=
        ArmStepsN.single (.cmpRI idx_reg (arraySizeBv arrayDecls arr) hCmp)
      have hCondTrue : s2.flags.condHolds .hs = true := by
        simp only [s2, Flags.condHolds, hIdxVal]
        have : arraySizeBv arrayDecls arr ≤ idxVal := by bv_omega
        simp [this]
      have hPC2 : s2.pc = pcMap pc + (vLoadVar layout idx idx_reg).length + 1 := by
        show s1.pc + 1 = _; rw [hPC1]
      have hBCond := hCodeBC.tail.head; rw [← hPC2] at hBCond
      let s3 : ArmState := { s2 with pc := boundsLabel }
      have hStepBCondN : ArmStepsN prog s2 s3 1 :=
        ArmStepsN.single (.bCond_taken .hs boundsLabel hBCond hCondTrue)
      have h12 : ArmStepsN prog s s2 (k1 + 1) := ArmStepsN_trans hSteps1N hStepCmpN
      have hChain : ArmStepsN prog s s3 (k1 + 1 + 1) := ArmStepsN_trans h12 hStepBCondN
      refine ⟨s3, k1 + 1 + 1, hChain, ?_, ?_⟩
      · intro pc' σ' am' h; cases h
      · show s3.pc = boundsLabel; rfl
  | arrStore_boundsError hinstr hidx hval hbounds =>
    rename_i ty idxVal arr idx val
    have heq : instr = .arrStore arr idx val ty := Option.some.inj (hInstr.symm.trans hinstr)
    rw [heq] at hSome hMapped
    have hPcArr : p[pc]? = some (.arrStore arr idx val ty) := heq ▸ hInstr
    have hNotFregIdx : ∀ r, layout idx ≠ some (.freg r) :=
      hWTL.int_not_freg (by have := hTS idx; rw [hidx] at this; exact this.symm)
    let idx_reg := match layout idx with | some (.ireg r) => r | _ => ArmReg.x1
    cases hBS : boundsSafe with
    | true =>
      have hBound := (hBoundsSafeOracle hBS).2 arr idx val ty hPcArr idxVal hidx
      rw [hAD] at hBound
      exact absurd hBound hbounds
    | false =>
      have hBoundsAD : ¬ idxVal < arraySizeBv arrayDecls arr := by rw [hAD]; exact hbounds
      have hArg : ∃ tail, instrs = vLoadVar layout idx idx_reg ++
          ([.cmpImm idx_reg (arraySizeBv arrayDecls arr), .bCond .hs boundsLabel] ++ tail) := by
        by_cases hTy : ty = .float
        · subst hTy
          exact ⟨_, by simp [verifiedGenInstr, hRC, hII, hBS] at hSome; exact hSome.symm⟩
        · cases ty
          · exact ⟨_, by simp [verifiedGenInstr, hRC, hII, hBS] at hSome; exact hSome.symm⟩
          · exact ⟨_, by simp [verifiedGenInstr, hRC, hII, hBS] at hSome; exact hSome.symm⟩
          · exact absurd rfl hTy
      obtain ⟨_tail, hInstrs⟩ := hArg
      rw [hInstrs] at hCodeInstr
      have hCodeA := hCodeInstr.append_left
      have hCodeBC := (hCodeInstr.append_right).append_left
      obtain ⟨s1, k1, hSteps1N, _, hIdx_1, _hRel1, _, hPC1, _, _⟩ :=
        vLoadVar_eff_exec prog layout idx σ s (pcMap pc) .x1 hStateRel hRegConv hPcRel
          hNotFregIdx (Or.inr (Or.inl rfl)) (hMapped idx (by simp [TAC.vars])) hCodeA
      have hIdxVal : s1.regs idx_reg = idxVal := by rw [hIdx_1, hidx]; simp [Value.encode]
      have hCmp := hCodeBC.head; rw [← hPC1] at hCmp
      let s2 := { s1 with flags := Flags.mk (s1.regs idx_reg) (arraySizeBv arrayDecls arr), pc := s1.pc + 1 }
      have hStepCmpN : ArmStepsN prog s1 s2 1 :=
        ArmStepsN.single (.cmpRI idx_reg (arraySizeBv arrayDecls arr) hCmp)
      have hCondTrue : s2.flags.condHolds .hs = true := by
        simp only [s2, Flags.condHolds, hIdxVal]
        have : arraySizeBv arrayDecls arr ≤ idxVal := by bv_omega
        simp [this]
      have hPC2 : s2.pc = pcMap pc + (vLoadVar layout idx idx_reg).length + 1 := by
        show s1.pc + 1 = _; rw [hPC1]
      have hBCond := hCodeBC.tail.head; rw [← hPC2] at hBCond
      let s3 : ArmState := { s2 with pc := boundsLabel }
      have hStepBCondN : ArmStepsN prog s2 s3 1 :=
        ArmStepsN.single (.bCond_taken .hs boundsLabel hBCond hCondTrue)
      have h12 : ArmStepsN prog s s2 (k1 + 1) := ArmStepsN_trans hSteps1N hStepCmpN
      have hChain : ArmStepsN prog s s3 (k1 + 1 + 1) := ArmStepsN_trans h12 hStepBCondN
      refine ⟨s3, k1 + 1 + 1, hChain, ?_, ?_⟩
      · intro pc' σ' am' h; cases h
      · show s3.pc = boundsLabel; rfl
  | print hinstr =>
    -- verifiedGenInstr returns `none` for plain `.print`; hSome contradicts.
    have heq : instr = .print _ _ := Option.some.inj (hInstr.symm.trans hinstr)
    rw [heq] at hSome; simp [verifiedGenInstr] at hSome
  | printInt hinstr =>
    rename_i v
    have heq : instr = .printInt v := Option.some.inj (hInstr.symm.trans hinstr)
    rw [heq] at hSome hMapped
    have hNotFreg : ∀ r, layout v ≠ some (.freg r) := by
      intro r h; simp [verifiedGenInstr, hRC, hII, h] at hSome
    have hVMapped : layout v ≠ none := hMapped v (by simp [TAC.vars])
    have hInstrs : instrs = vLoadVar layout v .x0 ++ [.callPrintI] := by
      simp only [verifiedGenInstr] at hSome
      exact (Option.some.inj hSome).symm
    rw [hInstrs] at hCodeInstr hPcNext
    have hCodeLoad := hCodeInstr.append_left (l2 := [ArmInstr.callPrintI])
    obtain ⟨s1, k1, hSteps1N, hk1, _, hRel1, _, hPC1, hAM1, _⟩ :=
      vLoadVar_exec prog layout v .x0 σ s (pcMap pc)
        hStateRel hRegConv hPcRel hCodeLoad (.inl rfl) hNotFreg hVMapped
    have hCodeCall : prog[s1.pc]? = some .callPrintI := by
      have h := hCodeInstr.append_right (l1 := vLoadVar layout v .x0) 0 (by simp)
      simp at h; rw [hPC1]; exact h
    let s2 := (s1.havocCallerSaved (havocRegsFn s1) (havocFRegsFn s1)).nextPC
    have hStepCallN : ArmStepsN prog s1 s2 1 := ArmStepsN.single (.callPrintI hCodeCall)
    have hChain : ArmStepsN prog s s2 (k1 + 1) := ArmStepsN_trans hSteps1N hStepCallN
    have hNCS : NoCallerSavedLayout layout := hNCSLPrintInt v heq
    have hRel2 : ExtStateRel layout σ s2 :=
      (ExtStateRel.havocCallerSaved_preserved hRel1 hNCS).nextPC
    refine ⟨s2, k1 + 1, hChain, ?_, hRel2, ?_, ?_⟩
    · intro pc' σ' am' _hCfg
      rw [hInstrs, hk1]; simp [List.length_append]
    · show s2.pc = pcMap (pc + 1)
      have hNext := hPcNext _ _ rfl
      simp [s2, ArmState.nextPC, ArmState.havocCallerSaved] at *
      rw [hPC1, hNext]; omega
    · simp [s2, ArmState.nextPC, ArmState.havocCallerSaved, hAM1, hArrayMem]
  | printBool hinstr =>
    rename_i v
    have heq : instr = .printBool v := Option.some.inj (hInstr.symm.trans hinstr)
    rw [heq] at hSome hMapped
    have hNotFreg : ∀ r, layout v ≠ some (.freg r) := by
      intro r h; simp [verifiedGenInstr, hRC, hII, h] at hSome
    have hVMapped : layout v ≠ none := hMapped v (by simp [TAC.vars])
    have hInstrs : instrs = vLoadVar layout v .x0 ++ [.callPrintB] := by
      simp only [verifiedGenInstr] at hSome
      exact (Option.some.inj hSome).symm
    rw [hInstrs] at hCodeInstr hPcNext
    have hCodeLoad := hCodeInstr.append_left (l2 := [ArmInstr.callPrintB])
    obtain ⟨s1, k1, hSteps1N, hk1, _, hRel1, _, hPC1, hAM1, _⟩ :=
      vLoadVar_exec prog layout v .x0 σ s (pcMap pc)
        hStateRel hRegConv hPcRel hCodeLoad (.inl rfl) hNotFreg hVMapped
    have hCodeCall : prog[s1.pc]? = some .callPrintB := by
      have h := hCodeInstr.append_right (l1 := vLoadVar layout v .x0) 0 (by simp)
      simp at h; rw [hPC1]; exact h
    let s2 := (s1.havocCallerSaved (havocRegsFn s1) (havocFRegsFn s1)).nextPC
    have hStepCallN : ArmStepsN prog s1 s2 1 := ArmStepsN.single (.callPrintB hCodeCall)
    have hChain : ArmStepsN prog s s2 (k1 + 1) := ArmStepsN_trans hSteps1N hStepCallN
    have hNCS : NoCallerSavedLayout layout := hNCSLPrintBool v heq
    have hRel2 : ExtStateRel layout σ s2 :=
      (ExtStateRel.havocCallerSaved_preserved hRel1 hNCS).nextPC
    refine ⟨s2, k1 + 1, hChain, ?_, hRel2, ?_, ?_⟩
    · intro pc' σ' am' _hCfg
      rw [hInstrs, hk1]; simp [List.length_append]
    · show s2.pc = pcMap (pc + 1)
      have hNext := hPcNext _ _ rfl
      simp [s2, ArmState.nextPC, ArmState.havocCallerSaved] at *
      rw [hPC1, hNext]; omega
    · simp [s2, ArmState.nextPC, ArmState.havocCallerSaved, hAM1, hArrayMem]
  | printFloat hinstr =>
    rename_i v
    have heq : instr = .printFloat v := Option.some.inj (hInstr.symm.trans hinstr)
    rw [heq] at hSome hMapped
    have hNotIreg : ∀ r, layout v ≠ some (.ireg r) := by
      intro r h; simp [verifiedGenInstr, hRC, hII, h] at hSome
    have hVMapped : layout v ≠ none := hMapped v (by simp [TAC.vars])
    have hInstrs : instrs = vLoadVarFP layout v .d0 ++ [.callPrintF] := by
      simp only [verifiedGenInstr] at hSome
      exact (Option.some.inj hSome).symm
    rw [hInstrs] at hCodeInstr hPcNext
    have hCodeLoad := hCodeInstr.append_left (l2 := [ArmInstr.callPrintF])
    obtain ⟨s1, k1, hSteps1N, hk1, _, hRel1, _, hPC1, hAM1, _, _⟩ :=
      vLoadVarFP_exec prog layout v .d0 σ s (pcMap pc)
        hStateRel hRegConv hPcRel hCodeLoad (.inl rfl) hNotIreg hVMapped
    have hCodeCall : prog[s1.pc]? = some .callPrintF := by
      have h := hCodeInstr.append_right (l1 := vLoadVarFP layout v .d0) 0 (by simp)
      simp at h; rw [hPC1]; exact h
    let s2 := (s1.havocCallerSaved (havocRegsFn s1) (havocFRegsFn s1)).nextPC
    have hStepCallN : ArmStepsN prog s1 s2 1 := ArmStepsN.single (.callPrintF hCodeCall)
    have hChain : ArmStepsN prog s s2 (k1 + 1) := ArmStepsN_trans hSteps1N hStepCallN
    have hNCS : NoCallerSavedLayout layout := hNCSLPrintFloat v heq
    have hRel2 : ExtStateRel layout σ s2 :=
      (ExtStateRel.havocCallerSaved_preserved hRel1 hNCS).nextPC
    refine ⟨s2, k1 + 1, hChain, ?_, hRel2, ?_, ?_⟩
    · intro pc' σ' am' _hCfg
      rw [hInstrs, hk1]; simp [List.length_append]
    · show s2.pc = pcMap (pc + 1)
      have hNext := hPcNext _ _ rfl
      simp [s2, ArmState.nextPC, ArmState.havocCallerSaved] at *
      rw [hPC1, hNext]; omega
    · simp [s2, ArmState.nextPC, ArmState.havocCallerSaved, hAM1, hArrayMem]
  | printString hinstr =>
    rename_i lit
    have heq : instr = .printString lit := Option.some.inj (hInstr.symm.trans hinstr)
    rw [heq] at hSome
    have hInstrs : instrs = [.callPrintS lit] := by
      simp only [verifiedGenInstr, hRC, hII, Bool.not_true, Bool.or_self,
                 Bool.false_eq_true, ↓reduceIte] at hSome
      exact (Option.some.inj hSome).symm
    rw [hInstrs] at hCodeInstr hPcNext
    have hCodeCall : prog[pcMap pc]? = some (.callPrintS lit) := by
      have h := hCodeInstr 0 (by simp); simp at h; exact h
    rw [← hPcRel] at hCodeCall
    let s2 := (s.havocCallerSaved (havocRegsFn s) (havocFRegsFn s)).nextPC
    have hStepN : ArmStepsN prog s s2 1 := ArmStepsN.single (.callPrintS lit hCodeCall)
    have hNCS : NoCallerSavedLayout layout := hNCSLPrintStr lit heq
    have hRel2 : ExtStateRel layout σ s2 :=
      (ExtStateRel.havocCallerSaved_preserved hStateRel hNCS).nextPC
    refine ⟨s2, 1, hStepN, ?_, hRel2, ?_, ?_⟩
    · intro pc' σ' am' _hCfg; rw [hInstrs]; simp
    · show s2.pc = pcMap (pc + 1)
      have hNext := hPcNext _ _ rfl
      simp [s2, ArmState.nextPC, ArmState.havocCallerSaved] at *
      rw [hPcRel, hNext]
    · simp [s2, ArmState.nextPC, ArmState.havocCallerSaved, hArrayMem]
  | const hinstr =>
    rename_i x v
    have heq : instr = .const x v := Option.some.inj (hInstr.symm.trans hinstr)
    rw [heq] at hSome hMapped
    cases v with
    | int n =>
      have hNotFregX : ∀ r, layout x ≠ some (.freg r) := by
        intro r h; have := hSome; simp [verifiedGenInstr, hRC, hII, h] at this
      have hLocXNe : layout x ≠ none := hMapped x (by simp [TAC.vars])
      have hInstrs : instrs = formalLoadImm64 .x0 n ++ vStoreVar layout x .x0 := by
        match hL : layout x with
        | some (.stack _) => simp [verifiedGenInstr, hRC, hII, hL] at hSome; exact hSome.symm
        | some (.ireg _) => simp [verifiedGenInstr, hRC, hII, hL] at hSome; exact hSome.symm
        | some (.freg r) => exact absurd hL (hNotFregX r)
        | none => exact absurd hL hLocXNe
      rw [hInstrs] at hCodeInstr hPcNext
      have hCodeL := hCodeInstr.append_left
      have hCodeR := hCodeInstr.append_right
      obtain ⟨s1, k1, hSteps1N, hk1, hFregs1, hx0, hStack1, hPC1, hRegs1, hAM1⟩ :=
        loadImm64_fregs_preserved prog .x0 n s (pcMap pc) hCodeL hPcRel
      have hRel1 : ExtStateRel layout σ s1 :=
        ExtStateRel.preserved_by_ireg_only hStateRel hRegConv hStack1 hFregs1
          (fun r h0 _ _ => hRegs1 r h0)
      have hx0enc : s1.regs .x0 = (Value.int n).encode := by rw [hx0]; rfl
      obtain ⟨s2, k2, hSteps2N, hk2, hRel2, hPC2, hAM2⟩ :=
        vStoreVar_exec prog layout x (Value.int n) σ s1
          (pcMap pc + (formalLoadImm64 .x0 n).length)
          hRel1 hInjective hRegConv hPC1 hx0enc hCodeR hNotFregX
      have hChain : ArmStepsN prog s s2 (k1 + k2) := ArmStepsN_trans hSteps1N hSteps2N
      refine ⟨s2, k1 + k2, hChain, ?_, hRel2, ?_, ?_⟩
      · intro pc' σ' am' _hCfg
        rw [hInstrs, hk1, hk2]; simp [List.length_append]
      · show s2.pc = pcMap (pc + 1)
        have := hPcNext _ _ rfl; simp at this; rw [hPC2]; omega
      · simp [hAM2, hAM1, hArrayMem]
    | bool b =>
      have hNotFregX : ∀ r, layout x ≠ some (.freg r) := by
        intro r h; have := hSome; simp [verifiedGenInstr, hRC, hII, h] at this
      have hLocXNe : layout x ≠ none := hMapped x (by simp [TAC.vars])
      have hInstrs : instrs = [ArmInstr.mov .x0 (if b then 1 else 0)] ++ vStoreVar layout x .x0 := by
        match hL : layout x with
        | some (.stack _) => simp [verifiedGenInstr, hRC, hII, hL] at hSome; exact hSome.symm
        | some (.ireg _) => simp [verifiedGenInstr, hRC, hII, hL] at hSome; exact hSome.symm
        | some (.freg r) => exact absurd hL (hNotFregX r)
        | none => exact absurd hL hLocXNe
      rw [hInstrs] at hCodeInstr hPcNext
      have hCodeL := hCodeInstr.append_left
      have hCodeR := hCodeInstr.append_right
      have hMov := hCodeL.head; rw [← hPcRel] at hMov
      let s1 := s.setReg .x0 (if b then 1 else 0) |>.nextPC
      have hStep1N : ArmStepsN prog s s1 1 :=
        ArmStepsN.single (.mov .x0 (if b then 1 else 0) hMov)
      have hx0 : s1.regs .x0 = (Value.bool b).encode := by
        simp [s1, ArmState.setReg, ArmState.nextPC, Value.encode]
      have hStack1 : s1.stack = s.stack := by simp [s1]
      have hFregs1 : s1.fregs = s.fregs := by simp [s1]
      have hPC1 : s1.pc = pcMap pc + 1 := by simp [s1, ArmState.nextPC]; exact hPcRel
      have hAM1 : s1.arrayMem = s.arrayMem := by simp [s1]
      have hRegs1 : ∀ r, r ≠ .x0 → s1.regs r = s.regs r := by
        intro r hr; simp [s1, ArmState.setReg, ArmState.nextPC, hr]
      have hRel1 : ExtStateRel layout σ s1 :=
        ExtStateRel.preserved_by_ireg_only hStateRel hRegConv hStack1 hFregs1
          (fun r h0 _ _ => hRegs1 r h0)
      obtain ⟨s2, k2, hSteps2N, hk2, hRel2, hPC2, hAM2⟩ :=
        vStoreVar_exec prog layout x (Value.bool b) σ s1
          (pcMap pc + 1) hRel1 hInjective hRegConv hPC1 hx0
          (by rw [show ([ArmInstr.mov .x0 (if b then (1 : BitVec 64) else 0)]).length = 1 from rfl] at hCodeR
              exact hCodeR)
          hNotFregX
      have hChain : ArmStepsN prog s s2 (1 + k2) := ArmStepsN_trans hStep1N hSteps2N
      refine ⟨s2, 1 + k2, hChain, ?_, hRel2, ?_, ?_⟩
      · intro pc' σ' am' _hCfg
        rw [hInstrs, hk2]; simp [List.length_append]; omega
      · show s2.pc = pcMap (pc + 1)
        have := hPcNext _ _ rfl; simp at this; rw [hPC2]; omega
      · simp [hAM2, hAM1, hArrayMem]
    | float f =>
      have hNotIregX : ∀ r, layout x ≠ some (.ireg r) := by
        intro r h; have := hSome
        simp only [verifiedGenInstr, h] at this
        simp_all
      have hLocXNe : layout x ≠ none := hMapped x (by simp [TAC.vars])
      match hLX : layout x with
      | some (.stack off) =>
        have hInstrs : instrs =
          formalLoadImm64 .x0 f ++ [ArmInstr.fmovToFP .d0 .x0] ++ vStoreVarFP layout x .d0 := by
          simp [verifiedGenInstr, hRC, hII, hLX] at hSome ⊢; exact hSome.symm
        rw [hInstrs] at hCodeInstr hPcNext
        have hCodeLM := hCodeInstr.append_left
        have hCodeR := hCodeInstr.append_right
        have hCodeL := hCodeLM.append_left
        have hCodeM := hCodeLM.append_right
        obtain ⟨s1, k1, hSteps1N, hk1, hFregs1, hx0, hStack1, hPC1, hRegs1, hAM1⟩ :=
          loadImm64_fregs_preserved prog .x0 f s (pcMap pc) hCodeL hPcRel
        have hRel1 : ExtStateRel layout σ s1 :=
          ExtStateRel.preserved_by_ireg_only hStateRel hRegConv hStack1 hFregs1
            (fun r h0 _ _ => hRegs1 r h0)
        have hFmov := hCodeM.head; rw [← hPC1] at hFmov
        let s2 := s1.setFReg .d0 (s1.regs .x0) |>.nextPC
        have hStep2N : ArmStepsN prog s1 s2 1 := ArmStepsN.single (.fmovToFP .d0 .x0 hFmov)
        have hD0 : s2.fregs .d0 = (Value.float f).encode := by
          simp [s2, ArmState.setFReg, ArmState.nextPC, hx0, Value.encode]
        have hPC2' : s2.pc = pcMap pc + ((formalLoadImm64 .x0 f).length + 1) := by
          simp [s2, ArmState.nextPC, hPC1]; omega
        have hAM2 : s2.arrayMem = s1.arrayMem := by simp [s2]
        have hRel2 : ExtStateRel layout σ s2 :=
          (ExtStateRel.setFReg_preserved hRel1 (fun v => hRegConv.not_d0 v)).nextPC
        have hLenLM : (formalLoadImm64 .x0 f ++ [ArmInstr.fmovToFP .d0 .x0]).length =
            (formalLoadImm64 .x0 f).length + 1 := by simp
        rw [hLenLM] at hCodeR
        obtain ⟨s3, k3, hSteps3N, hk3, hRel3, hPC3, hAM3⟩ :=
          vStoreVarFP_exec prog layout x (Value.float f) σ s2
            (pcMap pc + (formalLoadImm64 .x0 f).length + 1)
            hRel2 hInjective hRegConv hPC2' hD0 hCodeR hNotIregX
            (fun r h => by simp [hLX] at h)
        have h12 : ArmStepsN prog s s2 (k1 + 1) := ArmStepsN_trans hSteps1N hStep2N
        have hChain : ArmStepsN prog s s3 (k1 + 1 + k3) := ArmStepsN_trans h12 hSteps3N
        refine ⟨s3, k1 + 1 + k3, hChain, ?_, hRel3, ?_, ?_⟩
        · intro pc' σ' am' _hCfg
          rw [hInstrs, hk1, hk3]; simp [List.length_append]; omega
        · show s3.pc = pcMap (pc + 1)
          have := hPcNext _ _ rfl; simp at this; omega
        · simp [hAM3, hAM2, hAM1, hArrayMem]
      | some (.freg r) =>
        have hInstrs : instrs = formalLoadImm64 .x0 f ++ [ArmInstr.fmovToFP r .x0] := by
          simp [verifiedGenInstr, hRC, hII, hLX, vStoreVarFP] at hSome ⊢
          exact hSome.symm
        rw [hInstrs] at hCodeInstr hPcNext
        have hCodeL := hCodeInstr.append_left
        have hCodeR := hCodeInstr.append_right
        obtain ⟨s1, k1, hSteps1N, hk1, hFregs1, hx0, hStack1, hPC1, hRegs1, hAM1⟩ :=
          loadImm64_fregs_preserved prog .x0 f s (pcMap pc) hCodeL hPcRel
        have hRel1 : ExtStateRel layout σ s1 :=
          ExtStateRel.preserved_by_ireg_only hStateRel hRegConv hStack1 hFregs1
            (fun r h0 _ _ => hRegs1 r h0)
        have hFmov := hCodeR.head; rw [← hPC1] at hFmov
        have hx0enc : s1.regs .x0 = (Value.float f).encode := by rw [hx0]; rfl
        let s2 := (s1.setFReg r (Value.float f).encode).nextPC
        have hS2eq : s2 = (s1.setFReg r (s1.regs .x0)).nextPC := by simp [s2, hx0enc]
        have hStep2N : ArmStepsN prog s1 s2 1 := by
          rw [hS2eq]; exact ArmStepsN.single (.fmovToFP r .x0 hFmov)
        have hPC2 : s2.pc = pcMap pc + ((formalLoadImm64 .x0 f).length + 1) := by
          simp [s2, ArmState.nextPC, hPC1]; omega
        have hAM2 : s2.arrayMem = s1.arrayMem := by simp [s2]
        have hRel2 : ExtStateRel layout (σ[x ↦ Value.float f]) s2 :=
          (ExtStateRel.update_freg hRel1 hInjective hLX).nextPC
        have hChain : ArmStepsN prog s s2 (k1 + 1) := ArmStepsN_trans hSteps1N hStep2N
        refine ⟨s2, k1 + 1, hChain, ?_, hRel2, ?_, ?_⟩
        · intro pc' σ' am' _hCfg
          rw [hInstrs, hk1]; simp [List.length_append]
        · show s2.pc = pcMap (pc + 1)
          have := hPcNext _ _ rfl; simp at this; rw [hPC2]; omega
        · simp [hAM2, hAM1, hArrayMem]
      | some (.ireg r) => exact absurd hLX (hNotIregX r)
      | none => exact absurd hLX hLocXNe
  | copy hinstr =>
    rename_i x y
    have heq : instr = .copy x y := Option.some.inj (hInstr.symm.trans hinstr)
    rw [heq] at hSome hMapped
    by_cases hxy : x = y
    · subst hxy
      have hInstrs : instrs = [.movR .x0 .x0] := by
        simp [verifiedGenInstr, hRC, hII] at hSome; exact hSome.symm
      rw [hInstrs] at hCodeInstr hPcNext
      have hMov := hCodeInstr.head; rw [← hPcRel] at hMov
      let s2 := (s.setReg .x0 (s.regs .x0)).nextPC
      have hStepN : ArmStepsN prog s s2 1 := ArmStepsN.single (.movR .x0 .x0 hMov)
      refine ⟨s2, 1, hStepN, ?_, ?_, ?_, ?_⟩
      · intro pc' σ' am' _hCfg; rw [hInstrs]; simp
      · -- ExtStateRel on σ[x ↦ σ x]: σ[x ↦ σ x] = σ (semantically)
        show ExtStateRel layout (σ[x ↦ σ x]) s2
        intro w loc hw
        have hupd : (σ[x ↦ σ x]) w = σ w := by
          simp only [Store.update]; split <;> simp_all
        rw [hupd]
        match loc with
        | .stack off => simpa [s2, ArmState.nextPC, ArmState.setReg] using hStateRel w (.stack off) hw
        | .ireg r =>
          have hne : r ≠ .x0 := fun h => absurd (h ▸ hw) (hRegConv.not_x0 w)
          simpa [s2, ArmState.nextPC, ArmState.setReg, hne] using hStateRel w (.ireg r) hw
        | .freg r => simpa [s2, ArmState.nextPC, ArmState.setReg] using hStateRel w (.freg r) hw
      · show s2.pc = pcMap (pc + 1)
        have := hPcNext _ _ rfl; simp at this
        simp only [s2, ArmState.nextPC, ArmState.setReg]; rw [hPcRel, ← this]
      · simp [s2, ArmState.nextPC, ArmState.setReg, hArrayMem]
    have hxy_false : (x == y) = false := by simp [hxy]
    by_cases hYFreg : ∃ r, layout y = some (.freg r)
    · obtain ⟨r, hLY⟩ := hYFreg
      have hInstrs : instrs = vStoreVarFP layout x r := by
        simp [verifiedGenInstr, hRC, hII, hLY, if_neg hxy] at hSome; exact hSome.symm
      rw [hInstrs] at hCodeInstr hPcNext
      have hYVal : s.fregs r = (σ y).encode := hStateRel.read_freg hLY
      have hWTi := hWT pc hPC_bound
      have heq_instr := Prog.getElem?_eq_getElem hPC_bound
      rw [hinstr] at heq_instr; rw [← Option.some.inj heq_instr] at hWTi
      have hTyEq : tyCtx x = tyCtx y := match hWTi with | .copy h => h
      have hTyY : tyCtx y = .float := by
        cases h : tyCtx y with
        | float => rfl
        | int => exact absurd hLY (hWTL.1 y r (by rw [h]; decide))
        | bool => exact absurd hLY (hWTL.1 y r (by rw [h]; decide))
      have hNotIregX : ∀ r', layout x ≠ some (.ireg r') :=
        hWTL.float_not_ireg (hTyEq ▸ hTyY)
      match hLX : layout x with
      | some (.stack off) =>
        have hCode : vStoreVarFP layout x r = [.fstr r off] := by simp [vStoreVarFP, hLX]
        rw [hCode] at hCodeInstr hPcNext
        have hFstr := hCodeInstr.head; rw [← hPcRel] at hFstr
        let s2 := (s.setStack off (s.fregs r)).nextPC
        have hStepN : ArmStepsN prog s s2 1 := ArmStepsN.single (.fstr r off hFstr)
        refine ⟨s2, 1, hStepN, ?_, ?_, ?_, ?_⟩
        · intro pc' σ' am' _hCfg; rw [hInstrs, hCode]; simp
        · show ExtStateRel layout (σ[x ↦ σ y]) s2
          have heqSt : s2 = (s.setStack off ((σ y).encode)).nextPC := by
            simp [s2, hYVal]
          rw [heqSt]
          exact (ExtStateRel.update_stack hStateRel hInjective hLX).nextPC
        · show s2.pc = pcMap (pc + 1)
          have := hPcNext _ _ rfl; simp at this
          simp only [s2, ArmState.nextPC, ArmState.setStack]; rw [hPcRel, ← this]
        · simp [s2, ArmState.nextPC, ArmState.setStack, hArrayMem]
      | some (.freg r') =>
        by_cases hrr : r' = r
        · have hCode : vStoreVarFP layout x r = [] := by simp [vStoreVarFP, hLX, hrr]
          rw [hCode] at hCodeInstr hPcNext
          have hxy_same : x = y := hInjective x y (.freg r) (hrr ▸ hLX) hLY
          rw [hxy_same]
          refine ⟨s, 0, ArmStepsN.refl_zero, ?_, ?_, ?_, ?_⟩
          · intro pc' σ' am' _hCfg; rw [hInstrs, hCode]; simp
          · show ExtStateRel layout (σ[y ↦ σ y]) s
            intro w loc hw
            have hupd : (σ[y ↦ σ y]) w = σ w := by
              simp only [Store.update]; split <;> simp_all
            rw [hupd]; exact hStateRel w loc hw
          · show s.pc = pcMap (pc + 1)
            have := hPcNext _ _ rfl; simp at this; rw [hPcRel]; exact this.symm
          · exact hArrayMem
        · have hne : (r' == r) = false := by simp [hrr]
          simp only [vStoreVarFP, hLX, hne] at hCodeInstr hPcNext
          have hFmov := hCodeInstr.head; rw [← hPcRel] at hFmov
          let s2 := (s.setFReg r' (s.fregs r)).nextPC
          have hStepN : ArmStepsN prog s s2 1 := ArmStepsN.single (.fmovRR r' r hFmov)
          refine ⟨s2, 1, hStepN, ?_, ?_, ?_, ?_⟩
          · intro pc' σ' am' _hCfg
            rw [hInstrs]; simp [vStoreVarFP, hLX, hne]
          · show ExtStateRel layout (σ[x ↦ σ y]) s2
            have heqSt : s2 = (s.setFReg r' (σ y).encode).nextPC := by simp [s2, hYVal]
            rw [heqSt]
            exact (ExtStateRel.update_freg hStateRel hInjective hLX).nextPC
          · show s2.pc = pcMap (pc + 1)
            have := hPcNext _ _ rfl; simp at this
            simp only [s2, ArmState.nextPC, ArmState.setFReg]; rw [hPcRel, ← this]
          · simp [s2, ArmState.nextPC, ArmState.setFReg, hArrayMem]
      | some (.ireg r') => exact absurd hLX (hNotIregX r')
      | none =>
        have hCode : vStoreVarFP layout x r = [] := by simp [vStoreVarFP, hLX]
        rw [hCode] at hCodeInstr hPcNext
        refine ⟨s, 0, ArmStepsN.refl_zero, ?_, ?_, ?_, ?_⟩
        · intro pc' σ' am' _hCfg; rw [hInstrs, hCode]; simp
        · show ExtStateRel layout (σ[x ↦ σ y]) s
          intro w loc hw
          have hne : w ≠ x := fun h => by rw [h] at hw; simp [hLX] at hw
          rw [Store.update_other _ _ _ _ hne]; exact hStateRel w loc hw
        · show s.pc = pcMap (pc + 1)
          have := hPcNext _ _ rfl; simp at this; rw [hPcRel]; exact this.symm
        · exact hArrayMem
    · have hNotFregY : ∀ r, layout y ≠ some (.freg r) := fun r h => hYFreg ⟨r, h⟩
      by_cases hXFreg : ∃ r, layout x = some (.freg r)
      · obtain ⟨rf, hLX⟩ := hXFreg
        have hInstrs : instrs = vLoadVar layout y .x0 ++ [.fmovToFP rf .x0] := by
          match hLY : layout y with
          | some (.freg r) => exact absurd hLY (hNotFregY r)
          | some (.stack _) | some (.ireg _) | none =>
            have := hSome; simp [verifiedGenInstr, hRC, hII, hLY, hLX, if_neg hxy] at this
            exact this.symm
        rw [hInstrs] at hCodeInstr hPcNext
        have hCodeL := hCodeInstr.append_left
        have hCodeR := hCodeInstr.append_right
        obtain ⟨s1, k1, hSteps1N, hk1, hX0_1, hRel1, hFregs1, hPC1, hAM1, _⟩ :=
          vLoadVar_exec prog layout y .x0 σ s (pcMap pc) hStateRel hRegConv hPcRel hCodeL
            (Or.inl rfl) hNotFregY (hMapped y (by simp [TAC.vars]))
        have hFmov := hCodeR.head; rw [← hPC1] at hFmov
        let s2 := (s1.setFReg rf (s1.regs .x0)).nextPC
        have hStep2N : ArmStepsN prog s1 s2 1 := ArmStepsN.single (.fmovToFP rf .x0 hFmov)
        have hS2eq : s2 = (s1.setFReg rf (σ y).encode).nextPC := by simp [s2, hX0_1]
        have hChain : ArmStepsN prog s s2 (k1 + 1) := ArmStepsN_trans hSteps1N hStep2N
        refine ⟨s2, k1 + 1, hChain, ?_, ?_, ?_, ?_⟩
        · intro pc' σ' am' _hCfg; rw [hInstrs, hk1]; simp [List.length_append]
        · show ExtStateRel layout (σ[x ↦ σ y]) s2
          rw [hS2eq]; exact (ExtStateRel.update_freg hRel1 hInjective hLX).nextPC
        · show s2.pc = pcMap (pc + 1)
          have := hPcNext _ _ rfl; simp at this
          simp only [s2, ArmState.nextPC, ArmState.setFReg]; rw [hPC1, this]; omega
        · simp [s2, ArmState.nextPC, ArmState.setFReg, hAM1, hArrayMem]
      · have hNotFregX : ∀ r, layout x ≠ some (.freg r) := fun r h => hXFreg ⟨r, h⟩
        have hInstrs : instrs = vLoadVar layout y .x0 ++ vStoreVar layout x .x0 := by
          match hLY : layout y with
          | some (.freg r) => exact absurd hLY (hNotFregY r)
          | some (.stack _) | some (.ireg _) | none =>
            match hLX' : layout x with
            | some (.freg r) => exact absurd hLX' (hNotFregX r)
            | some (.stack _) | some (.ireg _) | none =>
              have := hSome; simp [verifiedGenInstr, hRC, hII, hLY, hLX', if_neg hxy] at this
              exact this.symm
        rw [hInstrs] at hCodeInstr hPcNext
        have hCodeL := hCodeInstr.append_left
        have hCodeR := hCodeInstr.append_right
        obtain ⟨s1, k1, hSteps1N, hk1, hX0_1, hRel1, hFregs1, hPC1, hAM1, _⟩ :=
          vLoadVar_exec prog layout y .x0 σ s (pcMap pc) hStateRel hRegConv hPcRel hCodeL
            (Or.inl rfl) hNotFregY (hMapped y (by simp [TAC.vars]))
        obtain ⟨s2, k2, hSteps2N, hk2, hRel2, hPC2, hAM2⟩ :=
          vStoreVar_exec prog layout x (σ y) σ s1 (pcMap pc + (vLoadVar layout y .x0).length)
            hRel1 hInjective hRegConv hPC1 hX0_1 hCodeR hNotFregX
        have hChain : ArmStepsN prog s s2 (k1 + k2) := ArmStepsN_trans hSteps1N hSteps2N
        refine ⟨s2, k1 + k2, hChain, ?_, hRel2, ?_, ?_⟩
        · intro pc' σ' am' _hCfg
          rw [hInstrs, hk1, hk2]; simp [List.length_append]
        · show s2.pc = pcMap (pc + 1)
          have := hPcNext _ _ rfl; simp at this; rw [hPC2]; omega
        · simp [hAM2, hAM1, hArrayMem]
  | binop hinstr hy hz hs =>
    rename_i x op y z a b
    have heq : instr = .binop x op y z := Option.some.inj (hInstr.symm.trans hinstr)
    rw [heq] at hSome hMapped
    have hNotFregY : ∀ r, layout y ≠ some (.freg r) := by
      intro r h; have := hSome; simp [verifiedGenInstr, hRC, hII, h] at this
    have hNotFregZ : ∀ r, layout z ≠ some (.freg r) := by
      intro r h; have := hSome; simp [verifiedGenInstr, hRC, hII, h] at this
    have hNotFregX : ∀ r, layout x ≠ some (.freg r) := by
      intro r h; have := hSome; simp [verifiedGenInstr, hRC, hII, h] at this
    let lv_reg := match layout y with | some (.ireg r) => r | _ => ArmReg.x1
    let rv_reg := match layout z with | some (.ireg r) => r | _ => ArmReg.x2
    let dst_reg := match layout x with | some (.ireg r) => r | _ => ArmReg.x0
    suffices hSimple : ∀ (armOp : ArmInstr),
        instrs = vLoadVar layout y lv_reg ++
          (vLoadVar layout z rv_reg ++ (armOp :: vStoreVar layout x dst_reg)) →
        (∀ s', prog[s'.pc]? = some armOp →
          ArmStep prog s' (s'.setReg dst_reg (op.eval (s'.regs lv_reg) (s'.regs rv_reg)) |>.nextPC)) →
        ∃ s' k, ArmStepsN prog s s' k ∧
          (∀ pc' σ' am', (.run (pc + 1) (σ[x ↦ .int (op.eval a b)]) am : Cfg) = .run pc' σ' am' → k = instrs.length) ∧
          ExtSimRel layout pcMap divLabel boundsLabel
            (.run (pc + 1) (σ[x ↦ .int (op.eval a b)]) am) s' by
      cases op with
      | add =>
        apply hSimple
        · have := hSome; simp [verifiedGenInstr, hRC, hII] at this; exact this.symm
        · exact fun _ h => .addR dst_reg lv_reg rv_reg h
      | sub =>
        apply hSimple
        · have := hSome; simp [verifiedGenInstr, hRC, hII] at this; exact this.symm
        · exact fun _ h => .subR dst_reg lv_reg rv_reg h
      | mul =>
        apply hSimple
        · have := hSome; simp [verifiedGenInstr, hRC, hII] at this; exact this.symm
        · exact fun _ h => .mulR dst_reg lv_reg rv_reg h
      | band =>
        apply hSimple
        · have := hSome; simp [verifiedGenInstr, hRC, hII] at this; exact this.symm
        · exact fun _ h => .andR dst_reg lv_reg rv_reg h
      | bor =>
        apply hSimple
        · have := hSome; simp [verifiedGenInstr, hRC, hII] at this; exact this.symm
        · exact fun _ h => .orrR dst_reg lv_reg rv_reg h
      | bxor =>
        apply hSimple
        · have := hSome; simp [verifiedGenInstr, hRC, hII] at this; exact this.symm
        · exact fun _ h => .eorR dst_reg lv_reg rv_reg h
      | shl =>
        apply hSimple
        · have := hSome; simp [verifiedGenInstr, hRC, hII] at this; exact this.symm
        · exact fun _ h => .lslR dst_reg lv_reg rv_reg h
      | shr =>
        apply hSimple
        · have := hSome; simp [verifiedGenInstr, hRC, hII] at this; exact this.symm
        · exact fun _ h => .asrR dst_reg lv_reg rv_reg h
      | div =>
        have hInstrs : instrs = vLoadVar layout y lv_reg ++
            (vLoadVar layout z rv_reg ++
            (.cbz rv_reg divLabel :: .sdivR dst_reg lv_reg rv_reg ::
             vStoreVar layout x dst_reg)) := by
          have := hSome; simp [verifiedGenInstr, hRC, hII] at this; exact this.symm
        rw [hInstrs] at hCodeInstr hPcNext
        have hCodeA := hCodeInstr.append_left
        have hCodeBcDE := hCodeInstr.append_right
        have hCodeB := hCodeBcDE.append_left
        have hCodecDE := hCodeBcDE.append_right
        obtain ⟨s1, k1, hSteps1N, hk1, hLV_1, hRel1, _, hPC1, hAM1, hRegs1⟩ :=
          vLoadVar_eff_exec prog layout y σ s (pcMap pc) .x1 hStateRel hRegConv hPcRel
            hNotFregY (Or.inr (Or.inl rfl)) (hMapped y (by simp [TAC.vars])) hCodeA
        have hk1' : k1 = (vLoadVar layout y lv_reg).length := hk1
        obtain ⟨s2, k2, hSteps2N, hk2, hRV_2, hRel2, _, hPC2_, hAM2, hRegs2⟩ :=
          vLoadVar_eff_exec prog layout z σ s1
            (pcMap pc + (vLoadVar layout y lv_reg).length) .x2
            hRel1 hRegConv hPC1 hNotFregZ (Or.inr (Or.inr rfl)) (hMapped z (by simp [TAC.vars])) hCodeB
        have hk2' : k2 = (vLoadVar layout z rv_reg).length := hk2
        have hPC2 : s2.pc = pcMap pc + (vLoadVar layout y lv_reg).length +
            (vLoadVar layout z rv_reg).length := hPC2_
        have hLV_2 : s2.regs lv_reg = a := by
          match hLY : layout y with
          | some (.ireg r) =>
            have hlv : lv_reg = r := by
              show (match layout y with | some (.ireg r) => r | _ => .x1) = r; simp [hLY]
            rw [hlv, hRel2.read_ireg hLY, hy]; simp [Value.encode]
          | some (.stack _) | none =>
            have hlv : lv_reg = .x1 := by
              show (match layout y with | some (.ireg r) => r | _ => .x1) = .x1; simp [hLY]
            rw [hlv]
            have hne : ArmReg.x1 ≠ rv_reg := by
              intro h
              match hLZ : layout z with
              | some (.ireg rz) =>
                have hrv : rv_reg = rz := by
                  show (match layout z with | some (.ireg r) => r | _ => .x2) = rz; simp [hLZ]
                rw [hrv] at h; exact hRegConv.not_x1 z (h ▸ hLZ)
              | some (.stack _) | none =>
                have hrv : rv_reg = .x2 := by
                  show (match layout z with | some (.ireg r) => r | _ => .x2) = .x2; simp [hLZ]
                rw [hrv] at h; exact absurd h (by decide)
              | some (.freg r) => exact absurd hLZ (hNotFregZ r)
            rw [hRegs2 .x1 hne, ← hlv, hLV_1, hy]; simp [Value.encode]
          | some (.freg r) => exact absurd hLY (hNotFregY r)
        have hRV_eq : s2.regs rv_reg = b := by rw [hRV_2, hz]; simp [Value.encode]
        have hb_ne0 : b ≠ 0 := by unfold BinOp.safe at hs; exact hs
        have hRV_ne0 : s2.regs rv_reg ≠ (0 : BitVec 64) := by rw [hRV_eq]; exact hb_ne0
        have hCbz := hCodecDE.head; rw [← hPC2_] at hCbz
        have hStepCbzN : ArmStepsN prog s2 s2.nextPC 1 :=
          ArmStepsN.single (.cbz_fall rv_reg divLabel hCbz hRV_ne0)
        have hPC_cbz : s2.nextPC.pc = pcMap pc + (vLoadVar layout y lv_reg).length +
            (vLoadVar layout z rv_reg).length + 1 := by
          show s2.pc + 1 = _; omega
        have hLV_cbz : s2.nextPC.regs lv_reg = a := by simp [ArmState.nextPC]; exact hLV_2
        have hRV_cbz : s2.nextPC.regs rv_reg = b := by simp [ArmState.nextPC]; exact hRV_eq
        have hRel_cbz : ExtStateRel layout σ s2.nextPC := hRel2.nextPC
        have hAM_cbz : s2.nextPC.arrayMem = s2.arrayMem := by simp [ArmState.nextPC]
        have hSdiv := hCodecDE.tail.head; rw [← hPC_cbz] at hSdiv
        have hStepSdivN : ArmStepsN prog s2.nextPC
            (s2.nextPC.setReg dst_reg (BitVec.sdiv (s2.nextPC.regs lv_reg) (s2.nextPC.regs rv_reg))).nextPC 1 :=
          ArmStepsN.single (.sdivR dst_reg lv_reg rv_reg hSdiv)
        have hSdivEq : (s2.nextPC.setReg dst_reg (BitVec.sdiv (s2.nextPC.regs lv_reg) (s2.nextPC.regs rv_reg))).nextPC =
            (s2.nextPC.setReg dst_reg (BinOp.eval .div a b)).nextPC := by
          rw [hLV_cbz, hRV_cbz]; rfl
        rw [hSdivEq] at hStepSdivN
        let s3 := (s2.nextPC.setReg dst_reg (BinOp.eval .div a b)).nextPC
        have hPC3 : s3.pc = pcMap pc + (vLoadVar layout y lv_reg).length +
            (vLoadVar layout z rv_reg).length + 2 := by show s2.nextPC.pc + 1 = _; omega
        have hAM3 : s3.arrayMem = s2.arrayMem := by simp [s3, ArmState.nextPC, ArmState.setReg]
        by_cases hXIR : ∃ r, layout x = some (.ireg r)
        · obtain ⟨r_dst, hDst⟩ := hXIR
          have hDR : dst_reg = r_dst := by
            change (match layout x with | some (.ireg r) => r | _ => .x0) = r_dst; rw [hDst]
          have hStore : vStoreVar layout x dst_reg = [] := by simp [vStoreVar, hDst, hDR]
          have hRel4 : ExtStateRel layout (σ[x ↦ .int (BinOp.eval .div a b)]) s3 := by
            show ExtStateRel layout (σ[x ↦ .int (BinOp.eval .div a b)])
              (s2.nextPC.setReg dst_reg (BinOp.eval .div a b)).nextPC
            rw [hDR, show BinOp.eval .div a b = (Value.int (BinOp.eval .div a b)).encode from by simp [Value.encode]]
            exact (ExtStateRel.update_ireg hRel_cbz hInjective hDst).nextPC
          have h12 : ArmStepsN prog s s2 (k1 + k2) := ArmStepsN_trans hSteps1N hSteps2N
          have h123 : ArmStepsN prog s s2.nextPC (k1 + k2 + 1) := ArmStepsN_trans h12 hStepCbzN
          have hChain : ArmStepsN prog s s3 (k1 + k2 + 1 + 1) := ArmStepsN_trans h123 hStepSdivN
          refine ⟨s3, k1 + k2 + 1 + 1, hChain, ?_, hRel4, ?_, ?_⟩
          · intro pc' σ' am' _hCfg
            rw [hInstrs, hk1', hk2', hStore]; simp [List.length_append]; omega
          · show s3.pc = pcMap (pc + 1)
            have := hPcNext _ _ rfl; simp [hStore] at this; omega
          · simp [hAM3, hAM2, hAM1, hArrayMem]
        · have hDR : dst_reg = .x0 := by
            change (match layout x with | some (.ireg r) => r | _ => .x0) = .x0
            split
            · next r h => exact absurd ⟨r, h⟩ hXIR
            · rfl
          have hRel3 : ExtStateRel layout σ s3 := by
            show ExtStateRel layout σ (s2.nextPC.setReg dst_reg (BinOp.eval .div a b)).nextPC
            rw [hDR]; exact (ExtStateRel.setReg_preserved hRel_cbz (fun w => hRegConv.not_x0 w)).nextPC
          have hVal3 : s3.regs .x0 = (Value.int (BinOp.eval .div a b)).encode := by
            simp [s3, hDR, ArmState.setReg, ArmState.nextPC, Value.encode]
          have hCodeStore : CodeAt prog
              (pcMap pc + (vLoadVar layout y lv_reg).length + (vLoadVar layout z rv_reg).length + 2)
              (vStoreVar layout x .x0) := by
            rw [← hDR]; exact hCodecDE.tail.tail
          obtain ⟨s4, k4, hSteps4N, hk4, hRel4, hPC4, hAM4⟩ :=
            vStoreVar_exec prog layout x (Value.int (BinOp.eval .div a b)) σ s3
              (pcMap pc + (vLoadVar layout y lv_reg).length + (vLoadVar layout z rv_reg).length + 2)
              hRel3 hInjective hRegConv hPC3 hVal3 hCodeStore hNotFregX
          have hk4' : k4 = (vStoreVar layout x dst_reg).length := by rw [hDR]; exact hk4
          have h12 : ArmStepsN prog s s2 (k1 + k2) := ArmStepsN_trans hSteps1N hSteps2N
          have h123 : ArmStepsN prog s s2.nextPC (k1 + k2 + 1) := ArmStepsN_trans h12 hStepCbzN
          have h1234 : ArmStepsN prog s s3 (k1 + k2 + 1 + 1) := ArmStepsN_trans h123 hStepSdivN
          have hChain : ArmStepsN prog s s4 (k1 + k2 + 1 + 1 + k4) := ArmStepsN_trans h1234 hSteps4N
          refine ⟨s4, k1 + k2 + 1 + 1 + k4, hChain, ?_, hRel4, ?_, ?_⟩
          · intro pc' σ' am' _hCfg
            rw [hInstrs, hk1', hk2', hk4']; simp [List.length_append]; omega
          · show s4.pc = pcMap (pc + 1)
            have := hPcNext _ _ rfl; rw [show dst_reg = ArmReg.x0 from hDR] at this; simp at this; omega
          · simp [hAM4, hAM3, hAM2, hAM1, hArrayMem]
      | mod =>
        have hInstrs : instrs = vLoadVar layout y lv_reg ++
            (vLoadVar layout z rv_reg ++
            (.cbz rv_reg divLabel :: .sdivR .x0 lv_reg rv_reg :: .mulR .x0 .x0 rv_reg ::
             .subR dst_reg lv_reg .x0 :: vStoreVar layout x dst_reg)) := by
          have := hSome; simp [verifiedGenInstr, hRC, hII] at this; exact this.symm
        rw [hInstrs] at hCodeInstr hPcNext
        have hCodeA := hCodeInstr.append_left
        have hCodeBcDE := hCodeInstr.append_right
        have hCodeB := hCodeBcDE.append_left
        have hCodecDE := hCodeBcDE.append_right
        obtain ⟨s1, k1, hSteps1N, hk1, hLV_1, hRel1, _, hPC1, hAM1, hRegs1⟩ :=
          vLoadVar_eff_exec prog layout y σ s (pcMap pc) .x1 hStateRel hRegConv hPcRel
            hNotFregY (Or.inr (Or.inl rfl)) (hMapped y (by simp [TAC.vars])) hCodeA
        have hk1' : k1 = (vLoadVar layout y lv_reg).length := hk1
        obtain ⟨s2, k2, hSteps2N, hk2, hRV_2, hRel2, _, hPC2_, hAM2, hRegs2⟩ :=
          vLoadVar_eff_exec prog layout z σ s1
            (pcMap pc + (vLoadVar layout y lv_reg).length) .x2
            hRel1 hRegConv hPC1 hNotFregZ (Or.inr (Or.inr rfl)) (hMapped z (by simp [TAC.vars])) hCodeB
        have hk2' : k2 = (vLoadVar layout z rv_reg).length := hk2
        have hPC2 : s2.pc = pcMap pc + (vLoadVar layout y lv_reg).length +
            (vLoadVar layout z rv_reg).length := hPC2_
        have hLV_2 : s2.regs lv_reg = a := by
          match hLY : layout y with
          | some (.ireg r) =>
            have hlv : lv_reg = r := by
              show (match layout y with | some (.ireg r) => r | _ => .x1) = r; simp [hLY]
            rw [hlv, hRel2.read_ireg hLY, hy]; simp [Value.encode]
          | some (.stack _) | none =>
            have hlv : lv_reg = .x1 := by
              show (match layout y with | some (.ireg r) => r | _ => .x1) = .x1; simp [hLY]
            rw [hlv]
            have hne : ArmReg.x1 ≠ rv_reg := by
              intro h
              match hLZ : layout z with
              | some (.ireg rz) =>
                have hrv : rv_reg = rz := by
                  show (match layout z with | some (.ireg r) => r | _ => .x2) = rz; simp [hLZ]
                rw [hrv] at h; exact hRegConv.not_x1 z (h ▸ hLZ)
              | some (.stack _) | none =>
                have hrv : rv_reg = .x2 := by
                  show (match layout z with | some (.ireg r) => r | _ => .x2) = .x2; simp [hLZ]
                rw [hrv] at h; exact absurd h (by decide)
              | some (.freg r) => exact absurd hLZ (hNotFregZ r)
            rw [hRegs2 .x1 hne, ← hlv, hLV_1, hy]; simp [Value.encode]
          | some (.freg r) => exact absurd hLY (hNotFregY r)
        have hRV_eq : s2.regs rv_reg = b := by rw [hRV_2, hz]; simp [Value.encode]
        have hb_ne0 : b ≠ 0 := by unfold BinOp.safe at hs; exact hs
        have hRV_ne0 : s2.regs rv_reg ≠ (0 : BitVec 64) := by rw [hRV_eq]; exact hb_ne0
        have hCbz := hCodecDE.head; rw [← hPC2_] at hCbz
        have hStepCbzN : ArmStepsN prog s2 s2.nextPC 1 :=
          ArmStepsN.single (.cbz_fall rv_reg divLabel hCbz hRV_ne0)
        have hPC_cbz : s2.nextPC.pc = pcMap pc + (vLoadVar layout y lv_reg).length +
            (vLoadVar layout z rv_reg).length + 1 := by show s2.pc + 1 = _; omega
        have hLV_cbz : s2.nextPC.regs lv_reg = a := by simp [ArmState.nextPC]; exact hLV_2
        have hRV_cbz : s2.nextPC.regs rv_reg = b := by simp [ArmState.nextPC]; exact hRV_eq
        have hRel_cbz : ExtStateRel layout σ s2.nextPC := hRel2.nextPC
        have hAM_cbz : s2.nextPC.arrayMem = s2.arrayMem := by simp [ArmState.nextPC]
        have hSdiv := hCodecDE.tail.head; rw [← hPC_cbz] at hSdiv
        let q := BitVec.sdiv a b
        have hStepSdivN : ArmStepsN prog s2.nextPC (s2.nextPC.setReg .x0 q).nextPC 1 := by
          have h := ArmStepsN.single (prog := prog) (.sdivR .x0 lv_reg rv_reg hSdiv)
          rwa [hLV_cbz, hRV_cbz] at h
        let s_q := (s2.nextPC.setReg .x0 q).nextPC
        have hPC_q : s_q.pc = pcMap pc + (vLoadVar layout y lv_reg).length +
            (vLoadVar layout z rv_reg).length + 2 := by show s2.nextPC.pc + 1 = _; omega
        have hLV_ne_x0 : lv_reg ≠ .x0 := by
          intro h
          match hLY : layout y with
          | some (.ireg r) =>
            have : lv_reg = r := by
              show (match layout y with | some (.ireg r) => r | _ => .x1) = r; simp [hLY]
            rw [this] at h; rw [h] at hLY; exact absurd hLY (hRegConv.not_x0 y)
          | some (.stack _) | none =>
            have : lv_reg = .x1 := by
              show (match layout y with | some (.ireg r) => r | _ => .x1) = .x1; simp [hLY]
            rw [this] at h; exact absurd h (by decide)
          | some (.freg r) => exact absurd hLY (hNotFregY r)
        have hRV_ne_x0 : rv_reg ≠ .x0 := by
          intro h
          match hLZ : layout z with
          | some (.ireg r) =>
            have : rv_reg = r := by
              show (match layout z with | some (.ireg r) => r | _ => .x2) = r; simp [hLZ]
            rw [this] at h; rw [h] at hLZ; exact absurd hLZ (hRegConv.not_x0 z)
          | some (.stack _) | none =>
            have : rv_reg = .x2 := by
              show (match layout z with | some (.ireg r) => r | _ => .x2) = .x2; simp [hLZ]
            rw [this] at h; exact absurd h (by decide)
          | some (.freg r) => exact absurd hLZ (hNotFregZ r)
        have hLV_q : s_q.regs lv_reg = a := by
          show (s2.nextPC.setReg .x0 q).nextPC.regs lv_reg = a
          rw [ArmState.nextPC_regs, ArmState.setReg_regs_other _ _ _ _ hLV_ne_x0,
              ArmState.nextPC_regs]; exact hLV_2
        have hRV_q : s_q.regs rv_reg = b := by
          show (s2.nextPC.setReg .x0 q).nextPC.regs rv_reg = b
          rw [ArmState.nextPC_regs, ArmState.setReg_regs_other _ _ _ _ hRV_ne_x0,
              ArmState.nextPC_regs]; exact hRV_eq
        have hMul := hCodecDE.tail.tail.head; rw [← hPC_q] at hMul
        have hStepMulN : ArmStepsN prog s_q
            (s_q.setReg .x0 (s_q.regs .x0 * s_q.regs rv_reg)).nextPC 1 :=
          ArmStepsN.single (.mulR .x0 .x0 rv_reg hMul)
        have hx0_q : s_q.regs .x0 = q := by
          show (s2.nextPC.setReg .x0 q).nextPC.regs .x0 = q
          simp [ArmState.nextPC_regs, ArmState.setReg_regs_same]
        let s_qb := (s_q.setReg .x0 (q * b)).nextPC
        have hMulEq : (s_q.setReg .x0 (s_q.regs .x0 * s_q.regs rv_reg)).nextPC = s_qb := by
          rw [hx0_q, hRV_q]
        rw [hMulEq] at hStepMulN
        have hPC_qb : s_qb.pc = pcMap pc + (vLoadVar layout y lv_reg).length +
            (vLoadVar layout z rv_reg).length + 3 := by show s_q.pc + 1 = _; omega
        have hLV_qb : s_qb.regs lv_reg = a := by
          show (s_q.setReg .x0 (q * b)).nextPC.regs lv_reg = a
          rw [ArmState.nextPC_regs, ArmState.setReg_regs_other _ _ _ _ hLV_ne_x0]
          exact hLV_q
        have hx0_qb : s_qb.regs .x0 = q * b := by
          show (s_q.setReg .x0 (q * b)).nextPC.regs .x0 = q * b
          simp [ArmState.nextPC_regs, ArmState.setReg_regs_same]
        have hSub := hCodecDE.tail.tail.tail.head; rw [← hPC_qb] at hSub
        have hStepSubN : ArmStepsN prog s_qb
            (s_qb.setReg dst_reg (s_qb.regs lv_reg - s_qb.regs .x0)).nextPC 1 :=
          ArmStepsN.single (.subR dst_reg lv_reg .x0 hSub)
        have hModEq : a - q * b = BinOp.eval .mod a b := by
          simp [BinOp.eval, q]; exact BitVec.srem_eq_sub_sdiv_mul a b
        let s5 := (s_qb.setReg dst_reg (BinOp.eval .mod a b)).nextPC
        have hSubEq : (s_qb.setReg dst_reg (s_qb.regs lv_reg - s_qb.regs .x0)).nextPC = s5 := by
          rw [hLV_qb, hx0_qb, hModEq]
        rw [hSubEq] at hStepSubN
        have hPC5 : s5.pc = pcMap pc + (vLoadVar layout y lv_reg).length +
            (vLoadVar layout z rv_reg).length + 4 := by show s_qb.pc + 1 = _; omega
        have hAM5 : s5.arrayMem = s2.arrayMem := by
          show (s_qb.setReg dst_reg (BinOp.eval .mod a b)).nextPC.arrayMem = s2.arrayMem
          simp [ArmState.nextPC_arrayMem, ArmState.setReg_arrayMem]
          show (s_q.setReg .x0 (q * b)).nextPC.arrayMem = s2.arrayMem
          simp [ArmState.nextPC_arrayMem, ArmState.setReg_arrayMem]
          show (s2.nextPC.setReg .x0 q).nextPC.arrayMem = s2.arrayMem
          simp [ArmState.nextPC_arrayMem, ArmState.setReg_arrayMem]
        by_cases hXIR : ∃ r, layout x = some (.ireg r)
        · obtain ⟨r_dst, hDst⟩ := hXIR
          have hDR : dst_reg = r_dst := by
            change (match layout x with | some (.ireg r) => r | _ => .x0) = r_dst; rw [hDst]
          have hStore : vStoreVar layout x dst_reg = [] := by simp [vStoreVar, hDst, hDR]
          have hRel_cbz_s : ExtStateRel layout σ s2.nextPC := hRel2.nextPC
          have hRelQ : ExtStateRel layout σ s_q :=
            (ExtStateRel.setReg_preserved hRel_cbz_s (fun w => hRegConv.not_x0 w)).nextPC
          have hRelQB : ExtStateRel layout σ s_qb :=
            (ExtStateRel.setReg_preserved hRelQ (fun w => hRegConv.not_x0 w)).nextPC
          have hRel5 : ExtStateRel layout (σ[x ↦ .int (BinOp.eval .mod a b)]) s5 := by
            show ExtStateRel layout (σ[x ↦ .int (BinOp.eval .mod a b)])
              (s_qb.setReg dst_reg (BinOp.eval .mod a b)).nextPC
            rw [hDR, show BinOp.eval .mod a b = (Value.int (BinOp.eval .mod a b)).encode from by simp [Value.encode]]
            exact (ExtStateRel.update_ireg hRelQB hInjective hDst).nextPC
          have h12 : ArmStepsN prog s s2 (k1 + k2) := ArmStepsN_trans hSteps1N hSteps2N
          have h123 : ArmStepsN prog s s2.nextPC (k1 + k2 + 1) := ArmStepsN_trans h12 hStepCbzN
          have h1234 : ArmStepsN prog s s_q (k1 + k2 + 1 + 1) := ArmStepsN_trans h123 hStepSdivN
          have h12345 : ArmStepsN prog s s_qb (k1 + k2 + 1 + 1 + 1) := ArmStepsN_trans h1234 hStepMulN
          have hChain : ArmStepsN prog s s5 (k1 + k2 + 1 + 1 + 1 + 1) := ArmStepsN_trans h12345 hStepSubN
          refine ⟨s5, k1 + k2 + 1 + 1 + 1 + 1, hChain, ?_, hRel5, ?_, ?_⟩
          · intro pc' σ' am' _hCfg
            rw [hInstrs, hk1', hk2', hStore]; simp [List.length_append]; omega
          · show s5.pc = pcMap (pc + 1)
            have := hPcNext _ _ rfl; simp [hStore] at this; omega
          · simp [hAM5, hAM2, hAM1, hArrayMem]
        · have hDR : dst_reg = .x0 := by
            change (match layout x with | some (.ireg r) => r | _ => .x0) = .x0
            split
            · next r h => exact absurd ⟨r, h⟩ hXIR
            · rfl
          have hRelQ : ExtStateRel layout σ s_q :=
            (ExtStateRel.setReg_preserved hRel2.nextPC (fun w => hRegConv.not_x0 w)).nextPC
          have hRelQB : ExtStateRel layout σ s_qb :=
            (ExtStateRel.setReg_preserved hRelQ (fun w => hRegConv.not_x0 w)).nextPC
          have hRel5 : ExtStateRel layout σ s5 := by
            show ExtStateRel layout σ (s_qb.setReg dst_reg (BinOp.eval .mod a b)).nextPC
            rw [hDR]; exact (ExtStateRel.setReg_preserved hRelQB (fun w => hRegConv.not_x0 w)).nextPC
          have hVal5 : s5.regs .x0 = (Value.int (BinOp.eval .mod a b)).encode := by
            show (s_qb.setReg dst_reg (BinOp.eval .mod a b)).nextPC.regs .x0 = _
            rw [ArmState.nextPC_regs, hDR, ArmState.setReg_regs_same]; simp [Value.encode]
          have hCodeStore : CodeAt prog
              (pcMap pc + (vLoadVar layout y lv_reg).length + (vLoadVar layout z rv_reg).length + 4)
              (vStoreVar layout x .x0) := by
            rw [← hDR]; exact hCodecDE.tail.tail.tail.tail
          obtain ⟨s6, k6, hSteps6N, hk6, hRel6, hPC6, hAM6⟩ :=
            vStoreVar_exec prog layout x (Value.int (BinOp.eval .mod a b)) σ s5
              (pcMap pc + (vLoadVar layout y lv_reg).length + (vLoadVar layout z rv_reg).length + 4)
              hRel5 hInjective hRegConv hPC5 hVal5 hCodeStore hNotFregX
          have hk6' : k6 = (vStoreVar layout x dst_reg).length := by rw [hDR]; exact hk6
          have h12 : ArmStepsN prog s s2 (k1 + k2) := ArmStepsN_trans hSteps1N hSteps2N
          have h123 : ArmStepsN prog s s2.nextPC (k1 + k2 + 1) := ArmStepsN_trans h12 hStepCbzN
          have h1234 : ArmStepsN prog s s_q (k1 + k2 + 1 + 1) := ArmStepsN_trans h123 hStepSdivN
          have h12345 : ArmStepsN prog s s_qb (k1 + k2 + 1 + 1 + 1) := ArmStepsN_trans h1234 hStepMulN
          have h123456 : ArmStepsN prog s s5 (k1 + k2 + 1 + 1 + 1 + 1) := ArmStepsN_trans h12345 hStepSubN
          have hChain : ArmStepsN prog s s6 (k1 + k2 + 1 + 1 + 1 + 1 + k6) := ArmStepsN_trans h123456 hSteps6N
          refine ⟨s6, k1 + k2 + 1 + 1 + 1 + 1 + k6, hChain, ?_, hRel6, ?_, ?_⟩
          · intro pc' σ' am' _hCfg
            rw [hInstrs, hk1', hk2', hk6']; simp [List.length_append]; omega
          · show s6.pc = pcMap (pc + 1)
            have := hPcNext _ _ rfl; rw [show dst_reg = ArmReg.x0 from hDR] at this; simp at this; omega
          · simp [hAM6, hAM5, hAM2, hAM1, hArrayMem]
    intro armOp hInstrs hArmStep
    rw [hInstrs] at hCodeInstr hPcNext
    have hCodeA := hCodeInstr.append_left
    have hCodeBcD := hCodeInstr.append_right
    have hCodeB := hCodeBcD.append_left
    have hCodecD := hCodeBcD.append_right
    obtain ⟨s1, k1, hSteps1N, hk1, hLV_1, hRel1, _, hPC1, hAM1, hRegs1⟩ :=
      vLoadVar_eff_exec prog layout y σ s (pcMap pc) .x1 hStateRel hRegConv hPcRel
        hNotFregY (Or.inr (Or.inl rfl)) (hMapped y (by simp [TAC.vars])) hCodeA
    have hk1' : k1 = (vLoadVar layout y lv_reg).length := hk1
    obtain ⟨s2, k2, hSteps2N, hk2, hRV_2, hRel2, _, hPC2_, hAM2, hRegs2⟩ :=
      vLoadVar_eff_exec prog layout z σ s1
        (pcMap pc + (vLoadVar layout y lv_reg).length) .x2
        hRel1 hRegConv hPC1 hNotFregZ (Or.inr (Or.inr rfl)) (hMapped z (by simp [TAC.vars])) hCodeB
    have hk2' : k2 = (vLoadVar layout z rv_reg).length := hk2
    have hPC2 : s2.pc = pcMap pc + (vLoadVar layout y lv_reg).length +
        (vLoadVar layout z rv_reg).length := hPC2_
    have hLV_2 : s2.regs lv_reg = a := by
      match hLY : layout y with
      | some (.ireg r) =>
        have hlv : lv_reg = r := by
          show (match layout y with | some (.ireg r) => r | _ => .x1) = r; simp [hLY]
        rw [hlv, hRel2.read_ireg hLY, hy]; simp [Value.encode]
      | some (.stack _) | none =>
        have hlv : lv_reg = .x1 := by
          show (match layout y with | some (.ireg r) => r | _ => .x1) = .x1; simp [hLY]
        rw [hlv]
        have hne : ArmReg.x1 ≠ rv_reg := by
          intro h
          match hLZ : layout z with
          | some (.ireg rz) =>
            have hrv : rv_reg = rz := by
              show (match layout z with | some (.ireg r) => r | _ => .x2) = rz; simp [hLZ]
            rw [hrv] at h; exact hRegConv.not_x1 z (h ▸ hLZ)
          | some (.stack _) | none =>
            have hrv : rv_reg = .x2 := by
              show (match layout z with | some (.ireg r) => r | _ => .x2) = .x2; simp [hLZ]
            rw [hrv] at h; exact absurd h (by decide)
          | some (.freg r) => exact absurd hLZ (hNotFregZ r)
        rw [hRegs2 .x1 hne, ← hlv, hLV_1, hy]; simp [Value.encode]
      | some (.freg r) => exact absurd hLY (hNotFregY r)
    have hRV_eq : s2.regs rv_reg = b := by rw [hRV_2, hz]; simp [Value.encode]
    have hOp := hCodecD.head; rw [← hPC2_] at hOp
    let s3 := (s2.setReg dst_reg (op.eval a b)).nextPC
    have hStep3N : ArmStepsN prog s2 s3 1 := by
      have h := ArmStepsN.single (hArmStep s2 hOp)
      rwa [hLV_2, hRV_eq] at h
    have hPC3 : s3.pc = pcMap pc + (vLoadVar layout y lv_reg).length +
        (vLoadVar layout z rv_reg).length + 1 := by show s2.pc + 1 = _; omega
    have hAM3 : s3.arrayMem = s2.arrayMem := by simp [s3, ArmState.nextPC, ArmState.setReg]
    by_cases hXIR : ∃ r, layout x = some (.ireg r)
    · obtain ⟨r_dst, hDst⟩ := hXIR
      have hDR : dst_reg = r_dst := by
        change (match layout x with | some (.ireg r) => r | _ => .x0) = r_dst; rw [hDst]
      have hStore : vStoreVar layout x dst_reg = [] := by simp [vStoreVar, hDst, hDR]
      have hRel4 : ExtStateRel layout (σ[x ↦ .int (op.eval a b)]) s3 := by
        show ExtStateRel layout (σ[x ↦ .int (op.eval a b)])
          (s2.setReg dst_reg (op.eval a b)).nextPC
        rw [hDR, show op.eval a b = (Value.int (op.eval a b)).encode from by simp [Value.encode]]
        exact (ExtStateRel.update_ireg hRel2 hInjective hDst).nextPC
      have h12 : ArmStepsN prog s s2 (k1 + k2) := ArmStepsN_trans hSteps1N hSteps2N
      have hChain : ArmStepsN prog s s3 (k1 + k2 + 1) := ArmStepsN_trans h12 hStep3N
      refine ⟨s3, k1 + k2 + 1, hChain, ?_, hRel4, ?_, ?_⟩
      · intro pc' σ' am' _hCfg
        rw [hInstrs, hk1', hk2', hStore]; simp [List.length_append]; omega
      · show s3.pc = pcMap (pc + 1)
        have := hPcNext _ _ rfl; simp [hStore] at this; omega
      · simp [hAM3, hAM2, hAM1, hArrayMem]
    · have hDR : dst_reg = .x0 := by
        change (match layout x with | some (.ireg r) => r | _ => .x0) = .x0
        split
        · next r h => exact absurd ⟨r, h⟩ hXIR
        · rfl
      have hRel3 : ExtStateRel layout σ s3 := by
        show ExtStateRel layout σ (s2.setReg dst_reg (op.eval a b)).nextPC
        rw [hDR]; exact (ExtStateRel.setReg_preserved hRel2 (fun w => hRegConv.not_x0 w)).nextPC
      have hVal3 : s3.regs .x0 = (Value.int (op.eval a b)).encode := by
        simp [s3, hDR, ArmState.setReg, ArmState.nextPC, Value.encode]
      have hCodeStore : CodeAt prog
          (pcMap pc + (vLoadVar layout y lv_reg).length + (vLoadVar layout z rv_reg).length + 1)
          (vStoreVar layout x .x0) := by rw [← hDR]; exact hCodecD.tail
      obtain ⟨s4, k4, hSteps4N, hk4, hRel4, hPC4, hAM4⟩ :=
        vStoreVar_exec prog layout x (Value.int (op.eval a b)) σ s3
          (pcMap pc + (vLoadVar layout y lv_reg).length + (vLoadVar layout z rv_reg).length + 1)
          hRel3 hInjective hRegConv hPC3 hVal3 hCodeStore hNotFregX
      have hk4' : k4 = (vStoreVar layout x dst_reg).length := by rw [hDR]; exact hk4
      have h12 : ArmStepsN prog s s2 (k1 + k2) := ArmStepsN_trans hSteps1N hSteps2N
      have h123 : ArmStepsN prog s s3 (k1 + k2 + 1) := ArmStepsN_trans h12 hStep3N
      have hChain : ArmStepsN prog s s4 (k1 + k2 + 1 + k4) := ArmStepsN_trans h123 hSteps4N
      refine ⟨s4, k1 + k2 + 1 + k4, hChain, ?_, hRel4, ?_, ?_⟩
      · intro pc' σ' am' _hCfg
        rw [hInstrs, hk1', hk2', hk4']; simp [List.length_append]; omega
      · show s4.pc = pcMap (pc + 1)
        have := hPcNext _ _ rfl; rw [show dst_reg = ArmReg.x0 from hDR] at this; simp at this; omega
      · simp [hAM4, hAM3, hAM2, hAM1, hArrayMem]
  | boolop hinstr =>
    rename_i x be
    have heq : instr = .boolop x be := Option.some.inj (hInstr.symm.trans hinstr)
    rw [heq] at hSome
    have hSimpleBE : be.hasSimpleOps = true := by
      cases hb : be.hasSimpleOps with
      | true => rfl
      | false => simp [verifiedGenInstr, hRC, hII, hb] at hSome
    have hNotFregX : ∀ r, layout x ≠ some (.freg r) := by
      intro r h; have := hSome; simp [verifiedGenInstr, hRC, hII, hSimpleBE, h] at this
    have hInstrs : instrs = verifiedGenBoolExpr layout be ++ vStoreVar layout x .x0 := by
      have := hSome; simp [verifiedGenInstr, hRC, hII, hSimpleBE] at this; exact this.symm
    rw [hInstrs] at hCodeInstr hPcNext
    have hCodeBE := hCodeInstr.append_left
    have hCodeStore := hCodeInstr.append_right
    have hWTbe : WellTypedBoolExpr tyCtx be := by
      have hwti := hWT pc hPC_bound
      have heq_i := Prog.getElem?_eq_getElem hPC_bound
      rw [hinstr] at heq_i; rw [← Option.some.inj heq_i] at hwti
      cases hwti with | boolop _ hbe => exact hbe
    obtain ⟨s1, k1, hSteps1N, hk1, hX0_1, hRel1, hPC1, hAM1⟩ :=
      verifiedGenBoolExpr_correct prog layout be σ s (pcMap pc) hStateRel hRegConv hCodeBE
        hPcRel tyCtx hTS hWTbe hWTL
        (fun v hv => hMapped v (by simp [heq, TAC.vars]; exact Or.inr hv)) hSimpleBE am
    have hX0_val : s1.regs .x0 = (Value.bool (be.eval σ am)).encode := by
      rw [hX0_1]; simp [Value.encode]
    obtain ⟨s2, k2, hSteps2N, hk2, hRel2, hPC2, hAM2⟩ :=
      vStoreVar_exec prog layout x (Value.bool (be.eval σ am)) σ s1
        (pcMap pc + (verifiedGenBoolExpr layout be).length)
        hRel1 hInjective hRegConv hPC1 hX0_val hCodeStore hNotFregX
    have hChain : ArmStepsN prog s s2 (k1 + k2) := ArmStepsN_trans hSteps1N hSteps2N
    refine ⟨s2, k1 + k2, hChain, ?_, hRel2, ?_, ?_⟩
    · intro pc' σ' am' _hCfg
      rw [hInstrs, hk1, hk2]; simp [List.length_append]
    · show s2.pc = pcMap (pc + 1)
      have := hPcNext _ _ rfl; simp at this; rw [hPC2]; omega
    · simp [hAM2, hAM1, hArrayMem]
  | iftrue hinstr hcond =>
    rename_i l_var be_var
    have heq : instr = .ifgoto be_var l_var := Option.some.inj (hInstr.symm.trans hinstr)
    rw [heq] at hSome hMapped
    have hSimpleBV : be_var.hasSimpleOps = true := by
      cases hb : be_var.hasSimpleOps with
      | true => rfl
      | false => simp [verifiedGenInstr, hRC, hII, hb] at hSome
    have hWTbe : WellTypedBoolExpr tyCtx be_var := by
      have hwti := hWT pc hPC_bound
      have heq_i := Prog.getElem?_eq_getElem hPC_bound
      rw [hinstr] at heq_i; rw [← Option.some.inj heq_i] at hwti
      cases hwti with | ifgoto hbe => exact hbe
    cases be_var with
    | not inner =>
      cases inner with
      | cmp op a b =>
        have hSimpleCmp : (BoolExpr.cmp op a b).hasSimpleOps = true := hSimpleBV
        obtain ⟨hSimpleA, hSimpleB⟩ := BoolExpr.hasSimpleOps_cmp hSimpleCmp
        have hWTcmp : WellTypedBoolExpr tyCtx (.cmp op a b) := by
          cases hWTbe with | not h => exact h
        obtain ⟨ha_ty, hb_ty⟩ : ExprHasTy tyCtx a .int ∧ ExprHasTy tyCtx b .int := by
          cases hWTcmp with | cmp ha hb => exact ⟨ha, hb⟩
        have hcmp_false : BoolExpr.eval σ am (.cmp op a b) = false := by
          simp [BoolExpr.eval] at hcond; exact hcond
        cases a with
        | var va => cases b with
          | var vb =>
            have hNotFregA : ∀ r, layout va ≠ some (.freg r) := hWTL.int_not_freg ha_ty
            have hNotFregB : ∀ r, layout vb ≠ some (.freg r) := hWTL.int_not_freg hb_ty
            have hTyA := hTS va; rw [ha_ty] at hTyA
            have hTyB := hTS vb; rw [hb_ty] at hTyB
            obtain ⟨nA, hnA⟩ := Value.int_of_typeOf_int hTyA
            obtain ⟨nB, hnB⟩ := Value.int_of_typeOf_int hTyB
            -- Match forms must agree with simp-unfolded codegen output below.
            -- `layout v` coerces via `CoeFun` but Lean doesn't see `layout v =
            -- List.lookup v layout.entries` as defeq inside match patterns,
            -- so we mirror the post-simp form explicitly. Wrap `cond`'s match
            -- in a fresh lambda to avoid Lean's motive inference capturing
            -- hypotheses that mention `op`.
            let a_reg : ArmReg :=
              match List.lookup va layout.entries with | some (.ireg r) => r | _ => .x1
            let b_reg : ArmReg :=
              match List.lookup vb layout.entries with | some (.ireg r) => r | _ => .x2
            let cond : Cond := (fun o : CmpOp => match o with
              | .eq => Cond.eq | .ne => .ne | .lt => .lt | .le => .le) op
            have hInstrs : instrs = vLoadVar layout va a_reg ++ vLoadVar layout vb b_reg ++
                [.cmp a_reg b_reg, .bCond cond.negate (pcMap l_var)] := by
              have := hSome; simp [verifiedGenInstr, hRC, hII, hSimpleBV] at this
              rw [← List.append_assoc] at this
              exact this.symm
            rw [hInstrs] at hCodeInstr hPcNext
            have hCodeA := hCodeInstr.append_left.append_left
            have hCodeB := hCodeInstr.append_left.append_right
            have hCodeCmpBCond := hCodeInstr.append_right
            obtain ⟨s1, k1, hSteps1N, hk1, hVal1, hRel1, _, hPC1, hAM1, hRegs1⟩ :=
              vLoadVar_eff_exec prog layout va σ s (pcMap pc) .x1 hStateRel hRegConv hPcRel
                hNotFregA (Or.inr (Or.inl rfl))
                (hMapped va (by simp [TAC.vars, BoolExpr.vars, Expr.freeVars])) hCodeA
            have hk1' : k1 = (vLoadVar layout va a_reg).length := hk1
            obtain ⟨s2, k2, hSteps2N, hk2, hVal2, hRel2, _, hPC2_, hAM2, hRegs2⟩ :=
              vLoadVar_eff_exec prog layout vb σ s1
                (pcMap pc + (vLoadVar layout va a_reg).length) .x2
                hRel1 hRegConv hPC1 hNotFregB (Or.inr (Or.inr rfl))
                (hMapped vb (by simp [TAC.vars, BoolExpr.vars, Expr.freeVars])) hCodeB
            have hk2' : k2 = (vLoadVar layout vb b_reg).length := hk2
            have hPC2 : s2.pc = pcMap pc + (vLoadVar layout va a_reg ++
                vLoadVar layout vb b_reg).length := by
              rw [List.length_append, ← Nat.add_assoc]; exact hPC2_
            have hA_s2 : s2.regs a_reg = nA := by
              have := eff_ireg_val_preserved layout va σ s2 .x1 b_reg hRel2 hNotFregA
                hRegs2 hVal1 (x1_ne_eff_x2 layout vb hRegConv hNotFregB)
              rw [this, hnA]; rfl
            have hB_s2 : s2.regs b_reg = nB := by rw [hVal2, hnB]; rfl
            have hCmp := hCodeCmpBCond.head; rw [← hPC2] at hCmp
            let s3 := { s2 with flags := Flags.mk (s2.regs a_reg) (s2.regs b_reg), pc := s2.pc + 1 }
            have hStepCmpN : ArmStepsN prog s2 s3 1 :=
              ArmStepsN.single (.cmpRR a_reg b_reg hCmp)
            have hPC3 : s3.pc = pcMap pc + (vLoadVar layout va a_reg ++
                vLoadVar layout vb b_reg).length + 1 := by
              show s2.pc + 1 = _; rw [hPC2]
            have hBCond := hCodeCmpBCond.tail.head; rw [← hPC3] at hBCond
            simp only [BoolExpr.eval, Expr.eval, Value.toInt, hnA, hnB] at hcmp_false
            have hCondTrue : s3.flags.condHolds cond.negate = true := by
              show ({ lhs := s2.regs a_reg, rhs := s2.regs b_reg } : Flags).condHolds cond.negate = true
              rw [hA_s2, hB_s2, Cond.negate_correct]
              cases op <;> simp_all [cond, Flags.condHolds, CmpOp.eval,
                BitVec.sle_eq_not_slt, bne, BEq.beq]
            let s_fin : ArmState := { s3 with pc := pcMap l_var }
            have hStepBCondN : ArmStepsN prog s3 s_fin 1 :=
              ArmStepsN.single (.bCond_taken cond.negate (pcMap l_var) hBCond hCondTrue)
            have h12 : ArmStepsN prog s s2 (k1 + k2) := ArmStepsN_trans hSteps1N hSteps2N
            have h123 : ArmStepsN prog s s3 (k1 + k2 + 1) := ArmStepsN_trans h12 hStepCmpN
            have hChain : ArmStepsN prog s s_fin (k1 + k2 + 1 + 1) :=
              ArmStepsN_trans h123 hStepBCondN
            refine ⟨s_fin, k1 + k2 + 1 + 1, hChain, ?_, ?_, rfl, ?_⟩
            · intro pc' σ' am' _hCfg
              rw [hInstrs, hk1', hk2']; simp [List.length_append]; omega
            · exact fun v loc hv => hRel2 v loc hv
            · show s_fin.arrayMem = am
              simp [s_fin, s3, hAM2, hAM1, hArrayMem]
          | lit nb =>
            have hNotFregA : ∀ r, layout va ≠ some (.freg r) := hWTL.int_not_freg ha_ty
            have hTyA := hTS va; rw [ha_ty] at hTyA
            obtain ⟨nA, hnA⟩ := Value.int_of_typeOf_int hTyA
            let a_reg : ArmReg :=
              match List.lookup va layout.entries with | some (.ireg r) => r | _ => .x1
            let cond : Cond := (fun o : CmpOp => match o with
              | .eq => Cond.eq | .ne => .ne | .lt => .lt | .le => .le) op
            have hInstrs : instrs = vLoadVar layout va a_reg ++ formalLoadImm64 .x2 nb ++
                [.cmp a_reg .x2, .bCond cond.negate (pcMap l_var)] := by
              have := hSome; simp [verifiedGenInstr, hRC, hII, hSimpleBV] at this
              rw [← List.append_assoc] at this
              exact this.symm
            rw [hInstrs] at hCodeInstr hPcNext
            have hCodeA := hCodeInstr.append_left.append_left
            have hCodeImm := hCodeInstr.append_left.append_right
            have hCodeCmpBCond := hCodeInstr.append_right
            obtain ⟨s1, k1, hSteps1N, hk1, hVal1, hRel1, _, hPC1, hAM1, hRegs1⟩ :=
              vLoadVar_eff_exec prog layout va σ s (pcMap pc) .x1 hStateRel hRegConv hPcRel
                hNotFregA (Or.inr (Or.inl rfl))
                (hMapped va (by simp [TAC.vars, BoolExpr.vars, Expr.freeVars])) hCodeA
            have hk1' : k1 = (vLoadVar layout va a_reg).length := hk1
            obtain ⟨s2, k2, hSteps2N, hk2, hFregs2, hX2, hStack2, hPC2_, hRegs2, hAM2⟩ :=
              loadImm64_fregs_preserved prog .x2 nb s1
                (pcMap pc + (vLoadVar layout va a_reg).length) hCodeImm hPC1
            have hRel2 := loadImm64_preserves_ExtStateRel prog layout .x2 nb σ s1 s2
                hRel1 hRegConv hStack2 hFregs2 hRegs2 hAM2 (Or.inr (Or.inr rfl))
            have hA_s2 : s2.regs a_reg = nA := by
              have := eff_ireg_val_preserved layout va σ s2 .x1 .x2 hRel2 hNotFregA
                hRegs2 hVal1 (by decide)
              rw [this, hnA]; rfl
            have hPC2 : s2.pc = pcMap pc + (vLoadVar layout va a_reg ++
                formalLoadImm64 .x2 nb).length := by
              rw [List.length_append, ← Nat.add_assoc]; exact hPC2_
            have hCmp := hCodeCmpBCond.head; rw [← hPC2] at hCmp
            let s3 : ArmState :=
              { s2 with flags := Flags.mk (s2.regs a_reg) (s2.regs .x2), pc := s2.pc + 1 }
            have hStepCmpN : ArmStepsN prog s2 s3 1 :=
              ArmStepsN.single (.cmpRR a_reg .x2 hCmp)
            have hPC3 : s3.pc = pcMap pc + (vLoadVar layout va a_reg ++
                formalLoadImm64 .x2 nb).length + 1 := by
              show s2.pc + 1 = _; rw [hPC2]
            have hBCond := hCodeCmpBCond.tail.head; rw [← hPC3] at hBCond
            simp only [BoolExpr.eval, Expr.eval, Value.toInt, hnA] at hcmp_false
            have hCondTrue : s3.flags.condHolds cond.negate = true := by
              show ({ lhs := s2.regs a_reg, rhs := s2.regs .x2 } : Flags).condHolds
                cond.negate = true
              rw [hA_s2, hX2, Cond.negate_correct]
              cases op <;> simp_all [cond, Flags.condHolds, CmpOp.eval,
                BitVec.sle_eq_not_slt, bne, BEq.beq]
            let s_fin : ArmState := { s3 with pc := pcMap l_var }
            have hStepBCondN : ArmStepsN prog s3 s_fin 1 :=
              ArmStepsN.single (.bCond_taken cond.negate (pcMap l_var) hBCond hCondTrue)
            have h12 : ArmStepsN prog s s2 (k1 + k2) := ArmStepsN_trans hSteps1N hSteps2N
            have h123 : ArmStepsN prog s s3 (k1 + k2 + 1) := ArmStepsN_trans h12 hStepCmpN
            have hChain : ArmStepsN prog s s_fin (k1 + k2 + 1 + 1) :=
              ArmStepsN_trans h123 hStepBCondN
            refine ⟨s_fin, k1 + k2 + 1 + 1, hChain, ?_, ?_, rfl, ?_⟩
            · intro pc' σ' am' _hCfg
              rw [hInstrs, hk1', hk2]; simp [List.length_append]; omega
            · exact fun v loc hv => hRel2 v loc hv
            · show s_fin.arrayMem = am
              simp [s_fin, s3, hAM2, hAM1, hArrayMem]
          | _ => rcases hSimpleB with ⟨_, h⟩ | ⟨_, h⟩ <;> simp at h
        | lit na => cases b with
          | var vb =>
            have hNotFregB : ∀ r, layout vb ≠ some (.freg r) := hWTL.int_not_freg hb_ty
            have hTyB := hTS vb; rw [hb_ty] at hTyB
            obtain ⟨nB, hnB⟩ := Value.int_of_typeOf_int hTyB
            let b_reg : ArmReg :=
              match List.lookup vb layout.entries with | some (.ireg r) => r | _ => .x2
            let cond : Cond := (fun o : CmpOp => match o with
              | .eq => Cond.eq | .ne => .ne | .lt => .lt | .le => .le) op
            have hInstrs : instrs = formalLoadImm64 .x1 na ++ vLoadVar layout vb b_reg ++
                [.cmp .x1 b_reg, .bCond cond.negate (pcMap l_var)] := by
              have := hSome; simp [verifiedGenInstr, hRC, hII, hSimpleBV] at this
              rw [← List.append_assoc] at this
              exact this.symm
            rw [hInstrs] at hCodeInstr hPcNext
            have hCodeImm := hCodeInstr.append_left.append_left
            have hCodeB := hCodeInstr.append_left.append_right
            have hCodeCmpBCond := hCodeInstr.append_right
            obtain ⟨s1, k1, hSteps1N, hk1, hFregs1, hX1, hStack1, hPC1, hRegs1, hAM1⟩ :=
              loadImm64_fregs_preserved prog .x1 na s (pcMap pc) hCodeImm hPcRel
            have hRel1 := loadImm64_preserves_ExtStateRel prog layout .x1 na σ s s1
                hStateRel hRegConv hStack1 hFregs1 hRegs1 hAM1 (Or.inr (Or.inl rfl))
            obtain ⟨s2, k2, hSteps2N, hk2, hVal2, hRel2, _, hPC2_, hAM2, hRegs2⟩ :=
              vLoadVar_eff_exec prog layout vb σ s1
                (pcMap pc + (formalLoadImm64 .x1 na).length) .x2
                hRel1 hRegConv hPC1 hNotFregB (Or.inr (Or.inr rfl))
                (hMapped vb (by simp [TAC.vars, BoolExpr.vars, Expr.freeVars])) hCodeB
            have hk2' : k2 = (vLoadVar layout vb b_reg).length := hk2
            have hX1_s2 : s2.regs .x1 = na := by
              rw [hRegs2 .x1 (x1_ne_eff_x2 layout vb hRegConv hNotFregB)]; exact hX1
            have hB_s2 : s2.regs b_reg = nB := by rw [hVal2, hnB]; rfl
            have hPC2 : s2.pc = pcMap pc + (formalLoadImm64 .x1 na ++
                vLoadVar layout vb b_reg).length := by
              rw [List.length_append, ← Nat.add_assoc]; exact hPC2_
            have hCmp := hCodeCmpBCond.head; rw [← hPC2] at hCmp
            let s3 : ArmState :=
              { s2 with flags := Flags.mk (s2.regs .x1) (s2.regs b_reg), pc := s2.pc + 1 }
            have hStepCmpN : ArmStepsN prog s2 s3 1 :=
              ArmStepsN.single (.cmpRR .x1 b_reg hCmp)
            have hPC3 : s3.pc = pcMap pc + (formalLoadImm64 .x1 na ++
                vLoadVar layout vb b_reg).length + 1 := by
              show s2.pc + 1 = _; rw [hPC2]
            have hBCond := hCodeCmpBCond.tail.head; rw [← hPC3] at hBCond
            simp only [BoolExpr.eval, Expr.eval, Value.toInt, hnB] at hcmp_false
            have hCondTrue : s3.flags.condHolds cond.negate = true := by
              show ({ lhs := s2.regs .x1, rhs := s2.regs b_reg } : Flags).condHolds
                cond.negate = true
              rw [hX1_s2, hB_s2, Cond.negate_correct]
              cases op <;> simp_all [cond, Flags.condHolds, CmpOp.eval,
                BitVec.sle_eq_not_slt, bne, BEq.beq]
            let s_fin : ArmState := { s3 with pc := pcMap l_var }
            have hStepBCondN : ArmStepsN prog s3 s_fin 1 :=
              ArmStepsN.single (.bCond_taken cond.negate (pcMap l_var) hBCond hCondTrue)
            have h12 : ArmStepsN prog s s2 (k1 + k2) := ArmStepsN_trans hSteps1N hSteps2N
            have h123 : ArmStepsN prog s s3 (k1 + k2 + 1) := ArmStepsN_trans h12 hStepCmpN
            have hChain : ArmStepsN prog s s_fin (k1 + k2 + 1 + 1) :=
              ArmStepsN_trans h123 hStepBCondN
            refine ⟨s_fin, k1 + k2 + 1 + 1, hChain, ?_, ?_, rfl, ?_⟩
            · intro pc' σ' am' _hCfg
              rw [hInstrs, hk1, hk2']; simp [List.length_append]; omega
            · exact fun v loc hv => hRel2 v loc hv
            · show s_fin.arrayMem = am
              simp [s_fin, s3, hAM2, hAM1, hArrayMem]
          | lit nb =>
            let cond : Cond := (fun o : CmpOp => match o with
              | .eq => Cond.eq | .ne => .ne | .lt => .lt | .le => .le) op
            have hInstrs : instrs = formalLoadImm64 .x1 na ++ formalLoadImm64 .x2 nb ++
                [.cmp .x1 .x2, .bCond cond.negate (pcMap l_var)] := by
              have := hSome; simp [verifiedGenInstr, hRC, hII, hSimpleBV] at this
              rw [← List.append_assoc] at this
              exact this.symm
            rw [hInstrs] at hCodeInstr hPcNext
            have hCodeImmA := hCodeInstr.append_left.append_left
            have hCodeImmB := hCodeInstr.append_left.append_right
            have hCodeCmpBCond := hCodeInstr.append_right
            obtain ⟨s1, k1, hSteps1N, hk1, hFregs1, hX1, hStack1, hPC1, hRegs1, hAM1⟩ :=
              loadImm64_fregs_preserved prog .x1 na s (pcMap pc) hCodeImmA hPcRel
            have hRel1 := loadImm64_preserves_ExtStateRel prog layout .x1 na σ s s1
                hStateRel hRegConv hStack1 hFregs1 hRegs1 hAM1 (Or.inr (Or.inl rfl))
            obtain ⟨s2, k2, hSteps2N, hk2, hFregs2, hX2, hStack2, hPC2_, hRegs2, hAM2⟩ :=
              loadImm64_fregs_preserved prog .x2 nb s1
                (pcMap pc + (formalLoadImm64 .x1 na).length) hCodeImmB hPC1
            have hRel2 := loadImm64_preserves_ExtStateRel prog layout .x2 nb σ s1 s2
                hRel1 hRegConv hStack2 hFregs2 hRegs2 hAM2 (Or.inr (Or.inr rfl))
            have hX1_s2 : s2.regs .x1 = na := by rw [hRegs2 .x1 (by decide)]; exact hX1
            have hPC2 : s2.pc = pcMap pc +
                (formalLoadImm64 .x1 na ++ formalLoadImm64 .x2 nb).length := by
              rw [List.length_append, ← Nat.add_assoc]; exact hPC2_
            have hCmp := hCodeCmpBCond.head; rw [← hPC2] at hCmp
            let s3 : ArmState :=
              { s2 with flags := Flags.mk (s2.regs .x1) (s2.regs .x2), pc := s2.pc + 1 }
            have hStepCmpN : ArmStepsN prog s2 s3 1 :=
              ArmStepsN.single (.cmpRR .x1 .x2 hCmp)
            have hPC3 : s3.pc = pcMap pc +
                (formalLoadImm64 .x1 na ++ formalLoadImm64 .x2 nb).length + 1 := by
              show s2.pc + 1 = _; rw [hPC2]
            have hBCond := hCodeCmpBCond.tail.head; rw [← hPC3] at hBCond
            simp only [BoolExpr.eval, Expr.eval, Value.toInt] at hcmp_false
            have hCondTrue : s3.flags.condHolds cond.negate = true := by
              show ({ lhs := s2.regs .x1, rhs := s2.regs .x2 } : Flags).condHolds
                cond.negate = true
              rw [hX1_s2, hX2, Cond.negate_correct]
              cases op <;> simp_all [cond, Flags.condHolds, CmpOp.eval,
                BitVec.sle_eq_not_slt, bne, BEq.beq]
            let s_fin : ArmState := { s3 with pc := pcMap l_var }
            have hStepBCondN : ArmStepsN prog s3 s_fin 1 :=
              ArmStepsN.single (.bCond_taken cond.negate (pcMap l_var) hBCond hCondTrue)
            have h12 : ArmStepsN prog s s2 (k1 + k2) := ArmStepsN_trans hSteps1N hSteps2N
            have h123 : ArmStepsN prog s s3 (k1 + k2 + 1) := ArmStepsN_trans h12 hStepCmpN
            have hChain : ArmStepsN prog s s_fin (k1 + k2 + 1 + 1) :=
              ArmStepsN_trans h123 hStepBCondN
            refine ⟨s_fin, k1 + k2 + 1 + 1, hChain, ?_, ?_, rfl, ?_⟩
            · intro pc' σ' am' _hCfg
              rw [hInstrs, hk1, hk2]; simp [List.length_append]; omega
            · exact fun v loc hv => hRel2 v loc hv
            · show s_fin.arrayMem = am
              simp [s_fin, s3, hAM2, hAM1, hArrayMem]
          | _ => rcases hSimpleB with ⟨_, h⟩ | ⟨_, h⟩ <;> simp at h
        | _ => rcases hSimpleA with ⟨_, h⟩ | ⟨_, h⟩ <;> simp at h
      | fcmp fop a b =>
        have hSimpleFcmp : (BoolExpr.fcmp fop a b).hasSimpleOps = true := hSimpleBV
        obtain ⟨hSimpleA, hSimpleB⟩ := BoolExpr.hasSimpleOps_fcmp hSimpleFcmp
        have hWTfcmp : WellTypedBoolExpr tyCtx (.fcmp fop a b) := by
          cases hWTbe with | not h => exact h
        obtain ⟨ha_ty, hb_ty⟩ : ExprHasTy tyCtx a .float ∧ ExprHasTy tyCtx b .float := by
          cases hWTfcmp with | fcmp ha hb => exact ⟨ha, hb⟩
        have hfcmp_false : BoolExpr.eval σ am (.fcmp fop a b) = false := by
          simp [BoolExpr.eval] at hcond; exact hcond
        let cond : Cond := (fun f : FloatCmpOp => match f with
          | .feq => Cond.eq | .fne => .ne | .flt => .lt | .fle => .le) fop
        cases a with
        | var va => cases b with
          | var vb =>
            have hNotIregA : ∀ r, layout va ≠ some (.ireg r) := hWTL.float_not_ireg ha_ty
            have hNotIregB : ∀ r, layout vb ≠ some (.ireg r) := hWTL.float_not_ireg hb_ty
            have hTyA := hTS va; rw [ha_ty] at hTyA
            have hTyB := hTS vb; rw [hb_ty] at hTyB
            obtain ⟨fA, hfA⟩ := Value.float_of_typeOf_float hTyA
            obtain ⟨fB, hfB⟩ := Value.float_of_typeOf_float hTyB
            let a_freg : ArmFReg :=
              match List.lookup va layout.entries with | some (.freg r) => r | _ => .d1
            let b_freg : ArmFReg :=
              match List.lookup vb layout.entries with | some (.freg r) => r | _ => .d2
            have hInstrs : instrs = vLoadVarFP layout va a_freg ++ vLoadVarFP layout vb b_freg ++
                [.fcmpR a_freg b_freg, .bCond cond.negate (pcMap l_var)] := by
              have := hSome; simp [verifiedGenInstr, hRC, hII, hSimpleBV] at this
              rw [← List.append_assoc] at this
              exact this.symm
            rw [hInstrs] at hCodeInstr hPcNext
            have hCodeA := hCodeInstr.append_left.append_left
            have hCodeB := hCodeInstr.append_left.append_right
            have hCodeFcmpBCond := hCodeInstr.append_right
            obtain ⟨s1, k1, hSteps1N, hk1, hVal1, hRel1, _, hPC1, hAM1, hFregs1, _⟩ :=
              vLoadVarFP_eff_exec prog layout va σ s (pcMap pc) .d1 hStateRel hRegConv hPcRel
                hNotIregA (Or.inr (Or.inl rfl))
                (hMapped va (by simp [TAC.vars, BoolExpr.vars, Expr.freeVars])) hCodeA
            have hk1' : k1 = (vLoadVarFP layout va a_freg).length := hk1
            obtain ⟨s2, k2, hSteps2N, hk2, hVal2, hRel2, _, hPC2_, hAM2, hFregs2, _⟩ :=
              vLoadVarFP_eff_exec prog layout vb σ s1
                (pcMap pc + (vLoadVarFP layout va a_freg).length) .d2
                hRel1 hRegConv hPC1 hNotIregB (Or.inr (Or.inr rfl))
                (hMapped vb (by simp [TAC.vars, BoolExpr.vars, Expr.freeVars])) hCodeB
            have hk2' : k2 = (vLoadVarFP layout vb b_freg).length := hk2
            have hPC2 : s2.pc = pcMap pc + (vLoadVarFP layout va a_freg ++
                vLoadVarFP layout vb b_freg).length := by
              rw [List.length_append, ← Nat.add_assoc]; exact hPC2_
            have hA_s2 : s2.fregs a_freg = fA := by
              have := eff_freg_val_preserved layout va σ s2 .d1 b_freg hRel2 hNotIregA
                hFregs2 hVal1 (d1_ne_eff_d2 layout vb hRegConv hNotIregB)
              rw [this, hfA]; rfl
            have hB_s2 : s2.fregs b_freg = fB := by rw [hVal2, hfB]; rfl
            have hFcmpI := hCodeFcmpBCond.head; rw [← hPC2] at hFcmpI
            let s3 : ArmState :=
              { s2 with flags := fcmpFlags (s2.fregs a_freg) (s2.fregs b_freg), pc := s2.pc + 1 }
            have hStepFcmpN : ArmStepsN prog s2 s3 1 :=
              ArmStepsN.single (.fcmpRR a_freg b_freg hFcmpI)
            have hPC3 : s3.pc = pcMap pc + (vLoadVarFP layout va a_freg ++
                vLoadVarFP layout vb b_freg).length + 1 := by
              show s2.pc + 1 = _; rw [hPC2]
            have hBCond := hCodeFcmpBCond.tail.head; rw [← hPC3] at hBCond
            simp only [BoolExpr.eval, Expr.eval, Value.toFloat, hfA, hfB] at hfcmp_false
            have hCondTrue : s3.flags.condHolds cond.negate = true := by
              show (fcmpFlags (s2.fregs a_freg) (s2.fregs b_freg)).condHolds
                cond.negate = true
              rw [hA_s2, hB_s2, Cond.negate_correct]
              cases fop <;>
                exact congrArg (!·) ((Flags.condHolds_float_correct _ fA fB).trans hfcmp_false)
            let s_fin : ArmState := { s3 with pc := pcMap l_var }
            have hStepBCondN : ArmStepsN prog s3 s_fin 1 :=
              ArmStepsN.single (.bCond_taken cond.negate (pcMap l_var) hBCond hCondTrue)
            have h12 : ArmStepsN prog s s2 (k1 + k2) := ArmStepsN_trans hSteps1N hSteps2N
            have h123 : ArmStepsN prog s s3 (k1 + k2 + 1) := ArmStepsN_trans h12 hStepFcmpN
            have hChain : ArmStepsN prog s s_fin (k1 + k2 + 1 + 1) :=
              ArmStepsN_trans h123 hStepBCondN
            refine ⟨s_fin, k1 + k2 + 1 + 1, hChain, ?_, ?_, rfl, ?_⟩
            · intro pc' σ' am' _hCfg
              rw [hInstrs, hk1', hk2']; simp [List.length_append]; omega
            · exact fun v loc hv => hRel2 v loc hv
            · show s_fin.arrayMem = am
              simp [s_fin, s3, hAM2, hAM1, hArrayMem]
          | flit fb =>
            have hNotIregA : ∀ r, layout va ≠ some (.ireg r) := hWTL.float_not_ireg ha_ty
            have hTyA := hTS va; rw [ha_ty] at hTyA
            obtain ⟨fA, hfA⟩ := Value.float_of_typeOf_float hTyA
            let a_freg : ArmFReg :=
              match List.lookup va layout.entries with | some (.freg r) => r | _ => .d1
            have hInstrs : instrs = vLoadVarFP layout va a_freg ++ formalLoadImm64 .x0 fb ++
                [.fmovToFP .d2 .x0, .fcmpR a_freg .d2, .bCond cond.negate (pcMap l_var)] := by
              have := hSome; simp [verifiedGenInstr, hRC, hII, hSimpleBV] at this
              rw [← List.append_assoc] at this
              exact this.symm
            rw [hInstrs] at hCodeInstr hPcNext
            have hCodeA := hCodeInstr.append_left.append_left
            have hCodeImm := hCodeInstr.append_left.append_right
            have hCodeTail := hCodeInstr.append_right
            obtain ⟨s1, k1, hSteps1N, hk1, hVal1, hRel1, _, hPC1, hAM1, hFregs1, _⟩ :=
              vLoadVarFP_eff_exec prog layout va σ s (pcMap pc) .d1 hStateRel hRegConv hPcRel
                hNotIregA (Or.inr (Or.inl rfl))
                (hMapped va (by simp [TAC.vars, BoolExpr.vars, Expr.freeVars])) hCodeA
            have hk1' : k1 = (vLoadVarFP layout va a_freg).length := hk1
            -- loadFlit_chain bundles (loadImm64 + fmov) into one step:
            have hFmov_at : prog[pcMap pc + (vLoadVarFP layout va a_freg).length
                + (formalLoadImm64 .x0 fb).length]? = some (.fmovToFP .d2 .x0) := by
              have := hCodeTail.head
              rw [List.length_append, ← Nat.add_assoc] at this
              exact this
            obtain ⟨s3, k23, hSteps23N, hk23, hD2_s3, hRel3, hPC3_raw, hAM3_s1, hFregs_s3_to_s1⟩ :=
              loadFlit_chain prog layout .d2 fb σ s1
                (pcMap pc + (vLoadVarFP layout va a_freg).length) hRel1 hRegConv hPC1
                hCodeImm hFmov_at (Or.inr (Or.inr rfl))
            have hPC3 : s3.pc = pcMap pc +
                (vLoadVarFP layout va a_freg ++ formalLoadImm64 .x0 fb).length + 1 := by
              rw [List.length_append]; rw [hPC3_raw]; omega
            have hA_s3 : s3.fregs a_freg = fA := by
              have := eff_freg_val_preserved layout va σ s3 .d1 .d2 hRel3 hNotIregA
                hFregs_s3_to_s1 hVal1 (by decide)
              rw [this, hfA]; rfl
            have hFcmpI := hCodeTail.tail.head; rw [← hPC3] at hFcmpI
            let s4 : ArmState :=
              { s3 with flags := fcmpFlags (s3.fregs a_freg) (s3.fregs .d2), pc := s3.pc + 1 }
            have hStepFcmpN : ArmStepsN prog s3 s4 1 :=
              ArmStepsN.single (.fcmpRR a_freg .d2 hFcmpI)
            have hPC4 : s4.pc = pcMap pc +
                (vLoadVarFP layout va a_freg ++ formalLoadImm64 .x0 fb).length + 1 + 1 := by
              show s3.pc + 1 = _; rw [hPC3]
            have hBCond := hCodeTail.tail.tail.head; rw [← hPC4] at hBCond
            simp only [BoolExpr.eval, Expr.eval, Value.toFloat, hfA] at hfcmp_false
            have hCondTrue : s4.flags.condHolds cond.negate = true := by
              show (fcmpFlags (s3.fregs a_freg) (s3.fregs .d2)).condHolds
                cond.negate = true
              rw [hA_s3, hD2_s3, Cond.negate_correct]
              cases fop <;>
                exact congrArg (!·) ((Flags.condHolds_float_correct _ fA fb).trans hfcmp_false)
            let s_fin : ArmState := { s4 with pc := pcMap l_var }
            have hStepBCondN : ArmStepsN prog s4 s_fin 1 :=
              ArmStepsN.single (.bCond_taken cond.negate (pcMap l_var) hBCond hCondTrue)
            have h13 : ArmStepsN prog s s3 (k1 + k23) := ArmStepsN_trans hSteps1N hSteps23N
            have h134 : ArmStepsN prog s s4 (k1 + k23 + 1) := ArmStepsN_trans h13 hStepFcmpN
            have hChain : ArmStepsN prog s s_fin (k1 + k23 + 1 + 1) :=
              ArmStepsN_trans h134 hStepBCondN
            refine ⟨s_fin, k1 + k23 + 1 + 1, hChain, ?_, ?_, rfl, ?_⟩
            · intro pc' σ' am' _hCfg
              rw [hInstrs, hk1', hk23]; simp [List.length_append]; omega
            · exact fun v loc hv => hRel3 v loc hv
            · show s_fin.arrayMem = am
              simp [s_fin, s4, hAM3_s1, hAM1, hArrayMem]
          | _ => rcases hSimpleB with ⟨_, h⟩ | ⟨_, h⟩ <;> simp at h
        | flit fa => cases b with
          | var vb =>
            have hNotIregB : ∀ r, layout vb ≠ some (.ireg r) := hWTL.float_not_ireg hb_ty
            have hTyB := hTS vb; rw [hb_ty] at hTyB
            obtain ⟨fB, hfB⟩ := Value.float_of_typeOf_float hTyB
            let b_freg : ArmFReg :=
              match List.lookup vb layout.entries with | some (.freg r) => r | _ => .d2
            -- Codegen swaps when a=.flit, b=.var: loads = loadB ++ loadA
            have hInstrs : instrs = vLoadVarFP layout vb b_freg ++ formalLoadImm64 .x0 fa ++
                [.fmovToFP .d1 .x0, .fcmpR .d1 b_freg, .bCond cond.negate (pcMap l_var)] := by
              have := hSome; simp [verifiedGenInstr, hRC, hII, hSimpleBV] at this
              rw [← List.append_assoc] at this
              exact this.symm
            rw [hInstrs] at hCodeInstr hPcNext
            have hCodeB := hCodeInstr.append_left.append_left
            have hCodeImm := hCodeInstr.append_left.append_right
            have hCodeTail := hCodeInstr.append_right
            obtain ⟨s1, k1, hSteps1N, hk1, hVal1, hRel1, _, hPC1, hAM1, hFregs1, _⟩ :=
              vLoadVarFP_eff_exec prog layout vb σ s (pcMap pc) .d2 hStateRel hRegConv hPcRel
                hNotIregB (Or.inr (Or.inr rfl))
                (hMapped vb (by simp [TAC.vars, BoolExpr.vars, Expr.freeVars])) hCodeB
            have hk1' : k1 = (vLoadVarFP layout vb b_freg).length := hk1
            have hFmov_at : prog[pcMap pc + (vLoadVarFP layout vb b_freg).length
                + (formalLoadImm64 .x0 fa).length]? = some (.fmovToFP .d1 .x0) := by
              have := hCodeTail.head
              rw [List.length_append, ← Nat.add_assoc] at this
              exact this
            obtain ⟨s3, k23, hSteps23N, hk23, hD1_s3, hRel3, hPC3_raw, hAM3_s1, hFregs_s3_to_s1⟩ :=
              loadFlit_chain prog layout .d1 fa σ s1
                (pcMap pc + (vLoadVarFP layout vb b_freg).length) hRel1 hRegConv hPC1
                hCodeImm hFmov_at (Or.inr (Or.inl rfl))
            have hPC3 : s3.pc = pcMap pc +
                (vLoadVarFP layout vb b_freg ++ formalLoadImm64 .x0 fa).length + 1 := by
              rw [List.length_append]; rw [hPC3_raw]; omega
            have hB_s3 : s3.fregs b_freg = fB := by
              have := eff_freg_val_preserved layout vb σ s3 .d2 .d1 hRel3 hNotIregB
                hFregs_s3_to_s1 hVal1 (by decide)
              rw [this, hfB]; rfl
            have hFcmpI := hCodeTail.tail.head; rw [← hPC3] at hFcmpI
            let s4 : ArmState :=
              { s3 with flags := fcmpFlags (s3.fregs .d1) (s3.fregs b_freg), pc := s3.pc + 1 }
            have hStepFcmpN : ArmStepsN prog s3 s4 1 :=
              ArmStepsN.single (.fcmpRR .d1 b_freg hFcmpI)
            have hPC4 : s4.pc = pcMap pc +
                (vLoadVarFP layout vb b_freg ++ formalLoadImm64 .x0 fa).length + 1 + 1 := by
              show s3.pc + 1 = _; rw [hPC3]
            have hBCond := hCodeTail.tail.tail.head; rw [← hPC4] at hBCond
            simp only [BoolExpr.eval, Expr.eval, Value.toFloat, hfB] at hfcmp_false
            have hCondTrue : s4.flags.condHolds cond.negate = true := by
              show (fcmpFlags (s3.fregs .d1) (s3.fregs b_freg)).condHolds
                cond.negate = true
              rw [hD1_s3, hB_s3, Cond.negate_correct]
              cases fop <;>
                exact congrArg (!·) ((Flags.condHolds_float_correct _ fa fB).trans hfcmp_false)
            let s_fin : ArmState := { s4 with pc := pcMap l_var }
            have hStepBCondN : ArmStepsN prog s4 s_fin 1 :=
              ArmStepsN.single (.bCond_taken cond.negate (pcMap l_var) hBCond hCondTrue)
            have h13 : ArmStepsN prog s s3 (k1 + k23) := ArmStepsN_trans hSteps1N hSteps23N
            have h134 : ArmStepsN prog s s4 (k1 + k23 + 1) := ArmStepsN_trans h13 hStepFcmpN
            have hChain : ArmStepsN prog s s_fin (k1 + k23 + 1 + 1) :=
              ArmStepsN_trans h134 hStepBCondN
            refine ⟨s_fin, k1 + k23 + 1 + 1, hChain, ?_, ?_, rfl, ?_⟩
            · intro pc' σ' am' _hCfg
              rw [hInstrs, hk1', hk23]; simp [List.length_append]; omega
            · exact fun v loc hv => hRel3 v loc hv
            · show s_fin.arrayMem = am
              simp [s_fin, s4, hAM3_s1, hAM1, hArrayMem]
          | flit fb =>
            -- Both operands literals: a_freg = .d1, b_freg = .d2 by default.
            -- simp produces cons form for [fmov_d1].  Match it.
            have hInstrs : instrs = formalLoadImm64 .x0 fa ++
                (.fmovToFP .d1 .x0 :: (formalLoadImm64 .x0 fb ++
                  [.fmovToFP .d2 .x0, .fcmpR .d1 .d2,
                   .bCond cond.negate (pcMap l_var)])) := by
              have := hSome; simp [verifiedGenInstr, hRC, hII, hSimpleBV] at this
              exact this.symm
            rw [hInstrs] at hCodeInstr hPcNext
            have hCodeImmA := hCodeInstr.append_left
            have hCodeRest := hCodeInstr.append_right
            have hCodeFmovA := hCodeRest.head
            have hCodeAfterFmovA := hCodeRest.tail
            have hCodeImmB := hCodeAfterFmovA.append_left
            have hCodeTail := hCodeAfterFmovA.append_right
            -- Step A: loadImm_a + fmov_d1 → s2 (via loadFlit_chain)
            obtain ⟨s2, k12, hSteps12N, hk12, hD1_s2, hRel2, hPC2, hAM2_s, hFregs_s2_to_s⟩ :=
              loadFlit_chain prog layout .d1 fa σ s (pcMap pc)
                hStateRel hRegConv hPcRel hCodeImmA hCodeFmovA (Or.inr (Or.inl rfl))
            -- Step B: loadImm_b + fmov_d2 → s4
            have hFmov_atB : prog[s2.pc + (formalLoadImm64 .x0 fb).length]?
                = some (.fmovToFP .d2 .x0) := by
              rw [hPC2]; exact hCodeTail.head
            have hCodeImmB' : CodeAt prog s2.pc (formalLoadImm64 .x0 fb) := by
              rw [hPC2]; exact hCodeImmB
            obtain ⟨s4, k34, hSteps34N, hk34, hD2_s4, hRel4, hPC4_raw, hAM4_s2, hFregs_s4_to_s2⟩ :=
              loadFlit_chain prog layout .d2 fb σ s2 s2.pc
                hRel2 hRegConv rfl hCodeImmB' hFmov_atB (Or.inr (Or.inr rfl))
            have hPC4 : s4.pc = pcMap pc + (formalLoadImm64 .x0 fa).length + 1
                + (formalLoadImm64 .x0 fb).length + 1 := by
              rw [hPC4_raw, hPC2]
            have hD1_s4 : s4.fregs .d1 = fa := by
              rw [hFregs_s4_to_s2 .d1 (by decide)]; exact hD1_s2
            -- Step C: fcmp
            have hFcmpI : prog[s4.pc]? = some (.fcmpR .d1 .d2) := by
              rw [hPC4]; exact hCodeTail.tail.head
            let s5 : ArmState :=
              { s4 with flags := fcmpFlags (s4.fregs .d1) (s4.fregs .d2), pc := s4.pc + 1 }
            have hStepFcmp : ArmStepsN prog s4 s5 1 :=
              ArmStepsN.single (.fcmpRR .d1 .d2 hFcmpI)
            have hBCond : prog[s5.pc]? = some (.bCond cond.negate (pcMap l_var)) := by
              show prog[s4.pc + 1]? = _
              rw [hPC4]; exact hCodeTail.tail.tail.head
            simp only [BoolExpr.eval, Expr.eval, Value.toFloat] at hfcmp_false
            have hCondTrue : s5.flags.condHolds cond.negate = true := by
              show (fcmpFlags (s4.fregs .d1) (s4.fregs .d2)).condHolds
                cond.negate = true
              rw [hD1_s4, hD2_s4, Cond.negate_correct]
              cases fop <;>
                exact congrArg (!·) ((Flags.condHolds_float_correct _ fa fb).trans hfcmp_false)
            -- Step D: bCond
            let s_fin : ArmState := { s5 with pc := pcMap l_var }
            have hStepBCond : ArmStepsN prog s5 s_fin 1 :=
              ArmStepsN.single (.bCond_taken cond.negate (pcMap l_var) hBCond hCondTrue)
            have h14 : ArmStepsN prog s s4 (k12 + k34) := ArmStepsN_trans hSteps12N hSteps34N
            have h145 : ArmStepsN prog s s5 (k12 + k34 + 1) := ArmStepsN_trans h14 hStepFcmp
            have hChain : ArmStepsN prog s s_fin (k12 + k34 + 1 + 1) :=
              ArmStepsN_trans h145 hStepBCond
            refine ⟨s_fin, k12 + k34 + 1 + 1, hChain, ?_, ?_, rfl, ?_⟩
            · intro pc' σ' am' _hCfg
              rw [hInstrs, hk12, hk34]; simp [List.length_append]; omega
            · exact fun v loc hv => hRel4 v loc hv
            · show s_fin.arrayMem = am
              simp [s_fin, s5, hAM4_s2, hAM2_s, hArrayMem]
          | _ => rcases hSimpleB with ⟨_, h⟩ | ⟨_, h⟩ <;> simp at h
        | _ => rcases hSimpleA with ⟨_, h⟩ | ⟨_, h⟩ <;> simp at h
      | lit b =>
        -- be_var = .not (.lit b); codegen falls back to verifiedGenBoolExpr + cbnz
        have hInstrs : instrs = verifiedGenBoolExpr layout (.not (.lit b)) ++
            [.cbnz .x0 (pcMap l_var)] := by
          have := hSome; simp [verifiedGenInstr, hRC, hII, hSimpleBV] at this
          exact this.symm
        rw [hInstrs] at hCodeInstr hPcNext
        obtain ⟨s_fin, k_fin, hChain, hk_fin, hRel_fin, hPC_fin, hAM_fin⟩ :=
          cbnz_taken_chain prog layout pcMap (.not (.lit b)) l_var pc σ am s
            hStateRel hRegConv hPcRel hCodeInstr.append_left hCodeInstr.append_right
            tyCtx hTS hWTbe hWTL (fun v hv => hMapped v (by simp [TAC.vars]; exact hv))
            hSimpleBV hcond
        refine ⟨s_fin, k_fin, hChain, ?_, hRel_fin, hPC_fin, ?_⟩
        · intro pc' σ' am' _hCfg
          rw [hInstrs, hk_fin]; simp [List.length_append]
        · rw [hAM_fin]; exact hArrayMem
      | bvar v =>
        have hInstrs : instrs = verifiedGenBoolExpr layout (.not (.bvar v)) ++
            [.cbnz .x0 (pcMap l_var)] := by
          have := hSome; simp [verifiedGenInstr, hRC, hII, hSimpleBV] at this
          exact this.symm
        rw [hInstrs] at hCodeInstr hPcNext
        obtain ⟨s_fin, k_fin, hChain, hk_fin, hRel_fin, hPC_fin, hAM_fin⟩ :=
          cbnz_taken_chain prog layout pcMap (.not (.bvar v)) l_var pc σ am s
            hStateRel hRegConv hPcRel hCodeInstr.append_left hCodeInstr.append_right
            tyCtx hTS hWTbe hWTL (fun v hv => hMapped v (by simp [TAC.vars]; exact hv))
            hSimpleBV hcond
        refine ⟨s_fin, k_fin, hChain, ?_, hRel_fin, hPC_fin, ?_⟩
        · intro pc' σ' am' _hCfg
          rw [hInstrs, hk_fin]; simp [List.length_append]
        · rw [hAM_fin]; exact hArrayMem
      | not inner' =>
        have hInstrs : instrs = verifiedGenBoolExpr layout (.not (.not inner')) ++
            [.cbnz .x0 (pcMap l_var)] := by
          have := hSome; simp [verifiedGenInstr, hRC, hII, hSimpleBV] at this
          exact this.symm
        rw [hInstrs] at hCodeInstr hPcNext
        obtain ⟨s_fin, k_fin, hChain, hk_fin, hRel_fin, hPC_fin, hAM_fin⟩ :=
          cbnz_taken_chain prog layout pcMap (.not (.not inner')) l_var pc σ am s
            hStateRel hRegConv hPcRel hCodeInstr.append_left hCodeInstr.append_right
            tyCtx hTS hWTbe hWTL (fun v hv => hMapped v (by simp [TAC.vars]; exact hv))
            hSimpleBV hcond
        refine ⟨s_fin, k_fin, hChain, ?_, hRel_fin, hPC_fin, ?_⟩
        · intro pc' σ' am' _hCfg
          rw [hInstrs, hk_fin]; simp [List.length_append]
        · rw [hAM_fin]; exact hArrayMem
      | bexpr _ => simp [BoolExpr.hasSimpleOps] at hSimpleBV
    | lit b =>
      have hInstrs : instrs = verifiedGenBoolExpr layout (.lit b) ++
          [.cbnz .x0 (pcMap l_var)] := by
        have := hSome; simp [verifiedGenInstr, hRC, hII, hSimpleBV] at this
        exact this.symm
      rw [hInstrs] at hCodeInstr hPcNext
      obtain ⟨s_fin, k_fin, hChain, hk_fin, hRel_fin, hPC_fin, hAM_fin⟩ :=
        cbnz_taken_chain prog layout pcMap (.lit b) l_var pc σ am s
          hStateRel hRegConv hPcRel hCodeInstr.append_left hCodeInstr.append_right
          tyCtx hTS hWTbe hWTL (fun v hv => hMapped v (by simp [TAC.vars]; exact hv))
          hSimpleBV hcond
      refine ⟨s_fin, k_fin, hChain, ?_, hRel_fin, hPC_fin, ?_⟩
      · intro pc' σ' am' _hCfg
        rw [hInstrs, hk_fin]; simp [List.length_append]
      · rw [hAM_fin]; exact hArrayMem
    | bvar v =>
      have hInstrs : instrs = verifiedGenBoolExpr layout (.bvar v) ++
          [.cbnz .x0 (pcMap l_var)] := by
        have := hSome; simp [verifiedGenInstr, hRC, hII, hSimpleBV] at this
        exact this.symm
      rw [hInstrs] at hCodeInstr hPcNext
      obtain ⟨s_fin, k_fin, hChain, hk_fin, hRel_fin, hPC_fin, hAM_fin⟩ :=
        cbnz_taken_chain prog layout pcMap (.bvar v) l_var pc σ am s
          hStateRel hRegConv hPcRel hCodeInstr.append_left hCodeInstr.append_right
          tyCtx hTS hWTbe hWTL (fun v hv => hMapped v (by simp [TAC.vars]; exact hv))
          hSimpleBV hcond
      refine ⟨s_fin, k_fin, hChain, ?_, hRel_fin, hPC_fin, ?_⟩
      · intro pc' σ' am' _hCfg
        rw [hInstrs, hk_fin]; simp [List.length_append]
      · rw [hAM_fin]; exact hArrayMem
    | cmp op a b =>
      have hInstrs : instrs = verifiedGenBoolExpr layout (.cmp op a b) ++
          [.cbnz .x0 (pcMap l_var)] := by
        have := hSome; simp [verifiedGenInstr, hRC, hII, hSimpleBV] at this
        exact this.symm
      rw [hInstrs] at hCodeInstr hPcNext
      obtain ⟨s_fin, k_fin, hChain, hk_fin, hRel_fin, hPC_fin, hAM_fin⟩ :=
        cbnz_taken_chain prog layout pcMap (.cmp op a b) l_var pc σ am s
          hStateRel hRegConv hPcRel hCodeInstr.append_left hCodeInstr.append_right
          tyCtx hTS hWTbe hWTL (fun v hv => hMapped v (by simp [TAC.vars]; exact hv))
          hSimpleBV hcond
      refine ⟨s_fin, k_fin, hChain, ?_, hRel_fin, hPC_fin, ?_⟩
      · intro pc' σ' am' _hCfg
        rw [hInstrs, hk_fin]; simp [List.length_append]
      · rw [hAM_fin]; exact hArrayMem
    | fcmp fop a b =>
      have hInstrs : instrs = verifiedGenBoolExpr layout (.fcmp fop a b) ++
          [.cbnz .x0 (pcMap l_var)] := by
        have := hSome; simp [verifiedGenInstr, hRC, hII, hSimpleBV] at this
        exact this.symm
      rw [hInstrs] at hCodeInstr hPcNext
      obtain ⟨s_fin, k_fin, hChain, hk_fin, hRel_fin, hPC_fin, hAM_fin⟩ :=
        cbnz_taken_chain prog layout pcMap (.fcmp fop a b) l_var pc σ am s
          hStateRel hRegConv hPcRel hCodeInstr.append_left hCodeInstr.append_right
          tyCtx hTS hWTbe hWTL (fun v hv => hMapped v (by simp [TAC.vars]; exact hv))
          hSimpleBV hcond
      refine ⟨s_fin, k_fin, hChain, ?_, hRel_fin, hPC_fin, ?_⟩
      · intro pc' σ' am' _hCfg
        rw [hInstrs, hk_fin]; simp [List.length_append]
      · rw [hAM_fin]; exact hArrayMem
    | bexpr _ => simp [BoolExpr.hasSimpleOps] at hSimpleBV
  | iffall hinstr hcond =>
    rename_i be_var l_var
    have heq : instr = .ifgoto be_var l_var := Option.some.inj (hInstr.symm.trans hinstr)
    rw [heq] at hSome hMapped
    have hSimpleBV : be_var.hasSimpleOps = true := by
      cases hb : be_var.hasSimpleOps with
      | true => rfl
      | false => simp [verifiedGenInstr, hRC, hII, hb] at hSome
    have hWTbe : WellTypedBoolExpr tyCtx be_var := by
      have hwti := hWT pc hPC_bound
      have heq_i := Prog.getElem?_eq_getElem hPC_bound
      rw [hinstr] at heq_i; rw [← Option.some.inj heq_i] at hwti
      cases hwti with | ifgoto hbe => exact hbe
    cases be_var with
    | not inner =>
      cases inner with
      | cmp op a b =>
        have hSimpleCmp : (BoolExpr.cmp op a b).hasSimpleOps = true := hSimpleBV
        obtain ⟨hSimpleA, hSimpleB⟩ := BoolExpr.hasSimpleOps_cmp hSimpleCmp
        have hWTcmp : WellTypedBoolExpr tyCtx (.cmp op a b) := by
          cases hWTbe with | not h => exact h
        obtain ⟨ha_ty, hb_ty⟩ : ExprHasTy tyCtx a .int ∧ ExprHasTy tyCtx b .int := by
          cases hWTcmp with | cmp ha hb => exact ⟨ha, hb⟩
        have hcmp_true : BoolExpr.eval σ am (.cmp op a b) = true := by
          simp [BoolExpr.eval] at hcond; exact hcond
        cases a with
        | var va => cases b with
          | var vb =>
            have hNotFregA : ∀ r, layout va ≠ some (.freg r) := hWTL.int_not_freg ha_ty
            have hNotFregB : ∀ r, layout vb ≠ some (.freg r) := hWTL.int_not_freg hb_ty
            have hTyA := hTS va; rw [ha_ty] at hTyA
            have hTyB := hTS vb; rw [hb_ty] at hTyB
            obtain ⟨nA, hnA⟩ := Value.int_of_typeOf_int hTyA
            obtain ⟨nB, hnB⟩ := Value.int_of_typeOf_int hTyB
            let a_reg : ArmReg :=
              match List.lookup va layout.entries with | some (.ireg r) => r | _ => .x1
            let b_reg : ArmReg :=
              match List.lookup vb layout.entries with | some (.ireg r) => r | _ => .x2
            let cond : Cond := (fun o : CmpOp => match o with
              | .eq => Cond.eq | .ne => .ne | .lt => .lt | .le => .le) op
            have hInstrs : instrs = vLoadVar layout va a_reg ++ vLoadVar layout vb b_reg ++
                [.cmp a_reg b_reg, .bCond cond.negate (pcMap l_var)] := by
              have := hSome; simp [verifiedGenInstr, hRC, hII, hSimpleBV] at this
              rw [← List.append_assoc] at this
              exact this.symm
            rw [hInstrs] at hCodeInstr hPcNext
            have hCodeA := hCodeInstr.append_left.append_left
            have hCodeB := hCodeInstr.append_left.append_right
            have hCodeCmpBCond := hCodeInstr.append_right
            obtain ⟨s1, k1, hSteps1N, hk1, hVal1, hRel1, _, hPC1, hAM1, hRegs1⟩ :=
              vLoadVar_eff_exec prog layout va σ s (pcMap pc) .x1 hStateRel hRegConv hPcRel
                hNotFregA (Or.inr (Or.inl rfl))
                (hMapped va (by simp [TAC.vars, BoolExpr.vars, Expr.freeVars])) hCodeA
            have hk1' : k1 = (vLoadVar layout va a_reg).length := hk1
            obtain ⟨s2, k2, hSteps2N, hk2, hVal2, hRel2, _, hPC2_, hAM2, hRegs2⟩ :=
              vLoadVar_eff_exec prog layout vb σ s1
                (pcMap pc + (vLoadVar layout va a_reg).length) .x2
                hRel1 hRegConv hPC1 hNotFregB (Or.inr (Or.inr rfl))
                (hMapped vb (by simp [TAC.vars, BoolExpr.vars, Expr.freeVars])) hCodeB
            have hk2' : k2 = (vLoadVar layout vb b_reg).length := hk2
            have hPC2 : s2.pc = pcMap pc + (vLoadVar layout va a_reg ++
                vLoadVar layout vb b_reg).length := by
              rw [List.length_append, ← Nat.add_assoc]; exact hPC2_
            have hA_s2 : s2.regs a_reg = nA := by
              have := eff_ireg_val_preserved layout va σ s2 .x1 b_reg hRel2 hNotFregA
                hRegs2 hVal1 (x1_ne_eff_x2 layout vb hRegConv hNotFregB)
              rw [this, hnA]; rfl
            have hB_s2 : s2.regs b_reg = nB := by rw [hVal2, hnB]; rfl
            have hCmp := hCodeCmpBCond.head; rw [← hPC2] at hCmp
            let s3 := { s2 with flags := Flags.mk (s2.regs a_reg) (s2.regs b_reg), pc := s2.pc + 1 }
            have hStepCmpN : ArmStepsN prog s2 s3 1 :=
              ArmStepsN.single (.cmpRR a_reg b_reg hCmp)
            have hPC3 : s3.pc = pcMap pc + (vLoadVar layout va a_reg ++
                vLoadVar layout vb b_reg).length + 1 := by
              show s2.pc + 1 = _; rw [hPC2]
            have hBCond := hCodeCmpBCond.tail.head; rw [← hPC3] at hBCond
            simp only [BoolExpr.eval, Expr.eval, Value.toInt, hnA, hnB] at hcmp_true
            have hCondFalse : s3.flags.condHolds cond.negate = false := by
              show ({ lhs := s2.regs a_reg, rhs := s2.regs b_reg } : Flags).condHolds cond.negate = false
              rw [hA_s2, hB_s2, Cond.negate_correct]
              cases op <;> simp_all [cond, Flags.condHolds, CmpOp.eval,
                BitVec.sle_eq_not_slt, bne, BEq.beq]
            let s_fin : ArmState := s3.nextPC
            have hStepBCondN : ArmStepsN prog s3 s_fin 1 :=
              ArmStepsN.single (.bCond_fall cond.negate (pcMap l_var) hBCond hCondFalse)
            have h12 : ArmStepsN prog s s2 (k1 + k2) := ArmStepsN_trans hSteps1N hSteps2N
            have h123 : ArmStepsN prog s s3 (k1 + k2 + 1) := ArmStepsN_trans h12 hStepCmpN
            have hChain : ArmStepsN prog s s_fin (k1 + k2 + 1 + 1) :=
              ArmStepsN_trans h123 hStepBCondN
            refine ⟨s_fin, k1 + k2 + 1 + 1, hChain, ?_, ?_, ?_, ?_⟩
            · intro pc' σ' am' _hCfg
              rw [hInstrs, hk1', hk2']; simp [List.length_append]; omega
            · exact fun v loc hv => hRel2 v loc hv
            · show s_fin.pc = pcMap (pc + 1)
              have hLen := hPcNext σ am rfl
              show s3.pc + 1 = pcMap (pc + 1)
              rw [hPC3, hLen]; simp [List.length_append]; omega
            · show s_fin.arrayMem = am
              simp [s_fin, s3, ArmState.nextPC, hAM2, hAM1, hArrayMem]
          | lit nb =>
            have hNotFregA : ∀ r, layout va ≠ some (.freg r) := hWTL.int_not_freg ha_ty
            have hTyA := hTS va; rw [ha_ty] at hTyA
            obtain ⟨nA, hnA⟩ := Value.int_of_typeOf_int hTyA
            let a_reg : ArmReg :=
              match List.lookup va layout.entries with | some (.ireg r) => r | _ => .x1
            let cond : Cond := (fun o : CmpOp => match o with
              | .eq => Cond.eq | .ne => .ne | .lt => .lt | .le => .le) op
            have hInstrs : instrs = vLoadVar layout va a_reg ++ formalLoadImm64 .x2 nb ++
                [.cmp a_reg .x2, .bCond cond.negate (pcMap l_var)] := by
              have := hSome; simp [verifiedGenInstr, hRC, hII, hSimpleBV] at this
              rw [← List.append_assoc] at this
              exact this.symm
            rw [hInstrs] at hCodeInstr hPcNext
            have hCodeA := hCodeInstr.append_left.append_left
            have hCodeImm := hCodeInstr.append_left.append_right
            have hCodeCmpBCond := hCodeInstr.append_right
            obtain ⟨s1, k1, hSteps1N, hk1, hVal1, hRel1, _, hPC1, hAM1, hRegs1⟩ :=
              vLoadVar_eff_exec prog layout va σ s (pcMap pc) .x1 hStateRel hRegConv hPcRel
                hNotFregA (Or.inr (Or.inl rfl))
                (hMapped va (by simp [TAC.vars, BoolExpr.vars, Expr.freeVars])) hCodeA
            have hk1' : k1 = (vLoadVar layout va a_reg).length := hk1
            obtain ⟨s2, k2, hSteps2N, hk2, hFregs2, hX2, hStack2, hPC2_, hRegs2, hAM2⟩ :=
              loadImm64_fregs_preserved prog .x2 nb s1
                (pcMap pc + (vLoadVar layout va a_reg).length) hCodeImm hPC1
            have hRel2 := loadImm64_preserves_ExtStateRel prog layout .x2 nb σ s1 s2
                hRel1 hRegConv hStack2 hFregs2 hRegs2 hAM2 (Or.inr (Or.inr rfl))
            have hA_s2 : s2.regs a_reg = nA := by
              have := eff_ireg_val_preserved layout va σ s2 .x1 .x2 hRel2 hNotFregA
                hRegs2 hVal1 (by decide)
              rw [this, hnA]; rfl
            have hPC2 : s2.pc = pcMap pc + (vLoadVar layout va a_reg ++
                formalLoadImm64 .x2 nb).length := by
              rw [List.length_append, ← Nat.add_assoc]; exact hPC2_
            have hCmp := hCodeCmpBCond.head; rw [← hPC2] at hCmp
            let s3 : ArmState :=
              { s2 with flags := Flags.mk (s2.regs a_reg) (s2.regs .x2), pc := s2.pc + 1 }
            have hStepCmpN : ArmStepsN prog s2 s3 1 :=
              ArmStepsN.single (.cmpRR a_reg .x2 hCmp)
            have hPC3 : s3.pc = pcMap pc + (vLoadVar layout va a_reg ++
                formalLoadImm64 .x2 nb).length + 1 := by
              show s2.pc + 1 = _; rw [hPC2]
            have hBCond := hCodeCmpBCond.tail.head; rw [← hPC3] at hBCond
            simp only [BoolExpr.eval, Expr.eval, Value.toInt, hnA] at hcmp_true
            have hCondFalse : s3.flags.condHolds cond.negate = false := by
              show ({ lhs := s2.regs a_reg, rhs := s2.regs .x2 } : Flags).condHolds cond.negate = false
              rw [hA_s2, hX2, Cond.negate_correct]
              cases op <;> simp_all [cond, Flags.condHolds, CmpOp.eval,
                BitVec.sle_eq_not_slt, bne, BEq.beq]
            let s_fin : ArmState := s3.nextPC
            have hStepBCondN : ArmStepsN prog s3 s_fin 1 :=
              ArmStepsN.single (.bCond_fall cond.negate (pcMap l_var) hBCond hCondFalse)
            have h12 : ArmStepsN prog s s2 (k1 + k2) := ArmStepsN_trans hSteps1N hSteps2N
            have h123 : ArmStepsN prog s s3 (k1 + k2 + 1) := ArmStepsN_trans h12 hStepCmpN
            have hChain : ArmStepsN prog s s_fin (k1 + k2 + 1 + 1) :=
              ArmStepsN_trans h123 hStepBCondN
            refine ⟨s_fin, k1 + k2 + 1 + 1, hChain, ?_, ?_, ?_, ?_⟩
            · intro pc' σ' am' _hCfg
              rw [hInstrs, hk1', hk2]; simp [List.length_append]; omega
            · exact fun v loc hv => hRel2 v loc hv
            · show s_fin.pc = pcMap (pc + 1)
              have hLen := hPcNext σ am rfl
              show s3.pc + 1 = pcMap (pc + 1)
              rw [hPC3, hLen]; simp [List.length_append]; omega
            · show s_fin.arrayMem = am
              simp [s_fin, s3, ArmState.nextPC, hAM2, hAM1, hArrayMem]
          | _ => rcases hSimpleB with ⟨_, h⟩ | ⟨_, h⟩ <;> simp at h
        | lit na => cases b with
          | var vb =>
            have hNotFregB : ∀ r, layout vb ≠ some (.freg r) := hWTL.int_not_freg hb_ty
            have hTyB := hTS vb; rw [hb_ty] at hTyB
            obtain ⟨nB, hnB⟩ := Value.int_of_typeOf_int hTyB
            let b_reg : ArmReg :=
              match List.lookup vb layout.entries with | some (.ireg r) => r | _ => .x2
            let cond : Cond := (fun o : CmpOp => match o with
              | .eq => Cond.eq | .ne => .ne | .lt => .lt | .le => .le) op
            have hInstrs : instrs = formalLoadImm64 .x1 na ++ vLoadVar layout vb b_reg ++
                [.cmp .x1 b_reg, .bCond cond.negate (pcMap l_var)] := by
              have := hSome; simp [verifiedGenInstr, hRC, hII, hSimpleBV] at this
              rw [← List.append_assoc] at this
              exact this.symm
            rw [hInstrs] at hCodeInstr hPcNext
            have hCodeImm := hCodeInstr.append_left.append_left
            have hCodeB := hCodeInstr.append_left.append_right
            have hCodeCmpBCond := hCodeInstr.append_right
            obtain ⟨s1, k1, hSteps1N, hk1, hFregs1, hX1, hStack1, hPC1, hRegs1, hAM1⟩ :=
              loadImm64_fregs_preserved prog .x1 na s (pcMap pc) hCodeImm hPcRel
            have hRel1 := loadImm64_preserves_ExtStateRel prog layout .x1 na σ s s1
                hStateRel hRegConv hStack1 hFregs1 hRegs1 hAM1 (Or.inr (Or.inl rfl))
            obtain ⟨s2, k2, hSteps2N, hk2, hVal2, hRel2, _, hPC2_, hAM2, hRegs2⟩ :=
              vLoadVar_eff_exec prog layout vb σ s1
                (pcMap pc + (formalLoadImm64 .x1 na).length) .x2
                hRel1 hRegConv hPC1 hNotFregB (Or.inr (Or.inr rfl))
                (hMapped vb (by simp [TAC.vars, BoolExpr.vars, Expr.freeVars])) hCodeB
            have hk2' : k2 = (vLoadVar layout vb b_reg).length := hk2
            have hX1_s2 : s2.regs .x1 = na := by
              rw [hRegs2 .x1 (x1_ne_eff_x2 layout vb hRegConv hNotFregB)]; exact hX1
            have hB_s2 : s2.regs b_reg = nB := by rw [hVal2, hnB]; rfl
            have hPC2 : s2.pc = pcMap pc + (formalLoadImm64 .x1 na ++
                vLoadVar layout vb b_reg).length := by
              rw [List.length_append, ← Nat.add_assoc]; exact hPC2_
            have hCmp := hCodeCmpBCond.head; rw [← hPC2] at hCmp
            let s3 : ArmState :=
              { s2 with flags := Flags.mk (s2.regs .x1) (s2.regs b_reg), pc := s2.pc + 1 }
            have hStepCmpN : ArmStepsN prog s2 s3 1 :=
              ArmStepsN.single (.cmpRR .x1 b_reg hCmp)
            have hPC3 : s3.pc = pcMap pc + (formalLoadImm64 .x1 na ++
                vLoadVar layout vb b_reg).length + 1 := by
              show s2.pc + 1 = _; rw [hPC2]
            have hBCond := hCodeCmpBCond.tail.head; rw [← hPC3] at hBCond
            simp only [BoolExpr.eval, Expr.eval, Value.toInt, hnB] at hcmp_true
            have hCondFalse : s3.flags.condHolds cond.negate = false := by
              show ({ lhs := s2.regs .x1, rhs := s2.regs b_reg } : Flags).condHolds cond.negate = false
              rw [hX1_s2, hB_s2, Cond.negate_correct]
              cases op <;> simp_all [cond, Flags.condHolds, CmpOp.eval,
                BitVec.sle_eq_not_slt, bne, BEq.beq]
            let s_fin : ArmState := s3.nextPC
            have hStepBCondN : ArmStepsN prog s3 s_fin 1 :=
              ArmStepsN.single (.bCond_fall cond.negate (pcMap l_var) hBCond hCondFalse)
            have h12 : ArmStepsN prog s s2 (k1 + k2) := ArmStepsN_trans hSteps1N hSteps2N
            have h123 : ArmStepsN prog s s3 (k1 + k2 + 1) := ArmStepsN_trans h12 hStepCmpN
            have hChain : ArmStepsN prog s s_fin (k1 + k2 + 1 + 1) :=
              ArmStepsN_trans h123 hStepBCondN
            refine ⟨s_fin, k1 + k2 + 1 + 1, hChain, ?_, ?_, ?_, ?_⟩
            · intro pc' σ' am' _hCfg
              rw [hInstrs, hk1, hk2']; simp [List.length_append]; omega
            · exact fun v loc hv => hRel2 v loc hv
            · show s_fin.pc = pcMap (pc + 1)
              have hLen := hPcNext σ am rfl
              show s3.pc + 1 = pcMap (pc + 1)
              rw [hPC3, hLen]; simp [List.length_append]; omega
            · show s_fin.arrayMem = am
              simp [s_fin, s3, ArmState.nextPC, hAM2, hAM1, hArrayMem]
          | lit nb =>
            let cond : Cond := (fun o : CmpOp => match o with
              | .eq => Cond.eq | .ne => .ne | .lt => .lt | .le => .le) op
            have hInstrs : instrs = formalLoadImm64 .x1 na ++ formalLoadImm64 .x2 nb ++
                [.cmp .x1 .x2, .bCond cond.negate (pcMap l_var)] := by
              have := hSome; simp [verifiedGenInstr, hRC, hII, hSimpleBV] at this
              rw [← List.append_assoc] at this
              exact this.symm
            rw [hInstrs] at hCodeInstr hPcNext
            have hCodeImmA := hCodeInstr.append_left.append_left
            have hCodeImmB := hCodeInstr.append_left.append_right
            have hCodeCmpBCond := hCodeInstr.append_right
            obtain ⟨s1, k1, hSteps1N, hk1, hFregs1, hX1, hStack1, hPC1, hRegs1, hAM1⟩ :=
              loadImm64_fregs_preserved prog .x1 na s (pcMap pc) hCodeImmA hPcRel
            have hRel1 := loadImm64_preserves_ExtStateRel prog layout .x1 na σ s s1
                hStateRel hRegConv hStack1 hFregs1 hRegs1 hAM1 (Or.inr (Or.inl rfl))
            obtain ⟨s2, k2, hSteps2N, hk2, hFregs2, hX2, hStack2, hPC2_, hRegs2, hAM2⟩ :=
              loadImm64_fregs_preserved prog .x2 nb s1
                (pcMap pc + (formalLoadImm64 .x1 na).length) hCodeImmB hPC1
            have hRel2 := loadImm64_preserves_ExtStateRel prog layout .x2 nb σ s1 s2
                hRel1 hRegConv hStack2 hFregs2 hRegs2 hAM2 (Or.inr (Or.inr rfl))
            have hX1_s2 : s2.regs .x1 = na := by rw [hRegs2 .x1 (by decide)]; exact hX1
            have hPC2 : s2.pc = pcMap pc +
                (formalLoadImm64 .x1 na ++ formalLoadImm64 .x2 nb).length := by
              rw [List.length_append, ← Nat.add_assoc]; exact hPC2_
            have hCmp := hCodeCmpBCond.head; rw [← hPC2] at hCmp
            let s3 : ArmState :=
              { s2 with flags := Flags.mk (s2.regs .x1) (s2.regs .x2), pc := s2.pc + 1 }
            have hStepCmpN : ArmStepsN prog s2 s3 1 :=
              ArmStepsN.single (.cmpRR .x1 .x2 hCmp)
            have hPC3 : s3.pc = pcMap pc +
                (formalLoadImm64 .x1 na ++ formalLoadImm64 .x2 nb).length + 1 := by
              show s2.pc + 1 = _; rw [hPC2]
            have hBCond := hCodeCmpBCond.tail.head; rw [← hPC3] at hBCond
            simp only [BoolExpr.eval, Expr.eval, Value.toInt] at hcmp_true
            have hCondFalse : s3.flags.condHolds cond.negate = false := by
              show ({ lhs := s2.regs .x1, rhs := s2.regs .x2 } : Flags).condHolds cond.negate = false
              rw [hX1_s2, hX2, Cond.negate_correct]
              cases op <;> simp_all [cond, Flags.condHolds, CmpOp.eval,
                BitVec.sle_eq_not_slt, bne, BEq.beq]
            let s_fin : ArmState := s3.nextPC
            have hStepBCondN : ArmStepsN prog s3 s_fin 1 :=
              ArmStepsN.single (.bCond_fall cond.negate (pcMap l_var) hBCond hCondFalse)
            have h12 : ArmStepsN prog s s2 (k1 + k2) := ArmStepsN_trans hSteps1N hSteps2N
            have h123 : ArmStepsN prog s s3 (k1 + k2 + 1) := ArmStepsN_trans h12 hStepCmpN
            have hChain : ArmStepsN prog s s_fin (k1 + k2 + 1 + 1) :=
              ArmStepsN_trans h123 hStepBCondN
            refine ⟨s_fin, k1 + k2 + 1 + 1, hChain, ?_, ?_, ?_, ?_⟩
            · intro pc' σ' am' _hCfg
              rw [hInstrs, hk1, hk2]; simp [List.length_append]; omega
            · exact fun v loc hv => hRel2 v loc hv
            · show s_fin.pc = pcMap (pc + 1)
              have hLen := hPcNext σ am rfl
              show s3.pc + 1 = pcMap (pc + 1)
              rw [hPC3, hLen]; simp [List.length_append]; omega
            · show s_fin.arrayMem = am
              simp [s_fin, s3, ArmState.nextPC, hAM2, hAM1, hArrayMem]
          | _ => rcases hSimpleB with ⟨_, h⟩ | ⟨_, h⟩ <;> simp at h
        | _ => rcases hSimpleA with ⟨_, h⟩ | ⟨_, h⟩ <;> simp at h
      | fcmp fop a b =>
        have hSimpleFcmp : (BoolExpr.fcmp fop a b).hasSimpleOps = true := hSimpleBV
        obtain ⟨hSimpleA, hSimpleB⟩ := BoolExpr.hasSimpleOps_fcmp hSimpleFcmp
        have hWTfcmp : WellTypedBoolExpr tyCtx (.fcmp fop a b) := by
          cases hWTbe with | not h => exact h
        obtain ⟨ha_ty, hb_ty⟩ : ExprHasTy tyCtx a .float ∧ ExprHasTy tyCtx b .float := by
          cases hWTfcmp with | fcmp ha hb => exact ⟨ha, hb⟩
        have hfcmp_true : BoolExpr.eval σ am (.fcmp fop a b) = true := by
          simp [BoolExpr.eval] at hcond; exact hcond
        let cond : Cond := (fun f : FloatCmpOp => match f with
          | .feq => Cond.eq | .fne => .ne | .flt => .lt | .fle => .le) fop
        cases a with
        | var va => cases b with
          | var vb =>
            have hNotIregA : ∀ r, layout va ≠ some (.ireg r) := hWTL.float_not_ireg ha_ty
            have hNotIregB : ∀ r, layout vb ≠ some (.ireg r) := hWTL.float_not_ireg hb_ty
            have hTyA := hTS va; rw [ha_ty] at hTyA
            have hTyB := hTS vb; rw [hb_ty] at hTyB
            obtain ⟨fA, hfA⟩ := Value.float_of_typeOf_float hTyA
            obtain ⟨fB, hfB⟩ := Value.float_of_typeOf_float hTyB
            let a_freg : ArmFReg :=
              match List.lookup va layout.entries with | some (.freg r) => r | _ => .d1
            let b_freg : ArmFReg :=
              match List.lookup vb layout.entries with | some (.freg r) => r | _ => .d2
            have hInstrs : instrs = vLoadVarFP layout va a_freg ++ vLoadVarFP layout vb b_freg ++
                [.fcmpR a_freg b_freg, .bCond cond.negate (pcMap l_var)] := by
              have := hSome; simp [verifiedGenInstr, hRC, hII, hSimpleBV] at this
              rw [← List.append_assoc] at this
              exact this.symm
            rw [hInstrs] at hCodeInstr hPcNext
            have hCodeA := hCodeInstr.append_left.append_left
            have hCodeB := hCodeInstr.append_left.append_right
            have hCodeFcmpBCond := hCodeInstr.append_right
            obtain ⟨s1, k1, hSteps1N, hk1, hVal1, hRel1, _, hPC1, hAM1, hFregs1, _⟩ :=
              vLoadVarFP_eff_exec prog layout va σ s (pcMap pc) .d1 hStateRel hRegConv hPcRel
                hNotIregA (Or.inr (Or.inl rfl))
                (hMapped va (by simp [TAC.vars, BoolExpr.vars, Expr.freeVars])) hCodeA
            have hk1' : k1 = (vLoadVarFP layout va a_freg).length := hk1
            obtain ⟨s2, k2, hSteps2N, hk2, hVal2, hRel2, _, hPC2_, hAM2, hFregs2, _⟩ :=
              vLoadVarFP_eff_exec prog layout vb σ s1
                (pcMap pc + (vLoadVarFP layout va a_freg).length) .d2
                hRel1 hRegConv hPC1 hNotIregB (Or.inr (Or.inr rfl))
                (hMapped vb (by simp [TAC.vars, BoolExpr.vars, Expr.freeVars])) hCodeB
            have hk2' : k2 = (vLoadVarFP layout vb b_freg).length := hk2
            have hPC2 : s2.pc = pcMap pc + (vLoadVarFP layout va a_freg ++
                vLoadVarFP layout vb b_freg).length := by
              rw [List.length_append, ← Nat.add_assoc]; exact hPC2_
            have hA_s2 : s2.fregs a_freg = fA := by
              have := eff_freg_val_preserved layout va σ s2 .d1 b_freg hRel2 hNotIregA
                hFregs2 hVal1 (d1_ne_eff_d2 layout vb hRegConv hNotIregB)
              rw [this, hfA]; rfl
            have hB_s2 : s2.fregs b_freg = fB := by rw [hVal2, hfB]; rfl
            have hFcmpI := hCodeFcmpBCond.head; rw [← hPC2] at hFcmpI
            let s3 : ArmState :=
              { s2 with flags := fcmpFlags (s2.fregs a_freg) (s2.fregs b_freg), pc := s2.pc + 1 }
            have hStepFcmpN : ArmStepsN prog s2 s3 1 :=
              ArmStepsN.single (.fcmpRR a_freg b_freg hFcmpI)
            have hPC3 : s3.pc = pcMap pc + (vLoadVarFP layout va a_freg ++
                vLoadVarFP layout vb b_freg).length + 1 := by
              show s2.pc + 1 = _; rw [hPC2]
            have hBCond := hCodeFcmpBCond.tail.head; rw [← hPC3] at hBCond
            simp only [BoolExpr.eval, Expr.eval, Value.toFloat, hfA, hfB] at hfcmp_true
            have hCondFalse : s3.flags.condHolds cond.negate = false := by
              show (fcmpFlags (s2.fregs a_freg) (s2.fregs b_freg)).condHolds
                cond.negate = false
              rw [hA_s2, hB_s2, Cond.negate_correct]
              cases fop <;>
                exact congrArg (!·) ((Flags.condHolds_float_correct _ fA fB).trans hfcmp_true)
            let s_fin : ArmState := s3.nextPC
            have hStepBCondN : ArmStepsN prog s3 s_fin 1 :=
              ArmStepsN.single (.bCond_fall cond.negate (pcMap l_var) hBCond hCondFalse)
            have h12 : ArmStepsN prog s s2 (k1 + k2) := ArmStepsN_trans hSteps1N hSteps2N
            have h123 : ArmStepsN prog s s3 (k1 + k2 + 1) := ArmStepsN_trans h12 hStepFcmpN
            have hChain : ArmStepsN prog s s_fin (k1 + k2 + 1 + 1) :=
              ArmStepsN_trans h123 hStepBCondN
            refine ⟨s_fin, k1 + k2 + 1 + 1, hChain, ?_, ?_, ?_, ?_⟩
            · intro pc' σ' am' _hCfg
              rw [hInstrs, hk1', hk2']; simp [List.length_append]; omega
            · exact fun v loc hv => hRel2 v loc hv
            · show s_fin.pc = pcMap (pc + 1)
              have hLen := hPcNext σ am rfl
              show s3.pc + 1 = pcMap (pc + 1)
              rw [hPC3, hLen]; simp [List.length_append]; omega
            · show s_fin.arrayMem = am
              simp [s_fin, s3, ArmState.nextPC, hAM2, hAM1, hArrayMem]
          | flit fb =>
            have hNotIregA : ∀ r, layout va ≠ some (.ireg r) := hWTL.float_not_ireg ha_ty
            have hTyA := hTS va; rw [ha_ty] at hTyA
            obtain ⟨fA, hfA⟩ := Value.float_of_typeOf_float hTyA
            let a_freg : ArmFReg :=
              match List.lookup va layout.entries with | some (.freg r) => r | _ => .d1
            have hInstrs : instrs = vLoadVarFP layout va a_freg ++ formalLoadImm64 .x0 fb ++
                [.fmovToFP .d2 .x0, .fcmpR a_freg .d2, .bCond cond.negate (pcMap l_var)] := by
              have := hSome; simp [verifiedGenInstr, hRC, hII, hSimpleBV] at this
              rw [← List.append_assoc] at this
              exact this.symm
            rw [hInstrs] at hCodeInstr hPcNext
            have hCodeA := hCodeInstr.append_left.append_left
            have hCodeImm := hCodeInstr.append_left.append_right
            have hCodeTail := hCodeInstr.append_right
            obtain ⟨s1, k1, hSteps1N, hk1, hVal1, hRel1, _, hPC1, hAM1, hFregs1, _⟩ :=
              vLoadVarFP_eff_exec prog layout va σ s (pcMap pc) .d1 hStateRel hRegConv hPcRel
                hNotIregA (Or.inr (Or.inl rfl))
                (hMapped va (by simp [TAC.vars, BoolExpr.vars, Expr.freeVars])) hCodeA
            have hk1' : k1 = (vLoadVarFP layout va a_freg).length := hk1
            have hFmov_at : prog[pcMap pc + (vLoadVarFP layout va a_freg).length
                + (formalLoadImm64 .x0 fb).length]? = some (.fmovToFP .d2 .x0) := by
              have := hCodeTail.head
              rw [List.length_append, ← Nat.add_assoc] at this
              exact this
            obtain ⟨s3, k23, hSteps23N, hk23, hD2_s3, hRel3, hPC3_raw, hAM3_s1, hFregs_s3_to_s1⟩ :=
              loadFlit_chain prog layout .d2 fb σ s1
                (pcMap pc + (vLoadVarFP layout va a_freg).length) hRel1 hRegConv hPC1
                hCodeImm hFmov_at (Or.inr (Or.inr rfl))
            have hPC3 : s3.pc = pcMap pc +
                (vLoadVarFP layout va a_freg ++ formalLoadImm64 .x0 fb).length + 1 := by
              rw [List.length_append]; rw [hPC3_raw]; omega
            have hA_s3 : s3.fregs a_freg = fA := by
              have := eff_freg_val_preserved layout va σ s3 .d1 .d2 hRel3 hNotIregA
                hFregs_s3_to_s1 hVal1 (by decide)
              rw [this, hfA]; rfl
            have hFcmpI := hCodeTail.tail.head; rw [← hPC3] at hFcmpI
            let s4 : ArmState :=
              { s3 with flags := fcmpFlags (s3.fregs a_freg) (s3.fregs .d2), pc := s3.pc + 1 }
            have hStepFcmpN : ArmStepsN prog s3 s4 1 :=
              ArmStepsN.single (.fcmpRR a_freg .d2 hFcmpI)
            have hPC4 : s4.pc = pcMap pc +
                (vLoadVarFP layout va a_freg ++ formalLoadImm64 .x0 fb).length + 1 + 1 := by
              show s3.pc + 1 = _; rw [hPC3]
            have hBCond := hCodeTail.tail.tail.head; rw [← hPC4] at hBCond
            simp only [BoolExpr.eval, Expr.eval, Value.toFloat, hfA] at hfcmp_true
            have hCondFalse : s4.flags.condHolds cond.negate = false := by
              show (fcmpFlags (s3.fregs a_freg) (s3.fregs .d2)).condHolds
                cond.negate = false
              rw [hA_s3, hD2_s3, Cond.negate_correct]
              cases fop <;>
                exact congrArg (!·) ((Flags.condHolds_float_correct _ fA fb).trans hfcmp_true)
            let s_fin : ArmState := s4.nextPC
            have hStepBCondN : ArmStepsN prog s4 s_fin 1 :=
              ArmStepsN.single (.bCond_fall cond.negate (pcMap l_var) hBCond hCondFalse)
            have h13 : ArmStepsN prog s s3 (k1 + k23) := ArmStepsN_trans hSteps1N hSteps23N
            have h134 : ArmStepsN prog s s4 (k1 + k23 + 1) := ArmStepsN_trans h13 hStepFcmpN
            have hChain : ArmStepsN prog s s_fin (k1 + k23 + 1 + 1) :=
              ArmStepsN_trans h134 hStepBCondN
            refine ⟨s_fin, k1 + k23 + 1 + 1, hChain, ?_, ?_, ?_, ?_⟩
            · intro pc' σ' am' _hCfg
              rw [hInstrs, hk1', hk23]; simp [List.length_append]; omega
            · exact fun v loc hv => hRel3 v loc hv
            · show s_fin.pc = pcMap (pc + 1)
              have hLen := hPcNext σ am rfl
              show s4.pc + 1 = pcMap (pc + 1)
              rw [hPC4, hLen]; simp [List.length_append]; omega
            · show s_fin.arrayMem = am
              simp [s_fin, s4, ArmState.nextPC, hAM3_s1, hAM1, hArrayMem]
          | _ => rcases hSimpleB with ⟨_, h⟩ | ⟨_, h⟩ <;> simp at h
        | flit fa => cases b with
          | var vb =>
            have hNotIregB : ∀ r, layout vb ≠ some (.ireg r) := hWTL.float_not_ireg hb_ty
            have hTyB := hTS vb; rw [hb_ty] at hTyB
            obtain ⟨fB, hfB⟩ := Value.float_of_typeOf_float hTyB
            let b_freg : ArmFReg :=
              match List.lookup vb layout.entries with | some (.freg r) => r | _ => .d2
            have hInstrs : instrs = vLoadVarFP layout vb b_freg ++ formalLoadImm64 .x0 fa ++
                [.fmovToFP .d1 .x0, .fcmpR .d1 b_freg, .bCond cond.negate (pcMap l_var)] := by
              have := hSome; simp [verifiedGenInstr, hRC, hII, hSimpleBV] at this
              rw [← List.append_assoc] at this
              exact this.symm
            rw [hInstrs] at hCodeInstr hPcNext
            have hCodeB := hCodeInstr.append_left.append_left
            have hCodeImm := hCodeInstr.append_left.append_right
            have hCodeTail := hCodeInstr.append_right
            obtain ⟨s1, k1, hSteps1N, hk1, hVal1, hRel1, _, hPC1, hAM1, hFregs1, _⟩ :=
              vLoadVarFP_eff_exec prog layout vb σ s (pcMap pc) .d2 hStateRel hRegConv hPcRel
                hNotIregB (Or.inr (Or.inr rfl))
                (hMapped vb (by simp [TAC.vars, BoolExpr.vars, Expr.freeVars])) hCodeB
            have hk1' : k1 = (vLoadVarFP layout vb b_freg).length := hk1
            have hFmov_at : prog[pcMap pc + (vLoadVarFP layout vb b_freg).length
                + (formalLoadImm64 .x0 fa).length]? = some (.fmovToFP .d1 .x0) := by
              have := hCodeTail.head
              rw [List.length_append, ← Nat.add_assoc] at this
              exact this
            obtain ⟨s3, k23, hSteps23N, hk23, hD1_s3, hRel3, hPC3_raw, hAM3_s1, hFregs_s3_to_s1⟩ :=
              loadFlit_chain prog layout .d1 fa σ s1
                (pcMap pc + (vLoadVarFP layout vb b_freg).length) hRel1 hRegConv hPC1
                hCodeImm hFmov_at (Or.inr (Or.inl rfl))
            have hPC3 : s3.pc = pcMap pc +
                (vLoadVarFP layout vb b_freg ++ formalLoadImm64 .x0 fa).length + 1 := by
              rw [List.length_append]; rw [hPC3_raw]; omega
            have hB_s3 : s3.fregs b_freg = fB := by
              have := eff_freg_val_preserved layout vb σ s3 .d2 .d1 hRel3 hNotIregB
                hFregs_s3_to_s1 hVal1 (by decide)
              rw [this, hfB]; rfl
            have hFcmpI := hCodeTail.tail.head; rw [← hPC3] at hFcmpI
            let s4 : ArmState :=
              { s3 with flags := fcmpFlags (s3.fregs .d1) (s3.fregs b_freg), pc := s3.pc + 1 }
            have hStepFcmpN : ArmStepsN prog s3 s4 1 :=
              ArmStepsN.single (.fcmpRR .d1 b_freg hFcmpI)
            have hPC4 : s4.pc = pcMap pc +
                (vLoadVarFP layout vb b_freg ++ formalLoadImm64 .x0 fa).length + 1 + 1 := by
              show s3.pc + 1 = _; rw [hPC3]
            have hBCond := hCodeTail.tail.tail.head; rw [← hPC4] at hBCond
            simp only [BoolExpr.eval, Expr.eval, Value.toFloat, hfB] at hfcmp_true
            have hCondFalse : s4.flags.condHolds cond.negate = false := by
              show (fcmpFlags (s3.fregs .d1) (s3.fregs b_freg)).condHolds
                cond.negate = false
              rw [hD1_s3, hB_s3, Cond.negate_correct]
              cases fop <;>
                exact congrArg (!·) ((Flags.condHolds_float_correct _ fa fB).trans hfcmp_true)
            let s_fin : ArmState := s4.nextPC
            have hStepBCondN : ArmStepsN prog s4 s_fin 1 :=
              ArmStepsN.single (.bCond_fall cond.negate (pcMap l_var) hBCond hCondFalse)
            have h13 : ArmStepsN prog s s3 (k1 + k23) := ArmStepsN_trans hSteps1N hSteps23N
            have h134 : ArmStepsN prog s s4 (k1 + k23 + 1) := ArmStepsN_trans h13 hStepFcmpN
            have hChain : ArmStepsN prog s s_fin (k1 + k23 + 1 + 1) :=
              ArmStepsN_trans h134 hStepBCondN
            refine ⟨s_fin, k1 + k23 + 1 + 1, hChain, ?_, ?_, ?_, ?_⟩
            · intro pc' σ' am' _hCfg
              rw [hInstrs, hk1', hk23]; simp [List.length_append]; omega
            · exact fun v loc hv => hRel3 v loc hv
            · show s_fin.pc = pcMap (pc + 1)
              have hLen := hPcNext σ am rfl
              show s4.pc + 1 = pcMap (pc + 1)
              rw [hPC4, hLen]; simp [List.length_append]; omega
            · show s_fin.arrayMem = am
              simp [s_fin, s4, ArmState.nextPC, hAM3_s1, hAM1, hArrayMem]
          | flit fb =>
            have hInstrs : instrs = formalLoadImm64 .x0 fa ++
                (.fmovToFP .d1 .x0 :: (formalLoadImm64 .x0 fb ++
                  [.fmovToFP .d2 .x0, .fcmpR .d1 .d2,
                   .bCond cond.negate (pcMap l_var)])) := by
              have := hSome; simp [verifiedGenInstr, hRC, hII, hSimpleBV] at this
              exact this.symm
            rw [hInstrs] at hCodeInstr hPcNext
            have hCodeImmA := hCodeInstr.append_left
            have hCodeRest := hCodeInstr.append_right
            have hCodeFmovA := hCodeRest.head
            have hCodeAfterFmovA := hCodeRest.tail
            have hCodeImmB := hCodeAfterFmovA.append_left
            have hCodeTail := hCodeAfterFmovA.append_right
            obtain ⟨s2, k12, hSteps12N, hk12, hD1_s2, hRel2, hPC2, hAM2_s, hFregs_s2_to_s⟩ :=
              loadFlit_chain prog layout .d1 fa σ s (pcMap pc)
                hStateRel hRegConv hPcRel hCodeImmA hCodeFmovA (Or.inr (Or.inl rfl))
            have hFmov_atB : prog[s2.pc + (formalLoadImm64 .x0 fb).length]?
                = some (.fmovToFP .d2 .x0) := by
              rw [hPC2]; exact hCodeTail.head
            have hCodeImmB' : CodeAt prog s2.pc (formalLoadImm64 .x0 fb) := by
              rw [hPC2]; exact hCodeImmB
            obtain ⟨s4, k34, hSteps34N, hk34, hD2_s4, hRel4, hPC4_raw, hAM4_s2, hFregs_s4_to_s2⟩ :=
              loadFlit_chain prog layout .d2 fb σ s2 s2.pc
                hRel2 hRegConv rfl hCodeImmB' hFmov_atB (Or.inr (Or.inr rfl))
            have hPC4 : s4.pc = pcMap pc + (formalLoadImm64 .x0 fa).length + 1
                + (formalLoadImm64 .x0 fb).length + 1 := by
              rw [hPC4_raw, hPC2]
            have hD1_s4 : s4.fregs .d1 = fa := by
              rw [hFregs_s4_to_s2 .d1 (by decide)]; exact hD1_s2
            have hFcmpI : prog[s4.pc]? = some (.fcmpR .d1 .d2) := by
              rw [hPC4]; exact hCodeTail.tail.head
            let s5 : ArmState :=
              { s4 with flags := fcmpFlags (s4.fregs .d1) (s4.fregs .d2), pc := s4.pc + 1 }
            have hStepFcmp : ArmStepsN prog s4 s5 1 :=
              ArmStepsN.single (.fcmpRR .d1 .d2 hFcmpI)
            have hBCond : prog[s5.pc]? = some (.bCond cond.negate (pcMap l_var)) := by
              show prog[s4.pc + 1]? = _
              rw [hPC4]; exact hCodeTail.tail.tail.head
            simp only [BoolExpr.eval, Expr.eval, Value.toFloat] at hfcmp_true
            have hCondFalse : s5.flags.condHolds cond.negate = false := by
              show (fcmpFlags (s4.fregs .d1) (s4.fregs .d2)).condHolds
                cond.negate = false
              rw [hD1_s4, hD2_s4, Cond.negate_correct]
              cases fop <;>
                exact congrArg (!·) ((Flags.condHolds_float_correct _ fa fb).trans hfcmp_true)
            let s_fin : ArmState := s5.nextPC
            have hStepBCond : ArmStepsN prog s5 s_fin 1 :=
              ArmStepsN.single (.bCond_fall cond.negate (pcMap l_var) hBCond hCondFalse)
            have h14 : ArmStepsN prog s s4 (k12 + k34) := ArmStepsN_trans hSteps12N hSteps34N
            have h145 : ArmStepsN prog s s5 (k12 + k34 + 1) := ArmStepsN_trans h14 hStepFcmp
            have hChain : ArmStepsN prog s s_fin (k12 + k34 + 1 + 1) :=
              ArmStepsN_trans h145 hStepBCond
            refine ⟨s_fin, k12 + k34 + 1 + 1, hChain, ?_, ?_, ?_, ?_⟩
            · intro pc' σ' am' _hCfg
              rw [hInstrs, hk12, hk34]; simp [List.length_append]; omega
            · exact fun v loc hv => hRel4 v loc hv
            · show s_fin.pc = pcMap (pc + 1)
              have hLen := hPcNext σ am rfl
              show s5.pc + 1 = pcMap (pc + 1)
              show s4.pc + 1 + 1 = pcMap (pc + 1)
              rw [hPC4, hLen]; simp [List.length_append]; omega
            · show s_fin.arrayMem = am
              simp [s_fin, s5, ArmState.nextPC, hAM4_s2, hAM2_s, hArrayMem]
          | _ => rcases hSimpleB with ⟨_, h⟩ | ⟨_, h⟩ <;> simp at h
        | _ => rcases hSimpleA with ⟨_, h⟩ | ⟨_, h⟩ <;> simp at h
      | lit b =>
        have hInstrs : instrs = verifiedGenBoolExpr layout (.not (.lit b)) ++
            [.cbnz .x0 (pcMap l_var)] := by
          have := hSome; simp [verifiedGenInstr, hRC, hII, hSimpleBV] at this
          exact this.symm
        rw [hInstrs] at hCodeInstr hPcNext
        obtain ⟨s_fin, k_fin, hChain, hk_fin, hRel_fin, hPC_fin, hAM_fin⟩ :=
          cbnz_fall_chain prog layout pcMap (.not (.lit b)) l_var pc σ am s
            hStateRel hRegConv hPcRel hCodeInstr.append_left hCodeInstr.append_right
            tyCtx hTS hWTbe hWTL (fun v hv => hMapped v (by simp [TAC.vars]; exact hv))
            hSimpleBV hcond
        refine ⟨s_fin, k_fin, hChain, ?_, hRel_fin, ?_, ?_⟩
        · intro pc' σ' am' _hCfg
          rw [hInstrs, hk_fin]; simp [List.length_append]
        · show s_fin.pc = pcMap (pc + 1)
          have hLen := hPcNext σ am rfl
          rw [hPC_fin, hLen]; simp [List.length_append]; omega
        · rw [hAM_fin]; exact hArrayMem
      | bvar v =>
        have hInstrs : instrs = verifiedGenBoolExpr layout (.not (.bvar v)) ++
            [.cbnz .x0 (pcMap l_var)] := by
          have := hSome; simp [verifiedGenInstr, hRC, hII, hSimpleBV] at this
          exact this.symm
        rw [hInstrs] at hCodeInstr hPcNext
        obtain ⟨s_fin, k_fin, hChain, hk_fin, hRel_fin, hPC_fin, hAM_fin⟩ :=
          cbnz_fall_chain prog layout pcMap (.not (.bvar v)) l_var pc σ am s
            hStateRel hRegConv hPcRel hCodeInstr.append_left hCodeInstr.append_right
            tyCtx hTS hWTbe hWTL (fun v hv => hMapped v (by simp [TAC.vars]; exact hv))
            hSimpleBV hcond
        refine ⟨s_fin, k_fin, hChain, ?_, hRel_fin, ?_, ?_⟩
        · intro pc' σ' am' _hCfg
          rw [hInstrs, hk_fin]; simp [List.length_append]
        · show s_fin.pc = pcMap (pc + 1)
          have hLen := hPcNext σ am rfl
          rw [hPC_fin, hLen]; simp [List.length_append]; omega
        · rw [hAM_fin]; exact hArrayMem
      | not inner' =>
        have hInstrs : instrs = verifiedGenBoolExpr layout (.not (.not inner')) ++
            [.cbnz .x0 (pcMap l_var)] := by
          have := hSome; simp [verifiedGenInstr, hRC, hII, hSimpleBV] at this
          exact this.symm
        rw [hInstrs] at hCodeInstr hPcNext
        obtain ⟨s_fin, k_fin, hChain, hk_fin, hRel_fin, hPC_fin, hAM_fin⟩ :=
          cbnz_fall_chain prog layout pcMap (.not (.not inner')) l_var pc σ am s
            hStateRel hRegConv hPcRel hCodeInstr.append_left hCodeInstr.append_right
            tyCtx hTS hWTbe hWTL (fun v hv => hMapped v (by simp [TAC.vars]; exact hv))
            hSimpleBV hcond
        refine ⟨s_fin, k_fin, hChain, ?_, hRel_fin, ?_, ?_⟩
        · intro pc' σ' am' _hCfg
          rw [hInstrs, hk_fin]; simp [List.length_append]
        · show s_fin.pc = pcMap (pc + 1)
          have hLen := hPcNext σ am rfl
          rw [hPC_fin, hLen]; simp [List.length_append]; omega
        · rw [hAM_fin]; exact hArrayMem
      | bexpr _ => simp [BoolExpr.hasSimpleOps] at hSimpleBV
    | lit b =>
      have hInstrs : instrs = verifiedGenBoolExpr layout (.lit b) ++
          [.cbnz .x0 (pcMap l_var)] := by
        have := hSome; simp [verifiedGenInstr, hRC, hII, hSimpleBV] at this
        exact this.symm
      rw [hInstrs] at hCodeInstr hPcNext
      obtain ⟨s_fin, k_fin, hChain, hk_fin, hRel_fin, hPC_fin, hAM_fin⟩ :=
        cbnz_fall_chain prog layout pcMap (.lit b) l_var pc σ am s
          hStateRel hRegConv hPcRel hCodeInstr.append_left hCodeInstr.append_right
          tyCtx hTS hWTbe hWTL (fun v hv => hMapped v (by simp [TAC.vars]; exact hv))
          hSimpleBV hcond
      refine ⟨s_fin, k_fin, hChain, ?_, hRel_fin, ?_, ?_⟩
      · intro pc' σ' am' _hCfg
        rw [hInstrs, hk_fin]; simp [List.length_append]
      · show s_fin.pc = pcMap (pc + 1)
        have hLen := hPcNext σ am rfl
        rw [hPC_fin, hLen]; simp [List.length_append]; omega
      · rw [hAM_fin]; exact hArrayMem
    | bvar v =>
      have hInstrs : instrs = verifiedGenBoolExpr layout (.bvar v) ++
          [.cbnz .x0 (pcMap l_var)] := by
        have := hSome; simp [verifiedGenInstr, hRC, hII, hSimpleBV] at this
        exact this.symm
      rw [hInstrs] at hCodeInstr hPcNext
      obtain ⟨s_fin, k_fin, hChain, hk_fin, hRel_fin, hPC_fin, hAM_fin⟩ :=
        cbnz_fall_chain prog layout pcMap (.bvar v) l_var pc σ am s
          hStateRel hRegConv hPcRel hCodeInstr.append_left hCodeInstr.append_right
          tyCtx hTS hWTbe hWTL (fun v hv => hMapped v (by simp [TAC.vars]; exact hv))
          hSimpleBV hcond
      refine ⟨s_fin, k_fin, hChain, ?_, hRel_fin, ?_, ?_⟩
      · intro pc' σ' am' _hCfg
        rw [hInstrs, hk_fin]; simp [List.length_append]
      · show s_fin.pc = pcMap (pc + 1)
        have hLen := hPcNext σ am rfl
        rw [hPC_fin, hLen]; simp [List.length_append]; omega
      · rw [hAM_fin]; exact hArrayMem
    | cmp op a b =>
      have hInstrs : instrs = verifiedGenBoolExpr layout (.cmp op a b) ++
          [.cbnz .x0 (pcMap l_var)] := by
        have := hSome; simp [verifiedGenInstr, hRC, hII, hSimpleBV] at this
        exact this.symm
      rw [hInstrs] at hCodeInstr hPcNext
      obtain ⟨s_fin, k_fin, hChain, hk_fin, hRel_fin, hPC_fin, hAM_fin⟩ :=
        cbnz_fall_chain prog layout pcMap (.cmp op a b) l_var pc σ am s
          hStateRel hRegConv hPcRel hCodeInstr.append_left hCodeInstr.append_right
          tyCtx hTS hWTbe hWTL (fun v hv => hMapped v (by simp [TAC.vars]; exact hv))
          hSimpleBV hcond
      refine ⟨s_fin, k_fin, hChain, ?_, hRel_fin, ?_, ?_⟩
      · intro pc' σ' am' _hCfg
        rw [hInstrs, hk_fin]; simp [List.length_append]
      · show s_fin.pc = pcMap (pc + 1)
        have hLen := hPcNext σ am rfl
        rw [hPC_fin, hLen]; simp [List.length_append]; omega
      · rw [hAM_fin]; exact hArrayMem
    | fcmp fop a b =>
      have hInstrs : instrs = verifiedGenBoolExpr layout (.fcmp fop a b) ++
          [.cbnz .x0 (pcMap l_var)] := by
        have := hSome; simp [verifiedGenInstr, hRC, hII, hSimpleBV] at this
        exact this.symm
      rw [hInstrs] at hCodeInstr hPcNext
      obtain ⟨s_fin, k_fin, hChain, hk_fin, hRel_fin, hPC_fin, hAM_fin⟩ :=
        cbnz_fall_chain prog layout pcMap (.fcmp fop a b) l_var pc σ am s
          hStateRel hRegConv hPcRel hCodeInstr.append_left hCodeInstr.append_right
          tyCtx hTS hWTbe hWTL (fun v hv => hMapped v (by simp [TAC.vars]; exact hv))
          hSimpleBV hcond
      refine ⟨s_fin, k_fin, hChain, ?_, hRel_fin, ?_, ?_⟩
      · intro pc' σ' am' _hCfg
        rw [hInstrs, hk_fin]; simp [List.length_append]
      · show s_fin.pc = pcMap (pc + 1)
        have hLen := hPcNext σ am rfl
        rw [hPC_fin, hLen]; simp [List.length_append]; omega
      · rw [hAM_fin]; exact hArrayMem
    | bexpr _ => simp [BoolExpr.hasSimpleOps] at hSimpleBV
  | arrLoad hinstr hidx hbounds =>
    rename_i idxVal arr dst idx ty
    have heq : instr = .arrLoad dst arr idx ty := Option.some.inj (hInstr.symm.trans hinstr)
    rw [heq] at hSome hMapped
    cases ty with
    | int =>
      have hNotFregIdx : ∀ r, layout idx ≠ some (.freg r) :=
        hWTL.int_not_freg (by have := hTS idx; rw [hidx] at this; exact this.symm)
      let idx_reg := match layout idx with | some (.ireg r) => r | _ => ArmReg.x1
      let dst_reg := match layout dst with | some (.ireg r) => r | _ => ArmReg.x0
      have hInstrs : instrs = vLoadVar layout idx idx_reg ++
          ((if boundsSafe then [] else
            [.cmpImm idx_reg (arraySizeBv arrayDecls arr), .bCond .hs boundsLabel]) ++
          .arrLd dst_reg arr idx_reg :: vStoreVar layout dst dst_reg) := by
        simp [verifiedGenInstr, hRC, hII] at hSome; exact hSome.symm
      rw [hInstrs] at hCodeInstr hPcNext
      have hCodeA := hCodeInstr.append_left
      have hCodeBCD := hCodeInstr.append_right
      obtain ⟨s1, k1, hSteps1N, hk1, hX1_1, hRel1, _, hPC1, hAM1, hRegs1⟩ :=
        vLoadVar_eff_exec prog layout idx σ s (pcMap pc) .x1 hStateRel hRegConv hPcRel
          hNotFregIdx (Or.inr (Or.inl rfl)) (hMapped idx (by simp [TAC.vars])) hCodeA
      have hk1' : k1 = (vLoadVar layout idx idx_reg).length := hk1
      have hIdxVal : s1.regs idx_reg = idxVal := by rw [hX1_1, hidx]; simp [Value.encode]
      have hNotFregDst : ∀ r, layout dst ≠ some (.freg r) := by
        have hwti := hWT pc hPC_bound
        rw [Prog.getElem?_eq_getElem hPC_bound |>.symm.trans hinstr |> Option.some.inj] at hwti
        cases hwti with
        | arrLoad hx _ _ => exact hWTL.int_not_freg hx
      cases hBS : boundsSafe with
      | true =>
        simp [hBS] at hCodeBCD
        have hCodeArrLd := hCodeBCD.head; rw [← hPC1] at hCodeArrLd
        let s3 := s1.setReg dst_reg (s1.arrayMem arr (s1.regs idx_reg)) |>.nextPC
        have hStepArrLdN : ArmStepsN prog s1 s3 1 :=
          ArmStepsN.single (.arrLd dst_reg arr idx_reg hCodeArrLd)
        have hDstVal : s3.regs dst_reg = am.read arr idxVal := by
          simp [s3, ArmState.setReg, ArmState.nextPC, ArrayMem.read, hIdxVal, hAM1, hArrayMem]
        by_cases hDIR : ∃ r, layout dst = some (.ireg r)
        · obtain ⟨r_dst, hDstLoc⟩ := hDIR
          have hDR : dst_reg = r_dst := by
            change (match layout dst with | some (.ireg r) => r | _ => .x0) = r_dst; rw [hDstLoc]
          have hStore : vStoreVar layout dst dst_reg = [] := by simp [vStoreVar, hDstLoc, hDR]
          have hRel4 : ExtStateRel layout (σ[dst ↦ .int (am.read arr idxVal)]) s3 := by
            show ExtStateRel layout (σ[dst ↦ .int (am.read arr idxVal)])
              (s1.setReg dst_reg (s1.arrayMem arr (s1.regs idx_reg))).nextPC
            rw [hDR, hIdxVal, hAM1, hArrayMem]
            exact (ExtStateRel.update_ireg hRel1 hInjective hDstLoc).nextPC
          have hAM3 : s3.arrayMem = am := by
            simp [s3, ArmState.setReg, ArmState.nextPC, hAM1, hArrayMem]
          have hChain : ArmStepsN prog s s3 (k1 + 1) := ArmStepsN_trans hSteps1N hStepArrLdN
          refine ⟨s3, k1 + 1, hChain, ?_, hRel4, ?_, hAM3⟩
          · intro pc' σ' am' _hCfg
            rw [hInstrs, hk1', hStore]; simp [List.length_append, hBS]
          · show s3.pc = pcMap (pc + 1)
            have hPC_s3 : s3.pc = pcMap pc + (vLoadVar layout idx idx_reg).length + 1 := by
              simp [s3, ArmState.setReg, ArmState.nextPC]; rw [hPC1]
            have := hPcNext _ _ rfl; simp [hStore, hBS] at this; rw [hPC_s3]; omega
        · have hDR : dst_reg = .x0 := by
            change (match layout dst with | some (.ireg r) => r | _ => .x0) = .x0
            split
            · next r h => exact absurd ⟨r, h⟩ hDIR
            · rfl
          have hRel3 : ExtStateRel layout σ s3 := by
            show ExtStateRel layout σ
              (s1.setReg dst_reg (s1.arrayMem arr (s1.regs idx_reg))).nextPC
            rw [hDR]; exact (ExtStateRel.setReg_preserved hRel1 (fun w => hRegConv.not_x0 w)).nextPC
          have hVal3 : s3.regs .x0 = (Value.int (am.read arr idxVal)).encode := by
            simp [Value.encode]; exact hDstVal ▸ (by rw [hDR])
          have hPC4 : s3.pc = pcMap pc + (vLoadVar layout idx idx_reg).length + 1 := by
            simp [s3, ArmState.setReg, ArmState.nextPC]; rw [hPC1]
          have hCodeStore : CodeAt prog s3.pc (vStoreVar layout dst .x0) := by
            rw [← hDR, hPC4]; exact hCodeBCD.tail
          obtain ⟨s4, k4, hSteps4N, hk4, hRel4, hPC5, hAM4⟩ :=
            vStoreVar_exec prog layout dst (Value.int (am.read arr idxVal)) σ s3
              s3.pc hRel3 hInjective hRegConv rfl hVal3 hCodeStore hNotFregDst
          have hk4' : k4 = (vStoreVar layout dst dst_reg).length := by rw [hDR]; exact hk4
          have h12 : ArmStepsN prog s s3 (k1 + 1) := ArmStepsN_trans hSteps1N hStepArrLdN
          have hChain : ArmStepsN prog s s4 (k1 + 1 + k4) := ArmStepsN_trans h12 hSteps4N
          have hAM_final : s4.arrayMem = am := by
            rw [hAM4]; simp [s3, ArmState.setReg, ArmState.nextPC, hAM1, hArrayMem]
          refine ⟨s4, k1 + 1 + k4, hChain, ?_, hRel4, ?_, hAM_final⟩
          · intro pc' σ' am' _hCfg
            rw [hInstrs, hk1', hk4']; simp [List.length_append, hBS]; omega
          · show s4.pc = pcMap (pc + 1)
            have := hPcNext _ _ rfl; rw [show dst_reg = ArmReg.x0 from hDR] at this
            simp [hBS] at this; omega
      | false =>
        simp [hBS] at hCodeBCD
        have hCmp := hCodeBCD.head; rw [← hPC1] at hCmp
        let s2 := { s1 with flags := Flags.mk (s1.regs idx_reg) (arraySizeBv arrayDecls arr), pc := s1.pc + 1 }
        have hStepCmpN : ArmStepsN prog s1 s2 1 :=
          ArmStepsN.single (.cmpRI idx_reg (arraySizeBv arrayDecls arr) hCmp)
        have hBoundsAD : idxVal < arraySizeBv arrayDecls arr := by rw [hAD]; exact hbounds
        have hCondFalse : s2.flags.condHolds .hs = false := by
          simp only [s2, Flags.condHolds, hIdxVal]
          cases h : decide (arraySizeBv arrayDecls arr ≤ idxVal) <;> simp_all <;> bv_omega
        have hPC2 : s2.pc = pcMap pc + (vLoadVar layout idx idx_reg).length + 1 := by
          show s1.pc + 1 = _; rw [hPC1]
        have hBCond := hCodeBCD.tail.head; rw [← hPC2] at hBCond
        have hStepBCondN : ArmStepsN prog s2 s2.nextPC 1 :=
          ArmStepsN.single (.bCond_fall .hs boundsLabel hBCond hCondFalse)
        have hRel2 : ExtStateRel layout σ s2.nextPC := hRel1.nextPC
        have hIdxVal2 : s2.nextPC.regs idx_reg = idxVal := by
          simp [ArmState.nextPC, s2]; exact hIdxVal
        have hAM2 : s2.nextPC.arrayMem = am := by simp [ArmState.nextPC, s2, hAM1, hArrayMem]
        have hPC3 : s2.nextPC.pc = pcMap pc + (vLoadVar layout idx idx_reg).length + 2 := by
          simp [ArmState.nextPC, s2]; rw [hPC1]
        have hCodeArrLd := hCodeBCD.tail.tail.head; rw [← hPC3] at hCodeArrLd
        let s3 := s2.nextPC.setReg dst_reg (s2.nextPC.arrayMem arr (s2.nextPC.regs idx_reg)) |>.nextPC
        have hStepArrLdN : ArmStepsN prog s2.nextPC s3 1 :=
          ArmStepsN.single (.arrLd dst_reg arr idx_reg hCodeArrLd)
        have hDstVal : s3.regs dst_reg = am.read arr idxVal := by
          simp [s3, ArmState.setReg, ArmState.nextPC, s2, ArrayMem.read]
          rw [hIdxVal]; rw [hAM1, hArrayMem]
        by_cases hDIR : ∃ r, layout dst = some (.ireg r)
        · obtain ⟨r_dst, hDstLoc⟩ := hDIR
          have hDR : dst_reg = r_dst := by
            change (match layout dst with | some (.ireg r) => r | _ => .x0) = r_dst; rw [hDstLoc]
          have hStore : vStoreVar layout dst dst_reg = [] := by simp [vStoreVar, hDstLoc, hDR]
          have hRel4 : ExtStateRel layout (σ[dst ↦ .int (am.read arr idxVal)]) s3 := by
            show ExtStateRel layout (σ[dst ↦ .int (am.read arr idxVal)])
              (s2.nextPC.setReg dst_reg (s2.nextPC.arrayMem arr (s2.nextPC.regs idx_reg))).nextPC
            rw [hDR, hIdxVal2, hAM2]
            exact (ExtStateRel.update_ireg hRel2 hInjective hDstLoc).nextPC
          have hAM3 : s3.arrayMem = am := by
            simp [s3, ArmState.setReg, ArmState.nextPC, s2, hAM1, hArrayMem]
          have h12 : ArmStepsN prog s s2 (k1 + 1) := ArmStepsN_trans hSteps1N hStepCmpN
          have h123 : ArmStepsN prog s s2.nextPC (k1 + 1 + 1) := ArmStepsN_trans h12 hStepBCondN
          have hChain : ArmStepsN prog s s3 (k1 + 1 + 1 + 1) := ArmStepsN_trans h123 hStepArrLdN
          refine ⟨s3, k1 + 1 + 1 + 1, hChain, ?_, hRel4, ?_, hAM3⟩
          · intro pc' σ' am' _hCfg
            rw [hInstrs, hk1', hStore]; simp [List.length_append, hBS]
          · show s3.pc = pcMap (pc + 1)
            have hPC_s3 : s3.pc = pcMap pc + (vLoadVar layout idx idx_reg).length + 3 := by
              simp [s3, ArmState.setReg, ArmState.nextPC, s2]; rw [hPC1]
            have := hPcNext _ _ rfl; simp [hStore, hBS] at this; rw [hPC_s3]; omega
        · have hDR : dst_reg = .x0 := by
            change (match layout dst with | some (.ireg r) => r | _ => .x0) = .x0
            split
            · next r h => exact absurd ⟨r, h⟩ hDIR
            · rfl
          have hRel3 : ExtStateRel layout σ s3 := by
            show ExtStateRel layout σ
              (s2.nextPC.setReg dst_reg (s2.nextPC.arrayMem arr (s2.nextPC.regs idx_reg))).nextPC
            rw [hDR]; exact (ExtStateRel.setReg_preserved hRel2 (fun w => hRegConv.not_x0 w)).nextPC
          have hVal3 : s3.regs .x0 = (Value.int (am.read arr idxVal)).encode := by
            simp [Value.encode]; exact hDstVal ▸ (by rw [hDR])
          have hPC4 : s3.pc = pcMap pc + (vLoadVar layout idx idx_reg).length + 3 := by
            simp [s3, ArmState.setReg, ArmState.nextPC, s2]; rw [hPC1]
          have hCodeStore : CodeAt prog s3.pc (vStoreVar layout dst .x0) := by
            rw [← hDR]; rw [hPC4]; exact hCodeBCD.tail.tail.tail
          obtain ⟨s4, k4, hSteps4N, hk4, hRel4, hPC5, hAM4⟩ :=
            vStoreVar_exec prog layout dst (Value.int (am.read arr idxVal)) σ s3
              s3.pc hRel3 hInjective hRegConv rfl hVal3 hCodeStore hNotFregDst
          have hk4' : k4 = (vStoreVar layout dst dst_reg).length := by rw [hDR]; exact hk4
          have hAM_final : s4.arrayMem = am := by
            rw [hAM4]; simp [s3, ArmState.setReg, ArmState.nextPC, s2, hAM1, hArrayMem]
          have h12 : ArmStepsN prog s s2 (k1 + 1) := ArmStepsN_trans hSteps1N hStepCmpN
          have h123 : ArmStepsN prog s s2.nextPC (k1 + 1 + 1) := ArmStepsN_trans h12 hStepBCondN
          have h1234 : ArmStepsN prog s s3 (k1 + 1 + 1 + 1) := ArmStepsN_trans h123 hStepArrLdN
          have hChain : ArmStepsN prog s s4 (k1 + 1 + 1 + 1 + k4) := ArmStepsN_trans h1234 hSteps4N
          refine ⟨s4, k1 + 1 + 1 + 1 + k4, hChain, ?_, hRel4, ?_, hAM_final⟩
          · intro pc' σ' am' _hCfg
            rw [hInstrs, hk1', hk4']; simp [List.length_append, hBS]; omega
          · show s4.pc = pcMap (pc + 1)
            have := hPcNext _ _ rfl; rw [show dst_reg = ArmReg.x0 from hDR] at this
            simp [hBS] at this; omega
    | bool =>
      have hNotFregIdx : ∀ r, layout idx ≠ some (.freg r) :=
        hWTL.int_not_freg (by have := hTS idx; rw [hidx] at this; exact this.symm)
      have hNotFregDst : ∀ r, layout dst ≠ some (.freg r) := by
        have hwti := hWT pc hPC_bound
        rw [Prog.getElem?_eq_getElem hPC_bound |>.symm.trans hinstr |> Option.some.inj] at hwti
        cases hwti with
        | arrLoad hx _ _ => exact hWTL.bool_not_freg hx
      let idx_reg := match layout idx with | some (.ireg r) => r | _ => ArmReg.x1
      let dst_reg := match layout dst with | some (.ireg r) => r | _ => ArmReg.x0
      have hInstrs : instrs = vLoadVar layout idx idx_reg ++
          ((if boundsSafe then [] else
            [.cmpImm idx_reg (arraySizeBv arrayDecls arr), .bCond .hs boundsLabel]) ++
          .arrLd dst_reg arr idx_reg :: .cmpImm dst_reg 0 :: .cset dst_reg .ne ::
          vStoreVar layout dst dst_reg) := by
        simp [verifiedGenInstr, hRC, hII] at hSome; exact hSome.symm
      rw [hInstrs] at hCodeInstr hPcNext
      have hCodeA := hCodeInstr.append_left
      have hCodeBCD := hCodeInstr.append_right
      obtain ⟨s1, k1, hSteps1N, hk1, hX1_1, hRel1, _, hPC1, hAM1, hRegs1⟩ :=
        vLoadVar_eff_exec prog layout idx σ s (pcMap pc) .x1 hStateRel hRegConv hPcRel
          hNotFregIdx (Or.inr (Or.inl rfl)) (hMapped idx (by simp [TAC.vars])) hCodeA
      have hk1' : k1 = (vLoadVar layout idx idx_reg).length := hk1
      have hIdxVal : s1.regs idx_reg = idxVal := by rw [hX1_1, hidx]; simp [Value.encode]
      let boolVal := Value.ofBitVec .bool (am.read arr idxVal)
      have hNormEnc : ∀ (rawBv : BitVec 64), rawBv = am.read arr idxVal →
          (if (Flags.mk rawBv 0).condHolds .ne then (1 : BitVec 64) else 0) = boolVal.encode := by
        intro rawBv hrw; subst hrw
        simp [Flags.condHolds, Value.encode, boolVal, bne, BEq.beq]
      cases hBS : boundsSafe with
      | true =>
        simp [hBS] at hCodeBCD
        have hCodeArrLd := hCodeBCD.head; rw [← hPC1] at hCodeArrLd
        let sA := s1.setReg dst_reg (s1.arrayMem arr (s1.regs idx_reg)) |>.nextPC
        have hStepArrLdN : ArmStepsN prog s1 sA 1 :=
          ArmStepsN.single (.arrLd dst_reg arr idx_reg hCodeArrLd)
        have hDstValA : sA.regs dst_reg = am.read arr idxVal := by
          simp [sA, ArmState.setReg, ArmState.nextPC, ArrayMem.read, hIdxVal, hAM1, hArrayMem]
        have hPCA : sA.pc = pcMap pc + (vLoadVar layout idx idx_reg).length + 1 := by
          simp [sA, ArmState.setReg, ArmState.nextPC]; rw [hPC1]
        have hCodeCmpImm := hCodeBCD.tail.head; rw [← hPCA] at hCodeCmpImm
        let sB := { sA with flags := Flags.mk (sA.regs dst_reg) 0, pc := sA.pc + 1 }
        have hStepCmpN : ArmStepsN prog sA sB 1 :=
          ArmStepsN.single (.cmpRI dst_reg 0 hCodeCmpImm)
        have hPCB : sB.pc = pcMap pc + (vLoadVar layout idx idx_reg).length + 2 := by
          show sA.pc + 1 = _; rw [hPCA]
        have hCodeCset := hCodeBCD.tail.tail.head; rw [← hPCB] at hCodeCset
        let s3 := sB.setReg dst_reg (if sB.flags.condHolds .ne then (1 : BitVec 64) else 0) |>.nextPC
        have hStepCsetN : ArmStepsN prog sB s3 1 :=
          ArmStepsN.single (.cset dst_reg .ne hCodeCset)
        have hCsetEq : (if sB.flags.condHolds .ne then (1 : BitVec 64) else 0) = boolVal.encode :=
          hNormEnc _ hDstValA
        have hDstVal : s3.regs dst_reg = boolVal.encode := by
          simp only [s3, ArmState.nextPC, ArmState.setReg, beq_self_eq_true, ite_true]
          exact hCsetEq
        by_cases hDIR : ∃ r, layout dst = some (.ireg r)
        · obtain ⟨r_dst, hDstLoc⟩ := hDIR
          have hDR : dst_reg = r_dst := by
            change (match layout dst with | some (.ireg r) => r | _ => .x0) = r_dst; rw [hDstLoc]
          have hStore : vStoreVar layout dst dst_reg = [] := by simp [vStoreVar, hDstLoc, hDR]
          have hRel4 : ExtStateRel layout (σ[dst ↦ boolVal]) s3 := by
            intro w loc hW
            by_cases hwv : w = dst
            · subst hwv; rw [hDstLoc] at hW; cases hW
              simp [Store.update]; exact hDR ▸ hDstVal
            · rw [Store.update_other σ dst w boolVal hwv]
              match loc, hW with
              | .stack off, hW =>
                show s3.stack off = (σ w).encode
                have : s3.stack off = s1.stack off := by
                  simp [s3, sB, sA, ArmState.setReg, ArmState.nextPC]
                rw [this]; exact hRel1 w (.stack off) hW
              | .ireg r', hW =>
                show s3.regs r' = (σ w).encode
                have hne : r' ≠ r_dst := fun heq =>
                  hwv (hInjective w dst (.ireg r') (hW) (heq ▸ hDstLoc))
                have hne' : r' ≠ dst_reg := hDR ▸ hne
                have : s3.regs r' = s1.regs r' := by
                  simp [s3, sB, sA, ArmState.nextPC, ArmState.setReg, beq_iff_eq, hne']
                rw [this]; exact hRel1 w (.ireg r') hW
              | .freg r', hW =>
                show s3.fregs r' = (σ w).encode
                have : s3.fregs r' = s1.fregs r' := by
                  simp [s3, sB, sA, ArmState.setReg, ArmState.nextPC]
                rw [this]; exact hRel1 w (.freg r') hW
          have hAM3 : s3.arrayMem = am := by
            simp [s3, sB, sA, ArmState.setReg, ArmState.nextPC, hAM1, hArrayMem]
          have h12 : ArmStepsN prog s sA (k1 + 1) := ArmStepsN_trans hSteps1N hStepArrLdN
          have h123 : ArmStepsN prog s sB (k1 + 1 + 1) := ArmStepsN_trans h12 hStepCmpN
          have hChain : ArmStepsN prog s s3 (k1 + 1 + 1 + 1) := ArmStepsN_trans h123 hStepCsetN
          refine ⟨s3, k1 + 1 + 1 + 1, hChain, ?_, hRel4, ?_, hAM3⟩
          · intro pc' σ' am' _hCfg
            rw [hInstrs, hk1', hStore]; simp [List.length_append, hBS]
          · show s3.pc = pcMap (pc + 1)
            have hPC_s3 : s3.pc = pcMap pc + (vLoadVar layout idx idx_reg).length + 3 := by
              simp [s3, sB, ArmState.setReg, ArmState.nextPC]; rw [hPCA]
            have := hPcNext _ _ rfl; simp [hStore, hBS] at this; rw [hPC_s3]; omega
        · have hDR : dst_reg = .x0 := by
            change (match layout dst with | some (.ireg r) => r | _ => .x0) = .x0
            split
            · next r h => exact absurd ⟨r, h⟩ hDIR
            · rfl
          have hRel3 : ExtStateRel layout σ s3 := by
            intro w loc hW
            match loc, hW with
            | .stack off, hW =>
              show s3.stack off = (σ w).encode
              have : s3.stack off = s1.stack off := by
                simp [s3, sB, sA, ArmState.setReg, ArmState.nextPC]
              rw [this]; exact hRel1 w (.stack off) hW
            | .ireg r', hW =>
              show s3.regs r' = (σ w).encode
              have hne : r' ≠ .x0 := fun heq => hRegConv.not_x0 w (heq ▸ hW)
              have hne' : r' ≠ dst_reg := hDR ▸ hne
              have : s3.regs r' = s1.regs r' := by
                simp [s3, sB, sA, ArmState.nextPC, ArmState.setReg, beq_iff_eq, hne']
              rw [this]; exact hRel1 w (.ireg r') hW
            | .freg r', hW =>
              show s3.fregs r' = (σ w).encode
              have : s3.fregs r' = s1.fregs r' := by
                simp [s3, sB, sA, ArmState.setReg, ArmState.nextPC]
              rw [this]; exact hRel1 w (.freg r') hW
          have hVal3 : s3.regs .x0 = boolVal.encode := by rw [← hDR]; exact hDstVal
          have hPC4 : s3.pc = pcMap pc + (vLoadVar layout idx idx_reg).length + 3 := by
            simp [s3, sB, ArmState.setReg, ArmState.nextPC]; rw [hPCA]
          have hCodeStore : CodeAt prog s3.pc (vStoreVar layout dst .x0) := by
            rw [← hDR, hPC4]; exact hCodeBCD.tail.tail.tail
          obtain ⟨s4, k4, hSteps4N, hk4, hRel4, hPC5, hAM4⟩ :=
            vStoreVar_exec prog layout dst boolVal σ s3
              s3.pc hRel3 hInjective hRegConv rfl hVal3 hCodeStore hNotFregDst
          have hk4' : k4 = (vStoreVar layout dst dst_reg).length := by rw [hDR]; exact hk4
          have hAM_final : s4.arrayMem = am := by
            rw [hAM4]; simp [s3, sB, sA, ArmState.setReg, ArmState.nextPC, hAM1, hArrayMem]
          have h12 : ArmStepsN prog s sA (k1 + 1) := ArmStepsN_trans hSteps1N hStepArrLdN
          have h123 : ArmStepsN prog s sB (k1 + 1 + 1) := ArmStepsN_trans h12 hStepCmpN
          have h1234 : ArmStepsN prog s s3 (k1 + 1 + 1 + 1) := ArmStepsN_trans h123 hStepCsetN
          have hChain : ArmStepsN prog s s4 (k1 + 1 + 1 + 1 + k4) := ArmStepsN_trans h1234 hSteps4N
          refine ⟨s4, k1 + 1 + 1 + 1 + k4, hChain, ?_, hRel4, ?_, hAM_final⟩
          · intro pc' σ' am' _hCfg
            rw [hInstrs, hk1', hk4']; simp [List.length_append, hBS]; omega
          · show s4.pc = pcMap (pc + 1)
            have := hPcNext _ _ rfl; rw [show dst_reg = ArmReg.x0 from hDR] at this
            simp [hBS] at this; omega
      | false =>
        simp [hBS] at hCodeBCD
        have hCmp := hCodeBCD.head; rw [← hPC1] at hCmp
        let s2 := { s1 with flags := Flags.mk (s1.regs idx_reg) (arraySizeBv arrayDecls arr), pc := s1.pc + 1 }
        have hStepCmpBoundsN : ArmStepsN prog s1 s2 1 :=
          ArmStepsN.single (.cmpRI idx_reg (arraySizeBv arrayDecls arr) hCmp)
        have hBoundsAD : idxVal < arraySizeBv arrayDecls arr := by rw [hAD]; exact hbounds
        have hCondFalse : s2.flags.condHolds .hs = false := by
          simp only [s2, Flags.condHolds, hIdxVal]
          cases h : decide (arraySizeBv arrayDecls arr ≤ idxVal) <;> simp_all <;> bv_omega
        have hPC2 : s2.pc = pcMap pc + (vLoadVar layout idx idx_reg).length + 1 := by
          show s1.pc + 1 = _; rw [hPC1]
        have hBCond := hCodeBCD.tail.head; rw [← hPC2] at hBCond
        have hStepBCondN : ArmStepsN prog s2 s2.nextPC 1 :=
          ArmStepsN.single (.bCond_fall .hs boundsLabel hBCond hCondFalse)
        have hRel2 : ExtStateRel layout σ s2.nextPC := hRel1.nextPC
        have hIdxVal2 : s2.nextPC.regs idx_reg = idxVal := by
          simp [ArmState.nextPC, s2]; exact hIdxVal
        have hAM2 : s2.nextPC.arrayMem = am := by
          simp [ArmState.nextPC, s2, hAM1, hArrayMem]
        have hPC3 : s2.nextPC.pc = pcMap pc + (vLoadVar layout idx idx_reg).length + 2 := by
          simp [ArmState.nextPC, s2]; rw [hPC1]
        have hCodeArrLd := hCodeBCD.tail.tail.head; rw [← hPC3] at hCodeArrLd
        let sA := s2.nextPC.setReg dst_reg (s2.nextPC.arrayMem arr (s2.nextPC.regs idx_reg)) |>.nextPC
        have hStepArrLdN : ArmStepsN prog s2.nextPC sA 1 :=
          ArmStepsN.single (.arrLd dst_reg arr idx_reg hCodeArrLd)
        have hDstValA : sA.regs dst_reg = am.read arr idxVal := by
          simp [sA, ArmState.setReg, ArmState.nextPC, s2, ArrayMem.read]
          rw [hIdxVal]; rw [hAM1, hArrayMem]
        have hPCA : sA.pc = pcMap pc + (vLoadVar layout idx idx_reg).length + 3 := by
          simp [sA, ArmState.setReg, ArmState.nextPC, s2]; rw [hPC1]
        have hCodeCmpImm := hCodeBCD.tail.tail.tail.head; rw [← hPCA] at hCodeCmpImm
        let sB := { sA with flags := Flags.mk (sA.regs dst_reg) 0, pc := sA.pc + 1 }
        have hStepCmpBN : ArmStepsN prog sA sB 1 :=
          ArmStepsN.single (.cmpRI dst_reg 0 hCodeCmpImm)
        have hPCB : sB.pc = pcMap pc + (vLoadVar layout idx idx_reg).length + 4 := by
          show sA.pc + 1 = _; rw [hPCA]
        have hCodeCset := hCodeBCD.tail.tail.tail.tail.head; rw [← hPCB] at hCodeCset
        let s3 := sB.setReg dst_reg (if sB.flags.condHolds .ne then (1 : BitVec 64) else 0) |>.nextPC
        have hStepCsetN : ArmStepsN prog sB s3 1 :=
          ArmStepsN.single (.cset dst_reg .ne hCodeCset)
        have hCsetEq : (if sB.flags.condHolds .ne then (1 : BitVec 64) else 0) = boolVal.encode :=
          hNormEnc _ hDstValA
        have hDstVal : s3.regs dst_reg = boolVal.encode := by
          simp only [s3, ArmState.nextPC, ArmState.setReg, beq_self_eq_true, ite_true]
          exact hCsetEq
        by_cases hDIR : ∃ r, layout dst = some (.ireg r)
        · obtain ⟨r_dst, hDstLoc⟩ := hDIR
          have hDR : dst_reg = r_dst := by
            change (match layout dst with | some (.ireg r) => r | _ => .x0) = r_dst; rw [hDstLoc]
          have hStore : vStoreVar layout dst dst_reg = [] := by simp [vStoreVar, hDstLoc, hDR]
          have hRel4 : ExtStateRel layout (σ[dst ↦ boolVal]) s3 := by
            intro w loc hW
            by_cases hwv : w = dst
            · subst hwv; rw [hDstLoc] at hW; cases hW
              simp [Store.update]; exact hDR ▸ hDstVal
            · rw [Store.update_other σ dst w boolVal hwv]
              match loc, hW with
              | .stack off, hW =>
                show s3.stack off = (σ w).encode
                have : s3.stack off = s1.stack off := by
                  simp [s3, sB, sA, ArmState.setReg, ArmState.nextPC, s2]
                rw [this]; exact hRel1 w (.stack off) hW
              | .ireg r', hW =>
                show s3.regs r' = (σ w).encode
                have hne : r' ≠ r_dst := fun heq =>
                  hwv (hInjective w dst (.ireg r') (hW) (heq ▸ hDstLoc))
                have hne' : r' ≠ dst_reg := hDR ▸ hne
                have : s3.regs r' = s1.regs r' := by
                  simp [s3, sB, sA, ArmState.nextPC, ArmState.setReg, beq_iff_eq, hne', s2]
                rw [this]; exact hRel1 w (.ireg r') hW
              | .freg r', hW =>
                show s3.fregs r' = (σ w).encode
                have : s3.fregs r' = s1.fregs r' := by
                  simp [s3, sB, sA, ArmState.setReg, ArmState.nextPC, s2]
                rw [this]; exact hRel1 w (.freg r') hW
          have hAM3 : s3.arrayMem = am := by
            simp [s3, sB, sA, ArmState.setReg, ArmState.nextPC, s2, hAM1, hArrayMem]
          have h12 : ArmStepsN prog s s2 (k1 + 1) := ArmStepsN_trans hSteps1N hStepCmpBoundsN
          have h123 : ArmStepsN prog s s2.nextPC (k1 + 1 + 1) := ArmStepsN_trans h12 hStepBCondN
          have h1234 : ArmStepsN prog s sA (k1 + 1 + 1 + 1) := ArmStepsN_trans h123 hStepArrLdN
          have h12345 : ArmStepsN prog s sB (k1 + 1 + 1 + 1 + 1) := ArmStepsN_trans h1234 hStepCmpBN
          have hChain : ArmStepsN prog s s3 (k1 + 1 + 1 + 1 + 1 + 1) := ArmStepsN_trans h12345 hStepCsetN
          refine ⟨s3, k1 + 1 + 1 + 1 + 1 + 1, hChain, ?_, hRel4, ?_, hAM3⟩
          · intro pc' σ' am' _hCfg
            rw [hInstrs, hk1', hStore]; simp [List.length_append, hBS]
          · show s3.pc = pcMap (pc + 1)
            have hPC_s3 : s3.pc = pcMap pc + (vLoadVar layout idx idx_reg).length + 5 := by
              simp [s3, sB, ArmState.setReg, ArmState.nextPC]; rw [hPCA]
            have := hPcNext _ _ rfl; simp [hStore, hBS] at this; rw [hPC_s3]; omega
        · have hDR : dst_reg = .x0 := by
            change (match layout dst with | some (.ireg r) => r | _ => .x0) = .x0
            split
            · next r h => exact absurd ⟨r, h⟩ hDIR
            · rfl
          have hRel3 : ExtStateRel layout σ s3 := by
            intro w loc hW
            match loc, hW with
            | .stack off, hW =>
              show s3.stack off = (σ w).encode
              have : s3.stack off = s1.stack off := by
                simp [s3, sB, sA, ArmState.setReg, ArmState.nextPC, s2]
              rw [this]; exact hRel1 w (.stack off) hW
            | .ireg r', hW =>
              show s3.regs r' = (σ w).encode
              have hne : r' ≠ .x0 := fun heq => hRegConv.not_x0 w (heq ▸ hW)
              have hne' : r' ≠ dst_reg := hDR ▸ hne
              have : s3.regs r' = s1.regs r' := by
                simp [s3, sB, sA, ArmState.nextPC, ArmState.setReg, beq_iff_eq, hne', s2]
              rw [this]; exact hRel1 w (.ireg r') hW
            | .freg r', hW =>
              show s3.fregs r' = (σ w).encode
              have : s3.fregs r' = s1.fregs r' := by
                simp [s3, sB, sA, ArmState.setReg, ArmState.nextPC, s2]
              rw [this]; exact hRel1 w (.freg r') hW
          have hVal3 : s3.regs .x0 = boolVal.encode := by rw [← hDR]; exact hDstVal
          have hPC4 : s3.pc = pcMap pc + (vLoadVar layout idx idx_reg).length + 5 := by
            simp [s3, sB, ArmState.setReg, ArmState.nextPC]; rw [hPCA]
          have hCodeStore : CodeAt prog s3.pc (vStoreVar layout dst .x0) := by
            rw [← hDR]; rw [hPC4]; exact hCodeBCD.tail.tail.tail.tail.tail
          obtain ⟨s4, k4, hSteps4N, hk4, hRel4, hPC5, hAM4⟩ :=
            vStoreVar_exec prog layout dst boolVal σ s3
              s3.pc hRel3 hInjective hRegConv rfl hVal3 hCodeStore hNotFregDst
          have hk4' : k4 = (vStoreVar layout dst dst_reg).length := by rw [hDR]; exact hk4
          have hAM_final : s4.arrayMem = am := by
            rw [hAM4]; simp [s3, sB, sA, ArmState.setReg, ArmState.nextPC, s2, hAM1, hArrayMem]
          have h12 : ArmStepsN prog s s2 (k1 + 1) := ArmStepsN_trans hSteps1N hStepCmpBoundsN
          have h123 : ArmStepsN prog s s2.nextPC (k1 + 1 + 1) := ArmStepsN_trans h12 hStepBCondN
          have h1234 : ArmStepsN prog s sA (k1 + 1 + 1 + 1) := ArmStepsN_trans h123 hStepArrLdN
          have h12345 : ArmStepsN prog s sB (k1 + 1 + 1 + 1 + 1) := ArmStepsN_trans h1234 hStepCmpBN
          have h123456 : ArmStepsN prog s s3 (k1 + 1 + 1 + 1 + 1 + 1) := ArmStepsN_trans h12345 hStepCsetN
          have hChain : ArmStepsN prog s s4 (k1 + 1 + 1 + 1 + 1 + 1 + k4) := ArmStepsN_trans h123456 hSteps4N
          refine ⟨s4, k1 + 1 + 1 + 1 + 1 + 1 + k4, hChain, ?_, hRel4, ?_, hAM_final⟩
          · intro pc' σ' am' _hCfg
            rw [hInstrs, hk1', hk4']; simp [List.length_append, hBS]; omega
          · show s4.pc = pcMap (pc + 1)
            have := hPcNext _ _ rfl; rw [show dst_reg = ArmReg.x0 from hDR] at this
            simp [hBS] at this; omega
    | float =>
      have hNotFregIdx : ∀ r, layout idx ≠ some (.freg r) :=
        hWTL.int_not_freg (by have := hTS idx; rw [hidx] at this; exact this.symm)
      have hNotIregDst : ∀ r, layout dst ≠ some (.ireg r) := by
        have hwti := hWT pc hPC_bound
        rw [Prog.getElem?_eq_getElem hPC_bound |>.symm.trans hinstr |> Option.some.inj] at hwti
        cases hwti with
        | arrLoad hx _ _ => exact hWTL.float_not_ireg hx
      let idx_reg := match layout idx with | some (.ireg r) => r | _ => ArmReg.x1
      let dst_freg := match layout dst with | some (.freg r) => r | _ => ArmFReg.d0
      have hInstrs : instrs = vLoadVar layout idx idx_reg ++
          ((if boundsSafe then [] else
            [.cmpImm idx_reg (arraySizeBv arrayDecls arr), .bCond .hs boundsLabel]) ++
          .farrLd dst_freg arr idx_reg :: vStoreVarFP layout dst dst_freg) := by
        simp [verifiedGenInstr, hRC, hII] at hSome; exact hSome.symm
      rw [hInstrs] at hCodeInstr hPcNext
      have hCodeA := hCodeInstr.append_left
      have hCodeBCD := hCodeInstr.append_right
      obtain ⟨s1, k1, hSteps1N, hk1, hX1_1, hRel1, _, hPC1, hAM1, hRegs1⟩ :=
        vLoadVar_eff_exec prog layout idx σ s (pcMap pc) .x1 hStateRel hRegConv hPcRel
          hNotFregIdx (Or.inr (Or.inl rfl)) (hMapped idx (by simp [TAC.vars])) hCodeA
      have hk1' : k1 = (vLoadVar layout idx idx_reg).length := hk1
      have hIdxVal : s1.regs idx_reg = idxVal := by rw [hX1_1, hidx]; simp [Value.encode]
      cases hBS : boundsSafe with
      | true =>
        simp [hBS] at hCodeBCD
        have hDstReg : dst_freg = match layout dst with | some (.freg r) => r | _ => .d0 := rfl
        have hCodeFarrLdStore := hCodeBCD; rw [← hPC1] at hCodeFarrLdStore
        have hFarrLdStep : ArmStep prog s1
            (s1.setFReg dst_freg (s1.arrayMem arr (s1.regs idx_reg)) |>.nextPC) :=
          .farrLd dst_freg arr idx_reg hCodeFarrLdStore.head
        have hResultEnc : s1.arrayMem arr (s1.regs idx_reg) =
            (Value.float (am.read arr idxVal)).encode := by
          simp [Value.encode, ArrayMem.read]; rw [hIdxVal, hAM1, hArrayMem]
        obtain ⟨s', k', hSteps'N, hk', hSimRel'⟩ :=
          fp_exec_and_store prog layout pcMap divLabel boundsLabel pc σ am dst dst_freg
            (s1.arrayMem arr (s1.regs idx_reg)) (Value.float (am.read arr idxVal))
            hResultEnc s1 s1.pc hRel1 hInjective hRegConv rfl (by rw [hAM1, hArrayMem])
            hDstReg hNotIregDst (.farrLd dst_freg arr idx_reg) hCodeFarrLdStore
            hFarrLdStep (vLoadVar layout idx idx_reg).length (by rw [hPC1])
            (by have := hPcNext _ _ rfl; simp [hBS] at this; omega)
        have hChain : ArmStepsN prog s s' (k1 + k') := ArmStepsN_trans hSteps1N hSteps'N
        refine ⟨s', k1 + k', hChain, ?_, hSimRel'⟩
        intro pc' σ' am' _hCfg
        rw [hInstrs, hk1', hk']; simp [List.length_append, hBS]; omega
      | false =>
        simp [hBS] at hCodeBCD
        have hCmp := hCodeBCD.head; rw [← hPC1] at hCmp
        let s2 := { s1 with flags := Flags.mk (s1.regs idx_reg) (arraySizeBv arrayDecls arr), pc := s1.pc + 1 }
        have hStepCmpN : ArmStepsN prog s1 s2 1 :=
          ArmStepsN.single (.cmpRI idx_reg (arraySizeBv arrayDecls arr) hCmp)
        have hBoundsAD : idxVal < arraySizeBv arrayDecls arr := by rw [hAD]; exact hbounds
        have hCondFalse : s2.flags.condHolds .hs = false := by
          simp only [s2, Flags.condHolds, hIdxVal]
          cases h : decide (arraySizeBv arrayDecls arr ≤ idxVal) <;> simp_all <;> bv_omega
        have hPC2 : s2.pc = pcMap pc + (vLoadVar layout idx idx_reg).length + 1 := by
          show s1.pc + 1 = _; rw [hPC1]
        have hBCond := hCodeBCD.tail.head; rw [← hPC2] at hBCond
        have hStepBCondN : ArmStepsN prog s2 s2.nextPC 1 :=
          ArmStepsN.single (.bCond_fall .hs boundsLabel hBCond hCondFalse)
        have hRel2 : ExtStateRel layout σ s2.nextPC := hRel1.nextPC
        have hDstReg : dst_freg = match layout dst with | some (.freg r) => r | _ => .d0 := rfl
        have hPC3 : s2.nextPC.pc = pcMap pc + (vLoadVar layout idx idx_reg).length + 2 := by
          simp [ArmState.nextPC, s2]; rw [hPC1]
        have hCodeFarrLdStore : CodeAt prog s2.nextPC.pc
            (.farrLd dst_freg arr idx_reg :: vStoreVarFP layout dst dst_freg) := by
          rw [hPC3]; exact hCodeBCD.tail.tail
        have hAM2 : s2.nextPC.arrayMem = am := by simp [ArmState.nextPC, s2, hAM1, hArrayMem]
        have hIdxVal2 : s2.nextPC.regs idx_reg = idxVal := by
          simp [ArmState.nextPC, s2]; exact hIdxVal
        have hFarrLdStep : ArmStep prog s2.nextPC
            (s2.nextPC.setFReg dst_freg (s2.nextPC.arrayMem arr (s2.nextPC.regs idx_reg)) |>.nextPC) :=
          .farrLd dst_freg arr idx_reg hCodeFarrLdStore.head
        have hResultEnc : s2.nextPC.arrayMem arr (s2.nextPC.regs idx_reg) =
            (Value.float (am.read arr idxVal)).encode := by
          simp [Value.encode, ArrayMem.read, ArmState.nextPC]
          show s2.arrayMem arr (s2.regs idx_reg) = am arr idxVal
          simp [s2]; rw [hIdxVal, hAM1, hArrayMem]
        obtain ⟨s', k', hSteps'N, hk', hSimRel'⟩ :=
          fp_exec_and_store prog layout pcMap divLabel boundsLabel pc σ am dst dst_freg
            (s2.nextPC.arrayMem arr (s2.nextPC.regs idx_reg)) (Value.float (am.read arr idxVal))
            hResultEnc s2.nextPC s2.nextPC.pc hRel2 hInjective hRegConv rfl hAM2
            hDstReg hNotIregDst (.farrLd dst_freg arr idx_reg) hCodeFarrLdStore
            hFarrLdStep ((vLoadVar layout idx idx_reg).length + 2) (by rw [hPC3]; omega)
            (by have := hPcNext _ _ rfl; simp [hBS] at this; omega)
        have h12 : ArmStepsN prog s s2 (k1 + 1) := ArmStepsN_trans hSteps1N hStepCmpN
        have h123 : ArmStepsN prog s s2.nextPC (k1 + 1 + 1) := ArmStepsN_trans h12 hStepBCondN
        have hChain : ArmStepsN prog s s' (k1 + 1 + 1 + k') := ArmStepsN_trans h123 hSteps'N
        refine ⟨s', k1 + 1 + 1 + k', hChain, ?_, hSimRel'⟩
        intro pc' σ' am' _hCfg
        rw [hInstrs, hk1', hk']; simp [List.length_append, hBS]; omega
  | arrStore hinstr hidx hval hbounds =>
    rename_i ty idxVal arr idx val
    have heq : instr = .arrStore arr idx val ty := Option.some.inj (hInstr.symm.trans hinstr)
    rw [heq] at hSome hMapped
    have hNotFregIdx : ∀ r, layout idx ≠ some (.freg r) :=
      hWTL.int_not_freg (by have := hTS idx; rw [hidx] at this; exact this.symm)
    let idx_reg := match layout idx with | some (.ireg r) => r | _ => ArmReg.x1
    by_cases hFloat : ty = .float
    · rw [hFloat] at hSome
      have hNotIregVal : ∀ r, layout val ≠ some (.ireg r) := by
        have hwti := hWT pc hPC_bound
        rw [Prog.getElem?_eq_getElem hPC_bound |>.symm.trans hinstr |> Option.some.inj] at hwti
        exact match hwti with | .arrStore _ hv _ => hWTL.float_not_ireg (hv.trans hFloat)
      let val_freg := match layout val with | some (.freg r) => r | _ => ArmFReg.d0
      have hInstrs : instrs = vLoadVar layout idx idx_reg ++
          ((if boundsSafe then [] else
            [.cmpImm idx_reg (arraySizeBv arrayDecls arr), .bCond .hs boundsLabel]) ++
          (vLoadVarFP layout val val_freg ++ [.farrSt arr idx_reg val_freg])) := by
        simp [verifiedGenInstr, hRC, hII] at hSome; exact hSome.symm
      rw [hInstrs] at hCodeInstr hPcNext
      have hCodeA := hCodeInstr.append_left
      have hCodeBCD := hCodeInstr.append_right
      obtain ⟨s1, k1, hSteps1N, hk1, hX1_1, hRel1, _, hPC1, hAM1, hRegs1⟩ :=
        vLoadVar_eff_exec prog layout idx σ s (pcMap pc) .x1 hStateRel hRegConv hPcRel
          hNotFregIdx (Or.inr (Or.inl rfl)) (hMapped idx (by simp [TAC.vars])) hCodeA
      have hk1' : k1 = (vLoadVar layout idx idx_reg).length := hk1
      have hIdxVal : s1.regs idx_reg = idxVal := by rw [hX1_1, hidx]; simp [Value.encode]
      cases hBS : boundsSafe with
      | true =>
        simp [hBS] at hCodeBCD
        have hCodeValSt := hCodeBCD; rw [← hPC1] at hCodeValSt
        have hCodeVal := hCodeValSt.append_left
        obtain ⟨s2, k2, hSteps2N, hk2, hFVal_2, hRel2, hRegs2eq, hPC2, hAM2, hFregs2, hStack2⟩ :=
          vLoadVarFP_eff_exec prog layout val σ s1 s1.pc .d0 hRel1 hRegConv rfl
            hNotIregVal (Or.inl rfl) (hMapped val (by simp [TAC.vars])) hCodeVal
        have hk2' : k2 = (vLoadVarFP layout val val_freg).length := hk2
        have hIdxVal2 : s2.regs idx_reg = idxVal := by rw [hRegs2eq]; exact hIdxVal
        have hValEnc : s2.fregs val_freg = (σ val).encode := by rw [hFVal_2]
        have hCodeFarrSt := hCodeValSt.append_right; rw [← hPC2] at hCodeFarrSt
        have hFarrSt := hCodeFarrSt.head
        let s3 := s2.setArrayMem arr (s2.regs idx_reg) (s2.fregs val_freg) |>.nextPC
        have hStepFarrStN : ArmStepsN prog s2 s3 1 :=
          ArmStepsN.single (.farrSt arr idx_reg val_freg hFarrSt)
        have hRel3 : ExtStateRel layout σ s3 := by
          simp [s3, ArmState.setArrayMem, ArmState.nextPC]; exact hRel2.nextPC
        have hPC3 : s3.pc = pcMap (pc + 1) := by
          have := hPcNext _ _ rfl; simp [hBS] at this
          have hPC_s3 : s3.pc = pcMap pc + (vLoadVar layout idx idx_reg).length +
              (vLoadVarFP layout val val_freg).length + 1 := by
            simp [s3, ArmState.setArrayMem, ArmState.nextPC]; rw [hPC2, hPC1]
          rw [hPC_s3]; omega
        have hAM3 : s3.arrayMem = am.write arr idxVal (σ val).toBits := by
          funext a i
          simp only [s3, ArmState.setArrayMem, ArmState.nextPC, ArrayMem.write,
                hIdxVal2, hValEnc, hAM2, hAM1, hArrayMem, Value.encode, Value.toBits]
          rfl
        have h12 : ArmStepsN prog s s2 (k1 + k2) := ArmStepsN_trans hSteps1N hSteps2N
        have hChain : ArmStepsN prog s s3 (k1 + k2 + 1) := ArmStepsN_trans h12 hStepFarrStN
        refine ⟨s3, k1 + k2 + 1, hChain, ?_, hRel3, hPC3, hAM3⟩
        intro pc' σ' am' _hCfg
        rw [hInstrs, hk1', hk2']; simp [List.length_append, hBS]; omega
      | false =>
        simp [hBS] at hCodeBCD
        have hCmp := hCodeBCD.head; rw [← hPC1] at hCmp
        let s2bc := { s1 with flags := Flags.mk (s1.regs idx_reg) (arraySizeBv arrayDecls arr), pc := s1.pc + 1 }
        have hStepCmpN : ArmStepsN prog s1 s2bc 1 :=
          ArmStepsN.single (.cmpRI idx_reg (arraySizeBv arrayDecls arr) hCmp)
        have hBoundsAD : idxVal < arraySizeBv arrayDecls arr := by rw [hAD]; exact hbounds
        have hCondFalse : s2bc.flags.condHolds .hs = false := by
          simp only [s2bc, Flags.condHolds, hIdxVal]
          cases h : decide (arraySizeBv arrayDecls arr ≤ idxVal) <;> simp_all <;> bv_omega
        have hPC2bc : s2bc.pc = pcMap pc + (vLoadVar layout idx idx_reg).length + 1 := by
          show s1.pc + 1 = _; rw [hPC1]
        have hBCond := hCodeBCD.tail.head; rw [← hPC2bc] at hBCond
        have hStepBCondN : ArmStepsN prog s2bc s2bc.nextPC 1 :=
          ArmStepsN.single (.bCond_fall .hs boundsLabel hBCond hCondFalse)
        have hRel1bc : ExtStateRel layout σ s2bc.nextPC := hRel1.nextPC
        have hIdxValBC : s2bc.nextPC.regs idx_reg = idxVal := by
          simp [ArmState.nextPC, s2bc]; exact hIdxVal
        have hPC_post_bc : s2bc.nextPC.pc = pcMap pc + (vLoadVar layout idx idx_reg).length + 2 := by
          simp [ArmState.nextPC, s2bc]; rw [hPC1]
        have hCodeValSt : CodeAt prog s2bc.nextPC.pc
            (vLoadVarFP layout val val_freg ++ [.farrSt arr idx_reg val_freg]) := by
          rw [hPC_post_bc]; exact hCodeBCD.tail.tail
        have hCodeVal := hCodeValSt.append_left
        obtain ⟨s2, k2, hSteps2N, hk2, hFVal_2, hRel2, hRegs2eq, hPC2, hAM2, hFregs2, hStack2⟩ :=
          vLoadVarFP_eff_exec prog layout val σ s2bc.nextPC s2bc.nextPC.pc .d0
            hRel1bc hRegConv rfl hNotIregVal (Or.inl rfl)
            (hMapped val (by simp [TAC.vars])) hCodeVal
        have hk2' : k2 = (vLoadVarFP layout val val_freg).length := hk2
        have hIdxVal2 : s2.regs idx_reg = idxVal := by rw [hRegs2eq]; exact hIdxValBC
        have hValEnc : s2.fregs val_freg = (σ val).encode := by rw [hFVal_2]
        have hCodeFarrSt := hCodeValSt.append_right; rw [← hPC2] at hCodeFarrSt
        have hFarrSt := hCodeFarrSt.head
        let s3 := s2.setArrayMem arr (s2.regs idx_reg) (s2.fregs val_freg) |>.nextPC
        have hStepFarrStN : ArmStepsN prog s2 s3 1 :=
          ArmStepsN.single (.farrSt arr idx_reg val_freg hFarrSt)
        have hRel3 : ExtStateRel layout σ s3 := by
          simp [s3, ArmState.setArrayMem, ArmState.nextPC]; exact hRel2.nextPC
        have hAM_bc : s2bc.nextPC.arrayMem = am := by
          simp [ArmState.nextPC, s2bc, hAM1, hArrayMem]
        have hAM2' : s2.arrayMem = am := by rw [hAM2, hAM_bc]
        have hPC3 : s3.pc = pcMap (pc + 1) := by
          have := hPcNext _ _ rfl; simp [hBS] at this
          have hPC_s3 : s3.pc = pcMap pc + (vLoadVar layout idx idx_reg).length + 2 +
              (vLoadVarFP layout val val_freg).length + 1 := by
            simp [s3, ArmState.setArrayMem, ArmState.nextPC]
            rw [hPC2, hPC_post_bc]
          rw [hPC_s3]; omega
        have hAM3 : s3.arrayMem = am.write arr idxVal (σ val).toBits := by
          funext a i
          simp only [s3, ArmState.setArrayMem, ArmState.nextPC, ArrayMem.write,
                hIdxVal2, hValEnc, hAM2', Value.encode, Value.toBits]
          rfl
        have h12 : ArmStepsN prog s s2bc (k1 + 1) := ArmStepsN_trans hSteps1N hStepCmpN
        have h123 : ArmStepsN prog s s2bc.nextPC (k1 + 1 + 1) := ArmStepsN_trans h12 hStepBCondN
        have h1234 : ArmStepsN prog s s2 (k1 + 1 + 1 + k2) := ArmStepsN_trans h123 hSteps2N
        have hChain : ArmStepsN prog s s3 (k1 + 1 + 1 + k2 + 1) := ArmStepsN_trans h1234 hStepFarrStN
        refine ⟨s3, k1 + 1 + 1 + k2 + 1, hChain, ?_, hRel3, hPC3, hAM3⟩
        intro pc' σ' am' _hCfg
        rw [hInstrs, hk1', hk2']; simp [List.length_append, hBS]; omega
    · have hNotFloat : (ty == .float) = false := by cases ty <;> simp_all
      have hNotFregVal : ∀ r, layout val ≠ some (.freg r) := by
        have hTyVal : tyCtx val = ty := by
          have hwti := hWT pc hPC_bound
          rw [Prog.getElem?_eq_getElem hPC_bound |>.symm.trans hinstr |> Option.some.inj] at hwti
          exact match hwti with | .arrStore _ hv _ => hv
        intro r h
        cases ty with
        | int => exact absurd h (hWTL.int_not_freg (by rw [hTyVal]) r)
        | bool => exact absurd h (hWTL.bool_not_freg (by rw [hTyVal]) r)
        | float => exact absurd rfl hFloat
      let val_reg := match layout val with | some (.ireg r) => r | _ => ArmReg.x2
      have hInstrs : instrs = vLoadVar layout idx idx_reg ++
          ((if boundsSafe then [] else
            [.cmpImm idx_reg (arraySizeBv arrayDecls arr), .bCond .hs boundsLabel]) ++
          (vLoadVar layout val val_reg ++ [.arrSt arr idx_reg val_reg])) := by
        simp [verifiedGenInstr, hRC, hII, hNotFloat] at hSome; exact hSome.symm
      rw [hInstrs] at hCodeInstr hPcNext
      have hCodeA := hCodeInstr.append_left
      have hCodeBCD := hCodeInstr.append_right
      obtain ⟨s1, k1, hSteps1N, hk1, hX1_1, hRel1, _, hPC1, hAM1, hRegs1⟩ :=
        vLoadVar_eff_exec prog layout idx σ s (pcMap pc) .x1 hStateRel hRegConv hPcRel
          hNotFregIdx (Or.inr (Or.inl rfl)) (hMapped idx (by simp [TAC.vars])) hCodeA
      have hk1' : k1 = (vLoadVar layout idx idx_reg).length := hk1
      have hIdxVal : s1.regs idx_reg = idxVal := by rw [hX1_1, hidx]; simp [Value.encode]
      cases hBS : boundsSafe with
      | true =>
        simp [hBS] at hCodeBCD
        have hCodeVal := hCodeBCD.append_left; rw [← hPC1] at hCodeVal
        obtain ⟨s2, k2, hSteps2N, hk2, hVal_2, hRel2, _, hPC2, hAM2, hRegs2⟩ :=
          vLoadVar_eff_exec prog layout val σ s1 s1.pc .x2 hRel1 hRegConv rfl
            hNotFregVal (Or.inr (Or.inr rfl)) (hMapped val (by simp [TAC.vars])) hCodeVal
        have hk2' : k2 = (vLoadVar layout val val_reg).length := hk2
        have hIdxVal2 : s2.regs idx_reg = idxVal := by
          match hLI : layout idx with
          | some (.ireg r) =>
            have hir : idx_reg = r := by
              show (match layout idx with | some (.ireg r) => r | _ => .x1) = r; simp [hLI]
            rw [hir, hRel2.read_ireg hLI, hidx]; simp [Value.encode]
          | some (.stack _) | none =>
            have hir : idx_reg = .x1 := by
              show (match layout idx with | some (.ireg r) => r | _ => .x1) = .x1; simp [hLI]
            rw [hir]
            have hne : ArmReg.x1 ≠ (match layout val with | some (.ireg r) => r | _ => .x2) := by
              match hLV : layout val with
              | some (.ireg rv) =>
                show ArmReg.x1 ≠ rv
                intro h; exact hRegConv.not_x1 val (h ▸ hLV)
              | some (.stack _) | none | some (.freg _) =>
                show ArmReg.x1 ≠ .x2; decide
            rw [hRegs2 .x1 hne, ← hir, hIdxVal]
          | some (.freg r) => exact absurd hLI (hNotFregIdx r)
        have hValEnc : s2.regs val_reg = (σ val).encode := by rw [hVal_2]
        have hPC2' : s2.pc = pcMap pc + (vLoadVar layout idx idx_reg).length +
            (vLoadVar layout val val_reg).length := by rw [hPC2, hPC1]
        have hCodeArrSt := hCodeBCD.append_right; rw [← hPC2'] at hCodeArrSt
        have hArrSt := hCodeArrSt.head
        let s3 := s2.setArrayMem arr (s2.regs idx_reg) (s2.regs val_reg) |>.nextPC
        have hStepArrStN : ArmStepsN prog s2 s3 1 :=
          ArmStepsN.single (.arrSt arr idx_reg val_reg hArrSt)
        have hRel3 : ExtStateRel layout σ s3 := by
          simp [s3, ArmState.setArrayMem, ArmState.nextPC]; exact hRel2.nextPC
        have hPC3 : s3.pc = pcMap (pc + 1) := by
          have := hPcNext _ _ rfl; simp [hBS] at this
          simp [s3, ArmState.setArrayMem, ArmState.nextPC]; rw [hPC2]; omega
        have hAM3 : s3.arrayMem = am.write arr idxVal (σ val).toBits := by
          funext a i
          simp only [s3, ArmState.setArrayMem, ArmState.nextPC, ArrayMem.write,
                hIdxVal2, hValEnc, hAM2, hAM1, hArrayMem, Value.encode, Value.toBits]
          rfl
        have h12 : ArmStepsN prog s s2 (k1 + k2) := ArmStepsN_trans hSteps1N hSteps2N
        have hChain : ArmStepsN prog s s3 (k1 + k2 + 1) := ArmStepsN_trans h12 hStepArrStN
        refine ⟨s3, k1 + k2 + 1, hChain, ?_, hRel3, hPC3, hAM3⟩
        intro pc' σ' am' _hCfg
        rw [hInstrs, hk1', hk2']; simp [List.length_append, hBS]; omega
      | false =>
        simp [hBS] at hCodeBCD
        have hCmp := hCodeBCD.head; rw [← hPC1] at hCmp
        let s2bc := { s1 with flags := Flags.mk (s1.regs idx_reg) (arraySizeBv arrayDecls arr), pc := s1.pc + 1 }
        have hStepCmpN : ArmStepsN prog s1 s2bc 1 :=
          ArmStepsN.single (.cmpRI idx_reg (arraySizeBv arrayDecls arr) hCmp)
        have hBoundsAD : idxVal < arraySizeBv arrayDecls arr := by rw [hAD]; exact hbounds
        have hCondFalse : s2bc.flags.condHolds .hs = false := by
          simp only [s2bc, Flags.condHolds, hIdxVal]
          cases h : decide (arraySizeBv arrayDecls arr ≤ idxVal) <;> simp_all <;> bv_omega
        have hPC2bc : s2bc.pc = pcMap pc + (vLoadVar layout idx idx_reg).length + 1 := by
          show s1.pc + 1 = _; rw [hPC1]
        have hBCond := hCodeBCD.tail.head; rw [← hPC2bc] at hBCond
        have hStepBCondN : ArmStepsN prog s2bc s2bc.nextPC 1 :=
          ArmStepsN.single (.bCond_fall .hs boundsLabel hBCond hCondFalse)
        have hRel1bc : ExtStateRel layout σ s2bc.nextPC := hRel1.nextPC
        have hIdxValBC : s2bc.nextPC.regs idx_reg = idxVal := by
          simp [ArmState.nextPC, s2bc]; exact hIdxVal
        have hPC_post_bc : s2bc.nextPC.pc = pcMap pc + (vLoadVar layout idx idx_reg).length + 2 := by
          simp [ArmState.nextPC, s2bc]; rw [hPC1]
        have hCodeValSt : CodeAt prog s2bc.nextPC.pc
            (vLoadVar layout val val_reg ++ [.arrSt arr idx_reg val_reg]) := by
          rw [hPC_post_bc]; exact hCodeBCD.tail.tail
        have hCodeVal := hCodeValSt.append_left
        obtain ⟨s2, k2, hSteps2N, hk2, hVal_2, hRel2, _, hPC2, hAM2, hRegs2⟩ :=
          vLoadVar_eff_exec prog layout val σ s2bc.nextPC s2bc.nextPC.pc .x2
            hRel1bc hRegConv rfl hNotFregVal (Or.inr (Or.inr rfl))
            (hMapped val (by simp [TAC.vars])) hCodeVal
        have hk2' : k2 = (vLoadVar layout val val_reg).length := hk2
        have hIdxVal2 : s2.regs idx_reg = idxVal := by
          match hLI : layout idx with
          | some (.ireg r) =>
            have hir : idx_reg = r := by
              show (match layout idx with | some (.ireg r) => r | _ => .x1) = r; simp [hLI]
            rw [hir, hRel2.read_ireg hLI, hidx]; simp [Value.encode]
          | some (.stack _) | none =>
            have hir : idx_reg = .x1 := by
              show (match layout idx with | some (.ireg r) => r | _ => .x1) = .x1; simp [hLI]
            rw [hir]
            have hne : ArmReg.x1 ≠ (match layout val with | some (.ireg r) => r | _ => .x2) := by
              match hLV : layout val with
              | some (.ireg rv) =>
                show ArmReg.x1 ≠ rv
                intro h; exact hRegConv.not_x1 val (h ▸ hLV)
              | some (.stack _) | none | some (.freg _) =>
                show ArmReg.x1 ≠ .x2; decide
            rw [hRegs2 .x1 hne, ← hir, hIdxValBC]
          | some (.freg r) => exact absurd hLI (hNotFregIdx r)
        have hValEnc : s2.regs val_reg = (σ val).encode := by rw [hVal_2]
        have hCodeArrSt := hCodeValSt.append_right; rw [← hPC2] at hCodeArrSt
        have hArrSt := hCodeArrSt.head
        let s3 := s2.setArrayMem arr (s2.regs idx_reg) (s2.regs val_reg) |>.nextPC
        have hStepArrStN : ArmStepsN prog s2 s3 1 :=
          ArmStepsN.single (.arrSt arr idx_reg val_reg hArrSt)
        have hRel3 : ExtStateRel layout σ s3 := by
          simp [s3, ArmState.setArrayMem, ArmState.nextPC]; exact hRel2.nextPC
        have hPC3 : s3.pc = pcMap (pc + 1) := by
          have := hPcNext _ _ rfl; simp [hBS] at this
          have hPC_s3 : s3.pc = pcMap pc + (vLoadVar layout idx idx_reg).length + 2 +
              (vLoadVar layout val val_reg).length + 1 := by
            simp [s3, ArmState.setArrayMem, ArmState.nextPC]
            rw [hPC2]; simp [ArmState.nextPC]; rw [hPC2bc]
          rw [hPC_s3]; omega
        have hAM_bc : s2bc.nextPC.arrayMem = am := by
          simp [ArmState.nextPC, s2bc, hAM1, hArrayMem]
        have hAM2' : s2.arrayMem = am := by rw [hAM2, hAM_bc]
        have hAM3 : s3.arrayMem = am.write arr idxVal (σ val).toBits := by
          funext a i
          simp only [s3, ArmState.setArrayMem, ArmState.nextPC, ArrayMem.write,
                hIdxVal2, hValEnc, hAM2', Value.encode, Value.toBits]
          rfl
        have h12 : ArmStepsN prog s s2bc (k1 + 1) := ArmStepsN_trans hSteps1N hStepCmpN
        have h123 : ArmStepsN prog s s2bc.nextPC (k1 + 1 + 1) := ArmStepsN_trans h12 hStepBCondN
        have h1234 : ArmStepsN prog s s2 (k1 + 1 + 1 + k2) := ArmStepsN_trans h123 hSteps2N
        have hChain : ArmStepsN prog s s3 (k1 + 1 + 1 + k2 + 1) := ArmStepsN_trans h1234 hStepArrStN
        refine ⟨s3, k1 + 1 + 1 + k2 + 1, hChain, ?_, hRel3, hPC3, hAM3⟩
        intro pc' σ' am' _hCfg
        rw [hInstrs, hk1', hk2']; simp [List.length_append, hBS]; omega
  | fbinop hinstr hy hz =>
    rename_i x fop y z a b
    have heq : instr = .fbinop x fop y z := Option.some.inj (hInstr.symm.trans hinstr)
    rw [heq] at hSome hMapped
    have hNotIregY : ∀ r, layout y ≠ some (.ireg r) := by
      intro r h; have := hSome; simp [verifiedGenInstr, hRC, hII, h] at this
    have hNotIregZ : ∀ r, layout z ≠ some (.ireg r) := by
      intro r h; have := hSome; simp [verifiedGenInstr, hRC, hII, h] at this
    have hNotIregX : ∀ r, layout x ≠ some (.ireg r) := by
      intro r h; have := hSome; simp [verifiedGenInstr, hRC, hII, h] at this
    let lv_reg := match layout y with | some (.freg r) => r | _ => ArmFReg.d1
    let rv_reg := match layout z with | some (.freg r) => r | _ => ArmFReg.d2
    let dst_reg := match layout x with | some (.freg r) => r | _ => ArmFReg.d0
    suffices hSimple : ∀ (fpOp : ArmInstr),
        instrs = vLoadVarFP layout y lv_reg ++
          (vLoadVarFP layout z rv_reg ++ (fpOp :: vStoreVarFP layout x dst_reg)) →
        (∀ s', prog[s'.pc]? = some fpOp →
          ArmStep prog s' (s'.setFReg dst_reg (FloatBinOp.eval fop (s'.fregs lv_reg) (s'.fregs rv_reg)) |>.nextPC)) →
        ∃ s' k, ArmStepsN prog s s' k ∧
          (∀ pc' σ' am', (.run (pc + 1) (σ[x ↦ .float (fop.eval a b)]) am : Cfg) = .run pc' σ' am' → k = instrs.length) ∧
          ExtSimRel layout pcMap divLabel boundsLabel
            (.run (pc + 1) (σ[x ↦ .float (fop.eval a b)]) am) s' by
      cases fop with
      | fadd =>
        apply hSimple
        · have := hSome; simp [verifiedGenInstr, hRC, hII] at this; exact this.symm
        · exact fun _ h => .faddR dst_reg lv_reg rv_reg h
      | fsub =>
        apply hSimple
        · have := hSome; simp [verifiedGenInstr, hRC, hII] at this; exact this.symm
        · exact fun _ h => .fsubR dst_reg lv_reg rv_reg h
      | fmul =>
        apply hSimple
        · have := hSome; simp [verifiedGenInstr, hRC, hII] at this; exact this.symm
        · exact fun _ h => .fmulR dst_reg lv_reg rv_reg h
      | fdiv =>
        apply hSimple
        · have := hSome; simp [verifiedGenInstr, hRC, hII] at this; exact this.symm
        · exact fun _ h => .fdivR dst_reg lv_reg rv_reg h
      | fpow =>
        have hNCS : NoCallerSavedLayout layout := hNCSLBin x y z heq
        have hInstrs : instrs = vLoadVarFP layout y lv_reg ++
            (vLoadVarFP layout z rv_reg ++ (.callBinF .fpow dst_reg lv_reg rv_reg :: vStoreVarFP layout x dst_reg)) := by
          have := hSome; simp [verifiedGenInstr, hRC, hII] at this; exact this.symm
        rw [hInstrs] at hCodeInstr hPcNext
        have hCodeA := hCodeInstr.append_left
        have hCodeBCD := hCodeInstr.append_right
        have hCodeB := hCodeBCD.append_left
        have hCodeCD := hCodeBCD.append_right
        obtain ⟨s1, k1, hSteps1N, hk1, hLV_1, hRel1, hRegs1, hPC1, hAM1, hFregs1, hStack1⟩ :=
          vLoadVarFP_eff_exec prog layout y σ s (pcMap pc) .d1 hStateRel hRegConv hPcRel
            hNotIregY (Or.inr (Or.inl rfl)) (hMapped y (by simp [TAC.vars])) hCodeA
        have hk1' : k1 = (vLoadVarFP layout y lv_reg).length := hk1
        obtain ⟨s2, k2, hSteps2N, hk2, hRV_2, hRel2, hRegs2, hPC2_, hAM2, hFregs2, hStack2⟩ :=
          vLoadVarFP_eff_exec prog layout z σ s1 _ .d2 hRel1 hRegConv hPC1
            hNotIregZ (Or.inr (Or.inr rfl)) (hMapped z (by simp [TAC.vars])) hCodeB
        have hk2' : k2 = (vLoadVarFP layout z rv_reg).length := hk2
        have hPC2 : s2.pc = pcMap pc + (vLoadVarFP layout y lv_reg).length +
            (vLoadVarFP layout z rv_reg).length := hPC2_
        have hLV_2 : s2.fregs lv_reg = a := by
          match hLY : layout y with
          | some (.freg ry) =>
            have hlv : lv_reg = ry := by
              show (match layout y with | some (.freg r) => r | _ => .d1) = ry; simp [hLY]
            rw [hlv, hRel2.read_freg hLY, hy]; rfl
          | some (.stack _) | none =>
            have hlv : lv_reg = .d1 := by
              show (match layout y with | some (.freg r) => r | _ => .d1) = .d1; simp [hLY]
            rw [hlv]
            have hne : ArmFReg.d1 ≠ rv_reg := by
              intro h
              match hLZ : layout z with
              | some (.freg rz) =>
                have hrv : rv_reg = rz := by
                  show (match layout z with | some (.freg r) => r | _ => .d2) = rz; simp [hLZ]
                rw [hrv] at h; exact hRegConv.not_d1 z (h ▸ hLZ)
              | some (.stack _) | none =>
                have hrv : rv_reg = .d2 := by
                  show (match layout z with | some (.freg r) => r | _ => .d2) = .d2; simp [hLZ]
                rw [hrv] at h; exact absurd h (by decide)
              | some (.ireg r) => exact absurd hLZ (hNotIregZ r)
            rw [hFregs2 .d1 hne, ← hlv, hLV_1, hy]; rfl
          | some (.ireg r) => exact absurd hLY (hNotIregY r)
        have hCall := hCodeCD.head; rw [← hPC2] at hCall
        let newRegs : ArmReg → BitVec 64 := havocRegsFn s2
        let newFregs : ArmFReg → BitVec 64 := havocFRegsFn s2
        have hRV_eq : s2.fregs rv_reg = b := by rw [hRV_2, hz]; rfl
        let s3 := (s2.havocCallerSaved newRegs newFregs) |>.setFReg dst_reg
          (FloatBinOp.eval .fpow (s2.fregs lv_reg) (s2.fregs rv_reg)) |>.nextPC
        have hStep3N : ArmStepsN prog s2 s3 1 :=
          ArmStepsN.single (.callBinF .fpow dst_reg lv_reg rv_reg hCall)
        have hDR_3 : s3.fregs dst_reg = (Value.float (FloatBinOp.eval .fpow a b)).encode := by
          simp [s3, ArmState.setFReg, ArmState.nextPC, ArmState.havocCallerSaved, Value.encode]
          rw [hLV_2, hRV_eq]
        have hPC3 : s3.pc = pcMap pc + (vLoadVarFP layout y lv_reg).length +
            (vLoadVarFP layout z rv_reg).length + 1 := by
          simp only [s3, ArmState.nextPC, ArmState.setFReg, ArmState.havocCallerSaved] at hPC2 ⊢; omega
        have hAM3 : s3.arrayMem = s2.arrayMem := by simp [s3, ArmState.havocCallerSaved]
        have hRelHavoc : ExtStateRel layout σ (s2.havocCallerSaved newRegs newFregs) :=
          ExtStateRel.havocCallerSaved_preserved hRel2 hNCS
        by_cases hXFR : ∃ r, layout x = some (.freg r)
        · obtain ⟨r_dst, hDst⟩ := hXFR
          have hDR : dst_reg = r_dst := by
            change (match layout x with | some (.freg r) => r | _ => .d0) = r_dst; rw [hDst]
          have hStore : vStoreVarFP layout x dst_reg = [] := by simp [vStoreVarFP, hDst, hDR]
          have hRel4 : ExtStateRel layout (σ[x ↦ .float (FloatBinOp.eval .fpow a b)]) s3 := by
            show ExtStateRel layout (σ[x ↦ .float (FloatBinOp.eval .fpow a b)])
              ((s2.havocCallerSaved newRegs newFregs) |>.setFReg dst_reg
                (FloatBinOp.eval .fpow (s2.fregs lv_reg) (s2.fregs rv_reg))).nextPC
            rw [hDR]
            have hval : FloatBinOp.eval .fpow (s2.fregs lv_reg) (s2.fregs rv_reg) =
                (Value.float (FloatBinOp.eval .fpow a b)).encode := by
              simp [Value.encode]; rw [hLV_2, hRV_eq]
            rw [hval]
            exact (ExtStateRel.update_freg hRelHavoc hInjective hDst).nextPC
          have h12 : ArmStepsN prog s s2 (k1 + k2) := ArmStepsN_trans hSteps1N hSteps2N
          have hChain : ArmStepsN prog s s3 (k1 + k2 + 1) := ArmStepsN_trans h12 hStep3N
          refine ⟨s3, k1 + k2 + 1, hChain, ?_, hRel4, ?_, ?_⟩
          · intro pc' σ' am' _hCfg
            rw [hInstrs, hk1', hk2', hStore]; simp [List.length_append]; omega
          · show s3.pc = pcMap (pc + 1)
            have := hPcNext _ _ rfl; simp [hStore] at this; omega
          · simp [hAM3, hAM2, hAM1, hArrayMem]
        · have hDR : dst_reg = .d0 := by
            change (match layout x with | some (.freg r) => r | _ => .d0) = .d0
            split
            · next r h => exact absurd ⟨r, h⟩ hXFR
            · rfl
          have hRel3 : ExtStateRel layout σ s3 := by
            show ExtStateRel layout σ
              ((s2.havocCallerSaved newRegs newFregs) |>.setFReg dst_reg
                (FloatBinOp.eval .fpow (s2.fregs lv_reg) (s2.fregs rv_reg))).nextPC
            rw [hDR]; exact (ExtStateRel.setFReg_preserved hRelHavoc (fun v => hRegConv.not_d0 v)).nextPC
          have hD0 : s3.fregs .d0 = (Value.float (FloatBinOp.eval .fpow a b)).encode := by
            rw [← hDR]; exact hDR_3
          have hCodeStore : CodeAt prog
              (pcMap pc + (vLoadVarFP layout y lv_reg).length +
                (vLoadVarFP layout z rv_reg).length + 1)
              (vStoreVarFP layout x .d0) := by
            rw [← hDR]
            exact hCodeCD.tail
          obtain ⟨s4, k4, hSteps4N, hk4, hRel4, hPC4, hAM4⟩ :=
            vStoreVarFP_exec prog layout x (Value.float (FloatBinOp.eval .fpow a b)) σ s3
              (pcMap pc + (vLoadVarFP layout y lv_reg).length +
                (vLoadVarFP layout z rv_reg).length + 1)
              hRel3 hInjective hRegConv hPC3 hD0 hCodeStore hNotIregX
              (fun r h => absurd ⟨r, h⟩ hXFR)
          have hk4' : k4 = (vStoreVarFP layout x dst_reg).length := by rw [hDR]; exact hk4
          have h12 : ArmStepsN prog s s2 (k1 + k2) := ArmStepsN_trans hSteps1N hSteps2N
          have h123 : ArmStepsN prog s s3 (k1 + k2 + 1) := ArmStepsN_trans h12 hStep3N
          have hChain : ArmStepsN prog s s4 (k1 + k2 + 1 + k4) := ArmStepsN_trans h123 hSteps4N
          refine ⟨s4, k1 + k2 + 1 + k4, hChain, ?_, hRel4, ?_, ?_⟩
          · intro pc' σ' am' _hCfg
            rw [hInstrs, hk1', hk2', hk4']; simp [List.length_append]; omega
          · show s4.pc = pcMap (pc + 1)
            have := hPcNext _ _ rfl; rw [show dst_reg = ArmFReg.d0 from hDR] at this; simp at this
            omega
          · simp [hAM4, hAM3, hAM2, hAM1, hArrayMem]
      | fmin =>
        apply hSimple
        · have := hSome; simp [verifiedGenInstr, hRC, hII] at this; exact this.symm
        · exact fun _ h => .fminR dst_reg lv_reg rv_reg h
      | fmax =>
        apply hSimple
        · have := hSome; simp [verifiedGenInstr, hRC, hII] at this; exact this.symm
        · exact fun _ h => .fmaxR dst_reg lv_reg rv_reg h
    -- Proof of hSimple
    intro fpOp hInstrs hArmStep
    rw [hInstrs] at hCodeInstr hPcNext
    have hCodeA := hCodeInstr.append_left
    have hCodeBCD := hCodeInstr.append_right
    have hCodeB := hCodeBCD.append_left
    have hCodeCD := hCodeBCD.append_right
    obtain ⟨s1, k1, hSteps1N, hk1, hLV_1, hRel1, hRegs1, hPC1, hAM1, hFregs1, hStack1⟩ :=
      vLoadVarFP_eff_exec prog layout y σ s (pcMap pc) .d1 hStateRel hRegConv hPcRel
        hNotIregY (Or.inr (Or.inl rfl)) (hMapped y (by simp [TAC.vars])) hCodeA
    have hk1' : k1 = (vLoadVarFP layout y lv_reg).length := hk1
    obtain ⟨s2, k2, hSteps2N, hk2, hRV_2, hRel2, hRegs2, hPC2_, hAM2, hFregs2, hStack2⟩ :=
      vLoadVarFP_eff_exec prog layout z σ s1 _ .d2 hRel1 hRegConv hPC1
        hNotIregZ (Or.inr (Or.inr rfl)) (hMapped z (by simp [TAC.vars])) hCodeB
    have hk2' : k2 = (vLoadVarFP layout z rv_reg).length := hk2
    have hPC2 : s2.pc = pcMap pc + (vLoadVarFP layout y lv_reg).length +
        (vLoadVarFP layout z rv_reg).length := hPC2_
    have hLV_2 : s2.fregs lv_reg = a := by
      match hLY : layout y with
      | some (.freg ry) =>
        have hlv : lv_reg = ry := by
          show (match layout y with | some (.freg r) => r | _ => .d1) = ry; simp [hLY]
        rw [hlv, hRel2.read_freg hLY, hy]; rfl
      | some (.stack _) | none =>
        have hlv : lv_reg = .d1 := by
          show (match layout y with | some (.freg r) => r | _ => .d1) = .d1; simp [hLY]
        rw [hlv]
        have hne : ArmFReg.d1 ≠ rv_reg := by
          intro h
          match hLZ : layout z with
          | some (.freg rz) =>
            have hrv : rv_reg = rz := by
              show (match layout z with | some (.freg r) => r | _ => .d2) = rz; simp [hLZ]
            rw [hrv] at h; exact hRegConv.not_d1 z (h ▸ hLZ)
          | some (.stack _) | none =>
            have hrv : rv_reg = .d2 := by
              show (match layout z with | some (.freg r) => r | _ => .d2) = .d2; simp [hLZ]
            rw [hrv] at h; exact absurd h (by decide)
          | some (.ireg r) => exact absurd hLZ (hNotIregZ r)
        rw [hFregs2 .d1 hne, ← hlv, hLV_1, hy]; rfl
      | some (.ireg r) => exact absurd hLY (hNotIregY r)
    have hRV_eq : s2.fregs rv_reg = b := by rw [hRV_2, hz]; rfl
    have hOp := hCodeCD.head; rw [← hPC2_] at hOp
    let s3 := (s2.setFReg dst_reg (FloatBinOp.eval fop a b)).nextPC
    have hStep3N : ArmStepsN prog s2 s3 1 := by
      have h := ArmStepsN.single (hArmStep s2 hOp)
      rwa [hLV_2, hRV_eq] at h
    have hPC3 : s3.pc = pcMap pc + (vLoadVarFP layout y lv_reg).length +
        (vLoadVarFP layout z rv_reg).length + 1 := by
      show s2.pc + 1 = _; omega
    have hAM3 : s3.arrayMem = s2.arrayMem := by simp [s3]
    by_cases hXFR : ∃ r, layout x = some (.freg r)
    · obtain ⟨r_dst, hDst⟩ := hXFR
      have hDR : dst_reg = r_dst := by
        change (match layout x with | some (.freg r) => r | _ => .d0) = r_dst; rw [hDst]
      have hStore : vStoreVarFP layout x dst_reg = [] := by simp [vStoreVarFP, hDst, hDR]
      have hRel4 : ExtStateRel layout (σ[x ↦ .float (fop.eval a b)]) s3 := by
        show ExtStateRel layout (σ[x ↦ .float (fop.eval a b)])
          (s2.setFReg dst_reg (FloatBinOp.eval fop a b)).nextPC
        rw [hDR]
        have : FloatBinOp.eval fop a b = (Value.float (fop.eval a b)).encode := by
          simp [Value.encode]
        rw [this]
        exact (ExtStateRel.update_freg hRel2 hInjective hDst).nextPC
      have h12 : ArmStepsN prog s s2 (k1 + k2) := ArmStepsN_trans hSteps1N hSteps2N
      have hChain : ArmStepsN prog s s3 (k1 + k2 + 1) := ArmStepsN_trans h12 hStep3N
      refine ⟨s3, k1 + k2 + 1, hChain, ?_, hRel4, ?_, ?_⟩
      · intro pc' σ' am' _hCfg
        rw [hInstrs, hk1', hk2', hStore]; simp [List.length_append]; omega
      · show s3.pc = pcMap (pc + 1)
        have := hPcNext _ _ rfl; simp [hStore] at this; omega
      · simp [hAM3, hAM2, hAM1, hArrayMem]
    · have hDR : dst_reg = .d0 := by
        change (match layout x with | some (.freg r) => r | _ => .d0) = .d0
        split
        · next r h => exact absurd ⟨r, h⟩ hXFR
        · rfl
      have hRel3 : ExtStateRel layout σ s3 := by
        show ExtStateRel layout σ (s2.setFReg dst_reg (FloatBinOp.eval fop a b)).nextPC
        rw [hDR]; exact (ExtStateRel.setFReg_preserved hRel2 (fun v => hRegConv.not_d0 v)).nextPC
      have hD0 : s3.fregs .d0 = (Value.float (fop.eval a b)).encode := by
        simp [s3, hDR, ArmState.setFReg, ArmState.nextPC, Value.encode]
      have hCodeStore : CodeAt prog
          (pcMap pc + (vLoadVarFP layout y lv_reg).length + (vLoadVarFP layout z rv_reg).length + 1)
          (vStoreVarFP layout x .d0) := by rw [← hDR]; exact hCodeCD.tail
      obtain ⟨s4, k4, hSteps4N, hk4, hRel4, hPC4, hAM4⟩ :=
        vStoreVarFP_exec prog layout x (Value.float (fop.eval a b)) σ s3
          (pcMap pc + (vLoadVarFP layout y lv_reg).length + (vLoadVarFP layout z rv_reg).length + 1)
          hRel3 hInjective hRegConv hPC3 hD0 hCodeStore hNotIregX
          (fun r h => absurd ⟨r, h⟩ hXFR)
      have hk4' : k4 = (vStoreVarFP layout x dst_reg).length := by rw [hDR]; exact hk4
      have h12 : ArmStepsN prog s s2 (k1 + k2) := ArmStepsN_trans hSteps1N hSteps2N
      have h123 : ArmStepsN prog s s3 (k1 + k2 + 1) := ArmStepsN_trans h12 hStep3N
      have hChain : ArmStepsN prog s s4 (k1 + k2 + 1 + k4) := ArmStepsN_trans h123 hSteps4N
      refine ⟨s4, k1 + k2 + 1 + k4, hChain, ?_, hRel4, ?_, ?_⟩
      · intro pc' σ' am' _hCfg
        rw [hInstrs, hk1', hk2', hk4']; simp [List.length_append]; omega
      · show s4.pc = pcMap (pc + 1)
        have := hPcNext _ _ rfl; rw [show dst_reg = ArmFReg.d0 from hDR] at this; simp at this
        omega
      · simp [hAM4, hAM3, hAM2, hAM1, hArrayMem]
  | intToFloat hinstr hy =>
    rename_i x y n
    have heq : instr = .intToFloat x y := Option.some.inj (hInstr.symm.trans hinstr)
    rw [heq] at hSome
    have hNotFregY : ∀ r, layout y ≠ some (.freg r) := by
      intro r h; have := hSome; simp [verifiedGenInstr, hRC, hII, h] at this
    have hNotIregX : ∀ r, layout x ≠ some (.ireg r) := by
      intro r h; have := hSome; simp only [verifiedGenInstr, h] at this
      simp_all
    match hLX : layout x with
    | some (.freg r) =>
      have hInstrs : instrs =
        vLoadVar layout y .x0 ++ [ArmInstr.scvtf r .x0] := by
        simp [verifiedGenInstr, hRC, hII, hLX, vStoreVarFP] at hSome
        exact hSome.symm
      rw [hInstrs] at hCodeInstr hPcNext
      have hCodeL := hCodeInstr.append_left
      have hCodeR := hCodeInstr.append_right
      obtain ⟨s1, k1, hSteps1N, hk1, hX0_1, hRel1, hFregs1, hPC1, hAM1, _⟩ :=
        vLoadVar_exec prog layout y .x0 σ s (pcMap pc) hStateRel hRegConv hPcRel hCodeL
          (Or.inl rfl) hNotFregY (hMapped y (by simp [heq, TAC.vars]))
      have hScvtf := hCodeR.head; rw [← hPC1] at hScvtf
      have hX0n : s1.regs .x0 = n := by rw [hX0_1, hy]; rfl
      let s2 := (s1.setFReg r (Value.float (intToFloatBv n)).encode).nextPC
      have hS2eq : (s1.setFReg r (intToFloatBv (s1.regs .x0))).nextPC = s2 := by
        simp [s2, hX0n, Value.encode]
      have hStepN : ArmStepsN prog s1 s2 1 := hS2eq ▸ ArmStepsN.single (.scvtf r .x0 hScvtf)
      have hChain : ArmStepsN prog s s2 (k1 + 1) := ArmStepsN_trans hSteps1N hStepN
      have hPC2 : s2.pc = pcMap pc + (vLoadVar layout y .x0).length + 1 := by
        simp [s2, ArmState.nextPC, hPC1]
      have hAM2 : s2.arrayMem = s1.arrayMem := by simp [s2]
      have hRel2 : ExtStateRel layout (σ[x ↦ Value.float (intToFloatBv n)]) s2 :=
        (ExtStateRel.update_freg hRel1 hInjective hLX).nextPC
      refine ⟨s2, k1 + 1, hChain, ?_, hRel2, ?_, ?_⟩
      · intro pc' σ' am' _hCfg; rw [hInstrs, hk1]; simp [List.length_append]
      · show s2.pc = pcMap (pc + 1)
        have := hPcNext _ _ rfl; simp at this; rw [hPC2]; omega
      · simp [hAM2, hAM1, hArrayMem]
    | some (.ireg r) => exact absurd hLX (hNotIregX r)
    | none =>
      exact absurd hLX (hMapped x (by simp [heq, TAC.vars]))
    | some (.stack _) =>
      have hInstrs : instrs =
        vLoadVar layout y .x0 ++ [ArmInstr.scvtf .d0 .x0] ++ vStoreVarFP layout x .d0 := by
        simp only [verifiedGenInstr, hLX] at hSome
        simp_all
      rw [hInstrs] at hCodeInstr hPcNext
      have hCodeLM := hCodeInstr.append_left
      have hCodeR := hCodeInstr.append_right
      have hCodeL := hCodeLM.append_left
      have hCodeM := hCodeLM.append_right
      obtain ⟨s1, k1, hSteps1N, hk1, hX0_1, hRel1, hFregs1, hPC1, hAM1, _⟩ :=
        vLoadVar_exec prog layout y .x0 σ s (pcMap pc) hStateRel hRegConv hPcRel hCodeL
          (Or.inl rfl) hNotFregY (hMapped y (by simp [heq, TAC.vars]))
      have hScvtf := hCodeM.head; rw [← hPC1] at hScvtf
      let s2 := s1.setFReg .d0 (intToFloatBv (s1.regs .x0)) |>.nextPC
      have hStep2N : ArmStepsN prog s1 s2 1 := ArmStepsN.single (.scvtf .d0 .x0 hScvtf)
      have hD0 : s2.fregs .d0 = (Value.float (intToFloatBv n)).encode := by
        simp [s2, ArmState.setFReg, ArmState.nextPC, Value.encode]
        rw [hX0_1, hy]; rfl
      have hPC2 : s2.pc = pcMap pc + (vLoadVar layout y .x0).length + 1 := by
        simp [s2, ArmState.nextPC, hPC1]
      have hRel2 : ExtStateRel layout σ s2 :=
        (ExtStateRel.setFReg_preserved hRel1 (fun v => hRegConv.not_d0 v)).nextPC
      have hAM2 : s2.arrayMem = s1.arrayMem := by simp [s2]
      obtain ⟨s3, k3, hSteps3N, hk3, hRel3, hPC3, hAM3⟩ :=
        vStoreVarFP_exec prog layout x (Value.float (intToFloatBv n)) σ s2
          (pcMap pc + (vLoadVar layout y .x0).length + 1)
          hRel2 hInjective hRegConv hPC2 hD0
          (by rw [show (vLoadVar layout y .x0 ++ [ArmInstr.scvtf .d0 .x0]).length =
            (vLoadVar layout y .x0).length + 1 from by simp] at hCodeR; exact hCodeR)
          hNotIregX
          (fun r h => by simp [hLX] at h)
      have h12 : ArmStepsN prog s s2 (k1 + 1) := ArmStepsN_trans hSteps1N hStep2N
      have hChain : ArmStepsN prog s s3 (k1 + 1 + k3) := ArmStepsN_trans h12 hSteps3N
      refine ⟨s3, k1 + 1 + k3, hChain, ?_, hRel3, ?_, ?_⟩
      · intro pc' σ' am' _hCfg
        rw [hInstrs, hk1, hk3]; simp [List.length_append]; omega
      · show s3.pc = pcMap (pc + 1)
        have := hPcNext _ _ rfl; simp at this
        omega
      · simp [hAM3, hAM2, hAM1, hArrayMem]
  | floatToInt hinstr hy =>
    rename_i x y f
    have heq : instr = .floatToInt x y := Option.some.inj (hInstr.symm.trans hinstr)
    rw [heq] at hSome
    have hNotIregY : ∀ r, layout y ≠ some (.ireg r) := by
      intro r h; have := hSome; simp [verifiedGenInstr, hRC, hII, h] at this
    have hNotFregX : ∀ r, layout x ≠ some (.freg r) := by
      intro r h; have := hSome; simp only [verifiedGenInstr, h] at this
      simp_all
    match hLY : layout y with
    | some (.freg r) =>
      have hInstrs : instrs =
        [ArmInstr.fcvtzs .x0 r] ++ vStoreVar layout x .x0 := by
        simp [verifiedGenInstr, hRC, hII, hLY, vLoadVarFP] at hSome
        exact hSome.symm
      rw [hInstrs] at hCodeInstr hPcNext
      have hCodeL := hCodeInstr.append_left
      have hCodeR := hCodeInstr.append_right
      have hFregR : s.fregs r = (σ y).encode := hStateRel y (.freg r) hLY
      have hFcvtzs := hCodeL.head; rw [← hPcRel] at hFcvtzs
      let s1 := (s.setReg .x0 (floatToIntBv (s.fregs r))).nextPC
      have hStep1N : ArmStepsN prog s s1 1 := ArmStepsN.single (.fcvtzs .x0 r hFcvtzs)
      have hX0 : s1.regs .x0 = (Value.int (floatToIntBv f)).encode := by
        simp [s1, ArmState.setReg, ArmState.nextPC, Value.encode, hFregR, hy]
      have hPC1 : s1.pc = pcMap pc + 1 := by
        simp [s1, ArmState.nextPC]; exact hPcRel
      have hRel1 : ExtStateRel layout σ s1 :=
        ExtStateRel.preserved_by_ireg_only hStateRel hRegConv
          (by simp [s1]) (by simp [s1]) (fun rr h0 _ _ => by simp [s1, ArmState.setReg, ArmState.nextPC, h0])
      have hAM1 : s1.arrayMem = s.arrayMem := by simp [s1]
      obtain ⟨s2, k2, hSteps2N, hk2, hRel2, hPC2, hAM2⟩ :=
        vStoreVar_exec prog layout x (Value.int (floatToIntBv f)) σ s1
          (pcMap pc + 1) hRel1 hInjective hRegConv hPC1 hX0 hCodeR hNotFregX
      have hChain : ArmStepsN prog s s2 (1 + k2) := ArmStepsN_trans hStep1N hSteps2N
      refine ⟨s2, 1 + k2, hChain, ?_, hRel2, ?_, ?_⟩
      · intro pc' σ' am' _hCfg; rw [hInstrs, hk2]; simp [List.length_append]; omega
      · show s2.pc = pcMap (pc + 1)
        have := hPcNext _ _ rfl; simp at this; omega
      · simp [hAM2, hAM1, hArrayMem]
    | some (.ireg r) => exact absurd hLY (hNotIregY r)
    | none =>
      exact absurd hLY (hMapped y (by simp [heq, TAC.vars]))
    | some (.stack _) =>
      have hInstrs : instrs =
        vLoadVarFP layout y .d0 ++ [ArmInstr.fcvtzs .x0 .d0] ++ vStoreVar layout x .x0 := by
        simp only [verifiedGenInstr, hLY] at hSome
        simp_all
      rw [hInstrs] at hCodeInstr hPcNext
      have hCodeLM := hCodeInstr.append_left
      have hCodeR := hCodeInstr.append_right
      have hCodeL := hCodeLM.append_left
      have hCodeM := hCodeLM.append_right
      obtain ⟨s1, k1, hSteps1N, hk1, hD0_1, hRel1, hRegs1, hPC1, hAM1, _, _⟩ :=
        vLoadVarFP_exec prog layout y .d0 σ s (pcMap pc) hStateRel hRegConv hPcRel hCodeL
          (Or.inl rfl) hNotIregY (hMapped y (by simp [heq, TAC.vars]))
      have hFcvtzs := hCodeM.head; rw [← hPC1] at hFcvtzs
      let s2 := s1.setReg .x0 (floatToIntBv (s1.fregs .d0)) |>.nextPC
      have hStep2N : ArmStepsN prog s1 s2 1 := ArmStepsN.single (.fcvtzs .x0 .d0 hFcvtzs)
      have hX0 : s2.regs .x0 = (Value.int (floatToIntBv f)).encode := by
        simp [s2, ArmState.setReg, ArmState.nextPC, Value.encode]
        rw [hD0_1, hy]; rfl
      have hPC2 : s2.pc = pcMap pc + (vLoadVarFP layout y .d0).length + 1 := by
        simp [s2, ArmState.nextPC, hPC1]
      have hRel2 : ExtStateRel layout σ s2 :=
        ExtStateRel.preserved_by_ireg_only hRel1 hRegConv
          (by simp [s2]) (by simp [s2]) (fun r h0 _ _ => by simp [s2, ArmState.setReg, ArmState.nextPC, h0])
      have hAM2 : s2.arrayMem = s1.arrayMem := by simp [s2]
      obtain ⟨s3, k3, hSteps3N, hk3, hRel3, hPC3, hAM3⟩ :=
        vStoreVar_exec prog layout x (Value.int (floatToIntBv f)) σ s2
          (pcMap pc + (vLoadVarFP layout y .d0).length + 1)
          hRel2 hInjective hRegConv hPC2 hX0
          (by rw [show (vLoadVarFP layout y .d0 ++ [ArmInstr.fcvtzs .x0 .d0]).length =
            (vLoadVarFP layout y .d0).length + 1 from by simp] at hCodeR; exact hCodeR)
          hNotFregX
      have h12 : ArmStepsN prog s s2 (k1 + 1) := ArmStepsN_trans hSteps1N hStep2N
      have hChain : ArmStepsN prog s s3 (k1 + 1 + k3) := ArmStepsN_trans h12 hSteps3N
      refine ⟨s3, k1 + 1 + k3, hChain, ?_, hRel3, ?_, ?_⟩
      · intro pc' σ' am' _hCfg; rw [hInstrs, hk1, hk3]; simp [List.length_append]; omega
      · show s3.pc = pcMap (pc + 1)
        have := hPcNext _ _ rfl; simp at this
        omega
      · simp [hAM3, hAM2, hAM1, hArrayMem]
  | floatUnary hinstr hy =>
    rename_i x op y f
    have heq : instr = .floatUnary x op y := Option.some.inj (hInstr.symm.trans hinstr)
    rw [heq] at hSome hMapped
    have hNotIregY : ∀ r, layout y ≠ some (.ireg r) := by
      intro r h; have := hSome; simp [verifiedGenInstr, hRC, hII, h] at this
    have hNotIregX : ∀ r, layout x ≠ some (.ireg r) := by
      intro r h; have := hSome
      simp only [verifiedGenInstr, h] at this
      simp_all
    let src_reg := match layout y with | some (.freg r) => r | _ => ArmFReg.d0
    let dst_reg := match layout x with | some (.freg r) => r | _ => ArmFReg.d0
    let armOp := ArmInstr.floatUnaryInstr op dst_reg src_reg
    have hInstrs : instrs =
      vLoadVarFP layout y src_reg ++ [armOp] ++ vStoreVarFP layout x dst_reg := by
      simp only [verifiedGenInstr] at hSome
      split at hSome <;> simp_all [src_reg, dst_reg, armOp]
      all_goals (try exact hSome.symm)
    rw [hInstrs] at hCodeInstr hPcNext
    have hCodeLM := hCodeInstr.append_left
    have hCodeR := hCodeInstr.append_right
    have hCodeL := hCodeLM.append_left
    have hCodeM := hCodeLM.append_right
    obtain ⟨s1, k1, hSteps1N, hk1, hSR_1, hRel1, hRegs1, hPC1, hAM1, hFregs1, hStack1⟩ :=
      vLoadVarFP_eff_exec prog layout y σ s (pcMap pc) .d0 hStateRel hRegConv hPcRel
        hNotIregY (Or.inl rfl) (hMapped y (by simp [TAC.vars])) hCodeL
    have hk1' : k1 = (vLoadVarFP layout y src_reg).length := hk1
    have hCall := hCodeM.head; rw [← hPC1] at hCall
    by_cases hNat : op.isNative = true
    · let s2 := s1.setFReg dst_reg (op.eval (s1.fregs src_reg)) |>.nextPC
      have hStep2N : ArmStepsN prog s1 s2 1 :=
        ArmStepsN.single (.floatUnaryNative op dst_reg src_reg hCall hNat)
      have hDR_2 : s2.fregs dst_reg = (Value.float (op.eval f)).encode := by
        simp [s2, ArmState.setFReg, ArmState.nextPC, Value.encode]
        rw [hSR_1, hy]; rfl
      have hPC2 : s2.pc = pcMap pc + (vLoadVarFP layout y src_reg).length + 1 := by
        simp only [s2, ArmState.nextPC, ArmState.setFReg, src_reg] at hPC1 ⊢; omega
      have hAM2 : s2.arrayMem = s1.arrayMem := by simp [s2]
      by_cases hXFR : ∃ r, layout x = some (.freg r)
      · obtain ⟨r_dst, hDst⟩ := hXFR
        have hDR : dst_reg = r_dst := by
          change (match layout x with | some (.freg r) => r | _ => .d0) = r_dst; rw [hDst]
        have hStore : vStoreVarFP layout x dst_reg = [] := by simp [vStoreVarFP, hDst, hDR]
        have hRel3 : ExtStateRel layout (σ[x ↦ .float (op.eval f)]) s2 := by
          show ExtStateRel layout (σ[x ↦ .float (op.eval f)])
            (s1.setFReg dst_reg (op.eval (s1.fregs src_reg))).nextPC
          rw [hDR]
          have hval : op.eval (s1.fregs src_reg) = (Value.float (op.eval f)).encode := by
            simp [Value.encode]; rw [hSR_1, hy]; rfl
          rw [hval]
          exact (ExtStateRel.update_freg hRel1 hInjective hDst).nextPC
        have hChain : ArmStepsN prog s s2 (k1 + 1) := ArmStepsN_trans hSteps1N hStep2N
        refine ⟨s2, k1 + 1, hChain, ?_, hRel3, ?_, ?_⟩
        · intro pc' σ' am' _hCfg
          rw [hInstrs, hk1', hStore]; simp [List.length_append]
        · show s2.pc = pcMap (pc + 1)
          have := hPcNext _ _ rfl; simp [hStore] at this; omega
        · simp [hAM2, hAM1, hArrayMem]
      · have hDR : dst_reg = .d0 := by
          change (match layout x with | some (.freg r) => r | _ => .d0) = .d0
          split
          · next r h => exact absurd ⟨r, h⟩ hXFR
          · rfl
        have hRel2 : ExtStateRel layout σ s2 := by
          show ExtStateRel layout σ (s1.setFReg dst_reg (op.eval (s1.fregs src_reg))).nextPC
          rw [hDR]; exact (ExtStateRel.setFReg_preserved hRel1 (fun v => hRegConv.not_d0 v)).nextPC
        have hD0 : s2.fregs .d0 = (Value.float (op.eval f)).encode := by
          rw [← hDR]; exact hDR_2
        have hCodeStore : CodeAt prog
            (pcMap pc + (vLoadVarFP layout y src_reg).length + 1)
            (vStoreVarFP layout x .d0) := by
          rw [← hDR]
          rw [show (vLoadVarFP layout y src_reg ++ [armOp]).length =
            (vLoadVarFP layout y src_reg).length + 1 from by simp] at hCodeR
          exact hCodeR
        obtain ⟨s3, k3, hSteps3N, hk3, hRel3, hPC3, hAM3⟩ :=
          vStoreVarFP_exec prog layout x (Value.float (op.eval f)) σ s2
            (pcMap pc + (vLoadVarFP layout y src_reg).length + 1)
            hRel2 hInjective hRegConv hPC2 hD0 hCodeStore hNotIregX
            (fun r h => absurd ⟨r, h⟩ hXFR)
        have hk3' : k3 = (vStoreVarFP layout x dst_reg).length := by rw [hDR]; exact hk3
        have h12 : ArmStepsN prog s s2 (k1 + 1) := ArmStepsN_trans hSteps1N hStep2N
        have hChain : ArmStepsN prog s s3 (k1 + 1 + k3) := ArmStepsN_trans h12 hSteps3N
        refine ⟨s3, k1 + 1 + k3, hChain, ?_, hRel3, ?_, ?_⟩
        · intro pc' σ' am' _hCfg
          rw [hInstrs, hk1', hk3']; simp [List.length_append]; omega
        · show s3.pc = pcMap (pc + 1)
          have := hPcNext _ _ rfl; rw [show dst_reg = ArmFReg.d0 from hDR] at this; simp at this
          omega
        · simp [hAM3, hAM2, hAM1, hArrayMem]
    · have hNotNat : op.isNative = false := by cases op <;> simp_all [FloatUnaryOp.isNative]
      let newRegs : ArmReg → BitVec 64 := havocRegsFn s1
      let newFregs : ArmFReg → BitVec 64 := havocFRegsFn s1
      let s2 := (s1.havocCallerSaved newRegs newFregs) |>.setFReg dst_reg (op.eval (s1.fregs src_reg)) |>.nextPC
      have hStep2N : ArmStepsN prog s1 s2 1 :=
        ArmStepsN.single (.floatUnaryLibCall op dst_reg src_reg hCall hNotNat)
      have hDR_2 : s2.fregs dst_reg = (Value.float (op.eval f)).encode := by
        simp [s2, ArmState.setFReg, ArmState.nextPC, ArmState.havocCallerSaved, Value.encode]
        rw [hSR_1, hy]; rfl
      have hPC2 : s2.pc = pcMap pc + (vLoadVarFP layout y src_reg).length + 1 := by
        simp only [s2, ArmState.nextPC, ArmState.setFReg, ArmState.havocCallerSaved, src_reg] at hPC1 ⊢; omega
      have hAM2 : s2.arrayMem = s1.arrayMem := by simp [s2, ArmState.havocCallerSaved]
      have hRelHavoc : ExtStateRel layout σ (s1.havocCallerSaved newRegs newFregs) :=
        ExtStateRel.havocCallerSaved_preserved hRel1 (hNCSL x op y heq hNotNat)
      by_cases hXFR : ∃ r, layout x = some (.freg r)
      · obtain ⟨r_dst, hDst⟩ := hXFR
        have hDR : dst_reg = r_dst := by
          change (match layout x with | some (.freg r) => r | _ => .d0) = r_dst; rw [hDst]
        have hStore : vStoreVarFP layout x dst_reg = [] := by simp [vStoreVarFP, hDst, hDR]
        have hRel3 : ExtStateRel layout (σ[x ↦ .float (op.eval f)]) s2 := by
          show ExtStateRel layout (σ[x ↦ .float (op.eval f)])
            ((s1.havocCallerSaved newRegs newFregs) |>.setFReg dst_reg (op.eval (s1.fregs src_reg))).nextPC
          rw [hDR]
          have hval : op.eval (s1.fregs src_reg) = (Value.float (op.eval f)).encode := by
            simp [Value.encode]; rw [hSR_1, hy]; rfl
          rw [hval]
          exact (ExtStateRel.update_freg hRelHavoc hInjective hDst).nextPC
        have hChain : ArmStepsN prog s s2 (k1 + 1) := ArmStepsN_trans hSteps1N hStep2N
        refine ⟨s2, k1 + 1, hChain, ?_, hRel3, ?_, ?_⟩
        · intro pc' σ' am' _hCfg
          rw [hInstrs, hk1', hStore]; simp [List.length_append]
        · show s2.pc = pcMap (pc + 1)
          have := hPcNext _ _ rfl; simp [hStore] at this; omega
        · simp [hAM2, hAM1, hArrayMem]
      · have hDR : dst_reg = .d0 := by
          change (match layout x with | some (.freg r) => r | _ => .d0) = .d0
          split
          · next r h => exact absurd ⟨r, h⟩ hXFR
          · rfl
        have hRel2 : ExtStateRel layout σ s2 := by
          show ExtStateRel layout σ
            ((s1.havocCallerSaved newRegs newFregs) |>.setFReg dst_reg (op.eval (s1.fregs src_reg))).nextPC
          rw [hDR]; exact (ExtStateRel.setFReg_preserved hRelHavoc (fun v => hRegConv.not_d0 v)).nextPC
        have hD0 : s2.fregs .d0 = (Value.float (op.eval f)).encode := by
          rw [← hDR]; exact hDR_2
        have hCodeStore : CodeAt prog
            (pcMap pc + (vLoadVarFP layout y src_reg).length + 1)
            (vStoreVarFP layout x .d0) := by
          rw [← hDR]
          rw [show (vLoadVarFP layout y src_reg ++ [armOp]).length =
            (vLoadVarFP layout y src_reg).length + 1 from by simp] at hCodeR
          exact hCodeR
        obtain ⟨s3, k3, hSteps3N, hk3, hRel3, hPC3, hAM3⟩ :=
          vStoreVarFP_exec prog layout x (Value.float (op.eval f)) σ s2
            (pcMap pc + (vLoadVarFP layout y src_reg).length + 1)
            hRel2 hInjective hRegConv hPC2 hD0 hCodeStore hNotIregX
            (fun r h => absurd ⟨r, h⟩ hXFR)
        have hk3' : k3 = (vStoreVarFP layout x dst_reg).length := by rw [hDR]; exact hk3
        have h12 : ArmStepsN prog s s2 (k1 + 1) := ArmStepsN_trans hSteps1N hStep2N
        have hChain : ArmStepsN prog s s3 (k1 + 1 + k3) := ArmStepsN_trans h12 hSteps3N
        refine ⟨s3, k1 + 1 + k3, hChain, ?_, hRel3, ?_, ?_⟩
        · intro pc' σ' am' _hCfg
          rw [hInstrs, hk1', hk3']; simp [List.length_append]; omega
        · show s3.pc = pcMap (pc + 1)
          have := hPcNext _ _ rfl; rw [show dst_reg = ArmFReg.d0 from hDR] at this; simp at this
          omega
        · simp [hAM3, hAM2, hAM1, hArrayMem]
  | fternop hinstr ha hb hc =>
    rename_i dst op a b c va vb vc
    have heq : instr = .fternop dst op a b c := Option.some.inj (hInstr.symm.trans hinstr)
    rw [heq] at hSome hMapped
    have hNotIregA : ∀ r, layout a ≠ some (.ireg r) := by
      intro r h; have := hSome; simp [verifiedGenInstr, hRC, hII, h] at this
    have hNotIregB : ∀ r, layout b ≠ some (.ireg r) := by
      intro r h; have := hSome; simp [verifiedGenInstr, hRC, hII, h] at this
    have hNotIregC : ∀ r, layout c ≠ some (.ireg r) := by
      intro r h; have := hSome; simp [verifiedGenInstr, hRC, hII, h] at this
    have hNotIregD : ∀ r, layout dst ≠ some (.ireg r) := by
      intro r h; have := hSome; simp [verifiedGenInstr, hRC, hII, h] at this
    let a_reg := match layout a with | some (.freg r) => r | _ => ArmFReg.d0
    let b_reg := match layout b with | some (.freg r) => r | _ => ArmFReg.d1
    let c_reg := match layout c with | some (.freg r) => r | _ => ArmFReg.d2
    let dst_reg := match layout dst with | some (.freg r) => r | _ => ArmFReg.d0
    let fpInstr := match op with
      | .fmadd => ArmInstr.fmaddR dst_reg b_reg c_reg a_reg
      | .fmsub => ArmInstr.fmsubR dst_reg b_reg c_reg a_reg
    have hInstrs : instrs = vLoadVarFP layout a a_reg ++
        (vLoadVarFP layout b b_reg ++
          (vLoadVarFP layout c c_reg ++ (fpInstr :: vStoreVarFP layout dst dst_reg))) := by
      have := hSome; simp [verifiedGenInstr, hRC, hII] at this; exact this.symm
    rw [hInstrs] at hCodeInstr hPcNext
    have hCodeA := hCodeInstr.append_left
    have hCodeBCD := hCodeInstr.append_right
    have hCodeB := hCodeBCD.append_left
    have hCodeCD := hCodeBCD.append_right
    have hCodeC := hCodeCD.append_left
    have hCodeOpStore := hCodeCD.append_right
    obtain ⟨s1, k1, hSteps1N, hk1, hA_1, hRel1, hRegs1, hPC1, hAM1, hFregs1, hStack1⟩ :=
      vLoadVarFP_eff_exec prog layout a σ s (pcMap pc) .d0 hStateRel hRegConv hPcRel
        hNotIregA (Or.inl rfl) (hMapped a (by simp [TAC.vars])) hCodeA
    have hk1' : k1 = (vLoadVarFP layout a a_reg).length := hk1
    obtain ⟨s2, k2, hSteps2N, hk2, hB_2, hRel2, hRegs2, hPC2, hAM2, hFregs2, hStack2⟩ :=
      vLoadVarFP_eff_exec prog layout b σ s1 _ .d1 hRel1 hRegConv hPC1
        hNotIregB (Or.inr (Or.inl rfl)) (hMapped b (by simp [TAC.vars])) hCodeB
    have hk2' : k2 = (vLoadVarFP layout b b_reg).length := hk2
    obtain ⟨s3, k3, hSteps3N, hk3, hC_3, hRel3, hRegs3, hPC3, hAM3, hFregs3, hStack3⟩ :=
      vLoadVarFP_eff_exec prog layout c σ s2 _ .d2 hRel2 hRegConv hPC2
        hNotIregC (Or.inr (Or.inr rfl)) (hMapped c (by simp [TAC.vars])) hCodeC
    have hk3' : k3 = (vLoadVarFP layout c c_reg).length := hk3
    have hA_3 : s3.fregs a_reg = va := by
      match hLA : layout a with
      | some (.freg ra) =>
        have : a_reg = ra := by simp [a_reg, hLA]
        rw [this, hRel3.read_freg hLA, ha]; rfl
      | some (.stack _) | none =>
        have : a_reg = .d0 := by simp [a_reg, hLA]
        rw [this]
        have hne_b : ArmFReg.d0 ≠ b_reg := by
          intro h; match hLB : layout b with
          | some (.freg rb) => exact hRegConv.not_d0 b (by simp [b_reg, hLB] at h; exact h ▸ hLB)
          | some (.stack _) | none => simp [b_reg, hLB] at h
          | some (.ireg r) => exact absurd hLB (hNotIregB r)
        have hne_c : ArmFReg.d0 ≠ c_reg := by
          intro h; match hLC : layout c with
          | some (.freg rc) => exact hRegConv.not_d0 c (by simp [c_reg, hLC] at h; exact h ▸ hLC)
          | some (.stack _) | none => simp [c_reg, hLC] at h
          | some (.ireg r) => exact absurd hLC (hNotIregC r)
        rw [hFregs3 .d0 hne_c, hFregs2 .d0 hne_b, ← this, hA_1, ha]; rfl
      | some (.ireg r) => exact absurd hLA (hNotIregA r)
    have hB_3 : s3.fregs b_reg = vb := by
      match hLB : layout b with
      | some (.freg rb) =>
        have : b_reg = rb := by simp [b_reg, hLB]
        rw [this, hRel3.read_freg hLB, hb]; rfl
      | some (.stack _) | none =>
        have : b_reg = .d1 := by simp [b_reg, hLB]
        rw [this]
        have hne : ArmFReg.d1 ≠ c_reg := by
          intro h; match hLC : layout c with
          | some (.freg rc) => exact hRegConv.not_d1 c (by simp [c_reg, hLC] at h; exact h ▸ hLC)
          | some (.stack _) | none => simp [c_reg, hLC] at h
          | some (.ireg r) => exact absurd hLC (hNotIregC r)
        rw [hFregs3 .d1 hne, ← this, hB_2, hb]; rfl
      | some (.ireg r) => exact absurd hLB (hNotIregB r)
    have hC_eq : s3.fregs c_reg = vc := by rw [hC_3, hc]; rfl
    have hCodeOpStore' : CodeAt prog s3.pc (fpInstr :: vStoreVarFP layout dst dst_reg) := by
      rwa [hPC3]
    have hResultBv : FloatTernOp.eval op va vb vc =
        (Value.float (FloatTernOp.eval op va vb vc)).encode := by simp [Value.encode]
    have hArmStepReal : ArmStep prog s3
        (s3.setFReg dst_reg (FloatTernOp.eval op va vb vc) |>.nextPC) := by
      have hHead := hCodeOpStore'.head
      simp only [fpInstr] at hHead
      cases op
      · show ArmStep prog s3 (s3.setFReg dst_reg
          (FloatBinOp.eval .fadd va (FloatBinOp.eval .fmul vb vc)) |>.nextPC)
        have step := ArmStep.fmaddR dst_reg b_reg c_reg a_reg hHead
        rw [hA_3, hB_3, hC_eq] at step; exact step
      · show ArmStep prog s3 (s3.setFReg dst_reg
          (FloatBinOp.eval .fsub va (FloatBinOp.eval .fmul vb vc)) |>.nextPC)
        have step := ArmStep.fmsubR dst_reg b_reg c_reg a_reg hHead
        rw [hA_3, hB_3, hC_eq] at step; exact step
    obtain ⟨s_fin, k_fin, hSteps_finN, hk_fin, hSimRel⟩ :=
      fp_exec_and_store prog layout pcMap divLabel boundsLabel
        pc σ am dst dst_reg (FloatTernOp.eval op va vb vc) (.float (FloatTernOp.eval op va vb vc))
        hResultBv s3 s3.pc hRel3 hInjective hRegConv rfl
        (by simp [hAM3, hAM2, hAM1, hArrayMem]) rfl hNotIregD
        fpInstr hCodeOpStore' hArmStepReal
        ((vLoadVarFP layout a a_reg).length + (vLoadVarFP layout b b_reg).length +
          (vLoadVarFP layout c c_reg).length)
        (by have hPC3' : s3.pc = pcMap pc + (vLoadVarFP layout a a_reg).length +
              (vLoadVarFP layout b b_reg).length + (vLoadVarFP layout c c_reg).length := hPC3
            omega)
        (by have := hPcNext _ _ rfl; simp at this ⊢; omega)
    have h12 : ArmStepsN prog s s2 (k1 + k2) := ArmStepsN_trans hSteps1N hSteps2N
    have h123 : ArmStepsN prog s s3 (k1 + k2 + k3) := ArmStepsN_trans h12 hSteps3N
    have hChain : ArmStepsN prog s s_fin (k1 + k2 + k3 + k_fin) := ArmStepsN_trans h123 hSteps_finN
    refine ⟨s_fin, k1 + k2 + k3 + k_fin, hChain, ?_, hSimRel⟩
    intro pc' σ' am' _hCfg
    rw [hInstrs, hk1', hk2', hk3', hk_fin]; simp [List.length_append]; omega

/-- Top-level backward simulation for verifiedGenInstr.
    Directly delegates to `verifiedGenInstr_correct`. -/
theorem ext_backward_simulation (p : Prog) (armProg : ArmProg)
    (layout : VarLayout) (pcMap : Nat → Nat)
    (haltLabel divLabel boundsLabel : Nat)
    (arrayDecls : List (ArrayName × Nat × VarTy))
    (boundsSafe : Bool)
    {pc : Nat} {σ : Store} {am : ArrayMem} {cfg' : Cfg} {s : ArmState}
    (hBoundsSafeOracle : boundsSafe = true →
      (∀ dst arr idx ty, p[pc]? = some (.arrLoad dst arr idx ty) →
        ∀ idxVal, σ idx = .int idxVal → idxVal < arraySizeBv arrayDecls arr) ∧
      (∀ arr idx val ty, p[pc]? = some (.arrStore arr idx val ty) →
        ∀ idxVal, σ idx = .int idxVal → idxVal < arraySizeBv arrayDecls arr))
    (hStep : p ⊩ Cfg.run pc σ am ⟶ cfg')
    (hRel : ExtSimRel layout pcMap divLabel boundsLabel (.run pc σ am) s)
    (hPC : pc < p.size)
    (tyCtx : TyCtx)
    (hWT : WellTypedProg tyCtx p) (hTS : TypedStore tyCtx σ)
    (hWTL : WellTypedLayout tyCtx layout)
    (instr : TAC) (hInstr : p[pc]? = some instr)
    (instrs : List ArmInstr)
    (hSome : verifiedGenInstr layout pcMap instr haltLabel divLabel boundsLabel arrayDecls boundsSafe = some instrs)
    (hRC : layout.regConventionSafe = true)
    (hII : layout.isInjective = true)
    (hCode : CodeAt armProg (pcMap pc) instrs)
    (hPcNext : ∀ σ' am', cfg' = .run (pc + 1) σ' am' →
      pcMap (pc + 1) = pcMap pc + instrs.length)
    (hMapped : ∀ v, v ∈ instr.vars → layout v ≠ none)
    (hAD : arrayDecls = p.arrayDecls)
    (hNCSL : ∀ x op y, instr = .floatUnary x op y → op.isNative = false → NoCallerSavedLayout layout)
    (hNCSLBin : ∀ x y z, instr = .fbinop x .fpow y z → NoCallerSavedLayout layout)
    (hNCSLPrintInt : ∀ v, instr = .printInt v → NoCallerSavedLayout layout)
    (hNCSLPrintBool : ∀ v, instr = .printBool v → NoCallerSavedLayout layout)
    (hNCSLPrintFloat : ∀ v, instr = .printFloat v → NoCallerSavedLayout layout)
    (hNCSLPrintStr : ∀ lit, instr = .printString lit → NoCallerSavedLayout layout) :
    ∃ s' k, ArmStepsN armProg s s' k ∧
        (∀ pc' σ' am', cfg' = .run pc' σ' am' → k = instrs.length) ∧
        ExtSimRel layout pcMap divLabel boundsLabel cfg' s' :=
  verifiedGenInstr_correct armProg layout pcMap p pc σ am s haltLabel divLabel boundsLabel
    arrayDecls boundsSafe hBoundsSafeOracle instr hInstr hRel instrs hSome hRC hII hPC tyCtx hWT hTS hWTL hMapped cfg' hStep hCode hPcNext hAD hNCSL hNCSLBin hNCSLPrintInt hNCSLPrintBool hNCSLPrintFloat hNCSLPrintStr
