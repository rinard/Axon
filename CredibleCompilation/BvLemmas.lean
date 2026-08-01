-- Copyright (c) 2026 Martin Rinard
import Std.Tactic.BVDecide

/-!
# BitVec reassembly lemmas for loadImm64

These lemmas prove that decomposing a 64-bit value into 16-bit chunks
and reassembling via mask/shift/or recovers the original value.
Separated into their own file because `bv_decide` on 64-bit bitvectors
is expensive and these rarely change.
-/

set_option maxHeartbeats 102400000

/-- The full 16-bit chunk reassembly identity on BitVec 64:
    decomposing into 4 chunks and reassembling via insertBits gives back the original. -/
theorem bv_reassemble (bits : BitVec 64) :
    let w0 : BitVec 64 := bits &&& 0xFFFF#64
    let w1 : BitVec 64 := (bits >>> 16) &&& 0xFFFF#64
    let w2 : BitVec 64 := (bits >>> 32) &&& 0xFFFF#64
    let w3 : BitVec 64 := (bits >>> 48) &&& 0xFFFF#64
    ((((w0 &&& ~~~(0xFFFF#64 <<< 16)) ||| (w1 <<< 16)) &&&
      ~~~(0xFFFF#64 <<< 32)) ||| (w2 <<< 32)) &&&
      ~~~(0xFFFF#64 <<< 48) ||| (w3 <<< 48) = bits := by
  bv_decide

-- Partial reassembly variants (when some chunks are zero, the insertBits is skipped)
theorem bv_reassemble_110 (bits : BitVec 64) (hw3 : (bits >>> 48) &&& 0xFFFF#64 = 0) :
    (((bits &&& 0xFFFF#64) &&& ~~~(0xFFFF#64 <<< 16) ||| ((bits >>> 16) &&& 0xFFFF#64) <<< 16) &&&
      ~~~(0xFFFF#64 <<< 32)) ||| ((bits >>> 32) &&& 0xFFFF#64) <<< 32 = bits := by bv_decide
theorem bv_reassemble_101 (bits : BitVec 64) (hw2 : (bits >>> 32) &&& 0xFFFF#64 = 0) :
    ((bits &&& 0xFFFF#64) &&& ~~~(0xFFFF#64 <<< 16) ||| ((bits >>> 16) &&& 0xFFFF#64) <<< 16) &&&
      ~~~(0xFFFF#64 <<< 48) ||| ((bits >>> 48) &&& 0xFFFF#64) <<< 48 = bits := by bv_decide
theorem bv_reassemble_100 (bits : BitVec 64) (hw2 : (bits >>> 32) &&& 0xFFFF#64 = 0)
    (hw3 : (bits >>> 48) &&& 0xFFFF#64 = 0) :
    (bits &&& 0xFFFF#64) &&& ~~~(0xFFFF#64 <<< 16) ||| ((bits >>> 16) &&& 0xFFFF#64) <<< 16 = bits := by bv_decide
theorem bv_reassemble_011 (bits : BitVec 64) (hw1 : (bits >>> 16) &&& 0xFFFF#64 = 0) :
    ((bits &&& 0xFFFF#64) &&& ~~~(0xFFFF#64 <<< 32) ||| ((bits >>> 32) &&& 0xFFFF#64) <<< 32) &&&
      ~~~(0xFFFF#64 <<< 48) ||| ((bits >>> 48) &&& 0xFFFF#64) <<< 48 = bits := by bv_decide
theorem bv_reassemble_010 (bits : BitVec 64) (hw1 : (bits >>> 16) &&& 0xFFFF#64 = 0)
    (hw3 : (bits >>> 48) &&& 0xFFFF#64 = 0) :
    (bits &&& 0xFFFF#64) &&& ~~~(0xFFFF#64 <<< 32) ||| ((bits >>> 32) &&& 0xFFFF#64) <<< 32 = bits := by bv_decide
theorem bv_reassemble_001 (bits : BitVec 64) (hw1 : (bits >>> 16) &&& 0xFFFF#64 = 0)
    (hw2 : (bits >>> 32) &&& 0xFFFF#64 = 0) :
    (bits &&& 0xFFFF#64) &&& ~~~(0xFFFF#64 <<< 48) ||| ((bits >>> 48) &&& 0xFFFF#64) <<< 48 = bits := by bv_decide
theorem bv_reassemble_000 (bits : BitVec 64) (hw1 : (bits >>> 16) &&& 0xFFFF#64 = 0)
    (hw2 : (bits >>> 32) &&& 0xFFFF#64 = 0) (hw3 : (bits >>> 48) &&& 0xFFFF#64 = 0) :
    bits &&& 0xFFFF#64 = bits := by bv_decide

-- ============================================================
-- BitVec srem identity: a - sdiv(a,b) * b = srem(a,b)
-- Used in the ARM correctness proof for the BinOp.mod case.
-- ============================================================

private theorem nat_div_mul_add_mod (n m : Nat) : n / m * m + n % m = n := by
  have := Nat.div_add_mod n m; rw [Nat.mul_comm] at this; exact this

theorem BitVec.udiv_mul_add_umod {w : Nat} (a b : BitVec w) :
    a / b * b + a % b = a := by
  apply BitVec.eq_of_toNat_eq
  have hlt := a.isLt; have hmul_le := Nat.div_mul_le_self a.toNat b.toNat
  rw [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_udiv,
      Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hmul_le hlt),
      BitVec.toNat_umod, nat_div_mul_add_mod, Nat.mod_eq_of_lt hlt]

theorem BitVec.sub_udiv_mul_eq_umod {w : Nat} (a b : BitVec w) :
    a - a / b * b = a % b := by
  apply BitVec.eq_of_toNat_eq
  have hlt := a.isLt; have hmul_le := Nat.div_mul_le_self a.toNat b.toNat
  have hmul_lt := Nat.lt_of_le_of_lt hmul_le hlt
  rw [BitVec.toNat_sub, BitVec.toNat_mul, BitVec.toNat_udiv,
      Nat.mod_eq_of_lt hmul_lt, BitVec.toNat_umod,
      show 2 ^ w - a.toNat / b.toNat * b.toNat + a.toNat = 2 ^ w + a.toNat % b.toNat from
        by have := nat_div_mul_add_mod a.toNat b.toNat; omega,
      Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod,
      Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le _ _) hlt)]

/-- The signed remainder identity: `a - sdiv(a,b) * b = srem(a,b)`.
    Proved by case-splitting on the sign bits and reducing to the unsigned identity. -/
theorem BitVec.srem_eq_sub_sdiv_mul {w : Nat} (a b : BitVec w) :
    a - BitVec.sdiv a b * b = BitVec.srem a b := by
  unfold BitVec.srem BitVec.sdiv
  rcases ha : a.msb <;> rcases hb : b.msb <;> simp
  case false.false => exact BitVec.sub_udiv_mul_eq_umod a b
  case false.true =>
    have h := BitVec.sub_udiv_mul_eq_umod a (-b)
    rw [BitVec.mul_neg, BitVec.sub_eq_add_neg, BitVec.neg_neg] at h; exact h
  case true.false =>
    have h := BitVec.sub_udiv_mul_eq_umod (-a) b
    rw [← h, BitVec.neg_sub, BitVec.neg_neg, BitVec.add_comm]
  case true.true =>
    have h := BitVec.sub_udiv_mul_eq_umod (-a) (-b)
    rw [BitVec.mul_neg, BitVec.sub_eq_add_neg, BitVec.neg_neg] at h
    rw [← h, BitVec.neg_add, BitVec.neg_neg]
