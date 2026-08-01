-- Copyright (c) 2026 Martin Rinard
import CredibleCompilation.Core

/-!
# ARM64 Subset Definitions

ARM64 register, instruction, condition, flags, and state definitions
for the code generator subset. Only models the ~18 instructions
actually emitted by `CodeGen.lean`.
-/

-- ============================================================
-- § 1. Registers
-- ============================================================

/-- ARM64 integer registers used by the code generator.
    x0-x2: scratch, x8: array address scratch, x3-x7/x9-x15: caller-saved allocatable,
    x16-x17: linker scratch (IP0/IP1), x18: platform-reserved,
    x19-x28: callee-saved allocatable (must be saved/restored in prologue/epilogue). -/
inductive ArmReg where
  | x0  | x1  | x2  | x3  | x4  | x5  | x6  | x7
  | x8  | x9  | x10 | x11 | x12 | x13 | x14 | x15
  | x16 | x17 | x18
  | x19 | x20 | x21 | x22 | x23 | x24 | x25 | x26 | x27 | x28
  deriving Repr, DecidableEq

-- sp is implicit (stack is addressed by offset)
-- x29/x30 are only used in prologue/epilogue (not modeled)

/-- Convert a register number to an ArmReg. -/
def ArmReg.fromRegNum : Nat → ArmReg
  | 0 => .x0 | 1 => .x1 | 2 => .x2 | 3 => .x3
  | 4 => .x4 | 5 => .x5 | 6 => .x6 | 7 => .x7
  | 8 => .x8 | 9 => .x9 | 10 => .x10 | 11 => .x11
  | 12 => .x12 | 13 => .x13 | 14 => .x14 | 15 => .x15
  | 16 => .x16 | 17 => .x17 | 18 => .x18
  | 19 => .x19 | 20 => .x20 | 21 => .x21 | 22 => .x22
  | 23 => .x23 | 24 => .x24 | 25 => .x25 | 26 => .x26
  | 27 => .x27 | 28 => .x28
  | _ => .x0  -- fallback

/-- Convert an ArmReg to its register number. -/
def ArmReg.toNat : ArmReg → Nat
  | .x0 => 0 | .x1 => 1 | .x2 => 2 | .x3 => 3
  | .x4 => 4 | .x5 => 5 | .x6 => 6 | .x7 => 7
  | .x8 => 8 | .x9 => 9 | .x10 => 10 | .x11 => 11
  | .x12 => 12 | .x13 => 13 | .x14 => 14 | .x15 => 15
  | .x16 => 16 | .x17 => 17 | .x18 => 18
  | .x19 => 19 | .x20 => 20 | .x21 => 21 | .x22 => 22
  | .x23 => 23 | .x24 => 24 | .x25 => 25 | .x26 => 26
  | .x27 => 27 | .x28 => 28

/-- ARM64 floating-point registers used by the code generator.
    d0-d1: scratch, d2-d15: allocatable. -/
inductive ArmFReg where
  | d0  | d1  | d2  | d3  | d4  | d5  | d6  | d7
  | d8  | d9  | d10 | d11 | d12 | d13 | d14 | d15
  deriving Repr, DecidableEq

/-- Convert a register number to an ArmFReg. -/
def ArmFReg.fromRegNum : Nat → ArmFReg
  | 0 => .d0 | 1 => .d1 | 2 => .d2 | 3 => .d3
  | 4 => .d4 | 5 => .d5 | 6 => .d6 | 7 => .d7
  | 8 => .d8 | 9 => .d9 | 10 => .d10 | 11 => .d11
  | 12 => .d12 | 13 => .d13 | 14 => .d14 | 15 => .d15
  | _ => .d0  -- fallback

/-- Convert an ArmFReg to its register number. -/
def ArmFReg.toNat : ArmFReg → Nat
  | .d0 => 0 | .d1 => 1 | .d2 => 2 | .d3 => 3
  | .d4 => 4 | .d5 => 5 | .d6 => 6 | .d7 => 7
  | .d8 => 8 | .d9 => 9 | .d10 => 10 | .d11 => 11
  | .d12 => 12 | .d13 => 13 | .d14 => 14 | .d15 => 15

-- ============================================================
-- § 2. Condition codes and flags
-- ============================================================

/-- ARM64 condition codes used by the code generator. -/
inductive Cond where
  | eq | ne | lt | le | gt | ge | hs | lo
  deriving Repr, DecidableEq

/-- Condition flags set by `cmp`. We store both operands so that
    signed comparison (`slt`/`sle`) is exact for all 64-bit values. -/
structure Flags where
  lhs : BitVec 64
  rhs : BitVec 64
  deriving Repr

/-- Evaluate a condition against the flags. -/
instance : DecidableEq Flags := fun a b =>
  if h1 : a.lhs = b.lhs then
    if h2 : a.rhs = b.rhs then isTrue (by cases a; cases b; simp_all)
    else isFalse (by intro heq; cases heq; exact h2 rfl)
  else isFalse (by intro heq; cases heq; exact h1 rfl)

def Flags.condHolds (f : Flags) : Cond → Bool
  | .eq => f.lhs == f.rhs
  | .ne => f.lhs != f.rhs
  | .lt => BitVec.slt f.lhs f.rhs
  | .le => BitVec.sle f.lhs f.rhs
  | .gt => BitVec.slt f.rhs f.lhs
  | .ge => BitVec.sle f.rhs f.lhs
  | .hs => f.rhs ≤ f.lhs
  | .lo => f.lhs < f.rhs

instance : Inhabited Flags := ⟨Flags.mk 0 0⟩

/-- Flags produced by an AArch64 `fcmp Dn, Dm` (opaque; concrete IEEE-754 behaviour attached
    via `@[implemented_by]`, exactly like the float binops in `Core`). Real `fcmp` sets NZCV from
    the IEEE 4-way result (less / equal / greater / unordered). Rather than model NZCV directly, we
    store a canonical `(lhs, rhs)` pair whose `condHolds` reproduces the AArch64 condition-code
    outcomes for every `Cond`:
    * a < b (ordered)  → (0, 1)                 : {ne, lt, le, lo}
    * a > b (ordered)  → (1, 0)                 : {ne, gt, ge, hs}
    * a = b            → (0, 0)                 : {eq, le, ge, hs}
    * unordered (NaN)  → (INT64_MIN, 0)         : {ne, lt, le, hs}  (N≠V and C=1)
    Storing raw bit patterns (the old model) was wrong: signed comparison of IEEE bits reverses
    order for negative floats and mishandles NaN/±0. -/
def fcmpFlagsImpl (a b : BitVec 64) : Flags :=
  let x := bitsToF64 a
  let y := bitsToF64 b
  if x < y then Flags.mk 0 1                                   -- a < b (ordered)
  else if y < x then Flags.mk 1 0                              -- a > b (ordered)
  else if x ≤ y then Flags.mk 0 0                              -- a = b (incl. +0/−0)
  else Flags.mk (BitVec.ofNat 64 0x8000000000000000) 0        -- unordered (NaN)

@[implemented_by fcmpFlagsImpl]
opaque fcmpFlags : BitVec 64 → BitVec 64 → Flags

/-- Negate a condition code: the result holds iff the original does not. -/
def Cond.negate : Cond → Cond
  | .eq => .ne | .ne => .eq
  | .lt => .ge | .ge => .lt
  | .le => .gt | .gt => .le
  | .hs => .lo | .lo => .hs

theorem Cond.negate_correct (f : Flags) (c : Cond) :
    f.condHolds c.negate = !f.condHolds c := by
  cases c <;> simp [Cond.negate, Flags.condHolds, BitVec.sle_eq_not_slt, bne, BEq.beq]
  · cases h : decide (f.lhs < f.rhs) <;> cases h2 : decide (f.rhs ≤ f.lhs) <;> simp_all <;> bv_omega
  · cases h : decide (f.rhs ≤ f.lhs) <;> cases h2 : decide (f.lhs < f.rhs) <;> simp_all <;> bv_omega

-- ============================================================
-- § 3. Machine state
-- ============================================================

/-- ARM64 machine state (restricted to the codegen subset). -/
structure ArmState where
  /-- Register file. -/
  regs  : ArmReg → BitVec 64
  /-- Floating-point register file. -/
  fregs : ArmFReg → BitVec 64 := fun _ => 0
  /-- Stack memory: maps byte offset from sp to 64-bit value. -/
  stack : Nat → BitVec 64
  /-- Program counter (index into instruction array). -/
  pc    : Nat
  /-- Condition flags from the last `cmp`. -/
  flags : Flags
  /-- Array memory (global, separate from scalar stack). -/
  arrayMem : ArrayMem := fun _ _ => 0

/-- Update a register. -/
def ArmState.setReg (s : ArmState) (r : ArmReg) (v : BitVec 64) : ArmState :=
  { s with regs := fun r' => if r' == r then v else s.regs r' }

/-- Update a stack slot. -/
def ArmState.setStack (s : ArmState) (off : Nat) (v : BitVec 64) : ArmState :=
  { s with stack := fun o => if o == off then v else s.stack o }

/-- Update an array memory slot. -/
def ArmState.setArrayMem (s : ArmState) (arr : ArrayName) (idx : BitVec 64) (v : BitVec 64) : ArmState :=
  { s with arrayMem := fun a i => if a == arr && i == idx then v else s.arrayMem a i }

/-- Update a floating-point register. -/
def ArmState.setFReg (s : ArmState) (r : ArmFReg) (v : BitVec 64) : ArmState :=
  { s with fregs := fun r' => if r' == r then v else s.fregs r' }

/-- Advance PC by 1. -/
def ArmState.nextPC (s : ArmState) : ArmState :=
  { s with pc := s.pc + 1 }

/-- True for caller-saved integer registers: x0-x15, x18 (platform).
    Callee-saved: x19-x28.  Linker scratch x16-x17 are also caller-saved. -/
def ArmReg.isCallerSaved : ArmReg → Bool
  | .x0 | .x1 | .x2 | .x3 | .x4 | .x5 | .x6 | .x7
  | .x8 | .x9 | .x10 | .x11 | .x12 | .x13 | .x14 | .x15
  | .x16 | .x17 | .x18 => true
  | .x19 | .x20 | .x21 | .x22 | .x23 | .x24 | .x25 | .x26 | .x27 | .x28 => false

/-- True for caller-saved FP registers: d0-d7.
    Callee-saved: d8-d15. -/
def ArmFReg.isCallerSaved : ArmFReg → Bool
  | .d0 | .d1 | .d2 | .d3 | .d4 | .d5 | .d6 | .d7 => true
  | .d8 | .d9 | .d10 | .d11 | .d12 | .d13 | .d14 | .d15 => false

/-- Havoc all caller-saved registers to arbitrary values.
    Models the effect of a library call on registers not preserved by the callee.
    `newRegs`/`newFregs` represent the arbitrary values left by the callee. -/
def ArmState.havocCallerSaved (s : ArmState)
    (newRegs : ArmReg → BitVec 64) (newFregs : ArmFReg → BitVec 64) : ArmState :=
  { s with
    regs := fun r => if r.isCallerSaved then newRegs r else s.regs r
    fregs := fun r => if r.isCallerSaved then newFregs r else s.fregs r }

@[simp] theorem ArmState.havocCallerSaved_stack (s : ArmState)
    (newRegs : ArmReg → BitVec 64) (newFregs : ArmFReg → BitVec 64) :
    (s.havocCallerSaved newRegs newFregs).stack = s.stack := rfl

@[simp] theorem ArmState.havocCallerSaved_pc (s : ArmState)
    (newRegs : ArmReg → BitVec 64) (newFregs : ArmFReg → BitVec 64) :
    (s.havocCallerSaved newRegs newFregs).pc = s.pc := rfl

/-!
### Deterministic havoc oracles

Library calls (printf, math builtins) clobber caller-saved registers
with values the ARM semantics does not model precisely.  The pre-pivot
`ArmStep` took the post-call register contents as existential
arguments, which made `ArmStep` nondeterministic and obstructed
state-uniqueness proofs.

The pivot: treat post-call register contents as a fixed-but-unknown
function of the pre-call state.  `havocRegsFn` / `havocFRegsFn` are
`opaque` — no reduction rule, so downstream proofs cannot peek at
their values — but they are total functions, so for each caller `s`
there is exactly one possible successor state.  This restores
determinism of `ArmStep` while preserving "the compiler must not
depend on post-call register values" as a proof obligation.
-/

opaque havocRegsFn : ArmState → ArmReg → BitVec 64

opaque havocFRegsFn : ArmState → ArmFReg → BitVec 64

-- ============================================================
-- § 4. ARM64 instructions
-- ============================================================

/-- ARM64 instructions used by the code generator. -/
inductive ArmInstr where
  /-- `mov Xd, #imm` — load immediate (small, fits in 16 bits). -/
  | mov      : ArmReg → BitVec 64 → ArmInstr
  /-- `mov Xd, Xn` — register-to-register move. -/
  | movR     : ArmReg → ArmReg → ArmInstr
  /-- `movz Xd, #imm16, lsl #shift` — move wide with zero. -/
  | movz     : ArmReg → UInt64 → Nat → ArmInstr
  /-- `movk Xd, #imm16, lsl #shift` — move wide with keep. -/
  | movk     : ArmReg → UInt64 → Nat → ArmInstr
  /-- `ldr Xd, [sp, #off]` — load from stack. -/
  | ldr      : ArmReg → Nat → ArmInstr
  /-- `str Xs, [sp, #off]` — store to stack. -/
  | str      : ArmReg → Nat → ArmInstr
  /-- `add Xd, Xn, Xm` — 64-bit addition. -/
  | addR     : ArmReg → ArmReg → ArmReg → ArmInstr
  /-- `sub Xd, Xn, Xm` — 64-bit subtraction. -/
  | subR     : ArmReg → ArmReg → ArmReg → ArmInstr
  /-- `mul Xd, Xn, Xm` — 64-bit multiplication. -/
  | mulR     : ArmReg → ArmReg → ArmReg → ArmInstr
  /-- `sdiv Xd, Xn, Xm` — signed 64-bit division. -/
  | sdivR    : ArmReg → ArmReg → ArmReg → ArmInstr
  /-- `cmp Xn, Xm` — compare two registers (sets flags). -/
  | cmp      : ArmReg → ArmReg → ArmInstr
  /-- `cmp Xn, #imm` — compare register with immediate (sets flags). -/
  | cmpImm   : ArmReg → BitVec 64 → ArmInstr
  /-- `cset Wd, cond` — set register to 0 or 1 based on flags. -/
  | cset     : ArmReg → Cond → ArmInstr
  /-- `cbz Xn, label` — branch if zero. -/
  | cbz      : ArmReg → Nat → ArmInstr
  /-- `cbnz Wn, label` — branch if nonzero. -/
  | cbnz     : ArmReg → Nat → ArmInstr
  /-- `and Wd, Wn, #imm` — bitwise AND with immediate. -/
  | andImm   : ArmReg → ArmReg → BitVec 64 → ArmInstr
  /-- `and Wd, Wn, Wm` — bitwise AND registers. -/
  | andR     : ArmReg → ArmReg → ArmReg → ArmInstr
  /-- `eor Wd, Wn, #imm` — exclusive OR with immediate. -/
  | eorImm   : ArmReg → ArmReg → BitVec 64 → ArmInstr
  /-- `orr Wd, Wn, Wm` — bitwise OR registers. -/
  | orrR     : ArmReg → ArmReg → ArmReg → ArmInstr
  /-- `eor Xd, Xn, Xm` — bitwise XOR registers. -/
  | eorR     : ArmReg → ArmReg → ArmReg → ArmInstr
  /-- `lsl Xd, Xn, Xm` — logical shift left (register). -/
  | lslR     : ArmReg → ArmReg → ArmReg → ArmInstr
  /-- `asr Xd, Xn, Xm` — arithmetic shift right (register). -/
  | asrR     : ArmReg → ArmReg → ArmReg → ArmInstr
  /-- `b label` — unconditional branch. -/
  | b        : Nat → ArmInstr
  /-- Print library call (`bl _printf`): havocs all caller-saved registers.
      Carries pre-computed assembly lines for the printf body (sub sp, arg
      loads, adrp/add for format string, bl _printf, add sp). -/
  | printCall : List String → ArmInstr
  /-- Typed integer print library call (`bl _printInt`): expects argument
      already in `x0`, havocs all caller-saved registers, no return value. -/
  | callPrintI : ArmInstr
  /-- Typed bool print library call (`bl _printBool`): expects argument
      already in `x0`, havocs all caller-saved registers, no return value. -/
  | callPrintB : ArmInstr
  /-- Typed float print library call (`bl _printFloat`): expects argument
      already in `d0`, havocs all caller-saved registers, no return value. -/
  | callPrintF : ArmInstr
  /-- Typed string print library call (`bl _printString`): the string literal
      is embedded in the rodata section; the call sets `x0` to its address
      and havocs all caller-saved registers. No return value. -/
  | callPrintS : String → ArmInstr
  /-- `b.cc label` — conditional branch based on flags. -/
  | bCond    : Cond → Nat → ArmInstr
  /-- Load from global array: `dst ← arrayMem[arr][idxReg]`. -/
  | arrLd    : ArmReg → ArrayName → ArmReg → ArmInstr
  /-- Store to global array: `arrayMem[arr][idxReg] ← valReg`. -/
  | arrSt    : ArrayName → ArmReg → ArmReg → ArmInstr
  -- Floating-point instructions
  /-- `fmov Dd, Xn` — move integer register to FP register. -/
  | fmovToFP : ArmFReg → ArmReg → ArmInstr
  /-- `fmov Dd, Dn` — move FP register to FP register. -/
  | fmovRR   : ArmFReg → ArmFReg → ArmInstr
  /-- `ldr Dd, [sp, #off]` — load FP from stack. -/
  | fldr     : ArmFReg → Nat → ArmInstr
  /-- `str Dd, [sp, #off]` — store FP to stack. -/
  | fstr     : ArmFReg → Nat → ArmInstr
  /-- `fadd Dd, Dn, Dm` — FP addition. -/
  | faddR    : ArmFReg → ArmFReg → ArmFReg → ArmInstr
  /-- `fsub Dd, Dn, Dm` — FP subtraction. -/
  | fsubR    : ArmFReg → ArmFReg → ArmFReg → ArmInstr
  /-- `fmul Dd, Dn, Dm` — FP multiplication. -/
  | fmulR    : ArmFReg → ArmFReg → ArmFReg → ArmInstr
  /-- `fdiv Dd, Dn, Dm` — FP division. -/
  | fdivR    : ArmFReg → ArmFReg → ArmFReg → ArmInstr
  /-- `fmadd Dd, Dn, Dm, Da` — FP fused multiply-add: Dd ← Da + Dn × Dm.
      Modeled as round(Da + round(Dn × Dm)) (two roundings), which is a safe
      under-approximation of the real single-rounding hardware semantics. -/
  | fmaddR   : ArmFReg → ArmFReg → ArmFReg → ArmFReg → ArmInstr
  /-- `fmsub Dd, Dn, Dm, Da` — FP fused multiply-subtract: Dd ← Da - Dn × Dm.
      Modeled as round(Da - round(Dn × Dm)) (two roundings). -/
  | fmsubR   : ArmFReg → ArmFReg → ArmFReg → ArmFReg → ArmInstr
  /-- `fminnm Dd, Dn, Dm` — FP minimum (IEEE 754-2008). -/
  | fminR    : ArmFReg → ArmFReg → ArmFReg → ArmInstr
  /-- `fmaxnm Dd, Dn, Dm` — FP maximum (IEEE 754-2008). -/
  | fmaxR    : ArmFReg → ArmFReg → ArmFReg → ArmInstr
  /-- Binary FP library call: `d0 ← op(d0, d1)`. For pow, etc. -/
  | callBinF : FloatBinOp → ArmFReg → ArmFReg → ArmFReg → ArmInstr
  /-- `fcmp Dn, Dm` — FP compare (sets flags). -/
  | fcmpR    : ArmFReg → ArmFReg → ArmInstr
  /-- `scvtf Dd, Xn` — signed int → FP conversion. -/
  | scvtf    : ArmFReg → ArmReg → ArmInstr
  /-- `fcvtzs Xd, Dn` — FP → signed int conversion. -/
  | fcvtzs   : ArmReg → ArmFReg → ArmInstr
  /-- Load from FP array: `dst ← arrayMem[arr][idxReg]`. -/
  | farrLd   : ArmFReg → ArrayName → ArmReg → ArmInstr
  /-- Store to FP array: `arrayMem[arr][idxReg] ← valFReg`. -/
  | farrSt   : ArrayName → ArmReg → ArmFReg → ArmInstr
  /-- Float unary intrinsic: library call or native instruction.
      Abstract: `fd ← op.eval(fn)`, preserves everything else. -/
  | floatUnaryInstr : FloatUnaryOp → ArmFReg → ArmFReg → ArmInstr
  deriving Repr, DecidableEq

/-- An ARM64 program is an array of instructions. -/
abbrev ArmProg := Array ArmInstr
