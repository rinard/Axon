-- Copyright (c) 2026 Martin Rinard
import CredibleCompilation.ArmDefs
import CredibleCompilation.AxiomCheck

/-!
# `AsmEnc` — a verified, encodability-checked encoder for the immediate/offset instruction forms

This pulls the *encoding* of every `ArmInstr` form that carries an immediate or a stack offset out of
the unverified string printer (`CodeGen.ppInstr`) and into the verified core (Tiers 1–2 of "maximize
verified codegen").

The bug class it closes: `ppInstr` rendered immediate/offset operands (`ldr/str [sp,#off]`,
`cmp #imm`, `mov #imm`, `and/eor #imm`, `movz/movk #imm16`) with a raw `#…`, no encodability check —
so an over-ceiling stack slot (many spilled variables) or a large compare/move constant produced an
instruction the assembler rejects. Here the constraints live *above* the verification line:

* **Structured lines.** `AsmLine` is a typed representation of the assembler lines these forms emit,
  rendered 1:1 by the trivial `renderLine` (the only remaining trusted syntactic step).

* **Tier 1 — encodability is a theorem.** `AsmLine.wf` captures the real AArch64 constraints
  (`ldr/str` unsigned-offset ≤ 32760 & 8-aligned; `cmp` imm12 ≤ 4095; `mov` a 16-bit MOVZ value;
  `movz/movk` a 16-bit `imm16` with shift ∈ {0,16,32,48}; logical `and/eor` a valid bitmask immediate).
  `emitCmd` **legalizes** the offending forms — an over-ceiling/misaligned slot goes to the
  register-offset form via scratch `x16`, and a non-encodable constant is materialized with
  `ldr x16, =imm` (literal pool, always legal) then used via a register form. `emitCmd_wf` proves
  `emitCmd` never produces an un-encodable line (precondition `cmdWf`, which is *vacuously true* for
  every form except `movz/movk`, whose 16-bit `imm16`/shift are established by the codegen that builds
  them). No offset ceiling or constant-size bug can survive.

* **Tier 2 — the encoding is faithful.** `decode` recovers the model instruction from the emitted
  lines and `decode_emitCmd` proves the round-trip `decode (emitCmd i) = some i` for every handled
  form — the emitter is injective and lossless.

Register legality is *free*: `ArmReg`/`ArmFReg` are enums of exactly the real registers.

Scope: this covers every form with an immediate/offset (the entire encodability surface). The
constraint-free forms (register-register ALU, branches, the float ops, the `print`/`call` ABI
terminals) carry no immediate — they cannot be un-encodable — and remain rendered by `ppInstr`.
Still trusted: `renderLine`, the real-hardware semantics of a well-formed line, and the codegen-wide
`movz/movk` `imm16` invariant (not yet discharged as a theorem).
-/

namespace AsmEnc

/-! ## Encodability predicates (the real AArch64 constraints) -/

/-- 64-bit `ldr/str` unsigned-offset immediate ceiling: `imm12 × 8 = 4095 × 8`. -/
def offCeil : Nat := 32760
/-- A stack byte offset directly encodable as a scaled unsigned `ldr/str` immediate. -/
def offOk (off : Nat) : Bool := (off % 8 == 0) && decide (off ≤ offCeil)
/-- A `mov Xd, #imm` immediate encodable as a single MOVZ (16-bit, zero-extended). -/
def movOk (imm : BitVec 64) : Bool := decide (imm.toNat < 65536)
/-- A `cmp Xn, #imm` immediate encodable as the 12-bit unshifted immediate. -/
def cmpOk (imm : BitVec 64) : Bool := decide (imm.toNat ≤ 4095)
/-- A logical (`and`/`eor`) immediate we render directly. Conservative: `1` is the only value the
    backend emits (boolean normalize/negate) and is a valid AArch64 bitmask immediate; anything else
    is legalized, so this needs no full bitmask-immediate decoder to stay sound. -/
def logOk (imm : BitVec 64) : Bool := imm == 1
/-- `movz/movk` operand: a 16-bit `imm16` and a legal shift. -/
def imm16Ok (imm16 : UInt64) : Bool := decide (imm16.toNat < 65536)
def shiftOk (shift : Nat) : Bool := shift == 0 || shift == 16 || shift == 32 || shift == 48

/-! ## Structured assembler lines -/

/-- One assembler line the immediate/offset path emits, as a typed value (rendered 1:1 by
    `renderLine`). The `*RegOff`, `litOff`, `litWord`, and register forms are the legalization targets
    (all carry no bounded immediate, hence legal for any value). -/
inductive AsmLine where
  -- loads/stores (immediate-offset + register-offset legalization)
  | ldrImmOff  (rd : ArmReg)  (off : Nat)
  | strImmOff  (rs : ArmReg)  (off : Nat)
  | fldrImmOff (fd : ArmFReg) (off : Nat)
  | fstrImmOff (fs : ArmFReg) (off : Nat)
  | ldrRegOff  (rd : ArmReg)  (idx : ArmReg)
  | strRegOff  (rs : ArmReg)  (idx : ArmReg)
  | fldrRegOff (fd : ArmFReg) (idx : ArmReg)
  | fstrRegOff (fs : ArmFReg) (idx : ArmReg)
  | litOff     (rd : ArmReg)  (off : Nat)          -- ldr Xd, =off  (materialized offset)
  -- moves / compares / logical immediates (+ legalization)
  | movImm     (rd : ArmReg)  (imm : BitVec 64)    -- mov Xd, #imm    (MOVZ-encodable)
  | litWord    (rd : ArmReg)  (imm : BitVec 64)    -- ldr Xd, =imm    (materialized constant)
  | movzL      (rd : ArmReg)  (imm16 : UInt64) (shift : Nat)
  | movkL      (rd : ArmReg)  (imm16 : UInt64) (shift : Nat)
  | cmpImmL    (rn : ArmReg)  (imm : BitVec 64)    -- cmp Xn, #imm    (imm12)
  | cmpRegL    (rn rm : ArmReg)                    -- cmp Xn, Xm
  | andImmL    (rd rn : ArmReg) (imm : BitVec 64)  -- and Xd, Xn, #imm
  | eorImmL    (rd rn : ArmReg) (imm : BitVec 64)  -- eor Xd, Xn, #imm
  | andRegL    (rd rn rm : ArmReg)                 -- and Xd, Xn, Xm
  | eorRegL    (rd rn rm : ArmReg)                 -- eor Xd, Xn, Xm
  deriving Repr, DecidableEq

/-- **Encodability** of one line — the constraint the assembler enforces. Register-offset / literal /
    register-register forms carry no bounded immediate and are legal for any value; register operands
    are always legal (the `ArmReg`/`ArmFReg` enums contain only real registers). -/
def AsmLine.wf : AsmLine → Bool
  | .ldrImmOff  _ off  => offOk off
  | .strImmOff  _ off  => offOk off
  | .fldrImmOff _ off  => offOk off
  | .fstrImmOff _ off  => offOk off
  | .ldrRegOff  _ _    => true
  | .strRegOff  _ _    => true
  | .fldrRegOff _ _    => true
  | .fstrRegOff _ _    => true
  | .litOff     _ _    => true
  | .movImm     _ imm  => movOk imm
  | .litWord    _ _    => true
  | .movzL      _ i16 sh => imm16Ok i16 && shiftOk sh
  | .movkL      _ i16 sh => imm16Ok i16 && shiftOk sh
  | .cmpImmL    _ imm  => cmpOk imm
  | .cmpRegL    _ _    => true
  | .andImmL    _ _ imm => logOk imm
  | .eorImmL    _ _ imm => logOk imm
  | .andRegL    _ _ _  => true
  | .eorRegL    _ _ _  => true

/-- Reserved scratch base/temp for legalization: `x16` (IP0), excluded from allocation by
    `VarLayout.regConventionSafe` and never used by the emitted body. -/
def scratch : ArmReg := .x16

/-- The instruction forms this encoder handles (the "core" set for the round-trip). -/
def isCore : ArmInstr → Bool
  | .ldr ..    => true
  | .str ..    => true
  | .fldr ..   => true
  | .fstr ..   => true
  | .mov ..    => true
  | .movz ..   => true
  | .movk ..   => true
  | .cmpImm .. => true
  | .andImm .. => true
  | .eorImm .. => true
  | _          => false

/-- Precondition for `emitCmd_wf`: vacuously `true` for every handled form except `movz/movk`, whose
    16-bit `imm16` and legal shift are guaranteed by the codegen (`formalLoadImm64`) that builds them. -/
def cmdWf : ArmInstr → Bool
  | .movz _ i16 sh => imm16Ok i16 && shiftOk sh
  | .movk _ i16 sh => imm16Ok i16 && shiftOk sh
  | _              => true

/-- The legalizing emitter. A directly-encodable operand uses the compact form; an over-ceiling or
    misaligned offset, or a non-encodable constant, is lowered via scratch `x16`. Every form outside
    the immediate/offset surface yields `[]` (rendered by the existing `ppInstr` scaffolding). -/
def emitCmd : ArmInstr → List AsmLine
  | .ldr rd off  => if offOk off then [.ldrImmOff rd off]
                    else [.litOff scratch off, .ldrRegOff rd scratch]
  | .str rs off  => if offOk off then [.strImmOff rs off]
                    else [.litOff scratch off, .strRegOff rs scratch]
  | .fldr fd off => if offOk off then [.fldrImmOff fd off]
                    else [.litOff scratch off, .fldrRegOff fd scratch]
  | .fstr fs off => if offOk off then [.fstrImmOff fs off]
                    else [.litOff scratch off, .fstrRegOff fs scratch]
  | .mov rd imm  => if movOk imm then [.movImm rd imm] else [.litWord rd imm]
  | .movz rd i16 sh => [.movzL rd i16 sh]
  | .movk rd i16 sh => [.movkL rd i16 sh]
  | .cmpImm rn imm  => if cmpOk imm then [.cmpImmL rn imm]
                       else [.litWord scratch imm, .cmpRegL rn scratch]
  | .andImm rd rn imm => if logOk imm then [.andImmL rd rn imm]
                         else [.litWord scratch imm, .andRegL rd rn scratch]
  | .eorImm rd rn imm => if logOk imm then [.eorImmL rd rn imm]
                         else [.litWord scratch imm, .eorRegL rd rn scratch]
  | _ => []

/-! ## Tier 1 — the emitter only produces encodable lines -/

/-- **Legality is a theorem.** For any instruction satisfying `cmdWf` (vacuous except for `movz/movk`),
    every line `emitCmd` produces satisfies `AsmLine.wf`: no `ldr/str` offset exceeds `32760`/is
    misaligned, no `cmp`/`mov`/`and`/`eor` immediate exceeds its field — the non-encodable cases take
    the legalized path. The offset-ceiling and large-constant bug classes are closed by construction. -/
theorem emitCmd_wf {i : ArmInstr} (h : cmdWf i = true) : (emitCmd i).all AsmLine.wf = true := by
  cases i <;>
    first
    | (simp only [emitCmd]; split <;>
        simp_all [AsmLine.wf, offOk, movOk, cmpOk, logOk, scratch, List.all])
    | simp_all [emitCmd, AsmLine.wf, cmdWf, imm16Ok, shiftOk, List.all]
    | simp [emitCmd, List.all]

/-! ## Tier 2 — the encoding is faithful (round-trips) -/

/-- Recover the model instruction from emitted lines. Inverse of `emitCmd` on the core set. -/
def decode : List AsmLine → Option ArmInstr
  | [.ldrImmOff rd off]                        => some (.ldr rd off)
  | [.strImmOff rs off]                        => some (.str rs off)
  | [.fldrImmOff fd off]                       => some (.fldr fd off)
  | [.fstrImmOff fs off]                       => some (.fstr fs off)
  | [.litOff .x16 off, .ldrRegOff rd .x16]     => some (.ldr rd off)
  | [.litOff .x16 off, .strRegOff rs .x16]     => some (.str rs off)
  | [.litOff .x16 off, .fldrRegOff fd .x16]    => some (.fldr fd off)
  | [.litOff .x16 off, .fstrRegOff fs .x16]    => some (.fstr fs off)
  | [.movImm rd imm]                           => some (.mov rd imm)
  | [.litWord rd imm]                          => some (.mov rd imm)
  | [.movzL rd i16 sh]                         => some (.movz rd i16 sh)
  | [.movkL rd i16 sh]                         => some (.movk rd i16 sh)
  | [.cmpImmL rn imm]                          => some (.cmpImm rn imm)
  | [.litWord .x16 imm, .cmpRegL rn .x16]      => some (.cmpImm rn imm)
  | [.andImmL rd rn imm]                       => some (.andImm rd rn imm)
  | [.litWord .x16 imm, .andRegL rd rn .x16]   => some (.andImm rd rn imm)
  | [.eorImmL rd rn imm]                       => some (.eorImm rd rn imm)
  | [.litWord .x16 imm, .eorRegL rd rn .x16]   => some (.eorImm rd rn imm)
  | _                                          => none

/-- **Faithful encoding.** Every handled instruction round-trips through the emitter: the emitted lines
    decode back to exactly the instruction they came from. So `emitCmd` is injective and lossless on
    the core set — the assembly unambiguously represents its model `ArmInstr`. -/
theorem decode_emitCmd {i : ArmInstr} (h : isCore i = true) :
    decode (emitCmd i) = some i := by
  cases i <;>
    first
    | (simp only [emitCmd, scratch]; split <;> rfl)   -- forms with an `if` (loads/stores, mov, cmp, and/eor)
    | (simp only [emitCmd, scratch]; rfl)             -- forms without an `if` (movz, movk)
    | simp [isCore] at h                               -- non-core forms: `h : false = true`

/-! ## Trusted 1:1 renderer (the only remaining syntactic step) -/

private def regName : ArmReg → String
  | .x0 => "x0" | .x1 => "x1" | .x2 => "x2" | .x3 => "x3"
  | .x4 => "x4" | .x5 => "x5" | .x6 => "x6" | .x7 => "x7"
  | .x8 => "x8" | .x9 => "x9" | .x10 => "x10" | .x11 => "x11"
  | .x12 => "x12" | .x13 => "x13" | .x14 => "x14" | .x15 => "x15"
  | .x16 => "x16" | .x17 => "x17" | .x18 => "x18"
  | .x19 => "x19" | .x20 => "x20" | .x21 => "x21" | .x22 => "x22"
  | .x23 => "x23" | .x24 => "x24" | .x25 => "x25" | .x26 => "x26"
  | .x27 => "x27" | .x28 => "x28"

private def fregName : ArmFReg → String
  | .d0 => "d0" | .d1 => "d1" | .d2 => "d2" | .d3 => "d3"
  | .d4 => "d4" | .d5 => "d5" | .d6 => "d6" | .d7 => "d7"
  | .d8 => "d8" | .d9 => "d9" | .d10 => "d10" | .d11 => "d11"
  | .d12 => "d12" | .d13 => "d13" | .d14 => "d14" | .d15 => "d15"

/-- Render one structured line to an assembler line (1:1, trusted). -/
def renderLine : AsmLine → String
  | .ldrImmOff  rd off  => s!"  ldr {regName rd}, [sp, #{off}]"
  | .strImmOff  rs off  => s!"  str {regName rs}, [sp, #{off}]"
  | .fldrImmOff fd off  => s!"  ldr {fregName fd}, [sp, #{off}]"
  | .fstrImmOff fs off  => s!"  str {fregName fs}, [sp, #{off}]"
  | .ldrRegOff  rd idx  => s!"  ldr {regName rd}, [sp, {regName idx}]"
  | .strRegOff  rs idx  => s!"  str {regName rs}, [sp, {regName idx}]"
  | .fldrRegOff fd idx  => s!"  ldr {fregName fd}, [sp, {regName idx}]"
  | .fstrRegOff fs idx  => s!"  str {fregName fs}, [sp, {regName idx}]"
  | .litOff     rd off  => s!"  ldr {regName rd}, ={off}"
  | .movImm     rd imm  => s!"  mov {regName rd}, #{imm.toNat}"
  | .litWord    rd imm  => s!"  ldr {regName rd}, ={imm.toNat}"
  | .movzL      rd i16 sh => if sh == 0 then s!"  movz {regName rd}, #{i16}"
                            else s!"  movz {regName rd}, #{i16}, lsl #{sh}"
  | .movkL      rd i16 sh => s!"  movk {regName rd}, #{i16}, lsl #{sh}"
  | .cmpImmL    rn imm  => s!"  cmp {regName rn}, #{imm.toNat}"
  | .cmpRegL    rn rm   => s!"  cmp {regName rn}, {regName rm}"
  | .andImmL    rd rn imm => s!"  and {regName rd}, {regName rn}, #{imm.toNat}"
  | .eorImmL    rd rn imm => s!"  eor {regName rd}, {regName rn}, #{imm.toNat}"
  | .andRegL    rd rn rm => s!"  and {regName rd}, {regName rn}, {regName rm}"
  | .eorRegL    rd rn rm => s!"  eor {regName rd}, {regName rn}, {regName rm}"

/-- The rendering used by `CodeGen.ppInstr` for the immediate/offset forms: legalize, then render 1:1.
    Byte-identical to the old output whenever the operand was already encodable; otherwise the
    (encodable) legalized sequence. -/
def render (i : ArmInstr) : List String := (emitCmd i).map renderLine

#assert_clean_axioms emitCmd_wf
#assert_clean_axioms decode_emitCmd

end AsmEnc
