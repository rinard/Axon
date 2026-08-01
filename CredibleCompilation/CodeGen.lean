-- Copyright (c) 2026 Martin Rinard
import Mathlib.Data.List.Nodup
import CredibleCompilation.AsmEnc
import CredibleCompilation.WhileLang
import CredibleCompilation.Parser
import CredibleCompilation.ConstPropOpt
import CredibleCompilation.CopyPropOpt
import CredibleCompilation.RematConstOpt
import CredibleCompilation.CSEOpt
import CredibleCompilation.LICMOpt
import CredibleCompilation.ConstHoistOpt
import CredibleCompilation.DAEOpt
import CredibleCompilation.FMAFusionOpt
import CredibleCompilation.DCEOpt
import CredibleCompilation.PeepholeOpt
import CredibleCompilation.RegAllocOpt
import CredibleCompilation.ExecChecker
import CredibleCompilation.CodeGenLayout
import CredibleCompilation.BoundsOpt
import CredibleCompilation.BoundsOptCert
import CredibleCompilation.ArmSemantics
import CredibleCompilation.ArmCorrectness
import CredibleCompilation.PropChecker

/-!
# ARM64 Code Generator for TAC Programs

Translates a type-checked `Prog` to ARM64 assembly (macOS AArch64).
Rejects programs that don't type-check.

## Design

- Variables are stored on the stack, indexed by a string→offset map.
- Integers are 64-bit signed (x registers).
- Booleans are stored as 0/1 in 64-bit slots.
- Observable variables are printed at halt via `_printf`.
- Division by zero calls `_exit(1)`.
-/

-- ============================================================
-- § 1. Variable layout
-- ============================================================

/-- Assign stack offsets to all variables that appear in the program. -/
-- collectVars, buildVarMap, lookupVar, varToArmReg, varToArmFReg,
-- buildVarLayout, checkCallerSaveSpec, checkCodegenPrereqs
-- are imported from CodeGenLayout.lean

private theorem mem_fst_of_mem_zip {a : α} {b : β} {l1 : List α} {l2 : List β}
    (h : (a, b) ∈ l1.zip l2) : a ∈ l1 := by
  induction l1 generalizing l2 with
  | nil => simp at h
  | cons _ _ ih =>
    cases l2 with
    | nil => simp at h
    | cons _ tl =>
      simp [List.zip_cons_cons] at h
      exact h.elim (fun ⟨h, _⟩ => h ▸ .head _) (fun h => .tail _ (ih h))

/-- The offsets produced by `buildVarMap` are pairwise distinct.
    Offsets are (i+1)*8 for i in [0, vars.length), which are injective. -/
private theorem buildVarMap_offsets_nodup (vars : List Var) :
    ((buildVarMap vars).map Prod.snd).Nodup := by
  simp only [buildVarMap, List.map_map]
  rw [List.Nodup, List.pairwise_map]
  -- Suffices: fst components of zip are pairwise distinct
  suffices List.Pairwise (fun a b => a.1 ≠ b.1) ((List.range vars.length).zip vars) by
    exact this.imp fun {a b} h heq => h (by
      show a.1 = b.1
      have : (a.1 + 1) * 8 = (b.1 + 1) * 8 := heq
      omega)
  -- Prove: zip preserves pairwise-distinctness on first components
  have hND := List.nodup_range (n := vars.length)
  rw [List.Nodup] at hND
  generalize List.range vars.length = ns at hND
  induction hND generalizing vars with
  | nil => simp
  | cons hmem _ ih =>
    cases vars with
    | nil => simp
    | cons v tl =>
      simp only [List.zip_cons_cons, List.pairwise_cons]
      exact ⟨fun ⟨x, w⟩ hm => hmem x (mem_fst_of_mem_zip hm), ih tl⟩


/-- Collect all distinct array names used in arrLoad/arrStore instructions. -/
private def collectArrays (p : Prog) : List String :=
  p.code.foldl (fun acc instr =>
    match instr with
    | .arrLoad _ arr _ _   => if acc.contains arr then acc else acc ++ [arr]
    | .arrStore arr _ _ _  => if acc.contains arr then acc else acc ++ [arr]
    | _                  => acc
  ) ([] : List String)

-- ============================================================
-- § 2. Assembly emission helpers
-- ============================================================

private def emit (lines : List String) : String :=
  String.intercalate "\n" lines

/-- Emit a `ldr`/`str` of `reg` at stack byte-offset `off`, legalizing offsets past the AArch64
    scaled 12-bit immediate ceiling.  An 8-aligned offset `≤ 32760` uses the compact immediate
    form `[sp, #off]`; any larger (or unaligned) offset is materialized in the reserved scratch
    `x16` (IP0 — never used by the emitted body) and accessed register-indexed.  This removes any
    limit on the number of stack-resident variables: the frame may be arbitrarily large.
    `verb` is `"ldr"` or `"str"`; the same form is valid for the `d*` float registers. -/
private def slotAccess (verb reg : String) (off : Nat) : List String :=
  if off % 8 == 0 && off ≤ 32760 then
    [s!"  {verb} {reg}, [sp, #{off}]"]
  else
    [s!"  ldr x16, ={off}", s!"  {verb} {reg}, [sp, x16]"]

/-- Load/store a stack variable (used only in prologue/epilogue/printf code). -/
private def loadVar (varMap : List (Var × Nat)) (v : Var) (reg : String) : List String :=
  match lookupVar varMap v with
  | some off => slotAccess "ldr" reg off
  | none => [s!"  // ERROR: unknown variable {v}"]

private def storeVar (varMap : List (Var × Nat)) (v : Var) (reg : String) : List String :=
  match lookupVar varMap v with
  | some off => slotAccess "str" reg off
  | none => [s!"  // ERROR: unknown variable {v}"]

private def loadVarFP (varMap : List (Var × Nat)) (v : Var) (freg : String) : List String :=
  match lookupVar varMap v with
  | some off => slotAccess "ldr" freg off
  | none => [s!"  // ERROR: unknown variable {v}"]

-- ============================================================
-- § 2a. ArmInstr pretty-printer
-- ============================================================

private def ppReg : ArmReg → String
  | .x0 => "x0" | .x1 => "x1" | .x2 => "x2" | .x3 => "x3"
  | .x4 => "x4" | .x5 => "x5" | .x6 => "x6" | .x7 => "x7"
  | .x8 => "x8" | .x9 => "x9" | .x10 => "x10" | .x11 => "x11"
  | .x12 => "x12" | .x13 => "x13" | .x14 => "x14" | .x15 => "x15"
  | .x16 => "x16" | .x17 => "x17" | .x18 => "x18"
  | .x19 => "x19" | .x20 => "x20" | .x21 => "x21" | .x22 => "x22"
  | .x23 => "x23" | .x24 => "x24" | .x25 => "x25" | .x26 => "x26"
  | .x27 => "x27" | .x28 => "x28"

private def ppFReg : ArmFReg → String
  | .d0 => "d0" | .d1 => "d1" | .d2 => "d2" | .d3 => "d3"
  | .d4 => "d4" | .d5 => "d5" | .d6 => "d6" | .d7 => "d7"
  | .d8 => "d8" | .d9 => "d9" | .d10 => "d10" | .d11 => "d11"
  | .d12 => "d12" | .d13 => "d13" | .d14 => "d14" | .d15 => "d15"

/-- Generate ARM load + store lines for one printf argument at stack offset `i*8`. -/
private def genPrintArgLoad (tyCtx : TyCtx) (layout : VarLayout)
    (varMap : List (Var × Nat)) (i : Nat) (v : Var) : List String :=
  let storeInstr := "  str " ++ (if tyCtx v == .float then "d0" else "x1") ++
    ", [sp, #" ++ toString (i * 8) ++ "]"
  if tyCtx v == .float then
    let loadLines := match layout v with
      | some (.freg reg) => [s!"  fmov d0, {ppFReg reg}"]
      | _ => loadVarFP varMap v "d0"
    loadLines ++ [storeInstr]
  else
    let loadLines := match layout v with
      | some (.ireg reg) => [s!"  mov x1, {ppReg reg}"]
      | _ => loadVar varMap v "x1"
    loadLines ++ [storeInstr]

private def ppCond : Cond → String
  | .eq => "eq" | .ne => "ne" | .lt => "lt" | .le => "le" | .gt => "gt" | .ge => "ge"
  | .hs => "hs" | .lo => "lo"

/-- Map float-comparison condition codes to ARM64 mnemonics.
    After `fcmp`, we use the SAME (signed) mnemonics as integer `cmp`. The model
    (`fcmpFlags` + `Flags.condHolds`) is a total-order encoding: it maps the IEEE
    4-way result (less / equal / greater / unordered) to a canonical `(lhs, rhs)`
    pair, with UNORDERED encoded so that `lt`/`le` hold and `gt`/`ge`/`eq` do not
    — exactly the AArch64 `lt`/`le` (N≠V) semantics, which INCLUDE the unordered
    case. Using `mi`/`ls` here (ordered-only, excluding unordered) would disagree
    with that encoding for NaN operands and is unrepresentable by `condHolds`
    without breaking `Cond.negate_correct`. -/
private def ppCondFloat : Cond → String
  | .eq => "eq" | .ne => "ne" | .lt => "lt" | .le => "le" | .gt => "gt" | .ge => "ge"
  | .hs => "hs" | .lo => "lo"

/-- Resolve a branch target (Nat) to a label string.
    Sentinel values map to special labels; others are reverse-mapped from
    ARM PC offsets back to TAC PC labels. -/
private def ppLabel (haltS divS boundsS : Nat) (tacPcOf : Nat → Option Nat)
    (target : Nat) : String :=
  if target == haltS then ".Lhalt"
  else if target == divS then ".Ldiv_by_zero"
  else if target == boundsS then ".Lbounds_err"
  else match tacPcOf target with
    | some tacPC => s!".L{tacPC}"
    | none => s!".Larm{target}"

/-- Encode a byte as a fixed-width hex digit pair (e.g. `0x41` → `"41"`).
    Used by `stringPoolLabel` to produce a deterministic, collision-free
    encoding of arbitrary string content as a valid assembler identifier. -/
private def hexByte (b : UInt8) : String :=
  let digit (n : Nat) : Char :=
    if n < 10 then Char.ofNat (n + '0'.toNat)
    else Char.ofNat (n - 10 + 'a'.toNat)
  String.mk [digit (b.toNat / 16), digit (b.toNat % 16)]

/-- Deterministic label for a printString literal: `.Lstr_<hex>` where `<hex>`
    is the lowercase hex encoding of the UTF-8 bytes of the literal. Pure
    function of the string — identical literals share a label (deduplication)
    and distinct literals never collide. -/
def stringPoolLabel (lit : String) : String :=
  ".Lstr_" ++ String.join (lit.toUTF8.toList.map hexByte)

/-- Pretty-print a single ArmInstr to one or more assembly lines.
    `afterFcmp` indicates the preceding instruction was `fcmpR`, so
    condition codes for `cset` use the float convention.
    Save/restore of caller-saved registers around library calls is now
    handled by the verified codegen layer (genCallSaveRestore), so ppInstr
    no longer needs libSave/libRestore parameters. -/
private def ppInstr (lbl : Nat → String) (afterFcmp : Bool)
    (instr : ArmInstr) : List String :=
  match instr with
  | .mov rd n =>
    AsmEnc.render (.mov rd n)
  | .movR rd rn =>
    if rd == rn then [] else [s!"  mov {ppReg rd}, {ppReg rn}"]
  | .movz rd imm16 shift =>
    AsmEnc.render (.movz rd imm16 shift)
  | .movk rd imm16 shift =>
    AsmEnc.render (.movk rd imm16 shift)
  | .ldr rd off =>
    -- verified, encodability-checked load (legalizes over-ceiling offsets); see AsmEnc
    AsmEnc.render (.ldr rd off)
  | .str rs off =>
    AsmEnc.render (.str rs off)
  | .addR rd rn rm =>
    [s!"  add {ppReg rd}, {ppReg rn}, {ppReg rm}"]
  | .subR rd rn rm =>
    [s!"  sub {ppReg rd}, {ppReg rn}, {ppReg rm}"]
  | .mulR rd rn rm =>
    [s!"  mul {ppReg rd}, {ppReg rn}, {ppReg rm}"]
  | .sdivR rd rn rm =>
    [s!"  sdiv {ppReg rd}, {ppReg rn}, {ppReg rm}"]
  | .cmp rn rm =>
    [s!"  cmp {ppReg rn}, {ppReg rm}"]
  | .cmpImm rn imm =>
    -- verified, encodability-checked compare (imm12, else legalize via ldr =imm); see AsmEnc
    AsmEnc.render (.cmpImm rn imm)
  | .cset rd c =>
    -- Model sets the named register `rd` (not always x0), 64-bit. Emit into
    -- `rd`; `cset Xd, cond` writes 0/1 zero-extended, matching `setReg rd`.
    [s!"  cset {ppReg rd}, {if afterFcmp then ppCondFloat c else ppCond c}"]
  | .cbz rn target =>
    [s!"  cbz {ppReg rn}, {lbl target}"]
  | .cbnz rn target =>
    -- Model tests the full 64-bit register `rn`; emit `cbnz Xn` (not `w0`),
    -- which tests all 64 bits and the register the model names.
    [s!"  cbnz {ppReg rn}, {lbl target}"]
  | .andImm rd rn imm =>
    AsmEnc.render (.andImm rd rn imm)
  | .andR rd rn rm =>
    [s!"  and {ppReg rd}, {ppReg rn}, {ppReg rm}"]
  | .eorImm rd rn imm =>
    AsmEnc.render (.eorImm rd rn imm)
  | .orrR rd rn rm =>
    [s!"  orr {ppReg rd}, {ppReg rn}, {ppReg rm}"]
  | .eorR rd rn rm =>
    [s!"  eor {ppReg rd}, {ppReg rn}, {ppReg rm}"]
  | .lslR rd rn rm =>
    [s!"  lsl {ppReg rd}, {ppReg rn}, {ppReg rm}"]
  | .asrR rd rn rm =>
    [s!"  asr {ppReg rd}, {ppReg rn}, {ppReg rm}"]
  | .b target =>
    [s!"  b {lbl target}"]
  | .printCall lines => lines
  | .callPrintI =>
    ["  stp x29, x30, [sp, #-16]!", "  bl _printInt", "  ldp x29, x30, [sp], #16"]
  | .callPrintB =>
    ["  stp x29, x30, [sp, #-16]!", "  bl _printBool", "  ldp x29, x30, [sp], #16"]
  | .callPrintF =>
    ["  stp x29, x30, [sp, #-16]!", "  bl _printFloat", "  ldp x29, x30, [sp], #16"]
  | .callPrintS lit =>
    [s!"  adrp x0, {stringPoolLabel lit}@PAGE",
     s!"  add x0, x0, {stringPoolLabel lit}@PAGEOFF",
     "  stp x29, x30, [sp, #-16]!",
     "  bl _printString",
     "  ldp x29, x30, [sp], #16"]
  | .bCond c target =>
    [s!"  b.{if afterFcmp then ppCondFloat c else ppCond c} {lbl target}"]
  | .arrLd dst arr idxReg =>
    [s!"  adrp x0, _arr_{arr}@PAGE",
     s!"  add x0, x0, _arr_{arr}@PAGEOFF",
     s!"  ldr {ppReg dst}, [x0, {ppReg idxReg}, lsl #3]"]
  | .arrSt arr idxReg valReg =>
    [s!"  adrp x0, _arr_{arr}@PAGE",
     s!"  add x0, x0, _arr_{arr}@PAGEOFF",
     s!"  str {ppReg valReg}, [x0, {ppReg idxReg}, lsl #3]"]
  | .fmovToFP fd rn =>
    [s!"  fmov {ppFReg fd}, {ppReg rn}"]
  | .fmovRR fd fn =>
    if fd == fn then [] else [s!"  fmov {ppFReg fd}, {ppFReg fn}"]
  | .fldr fd off =>
    AsmEnc.render (.fldr fd off)
  | .fstr fs off =>
    AsmEnc.render (.fstr fs off)
  | .faddR fd fn fm =>
    [s!"  fadd {ppFReg fd}, {ppFReg fn}, {ppFReg fm}"]
  | .fsubR fd fn fm =>
    [s!"  fsub {ppFReg fd}, {ppFReg fn}, {ppFReg fm}"]
  | .fmulR fd fn fm =>
    [s!"  fmul {ppFReg fd}, {ppFReg fn}, {ppFReg fm}"]
  | .fdivR fd fn fm =>
    [s!"  fdiv {ppFReg fd}, {ppFReg fn}, {ppFReg fm}"]
  | .fmaddR fd fn fm fa =>
    [s!"  fmadd {ppFReg fd}, {ppFReg fn}, {ppFReg fm}, {ppFReg fa}"]
  | .fmsubR fd fn fm fa =>
    [s!"  fmsub {ppFReg fd}, {ppFReg fn}, {ppFReg fm}, {ppFReg fa}"]
  | .fminR fd fn fm =>
    [s!"  fminnm {ppFReg fd}, {ppFReg fn}, {ppFReg fm}"]
  | .fmaxR fd fn fm =>
    [s!"  fmaxnm {ppFReg fd}, {ppFReg fn}, {ppFReg fm}"]
  | .callBinF fop fd fn fm =>
    let name := match fop with
      | .fpow => "_pow" | _ => "_unknown_binop"
    let load0 := if fn == .d0 then [] else [s!"  fmov d0, {ppFReg fn}"]
    let load1 := if fm == .d1 then [] else [s!"  fmov d1, {ppFReg fm}"]
    let store := if fd == .d0 then [] else [s!"  fmov {ppFReg fd}, d0"]
    load0 ++ load1 ++ [s!"  stp x29, x30, [sp, #-16]!", s!"  bl {name}",
             "  ldp x29, x30, [sp], #16"] ++ store
  | .fcmpR fn fm =>
    [s!"  fcmp {ppFReg fn}, {ppFReg fm}"]
  | .scvtf fd rn =>
    [s!"  scvtf {ppFReg fd}, {ppReg rn}"]
  | .fcvtzs rd fn =>
    [s!"  fcvtzs {ppReg rd}, {ppFReg fn}"]
  | .farrLd fd arr idxReg =>
    [s!"  adrp x0, _arr_{arr}@PAGE",
     s!"  add x0, x0, _arr_{arr}@PAGEOFF",
     s!"  ldr {ppFReg fd}, [x0, {ppReg idxReg}, lsl #3]"]
  | .farrSt arr idxReg fs =>
    [s!"  adrp x0, _arr_{arr}@PAGE",
     s!"  add x0, x0, _arr_{arr}@PAGEOFF",
     s!"  str {ppFReg fs}, [x0, {ppReg idxReg}, lsl #3]"]
  | .floatUnaryInstr op fd fn =>
    match op with
    | .sqrt => [s!"  fsqrt {ppFReg fd}, {ppFReg fn}"]
    | .abs  => [s!"  fabs {ppFReg fd}, {ppFReg fn}"]
    | .neg  => [s!"  fneg {ppFReg fd}, {ppFReg fn}"]
    | _ =>  -- library call intrinsics (save/restore handled by verified codegen)
      let name := match op with
        | .exp => "_exp" | .sin => "_sin" | .cos => "_cos" | .tan => "_tan"
        | .log => "_log" | .log2 => "_log2" | .log10 => "_log10" | .round => "_round"
        | .sqrt | .abs | .neg => unreachable!
      let load := if fn == .d0 then [] else [s!"  fmov d0, {ppFReg fn}"]
      let store := if fd == .d0 then [] else [s!"  fmov {ppFReg fd}, d0"]
      load ++ [s!"  stp x29, x30, [sp, #-16]!", s!"  bl {name}",
               "  ldp x29, x30, [sp], #16"] ++ store

/-- Pretty-print a list of ArmInstr, tracking fcmp state for cset. -/
private def ppInstrs (lbl : Nat → String)
    : List ArmInstr → List String
  | [] => []
  | instr :: rest =>
    let afterFcmp := match instr with | .fcmpR .. => true | _ => false
    let lines := ppInstr lbl false instr
    let restLines := ppInstrsAux lbl afterFcmp rest
    lines ++ restLines
where
  ppInstrsAux (lbl : Nat → String)
      (prevWasFcmp : Bool) : List ArmInstr → List String
    | [] => []
    | instr :: rest =>
      let lines := ppInstr lbl prevWasFcmp instr
      let nextFcmp := match instr with | .fcmpR .. => true | _ => false
      lines ++ ppInstrsAux lbl nextFcmp rest

/-- Harness hook (T1): render ArmInstr list to asm via the verified printer. -/
def renderAsmBody (instrs : List ArmInstr) : List String :=
  ppInstrs (fun n => s!".L{n}") instrs


-- ============================================================
-- § 2b. VarLayout construction
-- ============================================================


-- ============================================================
-- § 2c. Call-site save/restore for caller-saved registers
-- ============================================================

/-- Is a TAC instruction a library call that clobbers caller-saved registers?
    This includes non-native float unary ops (exp, sin, …) and fpow. -/
def isLibCallTAC : TAC → Bool
  | .floatUnary _ op _ => !op.isNative
  | .fbinop _ .fpow _ _ => true
  | .printInt _ => true
  | .printBool _ => true
  | .printFloat _ => true
  | .printString _ => true
  | _ => false

/-- Generate save/restore ArmInstr lists for caller-saved registers that are live
    at a library call site. Each live variable in a caller-saved register is saved
    to its existing stack slot (from varMap) before the call and restored after.
    Returns (saveInstrs, restoreInstrs). -/
def genCallSaveRestore (liveVars : List Var) (layout : VarLayout)
    (varMap : List (Var × Nat)) : List ArmInstr × List ArmInstr :=
  let callerSavedLive := liveVars.filterMap fun v =>
    match layout v with
    | some (.ireg r) =>
      if r.isCallerSaved then
        match varMap.find? (fun (x, _) => x == v) with
        | some (_, off) => some (Sum.inl (r, off))  -- int reg + stack offset
        | none => none
      else none
    | some (.freg r) =>
      if r.isCallerSaved then
        match varMap.find? (fun (x, _) => x == v) with
        | some (_, off) => some (Sum.inr (r, off))  -- float reg + stack offset
        | none => none
      else none
    | _ => none
  let saves := callerSavedLive.map fun
    | .inl (r, off) => ArmInstr.str r off
    | .inr (r, off) => ArmInstr.fstr r off
  let restores := callerSavedLive.map fun
    | .inl (r, off) => ArmInstr.ldr r off
    | .inr (r, off) => ArmInstr.fldr r off
  (saves, restores)

/-- Filter genCallerSaveAll entries to exclude the destination variable's register.
    For lib-calls, the destination's register should NOT be saved/restored because
    the base instructions write the result there and restoring would overwrite it. -/
private def callerSaveEntries (layout : VarLayout) (varMap : List (Var × Nat))
    (exclude : Option Var := none) : List CallerSaveEntry :=
  let all := genCallerSaveAll layout varMap
  match exclude with
  | none => all
  | some d => all.filter fun e =>
    match layout d, e with
    | some (.ireg r), .ireg ir _ => !(ir == r)
    | some (.freg r), .freg fr _ => !(fr == r)
    | _, _ => true

/-- Number of save/restore instructions for a call site. -/
private def callSaveRestoreLen (layout : VarLayout)
    (varMap : List (Var × Nat)) (exclude : Option Var := none) : Nat :=
  let entries := callerSaveEntries layout varMap exclude
  (entriesToSaves entries).length + (entriesToRestores entries).length

/-- Remove the destination variable of an instruction from a live-variable list.
    At a call site `x := f(...)`, x's old value is dead (being overwritten),
    so it must not be saved/restored — the call produces x's new value. -/
private def removeDest (instr : TAC) (live : List Var) : List Var :=
  match DAEOpt.instrDef instr with
  | some x => live.filter (· != x)
  | none => live

-- ============================================================
-- § 2d. pcMap and bounds-safe computation
-- ============================================================

/-- Compute instruction length for a TAC instruction.
    `pcMap` does not affect instruction count (only branch target values).
    Neither do `haltS`/`divS`/`boundsS` (they are just immediates inside
    branch instructions). We use dummy values (`fun _ => 0` and `0`) when
    invoking `verifiedGenInstr`; `verifiedGenInstr_length_pcMap_ind` and
    `verifiedGenInstr_length_labels_ind` justify this.
    Save/restore uses `genCallerSaveAll` (all caller-saved regs, not just live). -/
private def instrLength (layout : VarLayout) (arrayDecls : List (ArrayName × Nat × VarTy))
    (boundsSafe : Bool) (instr : TAC)
    (varMap : List (Var × Nat) := []) : Nat :=
  match instr with
  | .print _ _ =>
    -- saves + 1 printCall + restores
    1 + callSaveRestoreLen layout varMap
  | _ =>
  let baseLen := match verifiedGenInstr layout (fun _ => 0) instr 0 0 0 arrayDecls boundsSafe with
    | some l => l.length
    | none => 0
  if isLibCallTAC instr then
    baseLen + callSaveRestoreLen layout varMap (DAEOpt.instrDef instr)
  else baseLen

/-- Build a pcMap (TAC PC → cumulative ARM instruction offset) as a prefix sum. -/
private def buildPcMap (lengths : Array Nat) : Nat → Nat :=
  let offsets := lengths.foldl (init := #[0]) fun acc len =>
    acc.push (acc.back! + len)
  fun tacPC => offsets.getD tacPC 0

/-- Build reverse map: ARM instruction offset → TAC PC (only defined at boundaries). -/
private def buildTacPcOf (lengths : Array Nat) : Nat → Option Nat :=
  let init : List (Nat × Nat) × Nat := ([], 0)
  let pairs := (List.range lengths.size).foldl (init := init) fun state i =>
    let acc := state.1
    let cumLen := state.2
    ((cumLen, i) :: acc, cumLen + (lengths.getD i 0))
  fun armPC => (pairs.1.find? fun p => p.1 == armPC).map Prod.snd

/-- Phase 6 helper: Boolean check that the analyzer's entry-PC claim is
    trivially satisfiable. Combined with `checkLocalPreservation`, this
    forces `intervalMap inv 0 σ am` to hold for every `σ, am` — the exact
    shape required for `GenAsmSpec.invAtStart`. Satisfied when either
    the analyzer claims an empty `IMap` at PC 0 (the initial state of
    `analyzeIntervals` before any join/widen) or the program is empty so
    PC 0 is out of range (`intervalMap` falls through to `True`). -/
private def checkInvAtStart (inv : Array (Option BoundsOpt.IMap)) : Bool :=
  match inv[0]? with
  | some (some []) => true
  | none           => true
  | _              => false

/-- Phase 6: real per-PC bounds-check elision decision. Returns `true` only
    when all three conditions hold:
    1. `checkerOk` — the verified checker accepted the intervals globally.
    2. `instr` is an `.arrLoad` / `.arrStore`.
    3. `intervals[pc]` contains a `validIntervalLoose` entry for the index
       whose `hi` ≤ the array's declared size.
    The caller must compute `checkerOk := checkLocalPreservation p intervals &&
    checkInvAtStart intervals` once per program and thread it in. Under Phase 5,
    `hBoundsSafeOracle` at the `arrLoad`/`arrStore` arm needs access to
    `buildVerifiedInvMap p pc σ am`; when `isBoundsSafe` returns true here,
    the invariant is the conjunction of `checkerOk` (→ `intervalMap inv`
    is preserved) and the per-pc interval lookup being in-bounds. -/
private def isBoundsSafe (checkerOk : Bool) (arrayDecls : List (ArrayName × Nat × VarTy))
    (intervals : Array (Option BoundsOpt.IMap)) (pc : Nat) (instr : TAC) : Bool :=
  checkerOk &&
  match instr with
  | .arrLoad _ arr idx _ | .arrStore arr idx _ _ =>
      match intervals[pc]? with
      | some (some m) =>
          let r := BoundsOpt.imLookup m idx
          BoundsOpt.validIntervalLoose r && r.inBounds (arraySize arrayDecls arr) &&
            -- Bound arraySize so BitVec/Nat comparison agrees (arraySizeBv doesn't wrap).
            decide (arraySize arrayDecls arr < 2 ^ 62)
      | _ => false
  | _ => false

/-- Phase 6 wrapper: the per-PC bounds-check elision flag that the verified
    code generator actually consumes. Computes the intervals, runs the checker
    + entry-PC satisfaction gate, and then delegates to `isBoundsSafe` for the
    per-pc interval lookup. When the checker rejects, returns `false` so the
    generated ARM retains the explicit bounds check and the oracle hypothesis
    discharges vacuously. -/
def verifiedBoundsSafe (p : Prog) (pc : Nat) : Bool :=
  let intervals := BoundsOpt.analyzeIntervals p
  let checkerOk := BoundsOpt.checkLocalPreservation p intervals && checkInvAtStart intervals
  isBoundsSafe checkerOk p.arrayDecls intervals pc (p.code.getD pc .halt)

private theorem checkInvAtStart_sound {inv : Array (Option BoundsOpt.IMap)}
    (h : checkInvAtStart inv = true) (σ : Store) (am : ArrayMem) :
    BoundsOpt.intervalMap inv 0 σ am := by
  simp only [BoundsOpt.intervalMap]
  unfold checkInvAtStart at h
  split at h
  · -- inv[0]? = some (some [])
    rename_i heq
    rw [heq]
    intros v r hmem
    cases hmem
  · -- inv[0]? = none
    rename_i heq
    rw [heq]
    trivial
  · -- otherwise: h : false = true, contradiction
    exact absurd h (by decide)

/-- Phase 4: the validated per-program invariant map. Pipeline:
    1. Run `BoundsOpt.analyzeIntervals p` (untrusted oracle) to get intervals.
    2. Run the verified `BoundsOpt.checkLocalPreservation` checker.
    3. If the checker accepts AND the entry-PC claim is trivially satisfiable
       (via `checkInvAtStart`), lift the intervals to a `PInvariantMap` via
       `BoundsOpt.intervalMap`.
    4. Otherwise fall back to the constant-`True` map.
    Both branches satisfy `preserved p` and `∀ σ am, invMap 0 σ am`. -/
private def buildVerifiedInvMap (p : Prog) : PInvariantMap :=
  fun pc σ am =>
    let inv := BoundsOpt.analyzeIntervals p
    if BoundsOpt.checkLocalPreservation p inv && checkInvAtStart inv
    then BoundsOpt.intervalMap inv pc σ am
    else True

private theorem buildVerifiedInvMap_preserved (p : Prog) :
    (buildVerifiedInvMap p).preserved p := by
  intro pc σ am hInv pc' σ' am' hStep
  simp only [buildVerifiedInvMap] at hInv ⊢
  split at hInv
  · rename_i hChk
    rw [Bool.and_eq_true] at hChk
    split
    · exact BoundsOpt.checkLocalPreservation_sound p _ hChk.1 pc σ am hInv pc' σ' am' hStep
    · trivial
  · split
    · -- hChk-positive on pc', negative on (same) conditions: impossible
      rename_i hNeg hPos
      exact absurd hPos hNeg
    · trivial

private theorem buildVerifiedInvMap_atStart (p : Prog) :
    ∀ σ am, buildVerifiedInvMap p 0 σ am := by
  intro σ am
  simp only [buildVerifiedInvMap]
  split
  · rename_i hChk
    rw [Bool.and_eq_true] at hChk
    exact checkInvAtStart_sound hChk.2 σ am
  · trivial

-- ============================================================
-- § 3. Well-formedness checks (discharge proof hypotheses at runtime)
-- ============================================================

-- checkWellTypedLayout: imported from CodeGenLayout.lean

/-- Check that all branch targets are in bounds.
    Corresponds to the `hPC_bound` hypothesis on successor PCs. -/
def checkBranchTargets (code : Array TAC) : Option String :=
  let n := code.size
  match (List.range n).find? fun pc =>
    match code.getD pc .halt with
    | .goto l | .ifgoto _ l => l >= n
    | _ => false
  with
  | some pc =>
    let target := match code.getD pc .halt with
      | .goto l | .ifgoto _ l => l | _ => 0
    some s!"branch at PC {pc} targets {target} (out of bounds, size = {n})"
  | none => none

-- lookup_mem: imported from CodeGenLayout.lean

-- ============================================================
-- § 4b. Caller-save spec checker
-- ============================================================

-- listNodupBool, checkCallerSaveSpec: imported from CodeGenLayout.lean

/-- Soundness: if the caller-save check passes, all 6 properties hold. -/
private theorem checkCallerSaveSpec_sound {layout : VarLayout} {varMap : List (Var × Nat)}
    (h : checkCallerSaveSpec layout varMap = true) :
    let entries := genCallerSaveAll layout varMap
    -- hFresh
    (∀ e ∈ entries, ∀ v, layout v ≠ some (.stack e.off)) ∧
    -- hNodup
    (entries.map CallerSaveEntry.off).Nodup ∧
    -- hCoversIreg
    (∀ v ir, layout v = some (.ireg ir) → ir.isCallerSaved = true →
      ∃ off, CallerSaveEntry.ireg ir off ∈ entries) ∧
    -- hCoversFreg
    (∀ v fr, layout v = some (.freg fr) → fr.isCallerSaved = true →
      ∃ off, CallerSaveEntry.freg fr off ∈ entries) ∧
    -- hUniqIreg
    (∀ ir off1 off2, CallerSaveEntry.ireg ir off1 ∈ entries →
      CallerSaveEntry.ireg ir off2 ∈ entries → off1 = off2) ∧
    -- hUniqFreg
    (∀ fr off1 off2, CallerSaveEntry.freg fr off1 ∈ entries →
      CallerSaveEntry.freg fr off2 ∈ entries → off1 = off2) := by
  simp only [checkCallerSaveSpec, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hFreshB, hNodupB⟩, hCovIB⟩, hCovFB⟩, hUniqIB⟩, hUniqFB⟩ := h
  have hNodupP := listNodupBool_sound hNodupB
  refine ⟨?_, hNodupP, ?_, ?_, ?_, ?_⟩
  · -- hFresh
    intro e he v hContra
    have := (List.all_eq_true.mp hFreshB) e he
    have hAll := List.all_eq_true.mp this
    have hMem := lookup_mem hContra
    have := hAll ⟨v, .stack e.off⟩ hMem
    simp at this
  · -- hCoversIreg
    intro v ir hLoc hCS
    have hMem := lookup_mem hLoc
    have := (List.all_eq_true.mp hCovIB) ⟨v, .ireg ir⟩ hMem
    simp only [hCS, Bool.not_true, Bool.false_or] at this
    rw [List.any_eq_true] at this
    obtain ⟨e, heMem, heEq⟩ := this
    match e, heEq with
    | .ireg ir' off, heq =>
      simp at heq; exact ⟨off, heq ▸ heMem⟩
    | .freg _ _, heq => simp at heq
  · -- hCoversFreg
    intro v fr hLoc hCS
    have hMem := lookup_mem hLoc
    have := (List.all_eq_true.mp hCovFB) ⟨v, .freg fr⟩ hMem
    simp only [hCS, Bool.not_true, Bool.false_or] at this
    rw [List.any_eq_true] at this
    obtain ⟨e, heMem, heEq⟩ := this
    match e, heEq with
    | .freg fr' off, heq =>
      simp at heq; exact ⟨off, heq ▸ heMem⟩
    | .ireg _ _, heq => simp at heq
  · -- hUniqIreg: pairwise check → same reg means same offset
    intro ir off1 off2 h1 h2
    have h1' := (List.all_eq_true.mp hUniqIB) (.ireg ir off1) h1
    have h2' := (List.all_eq_true.mp h1') (.ireg ir off2) h2
    simp at h2'; exact h2'
  · -- hUniqFreg: pairwise check → same reg means same offset
    intro fr off1 off2 h1 h2
    have h1' := (List.all_eq_true.mp hUniqFB) (.freg fr off1) h1
    have h2' := (List.all_eq_true.mp h1') (.freg fr off2) h2
    simp at h2'; exact h2'

-- ============================================================
-- § 5. Program codegen
-- ============================================================

/-- Result of the verified code generation core.
    Contains structured ArmInstr arrays that can be pretty-printed by the
    unverified shell, and all metadata needed for label resolution.

    Phase 2 layout: `bodyFlat = (bodyPerPC concatenated) ++ haltSaveBlock`.
    `haltS` is the start of `haltSaveBlock` inside `bodyFlat`;
    `haltFinal = bodyFlat.size`;
    `divS = haltFinal + 1`, `boundsS = haltFinal + 2` (off-the-end, stuck). -/
structure VerifiedAsmResult where
  /-- Variable zeroing instructions (register zeros + stack zeros). -/
  initInstrs : Array ArmInstr
  /-- Per-TAC-PC list of generated ARM instructions.
      Library call sites include save/restore of live caller-saved registers. -/
  bodyPerPC : Array (List ArmInstr)
  /-- Instructions to save register-allocated observable values to stack.
      Lives at the END of `bodyFlat` (between `haltS` and `haltFinal`). -/
  haltSaveBlock : Array ArmInstr
  /-- TAC PC → cumulative ARM instruction offset. -/
  pcMap : Nat → Nat
  /-- Variable layout (register/stack assignments). -/
  layout : VarLayout
  /-- Variable name → stack offset map (all vars have slots for printf). -/
  varMap : List (Var × Nat)
  /-- Number of init instructions (for label offset computation). -/
  initLen : Nat
  /-- Start of halt-save block. Stored here for convenience; equals
      `(bodyPerPC.toList.flatMap id).length` (= `pcMap p.code.size`). -/
  haltS : Nat
  /-- End of halt-save block = end of `bodyFlat`. Stored here; equals
      `haltS + haltSaveBlock.size` (= `bodyFlat.size`). -/
  haltFinal : Nat
  /-- Division-by-zero sentinel: off-the-end of `bodyFlat`, hence stuck.
      Stored here; equals `haltFinal + 1`. -/
  divS : Nat
  /-- Array-bounds-violation sentinel: also off-the-end of `bodyFlat`, stuck.
      Stored here; equals `haltFinal + 2`. -/
  boundsS : Nat
  /-- Reverse map: ARM offset → TAC PC. -/
  tacPcOf : Nat → Option Nat
  /-- Callee-saved register save instructions (prologue). -/
  calleeSavePrologue : List ArmInstr
  /-- Callee-saved register restore instructions (epilogue). -/
  calleeSaveEpilogue : List ArmInstr
  /-- Which callee-saved registers are used: (intRegs, floatRegs). -/
  calleeSaveRegs : List Nat × List Nat

/-- Generate init instructions that zero all variables.
    Register vars get register-zero moves; stack vars get str x0. -/
private def genInitCode (vars : List Var) (layout : VarLayout) : List ArmInstr :=
  vars.filterMap fun v =>
    match layout v with
    | some (.freg r) => some (.fmovToFP r .x0)   -- fmov dN, xzr  (x0 is 0)
    | some (.ireg r) => some (.mov r 0)
    | some (.stack off) => some (.str .x0 off)
    | none => none

/-- Generate halt-save instructions for a single observable.
    - Register-allocated (ireg/freg): emit a store to the observable's stack slot.
    - Stack-resident: no-op (value is already at its output offset).
    - Missing layout or varMap entry: no-op (should be ruled out by a completeness
      invariant on `VerifiedAsmResult`; only reachable if invariants are violated). -/
def genHaltSaveOne (v : Var) (layout : VarLayout)
    (varMap : List (Var × Nat)) : List ArmInstr :=
  match layout v with
  | some (.ireg r) =>
    match lookupVar varMap v with
    | some off => [.str r off]
    | none => []
  | some (.freg r) =>
    match lookupVar varMap v with
    | some off => [.fstr r off]
    | none => []
  | some (.stack _) => []
  | none => []

/-- Generate instructions to save observable values to their halt-output stack slots.
    Iterates per-observable via `genHaltSaveOne`; see that function for per-case behavior. -/
def genHaltSave (observable : List Var) (layout : VarLayout)
    (varMap : List (Var × Nat)) : List ArmInstr :=
  observable.flatMap (genHaltSaveOne · layout varMap)

/-- Detect callee-saved registers used in the layout. Returns (intRegNums, floatRegNums). -/
private def detectCalleeSavedLayout (layout : VarLayout) : List Nat × List Nat :=
  let intRegs := layout.entries.filterMap fun (_, loc) =>
    match loc with
    | .ireg r => if !r.isCallerSaved then some r.toNat else none
    | _ => none
  let floatRegs := layout.entries.filterMap fun (_, loc) =>
    match loc with
    | .freg r => if !r.isCallerSaved then some r.toNat else none
    | _ => none
  (intRegs.eraseDups, floatRegs.eraseDups)

/-- Generate callee-save prologue (store) and epilogue (load) ArmInstr lists.
    `baseOffset` is the stack offset where the callee-save area begins
    (typically right after variable slots). -/
private def genVerifiedCalleeSave (intRegs : List Nat) (floatRegs : List Nat)
    (baseOffset : Nat) : List ArmInstr × List ArmInstr :=
  -- Save int registers
  let (intSaves, intRestores, _) := intRegs.foldl (fun (s, r, off) n =>
    let reg := ArmReg.fromRegNum n
    (s ++ [.str reg off], r ++ [.ldr reg off], off + 8)
  ) ([], [], baseOffset)
  -- Save float registers
  let (floatSaves, floatRestores, _) := floatRegs.foldl (fun (s, r, off) n =>
    let freg := ArmFReg.fromRegNum n
    (s ++ [.fstr freg off], r ++ [.fldr freg off], off + 8)
  ) ([], [], baseOffset + intRegs.length * 8)
  (intSaves ++ floatSaves, intRestores ++ floatRestores)

/-- Build the pre-computed assembly lines for a `printCall` instruction.
    These are emitted by `ppInstr` and model the printf calling convention:
    sub sp, arg loads, adrp/add for format string, bl _printf, add sp. -/
private def genPrintCallLines (tyCtx : TyCtx) (layout : VarLayout)
    (varMap : List (Var × Nat)) (pc : Nat) (fmt : String) (vs : List Var) : List String :=
  let stackSize := max 16 (((vs.length * 8 + 15) / 16) * 16)
  let fmtComment := fmt.foldl (fun acc c => match c with
    | '\n' => acc ++ "\\n" | '\t' => acc ++ "\\t" | c => acc ++ c.toString) ""
  let loadLines := (List.range vs.length).flatMap fun i =>
    genPrintArgLoad tyCtx layout varMap i (vs.getD i "")
  let comment := "  // print " ++ "\"" ++ fmtComment ++ "\""
  let fmtLabel := ".Lfmt_print_" ++ toString pc
  let subSp := "  sub sp, sp, #" ++ toString stackSize
  let addSp := "  add sp, sp, #" ++ toString stackSize
  let adrp := "  adrp x0, " ++ fmtLabel ++ "@PAGE"
  let addX0 := "  add x0, x0, " ++ fmtLabel ++ "@PAGEOFF"
  let bl := "  bl _printf"
  comment :: subSp :: loadLines ++ [adrp, addX0, bl, addSp]

/-- Step function for pass-2 body generation. For each TAC instruction,
    generates (and possibly wraps) ARM instructions, pushing onto the accumulator.
    Returns `none` if verifiedGenInstr fails; propagates `none` from previous steps. -/
private def bodyGenStep (code : Array TAC) (layout : VarLayout) (pcMap : Nat → Nat)
    (_liveOut : Array (List Var)) (varMap : List (Var × Nat))
    (checkerOk : Bool)
    (intervals : Array (Option BoundsOpt.IMap))
    (arrayDecls : List (ArrayName × Nat × VarTy))
    (haltS divS boundsS : Nat) (tyCtx : TyCtx)
    (acc : Option (Array (List ArmInstr))) (pc : Nat)
    : Option (Array (List ArmInstr)) :=
  match acc with
  | none => none
  | some arr =>
    let instr := code.getD pc .halt
    let safe := isBoundsSafe checkerOk arrayDecls intervals pc instr
    let isPrint := match instr with | .print _ _ => true | _ => false
    if isPrint then
      let (fmt, vs) := match instr with | .print f v => (f, v) | _ => ("", [])
      let entries := genCallerSaveAll layout varMap
      let saves := entriesToSaves entries
      let restores := entriesToRestores entries
      let printLines := genPrintCallLines tyCtx layout varMap pc fmt vs
      some (arr.push (saves ++ [ArmInstr.printCall printLines] ++ restores))
    else
    match verifiedGenInstr layout pcMap instr haltS divS boundsS arrayDecls safe with
    | none => none
    | some armInstrs =>
      let armInstrs' :=
        if isLibCallTAC instr then
          -- Exclude destination: restoring it would overwrite the computation result
          let entries := callerSaveEntries layout varMap (DAEOpt.instrDef instr)
          entriesToSaves entries ++ armInstrs ++ entriesToRestores entries
        else armInstrs
      some (arr.push armInstrs')

/-- Verified core of code generation. Performs all validation and produces
    structured ArmInstr data. No string emission or platform-specific code. -/
def verifiedGenerateAsm (tyCtx : TyCtx) (p : Prog) : Except String VerifiedAsmResult := do
  if !checkWellTypedProg tyCtx p then
    .error "program failed type check"
  else
    let vars := collectVars p
    let varMap := buildVarMap vars
    let layout := buildVarLayout vars varMap
    -- Check layout safety: no scratch registers, injective mapping
    if !layout.regConventionSafe then
      .error "layout uses scratch register"
    else if !layout.isInjective then
      .error "layout is not injective"
    else
    -- Check WellTypedLayout (hWTL hypothesis)
    match checkWellTypedLayout tyCtx layout p.code with
    | some err => .error s!"well-typed layout check failed: {err}"
    | none =>
    -- Check caller-save spec (callerSave_composition hypotheses)
    if !checkCallerSaveSpec layout varMap then
      .error "caller-save spec check failed"
    else
    -- Check branch targets in bounds (hPC_bound on successors)
    match checkBranchTargets p.code with
    | some err => .error s!"branch target check failed: {err}"
    | none =>
    let intervals := BoundsOpt.analyzeIntervals p
    let checkerOk := BoundsOpt.checkLocalPreservation p intervals && checkInvAtStart intervals
    -- Liveness analysis for call-site save/restore
    let liveOut := DAEOpt.analyzeLiveness p
    -- Pass 1: compute instruction lengths (pcMap- and label-independent).
    -- Internally instrLength uses dummy labels (`fun _ => 0` and `0 0 0`);
    -- verifiedGenInstr_length_params_ind bridges to the real labels used below.
    let lengths := (List.range p.code.size).map fun pc =>
      let instr := p.code.getD pc .halt
      let safe := isBoundsSafe checkerOk p.arrayDecls intervals pc instr
      instrLength layout p.arrayDecls safe instr varMap
    let lengthsArr := lengths.toArray
    -- Build real pcMap and reverse map
    let pcMap := buildPcMap lengthsArr
    let tacPcOf := buildTacPcOf lengthsArr
    -- Halt-save block: spill register-allocated observable values to stack.
    -- Lives at the end of bodyFlat (inside the verified region).
    let haltSaveBlockList := genHaltSave p.observable layout varMap
    -- Sentinel PCs: haltS = start of halt-save block, haltFinal = end of bodyFlat,
    -- divS/boundsS are off-the-end (stuck in ARM).
    let bodyInstrSize := pcMap p.code.size
    let haltS := bodyInstrSize
    let haltFinal := bodyInstrSize + haltSaveBlockList.length
    let divS := haltFinal + 1
    let boundsS := haltFinal + 2
    -- Generate init code
    let initInstrs := genInitCode vars layout
    -- Pass 2: generate instructions with real pcMap and real labels.
    -- For library call sites, wrap with save/restore of live caller-saved registers.
    let bodyResult := (List.range p.code.size).foldl
        (bodyGenStep p.code layout pcMap liveOut varMap checkerOk intervals p.arrayDecls haltS divS boundsS tyCtx)
        (some (Array.mkEmpty p.code.size))
    match bodyResult with
    | none => .error "verifiedGenInstr failed (layout or type mismatch)"
    | some bodyPerPC =>
    -- Callee-saved register prologue/epilogue
    let (csIntRegs, csFloatRegs) := detectCalleeSavedLayout layout
    let calleeSaveOffset := (vars.length + 1) * 8  -- right after variable slots
    let (csPrologue, csEpilogue) := genVerifiedCalleeSave csIntRegs csFloatRegs calleeSaveOffset
    .ok {
      initInstrs := initInstrs.toArray
      bodyPerPC := bodyPerPC
      haltSaveBlock := haltSaveBlockList.toArray
      pcMap := pcMap
      layout := layout
      varMap := varMap
      initLen := initInstrs.length
      haltS := haltS
      haltFinal := haltFinal
      divS := divS
      boundsS := boundsS
      tacPcOf := tacPcOf
      calleeSavePrologue := csPrologue
      calleeSaveEpilogue := csEpilogue
      calleeSaveRegs := (csIntRegs, csFloatRegs)
    }

-- ============================================================
-- § 5a. Whole-program refinement
-- ============================================================

/-!
## Whole-program refinement

Lifts the per-instruction `ext_backward_simulation` from ArmCorrectness.lean
to a multi-step simulation over `verifiedGenerateAsm`.

**Theorem statement.** If `verifiedGenerateAsm p = .ok r`, then any TAC
execution `p ⊩ Cfg.run pc σ am ⟶* cfg'` starting from an ARM state satisfying
`ExtSimRel` is simulated by `ArmSteps` preserving `ExtSimRel`.

**Known sorrys that propagate:**
- 0 sorrys from `verifiedGenInstr_correct` (arrLoad bool case closed)
-/

/-- The flat ARM body: per-PC instruction lists concatenated, followed by the
    halt-save block (written by a `.halt` TAC to spill observable values). -/
def VerifiedAsmResult.bodyFlat (r : VerifiedAsmResult) : ArmProg :=
  ((r.bodyPerPC.toList.flatMap id) ++ r.haltSaveBlock.toList).toArray

/-- The canonical zero-initialized ARM entry state: all registers and stack
    cleared, PC at the start of the bodyFlat (`pcMap 0`), flags zeroed.
    This is the state from which all backward correctness theorems begin
    their ARM trace. -/
def VerifiedAsmResult.initArmState (r : VerifiedAsmResult) : ArmState :=
  { regs := fun _ => 0, fregs := fun _ => 0, stack := fun _ => 0,
    pc := r.pcMap 0, flags := ⟨0, 0⟩ }

/-- Properties extracted from a successful `verifiedGenerateAsm` call.
    These are the invariants that the main code-generation function establishes
    via its runtime checks (type check, layout check, branch target check). -/
structure GenAsmSpec (tyCtx : TyCtx) (p : Prog) (r : VerifiedAsmResult) : Prop where
  /-- The program is well-typed under the given TyCtx. -/
  wellTypedProg : WellTypedProg tyCtx p
  /-- The layout respects types: float vars in fregs, non-float in iregs/stack. -/
  wellTypedLayout : WellTypedLayout tyCtx r.layout
  /-- No variable is mapped to a restricted register (scratch or reserved). -/
  regConventionSafe : RegConventionSafe r.layout
  /-- No two variables share a register/stack location. -/
  injective : VarLayoutInjective r.layout
  /-- The layout passed `verifiedGenerateAsm`'s executable `regConventionSafe`/`isInjective`
      checks.  These `Bool` facts are needed now that the per-instruction validity guard was
      hoisted out of `verifiedGenInstr`: the correctness lemmas take them as hypotheses. -/
  regConventionSafeBool : r.layout.regConventionSafe = true
  isInjectiveBool : r.layout.isInjective = true
  /-- bodyPerPC has one entry per TAC instruction. -/
  bodySize : r.bodyPerPC.size = p.size
  /-- Each non-print, non-lib-call bodyPerPC entry was produced by verifiedGenInstr
      with `boundsSafe = verifiedBoundsSafe p pc`. Phase 6 is live: `verifiedBoundsSafe`
      computes a real per-PC elision decision from `BoundsOpt` interval analysis +
      `checkLocalPreservation`/`checkInvAtStart`, so provably-in-bounds `arrLoad`/
      `arrStore` checks are dropped (and `hBoundsSafeOracle` is discharged from that
      decision, not vacuously). Print PCs use unverified codegen; lib-call PCs are
      wrapped (see callSiteSaveRestore). -/
  instrGen : ∀ pc, (hpc : pc < p.size) →
    isLibCallTAC p[pc] = false →
    (∀ fmt vs, p[pc] ≠ .print fmt vs) →
      verifiedGenInstr r.layout r.pcMap p[pc]
        r.haltS r.divS r.boundsS p.arrayDecls (verifiedBoundsSafe p pc) =
      some (r.bodyPerPC[pc]'(bodySize ▸ hpc))
  /-- pcMap is the prefix sum of bodyPerPC lengths. -/
  pcMapLengths : ∃ lengths : Array Nat,
    lengths.size = r.bodyPerPC.size ∧
    r.pcMap = buildPcMap lengths ∧
    ∀ (i : Nat) (hL : i < lengths.size) (hB : i < r.bodyPerPC.size),
      lengths[i] = (r.bodyPerPC[i]).length
  /-- Every variable referenced by an instruction has a layout entry. -/
  layoutComplete : ∀ pc (hpc : pc < p.size), ∀ v, v ∈ (p[pc]).vars → r.layout v ≠ none
  /-- At library call sites, bodyPerPC wraps verifiedGenInstr output with
      save/restore of caller-saved registers excluding the destination
      (via callerSaveEntries). -/
  callSiteSaveRestore : ∀ pc (hpc : pc < p.size),
    isLibCallTAC p[pc] = true →
    ∃ baseInstrs,
      verifiedGenInstr r.layout r.pcMap p[pc]
        r.haltS r.divS r.boundsS p.arrayDecls (verifiedBoundsSafe p pc) =
        some baseInstrs ∧
      r.bodyPerPC[pc]'(bodySize ▸ hpc) =
        entriesToSaves (callerSaveEntries r.layout r.varMap (DAEOpt.instrDef p[pc])) ++
        baseInstrs ++
        entriesToRestores (callerSaveEntries r.layout r.varMap (DAEOpt.instrDef p[pc]))
  /-- At print sites, bodyPerPC = entriesToSaves entries ++ [printCall _] ++ entriesToRestores entries
      where entries = genCallerSaveAll layout varMap. -/
  printSaveRestore : ∀ pc (hpc : pc < p.size),
    (∃ fmt vs, p[pc] = .print fmt vs) →
    ∃ lines,
      r.bodyPerPC[pc]'(bodySize ▸ hpc) =
        entriesToSaves (genCallerSaveAll r.layout r.varMap) ++
        [ArmInstr.printCall lines] ++
        entriesToRestores (genCallerSaveAll r.layout r.varMap)
  /-- The entries from genCallerSaveAll satisfy all callerSave_composition hypotheses. -/
  callerSaveSpec :
    let entries := genCallerSaveAll r.layout r.varMap
    (∀ e ∈ entries, ∀ v, r.layout v ≠ some (.stack e.off)) ∧
    (entries.map CallerSaveEntry.off).Nodup ∧
    (∀ v ir, r.layout v = some (.ireg ir) → ir.isCallerSaved = true →
      ∃ off, CallerSaveEntry.ireg ir off ∈ entries) ∧
    (∀ v fr, r.layout v = some (.freg fr) → fr.isCallerSaved = true →
      ∃ off, CallerSaveEntry.freg fr off ∈ entries) ∧
    (∀ ir off1 off2, CallerSaveEntry.ireg ir off1 ∈ entries →
      CallerSaveEntry.ireg ir off2 ∈ entries → off1 = off2) ∧
    (∀ fr off1 off2, CallerSaveEntry.freg fr off1 ∈ entries →
      CallerSaveEntry.freg fr off2 ∈ entries → off1 = off2)
  /-- haltS equals the total length of per-PC instructions = pcMap p.size.
      The halt-save block starts here in bodyFlat. -/
  haltS_eq : r.haltS = (r.bodyPerPC.toList.flatMap id).length
  /-- haltFinal = haltS + |haltSaveBlock| = bodyFlat.size.
      Reaching this PC means the program halted cleanly. -/
  haltFinal_eq : r.haltFinal = r.haltS + r.haltSaveBlock.size
  /-- divS is one past haltFinal: off-the-end, stuck in ARM. -/
  divS_eq : r.divS = r.haltFinal + 1
  /-- boundsS is two past haltFinal: also off-the-end, stuck in ARM. -/
  boundsS_eq : r.boundsS = r.haltFinal + 2
  /-- The halt-save block equals `genHaltSave p.observable layout varMap`. -/
  haltSaveBlock_eq : r.haltSaveBlock.toList = genHaltSave p.observable r.layout r.varMap
  /-- Every observable has a layout assignment compatible with `genHaltSaveOne`:
      register-allocated vars (ireg/freg) have a varMap stack slot for the
      save target; stack-allocated vars trivially satisfy the contract.
      This rules out the silent-drop cases of `genHaltSaveOne`. -/
  haltSaveComplete : ∀ v ∈ p.observable,
    (∃ ir off, r.layout v = some (.ireg ir) ∧ lookupVar r.varMap v = some off) ∨
    (∃ fr off, r.layout v = some (.freg fr) ∧ lookupVar r.varMap v = some off) ∨
    (∃ off, r.layout v = some (.stack off))
  /-- `varMap` offsets are injective: two variables sharing a stack slot are equal.
      Follows from `buildVarMap_offsets_nodup`. -/
  varMapInjOnOffsets : ∀ v w off,
    lookupVar r.varMap v = some off → lookupVar r.varMap w = some off → v = w
  /-- Stack-allocated layout offsets come from `varMap` (the ireg/freg/stack
      branches of `buildVarLayout`'s filterMap use `lookupVar varMap` as the
      stack fallback). Needed for the halt-save freshness argument: a write
      to `stack[varMap v]` (v ireg/freg) cannot clobber a stack-resident w's
      slot, because otherwise `varMap v = varMap w` would force `v = w`
      via `varMapInjOnOffsets`, contradicting the ireg/stack split. -/
  layoutStackComesFromVarMap : ∀ v off,
    r.layout v = some (.stack off) → lookupVar r.varMap v = some off
  /-- Phase 4 (validated interval analysis): the validated interval-
      based invariant map on `p` is preserved under `p`'s small-step
      semantics. `buildVerifiedInvMap p` runs `BoundsOpt.analyzeIntervals p`
      (untrusted oracle) and validates its per-PC local-preservation claim
      via `BoundsOpt.checkLocalPreservation`. If the checker rejects (or the
      entry-PC claim isn't trivially satisfiable), the map falls back to the
      constant `True` invariant. Either way, preservation holds. Load-bearing
      for Phase 5, which lifts this via `inv_preserved_steps` to derive a
      reachable-state invariant at the arrLoad/arrStore bounds-error arms. -/
  invPreserved : (buildVerifiedInvMap p).preserved p
  /-- The validated invariant holds trivially at the entry PC for every
      initial store and array memory. On the checker-accepted path this is
      `IMap.satisfies [] σ` (vacuous over an empty `IMap`) or a PC-0-out-of-
      bounds fallthrough to `True`; on the fallback path the map is `True`
      everywhere. Required so `inv_preserved_steps` can feed a base case at
      pc=0 (Phase 5). -/
  invAtStart : ∀ σ am, buildVerifiedInvMap p 0 σ am

-- checkWellTypedLayout_wellTyped: imported from CodeGenLayout.lean

/-- Foldl that appends preserves existing elements. -/
private theorem foldl_preserves_mem {init : List Var} {instrs : List TAC} {v : Var}
    (hv : v ∈ init) :
    v ∈ instrs.foldl (fun acc i =>
      acc ++ (TAC.vars i).filter fun w => !acc.contains w) init := by
  induction instrs generalizing init with
  | nil => exact hv
  | cons _ tl ih => simp only [List.foldl]; exact ih (List.mem_append_left _ hv)

/-- The foldl in checkWellTypedLayout collects all TAC.vars from all instructions. -/
private theorem foldl_collects (instrs : List TAC) (v : Var) (instr : TAC)
    (hMem : instr ∈ instrs) (hv : v ∈ TAC.vars instr) :
    v ∈ instrs.foldl (init := ([] : List Var)) fun acc i =>
      acc ++ (TAC.vars i).filter fun w => !acc.contains w := by
  suffices ∀ (init : List Var),
      v ∈ instrs.foldl (fun acc i =>
        acc ++ (TAC.vars i).filter fun w => !acc.contains w) init from this []
  intro init
  induction instrs generalizing init with
  | nil => simp at hMem
  | cons hd tl ih =>
    simp only [List.foldl]
    rcases List.mem_cons.mp hMem with rfl | htl
    · apply foldl_preserves_mem
      by_cases hmem : v ∈ init
      · exact List.mem_append_left _ hmem
      · apply List.mem_append_right
        rw [List.mem_filter]
        exact ⟨hv, by simp [hmem]⟩
    · exact ih htl _

/-- checkWellTypedLayout returning none implies all TAC.vars are in the layout. -/
private theorem checkWellTypedLayout_instrMapped {Γ : TyCtx} {layout : VarLayout}
    {code : Array TAC}
    (h : checkWellTypedLayout Γ layout code = none)
    {pc : Nat} (hpc : pc < code.size) {v : Var}
    (hv : v ∈ TAC.vars code[pc]) : layout v ≠ none := by
  simp only [checkWellTypedLayout] at h
  split at h
  · simp at h
  · rename_i hTypeOk
    split at h
    · simp at h
    · rename_i hComplete
      intro hNone
      have hInAll : v ∈ code.foldl (init := ([] : List Var)) fun acc instr =>
          acc ++ (TAC.vars instr).filter fun w => !acc.contains w := by
        rw [← Array.foldl_toList]
        exact foldl_collects code.toList v code[pc] (Array.getElem_mem_toList hpc) hv
      have := (List.find?_eq_none.mp hComplete) v hInAll
      simp [Option.isNone, hNone] at this

private theorem Array.push_inj {a : Array α} {x y : α} (h : a.push x = a.push y) : x = y := by
  have := congrArg (·[a.size]?) h; simp at this; exact this

/-- A foldl over `List.range n` that propagates `none` and pushes exactly one
    element per successful `some` step produces an array of size `n`. -/
private theorem foldl_push_size
    {n : Nat} {res : Array α}
    {F : Option (Array α) → Nat → Option (Array α)}
    (hNone : ∀ pc, F none pc = none)
    (hPush : ∀ arr pc, F (some arr) pc = none ∨ ∃ x, F (some arr) pc = some (arr.push x))
    (hFold : (List.range n).foldl F (some #[]) = some res) :
    res.size = n := by
  suffices key : ∀ (m : Nat) (initArr res : Array α),
      (List.range m).foldl F (some initArr) = some res →
      res.size = initArr.size + m by
    have := key n #[] res hFold; simp at this; exact this
  intro m
  induction m with
  | zero =>
    intro initArr res hEq; simp at hEq; subst hEq; omega
  | succ k ih =>
    intro initArr res hEq
    simp only [List.range_succ, List.foldl_append, List.foldl] at hEq
    generalize hMid : (List.range k).foldl F (some initArr) = midResult at hEq
    match midResult with
    | none => rw [hNone] at hEq; simp at hEq
    | some midArr =>
      have hMidSz := ih initArr midArr hMid
      rcases hPush midArr k with hFail | ⟨x, hP⟩
      · rw [hFail] at hEq; simp at hEq
      · rw [hP] at hEq; simp at hEq; subst hEq
        simp [Array.size_push, hMidSz]; omega

/-- A foldl that propagates `none` and pushes one element per step:
    for each index `pc < res.size`, there exists an intermediate array `mid`
    of size `pc` such that `F (some mid) pc = some (mid.push res[pc])`. -/
private theorem foldl_push_content
    {n : Nat} {res : Array α}
    {F : Option (Array α) → Nat → Option (Array α)}
    (hNone : ∀ pc, F none pc = none)
    (hPush : ∀ arr pc, F (some arr) pc = none ∨ ∃ x, F (some arr) pc = some (arr.push x))
    (hFold : (List.range n).foldl F (some #[]) = some res)
    (pc : Nat) (hpc : pc < res.size) :
    ∃ mid : Array α, mid.size = pc ∧
      F (some mid) pc = some (mid.push res[pc]) := by
  have hResSz : res.size = n := foldl_push_size hNone hPush hFold
  -- Generalized: for foldl over range m starting from initArr
  suffices key : ∀ (m : Nat) (initArr midRes : Array α),
      (List.range m).foldl F (some initArr) = some midRes →
      midRes.size = initArr.size + m →
      ∀ k, k < m → (hk : initArr.size + k < midRes.size) →
        ∃ mid : Array α, mid.size = initArr.size + k ∧
          F (some mid) k = some (mid.push midRes[initArr.size + k]) by
    have := key n #[] res hFold (by simp; exact hResSz) pc (by omega) (by simp; exact hpc)
    simpa using this
  intro m
  induction m with
  | zero => intro _ _ _ _ k hk; omega
  | succ j ih =>
    intro initArr midRes hEq hSz k hk hkBound
    simp only [List.range_succ, List.foldl_append, List.foldl] at hEq
    generalize hMid : (List.range j).foldl F (some initArr) = midResult at hEq
    match midResult with
    | none => rw [hNone] at hEq; simp at hEq
    | some midArr =>
      -- Get midArr size by the same foldl_push_size argument
      have hMidSz : midArr.size = initArr.size + j := by
        clear ih hEq hSz hk hkBound
        revert initArr midArr hMid
        induction j with
        | zero => intro i r h; simp at h; subst h; omega
        | succ j' ihj =>
          intro initArr midArr hEq
          simp only [List.range_succ, List.foldl_append, List.foldl] at hEq
          generalize hM : (List.range j').foldl F (some initArr) = mr at hEq
          match mr with
          | none => rw [hNone] at hEq; simp at hEq
          | some ma =>
            rcases hPush ma j' with hF | ⟨x, hP⟩
            · rw [hF] at hEq; simp at hEq
            · rw [hP] at hEq; simp at hEq; subst hEq
              simp [Array.size_push, ihj initArr ma hM]; omega
      rcases hPush midArr j with hFail | ⟨x, hP⟩
      · rw [hFail] at hEq; simp at hEq
      · rw [hP] at hEq; simp at hEq; subst hEq
        by_cases hkj : k = j
        · -- k = j: the element just pushed
          subst hkj
          have hNotLt : ¬ (initArr.size + k < midArr.size) := by omega
          simp only [Array.getElem_push, hNotLt, dite_false]
          exact ⟨midArr, hMidSz, hP⟩
        · -- k < j: use IH, element preserved by push
          have hkLt : k < j := by omega
          have hIdxLt : initArr.size + k < midArr.size := by omega
          have hPrevSz : midArr.size = initArr.size + j := hMidSz
          have ⟨mid, hMidSz', hStep⟩ := ih initArr midArr hMid hPrevSz k hkLt (by omega)
          refine ⟨mid, hMidSz', ?_⟩
          simp only [Array.getElem_push, hIdxLt, dite_true] at hStep ⊢
          exact hStep

-- ──────────────────────────────────────────────────────────────
-- bodyGenStep properties
-- ──────────────────────────────────────────────────────────────

@[simp] theorem bodyGenStep_none (code : Array TAC) (layout : VarLayout)
    (pcMap : Nat → Nat) (liveOut : Array (List Var))
    (varMap : List (Var × Nat)) (checkerOk : Bool)
    (intervals : Array (Option BoundsOpt.IMap))
    (arrayDecls : List (ArrayName × Nat × VarTy))
    (haltS divS boundsS : Nat) (tyCtx : TyCtx) (pc : Nat) :
    bodyGenStep code layout pcMap liveOut varMap checkerOk intervals arrayDecls
      haltS divS boundsS tyCtx none pc = none := rfl

theorem bodyGenStep_push (code : Array TAC) (layout : VarLayout)
    (pcMap : Nat → Nat) (liveOut : Array (List Var))
    (varMap : List (Var × Nat)) (checkerOk : Bool)
    (intervals : Array (Option BoundsOpt.IMap))
    (arrayDecls : List (ArrayName × Nat × VarTy))
    (haltS divS boundsS : Nat) (tyCtx : TyCtx) (arr : Array (List ArmInstr)) (pc : Nat) :
    bodyGenStep code layout pcMap liveOut varMap checkerOk intervals arrayDecls
      haltS divS boundsS tyCtx (some arr) pc = none ∨
    ∃ instrs, bodyGenStep code layout pcMap liveOut varMap checkerOk intervals arrayDecls
      haltS divS boundsS tyCtx (some arr) pc = some (arr.push instrs) := by
  simp only [bodyGenStep]
  split <;> split <;> simp_all <;>
    first
    | exact ⟨_, rfl⟩
    | (generalize verifiedGenInstr layout pcMap _ haltS divS boundsS arrayDecls _ = r
       cases r with
       | none => exact Or.inl rfl
       | some instrs => exact Or.inr ⟨_, rfl⟩)

/-- `verifiedGenInstr` output length is independent of pcMap.
    For goto/ifgoto, pcMap changes values but not list length.
    For all other instructions, pcMap is unused so `simp` normalizes to identical terms. -/
private theorem verifiedGenInstr_length_pcMap_indep {layout : VarLayout}
    {pcMap₁ pcMap₂ : Nat → Nat} {instr : TAC}
    {haltS divS boundsS : Nat} {arrayDecls : List (ArrayName × Nat × VarTy)}
    {safe : Bool} {l₁ l₂ : List ArmInstr}
    (h₁ : verifiedGenInstr layout pcMap₁ instr haltS divS boundsS arrayDecls safe = some l₁)
    (h₂ : verifiedGenInstr layout pcMap₂ instr haltS divS boundsS arrayDecls safe = some l₂) :
    l₁.length = l₂.length := by
  cases instr with
  | goto l =>
    simp only [verifiedGenInstr, Option.some.injEq] at h₁ h₂ <;> subst_vars <;> rfl
  | ifgoto be l =>
    simp only [verifiedGenInstr] at h₁ h₂
    split at h₁ <;> simp_all
    -- Lists differ only in pcMap inside one instruction; length is identical
    all_goals (split at h₁ <;> split at h₂ <;> simp_all
               <;> (try (obtain ⟨_, rfl⟩ := h₁; obtain ⟨_, rfl⟩ := h₂; simp [List.length_append]))
               <;> (try (subst_vars; obtain ⟨_, rfl⟩ := h₂; simp [List.length_append])))
  | const _ val =>
    have : some l₁ = some l₂ := by rw [← h₁, ← h₂]; cases val <;> simp [verifiedGenInstr]
    exact congrArg _ (Option.some.inj this)
  | copy _ _ | binop _ _ _ _ | boolop _ _ | halt
  | arrLoad _ _ _ _ | arrStore _ _ _ _ | fbinop _ _ _ _
  | intToFloat _ _ | floatToInt _ _ | floatUnary _ _ _ | fternop _ _ _ _ _ =>
    have : some l₁ = some l₂ := by rw [← h₁, ← h₂]; simp [verifiedGenInstr]
    exact congrArg _ (Option.some.inj this)
  | print _ _ => simp [verifiedGenInstr] at h₁
  | printInt v =>
    simp only [verifiedGenInstr] at h₁ h₂
    split at h₁ <;> simp_all <;> split at h₂ <;> simp_all
  | printBool v =>
    simp only [verifiedGenInstr] at h₁ h₂
    split at h₁ <;> simp_all <;> split at h₂ <;> simp_all
  | printFloat v =>
    simp only [verifiedGenInstr] at h₁ h₂
    split at h₁ <;> simp_all <;> split at h₂ <;> simp_all
  | printString lit =>
    simp only [verifiedGenInstr] at h₁ h₂
    simp_all

/-- instrLength equals the length of the generated instruction list (including
    save/restore wrapping at call sites). -/
private theorem instrLength_eq_length {layout : VarLayout} {pcMap : Nat → Nat} {instr : TAC}
    {haltS divS boundsS : Nat} {arrayDecls : List (ArrayName × Nat × VarTy)}
    {safe : Bool} {instrs : List ArmInstr}
    {varMap : List (Var × Nat)}
    (h : verifiedGenInstr layout pcMap instr haltS divS boundsS arrayDecls safe = some instrs) :
    instrLength layout arrayDecls safe instr varMap =
      (if isLibCallTAC instr then
        let entries := callerSaveEntries layout varMap (DAEOpt.instrDef instr)
        (entriesToSaves entries ++ instrs ++ entriesToRestores entries).length
      else instrs.length) := by
  -- Print case: verifiedGenInstr returns none, contradicting h
  -- Non-print: instrLength uses dummy pcMap (fun _ => 0) and dummy labels (0);
  -- equate lengths via pcMap- AND labels-independence.
  cases instr with
  | print => simp [verifiedGenInstr] at h
  | printInt v =>
    simp only [instrLength, isLibCallTAC, callSaveRestoreLen, callerSaveEntries, DAEOpt.instrDef]
    generalize hd : verifiedGenInstr layout (fun _ => 0)
      (.printInt v) 0 0 0 arrayDecls safe = dr
    cases dr with
    | none =>
      simp only [verifiedGenInstr] at h hd
      split at hd <;> simp_all <;> split at h <;> simp_all
    | some dl =>
      have hLen := verifiedGenInstr_length_params_ind layout (.printInt v)
        (fun _ => 0) pcMap 0 0 0 haltS divS boundsS arrayDecls safe dl instrs hd h
      simp only [hLen, List.length_append, entriesToSaves_length, entriesToRestores_length]
      simp [Nat.add_comm, Nat.add_left_comm]
  | printBool v =>
    simp only [instrLength, isLibCallTAC, callSaveRestoreLen, callerSaveEntries, DAEOpt.instrDef]
    generalize hd : verifiedGenInstr layout (fun _ => 0)
      (.printBool v) 0 0 0 arrayDecls safe = dr
    cases dr with
    | none =>
      simp only [verifiedGenInstr] at h hd
      split at hd <;> simp_all <;> split at h <;> simp_all
    | some dl =>
      have hLen := verifiedGenInstr_length_params_ind layout (.printBool v)
        (fun _ => 0) pcMap 0 0 0 haltS divS boundsS arrayDecls safe dl instrs hd h
      simp only [hLen, List.length_append, entriesToSaves_length, entriesToRestores_length]
      simp [Nat.add_comm, Nat.add_left_comm]
  | printFloat v =>
    simp only [instrLength, isLibCallTAC, callSaveRestoreLen, callerSaveEntries, DAEOpt.instrDef]
    generalize hd : verifiedGenInstr layout (fun _ => 0)
      (.printFloat v) 0 0 0 arrayDecls safe = dr
    cases dr with
    | none =>
      simp only [verifiedGenInstr] at h hd
      split at hd <;> simp_all <;> split at h <;> simp_all
    | some dl =>
      have hLen := verifiedGenInstr_length_params_ind layout (.printFloat v)
        (fun _ => 0) pcMap 0 0 0 haltS divS boundsS arrayDecls safe dl instrs hd h
      simp only [hLen, List.length_append, entriesToSaves_length, entriesToRestores_length]
      simp [Nat.add_comm, Nat.add_left_comm]
  | printString lit =>
    simp only [instrLength, isLibCallTAC, callSaveRestoreLen, callerSaveEntries, DAEOpt.instrDef,
               verifiedGenInstr] at h ⊢
    simp_all [List.length_append, entriesToSaves_length, entriesToRestores_length,
              Nat.add_comm, Nat.add_left_comm]
  | const v val =>
    simp only [instrLength, isLibCallTAC, verifiedGenInstr] at *
    cases val <;> simp_all <;> split at h <;> simp_all
  | copy dst src =>
    simp only [instrLength, isLibCallTAC, verifiedGenInstr] at *
    split at h <;> simp_all
  | binop x op y z =>
    simp only [instrLength, isLibCallTAC]
    generalize hd : verifiedGenInstr layout (fun _ => 0)
      (.binop x op y z) 0 0 0 arrayDecls safe = dr
    cases dr with
    | none =>
      -- Failure of verifiedGenInstr for .binop depends only on layout (freg checks).
      simp only [verifiedGenInstr] at h hd
      split at hd <;> simp_all <;> split at h <;> simp_all
    | some dl =>
      have hLen := verifiedGenInstr_length_params_ind layout (.binop x op y z)
        (fun _ => 0) pcMap 0 0 0 haltS divS boundsS arrayDecls safe dl instrs hd h
      simp [hLen]
  | boolop x be =>
    simp only [instrLength, isLibCallTAC, verifiedGenInstr] at *
    split at h <;> simp_all
  | goto l =>
    simp only [instrLength, isLibCallTAC, verifiedGenInstr, Option.some.injEq] at *
    subst_vars; rfl
  | ifgoto be l =>
    simp only [instrLength, isLibCallTAC]
    generalize hd : verifiedGenInstr layout (fun _ => 0)
      (.ifgoto be l) 0 0 0 arrayDecls safe = dr
    cases dr with
    | none =>
      simp only [verifiedGenInstr] at h hd
      split at hd <;> simp_all <;> split at h <;> simp_all
    | some dl =>
      have hLen := verifiedGenInstr_length_params_ind layout (.ifgoto be l)
        (fun _ => 0) pcMap 0 0 0 haltS divS boundsS arrayDecls safe dl instrs hd h
      simp [hLen]
  | halt =>
    simp only [instrLength, isLibCallTAC]
    generalize hd : verifiedGenInstr layout (fun _ => 0)
      (TAC.halt) 0 0 0 arrayDecls safe = dr
    cases dr with
    | none =>
      simp only [verifiedGenInstr] at h hd
      simp_all
    | some dl =>
      have hLen := verifiedGenInstr_length_params_ind layout TAC.halt
        (fun _ => 0) pcMap 0 0 0 haltS divS boundsS arrayDecls safe dl instrs hd h
      simp [hLen]
  | arrLoad x arr idx ty =>
    simp only [instrLength, isLibCallTAC]
    generalize hd : verifiedGenInstr layout (fun _ => 0)
      (.arrLoad x arr idx ty) 0 0 0 arrayDecls safe = dr
    cases dr with
    | none =>
      simp only [verifiedGenInstr] at h hd
      split at hd <;> simp_all <;> split at h <;> simp_all
    | some dl =>
      have hLen := verifiedGenInstr_length_params_ind layout (.arrLoad x arr idx ty)
        (fun _ => 0) pcMap 0 0 0 haltS divS boundsS arrayDecls safe dl instrs hd h
      simp [hLen]
  | arrStore arr idx val ty =>
    simp only [instrLength, isLibCallTAC]
    generalize hd : verifiedGenInstr layout (fun _ => 0)
      (.arrStore arr idx val ty) 0 0 0 arrayDecls safe = dr
    cases dr with
    | none =>
      simp only [verifiedGenInstr] at h hd
      split at hd <;> simp_all <;> split at h <;> simp_all
    | some dl =>
      have hLen := verifiedGenInstr_length_params_ind layout (.arrStore arr idx val ty)
        (fun _ => 0) pcMap 0 0 0 haltS divS boundsS arrayDecls safe dl instrs hd h
      simp [hLen]
  | fbinop x fop y z =>
    simp only [instrLength, isLibCallTAC, callSaveRestoreLen, callerSaveEntries, DAEOpt.instrDef]
    generalize hd : verifiedGenInstr layout (fun _ => 0)
      (.fbinop x fop y z) 0 0 0 arrayDecls safe = dr
    cases dr with
    | none =>
      simp only [verifiedGenInstr] at h hd
      split at hd <;> simp_all <;> split at h <;> simp_all
    | some dl =>
      have hLen := verifiedGenInstr_length_params_ind layout (.fbinop x fop y z)
        (fun _ => 0) pcMap 0 0 0 haltS divS boundsS arrayDecls safe dl instrs hd h
      simp only [hLen, List.length_append, entriesToSaves_length, entriesToRestores_length]
      cases fop <;> simp_all [Nat.add_comm] <;> omega
  | intToFloat x y =>
    simp only [instrLength, isLibCallTAC, verifiedGenInstr] at *
    split at h <;> simp_all
  | floatToInt x y =>
    simp only [instrLength, isLibCallTAC, verifiedGenInstr] at *
    split at h <;> simp_all
  | floatUnary x op y =>
    simp only [instrLength, isLibCallTAC, callSaveRestoreLen, callerSaveEntries, DAEOpt.instrDef]
    generalize hd : verifiedGenInstr layout (fun _ => 0)
      (.floatUnary x op y) 0 0 0 arrayDecls safe = dr
    cases dr with
    | none =>
      simp only [verifiedGenInstr] at h hd
      split at hd <;> simp_all <;> split at h <;> simp_all
    | some dl =>
      have hLen := verifiedGenInstr_length_params_ind layout (.floatUnary x op y)
        (fun _ => 0) pcMap 0 0 0 haltS divS boundsS arrayDecls safe dl instrs hd h
      simp only [hLen, List.length_append, entriesToSaves_length, entriesToRestores_length]
      cases op.isNative <;> simp_all [Nat.add_comm] <;> omega
  | fternop x op a b c =>
    simp only [instrLength, isLibCallTAC, verifiedGenInstr] at *
    split at h <;> simp_all


/-- The list pushed by `bodyGenStep` has length equal to `instrLength`. -/
private theorem bodyGenStep_length {code : Array TAC} {layout : VarLayout}
    {pcMap : Nat → Nat} {liveOut : Array (List Var)} {varMap : List (Var × Nat)}
    {checkerOk : Bool}
    {intervals : Array (Option BoundsOpt.IMap)}
    {arrayDecls : List (ArrayName × Nat × VarTy)}
    {haltS divS boundsS : Nat} {tyCtx : TyCtx}
    {arr : Array (List ArmInstr)} {pc : Nat}
    {instrs : List ArmInstr}
    (hStep : bodyGenStep code layout pcMap liveOut varMap checkerOk intervals arrayDecls
      haltS divS boundsS tyCtx (some arr) pc = some (arr.push instrs))
    (hpc : pc < code.size) :
    instrs.length = instrLength layout arrayDecls
      (isBoundsSafe checkerOk arrayDecls intervals pc (code.getD pc .halt))
      (code.getD pc .halt) varMap := by
  -- Normalize getD to getElem in goal
  have hGetD : code.getD pc .halt = code[pc] := by simp [Array.getD, hpc]
  rw [hGetD]
  -- Unfold bodyGenStep in hypothesis
  simp only [bodyGenStep, Array.getD, hpc, dite_true] at hStep
  -- Case split: print vs non-print (isPrint match)
  split at hStep
  · -- .print match
    rename_i fmt vs heq
    split at hStep
    · -- isPrint = true
      have heqI : code[pc] = TAC.print fmt vs := heq
      have := Array.push_inj (Option.some.inj hStep); subst this
      simp_all [instrLength, callSaveRestoreLen, callerSaveEntries, List.length_append]; omega
    · -- isPrint = false for .print: contradiction
      rename_i h; exact absurd rfl h
  · -- non-.print match
    rename_i heqPrint
    split at hStep
    · -- isPrint = true for non-print: contradiction
      rename_i h; simp at h
    · -- isPrint = false: the real non-print case
      simp at hStep
      split at hStep
      · simp at hStep  -- verifiedGenInstr = none: contradiction
      · rename_i armInstrs hGenInstr
        -- Use instrLength_eq_length to relate instrLength to verifiedGenInstr output
        rw [instrLength_eq_length hGenInstr]
        split at hStep
        · -- lib-call case
          rename_i hLib
          have hInstrs := Array.push_inj (Option.some.inj hStep)
          simp only [hLib, ite_true]; rw [← hInstrs]
          simp [List.length_append, entriesToSaves_length, entriesToRestores_length]
        · -- non-lib-call case
          rename_i hNotLib
          have hInstrs := Array.push_inj (Option.some.inj hStep)
          have hNotLib' : isLibCallTAC code[pc] = false := by
            cases h : isLibCallTAC code[pc] <;> simp_all
          simp [hNotLib', hInstrs]

-- `verifiedGenerateAsm_spec` moved after `buildPcMap_eq_take_length` and
-- `codeAt_of_bodyFlat'` to discharge the Phase-2 `haltS_eq` spec clause.

-- ──────────────────────────────────────────────────────────────
-- § 5b-pre. Helper lemmas for register convention bridge
-- ──────────────────────────────────────────────────────────────

-- String literal toList reductions (enable simp to reduce startsWithList for concrete prefixes)
@[simp] private theorem toList_ir : ("__ir" : String).toList = ['_', '_', 'i', 'r'] := rfl
@[simp] private theorem toList_br : ("__br" : String).toList = ['_', '_', 'b', 'r'] := rfl
@[simp] private theorem toList_fr : ("__fr" : String).toList = ['_', '_', 'f', 'r'] := rfl
@[simp] private theorem toList_t  : ("__t" : String).toList = ['_', '_', 't'] := rfl
@[simp] private theorem toList_ft : ("__ft" : String).toList = ['_', '_', 'f', 't'] := rfl
private theorem ts_t  : (toString "__t" : String) = "__t" := rfl
private theorem ts_ft : (toString "__ft" : String) = "__ft" := rfl

/-- Compiler int temps don't violate the register convention. -/
private theorem tmpName_not_violates (k : Nat) : violatesRegConvention (tmpName k) = false := by
  unfold violatesRegConvention startsWithList tmpName
  simp [String.toList_append, ts_t, List.isPrefixOf]

/-- Compiler float temps don't violate the register convention. -/
private theorem ftmpName_not_violates (k : Nat) : violatesRegConvention (ftmpName k) = false := by
  unfold violatesRegConvention startsWithList ftmpName
  simp [String.toList_append, ts_ft, List.isPrefixOf]

private theorem ts_bt : (toString "__bt" : String) = "__bt" := rfl

/-- Compiler bool temps don't violate the register convention. -/
private theorem btmpName_not_violates (k : Nat) : violatesRegConvention (btmpName k) = false := by
  unfold violatesRegConvention startsWithList btmpName
  simp [String.toList_append, ts_bt, List.isPrefixOf]
  rfl

/-- Variables without `__` prefix don't map to integer registers. -/
private theorem varToArmReg_none_of_not_dunder (v : Var) (h : startsWithList v "__" = false) :
    varToArmReg v = none := by
  have hir : startsWithList v "__ir" = false := by
    unfold startsWithList at *
    exact List.isPrefixOf_of_isPrefixOf_append "__".toList "ir".toList v.toList h
  have hbr : startsWithList v "__br" = false := by
    unfold startsWithList at *
    exact List.isPrefixOf_of_isPrefixOf_append "__".toList "br".toList v.toList h
  simp [varToArmReg, hir, hbr]

/-- Variables without `__` prefix don't map to float registers. -/
private theorem varToArmFReg_none_of_not_dunder (v : Var) (h : startsWithList v "__" = false) :
    varToArmFReg v = none := by
  have hfr : startsWithList v "__fr" = false := by
    unfold startsWithList at *
    exact List.isPrefixOf_of_isPrefixOf_append "__".toList "fr".toList v.toList h
  simp [varToArmFReg, hfr]

/-- If `varToArmReg v = some r` and `r` is a restricted register,
    then `violatesRegConvention v = true`. Contrapositive gives:
    pipeline passing → no restricted registers in layout. -/
private theorem varToArmReg_restricted_implies_violates {v : Var} {r : ArmReg}
    (hr : varToArmReg v = some r)
    (hRestr : r = .x0 ∨ r = .x1 ∨ r = .x2 ∨ r = .x16 ∨ r = .x17 ∨ r = .x18) :
    violatesRegConvention v = true := by
  unfold varToArmReg at hr; unfold violatesRegConvention; dsimp only at *
  -- Both functions compute the same irN from __ir/__br prefix + toNat?
  -- Name the shared subexpression so split works across both
  generalize hN : (if startsWithList v "__ir" = true then (String.drop v 4).toNat?
    else if startsWithList v "__br" = true then (String.drop v 4).toNat?
    else none) = irN at hr ⊢
  -- Now split on irN — in hr it determines r, in goal it determines the result
  split at hr <;> (first
    | rfl -- restricted: match on concrete irN reduces to true = true
    | (rcases hRestr with h | h | h | h | h | h <;> (subst h; simp at hr)) -- non-restricted: contradiction
    | simp at hr) -- wildcard: none = some r

/-- If `varToArmFReg v = some r` and `r` is a restricted FP register,
    then `violatesRegConvention v = true`. -/
private theorem varToArmFReg_restricted_implies_violates {v : Var} {r : ArmFReg}
    (hr : varToArmFReg v = some r)
    (hRestr : r = .d0 ∨ r = .d1 ∨ r = .d2) :
    violatesRegConvention v = true := by
  unfold varToArmFReg at hr; unfold violatesRegConvention; dsimp only at *
  by_cases hfr : startsWithList v "__fr" = true
  · simp only [hfr, ↓reduceIte] at hr
    generalize (String.drop v 4).toNat? = n? at hr ⊢
    -- Also resolve the __ir/__br if-expressions in the goal
    by_cases hir : startsWithList v "__ir" = true <;>
      by_cases hbr : startsWithList v "__br" = true <;>
      simp only [hir, hbr, Bool.false_eq_true, ↓reduceIte, hfr] at ⊢ <;>
      (split at hr <;> (first
        | rfl
        | (rcases hRestr with h | h | h <;> (subst h; simp at hr))
        | simp at hr))
  · simp [hfr] at hr

-- ──────────────────────────────────────────────────────────────
-- § 5b-pre2. Helper lemmas for collectVars monotonicity
-- ──────────────────────────────────────────────────────────────

/-- The "add if not present" pattern preserves existing membership. -/
private theorem mem_of_mem_addIfNew {acc : List Var} {w v : Var}
    (hw : w ∈ acc) : w ∈ (if acc.contains v then acc else acc ++ [v]) := by
  split
  · exact hw
  · exact List.mem_append_left _ hw

/-- The "add if not present" pattern ensures the new element is a member. -/
private theorem self_mem_addIfNew {acc : List Var} {v : Var} :
    v ∈ (if acc.contains v then acc else acc ++ [v]) := by
  split
  · next h => exact List.contains_iff_mem.mp h
  · exact List.mem_append_right _ (List.mem_singleton.mpr rfl)

/-- Containment: addIfNew only adds from {v} ∪ acc. -/
private theorem mem_of_mem_addIfNew_imp {acc : List Var} {v w : Var}
    (hw : w ∈ (if acc.contains v then acc else acc ++ [v])) : w ∈ acc ∨ w = v := by
  split at hw
  · exact Or.inl hw
  · cases List.mem_append.mp hw with
    | inl h => exact Or.inl h
    | inr h => exact Or.inr (List.mem_singleton.mp h)

/-- Containment: foldl addIfNew only adds from vs ∪ acc. -/
private theorem mem_foldl_addIfNew_imp {acc vs : List Var} {w : Var}
    (hw : w ∈ vs.foldl (fun a v => if a.contains v then a else a ++ [v]) acc) :
    w ∈ acc ∨ w ∈ vs := by
  induction vs generalizing acc with
  | nil => exact Or.inl hw
  | cons v rest ih =>
    simp only [List.foldl_cons] at hw
    rcases ih hw with h | h
    · rcases mem_of_mem_addIfNew_imp h with h | rfl
      · exact Or.inl h
      · exact Or.inr (List.mem_cons.mpr (Or.inl rfl))
    · exact Or.inr (List.mem_cons_of_mem _ h)

/-- Folding "add if not present" over a list preserves existing membership. -/
private theorem mem_foldl_addIfNew_of_mem {acc vs : List Var} {w : Var}
    (hw : w ∈ acc) : w ∈ vs.foldl (fun a v => if a.contains v then a else a ++ [v]) acc := by
  induction vs generalizing acc with
  | nil => exact hw
  | cons v rest ih => exact ih (mem_of_mem_addIfNew hw)

/-- Folding "add if not present" over a list includes every element of that list. -/
private theorem mem_foldl_addIfNew_of_mem_list {acc vs : List Var} {w : Var}
    (hw : w ∈ vs) : w ∈ vs.foldl (fun a v => if a.contains v then a else a ++ [v]) acc := by
  induction vs generalizing acc with
  | nil => simp at hw
  | cons v rest ih =>
    simp only [List.foldl_cons]
    cases List.mem_cons.mp hw with
    | inl heq => subst heq; exact mem_foldl_addIfNew_of_mem self_mem_addIfNew
    | inr hmem => exact ih hmem

/-- `addIfNew` preserves `Nodup`. -/
private theorem addIfNew_nodup {acc : List Var} {v : Var} (h : acc.Nodup) :
    (if acc.contains v then acc else acc ++ [v]).Nodup := by
  split
  · exact h
  · rename_i hne
    have hv_notin : v ∉ acc := fun hm =>
      hne (List.contains_iff_mem.mpr hm)
    rw [List.nodup_append]
    refine ⟨h, List.Pairwise.cons (fun a hn => by simp at hn) List.Pairwise.nil, ?_⟩
    intro w hw x hxm hxw
    rcases List.mem_singleton.mp hxm with rfl
    exact hv_notin (hxw ▸ hw)

/-- `foldl addIfNew` preserves `Nodup`. -/
private theorem foldl_addIfNew_nodup (vs : List Var) {acc : List Var} (h : acc.Nodup) :
    (vs.foldl (fun a v => if a.contains v then a else a ++ [v]) acc).Nodup := by
  induction vs generalizing acc with
  | nil => exact h
  | cons v rest ih =>
    simp only [List.foldl_cons]
    exact ih (addIfNew_nodup h)

/-- Inner code-fold in `collectVars` preserves Nodup starting from any Nodup acc. -/
private theorem list_foldl_collect_code_nodup (l : List TAC) {acc : List Var}
    (h : acc.Nodup) :
    (l.foldl (fun acc instr =>
      (TAC.vars instr).foldl (fun a v => if a.contains v then a else a ++ [v]) acc) acc).Nodup := by
  induction l generalizing acc with
  | nil => exact h
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    exact ih (foldl_addIfNew_nodup _ h)

/-- `collectVars p` has no duplicates. -/
private theorem collectVars_nodup (p : Prog) : (collectVars p).Nodup := by
  unfold collectVars
  apply foldl_addIfNew_nodup
  rw [← Array.foldl_toList]
  exact list_foldl_collect_code_nodup _ List.nodup_nil

-- ──────────────────────────────────────────────────────────────
-- § 5b. Totality: verifiedGenerateAsm succeeds for pipeline output
-- ──────────────────────────────────────────────────────────────

/-- If `(v, off) ∈ l`, then `lookupVar l v` returns some value. -/
private theorem lookupVar_of_mem_pair {l : List (Var × Nat)} {v : Var} {off : Nat}
    (h : (v, off) ∈ l) : ∃ n, lookupVar l v = some n := by
  unfold lookupVar
  induction l with
  | nil => simp at h
  | cons hd tl ih =>
    simp only [List.find?]
    split
    · exact ⟨_, rfl⟩
    · rename_i hp
      cases h with
      | head => simp [BEq.beq] at hp
      | tail _ htl => exact ih htl

/-- `List.map Prod.snd` on a zip with `List.range` recovers the original list
    (when the range is at least as long). -/
private theorem map_snd_zip_range (vars : List Var) :
    ((List.range vars.length).zip vars).map Prod.snd = vars := by
  induction vars with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.length_cons]
    rw [List.range_succ_eq_map, List.zip_cons_cons, List.map_cons]
    congr 1
    rw [List.zip_map_left, List.map_map]
    have : Prod.snd ∘ Prod.map Nat.succ id = @Prod.snd Nat Var := by ext ⟨_, _⟩; rfl
    rw [this]; exact ih

/-- The first components of `buildVarMap vars` are exactly `vars`. -/
private theorem buildVarMap_map_fst (vars : List Var) :
    (buildVarMap vars).map Prod.fst = vars := by
  unfold buildVarMap
  simp only [List.map_map]
  have : (Prod.fst ∘ fun (x : Nat × Var) => (x.2, (x.1 + 1) * 8)) = Prod.snd := by ext ⟨_, _⟩; rfl
  rw [this]
  exact map_snd_zip_range vars

private theorem fst_mem_of_mem_buildVarMap {vars : List Var} {v : Var}
    (hv : v ∈ vars) : ∃ off, (v, off) ∈ buildVarMap vars := by
  have hmem : v ∈ (buildVarMap vars).map Prod.fst := by
    rw [buildVarMap_map_fst]; exact hv
  obtain ⟨⟨x, off⟩, hmem', hfst⟩ := List.mem_map.mp hmem
  exact ⟨off, by simp at hfst; rw [← hfst]; exact hmem'⟩

/-- `lookupVar` succeeds for any variable that appears in the list used to build the map. -/
private theorem lookupVar_of_mem {vars : List Var} {v : Var}
    (hv : v ∈ vars) :
    ∃ off, lookupVar (buildVarMap vars) v = some off := by
  obtain ⟨off, hmem⟩ := fst_mem_of_mem_buildVarMap hv
  exact lookupVar_of_mem_pair hmem

/-- Every variable in `collectVars p` has a `lookupVar` entry in `buildVarMap`. -/
private theorem lookupVar_of_mem_collectVars {p : Prog} {v : Var}
    (hv : v ∈ collectVars p) :
    ∃ off, lookupVar (buildVarMap (collectVars p)) v = some off :=
  lookupVar_of_mem hv

/-- `buildVarLayout` maps every variable in `collectVars p` to some location. -/
private theorem buildVarLayout_complete {p : Prog} {v : Var}
    (hv : v ∈ collectVars p) :
    (buildVarLayout (collectVars p) (buildVarMap (collectVars p))) v ≠ none := by
  -- buildVarLayout uses filterMap: tries varToArmReg, varToArmFReg, lookupVar
  -- If the first two return none, lookupVar succeeds (since v ∈ collectVars)
  -- The filterMap function always returns some for v ∈ collectVars
  -- (lookupVar succeeds as fallback), so (v, loc) ∈ entries, so lookup ≠ none
  have hfv : ∃ loc, (match varToArmReg v with
      | some r => some (v, VarLoc.ireg r)
      | none => match varToArmFReg v with
        | some r => some (v, VarLoc.freg r)
        | none => match lookupVar (buildVarMap (collectVars p)) v with
          | some off => some (v, VarLoc.stack off)
          | none => none) = some (v, loc) := by
    cases h1 : varToArmReg v with
    | some r => exact ⟨.ireg r, rfl⟩
    | none =>
      cases h2 : varToArmFReg v with
      | some r => exact ⟨.freg r, rfl⟩
      | none =>
        obtain ⟨off, hoff⟩ := lookupVar_of_mem hv
        exact ⟨.stack off, by rw [hoff]⟩
  obtain ⟨loc, hfv⟩ := hfv
  -- (v, loc) is in the filterMap result (= layout entries)
  unfold buildVarLayout; simp only
  -- (v, loc) ∈ filterMap result
  have hmem : (v, loc) ∈ (collectVars p).filterMap (fun v =>
      match varToArmReg v with
      | some r => some (v, VarLoc.ireg r)
      | none => match varToArmFReg v with
        | some r => some (v, VarLoc.freg r)
        | none => match lookupVar (buildVarMap (collectVars p)) v with
          | some off => some (v, VarLoc.stack off)
          | none => none) :=
    List.mem_filterMap.mpr ⟨v, hv, hfv⟩
  -- List.lookup v entries ≠ none when (v, loc) ∈ entries
  suffices ∀ (entries : List (Var × VarLoc)),
      (v, loc) ∈ entries → List.lookup v entries ≠ none by exact this _ hmem
  intro entries hmem
  induction entries with
  | nil => simp at hmem
  | cons hd tl ih =>
    simp [List.lookup]
    split
    · simp
    · cases hmem with
      | head => rename_i hne; simp [beq_self_eq_true] at hne
      | tail _ h => exact ih h

/-- Every observable variable is in `collectVars p`. Follows because
    `collectVars` ends with a foldl over `p.observable` that adds each
    unseen variable to the accumulator. -/
private theorem observable_subset_collectVars {p : Prog} {v : Var}
    (hv : v ∈ p.observable) : v ∈ collectVars p := by
  unfold collectVars
  -- After the inner code-foldl produces `vars`, the outer observable-foldl
  -- preserves each observable via `mem_foldl_addIfNew_of_mem_list`.
  exact mem_foldl_addIfNew_of_mem_list hv

/-- Every variable in `collectVars p` has a `lookupVar` entry. Alias around the
    existing private `lookupVar_of_mem_collectVars` for Phase-2 spec clients. -/
private theorem buildVarMap_lookup_of_mem {p : Prog} {v : Var}
    (hv : v ∈ collectVars p) :
    lookupVar (buildVarMap (collectVars p)) v ≠ none := by
  obtain ⟨off, hoff⟩ := lookupVar_of_mem_collectVars hv
  rw [hoff]; simp

/-- A successful `lookupVar` tells us the variable appears in the first components
    of the list. Used by the varMap injectivity spec clause. -/
private theorem mem_keys_of_lookupVar_some {l : List (Var × Nat)} {v : Var} {off : Nat}
    (h : lookupVar l v = some off) : v ∈ l.map Prod.fst := by
  unfold lookupVar at h
  cases hf : l.find? (fun p => p.1 == v) with
  | none => rw [hf] at h; simp at h
  | some p =>
    have hm := List.find?_some hf
    simp at hm
    have hmem := List.mem_of_find?_eq_some hf
    exact List.mem_map.mpr ⟨p, hmem, hm⟩

/-- `lookupVar (buildVarMap vars) v = some off` implies `v ∈ vars`. -/
private theorem mem_of_lookupVar_some {vars : List Var} {v : Var} {off : Nat}
    (h : lookupVar (buildVarMap vars) v = some off) : v ∈ vars := by
  have := mem_keys_of_lookupVar_some h
  rwa [buildVarMap_map_fst] at this

/-- Every variable in `TAC.vars instr` for any instruction in `p.code` is in `collectVars p`. -/
-- Helper: the collectVars step function adds all vars of the instruction
private theorem collectVars_step_adds_vars {acc : List Var} {instr : TAC} {v : Var}
    (hv : v ∈ instr.vars) :
    v ∈ (TAC.vars instr).foldl (fun a v => if a.contains v then a else a ++ [v]) acc :=
  mem_foldl_addIfNew_of_mem_list hv

-- Helper: the collectVars step function preserves existing membership
private theorem collectVars_step_mono {acc : List Var} {instr : TAC} {w : Var}
    (hw : w ∈ acc) :
    w ∈ (TAC.vars instr).foldl (fun a v => if a.contains v then a else a ++ [v]) acc :=
  mem_foldl_addIfNew_of_mem hw

-- Helper: the collectVars step function only adds vars from instr.vars
private theorem collectVars_step_subset {acc : List Var} {instr : TAC} {w : Var}
    (hw : w ∈ (TAC.vars instr).foldl (fun a v => if a.contains v then a else a ++ [v]) acc) :
    w ∈ acc ∨ w ∈ instr.vars :=
  mem_foldl_addIfNew_imp hw

-- Predicate propagation: if P holds for acc and for all instruction vars,
-- then P holds for all vars in the code foldl result.
-- Uses collectVars_step_subset to show each step only adds from instr.vars.
private theorem collectVars_code_pred {P : Var → Prop}
    {code : Array TAC} {acc : List Var}
    (hacc : ∀ v ∈ acc, P v)
    (hcode : ∀ (i : Nat) (hi : i < code.size), ∀ v ∈ code[i].vars, P v) :
    ∀ v ∈ code.foldl (init := acc) (fun acc instr =>
      (TAC.vars instr).foldl (fun a v => if a.contains v then a else a ++ [v]) acc), P v := by
  -- Convert Array.foldl to List.foldl, then induction on the list
  rw [← Array.foldl_toList]
  intro v hv
  suffices ∀ (l : List TAC) (acc : List Var),
      (∀ w ∈ acc, P w) →
      (∀ instr ∈ l, ∀ w ∈ instr.vars, P w) →
      ∀ w ∈ l.foldl (init := acc) (fun acc instr =>
        (TAC.vars instr).foldl (fun a v => if a.contains v then a else a ++ [v]) acc), P w by
    refine this code.toList acc hacc (fun instr hi w hw => ?_) v hv
    have ⟨i, hlt, heq⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp hi)
    rw [← heq] at hw; exact hcode i hlt w hw
  intro l
  induction l with
  | nil => intro acc hacc _; exact hacc
  | cons hd tl ih =>
    intro acc hacc hinstrs w hw
    simp only [List.foldl_cons] at hw
    apply ih _ _ (fun instr hi => hinstrs instr (List.mem_cons_of_mem _ hi)) _ hw
    intro u hu
    rcases collectVars_step_subset hu with h | h
    · exact hacc u h
    · exact hinstrs hd (List.mem_cons.mpr (Or.inl rfl)) u h

-- Monotone foldl: if v ∈ acc and each step preserves membership, v stays in the result
private theorem mem_foldl_mono
    {f : List Var → TAC → List Var}
    {l : List TAC} {acc : List Var} {v : Var}
    (hv : v ∈ acc)
    (hmono : ∀ acc (b : TAC), v ∈ acc → v ∈ f acc b) :
    v ∈ l.foldl f acc := by
  induction l generalizing acc with
  | nil => exact hv
  | cons hd tl ih => exact ih (hmono _ hd hv)

-- General foldl lemma: if step adds v when processing e, and step is monotone,
-- then v ∈ foldl step init list whenever e ∈ list.
private theorem mem_foldl_of_mem_step
    {f : List Var → TAC → List Var}
    {l : List TAC} {init : List Var} {e : TAC} {v : Var}
    (he : e ∈ l)
    (hadd : ∀ acc, v ∈ f acc e)
    (hmono : ∀ acc (b : TAC), v ∈ acc → v ∈ f acc b) :
    v ∈ l.foldl f init := by
  induction l generalizing init with
  | nil => simp at he
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    cases List.mem_cons.mp he with
    | inl heq => subst heq; exact mem_foldl_mono (hadd init) hmono
    | inr htl => exact ih htl

private theorem vars_subset_collectVars {p : Prog} {pc : Nat} (hpc : pc < p.code.size)
    {v : Var} (hv : v ∈ (p.code[pc]).vars) :
    v ∈ collectVars p := by
  unfold collectVars
  -- The observable fold preserves membership
  apply mem_foldl_addIfNew_of_mem
  -- Now show v ∈ p.code.foldl step [] — convert Array.foldl to List.foldl
  rw [← Array.foldl_toList]
  apply mem_foldl_of_mem_step (e := p.code[pc])
  · exact Array.getElem_mem_toList hpc
  · intro acc; exact collectVars_step_adds_vars hv
  · intro acc instr hw; exact collectVars_step_mono hw

/-- If no variable name violates the register convention, then `buildVarLayout` maps
    no variable to a restricted register: `varToArmReg` on non-restricted names
    produces non-restricted registers, `varToArmFReg` likewise. -/
private theorem buildVarLayout_regConventionSafe (p : Prog)
    (hNoViol : checkNoRegConventionViolations p = true)
    (hObsOk : p.observable.all fun v => !violatesRegConvention v) :
    (buildVarLayout (collectVars p) (buildVarMap (collectVars p))).regConventionSafe = true := by
  -- regConventionSafe checks entries.all — show each entry is safe
  unfold buildVarLayout VarLayout.regConventionSafe
  simp only
  -- entries = filterMap f (collectVars p); show all are safe
  rw [List.all_eq_true]
  intro ⟨w, loc⟩ hmem
  -- (w, loc) ∈ filterMap result → f w = some (w, loc) for some w ∈ collectVars p
  rw [List.mem_filterMap] at hmem
  obtain ⟨w', hw'mem, hw'eq⟩ := hmem
  -- w' ∈ collectVars p → ¬violatesRegConvention w'
  -- (collectVars adds code vars checked by hNoViol, and observable vars checked by hObsOk)
  have hw'ok : violatesRegConvention w' = false := by
    -- Every var in collectVars comes from either p.code instructions or p.observable
    -- hNoViol checks code vars, hObsOk checks observable vars
    -- Strategy: show the collectVars step only adds vars from instr.vars,
    -- and all such vars satisfy ¬violatesRegConvention
    unfold checkNoRegConventionViolations at hNoViol
    simp only [Array.all_eq_true, List.all_eq_true, Bool.not_eq_true'] at hNoViol hObsOk
    -- hNoViol: ∀ instr ∈ p.code, ∀ v ∈ instr.vars, ¬violatesRegConvention v
    -- hObsOk: ∀ v ∈ p.observable, ¬violatesRegConvention v
    -- w' ∈ collectVars p = observable-fold (code-fold [] p.code)
    -- collectVars p = observable-fold (code-fold [] p.code)
    -- w' ∈ collectVars p → w' ∈ code-fold ∨ w' ∈ p.observable (by mem_foldl_addIfNew_imp)
    unfold collectVars at hw'mem
    rcases mem_foldl_addIfNew_imp hw'mem with hCode | hObs
    · -- w' ∈ code foldl result → predicate propagation gives the result
      exact collectVars_code_pred (by simp) hNoViol _ hCode
    · exact hObsOk _ hObs
  -- Case split on which branch of the filterMap produced the entry
  cases h1 : varToArmReg w' with
  | some r =>
    simp [h1] at hw'eq; obtain ⟨rfl, rfl⟩ := hw'eq
    simp only [Prod.snd, bne_iff_ne, Bool.and_eq_true, ne_eq]
    repeat' constructor
    -- 9 goals: each is ¬(.ireg r = .ireg .xN) or ¬(.ireg r = .freg .dN)
    all_goals intro heq
    -- .ireg = .freg cases are absurd
    all_goals first
      | exact VarLoc.noConfusion heq
      | (obtain rfl := VarLoc.ireg.inj heq; exact absurd
          (varToArmReg_restricted_implies_violates h1 (by simp)) (by simp [hw'ok]))
  | none =>
    cases h2 : varToArmFReg w' with
    | some r =>
      simp [h1, h2] at hw'eq; obtain ⟨rfl, rfl⟩ := hw'eq
      simp only [Prod.snd, bne_iff_ne, Bool.and_eq_true, ne_eq]
      repeat' constructor
      all_goals intro heq
      all_goals first
        | exact VarLoc.noConfusion heq
        | (obtain rfl := VarLoc.freg.inj heq
           exact absurd
            (varToArmFReg_restricted_implies_violates h2 (by simp)) (by simp [hw'ok]))
    | none =>
      simp [h1, h2] at hw'eq
      cases h3 : lookupVar (buildVarMap (collectVars p)) w' with
      | some off => simp [h3] at hw'eq; obtain ⟨_, rfl⟩ := hw'eq; simp [bne_iff_ne]
      | none => simp [h3] at hw'eq

/-- `isInjective.go` returns true when the location components are `Nodup`. -/
private theorem isInjective_go_of_nodup_snd :
    ∀ (entries : List (Var × VarLoc)),
    (entries.map Prod.snd).Nodup → VarLayout.isInjective.go entries = true := by
  intro entries
  induction entries with
  | nil => simp [VarLayout.isInjective.go]
  | cons hd rest ih =>
    intro hNodup
    simp only [List.map, List.nodup_cons] at hNodup
    obtain ⟨hNotIn, hRest⟩ := hNodup
    simp only [VarLayout.isInjective.go, Bool.and_eq_true, Bool.not_eq_true']
    exact ⟨by
      rw [Bool.eq_false_iff]
      intro hAny
      rw [List.any_eq_true] at hAny
      obtain ⟨⟨v, l⟩, hmem, heq⟩ := hAny
      simp [beq_iff_eq] at heq
      exact hNotIn (List.mem_map.mpr ⟨(v, l), hmem, heq⟩), ih hRest⟩

/-- Every variable in `collectVars p` is either in the code's instruction vars or in the
    observable list — bridging `collectVars` to `checkNoRegisterCollisions`'s domain. -/
private theorem mem_collectVars_imp {p : Prog} {v : Var} (hv : v ∈ collectVars p) :
    v ∈ p.code.toList.flatMap TAC.vars ∨ v ∈ p.observable := by
  unfold collectVars at hv
  rcases mem_foldl_addIfNew_imp hv with hCode | hObs
  · left
    have hP : ∀ (i : Nat) (hi : i < p.code.size), ∀ w ∈ p.code[i].vars,
        w ∈ p.code.toList.flatMap TAC.vars := by
      intro i hi w hw
      exact List.mem_flatMap.mpr ⟨p.code[i], Array.getElem_mem_toList hi, hw⟩
    exact collectVars_code_pred (by simp) hP v hCode
  · exact Or.inr hObs


/-- Layout injectivity from the direct codegen prereq check. -/
private theorem buildVarLayout_injective (tyCtx : TyCtx) (p : Prog)
    (hPrereqs : checkCodegenPrereqs tyCtx p = true) :
    (buildVarLayout (collectVars p) (buildVarMap (collectVars p))).isInjective = true := by
  simp only [checkCodegenPrereqs, Bool.and_eq_true] at hPrereqs
  exact hPrereqs.1.1.2

/-- `checkCallerSaveSpec` passes for the constructed layout and varMap. -/
private theorem checkCallerSaveSpec_succeeds (tyCtx : TyCtx) (p : Prog)
    (hPrereqs : checkCodegenPrereqs tyCtx p = true) :
    checkCallerSaveSpec
      (buildVarLayout (collectVars p) (buildVarMap (collectVars p)))
      (buildVarMap (collectVars p)) = true := by
  simp only [checkCodegenPrereqs, Bool.and_eq_true] at hPrereqs
  exact hPrereqs.1.2

/-- Successor bounds check on a program (mirrors checkSuccessorsInBounds for trans). -/
def checkSuccessorsInBounds_prog (p : Prog) : Bool :=
  p.size > 0 &&
  (List.range p.size).all fun pc =>
    match p[pc]? with
    | some (.goto l) | some (.ifgoto _ l) => l < p.size
    | _ => true

/-- `checkBranchTargets` passes if all successors are in bounds. -/
theorem checkBranchTargets_of_successorsInBounds (p : Prog)
    (hSIB : checkSuccessorsInBounds_prog p = true) :
    checkBranchTargets p.code = none := by
  -- Both functions check the same property; bridge via contradiction
  unfold checkBranchTargets
  unfold checkSuccessorsInBounds_prog at hSIB
  simp only [Prog.size, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hSIB
  obtain ⟨_, hAll⟩ := hSIB
  -- Show find? returns none by showing the predicate is false for all PCs
  have hfind : ∀ pc ∈ List.range p.code.size,
      (match p.code[pc]?.getD .halt with
       | .goto l | .ifgoto _ l => decide (p.code.size ≤ l)
       | _ => false) = false := by
    intro pc hpc
    have hlt : pc < p.code.size := List.mem_range.mp hpc
    have hAll_pc := hAll pc (List.mem_range.mpr hlt)
    -- Resolve p[pc]? and getD for this in-bounds pc
    simp only [show (p[pc]? : Option TAC) = some p.code[pc] from
      Array.getElem?_eq_getElem hlt] at hAll_pc
    simp only [show p.code[pc]?.getD .halt = p.code[pc] from by
      simp [Array.getElem?_eq_getElem hlt]]
    -- Generalize + cases so substitution applies to both hAll_pc and goal
    generalize p.code[pc] = instr at hAll_pc ⊢
    cases instr with
    | goto l =>
      simp only at hAll_pc ⊢
      rw [decide_eq_true_eq] at hAll_pc
      rw [decide_eq_false_iff_not]
      exact Nat.not_le.mpr hAll_pc
    | ifgoto _ l =>
      simp only at hAll_pc ⊢
      rw [decide_eq_true_eq] at hAll_pc
      rw [decide_eq_false_iff_not]
      exact Nat.not_le.mpr hAll_pc
    | _ => rfl
  -- Now close: find? with all-false predicate returns none
  have : (List.range p.code.size).find? (fun pc =>
      match p.code[pc]?.getD .halt with
      | .goto l | .ifgoto _ l => decide (p.code.size ≤ l)
      | _ => false) = none := by
    rw [List.find?_eq_none]; intro pc hpc
    exact Bool.eq_false_iff.mp (hfind pc hpc)
  simp [this]

/-- `checkBoolExprSimpleOps` passes for `compileToTAC` output. -/
theorem compileToTAC_checkBoolExprSimpleOps (prog : Program) :
    checkBoolExprSimpleOps prog.compileToTAC = true := by
  unfold checkBoolExprSimpleOps
  simp only [Array.all_eq_true]
  intro i hi
  have hmem : prog.compileToTAC.code[i] ∈ prog.compileToTAC.code.toList :=
    List.getElem_mem (by simp at hi ⊢; exact hi)
  exact prog.compileToTAC_allSimpleOps _ hmem


/-- `checkBranchTargets` passes for `compileToTAC` output. -/
theorem compileToTAC_checkBranchTargets (prog : Program) :
    checkBranchTargets prog.compileToTAC.code = none := by
  apply checkBranchTargets_of_successorsInBounds
  -- Prove checkSuccessorsInBounds_prog from compileToTAC_jumpTargetsBound
  obtain ⟨hpos, hgoto, hifgoto⟩ := prog.compileToTAC_jumpTargetsBound
  unfold checkSuccessorsInBounds_prog
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  refine ⟨hpos, ?_⟩
  intro pc hpc
  rw [List.mem_range] at hpc
  simp only [Prog.getElem?_code]
  -- Case split on what's at this PC
  cases hget : prog.compileToTAC.code[pc]? with
  | none => simp
  | some instr =>
    cases instr with
    | goto l =>
      rw [decide_eq_true_eq]
      exact hgoto l (List.mem_of_getElem? (by simp [List.getElem?_toArray]; exact hget))
    | ifgoto be l =>
      rw [decide_eq_true_eq]
      exact hifgoto be l (List.mem_of_getElem? (by simp [List.getElem?_toArray]; exact hget))
    | _ => simp



/-- `verifiedGenInstr` returns `some` for any instruction in a well-typed program
    whose layout is complete, well-typed, regConventionSafe, and injective,
    and whose BoolExprs have simple ops. -/
private theorem verifiedGenInstr_total
    {layout : VarLayout} {pcMap : Nat → Nat} {instr : TAC}
    {haltS divS boundsS : Nat} {arrayDecls : List (ArrayName × Nat × VarTy)}
    {safe : Bool}
    (hRC : layout.regConventionSafe = true)
    (hII : layout.isInjective = true)
    (hComplete : ∀ v, v ∈ instr.vars → layout v ≠ none)
    (hWTL : WellTypedLayout tyCtx layout)
    (hWT : WellTypedInstr tyCtx arrayDecls instr)
    (hSimple : TAC.hasSimpleOps instr = true)
    (hNotPrint : ∀ fmt vs, instr ≠ .print fmt vs) :
    ∃ instrs, verifiedGenInstr layout pcMap instr haltS divS boundsS arrayDecls safe = some instrs := by
  -- Normalize layout coercion for simp_all compatibility
  have hlay : ∀ v, layout v = List.lookup v layout.entries := fun _ => rfl
  cases hWT
  case print => exact absurd rfl (hNotPrint _ _)
  case goto => unfold verifiedGenInstr; simp [hRC, hII]
  case halt => unfold verifiedGenInstr; simp [hRC, hII]
  case copy hty =>
    rename_i dst src
    by_cases hxy : dst = src
    · -- Self-copy: verifiedGenInstr emits `[.movR .x0 .x0]`.
      refine ⟨[.movR .x0 .x0], ?_⟩
      subst hxy
      unfold verifiedGenInstr; simp [hRC, hII]
    · have hxy_false : (dst == src) = false := by simp [hxy]
      unfold verifiedGenInstr
      simp only [hRC, hII, Bool.not_true, Bool.false_or, hxy_false, if_false]
      clear hSimple hty hComplete hNotPrint
      cases List.lookup src layout.entries <;> cases List.lookup dst layout.entries <;> dsimp
      all_goals (first | exact ⟨_, rfl⟩ | skip)
      all_goals split <;> (first | exact ⟨_, rfl⟩ | skip)
      all_goals split <;> exact ⟨_, rfl⟩
  case const hty =>
    rename_i x v
    have hx := hComplete x (List.mem_cons.mpr (Or.inl rfl))
    unfold verifiedGenInstr; simp only [hRC, hII, Bool.not_true, Bool.false_or, ↓reduceIte]
    cases v with
    | int n =>
      simp only [Value.typeOf] at hty
      cases hlx : layout x with
      | none => exact absurd hlx hx
      | some loc => cases loc with
        | freg r => exact absurd hlx (hWTL.int_not_freg hty.symm r)
        | ireg _ => simp_all
        | stack _ => simp_all
    | bool b =>
      simp only [Value.typeOf] at hty
      cases hlx : layout x with
      | none => exact absurd hlx hx
      | some loc => cases loc with
        | freg r => exact absurd hlx (hWTL.bool_not_freg hty.symm r)
        | ireg _ => simp_all
        | stack _ => simp_all
    | float f =>
      simp only [Value.typeOf] at hty
      cases hlx : layout x with
      | none => exact absurd hlx hx
      | some loc => cases loc with
        | ireg r => exact absurd hlx (hWTL.float_not_ireg hty.symm r)
        | freg _ => simp_all
        | stack _ => simp_all
  case binop hx hy hz =>
    unfold verifiedGenInstr; simp only [hRC, hII, Bool.not_true, Bool.false_or]
    split
    · next _ _ _ _ r h => exact absurd h (hWTL.int_not_freg hy r)
    · next _ _ _ r h _ => exact absurd h (hWTL.int_not_freg hz r)
    · next _ _ r h _ _ => exact absurd h (hWTL.int_not_freg hx r)
    · split <;> exact ⟨_, rfl⟩
  case boolop hx _ =>
    unfold verifiedGenInstr; simp only [hRC, hII, Bool.not_true, Bool.false_or]; dsimp
    simp only [TAC.hasSimpleOps] at hSimple; simp only [hSimple, Bool.not_true, ↓reduceIte]
    split
    · rename_i h; exact absurd h (by decide) -- false = true
    · -- notFreg guard on dst
      split
      · rename_i _ _ r h; exact absurd h (hWTL.bool_not_freg hx r)
      · exact ⟨_, rfl⟩
  case ifgoto _ =>
    unfold verifiedGenInstr; simp only [hRC, hII, Bool.not_true, Bool.false_or]
    simp only [TAC.hasSimpleOps] at hSimple; simp only [hSimple, Bool.not_true, ↓reduceIte]
    split
    · rename_i h; exact absurd h (by decide)
    · split <;> exact ⟨_, rfl⟩
  case arrLoad => unfold verifiedGenInstr; simp [hRC, hII]; split <;> exact ⟨_, rfl⟩
  case arrStore => unfold verifiedGenInstr; simp [hRC, hII]; split <;> exact ⟨_, rfl⟩
  case fbinop hx hy hz =>
    unfold verifiedGenInstr; simp only [hRC, hII, Bool.not_true, Bool.false_or]
    split
    · next _ _ _ _ r h => exact absurd h (hWTL.float_not_ireg hy r)
    · next _ _ _ r h _ => exact absurd h (hWTL.float_not_ireg hz r)
    · next _ _ r h _ _ => exact absurd h (hWTL.float_not_ireg hx r)
    · exact ⟨_, rfl⟩
  case intToFloat hx hy =>
    unfold verifiedGenInstr; simp only [hRC, hII, Bool.not_true, Bool.false_or]
    split
    · next _ _ r h => exact absurd h (hWTL.int_not_freg hy r)
    · next _ r h _ => exact absurd h (hWTL.float_not_ireg hx r)
    · exact ⟨_, rfl⟩
  case floatToInt hx hy =>
    unfold verifiedGenInstr; simp only [hRC, hII, Bool.not_true, Bool.false_or]
    split
    · next _ _ r h => exact absurd h (hWTL.float_not_ireg hy r)
    · next _ r h _ => exact absurd h (hWTL.int_not_freg hx r)
    · exact ⟨_, rfl⟩
  case floatUnary hx hy =>
    unfold verifiedGenInstr; simp only [hRC, hII, Bool.not_true, Bool.false_or]
    split
    · next _ _ r h => exact absurd h (hWTL.float_not_ireg hy r)
    · next _ r h _ => exact absurd h (hWTL.float_not_ireg hx r)
    · exact ⟨_, rfl⟩
  case fternop hx ha hb hc =>
    unfold verifiedGenInstr; simp only [hRC, hII, Bool.not_true, Bool.false_or]
    split
    · next _ _ _ _ r h => exact absurd h (hWTL.float_not_ireg ha r)
    · next _ _ _ r h _ => exact absurd h (hWTL.float_not_ireg hb r)
    · next _ _ r h _ _ => exact absurd h (hWTL.float_not_ireg hc r)
    · next _ r h _ _ _ => exact absurd h (hWTL.float_not_ireg hx r)
    · exact ⟨_, rfl⟩
  case printInt hv =>
    rename_i v
    unfold verifiedGenInstr; simp only [hRC, hII, Bool.not_true, Bool.false_or]
    split
    · next r h => exact absurd h (hWTL.int_not_freg hv r)
    · exact ⟨_, rfl⟩
  case printBool hv =>
    rename_i v
    unfold verifiedGenInstr; simp only [hRC, hII, Bool.not_true, Bool.false_or]
    split
    · next r h =>
      rcases hv with h_bool | h_int
      · exact absurd h (hWTL.bool_not_freg h_bool r)
      · exact absurd h (hWTL.int_not_freg h_int r)
    · exact ⟨_, rfl⟩
  case printFloat hv =>
    rename_i v
    unfold verifiedGenInstr; simp only [hRC, hII, Bool.not_true, Bool.false_or]
    split
    · next r h => exact absurd h (hWTL.float_not_ireg hv r)
    · exact ⟨_, rfl⟩
  case printString =>
    unfold verifiedGenInstr; simp [hRC, hII]
  -- NOTE: copy case has a codegen gap — verifiedGenInstr returns none when
  -- src is in stack/ireg and dst is in freg. Fix needed in verifiedGenInstr:
  -- add vLoadVar + fmovToFP path for non-freg → freg copy.

-- ──────────────────────────────────────────────────────────────
-- § 5b-final. Totality of verifiedGenerateAsm
-- ──────────────────────────────────────────────────────────────

/-- `bodyGenStep` with `some` input returns `some` for any valid pc. -/
private theorem bodyGenStep_preserves_some
    {code : Array TAC} {layout : VarLayout} {pcMap : Nat → Nat}
    {liveOut : Array (List Var)} {varMap : List (Var × Nat)}
    {checkerOk : Bool}
    {intervals : Array (Option BoundsOpt.IMap)}
    {arrayDecls : List (ArrayName × Nat × VarTy)}
    {haltS divS boundsS : Nat} {tyCtx : TyCtx}
    {arr : Array (List ArmInstr)} {pc : Nat}
    (hpc : pc < code.size)
    (hRC : layout.regConventionSafe = true)
    (hII : layout.isInjective = true)
    (hComplete : ∀ v, v ∈ code[pc].vars → layout v ≠ none)
    (hWTL : WellTypedLayout tyCtx layout)
    (hWTI : WellTypedInstr tyCtx arrayDecls code[pc])
    (hSimple : code[pc].hasSimpleOps = true) :
    ∃ arr', bodyGenStep code layout pcMap liveOut varMap checkerOk intervals arrayDecls
      haltS divS boundsS tyCtx (some arr) pc = some arr' := by
  unfold bodyGenStep
  -- Normalize getD to getElem using hpc
  have hGetD : code.getD pc .halt = code[pc] := by simp [Array.getD, hpc]
  simp only [hGetD]
  -- Case split: print vs non-print
  split
  · -- print: unconditional some
    exact ⟨_, rfl⟩
  · -- non-print: verifiedGenInstr returns some
    rename_i hNotPrint
    have hNP : ∀ fmt vs, code[pc] ≠ .print fmt vs := by
      intro fmt vs h; exact hNotPrint fmt vs h
    obtain ⟨instrs, hinstrs⟩ := verifiedGenInstr_total hRC hII hComplete hWTL hWTI hSimple hNP
    rw [hinstrs]; split <;> exact ⟨_, rfl⟩

/-- `verifiedGenerateAsm` succeeds for any well-typed program whose layout
    passes the codegen prerequisite checks. -/
theorem verifiedGenerateAsm_total (tyCtx : TyCtx) (p : Prog)
    (hWT : checkWellTypedProg tyCtx p = true)
    (hPrereqs : checkCodegenPrereqs tyCtx p = true)
    (hBranch : checkBranchTargets p.code = none)
    (hSimpleOps : checkBoolExprSimpleOps p = true) :
    ∃ r, verifiedGenerateAsm tyCtx p = .ok r := by
  unfold verifiedGenerateAsm
  simp only [hWT, Bool.not_true, Bool.true_and, ↓reduceIte]
  -- Extract regConventionSafe and WTL from checkCodegenPrereqs
  have hRC : (buildVarLayout (collectVars p) (buildVarMap (collectVars p))).regConventionSafe = true := by
    simp only [checkCodegenPrereqs, Bool.and_eq_true] at hPrereqs
    exact hPrereqs.1.1.1
  have hWTL : checkWellTypedLayout tyCtx
      (buildVarLayout (collectVars p) (buildVarMap (collectVars p))) p.code = none := by
    simp only [checkCodegenPrereqs, Bool.and_eq_true, beq_iff_eq] at hPrereqs
    exact hPrereqs.2
  -- Discharge layout checks
  have hII := (buildVarLayout_injective tyCtx p hPrereqs)
  have hCS := (checkCallerSaveSpec_succeeds tyCtx p hPrereqs)
  simp only [hRC, hII, Bool.not_true, ↓reduceIte, hWTL, hCS, hBranch]
  -- One remaining `if false = true` guard
  split
  · exact absurd ‹false = true› (by decide)
  · -- Generalize the fold, prove it's some, then match gives .ok
    generalize hfoldEq : List.foldl _ (some _) (List.range _) = foldResult
    -- General: foldl preserves some if each step does
    have foldl_pres : ∀ (f : Option (Array (List ArmInstr)) → Nat → Option (Array (List ArmInstr)))
        (pcs : List Nat) (arr : Array (List ArmInstr)),
        (∀ pc ∈ pcs, ∀ a, ∃ a', f (some a) pc = some a') →
        ∃ r, pcs.foldl f (some arr) = some r := by
      intro f pcs; induction pcs with
      | nil => intro arr _; exact ⟨arr, rfl⟩
      | cons pc rest ih =>
        intro arr hstep
        obtain ⟨a', ha'⟩ := hstep pc (.head _) arr
        simp only [List.foldl_cons, ha']
        exact ih _ (fun q hq a => hstep q (.tail _ hq) a)
    -- Prove foldResult = some bp
    obtain ⟨bp, hbp⟩ : ∃ bp, foldResult = some bp := by
      rw [← hfoldEq]
      -- Per-step: bodyGenStep (some arr) pc returns some for pc < p.code.size
      -- Print path: unconditional some. Non-print: verifiedGenInstr_total gives some.
      -- Mechanically correct but blocked by dependent match / coercion plumbing.
      exact foldl_pres _ _ _ (fun pc hpc arr => by
        rw [List.mem_range] at hpc
        exact bodyGenStep_preserves_some hpc hRC hII
          (fun v hv => buildVarLayout_complete (vars_subset_collectVars hpc hv))
          (checkWellTypedLayout_wellTyped hWTL)
          (checkWellTypedProg_sound hWT _ hpc)
          (by simp only [checkBoolExprSimpleOps, TAC.hasSimpleOps, Array.all_eq_true] at hSimpleOps
              exact hSimpleOps pc hpc))
    rw [hbp]; exact ⟨_, rfl⟩

-- ──────────────────────────────────────────────────────────────
-- § 5b-pre4. compileExpr/compileBool/compileStmt produce no register vars
-- ──────────────────────────────────────────────────────────────

/-- tmpName doesn't map to an integer register. -/
private theorem tmpName_noArmReg (k : Nat) : varToArmReg (tmpName k) = none := by
  unfold varToArmReg startsWithList tmpName
  simp [String.toList_append, ts_t, List.isPrefixOf]

/-- tmpName doesn't map to a float register. -/
private theorem tmpName_noArmFReg (k : Nat) : varToArmFReg (tmpName k) = none := by
  unfold varToArmFReg startsWithList tmpName
  simp [String.toList_append, ts_t, List.isPrefixOf]

/-- ftmpName doesn't map to an integer register. -/
private theorem ftmpName_noArmReg (k : Nat) : varToArmReg (ftmpName k) = none := by
  unfold varToArmReg startsWithList ftmpName
  simp [String.toList_append, ts_ft, List.isPrefixOf]

/-- ftmpName doesn't map to a float register. -/
private theorem ftmpName_noArmFReg (k : Nat) : varToArmFReg (ftmpName k) = none := by
  unfold varToArmFReg startsWithList ftmpName
  simp [String.toList_append, ts_ft, List.isPrefixOf]

/-- btmpName doesn't map to an integer register. -/
private theorem btmpName_noArmReg (k : Nat) : varToArmReg (btmpName k) = none := by
  unfold varToArmReg startsWithList btmpName
  simp [String.toList_append, ts_bt, List.isPrefixOf]
  rfl

/-- btmpName doesn't map to a float register. -/
private theorem btmpName_noArmFReg (k : Nat) : varToArmFReg (btmpName k) = none := by
  unfold varToArmFReg startsWithList btmpName
  simp [String.toList_append, ts_bt, List.isPrefixOf]
  intro h
  have h_bt : ("__bt" : String).toList = ['_', '_', 'b', 't'] := by decide
  rw [h_bt] at h
  -- h : ['_', '_', 'f', 'r'] <+: ['_', '_', 'b', 't'] ++ (toString k).toList
  -- This is false: position 2 is 'b', not 'f'
  obtain ⟨t, ht⟩ := h
  simp at ht

/-- Unified predicate: `v` does not correspond to any restricted register name.
    This combines three facts needed for `checkCodegenPrereqs`:
    1. `v` is not an integer register (`varToArmReg v = none`),
    2. `v` is not a float register (`varToArmFReg v = none`),
    3. `v` does not violate the register convention (`violatesRegConvention v = false`). -/
private def noRegVar (v : Var) : Prop :=
  varToArmReg v = none ∧ varToArmFReg v = none ∧ violatesRegConvention v = false

/-- Variables without `__` prefix don't violate the register convention. -/
private theorem violatesRegConvention_false_of_not_dunder (v : Var)
    (h : startsWithList v "__" = false) :
    violatesRegConvention v = false := by
  have hir : startsWithList v "__ir" = false := by
    unfold startsWithList at *
    exact List.isPrefixOf_of_isPrefixOf_append "__".toList "ir".toList v.toList h
  have hbr : startsWithList v "__br" = false := by
    unfold startsWithList at *
    exact List.isPrefixOf_of_isPrefixOf_append "__".toList "br".toList v.toList h
  have hfr : startsWithList v "__fr" = false := by
    unfold startsWithList at *
    exact List.isPrefixOf_of_isPrefixOf_append "__".toList "fr".toList v.toList h
  simp [violatesRegConvention, hir, hbr, hfr]

/-- Source variables (no `__` prefix) satisfy `noRegVar`. -/
private theorem noRegVar_of_not_dunder (v : Var) (h : startsWithList v "__" = false) :
    noRegVar v :=
  ⟨varToArmReg_none_of_not_dunder v h,
   varToArmFReg_none_of_not_dunder v h,
   violatesRegConvention_false_of_not_dunder v h⟩

/-- Integer temporaries `__tK` satisfy `noRegVar`. -/
private theorem tmpName_noRegVar (k : Nat) : noRegVar (tmpName k) :=
  ⟨tmpName_noArmReg k, tmpName_noArmFReg k, tmpName_not_violates k⟩

/-- Float temporaries `__ftK` satisfy `noRegVar`. -/
private theorem ftmpName_noRegVar (k : Nat) : noRegVar (ftmpName k) :=
  ⟨ftmpName_noArmReg k, ftmpName_noArmFReg k, ftmpName_not_violates k⟩

/-- Bool temporaries `__btK` satisfy `noRegVar`. -/
private theorem btmpName_noRegVar (k : Nat) : noRegVar (btmpName k) :=
  ⟨btmpName_noArmReg k, btmpName_noArmFReg k, btmpName_not_violates k⟩

/-- Every var in compileExpr output has varToArmReg = none, and so does the result var. -/
private theorem compileExpr_noRegVar (e : SExpr) (offset nextTmp : Nat)
    (hSrc : Program.SExpr.noReservedVars e = true) :
    (∀ instr ∈ (compileExpr e offset nextTmp).1, ∀ v ∈ instr.vars, noRegVar v) ∧
    noRegVar (compileExpr e offset nextTmp).2.1 := by
  induction e generalizing offset nextTmp with
  | lit n =>
    simp only [compileExpr]
    exact ⟨fun instr hmem => by simp at hmem; subst hmem; intro v hv; simp [TAC.vars] at hv; subst hv; exact tmpName_noRegVar _,
           tmpName_noRegVar _⟩
  | var x =>
    simp only [Program.SExpr.noReservedVars, Bool.not_eq_true'] at hSrc
    simp only [compileExpr]
    exact ⟨fun _ hmem => by simp at hmem, noRegVar_of_not_dunder x hSrc⟩
  | bin _ a b iha ihb =>
    simp only [Program.SExpr.noReservedVars, Bool.and_eq_true] at hSrc
    simp only [compileExpr]
    have ⟨ha_instrs, ha_res⟩ := iha offset nextTmp hSrc.1
    have ⟨hb_instrs, hb_res⟩ := ihb (offset + (compileExpr a offset nextTmp).1.length)
      (compileExpr a offset nextTmp).2.2 hSrc.2
    constructor
    · intro instr hmem v hv
      simp [List.mem_append] at hmem
      rcases hmem with h | h | rfl
      · exact ha_instrs instr h v hv
      · exact hb_instrs instr h v hv
      · simp [TAC.vars] at hv; rcases hv with rfl | rfl | rfl
        · exact tmpName_noRegVar _
        · exact ha_res
        · exact hb_res
    · exact tmpName_noRegVar _
  | arrRead _ idx ih =>
    simp only [Program.SExpr.noReservedVars] at hSrc
    simp only [compileExpr]
    have ⟨hi_instrs, hi_res⟩ := ih offset nextTmp hSrc
    constructor
    · intro instr hmem v hv
      simp [List.mem_append] at hmem
      rcases hmem with h | rfl
      · exact hi_instrs instr h v hv
      · simp [TAC.vars] at hv; rcases hv with rfl | rfl
        · exact tmpName_noRegVar _
        · exact hi_res
    · exact tmpName_noRegVar _
  | flit _ =>
    simp only [compileExpr]
    exact ⟨fun instr hmem => by simp at hmem; subst hmem; intro v hv; simp [TAC.vars] at hv; subst hv; exact ftmpName_noRegVar _,
           ftmpName_noRegVar _⟩
  | fbin _ a b iha ihb =>
    simp only [Program.SExpr.noReservedVars, Bool.and_eq_true] at hSrc
    simp only [compileExpr]
    have ⟨ha_instrs, ha_res⟩ := iha offset nextTmp hSrc.1
    have ⟨hb_instrs, hb_res⟩ := ihb (offset + (compileExpr a offset nextTmp).1.length)
      (compileExpr a offset nextTmp).2.2 hSrc.2
    constructor
    · intro instr hmem v hv
      simp [List.mem_append] at hmem
      rcases hmem with h | h | rfl
      · exact ha_instrs instr h v hv
      · exact hb_instrs instr h v hv
      · simp [TAC.vars] at hv; rcases hv with rfl | rfl | rfl
        · exact ftmpName_noRegVar _
        · exact ha_res
        · exact hb_res
    · exact ftmpName_noRegVar _
  | intToFloat e ih =>
    simp only [Program.SExpr.noReservedVars] at hSrc
    simp only [compileExpr]
    have ⟨hi_instrs, hi_res⟩ := ih offset nextTmp hSrc
    constructor
    · intro instr hmem v hv
      simp [List.mem_append] at hmem
      rcases hmem with h | rfl
      · exact hi_instrs instr h v hv
      · simp [TAC.vars] at hv; rcases hv with rfl | rfl
        · exact ftmpName_noRegVar _
        · exact hi_res
    · exact ftmpName_noRegVar _
  | floatToInt e ih =>
    simp only [Program.SExpr.noReservedVars] at hSrc
    simp only [compileExpr]
    have ⟨hi_instrs, hi_res⟩ := ih offset nextTmp hSrc
    constructor
    · intro instr hmem v hv
      simp [List.mem_append] at hmem
      rcases hmem with h | rfl
      · exact hi_instrs instr h v hv
      · simp [TAC.vars] at hv; rcases hv with rfl | rfl
        · exact tmpName_noRegVar _
        · exact hi_res
    · exact tmpName_noRegVar _
  | floatUnary _ e ih =>
    simp only [Program.SExpr.noReservedVars] at hSrc
    simp only [compileExpr]
    have ⟨hi_instrs, hi_res⟩ := ih offset nextTmp hSrc
    constructor
    · intro instr hmem v hv
      simp [List.mem_append] at hmem
      rcases hmem with h | rfl
      · exact hi_instrs instr h v hv
      · simp [TAC.vars] at hv; rcases hv with rfl | rfl
        · exact ftmpName_noRegVar _
        · exact hi_res
    · exact ftmpName_noRegVar _
  | farrRead _ idx ih =>
    simp only [Program.SExpr.noReservedVars] at hSrc
    simp only [compileExpr]
    have ⟨hi_instrs, hi_res⟩ := ih offset nextTmp hSrc
    constructor
    · intro instr hmem v hv
      simp [List.mem_append] at hmem
      rcases hmem with h | rfl
      · exact hi_instrs instr h v hv
      · simp [TAC.vars] at hv; rcases hv with rfl | rfl
        · exact ftmpName_noRegVar _
        · exact hi_res
    · exact ftmpName_noRegVar _

/-- Every var in compileBool output has varToArmReg = none, and so do vars in the result BoolExpr. -/
private theorem compileBool_noRegVar (b : SBool) (offset nextTmp : Nat)
    (hSrc : Program.SBool.noReservedVars b = true) :
    (∀ instr ∈ (compileBool b offset nextTmp).1, ∀ v ∈ instr.vars, noRegVar v) ∧
    (∀ v ∈ (compileBool b offset nextTmp).2.1.vars, noRegVar v) := by
  induction b generalizing offset nextTmp with
  | lit _ => simp [compileBool, BoolExpr.vars]
  | bvar x =>
    simp only [Program.SBool.noReservedVars, Bool.not_eq_true'] at hSrc
    simp only [compileBool, BoolExpr.vars]
    constructor
    · intro _ h; simp at h
    · intro v hv; simp at hv; rw [hv]; exact noRegVar_of_not_dunder x hSrc
  | cmp _ a b =>
    simp only [Program.SBool.noReservedVars, Bool.and_eq_true] at hSrc
    simp only [compileBool]
    have ⟨ha_i, ha_r⟩ := compileExpr_noRegVar a offset nextTmp hSrc.1
    have ⟨hb_i, hb_r⟩ := compileExpr_noRegVar b
      (offset + (compileExpr a offset nextTmp).1.length)
      (compileExpr a offset nextTmp).2.2 hSrc.2
    constructor
    · intro instr hmem v hv
      simp [List.mem_append] at hmem
      rcases hmem with h | h
      · exact ha_i instr h v hv
      · exact hb_i instr h v hv
    · intro v hv
      simp [BoolExpr.vars, Expr.freeVars] at hv
      rcases hv with rfl | rfl
      · exact ha_r
      · exact hb_r
  | not e ih =>
    simp only [Program.SBool.noReservedVars] at hSrc
    simp only [compileBool]
    exact ih offset nextTmp hSrc
  | and a b iha ihb =>
    simp only [Program.SBool.noReservedVars, Bool.and_eq_true] at hSrc
    simp only [compileBool]
    have ⟨ha_i, ha_be⟩ := iha offset nextTmp hSrc.1
    have ⟨hb_i, hb_be⟩ := ihb (offset + (compileBool a offset nextTmp).1.length + 1)
      ((compileBool a offset nextTmp).2.2 + 1) hSrc.2
    constructor
    · intro instr hmem v hv
      simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem
      -- code = codeA ++ [ifgoto] ++ codeB ++ [ifgoto, const, goto, const]
      rcases hmem with ((ha | rfl) | hb) | rfl | rfl | rfl | rfl
      · exact ha_i instr ha v hv
      · -- ifgoto (.not ba) — vars from BoolExpr
        simp [TAC.vars] at hv; exact ha_be v hv
      · exact hb_i instr hb v hv
      · simp [TAC.vars] at hv; exact hb_be v hv
      · simp [TAC.vars] at hv; subst hv; exact tmpName_noRegVar _
      · simp [TAC.vars] at hv  -- goto has no vars
      · simp [TAC.vars] at hv; subst hv; exact tmpName_noRegVar _
    · -- result BoolExpr: .cmp .ne (.var tR) (.lit 0)
      intro v hv
      simp [BoolExpr.vars, Expr.freeVars] at hv; subst hv
      exact tmpName_noRegVar _
  | or a b iha ihb =>
    simp only [Program.SBool.noReservedVars, Bool.and_eq_true] at hSrc
    simp only [compileBool]
    have ⟨ha_i, ha_be⟩ := iha offset nextTmp hSrc.1
    have ⟨hb_i, hb_be⟩ := ihb (offset + (compileBool a offset nextTmp).1.length + 1)
      ((compileBool a offset nextTmp).2.2 + 1) hSrc.2
    constructor
    · intro instr hmem v hv
      simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem
      rcases hmem with ((ha | rfl) | hb) | rfl | rfl | rfl | rfl
      · exact ha_i instr ha v hv
      · simp [TAC.vars] at hv; exact ha_be v hv
      · exact hb_i instr hb v hv
      · simp [TAC.vars] at hv; exact hb_be v hv
      · simp [TAC.vars] at hv; subst hv; exact tmpName_noRegVar _
      · simp [TAC.vars] at hv
      · simp [TAC.vars] at hv; subst hv; exact tmpName_noRegVar _
    · intro v hv
      simp [BoolExpr.vars, Expr.freeVars] at hv; subst hv
      exact tmpName_noRegVar _
  | barrRead _ idx =>
    simp only [Program.SBool.noReservedVars] at hSrc
    simp only [compileBool]
    have ⟨hi_i, hi_r⟩ := compileExpr_noRegVar idx offset nextTmp hSrc
    constructor
    · intro instr hmem v hv
      simp [List.mem_append] at hmem
      rcases hmem with h | rfl
      · exact hi_i instr h v hv
      · simp [TAC.vars] at hv; rcases hv with rfl | rfl
        · exact btmpName_noRegVar _
        · exact hi_r
    · intro v hv
      simp [BoolExpr.vars, Expr.freeVars] at hv; subst hv
      exact btmpName_noRegVar _
  | fcmp _ a b =>
    simp only [Program.SBool.noReservedVars, Bool.and_eq_true] at hSrc
    simp only [compileBool]
    have ⟨ha_i, ha_r⟩ := compileExpr_noRegVar a offset nextTmp hSrc.1
    have ⟨hb_i, hb_r⟩ := compileExpr_noRegVar b
      (offset + (compileExpr a offset nextTmp).1.length)
      (compileExpr a offset nextTmp).2.2 hSrc.2
    constructor
    · intro instr hmem v hv
      simp [List.mem_append] at hmem
      rcases hmem with h | h
      · exact ha_i instr h v hv
      · exact hb_i instr h v hv
    · intro v hv
      simp [BoolExpr.vars, Expr.freeVars] at hv
      rcases hv with rfl | rfl
      · exact ha_r
      · exact hb_r

/-- Every var in compileExprs output has varToArmReg = none. -/
private theorem compileExprs_noRegVar (args : List SExpr) (offset nextTmp : Nat)
    (hSrc : args.all Program.SExpr.noReservedVars = true) :
    ∀ instr ∈ (compileExprs args offset nextTmp).1, ∀ v ∈ instr.vars, noRegVar v := by
  induction args generalizing offset nextTmp with
  | nil => intro _ hmem; simp [compileExprs] at hmem
  | cons e rest ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hSrc
    intro instr hmem v hv
    simp only [compileExprs, List.mem_append] at hmem
    rcases hmem with he | hrest
    · exact (compileExpr_noRegVar e offset nextTmp hSrc.1).1 instr he v hv
    · exact ih _ _ hSrc.2 instr hrest v hv

/-- Every result var produced by compileExprs has varToArmReg = none. -/
private theorem compileExprs_result_noRegVar (args : List SExpr) (offset nextTmp : Nat)
    (hSrc : args.all Program.SExpr.noReservedVars = true) :
    ∀ v ∈ (compileExprs args offset nextTmp).2.1, noRegVar v := by
  induction args generalizing offset nextTmp with
  | nil => intro _ hmem; simp [compileExprs] at hmem
  | cons e rest ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hSrc
    intro v hv
    simp only [compileExprs, List.mem_cons] at hv
    rcases hv with rfl | hrest
    · exact (compileExpr_noRegVar e offset nextTmp hSrc.1).2
    · exact ih _ _ hSrc.2 v hrest

set_option maxHeartbeats 400000 in
/-- Every var in compileStmt output has varToArmReg = none. -/
private theorem compileStmt_noRegVar (s : Stmt) (offset nextTmp : Nat)
    (labels : List (String × Nat))
    (hSrc : Program.Stmt.noReservedVars s = true) :
    ∀ instr ∈ (compileStmt s offset nextTmp labels).1, ∀ v ∈ instr.vars,
      noRegVar v := by
  induction s generalizing offset nextTmp labels with
  | skip => intro _ hmem; simp [compileStmt] at hmem
  | seq s1 s2 ih1 ih2 =>
    simp only [Program.Stmt.noReservedVars, Bool.and_eq_true] at hSrc
    intro instr hmem v hv
    simp only [compileStmt, List.mem_append] at hmem
    rcases hmem with h | h
    · exact ih1 _ _ labels hSrc.1 instr h v hv
    · exact ih2 _ _ labels hSrc.2 instr h v hv
  | label _ => intro _ hmem; simp [compileStmt] at hmem
  | goto _ =>
    intro instr hmem; simp [compileStmt] at hmem; subst hmem
    intro v hv; simp [TAC.vars] at hv
  | arrWrite _ idx val =>
    simp only [Program.Stmt.noReservedVars, Bool.and_eq_true] at hSrc
    have ⟨hi_i, hi_r⟩ := compileExpr_noRegVar idx offset nextTmp hSrc.1
    have ⟨hv_i, hv_r⟩ := compileExpr_noRegVar val
      (offset + (compileExpr idx offset nextTmp).1.length)
      (compileExpr idx offset nextTmp).2.2 hSrc.2
    intro instr hmem v hv; simp [compileStmt, List.mem_append] at hmem
    rcases hmem with h | h | rfl
    · exact hi_i instr h v hv
    · exact hv_i instr h v hv
    · simp [TAC.vars] at hv; rcases hv with rfl | rfl; exact hi_r; exact hv_r
  | farrWrite _ idx val =>
    simp only [Program.Stmt.noReservedVars, Bool.and_eq_true] at hSrc
    have ⟨hi_i, hi_r⟩ := compileExpr_noRegVar idx offset nextTmp hSrc.1
    have ⟨hv_i, hv_r⟩ := compileExpr_noRegVar val
      (offset + (compileExpr idx offset nextTmp).1.length)
      (compileExpr idx offset nextTmp).2.2 hSrc.2
    intro instr hmem v hv; simp [compileStmt, List.mem_append] at hmem
    rcases hmem with h | h | rfl
    · exact hi_i instr h v hv
    · exact hv_i instr h v hv
    · simp [TAC.vars] at hv; rcases hv with rfl | rfl; exact hi_r; exact hv_r
  | bassign x b =>
    simp only [Program.Stmt.noReservedVars, Bool.and_eq_true, Bool.not_eq_true'] at hSrc
    have ⟨hb_i, hb_be⟩ := compileBool_noRegVar b offset nextTmp hSrc.2
    intro instr hmem v hv
    simp only [compileStmt, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with hcode | rfl
    · exact hb_i instr hcode v hv
    · simp [TAC.vars] at hv; rcases hv with rfl | hbe
      · exact noRegVar_of_not_dunder _ hSrc.1
      · exact hb_be v hbe
  | ite b s1 s2 ih1 ih2 =>
    simp only [Program.Stmt.noReservedVars, Bool.and_eq_true] at hSrc
    match hcb : compileBool b offset nextTmp with
    | (codeB, be, tmpB) =>
    match hs2 : compileStmt s2 (offset + codeB.length + 1) tmpB labels with
    | (codeElse, tmpE) =>
    match hs1 : compileStmt s1 (offset + codeB.length + 1 + codeElse.length + 1) tmpE labels with
    | (codeThen, _) =>
    have ⟨hb_i, hb_be⟩ := compileBool_noRegVar b offset nextTmp hSrc.1.1
    simp only [compileStmt, hcb, hs2, hs1]
    intro instr hmem v hv
    simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with (((h | rfl) | h) | rfl) | h
    · have := compileBool_noRegVar b offset nextTmp hSrc.1.1
      simp [hcb] at this; exact this.1 instr h v hv
    · have := compileBool_noRegVar b offset nextTmp hSrc.1.1
      simp [hcb] at this; simp [TAC.vars] at hv; exact this.2 v hv
    · have h2 := ih2 (offset + codeB.length + 1) tmpB labels hSrc.2 instr
      simp only [hs2] at h2; exact h2 h v hv
    · simp [TAC.vars] at hv
    · have h1 := ih1 (offset + codeB.length + 1 + codeElse.length + 1) tmpE labels hSrc.1.2 instr
      simp only [hs1] at h1; exact h1 h v hv
  | loop b body ih =>
    simp only [Program.Stmt.noReservedVars, Bool.and_eq_true] at hSrc
    match hcb : compileBool b offset nextTmp with
    | (codeB, be, tmpB) =>
    match hsbody : compileStmt body (offset + codeB.length + 1) tmpB labels with
    | (codeBody, _) =>
    have ⟨hb_i, hb_be⟩ := compileBool_noRegVar b offset nextTmp hSrc.1
    simp only [compileStmt, hcb, hsbody]
    intro instr hmem v hv
    simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ((h | rfl) | h) | rfl
    · have := compileBool_noRegVar b offset nextTmp hSrc.1
      simp [hcb] at this; exact this.1 instr h v hv
    · have := compileBool_noRegVar b offset nextTmp hSrc.1
      simp [hcb] at this; simp [TAC.vars] at hv; exact this.2 v hv
    · have hih := ih (offset + codeB.length + 1) tmpB labels hSrc.2 instr
      simp only [hsbody] at hih; exact hih h v hv
    · simp [TAC.vars] at hv
  | ifgoto b _ =>
    simp only [Program.Stmt.noReservedVars] at hSrc
    match hcb : compileBool b offset nextTmp with
    | (codeB, be, tmpB) =>
    simp only [compileStmt, hcb]
    intro instr hmem v hv
    simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with h | rfl
    · have := compileBool_noRegVar b offset nextTmp hSrc
      simp [hcb] at this; exact this.1 instr h v hv
    · have := compileBool_noRegVar b offset nextTmp hSrc
      simp [hcb] at this; simp [TAC.vars] at hv; exact this.2 v hv
  | print _ args =>
    simp only [Program.Stmt.noReservedVars] at hSrc
    intro instr hmem v hv; simp [compileStmt, List.mem_append] at hmem
    rcases hmem with h | rfl
    · exact compileExprs_noRegVar args offset nextTmp hSrc instr h v hv
    · simp [TAC.vars] at hv
      exact compileExprs_result_noRegVar args offset nextTmp hSrc v hv
  | printInt e =>
    simp only [Program.Stmt.noReservedVars] at hSrc
    have ⟨he_i, he_r⟩ := compileExpr_noRegVar e offset nextTmp hSrc
    intro instr hmem v hv; simp [compileStmt, List.mem_append] at hmem
    rcases hmem with h | rfl
    · exact he_i instr h v hv
    · simp [TAC.vars] at hv; subst hv; exact he_r
  | printBool b =>
    simp only [Program.Stmt.noReservedVars] at hSrc
    have ⟨hb_i, hb_be⟩ := compileBool_noRegVar b offset nextTmp hSrc
    intro instr hmem v hv
    simp only [compileStmt, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with (h | hconv) | rfl
    · exact hb_i instr h v hv
    · -- conv code: 4 instrs (ifgoto, const, goto, const)
      rcases hconv with rfl | rfl | rfl | rfl
      · -- ifgoto: vars = be.vars
        simp [TAC.vars] at hv; exact hb_be v hv
      · simp [TAC.vars] at hv; subst hv; exact tmpName_noRegVar _
      · simp [TAC.vars] at hv  -- goto has no vars
      · simp [TAC.vars] at hv; subst hv; exact tmpName_noRegVar _
    · -- printBool tmp
      simp [TAC.vars] at hv; subst hv; exact tmpName_noRegVar _
  | printFloat e =>
    simp only [Program.Stmt.noReservedVars] at hSrc
    have ⟨he_i, he_r⟩ := compileExpr_noRegVar e offset nextTmp hSrc
    intro instr hmem v hv; simp [compileStmt, List.mem_append] at hmem
    rcases hmem with h | rfl
    · exact he_i instr h v hv
    · simp [TAC.vars] at hv; subst hv; exact he_r
  | printString lit =>
    intro instr hmem v hv; simp [compileStmt] at hmem
    subst hmem; simp [TAC.vars] at hv
  | assign x e =>
    simp only [Program.Stmt.noReservedVars, Bool.and_eq_true, Bool.not_eq_true'] at hSrc
    intro instr hmem v hv
    cases e with
    | lit _ =>
      simp [compileStmt] at hmem; rw [hmem] at hv; simp [TAC.vars] at hv
      rw [hv]; exact noRegVar_of_not_dunder _ hSrc.1
    | var y =>
      simp only [Program.SExpr.noReservedVars, Bool.not_eq_true'] at hSrc
      simp [compileStmt] at hmem; rw [hmem] at hv; simp [TAC.vars] at hv
      rcases hv with rfl | rfl
      · exact noRegVar_of_not_dunder _ hSrc.1
      · exact noRegVar_of_not_dunder _ hSrc.2
    | bin _ a b =>
      simp only [Program.SExpr.noReservedVars, Bool.and_eq_true] at hSrc
      have ⟨ha_i, ha_r⟩ := compileExpr_noRegVar a offset nextTmp hSrc.2.1
      have ⟨hb_i, hb_r⟩ := compileExpr_noRegVar b
        (offset + (compileExpr a offset nextTmp).1.length)
        (compileExpr a offset nextTmp).2.2 hSrc.2.2
      simp [compileStmt, List.mem_append] at hmem
      rcases hmem with ha | hb | rfl
      · exact ha_i instr ha v hv
      · exact hb_i instr hb v hv
      · simp only [TAC.vars, List.mem_cons, List.mem_nil_iff, or_false] at hv
        rcases hv with h | h | h
        · rw [h]; exact noRegVar_of_not_dunder _ hSrc.1
        · rw [h]; exact ha_r
        · rw [h]; exact hb_r
    | arrRead _ idx =>
      simp only [Program.SExpr.noReservedVars] at hSrc
      have ⟨hi_i, hi_r⟩ := compileExpr_noRegVar idx offset nextTmp hSrc.2
      simp [compileStmt, List.mem_append] at hmem
      rcases hmem with h | rfl | rfl
      · exact hi_i instr h v hv
      · simp [TAC.vars] at hv; rcases hv with rfl | rfl
        · exact tmpName_noRegVar _
        · exact hi_r
      · simp [TAC.vars] at hv; rcases hv with rfl | rfl
        · exact noRegVar_of_not_dunder _ hSrc.1
        · exact tmpName_noRegVar _
    | flit _ | fbin _ _ _ | intToFloat _ | floatToInt _ | floatUnary _ _ | farrRead _ _ =>
      have ⟨he_i, he_r⟩ := compileExpr_noRegVar _ offset nextTmp hSrc.2
      simp [compileStmt, List.mem_append] at hmem
      rcases hmem with h | rfl
      · exact he_i instr h v hv
      · simp [TAC.vars] at hv; rcases hv with rfl | rfl
        · exact noRegVar_of_not_dunder _ hSrc.1
        · exact he_r
  | fassign x e =>
    simp only [Program.Stmt.noReservedVars, Bool.and_eq_true, Bool.not_eq_true'] at hSrc
    intro instr hmem v hv
    cases e with
    | flit _ =>
      simp [compileStmt] at hmem; rw [hmem] at hv; simp [TAC.vars] at hv
      rw [hv]; exact noRegVar_of_not_dunder _ hSrc.1
    | var y =>
      simp only [Program.SExpr.noReservedVars, Bool.not_eq_true'] at hSrc
      simp [compileStmt] at hmem; rw [hmem] at hv; simp [TAC.vars] at hv
      rcases hv with rfl | rfl
      · exact noRegVar_of_not_dunder _ hSrc.1
      · exact noRegVar_of_not_dunder _ hSrc.2
    | fbin _ a b =>
      simp only [Program.SExpr.noReservedVars, Bool.and_eq_true] at hSrc
      have ⟨ha_i, ha_r⟩ := compileExpr_noRegVar a offset nextTmp hSrc.2.1
      have ⟨hb_i, hb_r⟩ := compileExpr_noRegVar b
        (offset + (compileExpr a offset nextTmp).1.length)
        (compileExpr a offset nextTmp).2.2 hSrc.2.2
      simp [compileStmt, List.mem_append] at hmem
      rcases hmem with ha | hb | rfl
      · exact ha_i instr ha v hv
      · exact hb_i instr hb v hv
      · simp only [TAC.vars, List.mem_cons, List.mem_nil_iff, or_false] at hv
        rcases hv with h | h | h
        · rw [h]; exact noRegVar_of_not_dunder _ hSrc.1
        · rw [h]; exact ha_r
        · rw [h]; exact hb_r
    | intToFloat e =>
      simp only [Program.SExpr.noReservedVars] at hSrc
      have ⟨he_i, he_r⟩ := compileExpr_noRegVar e offset nextTmp hSrc.2
      simp [compileStmt, List.mem_append] at hmem
      rcases hmem with h | rfl
      · exact he_i instr h v hv
      · simp [TAC.vars] at hv; rcases hv with rfl | rfl
        · exact noRegVar_of_not_dunder _ hSrc.1
        · exact he_r
    | floatUnary _ e =>
      simp only [Program.SExpr.noReservedVars] at hSrc
      have ⟨he_i, he_r⟩ := compileExpr_noRegVar e offset nextTmp hSrc.2
      simp [compileStmt, List.mem_append] at hmem
      rcases hmem with h | rfl
      · exact he_i instr h v hv
      · simp [TAC.vars] at hv; rcases hv with rfl | rfl
        · exact noRegVar_of_not_dunder _ hSrc.1
        · exact he_r
    | farrRead _ idx =>
      simp only [Program.SExpr.noReservedVars] at hSrc
      have ⟨hi_i, hi_r⟩ := compileExpr_noRegVar idx offset nextTmp hSrc.2
      simp [compileStmt, List.mem_append] at hmem
      rcases hmem with h | rfl | rfl
      · exact hi_i instr h v hv
      · simp [TAC.vars] at hv; rcases hv with rfl | rfl
        · exact ftmpName_noRegVar _
        · exact hi_r
      · simp [TAC.vars] at hv; rcases hv with rfl | rfl
        · exact noRegVar_of_not_dunder _ hSrc.1
        · exact ftmpName_noRegVar _
    | lit _ | bin _ _ _ | arrRead _ _ | floatToInt _ =>
      have ⟨he_i, he_r⟩ := compileExpr_noRegVar _ offset nextTmp hSrc.2
      simp [compileStmt, List.mem_append] at hmem
      rcases hmem with h | rfl
      · exact he_i instr h v hv
      · simp [TAC.vars] at hv; rcases hv with rfl | rfl
        · exact noRegVar_of_not_dunder _ hSrc.1
        · exact he_r
  | barrWrite arr idx bval =>
    simp only [Program.Stmt.noReservedVars, Bool.and_eq_true] at hSrc
    have ⟨hi_i, hi_r⟩ := compileExpr_noRegVar idx offset nextTmp hSrc.1
    have ⟨hb_i, hb_be⟩ := compileBool_noRegVar bval
      (offset + (compileExpr idx offset nextTmp).1.length)
      (compileExpr idx offset nextTmp).2.2 hSrc.2
    intro instr hmem v hv
    simp only [compileStmt, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with (hi | hb) | rfl | rfl
    · exact hi_i instr hi v hv
    · exact hb_i instr hb v hv
    · -- boolop tBool be: vars = tBool :: be.vars
      simp [TAC.vars] at hv
      rcases hv with rfl | hbv
      · exact btmpName_noRegVar _
      · exact hb_be v hbv
    · -- arrStore arr vIdx tBool .bool: vars = [vIdx, tBool]
      simp [TAC.vars] at hv
      rcases hv with rfl | rfl
      · exact hi_r
      · exact btmpName_noRegVar _

-- ──────────────────────────────────────────────────────────────
-- § 5b-pre5. compileToTAC output has noRegVar on all vars
-- ──────────────────────────────────────────────────────────────

/-- Extract `checkNoReservedNames` from `wellFormed`. -/
private theorem wellFormed_checkNoReservedNames (prog : Program)
    (h : prog.wellFormed = true) : prog.checkNoReservedNames = true := by
  unfold Program.wellFormed at h
  simp only [Bool.and_eq_true] at h
  exact h.1.2

/-- Extract `Stmt.noReservedVars prog.body` from `wellFormed`. -/
private theorem wellFormed_body_noReservedVars (prog : Program)
    (h : prog.wellFormed = true) : Program.Stmt.noReservedVars prog.body = true := by
  unfold Program.wellFormed at h
  simp only [Bool.and_eq_true] at h
  exact h.2

/-- Every var in `Program.initCode decls` satisfies `noRegVar`, provided decl names don't start with `__`. -/
private theorem initCode_noRegVar {decls : List (Var × VarTy)}
    (h : decls.all (fun p => !(startsWithList p.1 "__")) = true) :
    ∀ instr ∈ Program.initCode decls, ∀ v ∈ instr.vars, noRegVar v := by
  intro instr hmem v hv
  simp only [Program.initCode, List.mem_map] at hmem
  obtain ⟨⟨x, ty⟩, hxdecls, hxinstr⟩ := hmem
  simp only [List.all_eq_true] at h
  have hx : startsWithList x "__" = false := by
    have := h (x, ty) hxdecls
    simpa [Bool.not_eq_true'] using this
  have hvarsx : instr.vars = [x] := by
    rw [← hxinstr]; cases ty <;> rfl
  rw [hvarsx] at hv
  rcases List.mem_singleton.mp hv with rfl
  exact noRegVar_of_not_dunder _ hx

/-- Every var in `(compileToTAC prog).code` satisfies `noRegVar`. -/
private theorem compileToTAC_code_noRegVar (prog : Program) (htcs : prog.wellFormed = true) :
    ∀ instr ∈ prog.compileToTAC.code.toList, ∀ v ∈ instr.vars, noRegVar v := by
  have hBody := wellFormed_body_noReservedVars prog htcs
  have hDecls := wellFormed_checkNoReservedNames prog htcs
  unfold Program.checkNoReservedNames at hDecls
  intro instr hmem v hv
  -- code.toList = initCode decls ++ body ++ [halt]
  have hcode : prog.compileToTAC.code.toList =
      Program.initCode prog.decls ++ (compileStmt prog.body (Program.initCode prog.decls).length 0
        (collectLabels prog.body (Program.initCode prog.decls).length)).1 ++ [TAC.halt] := by
    simp [Program.compileToTAC]
  rw [hcode] at hmem
  rcases List.mem_append.mp hmem with hleft | hhalt
  · rcases List.mem_append.mp hleft with hinit | hbody
    · exact initCode_noRegVar hDecls instr hinit v hv
    · exact compileStmt_noRegVar prog.body _ _ _ hBody instr hbody v hv
  · simp at hhalt; subst hhalt; simp [TAC.vars] at hv

/-- Every var in `(compileToTAC prog).observable` satisfies `noRegVar`. -/
private theorem compileToTAC_observable_noRegVar (prog : Program)
    (htcs : prog.wellFormed = true) :
    ∀ v ∈ prog.compileToTAC.observable, noRegVar v := by
  have hDecls := wellFormed_checkNoReservedNames prog htcs
  unfold Program.checkNoReservedNames at hDecls
  simp only [List.all_eq_true] at hDecls
  intro v hv
  -- observable = prog.decls.map Prod.fst
  simp only [Program.compileToTAC, List.mem_map] at hv
  obtain ⟨⟨x, ty⟩, hxdecls, rfl⟩ := hv
  have hx : startsWithList x "__" = false := by
    have := hDecls (x, ty) hxdecls
    simpa [Bool.not_eq_true'] using this
  exact noRegVar_of_not_dunder x hx

/-- Every var in `collectVars (compileToTAC prog)` satisfies `noRegVar`. -/
private theorem collectVars_compileToTAC_noRegVar (prog : Program)
    (htcs : prog.wellFormed = true) :
    ∀ v ∈ collectVars prog.compileToTAC, noRegVar v := by
  intro v hv
  -- collectVars = observable-fold (code-fold [] p.code) p.observable
  unfold collectVars at hv
  rcases mem_foldl_addIfNew_imp hv with hCode | hObs
  · -- v is in the code foldl result
    apply collectVars_code_pred (by simp) _ v hCode
    intro i hi w hw
    have : prog.compileToTAC.code[i] ∈ prog.compileToTAC.code.toList :=
      Array.getElem_mem_toList hi
    exact compileToTAC_code_noRegVar prog htcs _ this w hw
  · exact compileToTAC_observable_noRegVar prog htcs v hObs

/-- `filterMap` produces `[]` when the function returns `none` on every element. -/
private theorem filterMap_eq_nil_of_forall_none {α β : Type} (f : α → Option β)
    (l : List α) (h : ∀ x ∈ l, f x = none) : l.filterMap f = [] := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    have hhd : f hd = none := h hd List.mem_cons_self
    rw [List.filterMap_cons, hhd]
    exact ih (fun x hx => h x (List.mem_cons_of_mem hd hx))

/-- If `v` is in the `allVars` fold from `checkWellTypedLayout`, then `v` was in
    some instruction's vars. -/
private theorem list_foldl_allVars_mem_imp (l : List TAC) (init : List Var) (v : Var)
    (h : v ∈ l.foldl (fun acc instr =>
      acc ++ (TAC.vars instr).filter fun w => !acc.contains w) init) :
    v ∈ init ∨ ∃ instr ∈ l, v ∈ TAC.vars instr := by
  induction l generalizing init with
  | nil => left; exact h
  | cons hd tl ih =>
    simp only [List.foldl_cons] at h
    rcases ih _ h with hinit | ⟨instr, hmem, hv⟩
    · rcases List.mem_append.mp hinit with h' | hf
      · left; exact h'
      · right; refine ⟨hd, List.mem_cons_self, ?_⟩
        exact (List.mem_filter.mp hf).1
    · right; exact ⟨instr, List.mem_cons_of_mem hd hmem, hv⟩

/-- `filterMap` equals `map` when the function produces `Some` on every input. -/
private theorem filterMap_eq_map_of_all_some {α β : Type}
    {l : List α} {f : α → Option β} {g : α → β}
    (h : ∀ v ∈ l, f v = some (g v)) : l.filterMap f = l.map g := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.filterMap_cons, h hd List.mem_cons_self, List.map_cons]
    exact congrArg _ (ih (fun v hv => h v (List.mem_cons_of_mem hd hv)))

/-- `buildVarMap (hd :: tl) = (hd, 8) :: (shift by 8) (buildVarMap tl)`. -/
private theorem buildVarMap_cons_shift (hd : Var) (tl : List Var) :
    buildVarMap (hd :: tl) =
    (hd, 8) :: (buildVarMap tl).map (fun p => (p.1, p.2 + 8)) := by
  unfold buildVarMap
  simp only [List.length_cons, List.range_succ_eq_map, List.zip_cons_cons,
             List.map_cons, List.zip_map_left, List.map_map]
  refine congrArg₂ List.cons (by rfl) ?_
  apply List.map_congr_left
  rintro ⟨i, v⟩ _
  simp only [Function.comp_apply, Prod.map_apply, id_eq]
  refine Prod.mk.injEq _ _ _ _ |>.mpr ⟨rfl, ?_⟩
  omega

/-- `lookupVar` pushes a uniform offset-shift on the varMap through the result. -/
private theorem lookupVar_map_shift (varMap : List (Var × Nat)) (k : Nat) (v : Var) :
    lookupVar (varMap.map (fun p => (p.1, p.2 + k))) v =
    (lookupVar varMap v).map (· + k) := by
  unfold lookupVar
  rw [List.find?_map]
  have hpred :
      ((fun (x : Var × Nat) => x.1 == v) ∘ (fun (p : Var × Nat) => (p.1, p.2 + k))) =
      (fun (x : Var × Nat) => x.1 == v) := by
    funext p; rfl
  rw [hpred]
  cases varMap.find? (fun p => p.1 == v) with
  | none => rfl
  | some p => rfl

/-- When the head's key doesn't match, `lookupVar` skips it. -/
private theorem lookupVar_cons_ne (hd : Var) (off : Nat)
    (varMap : List (Var × Nat)) (v : Var) (hne : v ≠ hd) :
    lookupVar ((hd, off) :: varMap) v = lookupVar varMap v := by
  unfold lookupVar
  have hfind :
      List.find? (fun (p : Var × Nat) => p.1 == v) ((hd, off) :: varMap) =
      List.find? (fun (p : Var × Nat) => p.1 == v) varMap := by
    apply List.find?_cons_of_neg
    simp only [beq_iff_eq]
    exact fun h => hne h.symm
  rw [hfind]

/-- For `Nodup vars`, `lookupVar (buildVarMap vars) vars[i] = some ((i+1)*8)`. -/
private theorem lookupVar_buildVarMap_getElem {vars : List Var} (hNodup : vars.Nodup)
    {i : Nat} (hi : i < vars.length) :
    lookupVar (buildVarMap vars) vars[i] = some ((i + 1) * 8) := by
  induction vars generalizing i with
  | nil => exact absurd hi (by simp)
  | cons hd tl ih =>
    simp only [List.nodup_cons] at hNodup
    obtain ⟨hNotMem, hNodupTl⟩ := hNodup
    rw [buildVarMap_cons_shift]
    match i, hi with
    | 0, _ =>
      show lookupVar ((hd, 8) :: _) hd = some ((0 + 1) * 8)
      unfold lookupVar
      simp [List.find?_cons]
    | i + 1, hi =>
      have hit : i < tl.length := by simp at hi; omega
      have hne : tl[i] ≠ hd := fun h => hNotMem (h ▸ List.getElem_mem hit)
      show lookupVar ((hd, 8) :: _) tl[i] = some ((i + 1 + 1) * 8)
      rw [lookupVar_cons_ne _ _ _ _ hne, lookupVar_map_shift,
          ih hNodupTl hit]
      show some ((i + 1) * 8 + 8) = some ((i + 1 + 1) * 8)
      congr 1
      omega

/-- `lookupVar (buildVarMap vars) · ` is injective on `vars` (when `vars.Nodup`). -/
private theorem lookupVar_buildVarMap_injOn
    {vars : List Var} (hNodup : vars.Nodup)
    {v₁ v₂ : Var} (hv₁ : v₁ ∈ vars) (hv₂ : v₂ ∈ vars)
    (h : lookupVar (buildVarMap vars) v₁ = lookupVar (buildVarMap vars) v₂) :
    v₁ = v₂ := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hv₁
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hv₂
  rw [lookupVar_buildVarMap_getElem hNodup hi,
      lookupVar_buildVarMap_getElem hNodup hj] at h
  have heq : i = j := by
    have := Option.some.inj h
    omega
  subst heq
  rfl

/-- Under the `noRegVar` assumption on `vars`, every layout entry is a `.stack` entry. -/
private theorem buildVarLayout_entries_stack_of_noRegVar
    {vars : List Var} {varMap : List (Var × Nat)}
    (hvars : ∀ v ∈ vars, noRegVar v)
    {v : Var} {loc : VarLoc}
    (hmem : (v, loc) ∈ (buildVarLayout vars varMap).entries) :
    ∃ off, loc = .stack off := by
  unfold buildVarLayout at hmem
  simp only at hmem
  rw [List.mem_filterMap] at hmem
  obtain ⟨v', hv'mem, hfeq⟩ := hmem
  have hnr := hvars v' hv'mem
  rw [hnr.1, hnr.2.1] at hfeq
  simp only at hfeq
  cases hlu : lookupVar varMap v' with
  | none => rw [hlu] at hfeq; simp at hfeq
  | some off =>
    rw [hlu] at hfeq
    simp at hfeq
    exact ⟨off, by rw [hfeq.2]⟩

/-- `compileToTAC` output satisfies `checkCodegenPrereqs`: its variable layout
    is regConventionSafe, injective, has empty caller-save spec, and is well-typed.
    Follows from the all-stack layout produced by `compileToTAC`'s output. -/
theorem compileToTAC_codegenPrereqs (prog : Program) (htcs : prog.wellFormed = true) :
    checkCodegenPrereqs prog.tyCtx prog.compileToTAC = true := by
  have hNoRegVar : ∀ v ∈ collectVars prog.compileToTAC, noRegVar v :=
    collectVars_compileToTAC_noRegVar prog htcs
  have hAllStack : ∀ v loc,
      (v, loc) ∈ (buildVarLayout (collectVars prog.compileToTAC)
        (buildVarMap (collectVars prog.compileToTAC))).entries →
      ∃ off, loc = .stack off :=
    fun v loc hmem => buildVarLayout_entries_stack_of_noRegVar hNoRegVar hmem
  unfold checkCodegenPrereqs
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · -- regConventionSafe: all entries are .stack, so none are restricted .ireg / .freg
    unfold VarLayout.regConventionSafe
    rw [List.all_eq_true]
    intro ⟨v, loc⟩ hmem
    obtain ⟨off, rfl⟩ := hAllStack v loc hmem
    simp
  · -- isInjective: offsets from buildVarMap are Nodup; .stack is injective.
    show VarLayout.isInjective _ = true
    unfold VarLayout.isInjective
    apply isInjective_go_of_nodup_snd
    have hNodupVars : (collectVars prog.compileToTAC).Nodup := collectVars_nodup _
    have hEntriesEq :
        (buildVarLayout (collectVars prog.compileToTAC)
            (buildVarMap (collectVars prog.compileToTAC))).entries =
        (collectVars prog.compileToTAC).map (fun v =>
          (v, VarLoc.stack
            ((lookupVar (buildVarMap (collectVars prog.compileToTAC)) v).getD 0))) := by
      show (collectVars prog.compileToTAC).filterMap _ = _
      apply filterMap_eq_map_of_all_some
      intro v hv
      have hnr := hNoRegVar v hv
      rw [hnr.1, hnr.2.1]
      simp only
      obtain ⟨off, hoff⟩ := lookupVar_of_mem hv
      rw [hoff]
      simp
    rw [hEntriesEq, List.map_map]
    apply List.Nodup.map_on _ hNodupVars
    intro v₁ hv₁ v₂ hv₂ heq
    simp only [Function.comp_apply] at heq
    obtain ⟨off₁, hoff₁⟩ := lookupVar_of_mem hv₁
    obtain ⟨off₂, hoff₂⟩ := lookupVar_of_mem hv₂
    rw [hoff₁, hoff₂] at heq
    simp only [Option.getD_some] at heq
    have hOff : off₁ = off₂ := by cases heq; rfl
    exact lookupVar_buildVarMap_injOn hNodupVars hv₁ hv₂
      (by rw [hoff₁, hoff₂, hOff])
  · -- checkCallerSaveSpec: with all-stack layout, genCallerSaveAll produces []
    -- so all six conjuncts are vacuous or trivial.
    have hEmpty : genCallerSaveAll
        (buildVarLayout (collectVars prog.compileToTAC)
          (buildVarMap (collectVars prog.compileToTAC)))
        (buildVarMap (collectVars prog.compileToTAC)) = [] := by
      unfold genCallerSaveAll
      apply filterMap_eq_nil_of_forall_none
      intro ⟨v, loc⟩ hmem
      obtain ⟨off, rfl⟩ := hAllStack v loc hmem
      rfl
    unfold checkCallerSaveSpec
    rw [hEmpty]
    simp [listNodupBool]
    -- Remaining: hCoversIreg and hCoversFreg over layout.entries
    refine ⟨?_, ?_⟩ <;>
      (intro v loc hmem;
       obtain ⟨off, rfl⟩ := hAllStack v loc hmem; rfl)
  · -- checkWellTypedLayout = none
    -- Prove typeErr = none and allVars.find? = none, then the nested match is none.
    have htypeErr :
        (buildVarLayout (collectVars prog.compileToTAC)
            (buildVarMap (collectVars prog.compileToTAC))).entries.find?
          (fun x => match x.snd with
            | .freg _ => prog.tyCtx x.fst != .float
            | .ireg _ => prog.tyCtx x.fst == .float
            | .stack _ => false) = none := by
      rw [List.find?_eq_none]
      intro ⟨v, loc⟩ hmem
      obtain ⟨off, rfl⟩ := hAllStack v loc hmem
      simp
    have hAllMapped :
        (prog.compileToTAC.code.foldl (init := ([] : List Var)) fun acc instr =>
          acc ++ (TAC.vars instr).filter fun w => !acc.contains w).find?
          (fun v => ((buildVarLayout (collectVars prog.compileToTAC)
              (buildVarMap (collectVars prog.compileToTAC))) v).isNone) = none := by
      rw [List.find?_eq_none]
      intro v hv
      rw [← Array.foldl_toList] at hv
      rcases list_foldl_allVars_mem_imp _ _ _ hv with hinit | ⟨instr, hmem, hvars⟩
      · simp at hinit
      · have ⟨pc, hpc, heq⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp hmem)
        rw [← heq] at hvars
        have hvc : v ∈ collectVars prog.compileToTAC := vars_subset_collectVars hpc hvars
        have hne := buildVarLayout_complete hvc
        dsimp only at hne ⊢
        simp [Option.isNone_iff_eq_none, hne]
    -- Close by showing both find?s are none via the stored hypotheses.
    unfold checkWellTypedLayout
    simp only []
    split
    · rename_i _ _ _ heq
      exact absurd (heq.symm.trans htypeErr) (by simp)
    · split
      · rename_i _ _ heq
        exact absurd (heq.symm.trans hAllMapped) (by simp)
      · rfl

-- `generateAsm_total` (no-optimization path) is a corollary of
-- `generateAsm_total_with_passes` in PipelineCorrectness.lean — defined there
-- because it needs `applyPasses` which is declared later in this file.

-- ──────────────────────────────────────────────────────────────
-- buildPcMap prefix-sum lemmas
-- ──────────────────────────────────────────────────────────────

/-- The offsets array built by `buildPcMap`'s foldl. -/
private def buildOffsets (lengths : Array Nat) : Array Nat :=
  lengths.foldl (init := #[0]) fun acc len => acc.push (acc.back! + len)

/-- Core invariant: `buildOffsets` via list foldl produces a prefix-sum array
    of size `lengths.size + 1` where `offsets[0] = 0` and
    `offsets[i+1] = offsets[i] + lengths[i]`. We characterize it by a recursive
    function and then prove `buildPcMap` properties from that. -/
private def prefixSumList : List Nat → Nat → List Nat
  | [], acc => [acc]
  | l :: rest, acc => acc :: prefixSumList rest (acc + l)

private theorem prefixSumList_length : ∀ (ls : List Nat) (acc : Nat),
    (prefixSumList ls acc).length = ls.length + 1 := by
  intro ls; induction ls with
  | nil => intro acc; simp [prefixSumList]
  | cons l rest ih => intro acc; simp [prefixSumList, ih]

private theorem prefixSumList_head : ∀ (ls : List Nat) (acc : Nat),
    (prefixSumList ls acc)[0]'(by simp [prefixSumList_length]) = acc := by
  intro ls; induction ls with
  | nil => intro acc; simp [prefixSumList]
  | cons l rest _ => intro acc; simp [prefixSumList]

private theorem prefixSumList_succ (ls : List Nat) (acc : Nat) (i : Nat)
    (hi : i < ls.length) :
    (prefixSumList ls acc)[i + 1]'(by rw [prefixSumList_length]; omega) =
    (prefixSumList ls acc)[i]'(by rw [prefixSumList_length]; omega) +
    ls[i]'hi := by
  induction ls generalizing acc i with
  | nil => simp at hi
  | cons l rest ih =>
    simp only [prefixSumList]
    cases i with
    | zero =>
      simp [List.getElem_cons_zero, prefixSumList_head]
    | succ n =>
      simp only [List.getElem_cons_succ]
      exact ih (acc + l) n (by simp at hi; omega)

/-- The foldl in `buildPcMap` preserves early indices: `push` only appends. -/
private theorem foldl_push_getD_zero :
    ∀ (ls : List Nat) (init : Array Nat) (hsz : 0 < init.size),
    init[0]'hsz = 0 →
    (ls.foldl (fun acc len => acc.push (acc.back! + len)) init).getD 0 0 = 0 := by
  intro ls; induction ls with
  | nil =>
    intro init hsz h0; simp only [List.foldl]
    unfold Array.getD; split
    · exact h0
    · omega
  | cons l rest ih =>
    intro init hsz h0; simp only [List.foldl]
    have hsz' : 0 < (init.push (init.back! + l)).size := by simp [Array.size_push]
    apply ih _ hsz'
    simp [Array.getElem_push, hsz, h0]

/-- `buildPcMap` starts at 0 for the first TAC PC. -/
private theorem buildPcMap_zero (lengths : Array Nat) :
    buildPcMap lengths 0 = 0 := by
  show (lengths.foldl (init := #[0]) fun acc len =>
    acc.push (acc.back! + len)).getD 0 0 = 0
  rw [← Array.foldl_toList]
  exact foldl_push_getD_zero lengths.toList #[0] (by simp) (by simp)

/-- Generalized bridge: foldl-with-push on an array `(pfx ++ [acc]).toArray`
    produces `pfx ++ prefixSumList ls acc`. -/
private theorem foldl_push_toList :
    ∀ (ls : List Nat) (pfx : List Nat) (acc : Nat),
    (ls.foldl (fun a len => a.push (a.back! + len))
      ((pfx ++ [acc]).toArray)).toList =
    pfx ++ prefixSumList ls acc := by
  intro ls; induction ls with
  | nil => intro pfx acc; simp [prefixSumList, List.foldl]
  | cons l rest ih =>
    intro pfx acc; simp only [List.foldl, prefixSumList]
    have h1 : (pfx ++ [acc]).toArray.back! = acc := by
      simp
    have h2 : (pfx ++ [acc]).toArray.push (acc + l) =
        ((pfx ++ [acc]) ++ [acc + l]).toArray := by simp
    rw [h1, h2, ih (pfx ++ [acc]) (acc + l)]
    simp

/-- The offsets array built by buildPcMap's foldl equals prefixSumList. -/
private theorem buildPcMap_offsets_eq (lengths : Array Nat) :
    (lengths.foldl (init := #[0]) fun acc len =>
      acc.push (acc.back! + len)).toList = prefixSumList lengths.toList 0 := by
  rw [← Array.foldl_toList]
  exact foldl_push_toList lengths.toList ([] : List Nat) 0

/-- `buildPcMap` gives prefix sums:
    `pcMap (pc + 1) = pcMap pc + lengths[pc]`. -/
private theorem buildPcMap_succ (lengths : Array Nat) (pc : Nat)
    (hpc : pc < lengths.size) :
    buildPcMap lengths (pc + 1) =
    buildPcMap lengths pc + lengths[pc] := by
  show (lengths.foldl (init := #[0]) fun acc len =>
    acc.push (acc.back! + len)).getD (pc + 1) 0 =
    (lengths.foldl (init := #[0]) fun acc len =>
    acc.push (acc.back! + len)).getD pc 0 + lengths[pc]
  let offsets := lengths.foldl (init := #[0]) fun acc len =>
    acc.push (acc.back! + len)
  have hEq := buildPcMap_offsets_eq lengths
  -- offsets.size
  have hSz : offsets.size = lengths.size + 1 := by
    have : offsets.toList.length = (prefixSumList lengths.toList 0).length :=
      congrArg List.length hEq
    simp [prefixSumList_length] at this; exact this
  -- Both indices in bounds
  have h1 : pc + 1 < offsets.size := by omega
  have h0 : pc < offsets.size := by omega
  -- Unfold getD, both in-bounds
  show (if _ : pc + 1 < offsets.size then offsets[pc + 1] else 0) =
       (if _ : pc < offsets.size then offsets[pc] else 0) + lengths[pc]
  simp only [h1, h0, dite_true]
  -- Connect offsets[i] to prefixSumList via toList
  have hIdx : ∀ (i : Nat) (hi : i < offsets.size),
      offsets[i] = (prefixSumList lengths.toList 0)[i]'(by
        rw [prefixSumList_length]; simp; omega) := by
    intro i hi
    have : offsets.toList[i]? = (prefixSumList lengths.toList 0)[i]? := by rw [hEq]
    rw [Array.getElem?_toList] at this
    rw [Array.getElem?_eq_getElem hi,
        List.getElem?_eq_getElem (by rw [prefixSumList_length]; simp; omega)] at this
    exact Option.some.inj this
  rw [hIdx _ h1, hIdx _ h0]
  have : lengths.toList[pc] = lengths[pc] := by simp
  rw [← this]
  exact prefixSumList_succ lengths.toList 0 pc (by simp; exact hpc)

-- ──────────────────────────────────────────────────────────────
-- CodeAt from the flat body
-- ──────────────────────────────────────────────────────────────

/-- Indexing into a flattened list of lists at a segment boundary:
    element `j` of segment `k` is at position `(sum of lengths of segments 0..k-1) + j`
    in the flat list. -/
private theorem flatMap_segment_getElem (lss : List (List α)) (k j : Nat)
    (hk : k < lss.length) (hj : j < lss[k].length) :
    let offset := (lss.take k).flatMap id |>.length
    ((lss.flatMap id)[offset + j]?) = some (lss[k][j]) := by
  induction lss generalizing k with
  | nil => simp at hk
  | cons hd tl ih =>
    simp only [List.flatMap_cons, id]
    cases k with
    | zero =>
      simp only [List.take_zero, List.flatMap_nil, List.length_nil, Nat.zero_add,
                  List.getElem_cons_zero] at hj ⊢
      rw [List.getElem?_append_left hj, List.getElem?_eq_getElem hj]
    | succ n =>
      have hk' : n < tl.length := by simp at hk; omega
      simp only [List.take_succ_cons, List.flatMap_cons, id, List.length_append,
                  List.getElem_cons_succ] at hj ⊢
      rw [List.getElem?_append_right (by omega)]
      conv => lhs; rw [show hd.length + ((tl.take n).flatMap id).length + j - hd.length =
             ((tl.take n).flatMap id).length + j from by omega]
      exact ih n hk' hj

/-- `buildPcMap lengths pc` equals the total length of the first `pc` segments. -/
theorem buildPcMap_eq_take_length (bodyPerPC : Array (List ArmInstr))
    (lengths : Array Nat)
    (hSz : lengths.size = bodyPerPC.size)
    (hLen : ∀ (i : Nat) (hL : i < lengths.size) (hB : i < bodyPerPC.size),
      lengths[i] = (bodyPerPC[i]).length)
    (pc : Nat) (hpc : pc ≤ bodyPerPC.size) :
    buildPcMap lengths pc =
    ((bodyPerPC.toList.take pc).flatMap id).length := by
  induction pc with
  | zero =>
    rw [buildPcMap_zero]
    simp
  | succ n ih =>
    have hn : n < lengths.size := by omega
    rw [buildPcMap_succ lengths n hn]
    have ih' := ih (by omega)
    rw [ih']
    -- take (n+1) = take n ++ [bodyPerPC.toList[n]]
    rw [List.take_add_one]
    rw [List.getElem?_eq_getElem (by simp; omega)]
    simp only [Option.toList_some, List.flatMap_append, List.flatMap_singleton, id,
               List.length_append]
    congr 1
    rw [hLen n hn (by omega)]
    simp

/-- Each per-PC instruction block is embedded in the flat body at the
    offset given by `pcMap`. -/
theorem codeAt_of_bodyFlat (bodyPerPC : Array (List ArmInstr))
    (lengths : Array Nat)
    (hSz : lengths.size = bodyPerPC.size)
    (hLen : ∀ (i : Nat) (hL : i < lengths.size) (hB : i < bodyPerPC.size),
      lengths[i] = (bodyPerPC[i]).length)
    (pc : Nat) (hpc : pc < bodyPerPC.size) :
    CodeAt (bodyPerPC.toList.flatMap id).toArray
      (buildPcMap lengths pc) bodyPerPC[pc] := by
  intro i hi
  -- Convert Array getElem? to List getElem?
  rw [List.getElem?_toArray]
  -- Rewrite buildPcMap as take-length
  rw [buildPcMap_eq_take_length bodyPerPC lengths hSz hLen pc (by omega)]
  -- Use flatMap_segment_getElem on bodyPerPC.toList
  have hpc' : pc < bodyPerPC.toList.length := by simp; exact hpc
  have hj : i < bodyPerPC.toList[pc].length := by simp; exact hi
  exact flatMap_segment_getElem bodyPerPC.toList pc i hpc' hj

/-- Wrapper: per-PC block embeds in `bodyFlat` (= flat ++ haltSaveBlock). -/
theorem codeAt_of_bodyFlat' (r : VerifiedAsmResult)
    (lengths : Array Nat)
    (hSz : lengths.size = r.bodyPerPC.size)
    (hLen : ∀ (i : Nat) (hL : i < lengths.size) (hB : i < r.bodyPerPC.size),
      lengths[i] = (r.bodyPerPC[i]).length)
    (pc : Nat) (hpc : pc < r.bodyPerPC.size) :
    CodeAt r.bodyFlat (buildPcMap lengths pc) r.bodyPerPC[pc] := by
  have h := codeAt_of_bodyFlat r.bodyPerPC lengths hSz hLen pc hpc
  exact CodeAt.liftToSuffix (suf := r.haltSaveBlock.toList) h

/-- Every live TAC PC in a `GenAsmSpec`-satisfying result emits ≥ 1 ARM
    instruction. Dispatches on three cases:
    - **print** (via `printSaveRestore`): output = saves ++ `[.printCall _]` ++ restores.
    - **lib-call** (via `callSiteSaveRestore`): output = saves ++ baseInstrs ++ restores,
      where `baseInstrs` is from `verifiedGenInstr` (≥ 1 via `verifiedGenInstr_output_pos`).
    - **normal** (via `instrGen`): output directly from `verifiedGenInstr` (≥ 1).

    Consumed by Phase 5b's forward-divergence theorem to extract a positive
    ARM step count for each TAC step in `step_simulation`. -/
theorem bodyPerPC_length_pos
    {tyCtx : TyCtx} {p : Prog} {r : VerifiedAsmResult}
    (spec : GenAsmSpec tyCtx p r) :
    ∀ pc (hpc : pc < p.size), 1 ≤ (r.bodyPerPC[pc]'(spec.bodySize ▸ hpc)).length := by
  intro pc hpc
  by_cases hPrint : ∃ fmt vs, p[pc] = .print fmt vs
  · obtain ⟨lines, hEq⟩ := spec.printSaveRestore pc hpc hPrint
    rw [hEq]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  · by_cases hLib : isLibCallTAC p[pc] = true
    · obtain ⟨baseInstrs, hGenInstr, hEq⟩ := spec.callSiteSaveRestore pc hpc hLib
      rw [hEq]
      simp only [List.length_append]
      have hBaseLen : 1 ≤ baseInstrs.length :=
        verifiedGenInstr_output_pos tyCtx r.layout r.pcMap p[pc]
          r.haltS r.divS r.boundsS p.arrayDecls (verifiedBoundsSafe p pc)
          hGenInstr spec.regConventionSafe spec.injective spec.wellTypedLayout
          (spec.wellTypedProg pc hpc) (spec.layoutComplete pc hpc)
      omega
    · have hNotLib : isLibCallTAC p[pc] = false := by
        cases h : isLibCallTAC p[pc] <;> simp_all
      have hNotPrint : ∀ fmt vs, p[pc] ≠ .print fmt vs := by
        intro fmt vs h; exact hPrint ⟨fmt, vs, h⟩
      have hGenInstr := spec.instrGen pc hpc hNotLib hNotPrint
      exact verifiedGenInstr_output_pos tyCtx r.layout r.pcMap p[pc]
        r.haltS r.divS r.boundsS p.arrayDecls (verifiedBoundsSafe p pc)
        hGenInstr spec.regConventionSafe spec.injective spec.wellTypedLayout
        (spec.wellTypedProg pc hpc) (spec.layoutComplete pc hpc)

/-- A successful `verifiedGenerateAsm` call satisfies `GenAsmSpec`. -/
theorem verifiedGenerateAsm_spec {tyCtx : TyCtx} {p : Prog} {r : VerifiedAsmResult}
    (hGen : verifiedGenerateAsm tyCtx p = .ok r) : GenAsmSpec tyCtx p r := by
  -- Unfold and clear error guards
  simp only [verifiedGenerateAsm] at hGen
  split at hGen <;> simp_all                     -- checkWellTypedProg
  -- regConventionSafe
  split at hGen <;> simp_all
  rename_i hRC
  -- isInjective
  split at hGen <;> simp_all
  rename_i hII
  -- checkWellTypedLayout
  split at hGen
  · simp_all
  · -- none case — continue
    -- checkCallerSaveSpec
    split at hGen
    · simp_all
    · -- !checkCallerSaveSpec = false, i.e. checkCallerSaveSpec = true
      rename_i hWTL hCSS
      replace hCSS : checkCallerSaveSpec
          (buildVarLayout (collectVars p) (buildVarMap (collectVars p)))
          (buildVarMap (collectVars p)) = true := by
        revert hCSS; simp
      -- checkBranchTargets
      split at hGen
      · simp_all
      · -- none case — continue to bodyResult
        split at hGen
        · simp_all
        · -- some bodyPerPC
          -- Extract r = constructed record
          simp only [Except.ok.injEq] at hGen; subst r
          rename_i bodyPerPC heqFold
          -- Foldl properties: Lean unifies F from heqFold
          have hBSz : bodyPerPC.size = p.code.size := by
            apply foldl_push_size _ _ heqFold
            · intro; rfl
            · intro arr pc; exact bodyGenStep_push _ _ _ _ _ _ _ _ _ _ _ _ arr pc
          refine ⟨
            checkWellTypedProg_sound ‹_›,
            checkWellTypedLayout_wellTyped ‹_›,
            VarLayout.regConventionSafe_spec _ hRC,
            VarLayout.isInjective_spec _ hII,
            hRC,
            hII,
            by simp [Prog.size_eq]; exact hBSz,
            ?instrGen, ?pcMapLengths, ?layoutComplete, ?callSiteSaveRestore,
            ?printSaveRestore, ?callerSaveSpec,
            ?haltS_eq, ?haltFinal_eq, ?divS_eq, ?boundsS_eq,
            ?haltSaveBlock_eq, ?haltSaveComplete,
            ?varMapInjOnOffsets, ?layoutStackComesFromVarMap,
            buildVerifiedInvMap_preserved p, buildVerifiedInvMap_atStart p⟩
          case instrGen =>
            intro pc hpc hNotLib hNotPrint
            have hpcB : pc < bodyPerPC.size := by rw [hBSz]; simp [Prog.size_eq] at hpc; exact hpc
            have hpcCode : pc < p.code.size := by simp [Prog.size_eq] at hpc; exact hpc
            have hContent := by
              apply foldl_push_content _ _ heqFold pc hpcB
              · intro; rfl
              · intro arr pc; exact bodyGenStep_push _ _ _ _ _ _ _ _ _ _ _ _ arr pc
            obtain ⟨mid, _, hStep⟩ := hContent
            simp only [bodyGenStep, Array.getD, show pc < p.code.size from hpcCode,
              dite_true] at hStep
            split at hStep <;> split at hStep
            · simp_all
            · simp_all
            · simp_all
            · simp at hStep
              split at hStep
              · simp at hStep
              · rename_i armInstrs hGenInstr
                have : isLibCallTAC p.code[pc] = false := hNotLib
                rw [this] at hStep; simp at hStep
                -- Phase 6: `verifiedBoundsSafe p pc` unfolds (by `rfl`) to the
                -- `isBoundsSafe checkerOk p.arrayDecls (analyzeIntervals p) pc p.code[pc]`
                -- form that `bodyGenStep` emitted.
                have hbs : verifiedBoundsSafe p pc =
                    isBoundsSafe
                      (BoundsOpt.checkLocalPreservation p (BoundsOpt.analyzeIntervals p) &&
                        checkInvAtStart (BoundsOpt.analyzeIntervals p))
                      p.arrayDecls (BoundsOpt.analyzeIntervals p) pc p.code[pc] := by
                  simp only [verifiedBoundsSafe]
                  congr 1
                  simp [Array.getD, show pc < p.code.size from hpcCode]
                rw [hbs]
                exact (Array.push_inj hStep) ▸ hGenInstr
          case pcMapLengths =>
            refine ⟨_, ?_, rfl, ?_⟩
            · simp [List.length_map, List.length_range, hBSz]
            · intro i hL hB
              have hpcCode : i < p.code.size := by rw [← hBSz]; exact hB
              have hContent := by
                apply foldl_push_content _ _ heqFold i hB
                · intro; rfl
                · intro arr pc; exact bodyGenStep_push _ _ _ _ _ _ _ _ _ _ _ _ arr pc
              obtain ⟨mid, _, hStep⟩ := hContent
              rw [bodyGenStep_length hStep hpcCode]
              simp [List.getElem_toArray, List.getElem_map]
          case layoutComplete =>
            intro pc hpc v hv
            exact checkWellTypedLayout_instrMapped ‹_› (by simp [Prog.size_eq] at hpc; exact hpc) hv
          case callSiteSaveRestore =>
            intro pc hpc hLib
            have hpcB : pc < bodyPerPC.size := by rw [hBSz]; simp [Prog.size_eq] at hpc; exact hpc
            have hpcCode : pc < p.code.size := by simp [Prog.size_eq] at hpc; exact hpc
            have hContent := by
              apply foldl_push_content _ _ heqFold pc hpcB
              · intro; rfl
              · intro arr pc; exact bodyGenStep_push _ _ _ _ _ _ _ _ _ _ _ _ arr pc
            obtain ⟨mid, _, hStep⟩ := hContent
            simp only [bodyGenStep, Array.getD, show pc < p.code.size from hpcCode,
              dite_true] at hStep
            split at hStep <;> split at hStep
            · simp_all [isLibCallTAC]
            · simp_all
            · simp_all
            · simp at hStep
              split at hStep
              · simp at hStep
              · rename_i armInstrs hGenInstr
                rw [show isLibCallTAC p.code[pc] = true from hLib] at hStep
                simp only [ite_true] at hStep
                have hEq := (Array.push_inj (Option.some.inj hStep)).symm
                rw [← List.append_assoc] at hEq
                -- Phase 6: rewrite hGenInstr's `isBoundsSafe ...` form into
                -- `verifiedBoundsSafe p pc` to match the spec field's shape.
                have hbs : verifiedBoundsSafe p pc =
                    isBoundsSafe
                      (BoundsOpt.checkLocalPreservation p (BoundsOpt.analyzeIntervals p) &&
                        checkInvAtStart (BoundsOpt.analyzeIntervals p))
                      p.arrayDecls (BoundsOpt.analyzeIntervals p) pc p.code[pc] := by
                  simp only [verifiedBoundsSafe]
                  congr 1
                  simp [Array.getD, show pc < p.code.size from hpcCode]
                rw [hbs]
                exact ⟨armInstrs, hGenInstr, hEq⟩
          case printSaveRestore =>
            intro pc hpc ⟨fmt, vs, hPrint⟩
            have hpcB : pc < bodyPerPC.size := by rw [hBSz]; simp [Prog.size_eq] at hpc; exact hpc
            have hpcCode : pc < p.code.size := by simp [Prog.size_eq] at hpc; exact hpc
            have hContent := by
              apply foldl_push_content _ _ heqFold pc hpcB
              · intro; rfl
              · intro arr pc; exact bodyGenStep_push _ _ _ _ _ _ _ _ _ _ _ _ arr pc
            obtain ⟨mid, _, hStep⟩ := hContent
            simp only [bodyGenStep, Array.getD, show pc < p.code.size from hpcCode,
              dite_true] at hStep
            split at hStep <;> split at hStep
            · have hEq := (Array.push_inj (Option.some.inj hStep)).symm
              exact ⟨_, hEq⟩
            · rename_i h; exact absurd rfl h
            · rename_i heq h
              have hPE : p[pc] = TAC.print fmt vs := hPrint
              simp [Prog.getElem_eq] at hPE
              simp_all
            · rename_i heq h
              have hPE : p[pc] = TAC.print fmt vs := hPrint
              simp [Prog.getElem_eq] at hPE
              simp_all
          case callerSaveSpec =>
            exact checkCallerSaveSpec_sound hCSS
          case haltS_eq =>
            -- r.haltS = bodyInstrSize = pcMap p.code.size = (bodyPerPC.toList.flatMap id).length
            -- lArr has size bodyPerPC.size and lArr[i] = bodyPerPC[i].length.
            generalize hlArrDef : ((List.range p.code.size).map fun pc =>
              instrLength (buildVarLayout (collectVars p) (buildVarMap (collectVars p)))
                p.arrayDecls
                (isBoundsSafe
                    (BoundsOpt.checkLocalPreservation p (BoundsOpt.analyzeIntervals p) &&
                      checkInvAtStart (BoundsOpt.analyzeIntervals p))
                    p.arrayDecls (BoundsOpt.analyzeIntervals p) pc
                  (p.code[pc]?.getD TAC.halt)) (p.code[pc]?.getD TAC.halt)
                (buildVarMap (collectVars p))).toArray = lArr
            have hSize : lArr.size = bodyPerPC.size := by
              subst hlArrDef; simp [List.length_map, List.length_range, hBSz]
            have hLenEq : ∀ (i : Nat) (_hL : i < lArr.size) (hB : i < bodyPerPC.size),
                lArr[i] = (bodyPerPC[i]).length := by
              intro i _ hB
              have hpcCode : i < p.code.size := by rw [← hBSz]; exact hB
              have hContent := by
                apply foldl_push_content _ _ heqFold i hB
                · intro; rfl
                · intro arr pc; exact bodyGenStep_push _ _ _ _ _ _ _ _ _ _ _ _ arr pc
              obtain ⟨mid, _, hStep⟩ := hContent
              rw [bodyGenStep_length hStep hpcCode]
              subst hlArrDef
              simp [List.getElem_toArray, List.getElem_map]
            change buildPcMap lArr p.code.size = _
            rw [buildPcMap_eq_take_length bodyPerPC lArr hSize hLenEq
                p.code.size (by omega)]
            rw [show p.code.size = bodyPerPC.toList.length from by simp [hBSz]]
            rw [List.take_of_length_le (Nat.le_refl _)]
          case haltFinal_eq =>
            -- haltFinal = bodyInstrSize + haltSaveBlockList.length by construction.
            -- r.haltS = bodyInstrSize, r.haltSaveBlock.size = haltSaveBlockList.length.
            show _ + _ = _ + _
            simp
          case divS_eq => rfl
          case boundsS_eq => rfl
          case haltSaveBlock_eq =>
            -- r.haltSaveBlock = haltSaveBlockList.toArray; .toList restores the list.
            show (genHaltSave p.observable _ _).toArray.toList = _
            simp
          case haltSaveComplete =>
            intro v hv
            have hvInCV := observable_subset_collectVars hv
            have hVM := buildVarMap_lookup_of_mem hvInCV
            have hLayout : buildVarLayout (collectVars p) (buildVarMap (collectVars p)) v ≠ none :=
              buildVarLayout_complete hvInCV
            -- r.layout after record-subst equals buildVarLayout ... at all v via rfl.
            rcases h1 : (buildVarLayout (collectVars p) (buildVarMap (collectVars p))) v
              with _ | loc
            · exact absurd h1 hLayout
            · cases loc with
              | ireg r =>
                obtain ⟨off, hoff⟩ : ∃ off,
                    lookupVar (buildVarMap (collectVars p)) v = some off := by
                  rcases hl : lookupVar (buildVarMap (collectVars p)) v with _ | off
                  · exact absurd hl hVM
                  · exact ⟨off, rfl⟩
                exact Or.inl ⟨r, off, rfl, hoff⟩
              | freg r =>
                obtain ⟨off, hoff⟩ : ∃ off,
                    lookupVar (buildVarMap (collectVars p)) v = some off := by
                  rcases hl : lookupVar (buildVarMap (collectVars p)) v with _ | off
                  · exact absurd hl hVM
                  · exact ⟨off, rfl⟩
                exact Or.inr (Or.inl ⟨r, off, rfl, hoff⟩)
              | stack off =>
                exact Or.inr (Or.inr ⟨off, rfl⟩)
          case varMapInjOnOffsets =>
            -- Injectivity on offsets: two vars with the same lookup value are
            -- equal, because (buildVarMap vars).map Prod.snd is Nodup.
            intro v w off hv hw
            have hNodup := collectVars_nodup p
            have hvMem := mem_of_lookupVar_some hv
            have hwMem := mem_of_lookupVar_some hw
            exact lookupVar_buildVarMap_injOn hNodup hvMem hwMem (by rw [hv, hw])
          case layoutStackComesFromVarMap =>
            -- `buildVarLayout` falls through to `lookupVar varMap v` for the
            -- stack case; so `layout v = .stack off` forces `lookupVar = some off`.
            intro v off hLayout
            -- Unfold: r.layout = buildVarLayout ... and r.varMap = buildVarMap ...
            show lookupVar (buildVarMap (collectVars p)) v = some off
            unfold buildVarLayout at hLayout
            simp only at hLayout
            -- hLayout : List.lookup v (filterMap ... entries) = some (.stack off)
            have hmem := lookup_mem hLayout
            rw [List.mem_filterMap] at hmem
            obtain ⟨v', _, hfeq⟩ := hmem
            -- hfeq : (match varToArmReg v' with ...) = some (v, .stack off)
            -- The result is .stack off only if both varToArmReg/varToArmFReg are
            -- none and lookupVar succeeds.
            cases h1 : varToArmReg v' with
            | some r => rw [h1] at hfeq; simp at hfeq
            | none =>
              rw [h1] at hfeq
              cases h2 : varToArmFReg v' with
              | some r => rw [h2] at hfeq; simp at hfeq
              | none =>
                rw [h2] at hfeq
                cases h3 : lookupVar (buildVarMap (collectVars p)) v' with
                | none => rw [h3] at hfeq; simp at hfeq
                | some off' =>
                  rw [h3] at hfeq
                  simp at hfeq
                  obtain ⟨hvEq, hoffEq⟩ := hfeq
                  subst hvEq; subst hoffEq
                  exact h3

/-- Stepping through the halt-save block `genHaltSave observable layout varMap`
    from an `ExtStateRel`-compatible state produces a new state `s'` that:
    (1) advances the PC by the block's length,
    (2) preserves `arrayMem`,
    (3) preserves `ExtStateRel` (the block only touches fresh stack slots).

    The freshness argument: each save writes `stack[lookupVar varMap v]` for an
    ireg/freg-resident observable `v`. If some stack-resident `w` were to share
    that slot (`layout w = some (.stack off)`), then by `layoutStackComesFromVarMap`
    `lookupVar varMap w = some off = lookupVar varMap v`, so `v = w` by
    `varMapInjOnOffsets` — contradicting the ireg/freg vs. stack split on `v`. -/
private theorem armSteps_haltSaveBlock
    {prog : ArmProg} {layout : VarLayout}
    {varMap : List (Var × Nat)} {observable : List Var}
    {σ : Store} (s : ArmState)
    (hRel : ExtStateRel layout σ s)
    (hInj : ∀ v w off,
      lookupVar varMap v = some off → lookupVar varMap w = some off → v = w)
    (hStackVM : ∀ v off, layout v = some (.stack off) → lookupVar varMap v = some off)
    (hCode : CodeAt prog s.pc (genHaltSave observable layout varMap)) :
    ∃ s', ArmSteps prog s s' ∧
      s'.pc = s.pc + (genHaltSave observable layout varMap).length ∧
      s'.arrayMem = s.arrayMem ∧
      ExtStateRel layout σ s' := by
  induction observable generalizing s with
  | nil =>
    refine ⟨s, .refl, ?_, rfl, hRel⟩
    simp [genHaltSave]
  | cons v rest ih =>
    -- genHaltSave (v :: rest) = genHaltSaveOne v layout varMap ++ genHaltSave rest ...
    have hFlat : genHaltSave (v :: rest) layout varMap =
        genHaltSaveOne v layout varMap ++ genHaltSave rest layout varMap := by
      simp [genHaltSave]
    rw [hFlat] at hCode
    have hCode1 : CodeAt prog s.pc (genHaltSaveOne v layout varMap) :=
      hCode.append_left (l2 := genHaltSave rest layout varMap)
    have hCodeRest : CodeAt prog (s.pc + (genHaltSaveOne v layout varMap).length)
        (genHaltSave rest layout varMap) :=
      hCode.append_right (l1 := genHaltSaveOne v layout varMap)
    -- Handle genHaltSaveOne by cases
    -- Common: freshness lemma. If we write stack[off] where lookupVar varMap v = some off
    -- and layout v is ireg/freg, then for any w with layout w = some (.stack off'),
    -- we have off' ≠ off.
    have hFresh_of :
        ∀ {off : Nat} {loc : VarLoc},
          layout v = some loc →
          (∀ ir, loc ≠ .ireg ir → ∀ fr, loc ≠ .freg fr → False) →
          lookupVar varMap v = some off →
          ∀ w, layout w ≠ some (.stack off) := by
      intro off loc _ _ hLu w hContra
      -- hContra : layout w = some (.stack off)
      have hLuW : lookupVar varMap w = some off := hStackVM w off hContra
      have hEq := hInj v w off hLu hLuW
      subst hEq
      -- Now layout v = some (.stack off) (from hContra), but we had layout v = some loc
      -- (ireg/freg). Contradiction.
      rename_i hLoc hClassify
      rw [hContra] at hLoc
      -- hLoc : some (.stack off) = some loc
      have : loc = .stack off := by cases hLoc; rfl
      subst this
      exact hClassify .x0 (by intro h; cases h) .d0 (by intro h; cases h)
    -- Case-split on genHaltSaveOne
    unfold genHaltSaveOne at hCode1
    rcases hlv : layout v with _ | ⟨off_stk | ir | fr⟩
    · -- layout v = none: genHaltSaveOne = []
      rw [hlv] at hCode1
      simp only at hCode1
      -- restore state: s unchanged
      have hRestCode : CodeAt prog s.pc (genHaltSave rest layout varMap) := by
        have : (genHaltSaveOne v layout varMap).length = 0 := by
          simp [genHaltSaveOne, hlv]
        rw [this, Nat.add_zero] at hCodeRest
        exact hCodeRest
      obtain ⟨s', hSteps, hPC', hAM', hRel'⟩ := ih s hRel hRestCode
      refine ⟨s', hSteps, ?_, hAM', hRel'⟩
      rw [hPC']; simp [genHaltSaveOne, genHaltSave, hlv]
    · -- .stack off_stk: genHaltSaveOne = []
      rw [hlv] at hCode1
      simp only at hCode1
      have hRestCode : CodeAt prog s.pc (genHaltSave rest layout varMap) := by
        have : (genHaltSaveOne v layout varMap).length = 0 := by
          simp [genHaltSaveOne, hlv]
        rw [this, Nat.add_zero] at hCodeRest
        exact hCodeRest
      obtain ⟨s', hSteps, hPC', hAM', hRel'⟩ := ih s hRel hRestCode
      refine ⟨s', hSteps, ?_, hAM', hRel'⟩
      rw [hPC']; simp [genHaltSaveOne, genHaltSave, hlv]
    · -- .ireg ir
      rw [hlv] at hCode1
      simp only at hCode1
      rcases hLu : lookupVar varMap v with _ | off
      · -- lookupVar = none: genHaltSaveOne = []
        rw [hLu] at hCode1
        simp only at hCode1
        have hRestCode : CodeAt prog s.pc (genHaltSave rest layout varMap) := by
          have : (genHaltSaveOne v layout varMap).length = 0 := by
            simp [genHaltSaveOne, hlv, hLu]
          rw [this, Nat.add_zero] at hCodeRest
          exact hCodeRest
        obtain ⟨s', hSteps, hPC', hAM', hRel'⟩ := ih s hRel hRestCode
        refine ⟨s', hSteps, ?_, hAM', hRel'⟩
        rw [hPC']; simp [genHaltSaveOne, genHaltSave, hlv, hLu]
      · -- .str ir off, then recurse
        rw [hLu] at hCode1
        simp only at hCode1
        -- hCode1 : CodeAt prog s.pc [.str ir off]
        have hInstr : prog[s.pc]? = some (.str ir off) := hCode1.head
        let s1 := (s.setStack off (s.regs ir)).nextPC
        have hStep : ArmStep prog s s1 := ArmStep.str ir off hInstr
        -- Freshness: no layout entry maps to .stack off
        have hFresh : ∀ w, layout w ≠ some (.stack off) := by
          intro w hContra
          have hLuW : lookupVar varMap w = some off := hStackVM w off hContra
          have hEq := hInj v w off hLu hLuW
          subst hEq
          rw [hlv] at hContra
          cases hContra
        have hRel1 : ExtStateRel layout σ s1 := by
          show ExtStateRel layout σ (s.setStack off (s.regs ir)).nextPC
          rw [show (s.setStack off (s.regs ir)).nextPC =
              { s.setStack off (s.regs ir) with pc := s.pc + 1 } from by
            simp [ArmState.nextPC, ArmState.setStack]]
          exact (ExtStateRel.setStack_fresh hRel hFresh).withPC _
        have hPC1 : s1.pc = s.pc + 1 := by simp [s1]
        have hAM1 : s1.arrayMem = s.arrayMem := by simp [s1]
        -- Recurse
        have hRestCode' : CodeAt prog s1.pc (genHaltSave rest layout varMap) := by
          rw [hPC1]
          have : (genHaltSaveOne v layout varMap).length = 1 := by
            simp [genHaltSaveOne, hlv, hLu]
          rw [this] at hCodeRest
          exact hCodeRest
        obtain ⟨s', hSteps', hPC', hAM', hRel'⟩ := ih s1 hRel1 hRestCode'
        refine ⟨s', (ArmSteps.single hStep).trans hSteps', ?_, ?_, hRel'⟩
        · rw [hPC', hPC1]
          simp [genHaltSaveOne, genHaltSave, hlv, hLu]; omega
        · rw [hAM', hAM1]
    · -- .freg fr
      rw [hlv] at hCode1
      simp only at hCode1
      rcases hLu : lookupVar varMap v with _ | off
      · -- lookupVar = none
        rw [hLu] at hCode1
        simp only at hCode1
        have hRestCode : CodeAt prog s.pc (genHaltSave rest layout varMap) := by
          have : (genHaltSaveOne v layout varMap).length = 0 := by
            simp [genHaltSaveOne, hlv, hLu]
          rw [this, Nat.add_zero] at hCodeRest
          exact hCodeRest
        obtain ⟨s', hSteps, hPC', hAM', hRel'⟩ := ih s hRel hRestCode
        refine ⟨s', hSteps, ?_, hAM', hRel'⟩
        rw [hPC']; simp [genHaltSaveOne, genHaltSave, hlv, hLu]
      · -- .fstr fr off, then recurse
        rw [hLu] at hCode1
        simp only at hCode1
        have hInstr : prog[s.pc]? = some (.fstr fr off) := hCode1.head
        let s1 := (s.setStack off (s.fregs fr)).nextPC
        have hStep : ArmStep prog s s1 := ArmStep.fstr fr off hInstr
        have hFresh : ∀ w, layout w ≠ some (.stack off) := by
          intro w hContra
          have hLuW : lookupVar varMap w = some off := hStackVM w off hContra
          have hEq := hInj v w off hLu hLuW
          subst hEq
          rw [hlv] at hContra
          cases hContra
        have hRel1 : ExtStateRel layout σ s1 := by
          show ExtStateRel layout σ (s.setStack off (s.fregs fr)).nextPC
          rw [show (s.setStack off (s.fregs fr)).nextPC =
              { s.setStack off (s.fregs fr) with pc := s.pc + 1 } from by
            simp [ArmState.nextPC, ArmState.setStack]]
          exact (ExtStateRel.setStack_fresh hRel hFresh).withPC _
        have hPC1 : s1.pc = s.pc + 1 := by simp [s1]
        have hAM1 : s1.arrayMem = s.arrayMem := by simp [s1]
        have hRestCode' : CodeAt prog s1.pc (genHaltSave rest layout varMap) := by
          rw [hPC1]
          have : (genHaltSaveOne v layout varMap).length = 1 := by
            simp [genHaltSaveOne, hlv, hLu]
          rw [this] at hCodeRest
          exact hCodeRest
        obtain ⟨s', hSteps', hPC', hAM', hRel'⟩ := ih s1 hRel1 hRestCode'
        refine ⟨s', (ArmSteps.single hStep).trans hSteps', ?_, ?_, hRel'⟩
        · rw [hPC', hPC1]
          simp [genHaltSaveOne, genHaltSave, hlv, hLu]; omega
        · rw [hAM', hAM1]

-- ──────────────────────────────────────────────────────────────
-- Per-step simulation (wraps ext_backward_simulation)
-- ──────────────────────────────────────────────────────────────

/-- Phase 6 oracle-discharge helper. If the validated per-pc flag
    `verifiedBoundsSafe p pc` is `true` and the invariant `buildVerifiedInvMap
    p pc σ am` holds, then for any `arrLoad`/`arrStore` at `pc` the index
    value is in-bounds. The `verifiedGenInstr_correct`/`ext_backward_simulation`
    `hBoundsSafeOracle` hypothesis is exactly this shape. -/
private theorem verifiedBoundsSafe_sound {p : Prog} {pc : Nat} {σ : Store} {am : ArrayMem}
    (hPC : pc < p.size)
    (hBS : verifiedBoundsSafe p pc = true)
    (hInv : buildVerifiedInvMap p pc σ am) :
    (∀ dst arr idx ty, p[pc]? = some (.arrLoad dst arr idx ty) →
      ∀ idxVal, σ idx = .int idxVal → idxVal < arraySizeBv p.arrayDecls arr) ∧
    (∀ arr idx val ty, p[pc]? = some (.arrStore arr idx val ty) →
      ∀ idxVal, σ idx = .int idxVal → idxVal < arraySizeBv p.arrayDecls arr) := by
  -- Unfold the safe flag: `checkerOk && per-pc interval check`.
  simp only [verifiedBoundsSafe, isBoundsSafe, Bool.and_eq_true] at hBS
  obtain ⟨hCheckerOk, hMatch⟩ := hBS
  -- Under checker accepting, `buildVerifiedInvMap` ≡ `intervalMap (analyzeIntervals p)`.
  have hInvUnfold : BoundsOpt.intervalMap (BoundsOpt.analyzeIntervals p) pc σ am := by
    have hcAnd :
        (BoundsOpt.checkLocalPreservation p (BoundsOpt.analyzeIntervals p) &&
          checkInvAtStart (BoundsOpt.analyzeIntervals p)) = true := by
      rw [Bool.and_eq_true]; exact hCheckerOk
    have h := hInv
    simp only [buildVerifiedInvMap, hcAnd, if_true] at h
    exact h
  -- Normalize `p.code.getD pc .halt = p[pc]` via `hPC`.
  have hPcCode : pc < p.code.size := by simpa [Prog.size] using hPC
  have hCodeAtPc : p.code.getD pc .halt = p[pc] := by
    simp [Array.getD, hPcCode]
  rw [hCodeAtPc] at hMatch
  -- Core: from (intervals[pc]? contains a loose-valid in-bounds entry for idx) +
  -- (σ idx = .int idxVal) + (IMap.satisfies at pc), derive idxVal < arraySizeBv.
  have core : ∀ arr idx,
      (match (BoundsOpt.analyzeIntervals p)[pc]? with
       | some (some m) =>
          let r := BoundsOpt.imLookup m idx
          BoundsOpt.validIntervalLoose r && r.inBounds (arraySize p.arrayDecls arr) &&
            decide (arraySize p.arrayDecls arr < 2 ^ 62)
       | _ => false) = true →
      ∀ idxVal, σ idx = .int idxVal → idxVal < arraySizeBv p.arrayDecls arr := by
    intro arr idx hL idxVal hidx
    revert hL hInvUnfold
    cases hE : (BoundsOpt.analyzeIntervals p)[pc]? with
    | none => intros; simp_all
    | some om =>
      cases om with
      | none => intros; simp_all
      | some m =>
        simp only [BoundsOpt.intervalMap, hE]
        intro hSat hL
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hL
        obtain ⟨⟨hValidLoose, hInBounds⟩, hSzLt⟩ := hL
        have hMem := BoundsOpt.imLookup_mem_of_valid_loose hValidLoose
        obtain ⟨bv, hσidx, hSatR⟩ := hSat idx _ hMem hValidLoose
        have hEqVal : bv = idxVal := Value.int.inj (hσidx.symm.trans hidx)
        subst hEqVal
        obtain ⟨_, _, hLt⟩ := hSatR
        simp only [BoundsOpt.IRange.inBounds, Bool.and_eq_true, decide_eq_true_eq] at hInBounds
        obtain ⟨_, hHiLe⟩ := hInBounds
        -- hi.toNat ≤ arraySize (as a Nat inequality).
        have hHiNat : (BoundsOpt.imLookup m idx).hi.toNat ≤ arraySize p.arrayDecls arr := by
          have : (BoundsOpt.imLookup m idx).hi ≤ (arraySize p.arrayDecls arr : Int) := hHiLe
          omega
        -- arraySize < 2^62 < 2^64, so arraySizeBv doesn't wrap.
        have hSzBv : arraySize p.arrayDecls arr < 2 ^ 64 := by
          have : (2 : Nat) ^ 62 < 2 ^ 64 := by decide
          omega
        have hLtArr : bv.toNat < arraySize p.arrayDecls arr := by omega
        simp only [arraySizeBv, BitVec.lt_def, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt hSzBv]
        exact hLtArr
  refine ⟨?_, ?_⟩
  · intro dst arr idx ty hPcArr idxVal hidx
    have : p[pc] = TAC.arrLoad dst arr idx ty := by
      have := Prog.getElem?_eq_getElem hPC
      rw [this] at hPcArr; exact Option.some.inj hPcArr
    rw [this] at hMatch
    exact core arr idx hMatch idxVal hidx
  · intro arr idx val ty hPcArr idxVal hidx
    have : p[pc] = TAC.arrStore arr idx val ty := by
      have := Prog.getElem?_eq_getElem hPC
      rw [this] at hPcArr; exact Option.some.inj hPcArr
    rw [this] at hMatch
    exact core arr idx hMatch idxVal hidx

/-- One-step simulation: if we can take a TAC step from a running
    configuration, there exist ARM steps preserving `ExtSimRel`.

    This wraps `ext_backward_simulation` by discharging `CodeAt` and
    `hPcNext` from the `GenAsmSpec` invariants.

    **Phase 6:** takes `hInv : buildVerifiedInvMap p pc σ am` as an extra
    hypothesis so the `hBoundsSafeOracle` at `arrLoad`/`arrStore` bounds-error
    arms can be discharged from the validated interval claim. -/
private theorem step_simulation {tyCtx : TyCtx} {p : Prog} {r : VerifiedAsmResult}
    (spec : GenAsmSpec tyCtx p r)
    {pc : Nat} {σ : Store} {am : ArrayMem} {cfg' : Cfg} {s : ArmState}
    (hStep : p ⊩ Cfg.run pc σ am ⟶ cfg')
    (hRel : ExtSimRel r.layout r.pcMap r.divS r.boundsS (.run pc σ am) s)
    (hPC : pc < p.size)
    (hTS : TypedStore tyCtx σ)
    (hInv : buildVerifiedInvMap p pc σ am) :
    ∃ s' k, ArmStepsN r.bodyFlat s s' k ∧
          (∀ pc' σ' am', cfg' = .run pc' σ' am' → 1 ≤ k) ∧
          ExtSimRel r.layout r.pcMap r.divS r.boundsS cfg' s' ∧
          (∀ σ' am', cfg' = .halt σ' am' → s'.pc = r.haltFinal) := by
  -- Case split: lib-call, print, or normal instruction
  by_cases hLib : isLibCallTAC p[pc] = true
  · -- Lib-call case: save/restore around computation (excludes destination)
    -- Determine cfg' early (before infrastructure, to avoid simp_all pollution)
    have hCfgRun : ∃ σ', cfg' = .run (pc + 1) σ' am := by
      have : pc < p.code.size := by simp [Prog.size_eq] at hPC; exact hPC
      cases hStep <;> simp_all [isLibCallTAC]
      -- Remaining: type-error cases — impossible under TypedStore + WellTypedProg
      -- WellTypedInstr gives Γ y = .float; TypedStore gives (σ y).typeOf = Γ y = .float
      all_goals {
        rename_i hInstr hTypeErr
        have hWTI := spec.wellTypedProg pc hPC
        rw [show p[pc] = p.code[pc] from rfl] at hWTI
        rw [hInstr] at hWTI
        cases hWTI <;> simp_all [TypedStore]
      }
    obtain ⟨σ', hCfg⟩ := hCfgRun
    -- TAC-level: lib-call only modifies the destination variable
    -- Prove before subst to avoid am-dependency issues in cases hStep
    have hDstOnly : ∀ v, DAEOpt.instrDef p[pc] ≠ some v → σ' v = σ v := by
      have : pc < p.code.size := by simp [Prog.size_eq] at hPC; exact hPC
      -- cases hStep with cfg' still abstract (avoids am = am.write unification)
      intro v hne
      cases hStep <;> simp_all [isLibCallTAC, DAEOpt.instrDef]
      all_goals (rw [← ‹_ = σ'›]; simp [Store.update]; intro h; exact absurd h.symm ‹_›)
    -- TAC result: σ' = σ[dst ↦ result] (before subst, to avoid am-dependency)
    have hLibStep : ∀ x op y, p.code[pc] = .floatUnary x op y →
        ∃ f, σ y = .float f ∧ σ' x = .float (op.eval f) := by
      have hpc : pc < p.code.size := by simp [Prog.size_eq] at hPC; exact hPC
      intro x' op' y' hI
      have hI' : p[pc]? = some (.floatUnary x' op' y') := by
        simp [Prog.getElem?_code, Array.getElem?_eq_getElem hpc, hI]
      cases hStep with
      | floatUnary hinstr hy =>
        have := Option.some.inj (hI'.symm.trans hinstr)
        rcases this with ⟨rfl, rfl, rfl⟩
        exact ⟨_, hy, by cases hCfg; simp [Store.update_self]⟩
      | floatUnary_typeError hinstr hne =>
        have := Option.some.inj (hI'.symm.trans hinstr)
        rcases this with ⟨rfl, rfl, rfl⟩
        have hWTI := spec.wellTypedProg pc hPC
        rw [show p[pc] = p.code[pc] from rfl, hI] at hWTI
        cases hWTI <;> simp_all [TypedStore]
      | _ => exfalso; simp_all
    have hLibStepBin : ∀ x y z, p.code[pc] = .fbinop x .fpow y z →
        ∃ fy fz, σ y = .float fy ∧ σ z = .float fz ∧
          σ' x = .float (FloatBinOp.eval .fpow fy fz) := by
      have hpc : pc < p.code.size := by simp [Prog.size_eq] at hPC; exact hPC
      intro x' y' z' hI
      have hI' : p[pc]? = some (.fbinop x' .fpow y' z') := by
        simp [Prog.getElem?_code, Array.getElem?_eq_getElem hpc, hI]
      cases hStep with
      | fbinop hinstr hy hz =>
        have := Option.some.inj (hI'.symm.trans hinstr)
        rcases this with ⟨rfl, rfl, rfl, rfl⟩
        exact ⟨_, _, hy, hz, by cases hCfg; simp [Store.update_self]⟩
      | fbinop_typeError hinstr hne =>
        have := Option.some.inj (hI'.symm.trans hinstr)
        rcases this with ⟨rfl, rfl, rfl, rfl⟩
        have hWTI := spec.wellTypedProg pc hPC
        rw [show p[pc] = p.code[pc] from rfl, hI] at hWTI
        cases hWTI <;> simp_all [TypedStore]
      | _ => exfalso; simp_all
    subst hCfg
    -- Get bodyPerPC = saves ++ baseInstrs ++ restores
    obtain ⟨baseInstrs, hGenInstr, hBody⟩ :=
      spec.callSiteSaveRestore pc hPC hLib
    -- Infrastructure
    obtain ⟨lengths, hLSz, hPcMap, hLenEq⟩ := spec.pcMapLengths
    have hpcB : pc < r.bodyPerPC.size := spec.bodySize ▸ hPC
    have hCodeAt : CodeAt r.bodyFlat (r.pcMap pc) (r.bodyPerPC[pc]'hpcB) := by
      rw [hPcMap]; exact codeAt_of_bodyFlat' r lengths hLSz hLenEq pc hpcB
    rw [hBody] at hCodeAt
    -- Abbreviate entries
    let entries := callerSaveEntries r.layout r.varMap (DAEOpt.instrDef p[pc])
    -- Split CodeAt: saves ++ baseInstrs ++ restores
    have hCodeSB := hCodeAt.append_left (l2 := entriesToRestores entries)
    have hCodeRestores := hCodeAt.append_right
      (l1 := entriesToSaves entries ++ baseInstrs)
    have hCodeSaves := hCodeSB.append_left (l2 := baseInstrs)
    have hCodeBase := hCodeSB.append_right (l1 := entriesToSaves entries)
    -- Extract ExtStateRel components
    obtain ⟨hStateRel, hPcRel, hArrayMem⟩ := hRel
    have hSPC : s.pc = r.pcMap pc := hPcRel
    -- hPcNext
    have hPcNext : r.pcMap (pc + 1) = r.pcMap pc + (r.bodyPerPC[pc]'hpcB).length := by
      rw [hPcMap, buildPcMap_succ lengths pc (by rw [hLSz]; exact hpcB)]
      congr 1; exact hLenEq pc (by rw [hLSz]; exact hpcB) hpcB
    -- Step 1: saves
    have hStepSaves := armSteps_saves r.bodyFlat entries s (hSPC ▸ hCodeSaves)
    let s_saved := {applyCallerSaves entries s with pc := s.pc + entries.length}
    have hSavedPC : s_saved.pc = r.pcMap pc + (entriesToSaves entries).length := by
      simp [s_saved, entriesToSaves_length, hSPC]
    -- Entry vars (non-dst caller-saved) are unchanged by the TAC step.
    -- An entry var's register is in callerSaveEntries, which excludes the dst.
    -- So the var ≠ dst, and hDstOnly gives σ'(v) = σ(v).
    have hEIU : ∀ v ir, r.layout v = some (.ireg ir) →
        (∃ off, CallerSaveEntry.ireg ir off ∈ entries) → σ' v = σ v := by
      intro v ir hLoc ⟨off, hMem⟩
      apply hDstOnly; intro hContra
      -- hContra : DAEOpt.instrDef p[pc] = some v
      -- hMem : .ireg ir off ∈ callerSaveEntries ... (some v)
      -- callerSaveEntries filters out entries matching layout v's register
      -- Since layout v = .ireg ir, the filter removes .ireg ir entries
      show False
      simp only [show entries = callerSaveEntries r.layout r.varMap (DAEOpt.instrDef p[pc]) from rfl,
        callerSaveEntries, hContra] at hMem
      rw [List.mem_filter] at hMem
      simp [hLoc] at hMem
    have hEFU : ∀ v fr, r.layout v = some (.freg fr) →
        (∃ off, CallerSaveEntry.freg fr off ∈ entries) → σ' v = σ v := by
      intro v fr hLoc ⟨off, hMem⟩
      apply hDstOnly; intro hContra
      show False
      simp only [show entries = callerSaveEntries r.layout r.varMap (DAEOpt.instrDef p[pc]) from rfl,
        callerSaveEntries, hContra] at hMem
      rw [List.mem_filter] at hMem
      simp [hLoc] at hMem
    -- ARM-level: base instruction stepping + state properties
    have hBaseExists : ∃ s_mid : ArmState,
        ArmSteps r.bodyFlat s_saved s_mid ∧
        s_mid.pc = s_saved.pc + baseInstrs.length ∧
        s_mid.arrayMem = am ∧
        (∀ e ∈ entries, s_mid.stack e.off = (applyCallerSaves entries s).stack e.off) ∧
        (∀ v ir, r.layout v = some (.ireg ir) →
          (∀ off, CallerSaveEntry.ireg ir off ∉ entries) → s_mid.regs ir = (σ' v).encode) ∧
        (∀ v fr, r.layout v = some (.freg fr) →
          (∀ off, CallerSaveEntry.freg fr off ∉ entries) → s_mid.fregs fr = (σ' v).encode) ∧
        (∀ v off, r.layout v = some (.stack off) → s_mid.stack off = (σ' v).encode) := by
      -- Step 0: ExtStateRel for s_saved
      have hEntriesSub' : entries.Sublist (genCallerSaveAll r.layout r.varMap) := by
        show (callerSaveEntries r.layout r.varMap (DAEOpt.instrDef p[pc])).Sublist _
        unfold callerSaveEntries
        cases DAEOpt.instrDef p[pc] with
        | none => exact List.Sublist.refl _
        | some _ => exact List.filter_sublist
      have hRelSaved : ExtStateRel r.layout σ s_saved := by
        show ExtStateRel r.layout σ {applyCallerSaves entries s with pc := s.pc + entries.length}
        intro v loc hv
        exact ExtStateRel.applyCallerSaves_preserved hStateRel entries
          (fun e he v' => spec.callerSaveSpec.1 e (hEntriesSub'.subset he) v') v loc hv
      -- Step 1: case-split on p[pc]
      cases hInstr : p.code[pc] with
      | floatUnary x op y =>
        -- Step 2: unfold verifiedGenInstr for floatUnary
        rw [show p[pc] = p.code[pc] from rfl, hInstr] at hGenInstr
        have hRegConv : RegConventionSafe r.layout := spec.regConventionSafe
        have hInjective : VarLayoutInjective r.layout := spec.injective
        have hNotIregY : ∀ ir, r.layout y ≠ some (.ireg ir) := by
          intro ir h; have := hGenInstr; simp [verifiedGenInstr, h] at this
        have hNotIregX : ∀ ir, r.layout x ≠ some (.ireg ir) := by
          intro ir h; have := hGenInstr
          simp only [verifiedGenInstr, h] at this
          first | (split at this <;> simp_all) | simp_all
        let src_reg := match r.layout y with | some (.freg r) => r | _ => ArmFReg.d0
        let dst_reg := match r.layout x with | some (.freg r) => r | _ => ArmFReg.d0
        have hInstrs : baseInstrs =
            vLoadVarFP r.layout y src_reg ++ [.floatUnaryInstr op dst_reg src_reg] ++
            vStoreVarFP r.layout x dst_reg := by
          simp only [verifiedGenInstr] at hGenInstr
          split at hGenInstr <;> simp_all [src_reg, dst_reg]
          all_goals exact hGenInstr.symm
        -- Phase A: load y into src_reg
        rw [hInstrs] at hCodeBase
        have hCodeLoad := hCodeBase.append_left.append_left
          (l2 := [.floatUnaryInstr op dst_reg src_reg])
        have hMappedY : r.layout y ≠ none := by
          have := spec.layoutComplete pc (by simp [Prog.size_eq] at hPC; exact hPC) y
          rw [show p[pc] = p.code[pc] from rfl, hInstr] at this
          exact this (by simp [TAC.vars])
        obtain ⟨s1, _, hSteps1N, _, hSR1, hRel1, hRegs1, hPC1, hAM1, hFregs1, hStack1⟩ :=
          vLoadVarFP_eff_exec r.bodyFlat r.layout y σ s_saved
            (r.pcMap pc + (entriesToSaves entries).length) .d0
            hRelSaved hRegConv hSavedPC hNotIregY (Or.inl rfl) hMappedY hCodeLoad
        have hSteps1 := ArmStepsN_to_ArmSteps hSteps1N
        -- Phase B: havoc (floatUnaryLibCall)
        have hCodeMid := hCodeBase.append_left.append_right
          (l1 := vLoadVarFP r.layout y src_reg)
        have hCall : r.bodyFlat[s1.pc]? = some (.floatUnaryInstr op dst_reg src_reg) := by
          rw [hPC1]; exact hCodeMid.head
        have hNotNat : op.isNative = false := by
          rw [show p[pc] = p.code[pc] from rfl, hInstr] at hLib
          cases op <;> simp [isLibCallTAC, FloatUnaryOp.isNative] at hLib ⊢
        let newRegs : ArmReg → BitVec 64 := havocRegsFn s1
        let newFregs : ArmFReg → BitVec 64 := havocFRegsFn s1
        let s2 := s1.havocCallerSaved newRegs newFregs |>.setFReg dst_reg (op.eval (s1.fregs src_reg)) |>.nextPC
        have hSteps2 : ArmSteps r.bodyFlat s1 s2 :=
          .single (.floatUnaryLibCall op dst_reg src_reg hCall hNotNat)
        -- Phase C: store dst_reg into x (manual, ExtStateRel broken)
        have hPC2 : s2.pc = s1.pc + 1 := by
          simp [s2, ArmState.nextPC, ArmState.setFReg, ArmState.havocCallerSaved]
        have hCodeStore : CodeAt r.bodyFlat s2.pc (vStoreVarFP r.layout x dst_reg) := by
          have h := hCodeBase.append_right
            (l1 := vLoadVarFP r.layout y src_reg ++ [.floatUnaryInstr op dst_reg src_reg])
          rw [hPC2, hPC1]; simp [List.length_append] at h ⊢; exact h
        -- Step through vStoreVarFP and compose
        -- Shared facts for all sub-cases
        have hPC1' : s1.pc = r.pcMap pc + (entriesToSaves entries).length +
            (vLoadVarFP r.layout y src_reg).length := hPC1
        have hAM2 : s2.arrayMem = s1.arrayMem := by
          simp [s2, ArmState.nextPC, ArmState.setFReg, ArmState.havocCallerSaved]
        have hAMChain : s2.arrayMem = am := by
          rw [hAM2, hAM1]; simp [s_saved, applyCallerSaves_arrayMem, hArrayMem]
        -- Non-entry ireg: shared across all sub-cases (store doesn't touch iregs)
        have hNEI_shared : ∀ v ir, r.layout v = some (.ireg ir) →
            (∀ off, CallerSaveEntry.ireg ir off ∉ entries) → s2.regs ir = (σ' v).encode := by
          intro v ir hLoc hNE
          -- s2.regs ir = (havocCallerSaved ...).regs ir (setFReg/nextPC don't touch regs)
          have : s2.regs ir = (s1.havocCallerSaved newRegs newFregs).regs ir := by
            simp [s2, ArmState.nextPC, ArmState.setFReg]
          rw [this]
          -- ir must be callee-saved (otherwise genCallerSaveAll has an entry, which
          -- passes the callerSaveEntries filter since layout x isn't ireg)
          have hCS : ir.isCallerSaved = false := by
            cases hcs : ir.isCallerSaved with
            | false => rfl
            | true =>
            obtain ⟨_, _, hCoversIreg, _⟩ := spec.callerSaveSpec
            obtain ⟨coff, hMem⟩ := hCoversIreg v ir hLoc hcs
            -- hMem : .ireg ir coff ∈ genCallerSaveAll
            -- Show it passes the callerSaveEntries filter (layout x isn't ireg)
            have hInE : CallerSaveEntry.ireg ir coff ∈ entries := by
              show _ ∈ callerSaveEntries r.layout r.varMap (DAEOpt.instrDef p[pc])
              rw [show p[pc] = p.code[pc] from rfl, hInstr]
              simp only [callerSaveEntries, DAEOpt.instrDef]
              rw [List.mem_filter]
              refine ⟨hMem, ?_⟩
              rcases hlx2 : r.layout x with _ | ⟨off2 | ir2 | fr2⟩ <;> simp [hlx2]
              exact absurd hlx2 (hNotIregX ir2)
            exact absurd hInE (hNE coff)
          -- Callee-saved: havocCallerSaved preserves ir
          show (fun r => if r.isCallerSaved then newRegs r else s1.regs r) ir = _
          simp [hCS]
          -- s1.regs = s_saved.regs = s.regs (load doesn't touch iregs)
          rw [hRegs1]; simp [s_saved, applyCallerSaves_regs]
          -- s.regs ir = (σ v).encode by hStateRel
          have hVal := hStateRel v (.ireg ir) hLoc; simp at hVal; rw [hVal]
          -- σ' v = σ v since dst (x) is not v (x is freg/stack, v is ireg)
          have hne : DAEOpt.instrDef p[pc] ≠ some v := by
            rw [show p[pc] = p.code[pc] from rfl, hInstr]; simp [DAEOpt.instrDef]
            intro h; rw [← h] at hLoc; exact absurd hLoc (hNotIregX ir)
          rw [hDstOnly v hne]
        -- Save slots: s2.stack = (applyCallerSaves entries s).stack
        have hStack2 : s2.stack = (applyCallerSaves entries s).stack := by
          simp [s2, ArmState.nextPC, ArmState.setFReg, ArmState.havocCallerSaved_stack, hStack1, s_saved]
        -- TAC result: extract σ' x and connect to ARM
        obtain ⟨f, hfy, hσx⟩ := hLibStep x op y hInstr
        -- ARM result: s2.fregs dst_reg = op.eval f = (σ' x).encode
        have hSR1' : s1.fregs src_reg = (σ y).encode := hSR1
        have hArmResult : s2.fregs dst_reg = (σ' x).encode := by
          simp [s2, ArmState.nextPC, ArmState.setFReg, ArmState.havocCallerSaved]
          rw [hSR1', hfy, hσx]; simp [Value.encode]
        rcases hlx : r.layout x with _ | ⟨off | ir | fr⟩
        · -- none: vStoreVarFP = [], s_mid = s2
          have hRC2 : ∀ e ∈ entries, s2.stack e.off = (applyCallerSaves entries s).stack e.off :=
            fun e _ => by rw [hStack2]
          refine ⟨s2, hSteps1.trans hSteps2, ?_, hAMChain, hRC2, hNEI_shared, ?_, ?_⟩
          · -- PC
            rw [hPC2, hPC1', hSavedPC, hInstrs]; simp [vStoreVarFP, hlx, List.length_append]; omega
          · -- non-entry freg
            intro v fr hLoc hNE
            -- dst_reg = .d0 (layout x = none), so fr ≠ .d0 by regConventionSafe
            have hDR : dst_reg = .d0 := by simp [dst_reg, hlx]
            have hfrne : fr ≠ ArmFReg.d0 := fun h => absurd (h ▸ hLoc) (hRegConv.not_d0 v)
            -- s2.fregs fr = (havocCallerSaved ...).fregs fr (setFReg only changed .d0)
            have : s2.fregs fr = (s1.havocCallerSaved newRegs newFregs).fregs fr := by
              simp [s2, ArmState.nextPC, ArmState.setFReg, hDR, hfrne]
            rw [this]
            -- fr callee-saved (same argument as ireg)
            have hCS : fr.isCallerSaved = false := by
              cases hcs : fr.isCallerSaved with
              | false => rfl
              | true =>
              obtain ⟨_, _, _, hCoversFreg, _⟩ := spec.callerSaveSpec
              obtain ⟨coff, hMem⟩ := hCoversFreg v fr hLoc hcs
              have hInE : CallerSaveEntry.freg fr coff ∈ entries := by
                show _ ∈ callerSaveEntries r.layout r.varMap (DAEOpt.instrDef p[pc])
                rw [show p[pc] = p.code[pc] from rfl, hInstr]
                simp only [callerSaveEntries, DAEOpt.instrDef]
                rw [List.mem_filter]
                exact ⟨hMem, by simp [hlx]⟩
              exact absurd hInE (hNE coff)
            show (fun r => if r.isCallerSaved then newFregs r else s1.fregs r) fr = _
            simp [hCS]
            -- s1.fregs fr preserved from load (fr ≠ src_reg or fr = src_reg)
            -- Use hRel1 (ExtStateRel for s1) since load preserves it
            have hVal := hRel1 v (.freg fr) hLoc; simp at hVal; rw [hVal]
            -- σ' v = σ v (v ≠ x since layout x = none)
            have hne : DAEOpt.instrDef p[pc] ≠ some v := by
              rw [show p[pc] = p.code[pc] from rfl, hInstr]; simp [DAEOpt.instrDef]
              intro h; rw [← h] at hLoc; simp [hlx] at hLoc
            rw [hDstOnly v hne]
          · -- stack vars
            intro v off' hLoc
            rw [hStack2]
            have hVal := hRelSaved v (.stack off') hLoc; simp at hVal; rw [hVal]
            have hne : DAEOpt.instrDef p[pc] ≠ some v := by
              rw [show p[pc] = p.code[pc] from rfl, hInstr]; simp [DAEOpt.instrDef]
              intro h; rw [← h] at hLoc; simp [hlx] at hLoc
            rw [hDstOnly v hne]
        · -- stack off: vStoreVarFP = [.fstr dst_reg off]
          simp [vStoreVarFP, hlx] at hCodeStore
          have hFstr : r.bodyFlat[s2.pc]? = some (.fstr dst_reg off) := hCodeStore.head
          let s3 := (s2.setStack off (s2.fregs dst_reg)).nextPC
          have hSteps3 : ArmSteps r.bodyFlat s2 s3 :=
            .single (.fstr dst_reg off hFstr)
          have hRegs3 : s3.regs = s2.regs := by simp [s3, ArmState.nextPC, ArmState.setStack]
          have hNEI3 : ∀ v ir, r.layout v = some (.ireg ir) →
              (∀ off, CallerSaveEntry.ireg ir off ∉ entries) → s3.regs ir = (σ' v).encode :=
            fun v ir hLoc hNE => hRegs3 ▸ hNEI_shared v ir hLoc hNE
          have hRC3 : ∀ e ∈ entries, s3.stack e.off = (applyCallerSaves entries s).stack e.off := by
            intro e he
            simp [s3, ArmState.nextPC, ArmState.setStack]
            -- e.off ≠ off because off is a layout offset for x, and save slots are fresh
            have hne : e.off ≠ off := by
              intro heq
              exact spec.callerSaveSpec.1 e (hEntriesSub'.subset he) x (heq ▸ hlx)
            simp [hne, hStack2]
          refine ⟨s3, hSteps1.trans (hSteps2.trans hSteps3), ?_, ?_, hRC3, hNEI3, ?_, ?_⟩
          · -- PC
            simp [s3, ArmState.nextPC, ArmState.setStack]
            rw [hPC2, hPC1', hSavedPC, hInstrs]; simp [vStoreVarFP, hlx, List.length_append]; omega
          · -- arrayMem
            simp [s3, ArmState.nextPC, ArmState.setStack, hAMChain]
          · -- non-entry freg (s3.fregs = s2.fregs since setStack doesn't touch fregs)
            intro v fr hLoc hNE
            have hFregs3 : s3.fregs = s2.fregs := by simp [s3, ArmState.nextPC, ArmState.setStack]
            rw [hFregs3]
            -- dst_reg = .d0 (layout x = stack, not freg)
            have hDR : dst_reg = .d0 := by simp [dst_reg, hlx]
            have hfrne : fr ≠ ArmFReg.d0 := fun h => absurd (h ▸ hLoc) (hRegConv.not_d0 v)
            have : s2.fregs fr = (s1.havocCallerSaved newRegs newFregs).fregs fr := by
              simp [s2, ArmState.nextPC, ArmState.setFReg, hDR, hfrne]
            rw [this]
            have hCS : fr.isCallerSaved = false := by
              cases hcs : fr.isCallerSaved with
              | false => rfl
              | true =>
              obtain ⟨_, _, _, hCoversFreg, _⟩ := spec.callerSaveSpec
              obtain ⟨coff, hMem⟩ := hCoversFreg v fr hLoc hcs
              have hInE : CallerSaveEntry.freg fr coff ∈ entries := by
                show _ ∈ callerSaveEntries r.layout r.varMap (DAEOpt.instrDef p[pc])
                rw [show p[pc] = p.code[pc] from rfl, hInstr]
                simp only [callerSaveEntries, DAEOpt.instrDef]
                rw [List.mem_filter]
                exact ⟨hMem, by simp [hlx]⟩
              exact absurd hInE (hNE coff)
            show (fun r => if r.isCallerSaved then newFregs r else s1.fregs r) fr = _
            simp [hCS]
            have hVal := hRel1 v (.freg fr) hLoc; simp at hVal; rw [hVal]
            have hne : DAEOpt.instrDef p[pc] ≠ some v := by
              rw [show p[pc] = p.code[pc] from rfl, hInstr]; simp [DAEOpt.instrDef]
              intro h; subst h; rw [hlx] at hLoc; cases hLoc
            rw [hDstOnly v hne]
          · -- stack vars
            intro v off' hLoc
            simp [s3, ArmState.nextPC, ArmState.setStack]
            by_cases hvo : off' = off
            · -- v maps to same offset as x → v = x by injectivity
              have hvx : v = x := hInjective v x (.stack off) (hvo ▸ hLoc) hlx
              subst hvx
              simp [hvo]; exact hArmResult
            · -- different offset → use s2.stack
              simp [hvo, hStack2]
              have hVal := hRelSaved v (.stack off') hLoc; simp at hVal; rw [hVal]
              have hvx : v ≠ x := by
                intro h; subst h; rw [hlx] at hLoc; cases hLoc; exact hvo rfl
              have hne : DAEOpt.instrDef p[pc] ≠ some v := by
                rw [show p[pc] = p.code[pc] from rfl, hInstr]; simp [DAEOpt.instrDef]; exact hvx.symm
              rw [hDstOnly v hne]
        · -- ireg: impossible
          exact absurd hlx (hNotIregX ir)
        · -- freg r: vStoreVarFP = fmovRR or []
          by_cases hEq : fr == dst_reg
          · -- fr = dst_reg: vStoreVarFP = [], s_mid = s2
            simp [vStoreVarFP, hlx, hEq] at hCodeStore
            have hRC2 : ∀ e ∈ entries, s2.stack e.off = (applyCallerSaves entries s).stack e.off :=
              fun e _ => by rw [hStack2]
            refine ⟨s2, hSteps1.trans hSteps2, ?_, hAMChain, hRC2, hNEI_shared, ?_, ?_⟩
            · -- PC
              rw [hPC2, hPC1', hSavedPC, hInstrs]
              simp [vStoreVarFP, hlx, hEq, List.length_append]; omega
            · -- non-entry freg (s_mid = s2, dst_reg = fr)
              intro v fr' hLoc hNE
              have hDR : dst_reg = fr := by simp [dst_reg, hlx]
              by_cases hff : fr' = fr
              · -- fr' = fr = dst_reg → v = x by injectivity
                subst hff; have := hInjective v x _ hLoc hlx; subst this
                rw [hDR] at hArmResult; exact hArmResult
              · -- fr' ≠ fr → setFReg didn't touch fr'
                have : s2.fregs fr' = (s1.havocCallerSaved newRegs newFregs).fregs fr' := by
                  simp [s2, ArmState.nextPC, ArmState.setFReg, hDR, hff]
                rw [this]
                have hCS : fr'.isCallerSaved = false := by
                  cases hcs : fr'.isCallerSaved with
                  | false => rfl
                  | true =>
                  obtain ⟨_, _, _, hCoversFreg, _⟩ := spec.callerSaveSpec
                  obtain ⟨coff, hMem⟩ := hCoversFreg v fr' hLoc hcs
                  have hInE : CallerSaveEntry.freg fr' coff ∈ entries := by
                    show _ ∈ callerSaveEntries r.layout r.varMap (DAEOpt.instrDef p[pc])
                    rw [show p[pc] = p.code[pc] from rfl, hInstr]
                    simp only [callerSaveEntries, DAEOpt.instrDef]
                    rw [List.mem_filter]
                    refine ⟨hMem, ?_⟩; simp [hlx, hff]
                  exact absurd hInE (hNE coff)
                show (fun r => if r.isCallerSaved then newFregs r else s1.fregs r) fr' = _
                simp [hCS]
                have hVal := hRel1 v (.freg fr') hLoc; simp at hVal; rw [hVal]
                have hne : DAEOpt.instrDef p[pc] ≠ some v := by
                  rw [show p[pc] = p.code[pc] from rfl, hInstr]; simp [DAEOpt.instrDef]
                  intro h; subst h; rw [hlx] at hLoc; cases hLoc; exact hff rfl
                rw [hDstOnly v hne]
            · -- stack vars
              intro v off' hLoc; rw [hStack2]
              have hVal := hRelSaved v (.stack off') hLoc; simp at hVal; rw [hVal]
              have hne : DAEOpt.instrDef p[pc] ≠ some v := by
                rw [show p[pc] = p.code[pc] from rfl, hInstr]; simp [DAEOpt.instrDef]
                intro h; subst h; rw [hlx] at hLoc; cases hLoc
              rw [hDstOnly v hne]
          · -- fr ≠ dst_reg: vStoreVarFP = [.fmovRR fr dst_reg]
            simp [vStoreVarFP, hlx, hEq] at hCodeStore
            have hFmov : r.bodyFlat[s2.pc]? = some (.fmovRR fr dst_reg) := hCodeStore.head
            let s3 := (s2.setFReg fr (s2.fregs dst_reg)).nextPC
            have hSteps3 : ArmSteps r.bodyFlat s2 s3 :=
              .single (.fmovRR fr dst_reg hFmov)
            have hRegs3 : s3.regs = s2.regs := by simp [s3, ArmState.nextPC, ArmState.setFReg]
            have hNEI3 : ∀ v ir, r.layout v = some (.ireg ir) →
                (∀ off, CallerSaveEntry.ireg ir off ∉ entries) → s3.regs ir = (σ' v).encode :=
              fun v ir hLoc hNE => hRegs3 ▸ hNEI_shared v ir hLoc hNE
            have hStack3 : s3.stack = s2.stack := by simp [s3, ArmState.nextPC, ArmState.setFReg]
            have hRC3 : ∀ e ∈ entries, s3.stack e.off = (applyCallerSaves entries s).stack e.off :=
              fun e _ => by rw [hStack3, hStack2]
            refine ⟨s3, hSteps1.trans (hSteps2.trans hSteps3), ?_, ?_, hRC3, hNEI3, ?_, ?_⟩
            · -- PC
              simp [s3, ArmState.nextPC, ArmState.setFReg]
              rw [hPC2, hPC1', hSavedPC, hInstrs]
              simp [vStoreVarFP, hlx, hEq, List.length_append]; omega
            · -- arrayMem
              simp [s3, ArmState.nextPC, ArmState.setFReg, hAMChain]
            · -- non-entry freg (s3 = setFReg fr ... of s2)
              intro v fr' hLoc hNE
              have hDR : dst_reg = fr := by simp [dst_reg, hlx]
              by_cases hff : fr' = fr
              · -- fr' = fr → v = x, s3.fregs fr = s2.fregs dst_reg = (σ' x).encode
                have hvx := hInjective v x _ (hff ▸ hLoc) hlx; subst hvx
                simp [s3, ArmState.nextPC, ArmState.setFReg, hff]
                exact hArmResult
              · -- fr' ≠ fr → s3.fregs fr' = s2.fregs fr'
                have : s3.fregs fr' = s2.fregs fr' := by
                  simp [s3, ArmState.nextPC, ArmState.setFReg, hff]
                rw [this]
                have : s2.fregs fr' = (s1.havocCallerSaved newRegs newFregs).fregs fr' := by
                  simp [s2, ArmState.nextPC, ArmState.setFReg, hDR, hff]
                rw [this]
                have hCS : fr'.isCallerSaved = false := by
                  cases hcs : fr'.isCallerSaved with
                  | false => rfl
                  | true =>
                  obtain ⟨_, _, _, hCoversFreg, _⟩ := spec.callerSaveSpec
                  obtain ⟨coff, hMem⟩ := hCoversFreg v fr' hLoc hcs
                  have hInE : CallerSaveEntry.freg fr' coff ∈ entries := by
                    show _ ∈ callerSaveEntries r.layout r.varMap (DAEOpt.instrDef p[pc])
                    rw [show p[pc] = p.code[pc] from rfl, hInstr]
                    simp only [callerSaveEntries, DAEOpt.instrDef]
                    rw [List.mem_filter]
                    refine ⟨hMem, ?_⟩; simp [hlx, hff]
                  exact absurd hInE (hNE coff)
                show (fun r => if r.isCallerSaved then newFregs r else s1.fregs r) fr' = _
                simp [hCS]
                have hVal := hRel1 v (.freg fr') hLoc; simp at hVal; rw [hVal]
                have hne : DAEOpt.instrDef p[pc] ≠ some v := by
                  rw [show p[pc] = p.code[pc] from rfl, hInstr]; simp [DAEOpt.instrDef]
                  intro h; subst h; rw [hlx] at hLoc; cases hLoc; exact hff rfl
                rw [hDstOnly v hne]
            · -- stack vars
              intro v off' hLoc; rw [hStack3, hStack2]
              have hVal := hRelSaved v (.stack off') hLoc; simp at hVal; rw [hVal]
              have hne : DAEOpt.instrDef p[pc] ≠ some v := by
                rw [show p[pc] = p.code[pc] from rfl, hInstr]; simp [DAEOpt.instrDef]
                intro h; subst h; rw [hlx] at hLoc; cases hLoc
              rw [hDstOnly v hne]
      | fbinop x fop y z =>
        cases fop with
        | fpow =>
          -- Step 2: unfold verifiedGenInstr for fbinop fpow
          rw [show p[pc] = p.code[pc] from rfl, hInstr] at hGenInstr
          have hRegConv : RegConventionSafe r.layout := spec.regConventionSafe
          have hInjective : VarLayoutInjective r.layout := spec.injective
          have hNotIregY : ∀ ir, r.layout y ≠ some (.ireg ir) := by
            intro ir h; have := hGenInstr; simp [verifiedGenInstr, h] at this
          have hNotIregZ : ∀ ir, r.layout z ≠ some (.ireg ir) := by
            intro ir h; have := hGenInstr; simp [verifiedGenInstr, h] at this
          have hNotIregX : ∀ ir, r.layout x ≠ some (.ireg ir) := by
            intro ir h; have := hGenInstr; simp [verifiedGenInstr, h] at this
          let lv_reg := match r.layout y with | some (.freg r) => r | _ => ArmFReg.d1
          let rv_reg := match r.layout z with | some (.freg r) => r | _ => ArmFReg.d2
          let dst_reg := match r.layout x with | some (.freg r) => r | _ => ArmFReg.d0
          have hInstrs : baseInstrs =
              vLoadVarFP r.layout y lv_reg ++ vLoadVarFP r.layout z rv_reg ++
              [.callBinF .fpow dst_reg lv_reg rv_reg] ++
              vStoreVarFP r.layout x dst_reg := by
            have h := hGenInstr
            simp only [verifiedGenInstr] at h
            -- Eliminate ireg branches by case-splitting each layout
            rcases hly : r.layout y with _ | ⟨ir | fr | off⟩
            all_goals rcases hlz : r.layout z with _ | ⟨ir | fr | off⟩
            all_goals rcases hlx : r.layout x with _ | ⟨ir | fr | off⟩
            all_goals (try { exact absurd hly (hNotIregY _) })
            all_goals (try { exact absurd hlz (hNotIregZ _) })
            all_goals (try { exact absurd hlx (hNotIregX _) })
            all_goals (simp [hly, hlz, hlx, lv_reg, rv_reg, dst_reg] at h ⊢; exact h.symm)
          -- Phase A: load y into lv_reg, then z into rv_reg
          rw [hInstrs] at hCodeBase
          have hCodeLoad1 := hCodeBase.append_left.append_left.append_left
            (l2 := vLoadVarFP r.layout z rv_reg)
          have hMappedY : r.layout y ≠ none := by
            have := spec.layoutComplete pc (by simp [Prog.size_eq] at hPC; exact hPC) y
            rw [show p[pc] = p.code[pc] from rfl, hInstr] at this
            exact this (by simp [TAC.vars])
          obtain ⟨s1, _, hSteps1N, _, hSR1, hRel1, hRegs1, hPC1, hAM1, hFregs1, hStack1⟩ :=
            vLoadVarFP_eff_exec r.bodyFlat r.layout y σ s_saved
              (r.pcMap pc + (entriesToSaves entries).length) .d1
              hRelSaved hRegConv hSavedPC hNotIregY (Or.inr (Or.inl rfl)) hMappedY hCodeLoad1
          have hSteps1 := ArmStepsN_to_ArmSteps hSteps1N
          -- Second load: z into rv_reg
          have hCodeLoad2 : CodeAt r.bodyFlat s1.pc (vLoadVarFP r.layout z rv_reg) := by
            rw [hPC1]
            exact hCodeBase.append_left.append_left.append_right
              (l1 := vLoadVarFP r.layout y lv_reg)
          have hMappedZ : r.layout z ≠ none := by
            have := spec.layoutComplete pc (by simp [Prog.size_eq] at hPC; exact hPC) z
            rw [show p[pc] = p.code[pc] from rfl, hInstr] at this
            exact this (by simp [TAC.vars])
          obtain ⟨s1b, _, hSteps1bN, _, hSR1b, hRel1b, hRegs1b, hPC1b, hAM1b, hFregs1b, hStack1b⟩ :=
            vLoadVarFP_eff_exec r.bodyFlat r.layout z σ s1
              s1.pc .d2
              hRel1 hRegConv rfl hNotIregZ (Or.inr (Or.inr rfl)) hMappedZ hCodeLoad2
          have hSteps1b := ArmStepsN_to_ArmSteps hSteps1bN
          -- Phase B: havoc (callBinF)
          have hCodeMid := hCodeBase.append_left.append_right
            (l1 := vLoadVarFP r.layout y lv_reg ++ vLoadVarFP r.layout z rv_reg)
          have hPC1' : s1.pc = r.pcMap pc + (entriesToSaves entries).length +
              (vLoadVarFP r.layout y lv_reg).length := hPC1
          have hPC1b' : s1b.pc = s1.pc + (vLoadVarFP r.layout z rv_reg).length := hPC1b
          have hCall : r.bodyFlat[s1b.pc]? = some (.callBinF .fpow dst_reg lv_reg rv_reg) := by
            rw [hPC1b', hPC1']
            have hIdx : r.pcMap pc + (entriesToSaves entries).length +
                (vLoadVarFP r.layout y lv_reg).length + (vLoadVarFP r.layout z rv_reg).length =
              r.pcMap pc + (entriesToSaves entries).length +
                (vLoadVarFP r.layout y lv_reg ++ vLoadVarFP r.layout z rv_reg).length := by
              simp [List.length_append]; omega
            rw [hIdx]; exact hCodeMid.head
          let newRegs : ArmReg → BitVec 64 := havocRegsFn s1b
          let newFregs : ArmFReg → BitVec 64 := havocFRegsFn s1b
          let s2 := s1b.havocCallerSaved newRegs newFregs |>.setFReg dst_reg
            (FloatBinOp.eval .fpow (s1b.fregs lv_reg) (s1b.fregs rv_reg)) |>.nextPC
          have hSteps2 : ArmSteps r.bodyFlat s1b s2 :=
            .single (.callBinF .fpow dst_reg lv_reg rv_reg hCall)
          -- Phase C setup: shared facts
          have hPC2 : s2.pc = s1b.pc + 1 := by
            simp [s2, ArmState.nextPC, ArmState.setFReg, ArmState.havocCallerSaved]
          have hAM2 : s2.arrayMem = s1b.arrayMem := by
            simp [s2, ArmState.nextPC, ArmState.setFReg, ArmState.havocCallerSaved]
          have hAMChain : s2.arrayMem = am := by
            rw [hAM2, hAM1b, hAM1]; simp [s_saved, applyCallerSaves_arrayMem, hArrayMem]
          have hStack2 : s2.stack = (applyCallerSaves entries s).stack := by
            simp [s2, ArmState.nextPC, ArmState.setFReg, ArmState.havocCallerSaved_stack,
              hStack1b, hStack1, s_saved]
          -- TAC result
          obtain ⟨fy, fz, hfy, hfz, hσx⟩ := hLibStepBin x y z hInstr
          have hSR1' : s1.fregs lv_reg = (σ y).encode := hSR1
          have hSR1b' : s1b.fregs rv_reg = (σ z).encode := hSR1b
          -- s1b.fregs lv_reg = (σ y).encode (preserved across second load)
          have hLvPreserved : s1b.fregs lv_reg = (σ y).encode := by
            rcases hly : r.layout y with _ | ⟨offy | iry | fry⟩
            · exact absurd hly hMappedY
            · -- y in stack: lv_reg = .d1, second load didn't touch .d1
              simp [lv_reg, hly]
              have : (ArmFReg.d1 : ArmFReg) ≠ rv_reg := by
                rcases hlz : r.layout z with _ | ⟨_ | _ | frz⟩ <;>
                  simp [rv_reg, hlz]
                exact fun h => absurd (h ▸ hlz) (hRegConv.not_d1 z)
              rw [hFregs1b _ this]
              have := hSR1'; simp [lv_reg, hly] at this; exact this
            · exact absurd hly (hNotIregY iry)
            · -- y in freg: use hRel1b (ExtStateRel preserved)
              have : lv_reg = fry := by simp [lv_reg, hly]
              rw [this]; exact hRel1b y (.freg fry) hly
          have hArmResult : s2.fregs dst_reg = (σ' x).encode := by
            simp [s2, ArmState.nextPC, ArmState.setFReg, ArmState.havocCallerSaved]
            rw [hLvPreserved, hSR1b', hfy, hfz, hσx]; simp [Value.encode]
          -- Non-entry ireg: shared (store doesn't touch iregs)
          have hNEI_shared : ∀ v ir, r.layout v = some (.ireg ir) →
              (∀ off, CallerSaveEntry.ireg ir off ∉ entries) → s2.regs ir = (σ' v).encode := by
            intro v ir hLoc hNE
            have : s2.regs ir = (s1b.havocCallerSaved newRegs newFregs).regs ir := by
              simp [s2, ArmState.nextPC, ArmState.setFReg]
            rw [this]
            have hCS : ir.isCallerSaved = false := by
              cases hcs : ir.isCallerSaved with
              | false => rfl
              | true =>
              obtain ⟨_, _, hCoversIreg, _⟩ := spec.callerSaveSpec
              obtain ⟨coff, hMem⟩ := hCoversIreg v ir hLoc hcs
              have hInE : CallerSaveEntry.ireg ir coff ∈ entries := by
                show _ ∈ callerSaveEntries r.layout r.varMap (DAEOpt.instrDef p[pc])
                rw [show p[pc] = p.code[pc] from rfl, hInstr]
                simp only [callerSaveEntries, DAEOpt.instrDef]
                rw [List.mem_filter]
                refine ⟨hMem, ?_⟩
                rcases hlx2 : r.layout x with _ | ⟨off2 | ir2 | fr2⟩ <;> simp [hlx2]
                exact absurd hlx2 (hNotIregX ir2)
              exact absurd hInE (hNE coff)
            show (fun r => if r.isCallerSaved then newRegs r else s1b.regs r) ir = _
            simp [hCS]
            rw [hRegs1b, hRegs1]; simp [s_saved, applyCallerSaves_regs]
            have hVal := hStateRel v (.ireg ir) hLoc; simp at hVal; rw [hVal]
            have hne : DAEOpt.instrDef p[pc] ≠ some v := by
              rw [show p[pc] = p.code[pc] from rfl, hInstr]; simp [DAEOpt.instrDef]
              intro h; rw [← h] at hLoc; exact absurd hLoc (hNotIregX ir)
            rw [hDstOnly v hne]
          -- Phase C: store + CodeAt
          have hCodeStore : CodeAt r.bodyFlat s2.pc (vStoreVarFP r.layout x dst_reg) := by
            have h := hCodeBase.append_right
              (l1 := vLoadVarFP r.layout y lv_reg ++ vLoadVarFP r.layout z rv_reg ++
                [.callBinF .fpow dst_reg lv_reg rv_reg])
            rw [hPC2, hPC1b', hPC1']
            have hIdx : r.pcMap pc + (entriesToSaves entries).length +
                (vLoadVarFP r.layout y lv_reg).length +
                (vLoadVarFP r.layout z rv_reg).length + 1 =
              r.pcMap pc + (entriesToSaves entries).length +
                (vLoadVarFP r.layout y lv_reg ++ vLoadVarFP r.layout z rv_reg ++
                  [ArmInstr.callBinF .fpow dst_reg lv_reg rv_reg]).length := by
              simp [List.length_append]; omega
            rw [hIdx]; exact h
          -- rcases on layout x
          rcases hlx : r.layout x with _ | ⟨off | ir | fr⟩
          · -- none
            have hRC2 : ∀ e ∈ entries, s2.stack e.off = (applyCallerSaves entries s).stack e.off :=
              fun e _ => by rw [hStack2]
            refine ⟨s2, (hSteps1.trans hSteps1b).trans hSteps2, ?_, hAMChain, hRC2, hNEI_shared, ?_, ?_⟩
            · rw [hPC2, hPC1b', hPC1', hSavedPC, hInstrs]
              simp [vStoreVarFP, hlx, List.length_append]; omega
            · -- non-entry freg
              intro v fr hLoc hNE
              have hDR : dst_reg = .d0 := by simp [dst_reg, hlx]
              have hfrne : fr ≠ ArmFReg.d0 := fun h => absurd (h ▸ hLoc) (hRegConv.not_d0 v)
              have : s2.fregs fr = (s1b.havocCallerSaved newRegs newFregs).fregs fr := by
                simp [s2, ArmState.nextPC, ArmState.setFReg, hDR, hfrne]
              rw [this]
              have hCS : fr.isCallerSaved = false := by
                cases hcs : fr.isCallerSaved with
                | false => rfl
                | true =>
                obtain ⟨_, _, _, hCoversFreg, _⟩ := spec.callerSaveSpec
                obtain ⟨coff, hMem⟩ := hCoversFreg v fr hLoc hcs
                have hInE : CallerSaveEntry.freg fr coff ∈ entries := by
                  show _ ∈ callerSaveEntries r.layout r.varMap (DAEOpt.instrDef p[pc])
                  rw [show p[pc] = p.code[pc] from rfl, hInstr]
                  simp only [callerSaveEntries, DAEOpt.instrDef]
                  rw [List.mem_filter]
                  exact ⟨hMem, by simp [hlx]⟩
                exact absurd hInE (hNE coff)
              show (fun r => if r.isCallerSaved then newFregs r else s1b.fregs r) fr = _
              simp [hCS]
              have hVal := hRel1b v (.freg fr) hLoc; simp at hVal; rw [hVal]
              have hne : DAEOpt.instrDef p[pc] ≠ some v := by
                rw [show p[pc] = p.code[pc] from rfl, hInstr]; simp [DAEOpt.instrDef]
                intro h; subst h; simp [hlx] at hLoc
              rw [hDstOnly v hne]
            · -- stack vars
              intro v off' hLoc
              rw [hStack2]
              have hVal := hRelSaved v (.stack off') hLoc; simp at hVal; rw [hVal]
              have hne : DAEOpt.instrDef p[pc] ≠ some v := by
                rw [show p[pc] = p.code[pc] from rfl, hInstr]; simp [DAEOpt.instrDef]
                intro h; subst h; simp [hlx] at hLoc
              rw [hDstOnly v hne]
          · -- stack off
            simp [vStoreVarFP, hlx] at hCodeStore
            have hFstr : r.bodyFlat[s2.pc]? = some (.fstr dst_reg off) := hCodeStore.head
            let s3 := (s2.setStack off (s2.fregs dst_reg)).nextPC
            have hSteps3 : ArmSteps r.bodyFlat s2 s3 := .single (.fstr dst_reg off hFstr)
            have hRegs3 : s3.regs = s2.regs := by simp [s3, ArmState.nextPC, ArmState.setStack]
            have hNEI3 := fun v ir hLoc hNE => hRegs3 ▸ hNEI_shared v ir hLoc hNE
            have hRC3 : ∀ e ∈ entries, s3.stack e.off = (applyCallerSaves entries s).stack e.off := by
              intro e he; simp [s3, ArmState.nextPC, ArmState.setStack]
              have hne : e.off ≠ off := by
                intro heq; exact spec.callerSaveSpec.1 e (hEntriesSub'.subset he) x (heq ▸ hlx)
              simp [hne, hStack2]
            refine ⟨s3, (hSteps1.trans hSteps1b).trans (hSteps2.trans hSteps3), ?_, ?_, hRC3, hNEI3, ?_, ?_⟩
            · simp [s3, ArmState.nextPC, ArmState.setStack]
              rw [hPC2, hPC1b', hPC1', hSavedPC, hInstrs]
              simp [vStoreVarFP, hlx, List.length_append]; omega
            · simp [s3, ArmState.nextPC, ArmState.setStack, hAMChain]
            · -- non-entry freg
              intro v fr hLoc hNE
              have hFregs3 : s3.fregs = s2.fregs := by simp [s3, ArmState.nextPC, ArmState.setStack]
              rw [hFregs3]
              have hDR : dst_reg = .d0 := by simp [dst_reg, hlx]
              have hfrne : fr ≠ ArmFReg.d0 := fun h => absurd (h ▸ hLoc) (hRegConv.not_d0 v)
              have : s2.fregs fr = (s1b.havocCallerSaved newRegs newFregs).fregs fr := by
                simp [s2, ArmState.nextPC, ArmState.setFReg, hDR, hfrne]
              rw [this]
              have hCS : fr.isCallerSaved = false := by
                cases hcs : fr.isCallerSaved with
                | false => rfl
                | true =>
                obtain ⟨_, _, _, hCoversFreg, _⟩ := spec.callerSaveSpec
                obtain ⟨coff, hMem⟩ := hCoversFreg v fr hLoc hcs
                have hInE : CallerSaveEntry.freg fr coff ∈ entries := by
                  show _ ∈ callerSaveEntries r.layout r.varMap (DAEOpt.instrDef p[pc])
                  rw [show p[pc] = p.code[pc] from rfl, hInstr]
                  simp only [callerSaveEntries, DAEOpt.instrDef]
                  rw [List.mem_filter]; exact ⟨hMem, by simp [hlx]⟩
                exact absurd hInE (hNE coff)
              show (fun r => if r.isCallerSaved then newFregs r else s1b.fregs r) fr = _
              simp [hCS]
              have hVal := hRel1b v (.freg fr) hLoc; simp at hVal; rw [hVal]
              have hne : DAEOpt.instrDef p[pc] ≠ some v := by
                rw [show p[pc] = p.code[pc] from rfl, hInstr]; simp [DAEOpt.instrDef]
                intro h; subst h; rw [hlx] at hLoc; cases hLoc
              rw [hDstOnly v hne]
            · -- stack vars
              intro v off' hLoc
              simp [s3, ArmState.nextPC, ArmState.setStack]
              by_cases hvo : off' = off
              · have hvx := hInjective v x (.stack off) (hvo ▸ hLoc) hlx; subst hvx
                simp [hvo]; exact hArmResult
              · simp [hvo, hStack2]
                have hVal := hRelSaved v (.stack off') hLoc; simp at hVal; rw [hVal]
                have hvx : v ≠ x := by
                  intro h; subst h; rw [hlx] at hLoc; cases hLoc; exact hvo rfl
                have hne : DAEOpt.instrDef p[pc] ≠ some v := by
                  rw [show p[pc] = p.code[pc] from rfl, hInstr]; simp [DAEOpt.instrDef]; exact hvx.symm
                rw [hDstOnly v hne]
          · exact absurd hlx (hNotIregX ir)
          · -- freg fr
            by_cases hEq : fr == dst_reg
            · -- fr = dst_reg
              simp [vStoreVarFP, hlx, hEq] at hCodeStore
              have hRC2 : ∀ e ∈ entries, s2.stack e.off = (applyCallerSaves entries s).stack e.off :=
                fun e _ => by rw [hStack2]
              refine ⟨s2, (hSteps1.trans hSteps1b).trans hSteps2, ?_, hAMChain, hRC2, hNEI_shared, ?_, ?_⟩
              · rw [hPC2, hPC1b', hPC1', hSavedPC, hInstrs]
                simp [vStoreVarFP, hlx, hEq, List.length_append]; omega
              · -- non-entry freg
                intro v fr' hLoc hNE
                have hDR : dst_reg = fr := by simp [dst_reg, hlx]
                by_cases hff : fr' = fr
                · subst hff; have := hInjective v x _ hLoc hlx; subst this
                  rw [hDR] at hArmResult; exact hArmResult
                · have : s2.fregs fr' = (s1b.havocCallerSaved newRegs newFregs).fregs fr' := by
                    simp [s2, ArmState.nextPC, ArmState.setFReg, hDR, hff]
                  rw [this]
                  have hCS : fr'.isCallerSaved = false := by
                    cases hcs : fr'.isCallerSaved with
                    | false => rfl
                    | true =>
                    obtain ⟨_, _, _, hCoversFreg, _⟩ := spec.callerSaveSpec
                    obtain ⟨coff, hMem⟩ := hCoversFreg v fr' hLoc hcs
                    have hInE : CallerSaveEntry.freg fr' coff ∈ entries := by
                      show _ ∈ callerSaveEntries r.layout r.varMap (DAEOpt.instrDef p[pc])
                      rw [show p[pc] = p.code[pc] from rfl, hInstr]
                      simp only [callerSaveEntries, DAEOpt.instrDef]
                      rw [List.mem_filter]; refine ⟨hMem, ?_⟩; simp [hlx, hff]
                    exact absurd hInE (hNE coff)
                  show (fun r => if r.isCallerSaved then newFregs r else s1b.fregs r) fr' = _
                  simp [hCS]
                  have hVal := hRel1b v (.freg fr') hLoc; simp at hVal; rw [hVal]
                  have hne : DAEOpt.instrDef p[pc] ≠ some v := by
                    rw [show p[pc] = p.code[pc] from rfl, hInstr]; simp [DAEOpt.instrDef]
                    intro h; subst h; rw [hlx] at hLoc; cases hLoc; exact hff rfl
                  rw [hDstOnly v hne]
              · -- stack vars
                intro v off' hLoc; rw [hStack2]
                have hVal := hRelSaved v (.stack off') hLoc; simp at hVal; rw [hVal]
                have hne : DAEOpt.instrDef p[pc] ≠ some v := by
                  rw [show p[pc] = p.code[pc] from rfl, hInstr]; simp [DAEOpt.instrDef]
                  intro h; subst h; rw [hlx] at hLoc; cases hLoc
                rw [hDstOnly v hne]
            · -- fr ≠ dst_reg
              simp [vStoreVarFP, hlx, hEq] at hCodeStore
              have hFmov : r.bodyFlat[s2.pc]? = some (.fmovRR fr dst_reg) := hCodeStore.head
              let s3 := (s2.setFReg fr (s2.fregs dst_reg)).nextPC
              have hSteps3 : ArmSteps r.bodyFlat s2 s3 := .single (.fmovRR fr dst_reg hFmov)
              have hRegs3 : s3.regs = s2.regs := by simp [s3, ArmState.nextPC, ArmState.setFReg]
              have hNEI3 := fun v ir hLoc hNE => hRegs3 ▸ hNEI_shared v ir hLoc hNE
              have hStack3 : s3.stack = s2.stack := by simp [s3, ArmState.nextPC, ArmState.setFReg]
              have hRC3 : ∀ e ∈ entries, s3.stack e.off = (applyCallerSaves entries s).stack e.off :=
                fun e _ => by rw [hStack3, hStack2]
              refine ⟨s3, (hSteps1.trans hSteps1b).trans (hSteps2.trans hSteps3), ?_, ?_, hRC3, hNEI3, ?_, ?_⟩
              · simp [s3, ArmState.nextPC, ArmState.setFReg]
                rw [hPC2, hPC1b', hPC1', hSavedPC, hInstrs]
                simp [vStoreVarFP, hlx, hEq, List.length_append]; omega
              · simp [s3, ArmState.nextPC, ArmState.setFReg, hAMChain]
              · -- non-entry freg
                intro v fr' hLoc hNE
                have hDR : dst_reg = fr := by simp [dst_reg, hlx]
                by_cases hff : fr' = fr
                · have hvx := hInjective v x _ (hff ▸ hLoc) hlx; subst hvx
                  simp [s3, ArmState.nextPC, ArmState.setFReg, hff]
                  exact hArmResult
                · have : s3.fregs fr' = s2.fregs fr' := by
                    simp [s3, ArmState.nextPC, ArmState.setFReg, hff]
                  rw [this]
                  have : s2.fregs fr' = (s1b.havocCallerSaved newRegs newFregs).fregs fr' := by
                    simp [s2, ArmState.nextPC, ArmState.setFReg, hDR, hff]
                  rw [this]
                  have hCS : fr'.isCallerSaved = false := by
                    cases hcs : fr'.isCallerSaved with
                    | false => rfl
                    | true =>
                    obtain ⟨_, _, _, hCoversFreg, _⟩ := spec.callerSaveSpec
                    obtain ⟨coff, hMem⟩ := hCoversFreg v fr' hLoc hcs
                    have hInE : CallerSaveEntry.freg fr' coff ∈ entries := by
                      show _ ∈ callerSaveEntries r.layout r.varMap (DAEOpt.instrDef p[pc])
                      rw [show p[pc] = p.code[pc] from rfl, hInstr]
                      simp only [callerSaveEntries, DAEOpt.instrDef]
                      rw [List.mem_filter]; refine ⟨hMem, ?_⟩; simp [hlx, hff]
                    exact absurd hInE (hNE coff)
                  show (fun r => if r.isCallerSaved then newFregs r else s1b.fregs r) fr' = _
                  simp [hCS]
                  have hVal := hRel1b v (.freg fr') hLoc; simp at hVal; rw [hVal]
                  have hne : DAEOpt.instrDef p[pc] ≠ some v := by
                    rw [show p[pc] = p.code[pc] from rfl, hInstr]; simp [DAEOpt.instrDef]
                    intro h; subst h; rw [hlx] at hLoc; cases hLoc; exact hff rfl
                  rw [hDstOnly v hne]
              · -- stack vars
                intro v off' hLoc; rw [hStack3, hStack2]
                have hVal := hRelSaved v (.stack off') hLoc; simp at hVal; rw [hVal]
                have hne : DAEOpt.instrDef p[pc] ≠ some v := by
                  rw [show p[pc] = p.code[pc] from rfl, hInstr]; simp [DAEOpt.instrDef]
                  intro h; subst h; rw [hlx] at hLoc; cases hLoc
                rw [hDstOnly v hne]
        | _ => simp [isLibCallTAC, show p[pc] = p.code[pc] from rfl, hInstr] at hLib
      | printInt v =>
        -- Void lib call: bl _printInt, no destination → σ' = σ.
        -- Setup: extract regConvSafe / injective from non-failure of verifiedGenInstr
        rw [show p[pc] = p.code[pc] from rfl, hInstr] at hGenInstr
        have hRC : r.layout.regConventionSafe = true := spec.regConventionSafeBool
        have hII : r.layout.isInjective = true := spec.isInjectiveBool
        have hRegConv : RegConventionSafe r.layout :=
          VarLayout.regConventionSafe_spec r.layout hRC
        have hNotFreg : ∀ fr, r.layout v ≠ some (.freg fr) := by
          intro fr h; simp [verifiedGenInstr, hRC, hII, h] at hGenInstr
        have hVMapped : r.layout v ≠ none := by
          have := spec.layoutComplete pc (by simp [Prog.size_eq] at hPC; exact hPC) v
          rw [show p[pc] = p.code[pc] from rfl, hInstr] at this
          exact this (by simp [TAC.vars])
        have hInstrs : baseInstrs = vLoadVar r.layout v .x0 ++ [.callPrintI] := by
          simp only [verifiedGenInstr] at hGenInstr
          exact (Option.some.inj hGenInstr).symm
        -- σ' = σ for printInt (no destination)
        have hσ_eq : σ' = σ := by
          funext w
          apply hDstOnly
          simp [show p[pc] = p.code[pc] from rfl, hInstr, DAEOpt.instrDef]
        -- DAEOpt.instrDef = none ⇒ entries = genCallerSaveAll (no exclusion filter)
        have hEntriesFull : entries = genCallerSaveAll r.layout r.varMap := by
          show callerSaveEntries r.layout r.varMap (DAEOpt.instrDef p[pc]) = _
          rw [show p[pc] = p.code[pc] from rfl, hInstr]
          simp [callerSaveEntries, DAEOpt.instrDef]
        -- Phase A: vLoadVar — construct s1 explicitly per layout case
        rw [hInstrs] at hCodeBase
        have hCodeLoad := hCodeBase.append_left (l2 := [ArmInstr.callPrintI])
        -- Bundle the load step + properties (existence + s1.stack = s_saved.stack)
        have hLoadFull : ∃ s1 : ArmState, ArmSteps r.bodyFlat s_saved s1 ∧
            ExtStateRel r.layout σ s1 ∧
            s1.fregs = s_saved.fregs ∧
            s1.stack = s_saved.stack ∧
            s1.arrayMem = s_saved.arrayMem ∧
            s1.pc = s_saved.pc + (vLoadVar r.layout v .x0).length ∧
            (∀ ir : ArmReg, ir ≠ .x0 → s1.regs ir = s_saved.regs ir) := by
          match hv : r.layout v with
          | some (.stack off) =>
            -- vLoadVar = [ldr .x0 off]
            have hEq := vLoadVar_stack r.layout v .x0 off hv
            have hCL := hCodeLoad
            rw [hEq] at hCL
            have hStepInstr := hCL.head; rw [← hSavedPC] at hStepInstr
            refine ⟨(s_saved.setReg .x0 (s_saved.stack off)).nextPC,
                    .single (.ldr .x0 off hStepInstr), ?_, ?_, ?_, ?_, ?_, ?_⟩
            · -- ExtStateRel
              have h := s_saved.stack off
              refine (ExtStateRel.setReg_preserved hRelSaved (fun w => hRegConv.not_x0 w)).nextPC
            · simp [ArmState.setReg, ArmState.nextPC]
            · simp [ArmState.setReg, ArmState.nextPC]
            · simp [ArmState.setReg, ArmState.nextPC]
            · simp [ArmState.setReg, ArmState.nextPC, hEq]
            · intro ir hne
              simp [ArmState.setReg, ArmState.nextPC, beq_iff_eq]
              intro h; exact absurd h hne
          | some (.ireg r_v) =>
            by_cases heq : r_v = .x0
            · subst heq
              -- vLoadVar = [], no step
              have hEq := vLoadVar_ireg_same r.layout v .x0 hv
              refine ⟨s_saved, .refl, hRelSaved, rfl, rfl, rfl, ?_, fun _ _ => rfl⟩
              simp [hEq]
            · have hbeq : (r_v == .x0) = false := by
                cases h : r_v == .x0
                · rfl
                · simp [beq_iff_eq] at h; exact absurd h heq
              have hEq := vLoadVar_ireg_diff r.layout v .x0 r_v hv hbeq
              have hCL := hCodeLoad
              rw [hEq] at hCL
              have hStepInstr := hCL.head; rw [← hSavedPC] at hStepInstr
              refine ⟨(s_saved.setReg .x0 (s_saved.regs r_v)).nextPC,
                      .single (.movR .x0 r_v hStepInstr), ?_, ?_, ?_, ?_, ?_, ?_⟩
              · refine (ExtStateRel.setReg_preserved hRelSaved (fun w => hRegConv.not_x0 w)).nextPC
              · simp [ArmState.setReg, ArmState.nextPC]
              · simp [ArmState.setReg, ArmState.nextPC]
              · simp [ArmState.setReg, ArmState.nextPC]
              · simp [ArmState.setReg, ArmState.nextPC, hEq]
              · intro ir hne
                simp [ArmState.setReg, ArmState.nextPC, beq_iff_eq]
                intro h; exact absurd h hne
          | some (.freg fr) => exact absurd hv (hNotFreg fr)
          | none => exact absurd hv hVMapped
        obtain ⟨s1, hSteps1, hRel1, hFregs1, hStack1, hAM1, hPC1, hOther1⟩ := hLoadFull
        -- Phase B: callPrintI step
        have hCodeCall : r.bodyFlat[s1.pc]? = some .callPrintI := by
          have h := hCodeBase.append_right (l1 := vLoadVar r.layout v .x0) 0 (by simp)
          simp at h
          rw [hPC1, hSavedPC]
          rw [show r.pcMap pc + (entriesToSaves entries).length = r.pcMap pc + entries.length from by
            simp [entriesToSaves_length]]
          exact h
        let newRegs : ArmReg → BitVec 64 := havocRegsFn s1
        let newFregs : ArmFReg → BitVec 64 := havocFRegsFn s1
        let s_mid := (s1.havocCallerSaved newRegs newFregs).nextPC
        have hSteps2 : ArmSteps r.bodyFlat s1 s_mid :=
          .single (.callPrintI hCodeCall)
        -- Now discharge the 7 hBaseExists obligations
        refine ⟨s_mid, hSteps1.trans hSteps2, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · -- (2) PC: s_mid.pc = s_saved.pc + baseInstrs.length
          show s_mid.pc = s_saved.pc + baseInstrs.length
          simp [s_mid, ArmState.nextPC, ArmState.havocCallerSaved]
          rw [hPC1, hSavedPC, hInstrs]; simp [List.length_append]; omega
        · -- (3) arrayMem preserved
          show s_mid.arrayMem = am
          simp [s_mid, ArmState.nextPC, ArmState.havocCallerSaved, hAM1, s_saved,
                applyCallerSaves_arrayMem, hArrayMem]
        · -- (4) Save slots preserved through load + havoc + nextPC
          intro e he
          show s_mid.stack e.off = (applyCallerSaves entries s).stack e.off
          simp [s_mid, ArmState.nextPC, ArmState.havocCallerSaved_stack, hStack1, s_saved]
        · -- (5) Callee-saved iregs hold σ' values
          intro w ir hLoc hNE
          show s_mid.regs ir = (σ' w).encode
          rw [hσ_eq]
          -- ir not in entries ⇒ (since entries = full set) ir is callee-saved
          have hCS : ir.isCallerSaved = false := by
            cases hcs : ir.isCallerSaved with
            | false => rfl
            | true =>
              obtain ⟨_, _, hCoversIreg, _⟩ := spec.callerSaveSpec
              obtain ⟨coff, hMem⟩ := hCoversIreg w ir hLoc hcs
              rw [← hEntriesFull] at hMem
              exact absurd hMem (hNE coff)
          -- s_mid.regs ir = s1.regs ir (havoc preserves callee-saved)
          have h1 : s_mid.regs ir = s1.regs ir := by
            simp [s_mid, ArmState.nextPC, ArmState.havocCallerSaved, hCS]
          -- s1.regs ir = s_saved.regs ir (load only touches x0; ir ≠ x0 since x0 is caller-saved)
          have hIrNotX0 : ir ≠ .x0 := fun h => by
            rw [h] at hCS; simp [ArmReg.isCallerSaved] at hCS
          have h2 : s1.regs ir = s_saved.regs ir := hOther1 ir hIrNotX0
          -- s_saved.regs ir = s.regs ir (saves only modify stack)
          have h3 : s_saved.regs ir = s.regs ir := by
            simp [s_saved, applyCallerSaves_regs]
          -- s.regs ir = (σ w).encode by hStateRel
          have h4 := hStateRel w (.ireg ir) hLoc
          simp at h4
          rw [h1, h2, h3, h4]
        · -- (6) Callee-saved fregs hold σ' values
          intro w fr hLoc hNE
          show s_mid.fregs fr = (σ' w).encode
          rw [hσ_eq]
          have hCS : fr.isCallerSaved = false := by
            cases hcs : fr.isCallerSaved with
            | false => rfl
            | true =>
              obtain ⟨_, _, _, hCoversFreg, _⟩ := spec.callerSaveSpec
              obtain ⟨coff, hMem⟩ := hCoversFreg w fr hLoc hcs
              rw [← hEntriesFull] at hMem
              exact absurd hMem (hNE coff)
          -- s_mid.fregs fr = s1.fregs fr (havoc preserves callee-saved)
          have h1 : s_mid.fregs fr = s1.fregs fr := by
            simp [s_mid, ArmState.nextPC, ArmState.havocCallerSaved, hCS]
          -- s1.fregs = s_saved.fregs (vLoadVar doesn't touch fregs)
          have h2 : s1.fregs fr = s_saved.fregs fr := by rw [hFregs1]
          -- s_saved.fregs = s.fregs
          have h3 : s_saved.fregs fr = s.fregs fr := by
            simp [s_saved, applyCallerSaves_fregs]
          have h4 := hStateRel w (.freg fr) hLoc
          simp at h4
          rw [h1, h2, h3, h4]
        · -- (7) Stack vars hold σ' values
          intro w off hLoc
          show s_mid.stack off = (σ' w).encode
          rw [hσ_eq]
          -- s_mid.stack = s1.stack = s_saved.stack
          have h1 : s_mid.stack off = s_saved.stack off := by
            simp [s_mid, ArmState.nextPC, ArmState.havocCallerSaved_stack, hStack1]
          -- For w mapped to .stack off, hFresh says no entry has offset off
          obtain ⟨hFresh, _, _, _, _, _⟩ := spec.callerSaveSpec
          have hOff : ∀ e ∈ genCallerSaveAll r.layout r.varMap, e.off ≠ off := by
            intro e he hEq
            exact hFresh e he w (hEq ▸ hLoc)
          have hOff' : ∀ e ∈ entries, e.off ≠ off := by
            rw [hEntriesFull]; exact hOff
          have h2 : s_saved.stack off = s.stack off := by
            simp [s_saved]
            exact applyCallerSaves_stack_other entries s off hOff'
          have h3 := hStateRel w (.stack off) hLoc
          simp at h3
          rw [h1, h2, h3]
      | printBool v =>
        -- Void lib call: bl _printBool, no destination → σ' = σ.
        -- Structurally identical to printInt: x0 calling convention,
        -- vLoadVar layout v .x0 ++ [.callPrintB].
        rw [show p[pc] = p.code[pc] from rfl, hInstr] at hGenInstr
        have hRC : r.layout.regConventionSafe = true := spec.regConventionSafeBool
        have hII : r.layout.isInjective = true := spec.isInjectiveBool
        have hRegConv : RegConventionSafe r.layout :=
          VarLayout.regConventionSafe_spec r.layout hRC
        have hNotFreg : ∀ fr, r.layout v ≠ some (.freg fr) := by
          intro fr h; simp [verifiedGenInstr, hRC, hII, h] at hGenInstr
        have hVMapped : r.layout v ≠ none := by
          have := spec.layoutComplete pc (by simp [Prog.size_eq] at hPC; exact hPC) v
          rw [show p[pc] = p.code[pc] from rfl, hInstr] at this
          exact this (by simp [TAC.vars])
        have hInstrs : baseInstrs = vLoadVar r.layout v .x0 ++ [.callPrintB] := by
          simp only [verifiedGenInstr] at hGenInstr
          exact (Option.some.inj hGenInstr).symm
        have hσ_eq : σ' = σ := by
          funext w
          apply hDstOnly
          simp [show p[pc] = p.code[pc] from rfl, hInstr, DAEOpt.instrDef]
        have hEntriesFull : entries = genCallerSaveAll r.layout r.varMap := by
          show callerSaveEntries r.layout r.varMap (DAEOpt.instrDef p[pc]) = _
          rw [show p[pc] = p.code[pc] from rfl, hInstr]
          simp [callerSaveEntries, DAEOpt.instrDef]
        rw [hInstrs] at hCodeBase
        have hCodeLoad := hCodeBase.append_left (l2 := [ArmInstr.callPrintB])
        have hLoadFull : ∃ s1 : ArmState, ArmSteps r.bodyFlat s_saved s1 ∧
            ExtStateRel r.layout σ s1 ∧
            s1.fregs = s_saved.fregs ∧
            s1.stack = s_saved.stack ∧
            s1.arrayMem = s_saved.arrayMem ∧
            s1.pc = s_saved.pc + (vLoadVar r.layout v .x0).length ∧
            (∀ ir : ArmReg, ir ≠ .x0 → s1.regs ir = s_saved.regs ir) := by
          match hv : r.layout v with
          | some (.stack off) =>
            have hEq := vLoadVar_stack r.layout v .x0 off hv
            have hCL := hCodeLoad
            rw [hEq] at hCL
            have hStepInstr := hCL.head; rw [← hSavedPC] at hStepInstr
            refine ⟨(s_saved.setReg .x0 (s_saved.stack off)).nextPC,
                    .single (.ldr .x0 off hStepInstr), ?_, ?_, ?_, ?_, ?_, ?_⟩
            · refine (ExtStateRel.setReg_preserved hRelSaved (fun w => hRegConv.not_x0 w)).nextPC
            · simp [ArmState.setReg, ArmState.nextPC]
            · simp [ArmState.setReg, ArmState.nextPC]
            · simp [ArmState.setReg, ArmState.nextPC]
            · simp [ArmState.setReg, ArmState.nextPC, hEq]
            · intro ir hne
              simp [ArmState.setReg, ArmState.nextPC, beq_iff_eq]
              intro h; exact absurd h hne
          | some (.ireg r_v) =>
            by_cases heq : r_v = .x0
            · subst heq
              have hEq := vLoadVar_ireg_same r.layout v .x0 hv
              refine ⟨s_saved, .refl, hRelSaved, rfl, rfl, rfl, ?_, fun _ _ => rfl⟩
              simp [hEq]
            · have hbeq : (r_v == .x0) = false := by
                cases h : r_v == .x0
                · rfl
                · simp [beq_iff_eq] at h; exact absurd h heq
              have hEq := vLoadVar_ireg_diff r.layout v .x0 r_v hv hbeq
              have hCL := hCodeLoad
              rw [hEq] at hCL
              have hStepInstr := hCL.head; rw [← hSavedPC] at hStepInstr
              refine ⟨(s_saved.setReg .x0 (s_saved.regs r_v)).nextPC,
                      .single (.movR .x0 r_v hStepInstr), ?_, ?_, ?_, ?_, ?_, ?_⟩
              · refine (ExtStateRel.setReg_preserved hRelSaved (fun w => hRegConv.not_x0 w)).nextPC
              · simp [ArmState.setReg, ArmState.nextPC]
              · simp [ArmState.setReg, ArmState.nextPC]
              · simp [ArmState.setReg, ArmState.nextPC]
              · simp [ArmState.setReg, ArmState.nextPC, hEq]
              · intro ir hne
                simp [ArmState.setReg, ArmState.nextPC, beq_iff_eq]
                intro h; exact absurd h hne
          | some (.freg fr) => exact absurd hv (hNotFreg fr)
          | none => exact absurd hv hVMapped
        obtain ⟨s1, hSteps1, hRel1, hFregs1, hStack1, hAM1, hPC1, hOther1⟩ := hLoadFull
        have hCodeCall : r.bodyFlat[s1.pc]? = some .callPrintB := by
          have h := hCodeBase.append_right (l1 := vLoadVar r.layout v .x0) 0 (by simp)
          simp at h
          rw [hPC1, hSavedPC]
          rw [show r.pcMap pc + (entriesToSaves entries).length = r.pcMap pc + entries.length from by
            simp [entriesToSaves_length]]
          exact h
        let newRegs : ArmReg → BitVec 64 := havocRegsFn s1
        let newFregs : ArmFReg → BitVec 64 := havocFRegsFn s1
        let s_mid := (s1.havocCallerSaved newRegs newFregs).nextPC
        have hSteps2 : ArmSteps r.bodyFlat s1 s_mid :=
          .single (.callPrintB hCodeCall)
        refine ⟨s_mid, hSteps1.trans hSteps2, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · show s_mid.pc = s_saved.pc + baseInstrs.length
          simp [s_mid, ArmState.nextPC, ArmState.havocCallerSaved]
          rw [hPC1, hSavedPC, hInstrs]; simp [List.length_append]; omega
        · show s_mid.arrayMem = am
          simp [s_mid, ArmState.nextPC, ArmState.havocCallerSaved, hAM1, s_saved,
                applyCallerSaves_arrayMem, hArrayMem]
        · intro e he
          show s_mid.stack e.off = (applyCallerSaves entries s).stack e.off
          simp [s_mid, ArmState.nextPC, ArmState.havocCallerSaved_stack, hStack1, s_saved]
        · intro w ir hLoc hNE
          show s_mid.regs ir = (σ' w).encode
          rw [hσ_eq]
          have hCS : ir.isCallerSaved = false := by
            cases hcs : ir.isCallerSaved with
            | false => rfl
            | true =>
              obtain ⟨_, _, hCoversIreg, _⟩ := spec.callerSaveSpec
              obtain ⟨coff, hMem⟩ := hCoversIreg w ir hLoc hcs
              rw [← hEntriesFull] at hMem
              exact absurd hMem (hNE coff)
          have h1 : s_mid.regs ir = s1.regs ir := by
            simp [s_mid, ArmState.nextPC, ArmState.havocCallerSaved, hCS]
          have hIrNotX0 : ir ≠ .x0 := fun h => by
            rw [h] at hCS; simp [ArmReg.isCallerSaved] at hCS
          have h2 : s1.regs ir = s_saved.regs ir := hOther1 ir hIrNotX0
          have h3 : s_saved.regs ir = s.regs ir := by
            simp [s_saved, applyCallerSaves_regs]
          have h4 := hStateRel w (.ireg ir) hLoc
          simp at h4
          rw [h1, h2, h3, h4]
        · intro w fr hLoc hNE
          show s_mid.fregs fr = (σ' w).encode
          rw [hσ_eq]
          have hCS : fr.isCallerSaved = false := by
            cases hcs : fr.isCallerSaved with
            | false => rfl
            | true =>
              obtain ⟨_, _, _, hCoversFreg, _⟩ := spec.callerSaveSpec
              obtain ⟨coff, hMem⟩ := hCoversFreg w fr hLoc hcs
              rw [← hEntriesFull] at hMem
              exact absurd hMem (hNE coff)
          have h1 : s_mid.fregs fr = s1.fregs fr := by
            simp [s_mid, ArmState.nextPC, ArmState.havocCallerSaved, hCS]
          have h2 : s1.fregs fr = s_saved.fregs fr := by rw [hFregs1]
          have h3 : s_saved.fregs fr = s.fregs fr := by
            simp [s_saved, applyCallerSaves_fregs]
          have h4 := hStateRel w (.freg fr) hLoc
          simp at h4
          rw [h1, h2, h3, h4]
        · intro w off hLoc
          show s_mid.stack off = (σ' w).encode
          rw [hσ_eq]
          have h1 : s_mid.stack off = s_saved.stack off := by
            simp [s_mid, ArmState.nextPC, ArmState.havocCallerSaved_stack, hStack1]
          obtain ⟨hFresh, _, _, _, _, _⟩ := spec.callerSaveSpec
          have hOff : ∀ e ∈ genCallerSaveAll r.layout r.varMap, e.off ≠ off := by
            intro e he hEq
            exact hFresh e he w (hEq ▸ hLoc)
          have hOff' : ∀ e ∈ entries, e.off ≠ off := by
            rw [hEntriesFull]; exact hOff
          have h2 : s_saved.stack off = s.stack off := by
            simp [s_saved]
            exact applyCallerSaves_stack_other entries s off hOff'
          have h3 := hStateRel w (.stack off) hLoc
          simp at h3
          rw [h1, h2, h3]
      | printString lit =>
        -- Void lib call, no operand: bl _printString. Single ARM step.
        rw [show p[pc] = p.code[pc] from rfl, hInstr] at hGenInstr
        have hRC : r.layout.regConventionSafe = true := spec.regConventionSafeBool
        have hII : r.layout.isInjective = true := spec.isInjectiveBool
        have hInstrs : baseInstrs = [.callPrintS lit] := by
          simp only [verifiedGenInstr, hRC, hII, Bool.not_true, Bool.or_self,
                     Bool.false_eq_true, ↓reduceIte] at hGenInstr
          exact (Option.some.inj hGenInstr).symm
        have hσ_eq : σ' = σ := by
          funext w
          apply hDstOnly
          simp [show p[pc] = p.code[pc] from rfl, hInstr, DAEOpt.instrDef]
        have hEntriesFull : entries = genCallerSaveAll r.layout r.varMap := by
          show callerSaveEntries r.layout r.varMap (DAEOpt.instrDef p[pc]) = _
          rw [show p[pc] = p.code[pc] from rfl, hInstr]
          simp [callerSaveEntries, DAEOpt.instrDef]
        rw [hInstrs] at hCodeBase
        have hCodeCall : r.bodyFlat[s_saved.pc]? = some (.callPrintS lit) := by
          have h := hCodeBase 0 (by simp); simp at h; rw [hSavedPC]
          rw [show r.pcMap pc + (entriesToSaves entries).length =
              r.pcMap pc + entries.length from by simp [entriesToSaves_length]]
          exact h
        let newRegs : ArmReg → BitVec 64 := havocRegsFn s_saved
        let newFregs : ArmFReg → BitVec 64 := havocFRegsFn s_saved
        let s_mid := (s_saved.havocCallerSaved newRegs newFregs).nextPC
        have hSteps : ArmSteps r.bodyFlat s_saved s_mid :=
          .single (.callPrintS lit hCodeCall)
        refine ⟨s_mid, hSteps, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · -- (2) PC
          show s_mid.pc = s_saved.pc + baseInstrs.length
          simp [s_mid, ArmState.nextPC, ArmState.havocCallerSaved, hInstrs]
        · -- (3) arrayMem
          show s_mid.arrayMem = am
          simp [s_mid, ArmState.nextPC, ArmState.havocCallerSaved, s_saved,
                applyCallerSaves_arrayMem, hArrayMem]
        · -- (4) Save slots
          intro e he
          show s_mid.stack e.off = (applyCallerSaves entries s).stack e.off
          simp [s_mid, ArmState.nextPC, ArmState.havocCallerSaved_stack, s_saved]
        · -- (5) Callee-saved iregs
          intro w ir hLoc hNE
          show s_mid.regs ir = (σ' w).encode
          rw [hσ_eq]
          have hCS : ir.isCallerSaved = false := by
            cases hcs : ir.isCallerSaved with
            | false => rfl
            | true =>
              obtain ⟨_, _, hCoversIreg, _⟩ := spec.callerSaveSpec
              obtain ⟨coff, hMem⟩ := hCoversIreg w ir hLoc hcs
              rw [← hEntriesFull] at hMem
              exact absurd hMem (hNE coff)
          have h1 : s_mid.regs ir = s_saved.regs ir := by
            simp [s_mid, ArmState.nextPC, ArmState.havocCallerSaved, hCS]
          have h2 : s_saved.regs ir = s.regs ir := by
            simp [s_saved, applyCallerSaves_regs]
          have h3 := hStateRel w (.ireg ir) hLoc
          simp at h3
          rw [h1, h2, h3]
        · -- (6) Callee-saved fregs
          intro w fr hLoc hNE
          show s_mid.fregs fr = (σ' w).encode
          rw [hσ_eq]
          have hCS : fr.isCallerSaved = false := by
            cases hcs : fr.isCallerSaved with
            | false => rfl
            | true =>
              obtain ⟨_, _, _, hCoversFreg, _⟩ := spec.callerSaveSpec
              obtain ⟨coff, hMem⟩ := hCoversFreg w fr hLoc hcs
              rw [← hEntriesFull] at hMem
              exact absurd hMem (hNE coff)
          have h1 : s_mid.fregs fr = s_saved.fregs fr := by
            simp [s_mid, ArmState.nextPC, ArmState.havocCallerSaved, hCS]
          have h2 : s_saved.fregs fr = s.fregs fr := by
            simp [s_saved, applyCallerSaves_fregs]
          have h3 := hStateRel w (.freg fr) hLoc
          simp at h3
          rw [h1, h2, h3]
        · -- (7) Stack vars
          intro w off hLoc
          show s_mid.stack off = (σ' w).encode
          rw [hσ_eq]
          have h1 : s_mid.stack off = s_saved.stack off := by
            simp [s_mid, ArmState.nextPC, ArmState.havocCallerSaved_stack]
          obtain ⟨hFresh, _, _, _, _, _⟩ := spec.callerSaveSpec
          have hOff : ∀ e ∈ genCallerSaveAll r.layout r.varMap, e.off ≠ off := by
            intro e he hEq
            exact hFresh e he w (hEq ▸ hLoc)
          have hOff' : ∀ e ∈ entries, e.off ≠ off := by
            rw [hEntriesFull]; exact hOff
          have h2 : s_saved.stack off = s.stack off := by
            simp [s_saved]
            exact applyCallerSaves_stack_other entries s off hOff'
          have h3 := hStateRel w (.stack off) hLoc
          simp at h3
          rw [h1, h2, h3]
      | printFloat v =>
        -- Void lib call, float operand: vLoadVarFP v .d0 ++ [.callPrintF].
        -- Mirrors printInt but for fregs; vLoadVarFP_exec returns stack
        -- preservation directly so no inline 3-way case-split needed.
        rw [show p[pc] = p.code[pc] from rfl, hInstr] at hGenInstr
        have hRC : r.layout.regConventionSafe = true := spec.regConventionSafeBool
        have hII : r.layout.isInjective = true := spec.isInjectiveBool
        have hRegConv : RegConventionSafe r.layout :=
          VarLayout.regConventionSafe_spec r.layout hRC
        have hNotIreg : ∀ ir, r.layout v ≠ some (.ireg ir) := by
          intro ir h; simp [verifiedGenInstr, hRC, hII, h] at hGenInstr
        have hVMapped : r.layout v ≠ none := by
          have := spec.layoutComplete pc (by simp [Prog.size_eq] at hPC; exact hPC) v
          rw [show p[pc] = p.code[pc] from rfl, hInstr] at this
          exact this (by simp [TAC.vars])
        have hInstrs : baseInstrs = vLoadVarFP r.layout v .d0 ++ [.callPrintF] := by
          simp only [verifiedGenInstr] at hGenInstr
          exact (Option.some.inj hGenInstr).symm
        have hσ_eq : σ' = σ := by
          funext w
          apply hDstOnly
          simp [show p[pc] = p.code[pc] from rfl, hInstr, DAEOpt.instrDef]
        have hEntriesFull : entries = genCallerSaveAll r.layout r.varMap := by
          show callerSaveEntries r.layout r.varMap (DAEOpt.instrDef p[pc]) = _
          rw [show p[pc] = p.code[pc] from rfl, hInstr]
          simp [callerSaveEntries, DAEOpt.instrDef]
        rw [hInstrs] at hCodeBase
        have hCodeLoad := hCodeBase.append_left (l2 := [ArmInstr.callPrintF])
        obtain ⟨s1, k1_U, hSteps1N, hk1_U, hFregsD0_U, hRel1, hRegs1, hPC1, hAM1, hOther1, hStack1⟩ :=
          vLoadVarFP_exec r.bodyFlat r.layout v .d0 σ s_saved
            (r.pcMap pc + (entriesToSaves entries).length)
            hRelSaved hRegConv hSavedPC hCodeLoad (.inl rfl) hNotIreg hVMapped
        have hSteps1 := ArmStepsN_to_ArmSteps hSteps1N
        have hCodeCall : r.bodyFlat[s1.pc]? = some .callPrintF := by
          have h := hCodeBase.append_right (l1 := vLoadVarFP r.layout v .d0) 0 (by simp)
          simp at h
          rw [hPC1]
          rw [show r.pcMap pc + (entriesToSaves entries).length =
              r.pcMap pc + entries.length from by simp [entriesToSaves_length]]
          exact h
        let newRegs : ArmReg → BitVec 64 := havocRegsFn s1
        let newFregs : ArmFReg → BitVec 64 := havocFRegsFn s1
        let s_mid := (s1.havocCallerSaved newRegs newFregs).nextPC
        have hSteps2 : ArmSteps r.bodyFlat s1 s_mid :=
          .single (.callPrintF hCodeCall)
        refine ⟨s_mid, hSteps1.trans hSteps2, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · -- (2) PC
          show s_mid.pc = s_saved.pc + baseInstrs.length
          simp [s_mid, ArmState.nextPC, ArmState.havocCallerSaved]
          rw [hPC1, hSavedPC, hInstrs]; simp [List.length_append]; omega
        · -- (3) arrayMem
          show s_mid.arrayMem = am
          simp [s_mid, ArmState.nextPC, ArmState.havocCallerSaved, hAM1, s_saved,
                applyCallerSaves_arrayMem, hArrayMem]
        · -- (4) Save slots: s_mid.stack = s1.stack = s_saved.stack on entry offsets
          intro e he
          show s_mid.stack e.off = (applyCallerSaves entries s).stack e.off
          simp [s_mid, ArmState.nextPC, ArmState.havocCallerSaved_stack, hStack1, s_saved]
        · -- (5) Callee-saved iregs hold σ' = σ values
          intro w ir hLoc hNE
          show s_mid.regs ir = (σ' w).encode
          rw [hσ_eq]
          have hCS : ir.isCallerSaved = false := by
            cases hcs : ir.isCallerSaved with
            | false => rfl
            | true =>
              obtain ⟨_, _, hCoversIreg, _⟩ := spec.callerSaveSpec
              obtain ⟨coff, hMem⟩ := hCoversIreg w ir hLoc hcs
              rw [← hEntriesFull] at hMem
              exact absurd hMem (hNE coff)
          have h1 : s_mid.regs ir = s1.regs ir := by
            simp [s_mid, ArmState.nextPC, ArmState.havocCallerSaved, hCS]
          -- s1.regs = s_saved.regs (vLoadVarFP doesn't touch iregs)
          have h2 : s1.regs ir = s_saved.regs ir := by rw [hRegs1]
          have h3 : s_saved.regs ir = s.regs ir := by
            simp [s_saved, applyCallerSaves_regs]
          have h4 := hStateRel w (.ireg ir) hLoc
          simp at h4
          rw [h1, h2, h3, h4]
        · -- (6) Callee-saved fregs hold σ' = σ values
          intro w fr hLoc hNE
          show s_mid.fregs fr = (σ' w).encode
          rw [hσ_eq]
          have hCS : fr.isCallerSaved = false := by
            cases hcs : fr.isCallerSaved with
            | false => rfl
            | true =>
              obtain ⟨_, _, _, hCoversFreg, _⟩ := spec.callerSaveSpec
              obtain ⟨coff, hMem⟩ := hCoversFreg w fr hLoc hcs
              rw [← hEntriesFull] at hMem
              exact absurd hMem (hNE coff)
          have h1 : s_mid.fregs fr = s1.fregs fr := by
            simp [s_mid, ArmState.nextPC, ArmState.havocCallerSaved, hCS]
          -- fr is callee-saved (not in entries), and load only writes .d0 (caller-saved)
          have hFrNotD0 : fr ≠ .d0 := fun h => by
            rw [h] at hCS; simp [ArmFReg.isCallerSaved] at hCS
          have h2 : s1.fregs fr = s_saved.fregs fr := hOther1 fr hFrNotD0
          have h3 : s_saved.fregs fr = s.fregs fr := by
            simp [s_saved, applyCallerSaves_fregs]
          have h4 := hStateRel w (.freg fr) hLoc
          simp at h4
          rw [h1, h2, h3, h4]
        · -- (7) Stack vars hold σ' = σ values
          intro w off hLoc
          show s_mid.stack off = (σ' w).encode
          rw [hσ_eq]
          have h1 : s_mid.stack off = s_saved.stack off := by
            simp [s_mid, ArmState.nextPC, ArmState.havocCallerSaved_stack, hStack1]
          obtain ⟨hFresh, _, _, _, _, _⟩ := spec.callerSaveSpec
          have hOff : ∀ e ∈ genCallerSaveAll r.layout r.varMap, e.off ≠ off := by
            intro e he hEq
            exact hFresh e he w (hEq ▸ hLoc)
          have hOff' : ∀ e ∈ entries, e.off ≠ off := by
            rw [hEntriesFull]; exact hOff
          have h2 : s_saved.stack off = s.stack off := by
            simp [s_saved]
            exact applyCallerSaves_stack_other entries s off hOff'
          have h3 := hStateRel w (.stack off) hLoc
          simp at h3
          rw [h1, h2, h3]
      | _ => simp [isLibCallTAC, show p[pc] = p.code[pc] from rfl, hInstr] at hLib
    obtain ⟨s_mid, hBaseSteps, hMidPC, hMidAM, hSaveSlots, hNEI, hNEF, hSV⟩ :=
      hBaseExists
    -- Step 3: restores
    have hRestorePC : s_mid.pc =
        r.pcMap pc + (entriesToSaves entries ++ baseInstrs).length := by
      rw [hMidPC, hSavedPC]; simp [List.length_append]; omega
    have hRestoreCode : CodeAt r.bodyFlat s_mid.pc (entriesToRestores entries) := by
      rw [hRestorePC]; exact hCodeRestores
    have hStepRestores := armSteps_restores r.bodyFlat entries s_mid hRestoreCode
    -- Compose all three
    let s_final := {applyCallerRestores entries s_mid with
      pc := s_mid.pc + entries.length}
    have hAllSteps : ArmSteps r.bodyFlat s s_final :=
      hStepSaves.trans (hBaseSteps.trans hStepRestores)
    -- Phase D: derive length-tracked ArmStepsN via pc-distinctness
    have hFinPC : s_final.pc = r.pcMap (pc + 1) := by
      show s_mid.pc + entries.length = r.pcMap (pc + 1)
      have hPcN := hPcNext
      rw [hBody] at hPcN
      rw [hMidPC, hSavedPC, hPcN]
      simp only [List.length_append, entriesToSaves_length, entriesToRestores_length,
        show entries = callerSaveEntries r.layout r.varMap (DAEOpt.instrDef p[pc]) from rfl]
      omega
    have hPcDiff : s.pc ≠ s_final.pc := by
      rw [hFinPC, hPcRel, hPcNext]
      have h1 : 1 ≤ (r.bodyPerPC[pc]'hpcB).length := bodyPerPC_length_pos spec pc hPC
      omega
    obtain ⟨kFinal, hArmN, hkPos⟩ := ArmSteps_to_ArmStepsN_pos hAllSteps hPcDiff
    -- Prove ExtSimRel for the final state
    obtain ⟨hFresh, hNodup, hCoversIreg, hCoversFreg, hUniqIreg, hUniqFreg⟩ :=
      spec.callerSaveSpec
    refine ⟨s_final, kFinal, hArmN, ?_, ⟨?_, ?_, ?_⟩, ?haltCond⟩
    · intro _ _ _ _hCfg; exact hkPos
    case haltCond =>
      intro σ' am' hEq; exact Cfg.noConfusion hEq
    · -- ExtStateRel via callerSave_composition_excluding
      -- entries ⊆ genCallerSaveAll (callerSaveEntries filters genCallerSaveAll)
      have hEntriesSub : entries.Sublist (genCallerSaveAll r.layout r.varMap) := by
        show (callerSaveEntries r.layout r.varMap (DAEOpt.instrDef p[pc])).Sublist _
        unfold callerSaveEntries
        cases DAEOpt.instrDef p[pc] with
        | none => exact List.Sublist.refl _
        | some _ => exact List.filter_sublist
      have hSubset : ∀ e, e ∈ entries → e ∈ genCallerSaveAll r.layout r.varMap :=
        fun e he => hEntriesSub.subset he
      -- Nodup on entries (sublist of nodup list)
      have hNodupE : (entries.map CallerSaveEntry.off).Nodup :=
        hNodup.sublist (hEntriesSub.map _)
      have hCSCE := ExtStateRel.callerSave_composition_excluding
        hStateRel entries s_mid
        (fun e he v hv => hFresh e (hSubset e he) v hv)
        hNodupE
        (fun r o1 o2 h1 h2 => hUniqIreg r o1 o2 (hSubset _ h1) (hSubset _ h2))
        (fun r o1 o2 h1 h2 => hUniqFreg r o1 o2 (hSubset _ h1) (hSubset _ h2))
        (fun ir off h => genCallerSaveAll_allCS_ireg (hSubset _ h))
        (fun fr off h => genCallerSaveAll_allCS_freg (hSubset _ h))
        hSaveSlots hNEI hNEF hSV hEIU hEFU
      -- hCSCE : ExtStateRel layout σ' (applyCallerRestores entries s_mid)
      -- s_final = {applyCallerRestores entries s_mid with pc := ...}
      show ExtStateRel r.layout σ' s_final
      exact hCSCE.withPC _
    · -- PcRel: s_final.pc = pcMap (pc + 1)
      exact hFinPC
    · -- ArrayMem preserved
      show (applyCallerRestores entries s_mid).arrayMem = am
      rw [applyCallerRestores_arrayMem]
      exact hMidAM
  · by_cases hPrint : ∃ fmt vs, p[pc] = .print fmt vs
    · -- Print case: save/restore around printCall (havoc)
      obtain ⟨fmt, vs, hPrintEq⟩ := hPrint
      -- Get bodyPerPC structure from GenAsmSpec
      obtain ⟨lines, hBody⟩ :=
        spec.printSaveRestore pc hPC ⟨fmt, vs, hPrintEq⟩
      -- Get pcMap/lengths infrastructure
      obtain ⟨lengths, hLSz, hPcMap, hLenEq⟩ := spec.pcMapLengths
      have hpcB : pc < r.bodyPerPC.size := spec.bodySize ▸ hPC
      -- CodeAt for the full bodyPerPC[pc] block
      have hCodeAt : CodeAt r.bodyFlat (r.pcMap pc) (r.bodyPerPC[pc]'hpcB) := by
        rw [hPcMap]; exact codeAt_of_bodyFlat' r lengths hLSz hLenEq pc hpcB
      rw [hBody] at hCodeAt
      -- Abbreviate entries
      let entries := genCallerSaveAll r.layout r.varMap
      -- Split CodeAt into three parts: (saves ++ [printCall]) ++ restores
      have hCodeSP := hCodeAt.append_left
        (l2 := entriesToRestores entries)
      have hCodeRestores := hCodeAt.append_right
        (l1 := entriesToSaves entries ++ [ArmInstr.printCall lines])
      have hCodeSaves := hCodeSP.append_left (l2 := [ArmInstr.printCall lines])
      have hCodePrint := hCodeSP.append_right (l1 := entriesToSaves entries)
      -- Extract ExtStateRel components
      obtain ⟨hStateRel, hPcRel, hArrayMem⟩ := hRel
      -- Print step: cfg' = .run (pc+1) σ am
      have hCfg : cfg' = .run (pc + 1) σ am := by
        have hInstr : p[pc]? = some (.print fmt vs) :=
          Prog.getElem?_eq_getElem hPC ▸ congrArg some hPrintEq
        cases hStep <;> simp_all
      subst hCfg
      -- hPcNext: pcMap(pc+1) = pcMap(pc) + bodyPerPC[pc].length
      have hPcNext : r.pcMap (pc + 1) = r.pcMap pc + (r.bodyPerPC[pc]'hpcB).length := by
        rw [hPcMap, buildPcMap_succ lengths pc (by rw [hLSz]; exact hpcB)]
        congr 1; exact hLenEq pc (by rw [hLSz]; exact hpcB) hpcB
      -- Rewrite s.pc to r.pcMap pc using PcRel
      have hSPC : s.pc = r.pcMap pc := hPcRel
      -- Step 1: saves
      have hStepSaves := armSteps_saves r.bodyFlat entries s
        (hSPC ▸ hCodeSaves)
      -- Step 2: printCall
      have hPrintCode : r.bodyFlat[s.pc + entries.length]? =
          some (ArmInstr.printCall lines) := by
        have := hCodePrint 0 (by simp)
        simp only [List.getElem_cons_zero, entriesToSaves_length] at this
        rw [hSPC]; exact this
      -- Opaque havoc oracles supply post-call register contents.
      let newRegs : ArmReg → BitVec 64 :=
        havocRegsFn {applyCallerSaves entries s with pc := s.pc + entries.length}
      let newFregs : ArmFReg → BitVec 64 :=
        havocFRegsFn {applyCallerSaves entries s with pc := s.pc + entries.length}
      have hStepPrint1 : ArmStep r.bodyFlat
          {applyCallerSaves entries s with pc := s.pc + entries.length}
          ({applyCallerSaves entries s with pc := s.pc + entries.length}.havocCallerSaved newRegs newFregs |>.nextPC) :=
        .printCall lines hPrintCode
      -- Step 3: restores
      have hRestorePC : s.pc + (entriesToSaves entries).length + 1 =
          r.pcMap pc + (entriesToSaves entries ++ [ArmInstr.printCall lines]).length := by
        simp [entriesToSaves_length, hSPC]; omega
      have hRestoreCode : CodeAt r.bodyFlat
          (s.pc + entries.length + 1) (entriesToRestores entries) := by
        rw [show s.pc + entries.length + 1 =
            s.pc + (entriesToSaves entries).length + 1 by simp [entriesToSaves_length]]
        rw [hRestorePC]; exact hCodeRestores
      -- The state after printCall
      let s_mid := {applyCallerSaves entries s with pc := s.pc + entries.length}.havocCallerSaved newRegs newFregs |>.nextPC
      have hMidPC : s_mid.pc = s.pc + entries.length + 1 := by
        simp [s_mid, ArmState.nextPC, ArmState.havocCallerSaved]
      have hStepRestores := armSteps_restores r.bodyFlat entries s_mid
        (hMidPC ▸ hRestoreCode)
      -- Compose all three: saves → printCall → restores
      let s_final := {applyCallerRestores entries s_mid with
        pc := s_mid.pc + entries.length}
      have hAllSteps : ArmSteps r.bodyFlat s s_final :=
        hStepSaves.trans ((ArmSteps.single hStepPrint1).trans hStepRestores)
      -- Phase D: derive length-tracked ArmStepsN via pc-distinctness
      have hFinPC : s_final.pc = r.pcMap (pc + 1) := by
        show s_mid.pc + entries.length = r.pcMap (pc + 1)
        have hPcN := hPcNext
        rw [hBody] at hPcN
        rw [hMidPC, hPcN, hSPC]
        simp only [List.length_append, entriesToSaves_length, entriesToRestores_length,
                   List.length_cons, List.length_nil]
        simp only [show entries = genCallerSaveAll r.layout r.varMap from rfl]
        omega
      have hPcDiff : s.pc ≠ s_final.pc := by
        rw [hFinPC, hPcRel, hPcNext]
        have h1 : 1 ≤ (r.bodyPerPC[pc]'hpcB).length := bodyPerPC_length_pos spec pc hPC
        omega
      obtain ⟨kFinal, hArmN, hkPos⟩ := ArmSteps_to_ArmStepsN_pos hAllSteps hPcDiff
      -- Prove ExtSimRel for the final state
      refine ⟨s_final, kFinal, hArmN, ?_, ⟨?_, ?_, ?_⟩, ?haltCond⟩
      · intro _ _ _ _hCfg; exact hkPos
      case haltCond =>
        intro σ' am' hEq; exact Cfg.noConfusion hEq
      · -- ExtStateRel: callerSave_composition on the logical state, then
        -- transfer to s_final via pc-independence.
        -- First, get the logical result
        let s_havoc := (applyCallerSaves entries s).havocCallerSaved newRegs newFregs
        -- Destructure callerSaveSpec
        obtain ⟨hFresh, hNodup, hCoversIreg, hCoversFreg, hUniqIreg, hUniqFreg⟩ :=
          spec.callerSaveSpec
        have hCSC := @ExtStateRel.callerSave_composition _ _ _
          hStateRel entries newRegs newFregs
          hFresh hNodup hCoversIreg hCoversFreg hUniqIreg hUniqFreg
          (fun ir off h => genCallerSaveAll_allCS_ireg h)
          (fun fr off h => genCallerSaveAll_allCS_freg h)
        -- hCSC : ExtStateRel layout σ (applyCallerRestores entries s_havoc)
        -- s_final = {applyCallerRestores entries s_mid with pc := ...}
        -- s_mid = {s_havoc with pc := ...}
        -- Use pc-irrelevance to relate
        have : applyCallerRestores entries s_mid =
            {applyCallerRestores entries s_havoc with
             pc := s_mid.pc} := by
          rw [show s_mid = {s_havoc with pc := s_mid.pc} from by
            simp [s_mid, s_havoc, ArmState.nextPC, ArmState.havocCallerSaved]]
          exact applyCallerRestores_pc_irrelevant entries s_havoc s_mid.pc
        show ExtStateRel r.layout σ s_final
        rw [show s_final = {applyCallerRestores entries s_mid with
            pc := s_mid.pc + entries.length} from rfl]
        rw [this]
        exact hCSC.withPC _
      · -- PcRel: s_final.pc = pcMap (pc + 1)
        exact hFinPC
      · -- ArrayMem preserved (saves/havoc/restores don't touch arrayMem)
        show (applyCallerRestores entries s_mid).arrayMem = am
        rw [applyCallerRestores_arrayMem]
        simp [s_mid, ArmState.nextPC, ArmState.havocCallerSaved,
              applyCallerSaves_arrayMem]
        exact hArrayMem
    · -- Normal case: delegate to ext_backward_simulation
      have hNotPrint : ∀ fmt vs, p[pc] ≠ .print fmt vs := by
        intro fmt vs h; exact hPrint ⟨fmt, vs, h⟩
      have hNotLib : isLibCallTAC p[pc] = false := by
        cases h : isLibCallTAC p[pc] <;> simp_all
      -- Phase 6: `safe` is now `verifiedBoundsSafe p pc` per `instrGen`.
      have hSome := spec.instrGen pc hPC hNotLib hNotPrint
      let safe : Bool := verifiedBoundsSafe p pc
      -- Get pcMap = buildPcMap lengths with element-wise equality
      obtain ⟨lengths, hLSz, hPcMap, hLenEq⟩ := spec.pcMapLengths
      have hpcB : pc < r.bodyPerPC.size := spec.bodySize ▸ hPC
      -- CodeAt from codeAt_of_bodyFlat
      have hCodeAt : CodeAt r.bodyFlat (r.pcMap pc) (r.bodyPerPC[pc]'hpcB) := by
        rw [hPcMap]; exact codeAt_of_bodyFlat' r lengths hLSz hLenEq pc hpcB
      -- hPcNext from buildPcMap_succ
      have hPcNext : ∀ σ' am', cfg' = .run (pc + 1) σ' am' →
          r.pcMap (pc + 1) = r.pcMap pc + (r.bodyPerPC[pc]'hpcB).length := by
        intro _ _ _
        rw [hPcMap, buildPcMap_succ lengths pc (by rw [hLSz]; exact hpcB)]
        congr 1; exact hLenEq pc (by rw [hLSz]; exact hpcB) hpcB
      -- Halt intercept: after `.b haltS`, step through the haltSaveBlock.
      -- The normal ext_backward_simulation would stop at haltS; we continue to
      -- haltFinal so downstream phases can name that PC directly.
      by_cases hHalt : p[pc] = .halt
      · -- Extract ExtSimRel components
        obtain ⟨hStateRel, hPcRel, hArrayMem⟩ := hRel
        have hSPC : s.pc = r.pcMap pc := hPcRel
        -- Step.halt forces cfg' = .halt σ am
        have hCfg : cfg' = .halt σ am := by
          have hInstr : p[pc]? = some .halt :=
            Prog.getElem?_eq_getElem hPC ▸ congrArg some hHalt
          cases hStep <;> simp_all
        subst hCfg
        -- verifiedGenInstr for .halt returns [.b r.haltS]
        have hRC : r.layout.regConventionSafe = true := spec.regConventionSafeBool
        have hII : r.layout.isInjective = true := spec.isInjectiveBool
        have hInstrs : r.bodyPerPC[pc]'hpcB = [.b r.haltS] := by
          rw [hHalt] at hSome
          simp only [verifiedGenInstr] at hSome
          exact (Option.some.inj hSome).symm
        rw [hInstrs] at hCodeAt
        -- Branch to r.haltS
        have hBranch : r.bodyFlat[s.pc]? = some (.b r.haltS) := by
          rw [hSPC]; exact hCodeAt.head
        let s1 : ArmState := { s with pc := r.haltS }
        have hStep1 : ArmStep r.bodyFlat s s1 :=
          ArmStep.branch r.haltS hBranch
        have hRel1 : ExtStateRel r.layout σ s1 := hStateRel.withPC _
        have hAM1 : s1.arrayMem = am := hArrayMem
        -- CodeAt for the halt-save block inside bodyFlat:
        -- bodyFlat = (bodyPerPC flat) ++ haltSaveBlock, starting at haltS.
        have hCodeSave : CodeAt r.bodyFlat s1.pc
            (genHaltSave p.observable r.layout r.varMap) := by
          show CodeAt r.bodyFlat r.haltS _
          -- r.haltS = (bodyPerPC flat).length (by spec), so a suffix lives at haltS.
          rw [spec.haltS_eq, show r.bodyFlat =
            ((r.bodyPerPC.toList.flatMap id) ++ r.haltSaveBlock.toList).toArray from rfl]
          intro i hi
          -- bodyFlat[flat.length + i] = haltSaveBlock[i] (when i < haltSaveBlock.size).
          have hLen : i < r.haltSaveBlock.toList.length := by
            have : r.haltSaveBlock.toList.length =
                (genHaltSave p.observable r.layout r.varMap).length := by
              rw [spec.haltSaveBlock_eq]
            rw [this]; exact hi
          rw [List.getElem?_toArray,
              List.getElem?_append_right (Nat.le_add_right _ _),
              Nat.add_sub_cancel_left]
          rw [List.getElem?_eq_getElem hLen]
          congr 1
          have hhb := spec.haltSaveBlock_eq
          rw [show r.haltSaveBlock.toList[i] =
              (genHaltSave p.observable r.layout r.varMap)[i]'(hhb ▸ hLen)
            from by congr 1]
        -- Step through haltSaveBlock
        obtain ⟨s_fin, hSteps, hPC_fin, hAM_fin, hRel_fin⟩ :=
          armSteps_haltSaveBlock (layout := r.layout) (varMap := r.varMap)
            (observable := p.observable) (σ := σ) (prog := r.bodyFlat)
            s1 hRel1
            spec.varMapInjOnOffsets
            spec.layoutStackComesFromVarMap
            hCodeSave
        -- Phase D: lift to length-tracked ArmStepsN. Halt case: .run claim is vacuous.
        have hAllSteps : ArmSteps r.bodyFlat s s_fin :=
          (ArmSteps.single hStep1).trans hSteps
        obtain ⟨kFinal, hArmN⟩ := ArmSteps_to_ArmStepsN hAllSteps
        refine ⟨s_fin, kFinal, hArmN, ?_, ⟨hRel_fin, ?_⟩, ?haltCond⟩
        · intro _ _ _ hCfg; exact Cfg.noConfusion hCfg
        · show s_fin.arrayMem = am
          rw [hAM_fin, hAM1]
        case haltCond =>
          intro σ' am' _hEq
          -- s_fin.pc = s1.pc + (genHaltSave ...).length = r.haltS + haltSaveBlock.size = r.haltFinal
          have hSaveLen : (genHaltSave p.observable r.layout r.varMap).length =
              r.haltSaveBlock.toList.length := by
            rw [spec.haltSaveBlock_eq]
          rw [hPC_fin, show s1.pc = r.haltS from rfl, hSaveLen]
          rw [show r.haltSaveBlock.toList.length = r.haltSaveBlock.size from by
              rw [Array.length_toList]]
          exact spec.haltFinal_eq.symm
      · -- hNCSL/hNCSLBin: vacuously true (not a lib-call)
        have hNCSL : ∀ x op y, p[pc] = .floatUnary x op y →
            op.isNative = false → NoCallerSavedLayout r.layout := by
          intro x op y heq hNN
          simp [isLibCallTAC, heq, hNN] at hNotLib
        have hNCSLBin : ∀ x y z, p[pc] = .fbinop x .fpow y z →
            NoCallerSavedLayout r.layout := by
          intro x y z heq
          simp [isLibCallTAC, heq] at hNotLib
        have hNCSLPrintInt : ∀ v, p[pc] = .printInt v →
            NoCallerSavedLayout r.layout := by
          intro v heq
          simp [isLibCallTAC, heq] at hNotLib
        have hNCSLPrintBool : ∀ v, p[pc] = .printBool v →
            NoCallerSavedLayout r.layout := by
          intro v heq
          simp [isLibCallTAC, heq] at hNotLib
        have hNCSLPrintFloat : ∀ v, p[pc] = .printFloat v →
            NoCallerSavedLayout r.layout := by
          intro v heq
          simp [isLibCallTAC, heq] at hNotLib
        have hNCSLPrintStr : ∀ lit, p[pc] = .printString lit →
            NoCallerSavedLayout r.layout := by
          intro lit heq
          simp [isLibCallTAC, heq] at hNotLib
        -- Phase 6: the oracle discharges from `buildVerifiedInvMap p pc σ am`
        -- (= `hInv`) via the helper theorem `verifiedBoundsSafe_sound`.
        have hOracle : safe = true →
            (∀ dst arr idx ty, p[pc]? = some (.arrLoad dst arr idx ty) →
              ∀ idxVal, σ idx = .int idxVal → idxVal < arraySizeBv p.arrayDecls arr) ∧
            (∀ arr idx val ty, p[pc]? = some (.arrStore arr idx val ty) →
              ∀ idxVal, σ idx = .int idxVal → idxVal < arraySizeBv p.arrayDecls arr) :=
          fun hBS => verifiedBoundsSafe_sound hPC hBS hInv
        obtain ⟨s', kEBS, hArmStepsN, hKEBS, hRelOut⟩ := ext_backward_simulation p r.bodyFlat r.layout r.pcMap
          r.haltS r.divS r.boundsS p.arrayDecls safe hOracle
          hStep hRel hPC tyCtx spec.wellTypedProg hTS spec.wellTypedLayout
          p[pc] (Prog.getElem?_eq_getElem hPC)
          (r.bodyPerPC[pc]'hpcB) hSome spec.regConventionSafeBool spec.isInjectiveBool hCodeAt hPcNext
          (spec.layoutComplete pc hPC) rfl hNCSL hNCSLBin hNCSLPrintInt hNCSLPrintBool hNCSLPrintFloat hNCSLPrintStr
        -- Phase D: propagate length-tracked tuple. On .run, kEBS = block length ≥ 1.
        have hLenPos : 1 ≤ (r.bodyPerPC[pc]'hpcB).length := bodyPerPC_length_pos spec pc hPC
        refine ⟨s', kEBS, hArmStepsN, ?_, hRelOut, ?haltCond⟩
        · intro pc' σ' am' hCfg; rw [hKEBS _ _ _ hCfg]; exact hLenPos
        case haltCond =>
          intro σ' am' hEq
          subst hEq
          -- cfg' = .halt forces p[pc] = .halt via Step inversion, but hHalt says otherwise.
          cases hStep with
          | halt hinstr =>
            have : p[pc] = .halt := by
              have hGet := Prog.getElem?_eq_getElem hPC
              rw [hGet] at hinstr; exact Option.some.inj hinstr
            exact absurd this hHalt

-- ──────────────────────────────────────────────────────────────
-- Multi-step simulation (main theorem)
-- ──────────────────────────────────────────────────────────────

/-- Extract `pc < p.size` from any TAC step out of a running configuration.
    Every `Step` constructor requires `p[pc]? = some _`. -/
private theorem Step.pc_lt_of_step {p : Prog} {pc : Nat} {σ : Store}
    {am : ArrayMem} {cfg' : Cfg}
    (hStep : p ⊩ Cfg.run pc σ am ⟶ cfg') : pc < p.size := by
  if h : pc < p.size then exact h
  else have := Prog.getElem?_none h; cases hStep <;> simp_all

/-- Classify a single step result: either the successor is `.run` with
    `TypedStore` preserved, or it is terminal (no further steps). -/
private theorem step_run_or_terminal {tyCtx : TyCtx} {p : Prog} {pc : Nat} {σ : Store}
    {am : ArrayMem} {c : Cfg}
    (hwtp : WellTypedProg tyCtx p) (hts : TypedStore tyCtx σ)
    (hpc : pc < p.size) (hstep : p ⊩ Cfg.run pc σ am ⟶ c) :
    (∃ pc' σ' am', c = .run pc' σ' am' ∧ TypedStore tyCtx σ') ∨
    (∀ c', ¬ (p ⊩ c ⟶ c')) := by
  cases hstep with
  | const h =>
    exact .inl ⟨_, _, _, rfl, type_preservation hwtp hts hpc
      (show Step p (.run pc σ am) _ from .const h)⟩
  | copy h =>
    exact .inl ⟨_, _, _, rfl, type_preservation hwtp hts hpc
      (show Step p (.run pc σ am) _ from .copy h)⟩
  | binop h h1 h2 h3 =>
    exact .inl ⟨_, _, _, rfl, type_preservation hwtp hts hpc
      (show Step p (.run pc σ am) _ from .binop h h1 h2 h3)⟩
  | boolop h =>
    exact .inl ⟨_, _, _, rfl, type_preservation hwtp hts hpc
      (show Step p (.run pc σ am) _ from .boolop h)⟩
  | goto _ => exact .inl ⟨_, _, _, rfl, hts⟩
  | iftrue _ _ => exact .inl ⟨_, _, _, rfl, hts⟩
  | iffall _ _ => exact .inl ⟨_, _, _, rfl, hts⟩
  | arrLoad h h1 h2 =>
    exact .inl ⟨_, _, _, rfl, type_preservation hwtp hts hpc
      (show Step p (.run pc σ am) _ from .arrLoad h h1 h2)⟩
  | arrStore h h1 h2 h3 =>
    exact .inl ⟨_, _, _, rfl, type_preservation hwtp hts hpc
      (show Step p (.run pc σ am) _ from .arrStore h h1 h2 h3)⟩
  | fbinop h h1 h2 =>
    exact .inl ⟨_, _, _, rfl, type_preservation hwtp hts hpc
      (show Step p (.run pc σ am) _ from .fbinop h h1 h2)⟩
  | intToFloat h h1 =>
    exact .inl ⟨_, _, _, rfl, type_preservation hwtp hts hpc
      (show Step p (.run pc σ am) _ from .intToFloat h h1)⟩
  | floatToInt h h1 =>
    exact .inl ⟨_, _, _, rfl, type_preservation hwtp hts hpc
      (show Step p (.run pc σ am) _ from .floatToInt h h1)⟩
  | floatUnary h h1 =>
    exact .inl ⟨_, _, _, rfl, type_preservation hwtp hts hpc
      (show Step p (.run pc σ am) _ from .floatUnary h h1)⟩
  | fternop h h1 h2 h3 =>
    exact .inl ⟨_, _, _, rfl, type_preservation hwtp hts hpc
      (show Step p (.run pc σ am) _ from .fternop h h1 h2 h3)⟩
  | halt _ => exact .inr fun _ h => Step.no_step_from_halt h
  | binop_divByZero _ _ _ _ => exact .inr fun _ h => Step.no_step_from_errorDiv h
  | binop_typeError _ _ => exact .inr fun _ h => Step.no_step_from_typeError h
  | arrLoad_boundsError _ _ _ => exact .inr fun _ h => Step.no_step_from_errorBounds h
  | arrStore_boundsError _ _ _ _ => exact .inr fun _ h => Step.no_step_from_errorBounds h
  | arrLoad_typeError _ _ => exact .inr fun _ h => Step.no_step_from_typeError h
  | arrStore_typeError _ _ => exact .inr fun _ h => Step.no_step_from_typeError h
  | fbinop_typeError _ _ => exact .inr fun _ h => Step.no_step_from_typeError h
  | intToFloat_typeError _ _ => exact .inr fun _ h => Step.no_step_from_typeError h
  | floatToInt_typeError _ _ => exact .inr fun _ h => Step.no_step_from_typeError h
  | floatUnary_typeError _ _ => exact .inr fun _ h => Step.no_step_from_typeError h
  | fternop_typeError _ _ => exact .inr fun _ h => Step.no_step_from_typeError h
  | print _ => exact .inl ⟨_, _, _, rfl, hts⟩
  | printInt _ => exact .inl ⟨_, _, _, rfl, hts⟩
  | printBool _ => exact .inl ⟨_, _, _, rfl, hts⟩
  | printFloat _ => exact .inl ⟨_, _, _, rfl, hts⟩
  | printString _ => exact .inl ⟨_, _, _, rfl, hts⟩

/-- Whole-program backward simulation for `verifiedGenerateAsm`.

    If the verified code generator succeeds on program `p`, then any
    multi-step TAC execution starting from a configuration whose ARM
    counterpart satisfies `ExtSimRel` is simulated by `ArmSteps`
    preserving `ExtSimRel`.

    The proof proceeds by induction on the TAC `Steps` derivation,
    applying `step_simulation` (which wraps `ext_backward_simulation`)
    at each step, using `step_run_or_terminal` to classify the
    intermediate config, and `type_preservation` for `TypedStore`.

    **Propagated sorrys:** 0 from `verifiedGenInstr_correct`. -/
theorem tacToArm_refinement {tyCtx : TyCtx} {p : Prog} {r : VerifiedAsmResult}
    (hGen : verifiedGenerateAsm tyCtx p = .ok r)
    {pc : Nat} {σ : Store} {am : ArrayMem}
    (s : ArmState)
    (hRel : ExtSimRel r.layout r.pcMap r.divS r.boundsS (.run pc σ am) s)
    (hTS : TypedStore tyCtx σ)
    (hInv : buildVerifiedInvMap p pc σ am)
    {n : Nat} (cfg' : Cfg) (hStepsN : StepsN p (.run pc σ am) cfg' n) :
    ∃ s' k, ArmStepsN r.bodyFlat s s' k ∧
      (∀ pc' σ' am', cfg' = .run pc' σ' am' → n ≤ k) ∧
      ExtSimRel r.layout r.pcMap r.divS r.boundsS cfg' s' ∧
      (∀ σ' am', cfg' = .halt σ' am' → s'.pc = r.haltFinal) := by
  have spec := verifiedGenerateAsm_spec hGen
  -- Induction on n: generalize over the start config (pattern from type_preservation_steps).
  suffices ∀ n pc σ am (s : ArmState),
      ExtSimRel r.layout r.pcMap r.divS r.boundsS (.run pc σ am) s →
      TypedStore tyCtx σ →
      buildVerifiedInvMap p pc σ am →
      ∀ cfg', StepsN p (.run pc σ am) cfg' n →
      ∃ s' k, ArmStepsN r.bodyFlat s s' k ∧
        (∀ pc' σ' am', cfg' = .run pc' σ' am' → n ≤ k) ∧
        ExtSimRel r.layout r.pcMap r.divS r.boundsS cfg' s' ∧
        (∀ σ' am', cfg' = .halt σ' am' → s'.pc = r.haltFinal) from
    this n pc σ am s hRel hTS hInv cfg' hStepsN
  intro n
  induction n with
  | zero =>
    intro pc σ am s hRel _ _ cfg' hStepsN
    change Cfg.run pc σ am = cfg' at hStepsN
    subst hStepsN
    refine ⟨s, 0, rfl, ?_, hRel, ?_⟩
    · intro _ _ _ _; omega
    · intro σ' am' hEq; exact Cfg.noConfusion hEq
  | succ n ih =>
    intro pc σ am s hRel hTS_cur hInv_cur cfg' hStepsN
    obtain ⟨c'', hStep1, hRest⟩ := hStepsN
    have hPC := Step.pc_lt_of_step hStep1
    obtain ⟨s_mid, k1, hArmN1, hK1, hRel_mid, hHaltMid⟩ :=
      step_simulation spec hStep1 hRel hPC hTS_cur hInv_cur
    -- Classify the one-step successor
    rcases step_run_or_terminal spec.wellTypedProg hTS_cur hPC hStep1 with
      ⟨pc', σ', am', hEq, hTS'⟩ | hTerminal
    · -- Successor is .run: subst and apply IH.
      subst hEq
      have hInv' : buildVerifiedInvMap p pc' σ' am' :=
        spec.invPreserved pc σ am hInv_cur pc' σ' am' hStep1
      obtain ⟨s', k2, hArmN2, hK2, hRel', hHalt'⟩ :=
        ih _ _ _ s_mid hRel_mid hTS' hInv' cfg' hRest
      refine ⟨s', k1 + k2, ArmStepsN_trans hArmN1 hArmN2, ?_, hRel', hHalt'⟩
      intro pc'' σ'' am'' hCfg
      have hk1_ge : 1 ≤ k1 := hK1 pc' σ' am' rfl
      have hk2_ge : n ≤ k2 := hK2 pc'' σ'' am'' hCfg
      omega
    · -- Successor is terminal: hRest's head step would contradict hTerminal.
      cases n with
      | zero =>
        change c'' = cfg' at hRest
        subst hRest
        refine ⟨s_mid, k1, hArmN1, ?_, hRel_mid, hHaltMid⟩
        intro pc'' σ'' am'' hCfg
        exact hK1 pc'' σ'' am'' hCfg
      | succ n' =>
        obtain ⟨c3, hStep3, _⟩ := hRest
        exact absurd hStep3 (hTerminal _)

/-- Corollary: initial ExtSimRel establishment.
    For a zero-initialized store, if the layout maps every variable and
    the ARM state's registers/stack/fregs are all zero at PC = pcMap 0,
    then `ExtSimRel` holds at the initial configuration. -/
theorem initial_extSimRel (layout : VarLayout) (pcMap : Nat → Nat)
    (divS boundsS : Nat)
    (σ₀ : Store) (am₀ : ArrayMem) (s₀ : ArmState)
    (hEncode : ∀ v, (σ₀ v).encode = 0)
    (hPC : s₀.pc = pcMap 0)
    (hRegs : ∀ r, s₀.regs r = 0)
    (hFregs : ∀ r, s₀.fregs r = 0)
    (hStack : ∀ off, s₀.stack off = 0)
    (hAM : s₀.arrayMem = am₀) :
    ExtSimRel layout pcMap divS boundsS (.run 0 σ₀ am₀) s₀ := by
  refine ⟨?_, ?_, ?_⟩
  · intro v loc hLoc
    rw [hEncode]
    match loc with
    | .stack off => exact hStack off
    | .ireg r => exact hRegs r
    | .freg r => exact hFregs r
  · exact hPC
  · exact hAM

/-- Top-level correctness: if code generation succeeds and the TAC program
    starts from a zero-initialized store, every reachable TAC configuration
    is simulated by ARM steps from a zeroed ARM state.

    This combines `tacToArm_refinement` with `initial_extSimRel` to
    eliminate all intermediate hypotheses. The only requirements are:
    1. Code generation succeeded (`verifiedGenerateAsm p = .ok r`)
    2. The TAC program reaches `cfg'` from the typed zero-initialized store

    `Store.typedInit` assigns each variable the zero value of its declared type
    (`Value.ofBitVec (Γ v) 0`), so `TypedStore` holds for any type context.

    **Propagated sorrys:** 0 from `verifiedGenInstr_correct`. -/
private theorem typedInit_encode (Γ : TyCtx) (v : Var) :
    (Store.typedInit Γ v).encode = 0 := by
  simp [Store.typedInit, Value.ofBitVec, Value.encode]
  cases Γ v <;> simp

theorem tacToArm_correctness {tyCtx : TyCtx} {p : Prog} {r : VerifiedAsmResult}
    (hGen : verifiedGenerateAsm tyCtx p = .ok r)
    {cfg' : Cfg}
    (hSteps : p ⊩ Cfg.run 0 (Store.typedInit tyCtx) (fun _ _ => 0) ⟶* cfg') :
    ∃ s', ArmSteps r.bodyFlat
      { regs := fun _ => 0, fregs := fun _ => 0, stack := fun _ => 0,
        pc := r.pcMap 0, flags := ⟨0, 0⟩ } s' ∧
      ExtSimRel r.layout r.pcMap r.divS r.boundsS cfg' s' ∧
      (∀ σ' am', cfg' = .halt σ' am' → s'.pc = r.haltFinal) := by
  obtain ⟨n, hStepsN⟩ := Steps_to_StepsN hSteps
  obtain ⟨s', _k, hArmN, _hK, hRel, hHalt⟩ :=
    tacToArm_refinement hGen _
      (initial_extSimRel r.layout r.pcMap r.divS r.boundsS (Store.typedInit tyCtx) (fun _ _ => 0)
        { regs := fun _ => 0, fregs := fun _ => 0, stack := fun _ => 0,
          pc := r.pcMap 0, flags := ⟨0, 0⟩ }
        (typedInit_encode tyCtx) rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) rfl)
      (TypedStore.typedInit tyCtx)
      (buildVerifiedInvMap_atStart p (Store.typedInit tyCtx) (fun _ _ => 0))
      cfg' hStepsN
  exact ⟨s', ArmStepsN_to_ArmSteps hArmN, hRel, hHalt⟩

/-- Length-tracked variant of `tacToArm_correctness`. Takes `StepsN` of length `n`
    and returns `ArmStepsN` of length `k` with `n ≤ k` on `.run` endings.
    Used by `source_diverges_gives_ArmDiverges_init` in PipelineCorrectness.lean
    to build `ArmDiverges` by truncating via `ArmStepsN_prefix`. -/
theorem tacToArm_correctness_N {tyCtx : TyCtx} {p : Prog} {r : VerifiedAsmResult}
    (hGen : verifiedGenerateAsm tyCtx p = .ok r)
    {cfg' : Cfg} {n : Nat}
    (hStepsN : StepsN p (Cfg.run 0 (Store.typedInit tyCtx) (fun _ _ => 0)) cfg' n) :
    ∃ s' k, ArmStepsN r.bodyFlat
      { regs := fun _ => 0, fregs := fun _ => 0, stack := fun _ => 0,
        pc := r.pcMap 0, flags := ⟨0, 0⟩ } s' k ∧
      (∀ pc' σ' am', cfg' = .run pc' σ' am' → n ≤ k) ∧
      ExtSimRel r.layout r.pcMap r.divS r.boundsS cfg' s' ∧
      (∀ σ' am', cfg' = .halt σ' am' → s'.pc = r.haltFinal) :=
  tacToArm_refinement hGen _
    (initial_extSimRel r.layout r.pcMap r.divS r.boundsS (Store.typedInit tyCtx) (fun _ _ => 0)
      { regs := fun _ => 0, fregs := fun _ => 0, stack := fun _ => 0,
        pc := r.pcMap 0, flags := ⟨0, 0⟩ }
      (typedInit_encode tyCtx) rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) rfl)
    (TypedStore.typedInit tyCtx)
    (buildVerifiedInvMap_atStart p (Store.typedInit tyCtx) (fun _ _ => 0))
    cfg' hStepsN

/-- Caller-saved integer register numbers (x3-x8, x9-x15). -/
private def callerSavedIntRegs : List Nat := [3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- Caller-saved float register numbers (d0-d7). d0 is the call arg/return. -/
private def callerSavedFloatRegs : List Nat := [0, 1, 2, 3, 4, 5, 6, 7]

/-- Callee-saved integer register numbers. If any are used, the prologue/epilogue
    must save and restore them. -/
private def calleeSavedIntRegs : List Nat := [19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

/-- Callee-saved float register numbers (d8-d15). -/
private def calleeSavedFloatRegs : List Nat := [8, 9, 10, 11, 12, 13, 14, 15]

-- detectCalleeSaved, detectCallerSaved, pairUpSameClass, libcallSaveRestore,
-- calleeSavePrologue, calleeSaveEpilogue: removed.
-- Callee-save prologue/epilogue and caller-save save/restore are now
-- generated as verified ArmInstr in verifiedGenerateAsm.

/-- Defense-in-depth: check that no variable maps to a restricted register.
    This is redundant with `checkNoRegConventionViolations` in the certificate checker
    and `VarLayout.regConventionSafe` in `verifiedGenerateAsm`, but guards against
    bugs in either check. -/
private def checkRegConvention (vars : List Var) : Except String Unit := do
  for v in vars do
    if violatesRegConvention v then
      throw s!"register convention violation: variable '{v}' maps to a restricted register"

/-- Format a `VerifiedAsmResult` into a complete assembly text.  Wraps the
    verified core (`r.bodyFlat`) with AArch64 prologue/epilogue, runtime error
    handlers (div-by-zero, bounds), printf format strings, and array data
    sections.  All wrapping/printing here is unverified — the verified core
    is the `VerifiedAsmResult` itself, produced by `verifiedGenerateAsm`. -/
def formatVerifiedAsm (r : VerifiedAsmResult) (p : Prog) : Except String String := do
  let vars := collectVars p
  -- Defense-in-depth: register convention and callee-save checks
  checkRegConvention vars
  let layoutCallee := detectCalleeSavedLayout r.layout
  let (csIntRegs, csFloatRegs) := r.calleeSaveRegs
  if !layoutCallee.1.all csIntRegs.contains then
    .error "callee-saved int register used in layout but not saved in prologue"
  if !layoutCallee.2.all csFloatRegs.contains then
    .error "callee-saved float register used in layout but not saved in prologue"
  -- Stack frame: 16-byte aligned
  -- Layout: [scratch 8B] [var1 8B] ... [varN 8B] [callee-saved slots] [padding] [x29 8B] [x30 8B]
  let calleeSaveBytes := (csIntRegs.length + csFloatRegs.length) * 8
  let frameSize := ((vars.length + 1) * 8 + calleeSaveBytes + 16 + 15) / 16 * 16
  -- Helpers for large frame constants.  AArch64 add/sub take a 12-bit unsigned immediate
  -- (≤ 4095); anything larger is materialized in a scratch register.  `mov` only reaches a
  -- 16-bit value, so for frames ≥ 65536 the constant comes from the literal pool (`ldr =`),
  -- which imposes no bound on the frame size (hence no bound on the variable count).
  let bigConst (r : String) (n : Nat) : List String :=
    if n < 65536 then [s!"  mov {r}, #{n}"] else [s!"  ldr {r}, ={n}"]
  let subSpFrame := if frameSize ≤ 4095 then
      [s!"  sub sp, sp, #{frameSize}"]
    else
      bigConst "x1" frameSize ++ ["  sub sp, sp, x1"]
  let addSpFrame := if frameSize ≤ 4095 then
      [s!"  add sp, sp, #{frameSize}"]
    else
      bigConst "x1" frameSize ++ ["  add sp, sp, x1"]
  let addFp := if frameSize - 16 ≤ 4095 then
      [s!"  add x29, sp, #{frameSize - 16}"]
    else
      bigConst "x1" (frameSize - 16) ++ ["  add x29, sp, x1"]
  -- Pretty-print callee-save prologue/epilogue from verified ArmInstr
  let lbl := ppLabel r.haltS r.divS r.boundsS r.tacPcOf
  let csProlog := ppInstrs lbl r.calleeSavePrologue
  let csEpilog := ppInstrs lbl r.calleeSaveEpilogue
  let header := [
    ".global _main",
    ".align 2",
    "",
    "_main:"] ++
    subSpFrame ++
    slotAccess "str" "x30" (frameSize - 8) ++
    slotAccess "str" "x29" (frameSize - 16) ++
    addFp ++
    (if csProlog.isEmpty then [] else
      ["  // Save callee-saved registers"] ++ csProlog) ++
    ["",
    "  // Initialize all variables to 0",
    "  mov x0, #0"
  ]
  -- Pretty-print init instructions
  let initLines := ppInstrs lbl r.initInstrs.toList
  -- Pretty-print body with TAC PC labels (uniform for all instructions,
  -- including print — printCall in bodyPerPC carries pre-computed printf lines)
  let body := (List.range r.bodyPerPC.size).flatMap fun pc =>
    [s!".L{pc}:"] ++ ppInstrs lbl ((r.bodyPerPC[pc]!))
  -- Halt epilogue: spill observable values to stack so they're inspectable from
  -- outside the process (e.g., a debugger), then exit. Output happens only via
  -- explicit print* statements during program execution; observable values are
  -- a semantic-preservation contract for the verified compiler, not I/O.
  let saveLines := ppInstrs lbl r.haltSaveBlock.toList
  let footer := [
    "",
    ".Lhalt:",
    "  // Spill observable values to stack (semantic-preservation contract)"] ++
    saveLines ++
    ["",
     "  // Exit with code 0",
     "  mov x0, #0"] ++
    (if csEpilog.isEmpty then [] else
      ["  // Restore callee-saved registers"] ++ csEpilog) ++
    slotAccess "ldr" "x29" (frameSize - 16) ++
    slotAccess "ldr" "x30" (frameSize - 8) ++
    addSpFrame ++
    ["  ret",
     "",
     ".Ldiv_by_zero:",
     "  adrp x0, .Ldiv_msg@PAGE",
     "  add x0, x0, .Ldiv_msg@PAGEOFF",
     "  bl _printf",
     "  mov x0, #1",
     "  bl _exit",
     "",
     ".Lbounds_err:",
     "  adrp x0, .Lbounds_msg@PAGE",
     "  add x0, x0, .Lbounds_msg@PAGEOFF",
     "  bl _printf",
     "  mov x0, #1",
     "  bl _exit",
     "",
     ".section __TEXT,__cstring",
     ".Ldiv_msg:",
     "  .asciz \"error: division by zero\\n\"",
     ".Lbounds_msg:",
     "  .asciz \"error: array index out of bounds\\n\"",
     ""] ++
    -- Per-instruction format strings for variadic-print statements (legacy path).
    -- The .Lfmt:/.Lfmt_float:/.Lname_* labels used by the old auto-dump are
    -- gone; observable values are spilled to stack at .Lhalt for inspection but
    -- no longer printed. Output happens only via explicit print* statements.
    (List.range p.code.size).filterMap (fun pc =>
      match p.code.getD pc .halt with
      | .print fmt _ =>
        -- Re-escape special characters for .asciz directive
        let escaped := fmt.foldl (fun acc c =>
          match c with
          | '\n' => acc ++ "\\n"
          | '\t' => acc ++ "\\t"
          | '\\' => acc ++ "\\\\"
          | '"'  => acc ++ "\\\""
          | c    => acc ++ c.toString) ""
        some s!".Lfmt_print_{pc}:\n  .asciz \"{escaped}\""
      | _ => none) ++
    -- Per-distinct-string entries for printString instructions
    [""] ++
    (((List.range p.code.size).filterMap (fun pc =>
      match p.code.getD pc .halt with
      | .printString lit => some lit
      | _ => none)).dedup.map (fun lit =>
        let escaped := lit.foldl (fun acc c =>
          match c with
          | '\n' => acc ++ "\\n"
          | '\t' => acc ++ "\\t"
          | '\\' => acc ++ "\\\\"
          | '"'  => acc ++ "\\\""
          | c    => acc ++ c.toString) ""
        s!"{stringPoolLabel lit}:\n  .asciz \"{escaped}\""))
  -- Emit .data section for each array (size × 8 bytes, zero-initialized)
  let arrays := collectArrays p
  let arrayData := if arrays.isEmpty then [] else
    ["", ".section __DATA,__data"] ++
    arrays.flatMap fun arr =>
      [s!".global _arr_{arr}",
       ".align 3",
       s!"_arr_{arr}:",
       s!"  .space {(if p.arraySize arr == 0 then 1024 else p.arraySize arr) * 8}"]
  .ok (emit (header ++ [""] ++ initLines ++ [""] ++ body ++ footer ++ arrayData ++ [""]))

/-- Generate the complete assembly for a program.  Thin wrapper: produces the
    verified core via `verifiedGenerateAsm`, then renders it via `formatVerifiedAsm`. -/
def generateAsm (tyCtx : TyCtx) (p : Prog) : Except String String := do
  let r ← verifiedGenerateAsm tyCtx p
  formatVerifiedAsm r p

-- ============================================================
-- § 6. End-to-end: parse → compile → codegen
-- ============================================================

/-- Apply a single optimization pass: run it, override the certificate's tyCtx
    with the expected one, check the certificate, return the optimized program.
    Overriding tyCtx ensures the certificate is validated under the correct
    type context regardless of what the pass produced. -/
def applyPass (name : String) (tyCtx : TyCtx) (pass : Prog → ECertificate) (p : Prog) : Except String Prog :=
  let cert := { pass p with tyCtx := tyCtx }
  if cert.orig.code != p.code || cert.orig.observable != p.observable ||
     cert.orig.arrayDecls != p.arrayDecls then
    .error s!"optimization certificate orig mismatch for {name} (code={cert.orig.code == p.code} obs={cert.orig.observable == p.observable} arr={cert.orig.arrayDecls == p.arrayDecls})"
  else if checkCertificateExec cert then .ok cert.trans
  else
    let checks := checkCertificateVerboseExec cert
    let failures := checks.filter (fun (_, b) => !b)
    let failNames := failures.map (fun (n, _) => n)
    .error s!"optimization certificate check failed for {name}: {failNames}"

/-- Apply each optimization pass in sequence:
    DCE → ConstProp → DCE → DAE → CSE → LICM → ConstHoist → Peephole → DCE → RegAlloc.
    DCE at start: eliminates dead code from goto patterns in source.
    DCE after ConstProp: eliminates dead branches from constant folding.
    DCE before RegAlloc: cleans up after Peephole.
    Each pass is checked by the executable certificate checker. -/
def optimizePipeline (tyCtx : TyCtx) (p : Prog) : Except String Prog := do
  let p ← applyPass "DCE" tyCtx (DCEOpt.optimize tyCtx) p
  let p ← applyPass "LICM" tyCtx (LICMOpt.optimize tyCtx) p
  let p ← applyPass "ConstProp" tyCtx (ConstPropOpt.optimize tyCtx) p
  let p ← applyPass "DCE" tyCtx (DCEOpt.optimize tyCtx) p
  let p ← applyPass "DAE" tyCtx (DAEOpt.optimize tyCtx) p
  let p ← applyPass "FMAFusion" tyCtx (FMAFusionOpt.optimize tyCtx) p
  let p ← applyPass "CSE" tyCtx (CSEOpt.optimize tyCtx) p
  let p ← applyPass "ConstHoist" tyCtx (ConstHoistOpt.optimize tyCtx) p
  let p ← applyPass "Peephole" tyCtx (PeepholeOpt.optimize tyCtx) p
  let p ← applyPass "DCE" tyCtx (DCEOpt.optimize tyCtx) p
  applyPass "RegAlloc" tyCtx (RegAllocOpt.optimize tyCtx) p


/-- Apply a list of certificate-checked optimization passes resiliently.
    Each pass is checked by the executable certificate checker; if a check
    fails, that pass is skipped and the pipeline continues with the
    unoptimized program. Always succeeds. -/
def applyPasses (tyCtx : TyCtx) : List (String × (Prog → ECertificate)) → Prog → Prog
  | [], p => p
  | (name, pass) :: rest, p =>
    let p' := match applyPass name tyCtx pass p with
      | .ok p' => p'
      | .error _ => p
    applyPasses tyCtx rest p'

/-- Apply `passes` repeatedly, stopping when either the program code is
    unchanged after a full iteration (fixed point) or `maxIter` iterations
    have run, whichever comes first. Each pass inside is certificate-checked
    via `applyPasses`. -/
def applyPassesUntilFixedOrN (tyCtx : TyCtx)
    (passes : List (String × (Prog → ECertificate))) :
    Nat → Prog → Prog
  | 0, p => p
  | n + 1, p =>
    let p' := applyPasses tyCtx passes p
    if p'.code == p.code then p'
    else applyPassesUntilFixedOrN tyCtx passes n p'

/-- Previous (legacy) optimization pass list, kept for comparison. -/
def previousPasses (tyCtx : TyCtx) : List (String × (Prog → ECertificate)) :=
  [ ("DCE", DCEOpt.optimize tyCtx),
    ("LICM", LICMOpt.optimize tyCtx),
    ("ConstProp", ConstPropOpt.optimize tyCtx),
    ("DCE", DCEOpt.optimize tyCtx),
    ("DAE", DAEOpt.optimize tyCtx),
    ("FMAFusion", FMAFusionOpt.optimize tyCtx),
    ("CSE", CSEOpt.optimize tyCtx),
    ("ConstHoist", ConstHoistOpt.optimize tyCtx),
    ("Peephole", PeepholeOpt.optimize tyCtx),
    ("DCE", DCEOpt.optimize tyCtx),
    ("RegAlloc", RegAllocOpt.optimize tyCtx) ]

/-- The standard optimization pass list.

    Structure:
      Phase 1: front-load ConstProp + DCE + CSE so later passes see
        folded constants and unified subexpressions.
      Phase 2: LICM cluster `[LICM, ConstProp, ConstHoist, CSE, DAE]`,
        repeated 4 times. LICM hoists `const` instructions one loop
        level per run; the cluster around it canonicalizes copies and
        kills writes the redundancy passes have made dead. 4 iterations
        suffice for the deepest Livermore nest (k21 matmul: rep/k/i/j).
      Phase 3: FMAFusion runs late, after redundancy is gone, so every
        surviving `fmul` is real and fusion candidates are not stranded
        by upstream CSE replacing a consumer with a copy.
      Phase 4: final DCE + Peephole cleanup, then RegAlloc.

    Each pass is independently certificate-checked by `applyPasses`, so
    reordering and iteration cost only compile time. -/
def standardPasses (tyCtx : TyCtx) : List (String × (Prog → ECertificate)) :=
  -- Phase 1: front-load
  [ ("ConstProp", ConstPropOpt.optimize tyCtx),
    ("DCE", DCEOpt.optimize tyCtx),
    ("CSE", CSEOpt.optimize tyCtx),
    ("ConstProp", ConstPropOpt.optimize tyCtx),
    ("DAE", DAEOpt.optimize tyCtx),
  -- Phase 2: LICM cluster × 4 (one iteration per loop-nesting level)
    ("LICM", LICMOpt.optimize tyCtx),
    ("ConstProp", ConstPropOpt.optimize tyCtx),
    ("ConstHoist", ConstHoistOpt.optimize tyCtx),
    ("CSE", CSEOpt.optimize tyCtx),
    ("DAE", DAEOpt.optimize tyCtx),
    ("LICM", LICMOpt.optimize tyCtx),
    ("ConstProp", ConstPropOpt.optimize tyCtx),
    ("ConstHoist", ConstHoistOpt.optimize tyCtx),
    ("CSE", CSEOpt.optimize tyCtx),
    ("DAE", DAEOpt.optimize tyCtx),
    ("LICM", LICMOpt.optimize tyCtx),
    ("ConstProp", ConstPropOpt.optimize tyCtx),
    ("ConstHoist", ConstHoistOpt.optimize tyCtx),
    ("CSE", CSEOpt.optimize tyCtx),
    ("DAE", DAEOpt.optimize tyCtx),
    ("LICM", LICMOpt.optimize tyCtx),
    ("ConstProp", ConstPropOpt.optimize tyCtx),
    ("ConstHoist", ConstHoistOpt.optimize tyCtx),
    ("CSE", CSEOpt.optimize tyCtx),
    ("DAE", DAEOpt.optimize tyCtx),
  -- Phase 3: late FMAFusion
    ("FMAFusion", FMAFusionOpt.optimize tyCtx),
  -- Phase 4: cleanup + register allocation
    ("DCE", DCEOpt.optimize tyCtx),
    ("Peephole", PeepholeOpt.optimize tyCtx),
    ("RegAlloc", RegAllocOpt.optimize tyCtx) ]

/-- Front-load: ConstProp/DCE/CSE/ConstProp/DAE before the LICM cluster. -/
def prefixPasses (tyCtx : TyCtx) : List (String × (Prog → ECertificate)) :=
  [ ("ConstProp", ConstPropOpt.optimize tyCtx),
    ("DCE", DCEOpt.optimize tyCtx),
    ("CSE", CSEOpt.optimize tyCtx),
    ("ConstProp", ConstPropOpt.optimize tyCtx),
    ("DAE", DAEOpt.optimize tyCtx) ]

/-- One iteration of the LICM cluster: hoist consts one loop level, then
    canonicalize copies and kill writes the redundancy passes have made dead. -/
def licmClusterPasses (tyCtx : TyCtx) : List (String × (Prog → ECertificate)) :=
  [ ("LICM", LICMOpt.optimize tyCtx),
    ("ConstProp", ConstPropOpt.optimize tyCtx),
    ("ConstHoist", ConstHoistOpt.optimize tyCtx),
    ("CSE", CSEOpt.optimize tyCtx),
    ("DAE", DAEOpt.optimize tyCtx) ]

/-- Suffix: late FMAFusion, then cleanup + register allocation.
    CopyProp is intentionally NOT included here. Empirically (see commit
    history), TAC-level copy propagation extends live ranges of the
    surviving variable past where the eliminated copy's uses lived, which
    fights the Stage 1 Chaitin spill heuristic and causes regressions on
    heavy kernels (-17% on k18, -3% on k08). The pass exists in
    CopyPropOpt.lean if needed for experimentation; coalescing inside
    RegAlloc would be the next thing to try if copy elimination is wanted. -/
def suffixPasses (tyCtx : TyCtx) : List (String × (Prog → ECertificate)) :=
  [ ("FMAFusion", FMAFusionOpt.optimize tyCtx),
    ("DCE", DCEOpt.optimize tyCtx),
    ("Peephole", PeepholeOpt.optimize tyCtx),
    ("RegAlloc", RegAllocOpt.optimize tyCtx) ]

/-- Standard pipeline with a fixed-point LICM cluster.

    Runs `prefixPasses`, then iterates `licmClusterPasses` until the program
    code is unchanged after a full iteration or 5 iterations have run
    (whichever comes first), then runs `suffixPasses`.

    Equivalent to `applyPasses tyCtx (standardPasses tyCtx)` when no further
    code change occurs after the first cluster iteration; can be more or less
    work depending on how quickly a fixed point is reached. -/
def applyStandardPipelineFixpoint (tyCtx : TyCtx) (p : Prog) : Prog :=
  let p := applyPasses tyCtx (prefixPasses tyCtx) p
  let p := applyPassesUntilFixedOrN tyCtx (licmClusterPasses tyCtx) 5 p
  applyPasses tyCtx (suffixPasses tyCtx) p

/-- **Legacy unrolled-passes driver core.**

    Same shape as the production driver `compileProgramAst`, but uses the
    unrolled `applyPasses tyCtx (standardPasses tyCtx)` pipeline instead
    of `applyStandardPipelineFixpoint`.  Retained because some top-level
    theorems historically reasoned about this form. -/
def compileProgramAstOld (prog : Program) (noOpt : Bool := false) :
    Except String VerifiedAsmResult :=
  if prog.wellFormed then
    verifiedGenerateAsm prog.tyCtx
      (applyPasses prog.tyCtx (if noOpt then [] else standardPasses prog.tyCtx)
        prog.compileToTAC)
  else
    .error "program is not well-formed"

/-- **Verified core of the compiler driver.**

    From a parsed `Program` AST, runs the post-parse compilation pipeline:
    well-formedness check, AST → TAC, optimization passes (or none if `noOpt`),
    verified ARM codegen.  Returns a `VerifiedAsmResult` carrying the proof
    payload (`GenAsmSpec`), or an error string if the program is not well-formed.

    Optimization uses `applyStandardPipelineFixpoint` (front-load prefix →
    LICM cluster fixed-point ≤5 → suffix), matching what `compilePipeline`
    and `compileToAsmWith` actually run.  The connecting top-level theorems
    `compileProgramAst_correctness`, `compileProgramAst_total`,
    `compileProgramAst_arm_*` reason about this function. -/
def compileProgramAst (prog : Program) (noOpt : Bool := false) :
    Except String VerifiedAsmResult :=
  if prog.wellFormed then
    let opt :=
      if noOpt then prog.compileToTAC
      else applyStandardPipelineFixpoint prog.tyCtx prog.compileToTAC
    verifiedGenerateAsm prog.tyCtx opt
  else
    .error "program is not well-formed"

def compileToAsmWith (input : String) (noOpt : Bool) : Except String String := do
  let prog ← parseProgram input
  let r ← compileProgramAst prog noOpt
  let opt :=
    if noOpt then prog.compileToTAC
    else applyStandardPipelineFixpoint prog.tyCtx prog.compileToTAC
  formatVerifiedAsm r opt

/-- **Structured compilation pipeline.**  Each stage maps directly to a
    construct used in the top-level correctness theorems
    (`while_to_arm_correctness` et al.).  Naming the stages explicitly here
    makes the driver's structure mirror the verified pipeline.

    Stages:
    1. **Parser (unverified).**  `parseProgram : String → Except String Program`.
    2. **Well-formedness check.**  `prog.wellFormed = true` is the precondition
       of every top-level theorem.
    3. **AST → TAC (verified).**  `prog.compileToTAC : Prog`, certified by
       `compileToTAC_wellTyped`, `compileToTAC_stepClosed`,
       `compileToTAC_checkBranchTargets`, `compileToTAC_codegenPrereqs`.
    4. **Optimizations (verified, certificate-checked).**  `applyPasses tyCtx
       passes (compileToTAC prog)` — each pass is checked by the executable
       certificate checker; preservation lemmas are
       `applyPasses_preserves_{halt_am, errorDiv, errorBounds, diverge,
       invariants, stepClosedInBounds}`.
    5. **TAC → verified ASM core (verified).**  `verifiedGenerateAsm tyCtx
       opt = .ok r`, where `r : VerifiedAsmResult` carries the proof
       payload (`GenAsmSpec`).  Totality from `generateAsm_total_with_passes`.
    6. **Wrap + pretty-print (unverified).**  `formatVerifiedAsm r opt`
       renders the verified core to assembly text by adding AArch64
       prologue/epilogue, runtime error handlers, format strings, and
       array data sections. -/
def compilePipeline (input : String) (noOpt : Bool := false) :
    Except String String := do
  -- Stage 1: parse (unverified)
  let prog ← parseProgram input
  -- Stages 2-5: verified core (well-formedness, AST→TAC, optimizations, verified ASM)
  let r ← compileProgramAst prog noOpt
  -- Stage 6: wrap + pretty-print (unverified)
  let opt :=
    if noOpt then prog.compileToTAC
    else applyStandardPipelineFixpoint prog.tyCtx prog.compileToTAC
  formatVerifiedAsm r opt

def compileToAsm (input : String) : Except String String :=
  compileToAsmWith input false

-- ============================================================
-- § 7. IO driver: write assembly, assemble, and run
-- ============================================================

/-- Write assembly to a file, assemble it, link it, and run the resulting binary. -/
def assembleAndRun (asm : String) (asmFile binFile : String := "/tmp/tac_out.s")
    : IO UInt32 := do
  let asmPath := asmFile
  let binPath := binFile.replace ".s" ""
  IO.FS.writeFile ⟨asmPath⟩ asm
  -- Assemble and link via cc (handles macOS linker details)
  let result ← IO.Process.output {
    cmd := "cc"
    args := #["-o", binPath, asmPath, "-lSystem"]
  }
  if result.exitCode != 0 then
    IO.eprintln s!"Assembly failed:\n{result.stderr}"
    return 1
  -- Run
  let run ← IO.Process.output { cmd := binPath }
  IO.print run.stdout
  if run.exitCode != 0 then
    IO.eprintln run.stderr
  return run.exitCode

-- ============================================================
-- § 8. Tests
-- ============================================================

-- Generate assembly for a simple program
#eval! compileToAsm "
  var x : int, y : int;
  x := 3;
  y := x + 4
"

-- Generate assembly for an array program
#eval! compileToAsm "
  var i : int, x : int;
  arr[0] := 42;
  i := 1;
  arr[i] := 100;
  i := 0;
  x := arr[i]
"

-- Generate assembly for sum 1..n (n initialized to 0, so sum = 0)
#eval! compileToAsm "
  var n : int, s : int, i : int;
  s := 0;
  i := 1;
  while (i <= n) {
    s := s + i;
    i := i + 1
  }
"
