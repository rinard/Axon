-- Copyright (c) 2026 Martin Rinard
import CredibleCompilation.CodeGen

-- Full executable evaluator (integer/control subset; matches Harness/ArmExec.lean
-- where execStep_sound is proven). Dev uses the masked/correct shift.
def execStep (prog : ArmProg) (s : ArmState) : Option ArmState :=
  match prog[s.pc]? with
  | some (.mov rd imm)    => some (s.setReg rd imm |>.nextPC)
  | some (.movR rd rn)    => some (s.setReg rd (s.regs rn) |>.nextPC)
  | some (.addR rd rn rm) => some (s.setReg rd (s.regs rn + s.regs rm) |>.nextPC)
  | some (.subR rd rn rm) => some (s.setReg rd (s.regs rn - s.regs rm) |>.nextPC)
  | some (.mulR rd rn rm) => some (s.setReg rd (s.regs rn * s.regs rm) |>.nextPC)
  | some (.sdivR rd rn rm)=> some (s.setReg rd (BitVec.sdiv (s.regs rn) (s.regs rm)) |>.nextPC)
  | some (.andR rd rn rm) => some (s.setReg rd (s.regs rn &&& s.regs rm) |>.nextPC)
  | some (.orrR rd rn rm) => some (s.setReg rd (s.regs rn ||| s.regs rm) |>.nextPC)
  | some (.eorR rd rn rm) => some (s.setReg rd (s.regs rn ^^^ s.regs rm) |>.nextPC)
  | some (.cmp rn rm)     => some { s with flags := Flags.mk (s.regs rn) (s.regs rm), pc := s.pc + 1 }
  | some (.cset rd c)     => some (s.setReg rd (if s.flags.condHolds c then (1 : BitVec 64) else 0) |>.nextPC)
  | some (.lslR rd rn rm) => some (s.setReg rd (s.regs rn <<< ((s.regs rm).toNat % 64)) |>.nextPC)
  | some (.asrR rd rn rm) => some (s.setReg rd (BitVec.sshiftRight (s.regs rn) ((s.regs rm).toNat % 64)) |>.nextPC)
  | _ => none

def execRun (prog : ArmProg) (s : ArmState) : Nat → Option ArmState
  | 0     => some s
  | n + 1 => match execStep prog s with
             | some s' => execRun prog s' n
             | none    => none

def allRegs : List ArmReg :=
  [.x0,.x1,.x2,.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13,.x14,.x15,
   .x16,.x17,.x18,.x19,.x20,.x21,.x22,.x23,.x24,.x25,.x26,.x27,.x28]
def usableRegs : List ArmReg := allRegs.filter (fun r => r != .x16 && r != .x17 && r != .x18)
def shiftRegs : List ArmReg := [.x25,.x26,.x27,.x28]   -- init bounded (<128): panic-safe shift amounts
def regIdx (r : ArmReg) : Nat := allRegs.idxOf r
def regName (r : ArmReg) : String := "x" ++ toString (regIdx r)
def allConds : List Cond := [.eq,.ne,.lt,.le,.gt,.ge,.hs,.lo]

def lcg (s : UInt64) : UInt64 := s * 6364136223846793005 + 1442695040888963407
def edgePool : Array UInt64 :=
  #[0, 1, 0xFFFFFFFFFFFFFFFF, 0x8000000000000000, 0x7FFFFFFFFFFFFFFF, 2, 64, 65, 100, 0x100000000, 7, 63]
def genVal (s : UInt64) : UInt64 :=
  if s % 3 == 0 then s else edgePool[s.toNat % edgePool.size]!
def pickReg (rs : List ArmReg) (s : UInt64) : ArmReg × UInt64 :=
  ((rs[s.toNat % rs.length]?).getD .x0, lcg s)

def genInstrs (s0 : UInt64) : List ArmInstr × UInt64 :=
  let op := s0.toNat % 13
  let s1 := lcg s0
  let (rd, s2) := pickReg usableRegs s1
  let (rn, s3) := pickReg usableRegs s2
  let (rm, s4) := pickReg usableRegs s3
  let (sa, s5) := pickReg shiftRegs s4         -- bounded shift-amount register
  let cnd := (allConds[(s2.toNat) % allConds.length]?).getD .eq
  match op with
  | 0  => ([.mov rd (BitVec.ofNat 64 (s2.toNat % 4096))], s2)
  | 1  => ([.movR rd rn], s2)
  | 2  => ([.addR rd rn rm], s4)
  | 3  => ([.subR rd rn rm], s4)
  | 4  => ([.mulR rd rn rm], s4)
  | 5  => ([.sdivR rd rn rm], s4)
  | 6  => ([.andR rd rn rm], s4)
  | 7  => ([.orrR rd rn rm], s4)
  | 8  => ([.eorR rd rn rm], s4)
  | 9  => ([.lslR rd rn sa], s5)
  | 10 => ([.asrR rd rn sa], s5)
  | _  => ([.cmp rn rm, .cset .x0 cnd], s4)      -- paired: flags then condition read

partial def genSeq (s : UInt64) : Nat → List ArmInstr × UInt64
  | 0 => ([], s)
  | n+1 => let (is, s') := genInstrs s; let (rest, s'') := genSeq s' n; (is ++ rest, s'')

def genInits (s : UInt64) : Nat → Array UInt64 × UInt64
  | 0 => (#[], s)
  | n+1 => let v := genVal s; let (rest, s') := genInits (lcg s) n; (#[v] ++ rest, s')

-- bound the shift-amount registers (idx >= 25) to < 128 so the model never panics
def boundShiftRegs (a : Array UInt64) : Array UInt64 :=
  (List.range a.size).foldl (fun acc i =>
    if i >= 25 then acc.set! i (acc.getD i 0 % 128) else acc) a

def mkInit (initVals : Array UInt64) : ArmState :=
  { regs := fun r => BitVec.ofNat 64 (initVals.getD (regIdx r) 0).toNat,
    stack := fun _ => 0, pc := 0, flags := Flags.mk 0 0 }

def asmFile (body : List String) : String :=
  let loads  := usableRegs.map (fun r => s!"  ldr {regName r}, [x16, #{8 * regIdx r}]")
  let stores := usableRegs.map (fun r => s!"  str {regName r}, [x16, #{8 * regIdx r}]")
  String.intercalate "\n" ([
    ".global _t1run", ".align 2", "_t1run:",
    "  stp x29, x30, [sp, #-160]!",
    "  stp x19, x20, [sp, #16]", "  stp x21, x22, [sp, #32]",
    "  stp x23, x24, [sp, #48]", "  stp x25, x26, [sp, #64]",
    "  stp x27, x28, [sp, #80]", "  mov x16, x0"] ++ loads ++ body ++ stores ++ [
    "  ldp x19, x20, [sp, #16]", "  ldp x21, x22, [sp, #32]",
    "  ldp x23, x24, [sp, #48]", "  ldp x25, x26, [sp, #64]",
    "  ldp x27, x28, [sp, #80]", "  ldp x29, x30, [sp], #160", "  ret", ""])

def cFile (inits : Array UInt64) : String :=
  let vals := String.intercalate ", " ((List.range 29).map (fun i => toString (inits.getD i 0) ++ "ULL"))
  "#include <stdio.h>\n#include <stdint.h>\nextern void t1run(uint64_t*);\n" ++
  "int main(void){\n  uint64_t a[29] = {" ++ vals ++ "};\n" ++
  "  t1run(a);\n  for (int i=0;i<29;i++) printf(\"%llu\\n\",(unsigned long long)a[i]);\n  return 0;\n}\n"

def runOne (dir : String) (seed : Nat) (nInstr : Nat) : IO (Option String) := do
  let s0 : UInt64 := lcg (UInt64.ofNat (seed + 1))
  let (instrs, s1) := genSeq s0 nInstr
  let (inits0, _)  := genInits s1 29
  let inits := boundShiftRegs inits0
  let prog := instrs.toArray
  match execRun prog (mkInit inits) instrs.length with
  | none => return some s!"seed {seed}: execRun=none"
  | some sf =>
    let body := renderAsmBody instrs
    let sp := s!"{dir}/t1_{seed}.s"; let cp := s!"{dir}/t1_{seed}.c"; let bp := s!"{dir}/t1_{seed}"
    IO.FS.writeFile sp (asmFile body)
    IO.FS.writeFile cp (cFile inits)
    let cc ← IO.Process.output { cmd := "cc", args := #["-o", bp, sp, cp] }
    if cc.exitCode != 0 then return some s!"seed {seed}: cc failed\n{cc.stderr}"
    let run ← IO.Process.output { cmd := bp, args := #[] }
    let machine := (run.stdout.splitOn "\n").filterMap (fun l => l.toNat?)
    for r in usableRegs do
      let m := (sf.regs r).toNat
      let mach := machine.getD (regIdx r) 0
      if m != mach then
        let bodyStr := String.intercalate "\n" body
        return some s!"DIVERGENCE seed={seed} {regName r}: model={m} machine={mach}\n  body:\n{bodyStr}"
    return none

def seedBase : IO Nat := do return ((← IO.getEnv "SEED_BASE").bind String.toNat?).getD 0

def main : IO Unit := do
  let base ← seedBase
  let dir := "/tmp/t1"
  let _ ← IO.Process.output { cmd := "mkdir", args := #["-p", dir] }
  let mut div := 0; let mut n := 0
  for seed in [base:base+200] do
    n := n + 1
    match ← runOne dir seed 8 with
    | none => pure ()
    | some msg => div := div + 1; IO.println msg
  IO.println s!"\n=== T1: {n} sequences, {div} divergences ==="
