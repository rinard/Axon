-- Copyright (c) 2026 Martin Rinard
import CredibleCompilation.CodeGen

/- T1-branch: co-simulate forward control flow (cbz/cbnz) against the machine.
   Branch targets are forward-only, so the program counter is monotone and the
   model run terminates; the model is driven by `step` (mirroring the verified
   execStep) until pc runs off the end. The asm emits a `.Li:` label before each
   instruction so the printer's `.L{target}` references resolve. -/

def step (prog : ArmProg) (s : ArmState) : Option ArmState :=
  match prog[s.pc]? with
  | some (.mov rd imm)    => some (s.setReg rd imm |>.nextPC)
  | some (.movR rd rn)    => some (s.setReg rd (s.regs rn) |>.nextPC)
  | some (.addR rd rn rm) => some (s.setReg rd (s.regs rn + s.regs rm) |>.nextPC)
  | some (.subR rd rn rm) => some (s.setReg rd (s.regs rn - s.regs rm) |>.nextPC)
  | some (.mulR rd rn rm) => some (s.setReg rd (s.regs rn * s.regs rm) |>.nextPC)
  | some (.andR rd rn rm) => some (s.setReg rd (s.regs rn &&& s.regs rm) |>.nextPC)
  | some (.orrR rd rn rm) => some (s.setReg rd (s.regs rn ||| s.regs rm) |>.nextPC)
  | some (.eorR rd rn rm) => some (s.setReg rd (s.regs rn ^^^ s.regs rm) |>.nextPC)
  | some (.cbz rn lbl)    => some (if s.regs rn = 0 then { s with pc := lbl } else s.nextPC)
  | some (.cbnz rn lbl)   => some (if s.regs rn = 0 then s.nextPC else { s with pc := lbl })
  | _ => none

/-- Drive the model to termination: step until pc leaves the program. Forward-only
    branches make pc monotone, so `fuel = size+1` always suffices. -/
def runEnd (prog : ArmProg) (s : ArmState) : Nat → Option ArmState
  | 0     => some s
  | k + 1 => if s.pc ≥ prog.size then some s
             else match step prog s with
                  | some s' => runEnd prog s' k
                  | none    => none

def allRegs : List ArmReg :=
  [.x0,.x1,.x2,.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13,.x14,.x15,
   .x16,.x17,.x18,.x19,.x20,.x21,.x22,.x23,.x24,.x25,.x26,.x27,.x28]
def usableRegs : List ArmReg := allRegs.filter (fun r => r != .x16 && r != .x17 && r != .x18)
def regIdx (r : ArmReg) : Nat := allRegs.idxOf r
def regName (r : ArmReg) : String := "x" ++ toString (regIdx r)

def lcg (s : UInt64) : UInt64 := s * 6364136223846793005 + 1442695040888963407
def pickReg (s : UInt64) : ArmReg × UInt64 := ((usableRegs[s.toNat % usableRegs.length]?).getD .x0, lcg s)
-- bias toward 0 so cbz/cbnz go both ways
def edgePool : Array UInt64 := #[0, 0, 0, 1, 2, 7, 0xFFFFFFFFFFFFFFFF, 100, 0, 64]

/-- Generate instruction at position `i` of a length-`n` program. Branches target
    a strictly-greater label in `[i+1, n]` (n = one past the last instruction). -/
def genAt (i n : Nat) (s0 : UInt64) : ArmInstr × UInt64 :=
  let op := s0.toNat % 12
  let (rd, s1) := pickReg (lcg s0)
  let (rn, s2) := pickReg s1
  let (rm, s3) := pickReg s2
  let tgt := i + 1 + (s3.toNat % (n - i))
  match op with
  | 0 => (.mov rd (BitVec.ofNat 64 (s1.toNat % 4096)), s1)
  | 1 => (.movR rd rn, s1)
  | 2 => (.addR rd rn rm, s3)
  | 3 => (.subR rd rn rm, s3)
  | 4 => (.mulR rd rn rm, s3)
  | 5 => (.andR rd rn rm, s3)
  | 6 => (.orrR rd rn rm, s3)
  | 7 => (.eorR rd rn rm, s3)
  | 8 | 9  => (.cbz rn tgt, s3)
  | _      => (.cbz rd tgt, s3)

partial def genProg (n : Nat) (s : UInt64) : List ArmInstr × UInt64 :=
  let rec go (i : Nat) (s : UInt64) : List ArmInstr × UInt64 :=
    if i ≥ n then ([], s)
    else let (instr, s') := genAt i n s
         let (rest, s'') := go (i + 1) s'
         (instr :: rest, s'')
  go 0 s

def genInits (s : UInt64) : Nat → Array UInt64 × UInt64
  | 0 => (#[], s)
  | k+1 => let v := edgePool[s.toNat % edgePool.size]!; let (r, s') := genInits (lcg s) k; (#[v] ++ r, s')

def mkInit (vals : Array UInt64) : ArmState :=
  { regs := fun r => BitVec.ofNat 64 (vals.getD (regIdx r) 0).toNat,
    stack := fun _ => 0, pc := 0, flags := Flags.mk 0 0 }

-- per-instruction labels so `.L{target}` references resolve; `.L{n}` is the exit.
def labeledBody (instrs : List ArmInstr) : List String :=
  let n := instrs.length
  let lines := (instrs.zipIdx).flatMap (fun (instr, i) => s!".L{i}:" :: renderAsmBody [instr])
  lines ++ [s!".L{n}:"]

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

def runOne (dir : String) (seed n : Nat) : IO (Option String) := do
  let s0 := lcg (UInt64.ofNat (seed + 1))
  let (instrs, s1) := genProg n s0
  let (inits, _)   := genInits s1 29
  let prog := instrs.toArray
  match runEnd prog (mkInit inits) (n + 1) with
  | none => return some s!"seed {seed}: runEnd=none"
  | some sf =>
    let body := labeledBody instrs
    let sp := s!"{dir}/tb_{seed}.s"; let cp := s!"{dir}/tb_{seed}.c"; let bp := s!"{dir}/tb_{seed}"
    IO.FS.writeFile sp (asmFile body)
    IO.FS.writeFile cp (cFile inits)
    let cc ← IO.Process.output { cmd := "cc", args := #["-o", bp, sp, cp] }
    if cc.exitCode != 0 then return some s!"seed {seed}: cc failed\n{cc.stderr}"
    let run ← IO.Process.output { cmd := bp, args := #[] }
    let outs := (run.stdout.splitOn "\n").filterMap (fun l => l.toNat?)
    for r in usableRegs do
      let m := (sf.regs r).toNat
      let mach := outs.getD (regIdx r) 0
      if m != mach then
        return some s!"DIVERGENCE seed={seed} {regName r}: model={m} machine={mach}\n{String.intercalate "\n" body}"
    return none

def seedBase : IO Nat := do return ((← IO.getEnv "SEED_BASE").bind String.toNat?).getD 0

def main : IO Unit := do
  let base ← seedBase
  let dir := "/tmp/tb"
  let _ ← IO.Process.output { cmd := "mkdir", args := #["-p", dir] }
  let mut div := 0; let mut n := 0
  for seed in [base:base+200] do
    n := n + 1
    match ← runOne dir seed 10 with
    | none => pure ()
    | some msg => div := div + 1; IO.println msg
  IO.println s!"\n=== T1-branch: {n} sequences, {div} divergences ==="
