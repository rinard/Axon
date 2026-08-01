-- Copyright (c) 2026 Martin Rinard
import CredibleCompilation.CodeGen

/- T1-stack: co-simulate stack memory (ldr/str → `[sp,#off]`) against the machine.
   Offsets live in the 96..159 slice of the frame, which is allocated but unused by
   the register-save prologue; that slice is pre-zeroed so a load before any store
   matches the model's zero-initialized stack. -/

def step (prog : ArmProg) (s : ArmState) : Option ArmState :=
  match prog[s.pc]? with
  | some (.mov rd imm)    => some (s.setReg rd imm |>.nextPC)
  | some (.movR rd rn)    => some (s.setReg rd (s.regs rn) |>.nextPC)
  | some (.addR rd rn rm) => some (s.setReg rd (s.regs rn + s.regs rm) |>.nextPC)
  | some (.ldr rd off)    => some (s.setReg rd (s.stack off) |>.nextPC)
  | some (.str rs off)    => some (s.setStack off (s.regs rs) |>.nextPC)
  | _ => none

def run (prog : ArmProg) (s : ArmState) : Nat → Option ArmState
  | 0 => some s
  | n+1 => match step prog s with | some s' => run prog s' n | none => none

def allRegs : List ArmReg :=
  [.x0,.x1,.x2,.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13,.x14,.x15,
   .x16,.x17,.x18,.x19,.x20,.x21,.x22,.x23,.x24,.x25,.x26,.x27,.x28]
def usableRegs : List ArmReg := allRegs.filter (fun r => r != .x16 && r != .x17 && r != .x18)
def regIdx (r : ArmReg) : Nat := allRegs.idxOf r
def regName (r : ArmReg) : String := "x" ++ toString (regIdx r)

def lcg (s : UInt64) : UInt64 := s * 6364136223846793005 + 1442695040888963407
def pickReg (s : UInt64) : ArmReg × UInt64 := ((usableRegs[s.toNat % usableRegs.length]?).getD .x0, lcg s)
def edgePool : Array UInt64 := #[0, 1, 0xFFFFFFFFFFFFFFFF, 0x8000000000000000, 7, 100, 2, 64]
def scratchOffs : Array Nat := #[96, 104, 112, 120, 128, 136, 144, 152]   -- frame slice, 8 slots

def genInstr (s0 : UInt64) : ArmInstr × UInt64 :=
  let op := s0.toNat % 8
  let (rd, s1) := pickReg (lcg s0)
  let (rn, s2) := pickReg s1
  let (rm, s3) := pickReg s2
  let off := scratchOffs[s2.toNat % scratchOffs.size]!
  match op with
  | 0 => (.mov rd (BitVec.ofNat 64 (s1.toNat % 4096)), s1)
  | 1 => (.movR rd rn, s1)
  | 2 => (.addR rd rn rm, s3)
  | 3 | 4 => (.str rd off, s2)       -- store reg → scratch
  | _ => (.ldr rd off, s2)           -- load scratch → reg

partial def genSeq (s : UInt64) : Nat → List ArmInstr × UInt64
  | 0 => ([], s)
  | n+1 => let (i, s') := genInstr s; let (rest, s'') := genSeq s' n; (i :: rest, s'')

def genInits (s : UInt64) : Nat → Array UInt64 × UInt64
  | 0 => (#[], s)
  | k+1 => let v := edgePool[s.toNat % edgePool.size]!; let (r, s') := genInits (lcg s) k; (#[v] ++ r, s')

def mkInit (vals : Array UInt64) : ArmState :=
  { regs := fun r => BitVec.ofNat 64 (vals.getD (regIdx r) 0).toNat,
    stack := fun _ => 0, pc := 0, flags := Flags.mk 0 0 }

def asmFile (body : List String) : String :=
  let loads  := usableRegs.map (fun r => s!"  ldr {regName r}, [x16, #{8 * regIdx r}]")
  let stores := usableRegs.map (fun r => s!"  str {regName r}, [x16, #{8 * regIdx r}]")
  String.intercalate "\n" ([
    ".global _t1run", ".align 2", "_t1run:",
    "  stp x29, x30, [sp, #-160]!",
    "  stp x19, x20, [sp, #16]", "  stp x21, x22, [sp, #32]",
    "  stp x23, x24, [sp, #48]", "  stp x25, x26, [sp, #64]",
    "  stp x27, x28, [sp, #80]",
    -- pre-zero the scratch slice 96..159 so loads-before-stores read 0
    "  stp xzr, xzr, [sp, #96]", "  stp xzr, xzr, [sp, #112]",
    "  stp xzr, xzr, [sp, #128]", "  stp xzr, xzr, [sp, #144]",
    "  mov x16, x0"] ++ loads ++ body ++ stores ++ [
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
  let (instrs, s1) := genSeq s0 n
  let (inits, _)   := genInits s1 29
  let prog := instrs.toArray
  match run prog (mkInit inits) instrs.length with
  | none => return some s!"seed {seed}: run=none"
  | some sf =>
    let body := renderAsmBody instrs
    let sp := s!"{dir}/ts_{seed}.s"; let cp := s!"{dir}/ts_{seed}.c"; let bp := s!"{dir}/ts_{seed}"
    IO.FS.writeFile sp (asmFile body)
    IO.FS.writeFile cp (cFile inits)
    let cc ← IO.Process.output { cmd := "cc", args := #["-o", bp, sp, cp] }
    if cc.exitCode != 0 then return some s!"seed {seed}: cc failed\n{cc.stderr}"
    let r ← IO.Process.output { cmd := bp, args := #[] }
    let outs := (r.stdout.splitOn "\n").filterMap (fun l => l.toNat?)
    for reg in usableRegs do
      let m := (sf.regs reg).toNat
      let mach := outs.getD (regIdx reg) 0
      if m != mach then
        return some s!"DIVERGENCE seed={seed} {regName reg}: model={m} machine={mach}\n{String.intercalate "\n" body}"
    return none

def seedBase : IO Nat := do return ((← IO.getEnv "SEED_BASE").bind String.toNat?).getD 0

def main : IO Unit := do
  let base ← seedBase
  let dir := "/tmp/ts"
  let _ ← IO.Process.output { cmd := "mkdir", args := #["-p", dir] }
  let mut div := 0; let mut cnt := 0
  for seed in [base:base+200] do
    cnt := cnt + 1
    match ← runOne dir seed 10 with
    | none => pure ()
    | some msg => div := div + 1; IO.println msg
  IO.println s!"\n=== T1-stack: {cnt} sequences, {div} divergences ==="
