-- Copyright (c) 2026 Martin Rinard
import CredibleCompilation.CodeGen

/- T1-array: co-simulate global array memory (arrLd/arrSt) against the machine.
   Arrays are `.comm _arr_{name}` globals (BSS-zero, matching the model's zero-init
   arrayMem). Index registers are held to 0..15 (in bounds). x0 is excluded from the
   diff and from operands because the printer uses it as adrp address scratch — a
   clobber the relational model does not reflect (faithful only because codegen keeps
   x0 dead there). -/

def step (prog : ArmProg) (s : ArmState) : Option ArmState :=
  match prog[s.pc]? with
  | some (.mov rd imm)         => some (s.setReg rd imm |>.nextPC)
  | some (.movR rd rn)         => some (s.setReg rd (s.regs rn) |>.nextPC)
  | some (.addR rd rn rm)      => some (s.setReg rd (s.regs rn + s.regs rm) |>.nextPC)
  | some (.arrLd dst arr ix)   => some (s.setReg dst (s.arrayMem arr (s.regs ix)) |>.nextPC)
  | some (.arrSt arr ix rv)    => some (s.setArrayMem arr (s.regs ix) (s.regs rv) |>.nextPC)
  | _ => none

def run (prog : ArmProg) (s : ArmState) : Nat → Option ArmState
  | 0 => some s
  | n+1 => match step prog s with | some s' => run prog s' n | none => none

def allRegs : List ArmReg :=
  [.x0,.x1,.x2,.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13,.x14,.x15,
   .x16,.x17,.x18,.x19,.x20,.x21,.x22,.x23,.x24,.x25,.x26,.x27,.x28]
def regIdx (r : ArmReg) : Nat := allRegs.idxOf r
def regName (r : ArmReg) : String := "x" ++ toString (regIdx r)
-- registers loaded/compared (exclude reserved x16/x17/x18 and the adrp-scratch x0)
def liveRegs : List ArmReg :=
  [.x1,.x2,.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13,.x14,.x15,
   .x19,.x20,.x21,.x22,.x23,.x24,.x25,.x26,.x27,.x28]
def dataRegs : List ArmReg :=    -- write targets: never the index regs (keep them in-bounds)
  [.x1,.x2,.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13,.x14,.x15,.x19,.x20,.x21,.x22,.x23,.x24]
def idxRegs : List ArmReg := [.x25,.x26,.x27,.x28]   -- init 0..15, used only as indices
def arrNames : Array String := #["A", "B"]

def lcg (s : UInt64) : UInt64 := s * 6364136223846793005 + 1442695040888963407
def pick (rs : List ArmReg) (s : UInt64) : ArmReg × UInt64 := ((rs[s.toNat % rs.length]?).getD .x1, lcg s)
def edgePool : Array UInt64 := #[0, 1, 0xFFFFFFFFFFFFFFFF, 0x8000000000000000, 7, 100, 2, 42]

def genInstr (s0 : UInt64) : ArmInstr × UInt64 :=
  let op := s0.toNat % 7
  let (rd, s1) := pick dataRegs (lcg s0)
  let (rn, s2) := pick dataRegs s1
  let (rm, s3) := pick dataRegs s2
  let (ix, s4) := pick idxRegs s3
  let nm := arrNames[s2.toNat % arrNames.size]!
  match op with
  | 0 => (.mov rd (BitVec.ofNat 64 (s1.toNat % 4096)), s1)
  | 1 => (.movR rd rn, s1)
  | 2 => (.addR rd rn rm, s3)
  | 3 | 4 => (.arrSt nm ix rd, s4)        -- store rd → arr[ix]
  | _ => (.arrLd rd nm ix, s4)            -- load arr[ix] → rd

partial def genSeq (s : UInt64) : Nat → List ArmInstr × UInt64
  | 0 => ([], s)
  | n+1 => let (i, s') := genInstr s; let (rest, s'') := genSeq s' n; (i :: rest, s'')

def genInits (s : UInt64) : Nat → Array UInt64 × UInt64
  | 0 => (#[], s)
  | k+1 => let v := edgePool[s.toNat % edgePool.size]!; let (r, s') := genInits (lcg s) k; (#[v] ++ r, s')
-- hold index regs (idx ≥ 25) to 0..15
def boundIdx (a : Array UInt64) : Array UInt64 :=
  (List.range a.size).foldl (fun acc i => if i ≥ 25 then acc.set! i (acc.getD i 0 % 16) else acc) a

def mkInit (vals : Array UInt64) : ArmState :=
  { regs := fun r => BitVec.ofNat 64 (vals.getD (regIdx r) 0).toNat,
    stack := fun _ => 0, pc := 0, flags := Flags.mk 0 0 }

def asmFile (body : List String) : String :=
  let loads  := liveRegs.map (fun r => s!"  ldr {regName r}, [x16, #{8 * regIdx r}]")
  let stores := liveRegs.map (fun r => s!"  str {regName r}, [x16, #{8 * regIdx r}]")
  String.intercalate "\n" ([
    ".global _t1run", ".align 2", "_t1run:",
    "  stp x29, x30, [sp, #-160]!",
    "  stp x19, x20, [sp, #16]", "  stp x21, x22, [sp, #32]",
    "  stp x23, x24, [sp, #48]", "  stp x25, x26, [sp, #64]",
    "  stp x27, x28, [sp, #80]", "  mov x16, x0"] ++ loads ++ body ++ stores ++ [
    "  ldp x19, x20, [sp, #16]", "  ldp x21, x22, [sp, #32]",
    "  ldp x23, x24, [sp, #48]", "  ldp x25, x26, [sp, #64]",
    "  ldp x27, x28, [sp, #80]", "  ldp x29, x30, [sp], #160", "  ret",
    ".comm _arr_A, 128, 3", ".comm _arr_B, 128, 3", ""])

def cFile (inits : Array UInt64) : String :=
  let vals := String.intercalate ", " ((List.range 29).map (fun i => toString (inits.getD i 0) ++ "ULL"))
  "#include <stdio.h>\n#include <stdint.h>\nextern void t1run(uint64_t*);\n" ++
  "int main(void){\n  uint64_t a[29] = {" ++ vals ++ "};\n" ++
  "  t1run(a);\n  for (int i=0;i<29;i++) printf(\"%llu\\n\",(unsigned long long)a[i]);\n  return 0;\n}\n"

def runOne (dir : String) (seed n : Nat) : IO (Option String) := do
  let s0 := lcg (UInt64.ofNat (seed + 1))
  let (instrs, s1) := genSeq s0 n
  let (inits0, _)  := genInits s1 29
  let inits := boundIdx inits0
  let prog := instrs.toArray
  match run prog (mkInit inits) instrs.length with
  | none => return some s!"seed {seed}: run=none"
  | some sf =>
    let body := renderAsmBody instrs
    let sp := s!"{dir}/ta_{seed}.s"; let cp := s!"{dir}/ta_{seed}.c"; let bp := s!"{dir}/ta_{seed}"
    IO.FS.writeFile sp (asmFile body)
    IO.FS.writeFile cp (cFile inits)
    let cc ← IO.Process.output { cmd := "cc", args := #["-o", bp, sp, cp] }
    if cc.exitCode != 0 then return some s!"seed {seed}: cc failed\n{cc.stderr}"
    let r ← IO.Process.output { cmd := bp, args := #[] }
    let outs := (r.stdout.splitOn "\n").filterMap (fun l => l.toNat?)
    for reg in liveRegs do
      let m := (sf.regs reg).toNat
      let mach := outs.getD (regIdx reg) 0
      if m != mach then
        return some s!"DIVERGENCE seed={seed} {regName reg}: model={m} machine={mach}\n{String.intercalate "\n" body}"
    return none

def seedBase : IO Nat := do return ((← IO.getEnv "SEED_BASE").bind String.toNat?).getD 0

def main : IO Unit := do
  let base ← seedBase
  let dir := "/tmp/ta"
  let _ ← IO.Process.output { cmd := "mkdir", args := #["-p", dir] }
  let mut div := 0; let mut cnt := 0
  for seed in [base:base+200] do
    cnt := cnt + 1
    match ← runOne dir seed 10 with
    | none => pure ()
    | some msg => div := div + 1; IO.println msg
  IO.println s!"\n=== T1-array: {cnt} sequences, {div} divergences ==="
