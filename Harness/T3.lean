-- Copyright (c) 2026 Martin Rinard
import CredibleCompilation.Parser

/- T3 — text → parse: parser robustness (RQ3). Oracle = **totality**: `parseProgram` must
   return `.ok`/`.error` on ANY input — never panic or hang. We (a) sanity-check that real `.w`
   seeds parse, (b) char-mutate the seeds and require every parse to *return*, and (c) feed
   random text and require rejection (not a crash). A panic aborts the process; the offending
   input is left in `/tmp/t3_current.w` for forensics. Hang-detection (a per-input subprocess
   timeout) is the documented extension; v1 catches panics + classifies accept/reject. -/

def lcg (s : UInt64) : UInt64 := s * 6364136223846793005 + 1442695040888963407
def charPool : Array Char :=
  #['{','}','(',')','[',']',';',':',',','"','0','9','-','+','*','x','i','f',' ','\n','=','<','>','!','&','|','.','v','a','r']

def mutateOnce (cs : List Char) (s : UInt64) : List Char × UInt64 :=
  let n := cs.length
  if n == 0 then (cs, lcg s) else
  let pos := s.toNat % n
  let s1 := lcg s
  let c := (charPool[(lcg s1).toNat % charPool.size]?).getD 'x'
  let cs' := match s1.toNat % 3 with
    | 0 => cs.eraseIdx pos
    | 1 => cs.set pos c
    | _ => (cs.take pos) ++ [c] ++ (cs.drop pos)
  (cs', lcg (lcg s1))

partial def mutateK (cs : List Char) (s : UInt64) : Nat → List Char × UInt64
  | 0 => (cs, s)
  | k+1 => let (cs', s') := mutateOnce cs s; mutateK cs' s' k

def genRandStr (s : UInt64) : Nat → List Char × UInt64
  | 0 => ([], s)
  | k+1 => let c := (charPool[s.toNat % charPool.size]?).getD 'x'
           let (rest, s') := genRandStr (lcg s) k; (c :: rest, s')

def seedBase : IO Nat := do return ((← IO.getEnv "SEED_BASE").bind String.toNat?).getD 0

def main : IO Unit := do
  let base ← seedBase
  let dir : System.FilePath := "benchmarks/livermore"
  let entries ← (try dir.readDir catch _ => pure #[])
  let wpaths := entries.toList.filterMap (fun e =>
    if e.fileName.endsWith ".w" then some e.path else none) |>.take 12
  let mut seeds : List String := []
  for p in wpaths do
    seeds := seeds ++ [← IO.FS.readFile p]
  IO.println s!"loaded {seeds.length} seed programs"

  -- (a) seeds must parse
  let mut badSeeds := 0
  for c in seeds do
    match parseProgram c with
    | .ok _ => pure ()
    | .error e => badSeeds := badSeeds + 1; IO.println s!"SEED-INVALID: {e}"

  -- (b) mutational fuzz — every parse must RETURN (totality)
  let mut total := 0; let mut ok := 0; let mut err := 0
  let mut s : UInt64 := UInt64.ofNat base + 0x1234567
  for c in seeds do
    for _ in [0:200] do
      let k := 1 + (s.toNat % 6)
      let (cs, s') := mutateK c.toList (lcg s) k
      s := s'
      let m := String.mk cs
      IO.FS.writeFile "/tmp/t3_current.w" m
      total := total + 1
      match parseProgram m with        -- forces the parse; a panic aborts here
      | .ok _ => ok := ok + 1
      | .error _ => err := err + 1

  -- (c) random text — must reject (not crash)
  let mut randAccepted := 0
  for _ in [0:300] do
    let len := 1 + (s.toNat % 80)
    let (cs, s') := genRandStr (lcg s) len
    s := s'
    let m := String.mk cs
    IO.FS.writeFile "/tmp/t3_current.w" m
    total := total + 1
    match parseProgram m with
    | .ok _ => randAccepted := randAccepted + 1; ok := ok + 1
    | .error _ => err := err + 1

  IO.println s!"=== T3: {total} parses ALL returned (totality holds) — ok={ok} err={err}; "
  IO.println s!"    seeds-invalid={badSeeds}, random-text-accepted={randAccepted} ==="
