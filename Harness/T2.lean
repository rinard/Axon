-- Copyright (c) 2026 Martin Rinard
import CredibleCompilation.WhileLang
import CredibleCompilation.Parser

/- T2 — AST round-trip: generate a type-correct `Program`, print it (`toString`), parse it
   (`parseProgram`), print the result, and compare the two strings. A mismatch (or a parse
   failure on a well-formed AST) is a parser/printer bug (RQ3). The oracle is string-level
   idempotence `print = print ∘ parse ∘ print` — the AST carries `Float` (no lawful structural
   DecidableEq), so we compare printed forms. v1 covers the int subset; floats/bools/arrays/
   control are the documented coverage levers. -/

instance : Inhabited SExpr := ⟨.lit 0⟩
instance : Inhabited SBool := ⟨.lit false⟩
instance : Inhabited Stmt := ⟨.skip⟩

def lcg (s : UInt64) : UInt64 := s * 6364136223846793005 + 1442695040888963407
def intPool : Array Int := #[0, 1, -1, 2, 7, -7, 255, -256, 2147483647, -2147483648, 100, 63]
def vars : List String := ["a", "b", "c", "d"]
def binOps : Array BinOp := #[.add,.sub,.mul,.div,.mod,.band,.bor,.bxor,.shl,.shr]
def cmpOps : Array CmpOp := #[.eq,.ne,.lt,.le]

partial def genSExpr (s : UInt64) : Nat → SExpr × UInt64
  | 0 =>
    if s.toNat % 2 == 0 then (.lit (intPool[s.toNat % intPool.size]!), lcg s)
    else (.var ((vars[s.toNat % vars.length]?).getD "a"), lcg s)
  | d+1 =>
    match s.toNat % 4 with
    | 0 => (.lit (intPool[s.toNat % intPool.size]!), lcg s)
    | 1 => (.var ((vars[s.toNat % vars.length]?).getD "a"), lcg s)
    | _ =>
      let op := (binOps[s.toNat % binOps.size]?).getD .add
      let (a, s1) := genSExpr (lcg s) d
      let (b, s2) := genSExpr s1 d
      (.bin op a b, s2)

partial def genSBool (s : UInt64) : Nat → SBool × UInt64
  | 0 =>
    let (a, s1) := genSExpr (lcg s) 1
    let (b, s2) := genSExpr s1 1
    (.cmp ((cmpOps[s.toNat % cmpOps.size]?).getD .lt) a b, s2)
  | d+1 =>
    -- NB: SBool.lit true/false is parser-UNREACHABLE (Parser desugars true→`0==0`, false→`0!=0`),
    -- so we don't generate it here — a round-trip test must use parser-reachable ASTs.
    match s.toNat % 4 with
    | 0 => let (b, s1) := genSBool (lcg s) d; (.not b, s1)
    | 1 => let (x, s1) := genSBool (lcg s) d; let (y, s2) := genSBool s1 d; (.and x y, s2)
    | 2 => let (x, s1) := genSBool (lcg s) d; let (y, s2) := genSBool s1 d; (.or x y, s2)
    | _ => let (a, s1) := genSExpr (lcg s) 1; let (b, s2) := genSExpr s1 1
           (.cmp ((cmpOps[s.toNat % cmpOps.size]?).getD .lt) a b, s2)

partial def genStmt (s : UInt64) : Nat → Stmt × UInt64
  | 0 =>
    if s.toNat % 3 == 0 then (.skip, lcg s)
    else let (e, s1) := genSExpr (lcg s) 1; (.assign ((vars[s.toNat % vars.length]?).getD "a") e, s1)
  | d+1 =>
    match s.toNat % 5 with
    | 0 => let (e, s1) := genSExpr (lcg s) 2; (.assign ((vars[s.toNat % vars.length]?).getD "a") e, s1)
    | 1 => let (a, s1) := genStmt (lcg s) d; let (b, s2) := genStmt s1 d; (.seq a b, s2)
    | 2 => let (c, s1) := genSBool (lcg s) 1; let (t, s2) := genStmt s1 d; let (e, s3) := genStmt s2 d
           (.ite c t e, s3)
    | 3 => let (c, s1) := genSBool (lcg s) 1; let (b, s2) := genStmt s1 d; (.loop c b, s2)
    | _ => let (e, s1) := genSExpr (lcg s) 2; (.assign ((vars[s.toNat % vars.length]?).getD "a") e, s1)

def genProgram (s : UInt64) : Program × UInt64 :=
  let (body, s') := genStmt s 3
  ({ decls := [("a", .int), ("b", .int), ("c", .int), ("d", .int)], body := body }, s')

def seedBase : IO Nat := do return ((← IO.getEnv "SEED_BASE").bind String.toNat?).getD 0

def main : IO Unit := do
  let base ← seedBase
  let mut div := 0; let mut n := 0
  for seed in [base:base+300] do
    n := n + 1
    let s0 := lcg (UInt64.ofNat (seed + 1))
    let (prog, _) := genProgram s0
    let t1 := toString prog
    match parseProgram t1 with
    | .error e =>
      div := div + 1
      IO.println s!"PARSE-FAIL seed={seed}: {e}\n--- printed ---\n{t1}\n"
    | .ok prog' =>
      let t2 := toString prog'
      if t1 != t2 then
        div := div + 1
        IO.println s!"ROUNDTRIP-MISMATCH seed={seed}\n--- t1 ---\n{t1}\n--- t2 ---\n{t2}\n"
  IO.println s!"=== T2: {n} programs, {div} round-trip failures ==="
