-- Copyright (c) 2026 Martin Rinard
import CredibleCompilation.DCEOpt

/-!
# Dead Code Elimination Optimizer — Examples

Tests the optimizer on several programs and verifies that the generated
certificates pass `checkCertificateExec`.
-/

open DCEOpt

namespace DCEOptExamples

def exTyCtx : TyCtx := fun _ => .int

-- ============================================================
-- § 1. Dead branch: always-taken ifgoto eliminates fallthrough
-- ============================================================

/-! Original:
    0: x := 1
    1: if x ≠ 0 goto 3    ← always taken (x = 1)
    2: halt                ← DEAD
    3: y := 5
    4: halt

  Expected: pc 2 removed, ifgoto becomes goto
    0: x := 1
    1: goto 2
    2: y := 5
    3: halt
-/

def deadBranchProg : Prog :=
  { code := #[.const "x" (.int 1), .ifgoto (.cmp .ne (.var "x") (.lit 0)) 3, .halt,
              .const "y" (.int 5), .halt],
    observable := ["y"] }

def deadBranchCert := optimize exTyCtx deadBranchProg

#eval! deadBranchCert.trans
#eval! checkCertificateExec deadBranchCert
#eval! checkCertificateVerboseExec deadBranchCert

-- ============================================================
-- § 2. Dead fallthrough: always-false ifgoto
-- ============================================================

/-! Original:
    0: x := 0
    1: if x ≠ 0 goto 4    ← always false (x = 0)
    2: y := 42
    3: halt
    4: z := 99             ← DEAD (never reached)
    5: halt                ← DEAD

  Expected: pcs 4-5 removed, ifgoto becomes goto
    0: x := 0
    1: goto 2
    2: y := 42
    3: halt
-/

def deadFallthroughProg : Prog :=
  { code := #[.const "x" (.int 0), .ifgoto (.cmp .ne (.var "x") (.lit 0)) 4,
              .const "y" (.int 42), .halt, .const "z" (.int 99), .halt],
    observable := ["y"] }

def deadFallthroughCert := optimize exTyCtx deadFallthroughProg

#eval! deadFallthroughCert.trans
#eval! checkCertificateExec deadFallthroughCert
#eval! checkCertificateVerboseExec deadFallthroughCert

-- ============================================================
-- § 3. Goto skips dead block
-- ============================================================

/-! Original:
    0: goto 4
    1: a := 1              ← DEAD
    2: b := 2              ← DEAD
    3: halt                ← DEAD
    4: c := 3
    5: halt

  Expected: pcs 1-3 removed
    0: goto 1
    1: c := 3
    2: halt
-/

def gotoSkipProg : Prog :=
  { code := #[.goto 4, .const "a" (.int 1), .const "b" (.int 2), .halt,
              .const "c" (.int 3), .halt],
    observable := ["c"] }

def gotoSkipCert := optimize exTyCtx gotoSkipProg

#eval! gotoSkipCert.trans
#eval! checkCertificateExec gotoSkipCert
#eval! checkCertificateVerboseExec gotoSkipCert

-- ============================================================
-- § 4. No dead code (all reachable)
-- ============================================================

/-! Original:
    0: x := 5
    1: y := 3
    2: z := x + y
    3: halt

  Expected: no change (all PCs reachable, no deterministic branches)
-/

def noDeadProg : Prog :=
  { code := #[.const "x" (.int 5), .const "y" (.int 3),
              .binop "z" .add "x" "y", .halt],
    observable := ["z"] }

def noDeadCert := optimize exTyCtx noDeadProg

#eval! noDeadCert.trans
#eval! checkCertificateExec noDeadCert
#eval! checkCertificateVerboseExec noDeadCert

-- ============================================================
-- § 5. Loop with dead exit path
-- ============================================================

/-! Original:
    0: n := 1
    1: if n ≠ 0 goto 3    ← always taken (n = 1)
    2: halt                ← DEAD
    3: y := 5
    4: goto 6
    5: halt                ← DEAD (unreachable)
    6: halt

  Expected: pcs 2 and 5 removed
    0: n := 1
    1: goto 2              ← was ifgoto
    2: y := 5
    3: goto 4
    4: halt
-/

def deadExitProg : Prog :=
  { code := #[.const "n" (.int 1), .ifgoto (.cmp .ne (.var "n") (.lit 0)) 3, .halt,
              .const "y" (.int 5), .goto 6, .halt, .halt],
    observable := ["y"] }

def deadExitCert := optimize exTyCtx deadExitProg

#eval! deadExitCert.trans
#eval! checkCertificateExec deadExitCert
#eval! checkCertificateVerboseExec deadExitCert

-- ============================================================
-- § 6. Non-deterministic branch (both sides live)
-- ============================================================

/-! Original:
    0: if x < 10 goto 3   ← x unknown, both paths live
    1: a := 1
    2: halt
    3: b := 2
    4: halt

  Expected: no dead code removed (all reachable), but labels remapped
  (identity mapping since nothing is removed)
-/

def liveBranchProg : Prog :=
  { code := #[.ifgoto (.cmp .lt (.var "x") (.lit 10)) 3, .const "a" (.int 1), .halt,
              .const "b" (.int 2), .halt],
    observable := ["a", "b"] }

def liveBranchCert := optimize exTyCtx liveBranchProg

#eval! liveBranchCert.trans
#eval! checkCertificateExec liveBranchCert
#eval! checkCertificateVerboseExec liveBranchCert

-- ============================================================
-- § 7. Cascading dead code
-- ============================================================

/-! Original:
    0: x := 1
    1: if x ≠ 0 goto 5    ← always taken
    2: a := 10             ← DEAD
    3: b := 20             ← DEAD
    4: halt                ← DEAD
    5: y := 0
    6: if y ≠ 0 goto 8    ← always false (y = 0)
    7: c := 30
    8: halt                ← DEAD (unreachable from the only path)

  Expected: cascade of both eliminations
    0: x := 1
    1: goto 2
    2: y := 0
    3: goto 4
    4: c := 30
    5: halt
-/

def cascadeProg : Prog :=
  { code := #[.const "x" (.int 1), .ifgoto (.cmp .ne (.var "x") (.lit 0)) 5,
              .const "a" (.int 10), .const "b" (.int 20), .halt,
              .const "y" (.int 0), .ifgoto (.cmp .ne (.var "y") (.lit 0)) 8,
              .const "c" (.int 30), .halt],
    observable := ["c"] }

def cascadeCert := optimize exTyCtx cascadeProg

#eval! cascadeCert.trans
#eval! checkCertificateExec cascadeCert
#eval! checkCertificateVerboseExec cascadeCert

end DCEOptExamples
