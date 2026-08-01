-- Copyright (c) 2026 Martin Rinard
import CredibleCompilation.PeepholeOpt
import CredibleCompilation.LICMOpt

/-!
# Peephole Optimizer — Examples

Tests the peephole optimizer on several programs and verifies that the
generated certificates pass `checkCertificateExec`.
-/

open PeepholeOpt

namespace PeepholeOptExamples

def exTyCtx : TyCtx := fun _ => .int

-- ============================================================
-- § 1. LICM cleanup: remove goto (pc+1) left by LICM
-- ============================================================

/-! LICM output for classic loop-invariant recomputation:
    0: one := 1
    1: t := a * b
    2: if n ≠ 0 goto 4
    3: halt
    4: s := s + t
    5: goto 6             ← no-op from LICM
    6: n := n - one
    7: goto 2

  Expected after peephole: pc 5 removed
    0: one := 1
    1: t := a * b
    2: if n ≠ 0 goto 4
    3: halt
    4: s := s + t
    5: n := n - one
    6: goto 2
-/

def licmProg : Prog :=
  { code := #[
      .const "one" (.int 1),
      .binop "t" .mul "a" "b",
      .ifgoto (.cmp .ne (.var "n") (.lit 0)) 4,
      .halt,
      .binop "s" .add "s" "t",
      .goto 6,
      .binop "n" .sub "n" "one",
      .goto 2
    ], observable := ["s"] }

def licmCert := optimize exTyCtx licmProg

#eval! licmCert.trans
#eval! checkCertificateExec licmCert
#eval! checkCertificateVerboseExec licmCert

-- ============================================================
-- § 2. Self-copy removal
-- ============================================================

/-! Original:
    0: const x 5
    1: copy x x           ← no-op
    2: const y 3
    3: halt

  Expected: pc 1 removed
    0: const x 5
    1: const y 3
    2: halt
-/

def selfCopyProg : Prog :=
  { code := #[
      .const "x" (.int 5),
      .copy "x" "x",
      .const "y" (.int 3),
      .halt
    ], observable := ["x", "y"] }

def selfCopyCert := optimize exTyCtx selfCopyProg

#eval! selfCopyCert.trans
#eval! checkCertificateExec selfCopyCert
#eval! checkCertificateVerboseExec selfCopyCert

-- ============================================================
-- § 3. Multiple consecutive no-ops
-- ============================================================

/-! Original:
    0: const x 1
    1: goto 2             ← no-op
    2: goto 3             ← no-op
    3: goto 4             ← no-op
    4: const y 2
    5: halt

  Expected: pcs 1-3 removed
    0: const x 1
    1: const y 2
    2: halt
-/

def chainNopProg : Prog :=
  { code := #[
      .const "x" (.int 1),
      .goto 2,
      .goto 3,
      .goto 4,
      .const "y" (.int 2),
      .halt
    ], observable := ["x", "y"] }

def chainNopCert := optimize exTyCtx chainNopProg

#eval! chainNopCert.trans
#eval! checkCertificateExec chainNopCert
#eval! checkCertificateVerboseExec chainNopCert

-- ============================================================
-- § 4. No change (no no-ops)
-- ============================================================

/-! Original:
    0: const x 5
    1: const y 3
    2: binop z add x y
    3: halt

  Expected: unchanged
-/

def noChangeProg : Prog :=
  { code := #[
      .const "x" (.int 5),
      .const "y" (.int 3),
      .binop "z" .add "x" "y",
      .halt
    ], observable := ["z"] }

def noChangeCert := optimize exTyCtx noChangeProg

#eval! noChangeCert.trans
#eval! checkCertificateExec noChangeCert
#eval! checkCertificateVerboseExec noChangeCert

-- ============================================================
-- § 5. Goto targeting a no-op
-- ============================================================

/-! Original:
    0: const x 1
    1: goto 3
    2: goto 3             ← no-op (goto pc+1)
    3: const y 2
    4: halt

  Expected: pc 2 removed, goto at pc 1 remapped
    0: const x 1
    1: goto 2
    2: const y 2
    3: halt
-/

def gotoToNopProg : Prog :=
  { code := #[
      .const "x" (.int 1),
      .goto 3,
      .goto 3,
      .const "y" (.int 2),
      .halt
    ], observable := ["x", "y"] }

def gotoToNopCert := optimize exTyCtx gotoToNopProg

#eval! gotoToNopCert.trans
#eval! checkCertificateExec gotoToNopCert
#eval! checkCertificateVerboseExec gotoToNopCert

-- ============================================================
-- § 6. Ifgoto with no-op after fallthrough
-- ============================================================

/-! Original:
    0: if x < 10 goto 3
    1: goto 2             ← no-op
    2: const a 1
    3: halt

  Expected: pc 1 removed
    0: if x < 10 goto 2
    1: const a 1
    2: halt
-/

def ifgotoNopProg : Prog :=
  { code := #[
      .ifgoto (.cmp .lt (.var "x") (.lit 10)) 3,
      .goto 2,
      .const "a" (.int 1),
      .halt
    ], observable := ["a"] }

def ifgotoNopCert := optimize exTyCtx ifgotoNopProg

#eval! ifgotoNopCert.trans
#eval! checkCertificateExec ifgotoNopCert
#eval! checkCertificateVerboseExec ifgotoNopCert

-- ============================================================
-- § 7. End-to-end: LICM then peephole
-- ============================================================

/-! Run LICM on the classic loop program, then peephole the result.
    This demonstrates the optimizer pipeline.
-/

def e2eProg : Prog :=
  { code := #[
      .const "one" (.int 1),
      .binop "t" .mul "a" "b",
      .ifgoto (.cmp .ne (.var "n") (.lit 0)) 4,
      .halt,
      .binop "s" .add "s" "t",
      .binop "t" .mul "a" "b",
      .binop "n" .sub "n" "one",
      .goto 2
    ], observable := ["s"] }

-- Step 1: LICM removes redundant t := a*b (becomes goto 6)
def e2eLicm := LICMOpt.optimize exTyCtx e2eProg

-- Step 2: Peephole removes the goto 6 left by LICM
def e2ePeep := optimize exTyCtx e2eLicm.trans

#eval! e2eLicm.trans    -- after LICM: has goto 6
#eval! e2ePeep.trans    -- after peephole: goto 6 removed
#eval! checkCertificateExec e2ePeep
#eval! checkCertificateVerboseExec e2ePeep

end PeepholeOptExamples
