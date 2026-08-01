-- Copyright (c) 2026 Martin Rinard
import CredibleCompilation.ConstPropOpt

/-!
# Constant Propagation Optimizer — Examples

Tests the optimizer on several programs and verifies that the generated
certificates pass `checkCertificateExec`.
-/

open ConstPropOpt

namespace ConstPropOptExamples

/-- All example programs here are integer-typed; `tyCtx` used to be a field of `Prog`
    and is now an explicit argument to `optimize`. -/
def cpTyCtx : TyCtx := fun _ => .int

-- ============================================================
-- § 1. Simple constant chain
-- ============================================================

/-! Original:
    0: x := 7
    1: y := x       ← copy, x is known 7
    2: z := y       ← copy, y is known 7
    3: halt

  Expected transformation:
    0: x := 7
    1: y := 7       ← const propagated
    2: z := 7       ← const propagated
    3: halt
-/

def simpleProg : Prog :=
  { code := #[.const "x" (.int 7), .copy "y" "x", .copy "z" "y", .halt],
    observable := ["z"] }

def simpleCert := optimize cpTyCtx simpleProg

#eval! simpleCert.trans
#eval! checkCertificateExec simpleCert
#eval! checkCertificateVerboseExec simpleCert

-- ============================================================
-- § 2. Constant folding through binop
-- ============================================================

/-! Original:
    0: a := 5
    1: b := 3
    2: c := a + b   ← both operands known: 5 + 3 = 8
    3: d := c * b   ← both known: 8 * 3 = 24
    4: halt
-/

def foldProg : Prog :=
  { code := #[.const "a" (.int 5), .const "b" (.int 3),
              .binop "c" .add "a" "b", .binop "d" .mul "c" "b", .halt],
    observable := ["d"] }

def foldCert := optimize cpTyCtx foldProg

#eval! foldCert.trans
#eval! checkCertificateExec foldCert
#eval! checkCertificateVerboseExec foldCert

-- ============================================================
-- § 3. Partial constants (not all operands known)
-- ============================================================

/-! Original:
    0: a := 10
    1: b := a + x   ← x unknown, can't fold
    2: c := a       ← copy, a known → const 10
    3: halt

  Expected: pc 1 unchanged, pc 2 becomes const "c" 10
-/

def partialProg : Prog :=
  { code := #[.const "a" (.int 10), .binop "b" .add "a" "x", .copy "c" "a", .halt],
    observable := ["b", "c"] }

def partialCert := optimize cpTyCtx partialProg

#eval! partialCert.trans
#eval! checkCertificateExec partialCert
#eval! checkCertificateVerboseExec partialCert

-- ============================================================
-- § 4. Branch elimination (always-taken)
-- ============================================================

/-! Original:
    0: x := 1
    1: if x ≠ 0 goto 3    ← always true (x = 1)
    2: halt                ← dead code
    3: y := 5
    4: halt

  Expected: pc 1 becomes goto 3
-/

def branchProg : Prog :=
  { code := #[.const "x" (.int 1), .ifgoto (.cmp .ne (.var "x") (.lit 0)) 3, .halt,
              .const "y" (.int 5), .halt],
    observable := ["y"] }

def branchCert := optimize cpTyCtx branchProg

#eval! branchCert.trans
#eval! checkCertificateExec branchCert
#eval! checkCertificateVerboseExec branchCert

-- ============================================================
-- § 5. Branch elimination (always-fallthrough)
-- ============================================================

/-! Original:
    0: x := 0
    1: if x ≠ 0 goto 3    ← always false (x = 0)
    2: y := 42
    3: halt

  Expected: pc 1 becomes goto 2
-/

def fallProg : Prog :=
  { code := #[.const "x" (.int 0), .ifgoto (.cmp .ne (.var "x") (.lit 0)) 3,
              .const "y" (.int 42), .halt],
    observable := ["y"] }

def fallCert := optimize cpTyCtx fallProg

#eval! fallCert.trans
#eval! checkCertificateExec fallCert
#eval! checkCertificateVerboseExec fallCert

-- ============================================================
-- § 6. Loop (constants preserved through loop)
-- ============================================================

/-! Original:
    0: one := 1
    1: n := 10
    2: i := 0
    3: if i < n goto 5     ← can't resolve (i changes)
    4: halt
    5: i := i + one
    6: goto 3

  Expected: no data changes (loop variable `i` isn't constant at
  the loop header), but the certificate should still verify.
-/

def loopProg : Prog :=
  { code := #[.const "one" (.int 1), .const "n" (.int 10), .const "i" (.int 0),
              .ifgoto (.cmp .lt (.var "i") (.var "n")) 5, .halt,
              .binop "i" .add "i" "one", .goto 3],
    observable := ["i"] }

def loopCert := optimize cpTyCtx loopProg

#eval! loopCert.trans
#eval! checkCertificateExec loopCert
#eval! checkCertificateVerboseExec loopCert

-- ============================================================
-- § 7. Constant propagation + folding in straight-line code
-- ============================================================

/-! Original:
    0: x := 100
    1: y := x        ← propagate to 100
    2: z := y        ← propagate to 100
    3: w := x + z    ← fold: 100 + 100 = 200
    4: v := w - y    ← fold: 200 - 100 = 100
    5: halt
-/

def chainProg : Prog :=
  { code := #[.const "x" (.int 100), .copy "y" "x", .copy "z" "y",
              .binop "w" .add "x" "z", .binop "v" .sub "w" "y", .halt],
    observable := ["v", "w"] }

def chainCert := optimize cpTyCtx chainProg

#eval! chainCert.trans
#eval! checkCertificateExec chainCert
#eval! checkCertificateVerboseExec chainCert

end ConstPropOptExamples
