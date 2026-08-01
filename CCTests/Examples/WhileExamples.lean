-- Copyright (c) 2026 Martin Rinard
import CredibleCompilation.WhileLang
import CredibleCompilation.ExecChecker
import CredibleCompilation.ConstPropOpt
import CredibleCompilation.CodeGen

/-!
# While Language — End-to-end Examples

Demonstrates the full pipeline: source program → compile to TAC →
optimize → certificate check.
-/

open SExpr SBool Stmt

/-- Compile a bare Stmt to a Prog (for test examples only).
    The verified path is `Program.compileToTAC`; this is a convenience wrapper. -/
private def compileStmtToProg (s : Stmt) : Prog :=
  let labels := collectLabels s 0
  let (code, _) := compileStmt s 0 0 labels
  .ofCode (code ++ [TAC.halt]).toArray

-- ============================================================
-- § 1. Sum 1..n
-- ============================================================

namespace WhileSum

/-- `s := 0; i := 1; while (i <= n) { s := s + i; i := i + 1 }` -/
def prog : Stmt :=
  assign "s" (lit 0) ;;
  assign "i" (lit 1) ;;
  loop (cmp .le (var "i") (var "n"))
    (assign "s" (bin .add (var "s") (var "i")) ;;
     assign "i" (bin .add (var "i") (lit 1)))

def tac : Prog := { compileStmtToProg prog with observable := ["s"] }

-- Compile and verify
#eval tac.code.toList
#eval do let (σ, _) ← Stmt.interp 1000 (fun v => if v == "n" then .int 10 else .int 0) ArrayMem.init ([] : List (ArrayName × Nat × VarTy)) prog; return σ "s"

-- Optimize with constant propagation, then check
def cert := ConstPropOpt.optimize (fun _ => .int) tac
#eval checkCertificateExec cert
#eval checkCertificateVerboseExec cert

end WhileSum

-- ============================================================
-- § 2. Factorial
-- ============================================================

namespace WhileFactorial

/-- `r := 1; while (n != 0) { r := r * n; n := n - 1 }` -/
def prog : Stmt :=
  assign "r" (lit 1) ;;
  loop (cmp .ne (var "n") (lit 0))
    (assign "r" (bin .mul (var "r") (var "n")) ;;
     assign "n" (bin .sub (var "n") (lit 1)))

def tac : Prog := { compileStmtToProg prog with observable := ["r"] }

#eval tac.code.toList
#eval do let (σ, _) ← Stmt.interp 1000 (fun v => if v == "n" then .int 5 else .int 0) ArrayMem.init ([] : List (ArrayName × Nat × VarTy)) prog; return σ "r"

def cert := ConstPropOpt.optimize (fun _ => .int) tac
#eval checkCertificateExec cert
#eval checkCertificateVerboseExec cert

end WhileFactorial

-- ============================================================
-- § 3. Max of two values
-- ============================================================

namespace WhileMax

/-- `if (a < b) then m := b else m := a` -/
def prog : Stmt :=
  ite (cmp .lt (var "a") (var "b"))
    (assign "m" (var "b"))
    (assign "m" (var "a"))

def tac : Prog := { compileStmtToProg prog with observable := ["m"] }

#eval tac.code.toList
#eval do let (σ, _) ← Stmt.interp 100 (fun v => if v == "a" then .int 3 else if v == "b" then .int 7 else .int 0) ArrayMem.init ([] : List (ArrayName × Nat × VarTy)) prog; return σ "m"

def cert := ConstPropOpt.optimize (fun _ => .int) tac
#eval checkCertificateExec cert
#eval checkCertificateVerboseExec cert

end WhileMax

-- ============================================================
-- § 4. Constant expression (optimization target)
-- ============================================================

namespace WhileConstExpr

/-- `x := 2 + 3; y := x * 4` — all constant, should fold completely. -/
def prog : Stmt :=
  assign "x" (bin .add (lit 2) (lit 3)) ;;
  assign "y" (bin .mul (var "x") (lit 4))

def tac : Prog := { compileStmtToProg prog with observable := ["y"] }

#eval tac.code.toList
#eval do let (σ, _) ← Stmt.interp 100 (fun _ => .int 0) ArrayMem.init ([] : List (ArrayName × Nat × VarTy)) prog; return σ "y"

-- Constant propagation should fold this aggressively
def cert := ConstPropOpt.optimize (fun _ => .int) tac
#eval cert.trans.code.toList
#eval checkCertificateExec cert
#eval checkCertificateVerboseExec cert

end WhileConstExpr

-- ============================================================
-- § 5. Common subexpression (CSE target)
-- ============================================================

namespace WhileAbsVal

/-- `if (x < 0) then r := 0 - x else r := x` — absolute value. -/
def prog : Stmt :=
  ite (cmp .lt (var "x") (lit 0))
    (assign "r" (bin .sub (lit 0) (var "x")))
    (assign "r" (var "x"))

def tac : Prog := { compileStmtToProg prog with observable := ["r"] }

#eval tac.code.toList

def cert := ConstPropOpt.optimize (fun _ => .int) tac
#eval checkCertificateExec cert
#eval checkCertificateVerboseExec cert

end WhileAbsVal

-- ============================================================
-- § 6. Nested loop (stress test)
-- ============================================================

namespace WhileNested

/-- `s := 0; i := 0;
    while (i < n) {
      j := 0;
      while (j < n) { s := s + 1; j := j + 1 };
      i := i + 1
    }` -/
def prog : Stmt :=
  assign "s" (lit 0) ;;
  assign "i" (lit 0) ;;
  loop (cmp .lt (var "i") (var "n"))
    (assign "j" (lit 0) ;;
     loop (cmp .lt (var "j") (var "n"))
       (assign "s" (bin .add (var "s") (lit 1)) ;;
        assign "j" (bin .add (var "j") (lit 1))) ;;
     assign "i" (bin .add (var "i") (lit 1)))

def tac : Prog := { compileStmtToProg prog with observable := ["s"] }

#eval tac.code.toList
#eval do let (σ, _) ← Stmt.interp 10000 (fun v => if v == "n" then .int 3 else .int 0) ArrayMem.init ([] : List (ArrayName × Nat × VarTy)) prog; return σ "s"

def cert := ConstPropOpt.optimize (fun _ => .int) tac
#eval checkCertificateExec cert
#eval checkCertificateVerboseExec cert

end WhileNested

-- ============================================================
-- § 7. Division example (stuck on div-by-zero)
-- ============================================================

namespace WhileDiv

/-- `q := a / b` — gets stuck if b = 0. -/
def prog : Stmt :=
  assign "q" (bin .div (var "a") (var "b"))

def tac : Prog := { compileStmtToProg prog with observable := ["q"] }

#eval tac.code.toList

def cert := ConstPropOpt.optimize (fun _ => .int) tac
#eval checkCertificateExec cert

end WhileDiv

-- ============================================================
-- § 8. Boolean literal assignment
-- ============================================================

namespace WhileBoolLit

/-- `x := 10; done := false; while (!done) { x := x - 1; if (x == 0) then done := true else skip }` -/
def prog : Program where
  decls := [("x", .int), ("done", .bool)]
  body :=
    assign "x" (lit 10) ;;
    bassign "done" (.lit false) ;;
    loop (.not (.bvar "done"))
      (assign "x" (bin .sub (var "x") (lit 1)) ;;
       ite (cmp .eq (var "x") (lit 0))
         (bassign "done" (.lit true))
         skip)

#eval prog.typeCheck
def tac : Prog := prog.compileToTAC

#eval tac.code.toList
#eval do let (σ, _) ← prog.interp 1000; return σ "x"

def cert := ConstPropOpt.optimize prog.tyCtx tac
#eval checkCertificateExec cert
#eval checkCertificateVerboseExec cert

-- Generate assembly and run natively
#eval! generateAsm prog.tyCtx tac
#eval! do
  match generateAsm prog.tyCtx tac with
  | .ok asm => let _ ← assembleAndRun asm "/tmp/boollit.s" "/tmp/boollit.s"; return ()
  | .error err => IO.eprintln s!"codegen failed: {err}"

end WhileBoolLit

-- ============================================================
-- § 9. Array sum
-- ============================================================

namespace WhileArraySum

/-- `s := 0; i := 0; while (i < n) { s := s + a[i]; i := i + 1 }` -/
def prog : Stmt :=
  assign "s" (lit 0) ;;
  assign "i" (lit 0) ;;
  loop (cmp .lt (var "i") (var "n"))
    (assign "s" (bin .add (var "s") (arrRead "a" (var "i"))) ;;
     assign "i" (bin .add (var "i") (lit 1)))

def tac : Prog := { compileStmtToProg prog with observable := ["s"] }

#eval tac.code.toList

-- Sum a[0..2] = 10 + 20 + 30 = 60
#eval do
  let am := ArrayMem.init |>.write "a" 0 10 |>.write "a" 1 20 |>.write "a" 2 30
  let decls : List (ArrayName × Nat × VarTy) := [("a", 1024, .int)]
  let (σ, _) ← Stmt.interp 1000 (fun v => if v == "n" then .int 3 else .int 0) am decls prog
  return σ "s"

def cert := ConstPropOpt.optimize (fun _ => .int) tac
#eval checkCertificateExec cert
#eval checkCertificateVerboseExec cert

end WhileArraySum

-- ============================================================
-- § 10. Array init (write)
-- ============================================================

namespace WhileArrayInit

/-- `i := 0; while (i < n) { a[i] := i * i; i := i + 1 }` -/
def prog : Stmt :=
  assign "i" (lit 0) ;;
  loop (cmp .lt (var "i") (var "n"))
    (Stmt.arrWrite "a" (var "i") (bin .mul (var "i") (var "i")) ;;
     assign "i" (bin .add (var "i") (lit 1)))

def tac : Prog := { compileStmtToProg prog with observable := ["i"] }

#eval tac.code.toList

-- After init: a[0]=0, a[1]=1, a[2]=4
#eval do
  let decls : List (ArrayName × Nat × VarTy) := [("a", 1024, .int)]
  let (_, am) ← Stmt.interp 1000 (fun v => if v == "n" then .int 3 else .int 0) ArrayMem.init decls prog
  return (am.read "a" 0, am.read "a" 1, am.read "a" 2)

def cert := ConstPropOpt.optimize (fun _ => .int) tac
#eval checkCertificateExec cert
#eval checkCertificateVerboseExec cert

end WhileArrayInit
