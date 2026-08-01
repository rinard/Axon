-- Copyright (c) 2026 Martin Rinard
import CredibleCompilation.WhileLang

/-!
# Typed Program Examples — Static Type Checking

Demonstrates the `Program` type with explicit variable declarations and
static type checking. Programs that pass `typeCheck` are guaranteed to
compile to well-typed TAC, which by the progress theorem means no type
errors can occur at runtime.
-/

open SExpr SBool Stmt Program

-- ============================================================
-- § 1. Typed Sum 1..n
-- ============================================================

namespace TypedSum

def prog : Program where
  decls := [("n", .int), ("s", .int), ("i", .int)]
  body :=
    assign "s" (lit 0) ;;
    assign "i" (lit 1) ;;
    loop (cmp .le (var "i") (var "n"))
      (assign "s" (bin .add (var "s") (var "i")) ;;
       assign "i" (bin .add (var "i") (lit 1)))

-- Type check passes — all variables declared with correct types
#eval prog.typeCheck           -- true
#eval prog.verifyWellTyped     -- true (compiled TAC is well-typed)

-- Compile and run
def tac : Prog := prog.compileToTAC
#eval tac.code.toList
#eval do let (σ, _) ← prog.interp 1000 (inputs := [("n", .int 10)]); return σ "s"

end TypedSum

-- ============================================================
-- § 2. Typed Factorial
-- ============================================================

namespace TypedFactorial

def prog : Program where
  decls := [("n", .int), ("r", .int)]
  body :=
    assign "r" (lit 1) ;;
    loop (cmp .ne (var "n") (lit 0))
      (assign "r" (bin .mul (var "r") (var "n")) ;;
       assign "n" (bin .sub (var "n") (lit 1)))

#eval prog.typeCheck           -- true
#eval prog.verifyWellTyped     -- true
#eval do let (σ, _) ← prog.interp 1000 (inputs := [("n", .int 5)]); return σ "r"

end TypedFactorial

-- ============================================================
-- § 3. Typed boolean example
-- ============================================================

namespace TypedBoolFlag

/-- Linear search: `found := false; i := 0; while (!found && i < n) { ... }` -/
def prog : Program where
  decls := [("found", .bool), ("i", .int), ("n", .int), ("target", .int)]
  body :=
    bassign "found" (.bvar "found") ;;  -- init from default (false)
    assign "i" (lit 0) ;;
    loop (.and (.not (.bvar "found")) (cmp .lt (var "i") (var "n")))
      (ite (cmp .eq (var "i") (var "target"))
        (bassign "found" (.cmp .eq (var "i") (var "target")))
        skip ;;
       assign "i" (bin .add (var "i") (lit 1)))

#eval prog.typeCheck           -- true
#eval prog.verifyWellTyped     -- true
#eval do let (σ, _) ← prog.interp 1000 (inputs := [("n", .int 10), ("target", .int 7)]); return (σ "found", σ "i")

end TypedBoolFlag

-- ============================================================
-- § 4. Type error detection
-- ============================================================

namespace TypeErrors

/-- Using an int variable as a bool — should fail type check. -/
def badProg1 : Program where
  decls := [("x", .int)]
  body := bassign "x" (.cmp .eq (lit 1) (lit 2))  -- x is int, but bassign needs bool

#eval badProg1.typeCheck  -- false

/-- Using an undeclared variable — should fail type check. -/
def badProg2 : Program where
  decls := [("x", .int)]
  body := assign "x" (bin .add (var "x") (var "y"))  -- y not declared

#eval badProg2.typeCheck  -- false

/-- Reading a bool variable in arithmetic — should fail type check. -/
def badProg3 : Program where
  decls := [("x", .int), ("b", .bool)]
  body := assign "x" (var "b")  -- b is bool, but var needs int

#eval badProg3.typeCheck  -- false

/-- Duplicate declarations — should fail type check. -/
def badProg4 : Program where
  decls := [("x", .int), ("x", .bool)]
  body := skip

#eval badProg4.typeCheck  -- false

/-- Well-typed program for comparison. -/
def goodProg : Program where
  decls := [("x", .int), ("b", .bool)]
  body :=
    assign "x" (bin .add (lit 1) (lit 2)) ;;
    bassign "b" (.cmp .lt (var "x") (lit 10))

#eval goodProg.typeCheck        -- true
#eval goodProg.verifyWellTyped  -- true

end TypeErrors
