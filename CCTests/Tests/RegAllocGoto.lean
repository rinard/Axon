-- Copyright (c) 2026 Martin Rinard
import CredibleCompilation.RegAllocOpt
import CredibleCompilation.ExecChecker
import CredibleCompilation.CodeGen
import CredibleCompilation.WhileLang

/-! Regression test: RegAlloc on programs with goto/ifgoto.
    DCE at the end of optimizePipeline eliminates unreachable code
    before RegAlloc, preventing certificate check failures. -/

open SExpr SBool Stmt

def fwdGotoProg : Program where
  decls := [("x", .int), ("y", .int)]
  body :=
    assign "x" (lit 1) ;;
    Stmt.goto "SKIP" ;;
    assign "x" (lit 99) ;;
    label "SKIP" ;;
    assign "y" (var "x")

def backwardGoto : Program where
  decls := [("x", .int)]
  body :=
    assign "x" (lit 0) ;;
    label "LOOP" ;;
    assign "x" (bin .add (var "x") (lit 1)) ;;
    ifgoto (cmp .lt (var "x") (lit 5)) "LOOP"

def irreducible : Program where
  decls := [("x", .int)]
  body :=
    assign "x" (lit 0) ;;
    Stmt.goto "B" ;;
    label "A" ;;
    assign "x" (bin .add (var "x") (lit 1)) ;;
    label "B" ;;
    assign "x" (bin .mul (var "x") (lit 2)) ;;
    ifgoto (cmp .lt (var "x") (lit 10)) "A"

def earlyExit : Program where
  decls := [("i", .int), ("found", .int)]
  body :=
    assign "i" (lit 0) ;;
    assign "found" (lit 0) ;;
    label "SEARCH" ;;
    ifgoto (cmp .eq (var "i") (lit 7)) "FOUND" ;;
    assign "i" (bin .add (var "i") (lit 1)) ;;
    ifgoto (cmp .lt (var "i") (lit 10)) "SEARCH" ;;
    Stmt.goto "END" ;;
    label "FOUND" ;;
    assign "found" (lit 1) ;;
    label "END" ;;
    skip

-- Full pipeline (including RegAlloc) via optimizePipeline
def testPipeline (name : String) (tyCtx : TyCtx) (tac : Prog) : IO Unit := do
  IO.print s!"{name}: "
  match optimizePipeline tyCtx tac >>= optimizePipeline tyCtx with
  | .ok _ => IO.println "PASS"
  | .error e => IO.println s!"FAIL ({e})"

#eval! do
  testPipeline "forward goto" fwdGotoProg.tyCtx fwdGotoProg.compileToTAC
  testPipeline "backward goto" backwardGoto.tyCtx backwardGoto.compileToTAC
  testPipeline "irreducible" irreducible.tyCtx irreducible.compileToTAC
  testPipeline "early exit" earlyExit.tyCtx earlyExit.compileToTAC

-- End-to-end compileToAsm on benchmark goto programs
#eval! do
  let test (file : String) : IO Unit := do
    IO.print s!"{file}: "
    let src ← IO.FS.readFile file
    match compileToAsm src with
    | .ok _ => IO.println "PASS"
    | .error e => IO.println s!"FAIL ({e})"
  test "benchmarks/livermore/k16_monte_carlo.w"
  test "benchmarks/livermore/k17_implicit_cond.w"
