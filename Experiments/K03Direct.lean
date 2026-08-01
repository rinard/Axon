-- Copyright (c) 2026 Martin Rinard
import CredibleCompilation.CodeGen

/-!
# K03 inner-product — direct AST → verified pipeline (no parser).

Translates the canonical Livermore Loops Kernel 3 (inner product) directly
into a `WhileLang.Program` value, bypassing the unverified `parseProgram`
front-end, then runs it through the verified core pipeline
(`compileProgramAst`) and final formatting (`formatVerifiedAsm`)
to produce ARM64 assembly text. The `main` writes the .s, links it
against the runtime, and runs the binary.

Source-of-truth references (NOT the derived per-kernel files):
  * Kernel body  — `/tmp/livermore_orig/kernels_only.f` lines 36-45
                   (verbatim from netlib `lloops.f` lines 1999-2009).
  * SIGNEL init  — `/tmp/livermore_orig/lloops.f` lines 5013-5060.

The kernel:
    Q = 0
    DO 3 k = 1, n
      Q = Q + Z(k) * X(k)

The SIGNEL recurrence (with SCALED = 0.1, BIASED = 0.0):
    FUZZ = 1.234500d-3
    BUZZ = 1.0  + FUZZ
    FIZZ = 1.1  * FUZZ
    DO 1 k = 1, n
      BUZZ = (1.0 - FUZZ) * BUZZ + FUZZ
      FUZZ = -FUZZ
      V(k) = (BUZZ - FIZZ) * 0.1

For this experiment N = 1001 (canonical sizing) and NREPS = 2 (small for
fast testing — Q is invariant in `rep` so the value is independent of NREPS).
-/

private def N      : Int := 1001
private def NREPS  : Int := 2
private def ASIZE  : Nat := 1002  -- arrays use 1-based indexing, so size N+1

-- ---------- Expression helpers (concise constructors) ----------

private abbrev fl  (f : Float)         : SExpr := .flit f
private abbrev il  (n : Int)           : SExpr := .lit n
private abbrev v   (x : String)        : SExpr := .var x
private abbrev fadd (a b : SExpr)      : SExpr := .fbin .fadd a b
private abbrev fsub (a b : SExpr)      : SExpr := .fbin .fsub a b
private abbrev fmul (a b : SExpr)      : SExpr := .fbin .fmul a b
private abbrev iadd (a b : SExpr)      : SExpr := .bin  .add  a b
private abbrev fread (arr : String) (i : SExpr) : SExpr := .farrRead arr i

-- ---------- The K03 program AST (built directly, no parser) ----------

/-- One pass of SIGNEL filling array `arr` with N values. -/
private def signelFill (arr : String) : Stmt :=
  -- FUZZ = 1.234500e-3
  .fassign "fuzz" (fl 1.234500e-3) ;;
  -- BUZZ = 1.0 + FUZZ
  .fassign "buzz" (fadd (fl 1.0) (v "fuzz")) ;;
  -- FIZZ = 1.1 * FUZZ
  .fassign "fizz" (fmul (fl 1.1) (v "fuzz")) ;;
  -- k = 1
  .assign "k" (il 1) ;;
  -- DO k = 1, n
  .loop (.cmp .le (v "k") (il N))
    ( .fassign "buzz" (fadd (fmul (fsub (fl 1.0) (v "fuzz")) (v "buzz")) (v "fuzz")) ;;
      .fassign "fuzz" (fsub (fl 0.0) (v "fuzz")) ;;     -- canonical -FUZZ
      .farrWrite arr (v "k") (fmul (fsub (v "buzz") (v "fizz")) (fl 0.1)) ;;
      .assign "k" (iadd (v "k") (il 1)) )

/-- The kernel body: q += z[k] * x[k] for k = 1..N. -/
private def kernelBody : Stmt :=
  .fassign "q" (fl 0.0) ;;
  .assign "k" (il 1) ;;
  .loop (.cmp .le (v "k") (il N))
    ( .fassign "q" (fadd (v "q") (fmul (fread "z" (v "k")) (fread "x" (v "k")))) ;;
      .assign "k" (iadd (v "k") (il 1)) )

/-- The full K03 program: SIGNEL(z) ; SIGNEL(x) ; rep loop ; print Q. -/
def k03DotProgram : Program where
  decls :=
    [ ("k",    .int)
    , ("rep",  .int)
    , ("q",    .float)
    , ("fuzz", .float)
    , ("buzz", .float)
    , ("fizz", .float)
    ]
  arrayDecls :=
    [ ("z", ASIZE, .float)
    , ("x", ASIZE, .float)
    ]
  body :=
    signelFill "z" ;;
    signelFill "x" ;;
    .assign "rep" (il 1) ;;
    .loop (.cmp .le (v "rep") (il NREPS))
      ( kernelBody ;;
        .assign "rep" (iadd (v "rep") (il 1)) ) ;;
    .printFloat (v "q") ;;
    .printString "\n"

-- ---------- Compile + link + run driver ----------

/-- Mirror of `Compiler.compileToAsmWith`, but takes a `Program` directly
    instead of going through `parseProgram`. -/
private def compileProgToAsm (prog : Program) (noOpt : Bool) : Except String String := do
  let r ← compileProgramAst prog noOpt
  let opt :=
    if noOpt then prog.compileToTAC
    else applyStandardPipelineFixpoint prog.tyCtx prog.compileToTAC
  formatVerifiedAsm r opt

/-- Inline materialization of the C runtime so we don't depend on `Compiler.lean`
    (which has its own `main`). Mirrors `Compiler.writeRuntime`. -/
private def writeRuntimeLocal : IO String := do
  let path := "/tmp/credible_runtime.c"
  let src ← IO.FS.readFile ⟨"Compiler/runtime.c"⟩
  IO.FS.writeFile ⟨path⟩ src
  return path

def main (args : List String) : IO UInt32 := do
  let asmPath := "/tmp/k03_direct.s"
  let binPath := "/tmp/k03_direct"
  -- Sanity: program must be well-formed (the verified pipeline checks it too,
  -- but printing this gives a clear error if AST is malformed).
  if !k03DotProgram.wellFormed then
    IO.eprintln "ERROR: k03DotProgram fails wellFormed check (typeCheck/noGoto/noReservedNames)"
    return 1
  IO.eprintln s!"K03 direct-AST: program OK, decls={k03DotProgram.decls.length}, \
    arrays={k03DotProgram.arrayDecls.length}"
  -- Run the verified pipeline starting from the AST (no parser).
  match compileProgToAsm k03DotProgram (noOpt := false) with
  | .error e =>
    IO.eprintln s!"compile error: {e}"
    return 1
  | .ok asm =>
    IO.FS.writeFile ⟨asmPath⟩ asm
    IO.eprintln s!"wrote {asmPath} ({asm.length} bytes)"
    -- Materialize the C runtime (printFloat, printString, etc.)
    let runtimePath ← writeRuntimeLocal
    -- Link
    let cc ← IO.Process.output { cmd := "cc", args := #["-o", binPath, asmPath, runtimePath] }
    if cc.exitCode != 0 then
      IO.eprintln s!"link failed:\n{cc.stderr}"
      return 1
    IO.eprintln s!"linked: {binPath}"
    if args.contains "--no-run" then return 0
    -- Run and print to stdout
    let run ← IO.Process.output { cmd := binPath, args := #[] }
    IO.print run.stdout
    if run.exitCode != 0 then
      IO.eprintln s!"binary exited with {run.exitCode}"
      IO.eprintln run.stderr
    return run.exitCode
