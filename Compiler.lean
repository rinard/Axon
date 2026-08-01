-- Copyright (c) 2026 Martin Rinard
import CredibleCompilation.CodeGen

/-- Embedded C runtime stubs for typed-print library calls (printInt, printBool,
    printFloat, printString). Written to a temp file at link time. -/
def runtimeSrc : String := include_str "Compiler/runtime.c"

/-- Materialize `runtimeSrc` to a temp file and return its path. -/
def writeRuntime : IO String := do
  let path := "/tmp/credible_runtime.c"
  IO.FS.writeFile ⟨path⟩ runtimeSrc
  return path

-- ============================================================
-- Instrumented IO-aware pass runners (used by compileFileToFile).
-- Pure variants live in CodeGen.lean and remain unchanged.
-- Marker lines are emitted to stderr for downstream scripts:
--   [PASS]    phase=<p> iter=<i> name=<n> us=<elapsed> size_in=<a> size_out=<b>
--   [CLUSTER] iters=<n> fixedPoint=<true|false>
--   [STAGE]   name=<n> us=<elapsed> ...
--   [TOTAL]   compile_us=<elapsed>
-- ============================================================

private def runPassTimed (tyCtx : TyCtx) (phase : String) (iter : Nat)
    (name : String) (pass : Prog → ECertificate) (p : Prog) : IO Prog := do
  -- Split timing: analyze = build certificate; check = run executable checker.
  -- IORef round-trip between t0/t1 forces evaluation of the cert structure so
  -- the Lean compiler cannot hoist construction work into the check window.
  let t0 ← IO.monoNanosNow
  let cert := { pass p with tyCtx := tyCtx }
  let ref ← IO.mkRef cert
  let cert ← ref.get
  let t1 ← IO.monoNanosNow
  let p' :=
    if cert.orig.code != p.code || cert.orig.observable != p.observable ||
       cert.orig.arrayDecls != p.arrayDecls then p
    else if checkCertificateExec cert then cert.trans
    else p
  let t2 ← IO.monoNanosNow
  let analyze_us := (t1 - t0) / 1000
  let check_us := (t2 - t1) / 1000
  let total_us := (t2 - t0) / 1000
  IO.eprintln s!"[PASS] phase={phase} iter={iter} name={name} us={total_us} \
    analyze_us={analyze_us} check_us={check_us} \
    size_in={p.size} size_out={p'.size}"
  pure p'

private def runPassListTimed (tyCtx : TyCtx) (phase : String) (iter : Nat)
    (passes : List (String × (Prog → ECertificate))) (p : Prog) : IO Prog :=
  passes.foldlM (fun p (name, pass) => runPassTimed tyCtx phase iter name pass p) p

private def runFixpointTimedAux (tyCtx : TyCtx)
    (passes : List (String × (Prog → ECertificate))) :
    Nat → Nat → Prog → IO (Prog × Nat × Bool)
  | 0, iter, p => pure (p, iter, false)
  | n + 1, iter, p => do
    let p' ← runPassListTimed tyCtx "cluster" (iter + 1) passes p
    if p'.code == p.code then pure (p', iter + 1, true)
    else runFixpointTimedAux tyCtx passes n (iter + 1) p'

private def runFixpointTimed (tyCtx : TyCtx)
    (passes : List (String × (Prog → ECertificate))) (maxIter : Nat)
    (p : Prog) : IO Prog := do
  let (p', iters, fixedPoint) ← runFixpointTimedAux tyCtx passes maxIter 0 p
  IO.eprintln s!"[CLUSTER] iters={iters} fixedPoint={fixedPoint}"
  pure p'

/-- Mirror of `applyStandardPipelineFixpoint` with per-pass timing instrumentation. -/
private def runStandardPipelineTimed (tyCtx : TyCtx) (p : Prog) : IO Prog := do
  let p ← runPassListTimed tyCtx "prefix" 0 (prefixPasses tyCtx) p
  let p ← runFixpointTimed tyCtx (licmClusterPasses tyCtx) 5 p
  runPassListTimed tyCtx "suffix" 0 (suffixPasses tyCtx) p

/-- **Structured driver: compile a source file to an assembly text file.**

    Each step's name and order matches the corresponding stage in the verified
    pipeline (see `compilePipeline` in CodeGen.lean and the top-level theorems
    in PipelineCorrectness.lean).  Stages are logged to stderr so the structure
    is observable from the command line.

    Per-pass timings, LICM cluster iteration count, and total compile time are
    emitted as `[PASS]`, `[CLUSTER]`, `[STAGE]`, `[TOTAL]` marker lines on
    stderr for downstream report scripts to parse. -/
def compileFileToFile (inputFile outputFile : String) (noOpt : Bool) : IO UInt32 := do
  let tStart ← IO.monoNanosNow
  IO.eprintln s!"[1/6] Reading source file: {inputFile}"
  let tReadStart ← IO.monoNanosNow
  let src ← IO.FS.readFile ⟨inputFile⟩
  let tReadEnd ← IO.monoNanosNow
  IO.eprintln s!"[STAGE] name=read us={(tReadEnd - tReadStart) / 1000}"
  -- Stage 1: parse (unverified)
  IO.eprintln s!"[2/6] Parsing (unverified)..."
  let tParseStart ← IO.monoNanosNow
  let prog ← match parseProgram src with
    | .ok p => pure p
    | .error e => IO.eprintln s!"  parse error: {e}"; return 1
  let tParseEnd ← IO.monoNanosNow
  IO.eprintln s!"[STAGE] name=parse us={(tParseEnd - tParseStart) / 1000}"
  -- Stage 2: well-formedness
  IO.eprintln s!"[3/6] Well-formedness check..."
  let tWfStart ← IO.monoNanosNow
  if !prog.wellFormed then
    IO.eprintln s!"  program is not well-formed (typecheck/noGoto/noReservedNames failed)"
    return 1
  let tWfEnd ← IO.monoNanosNow
  IO.eprintln s!"[STAGE] name=wellformed us={(tWfEnd - tWfStart) / 1000}"
  let tyCtx := prog.tyCtx
  -- Stage 3: AST → TAC (verified)
  IO.eprintln s!"[4/6] AST → TAC (verified by compileToTAC_*) ..."
  let tTacStart ← IO.monoNanosNow
  let tac := prog.compileToTAC
  let tTacEnd ← IO.monoNanosNow
  IO.eprintln s!"[STAGE] name=compileToTAC us={(tTacEnd - tTacStart) / 1000} tac_size={tac.size}"
  IO.eprintln s!"  TAC size: {tac.size}"
  -- Stage 4: optimizations (verified, certificate-checked, instrumented)
  IO.eprintln s!"[5/6] Applying optimization passes \
    (prefix + LICM cluster fixed-point ≤5 + suffix)..."
  let tOptStart ← IO.monoNanosNow
  let opt ← if noOpt then pure tac else runStandardPipelineTimed tyCtx tac
  let tOptEnd ← IO.monoNanosNow
  IO.eprintln s!"[STAGE] name=optimize us={(tOptEnd - tOptStart) / 1000} opt_size={opt.size}"
  IO.eprintln s!"  Optimized TAC size: {opt.size}"
  -- Stage 5: TAC → verified ASM core (verified)
  IO.eprintln s!"[6/6] TAC → verified ASM (verifiedGenerateAsm) + format & write..."
  let tCgStart ← IO.monoNanosNow
  let r ← match verifiedGenerateAsm tyCtx opt with
    | .ok r => pure r
    | .error e => IO.eprintln s!"  verifiedGenerateAsm error: {e}"; return 1
  let tCgEnd ← IO.monoNanosNow
  IO.eprintln s!"[STAGE] name=verifiedCodegen us={(tCgEnd - tCgStart) / 1000} \
    arm_instrs={r.bodyFlat.size}"
  IO.eprintln s!"  Verified ASM core: {r.bodyFlat.size} ARM instructions"
  -- Stage 6: format (unverified pretty-print + boilerplate) → write
  let tFmtStart ← IO.monoNanosNow
  let asm ← match formatVerifiedAsm r opt with
    | .ok s => pure s
    | .error e => IO.eprintln s!"  format error: {e}"; return 1
  IO.FS.writeFile ⟨outputFile⟩ asm
  let tFmtEnd ← IO.monoNanosNow
  IO.eprintln s!"[STAGE] name=format us={(tFmtEnd - tFmtStart) / 1000}"
  IO.eprintln s!"  Written: {outputFile}"
  let tEnd ← IO.monoNanosNow
  IO.eprintln s!"[TOTAL] compile_us={(tEnd - tStart) / 1000}"
  return 0

def main (args : List String) : IO UInt32 := do
  -- Parse -O0 flag from anywhere in args
  let noOpt := args.contains "-O0"
  let args := args.filter (· != "-O0")
  match args with
  | [inputFile] =>
    let src ← IO.FS.readFile ⟨inputFile⟩
    match compilePipeline src noOpt with
    | .ok asm => IO.print asm; return 0
    | .error e => IO.eprintln s!"error: {e}"; return 1
  | [inputFile, "-S", outputFile] =>
    -- Structured pipeline: compile to assembly text file with stage logging.
    compileFileToFile inputFile outputFile noOpt
  | [inputFile, "-o", outputFile] =>
    let src ← IO.FS.readFile ⟨inputFile⟩
    match compilePipeline src noOpt with
    | .ok asm =>
      let asmFile := outputFile ++ ".s"
      IO.FS.writeFile ⟨asmFile⟩ asm
      let runtimePath ← writeRuntime
      let cc ← IO.Process.output { cmd := "cc", args := #["-o", outputFile, asmFile, runtimePath] }
      if cc.exitCode != 0 then IO.eprintln cc.stderr; return 1
      IO.eprintln s!"compiled: {outputFile}"; return 0
    | .error e => IO.eprintln s!"error: {e}"; return 1
  | [inputFile, "-r"] =>
    let src ← IO.FS.readFile ⟨inputFile⟩
    match compilePipeline src noOpt with
    | .ok asm =>
      let asmFile := "/tmp/while_out.s"
      let binFile := "/tmp/while_out"
      IO.FS.writeFile ⟨asmFile⟩ asm
      let runtimePath ← writeRuntime
      let cc ← IO.Process.output { cmd := "cc", args := #["-o", binFile, asmFile, runtimePath] }
      if cc.exitCode != 0 then IO.eprintln cc.stderr; return 1
      let run ← IO.Process.spawn { cmd := binFile, stdin := .inherit, stdout := .inherit, stderr := .inherit }
      let exit ← run.wait; return exit
    | .error e => IO.eprintln s!"error: {e}"; return 1
  | [inputFile, "-debug"] =>
    let src ← IO.FS.readFile ⟨inputFile⟩
    match parseProgram src with
    | .error e => IO.eprintln s!"parse error: {e}"; return 1
    | .ok prog =>
      if !prog.wellFormed then IO.eprintln "well-formedness check failed"; return 1
      let tac := prog.compileToTAC
      let tyCtx := prog.tyCtx
      IO.println s!"TAC size: {tac.size}"
      IO.println s!"LICM hoistable: {LICMOpt.numHoistable tac}"
      let cert := { RegAllocOpt.optimize tyCtx tac with tyCtx := tyCtx }
      IO.println s!"Trans size: {cert.trans.size}"
      for (name, result) in checkCertificateVerboseExec cert do
        IO.println s!"  {name}: {if result then "ok" else "FAIL"}"
      return 0
  | [inputFile, "-licm"] =>
    let src ← IO.FS.readFile ⟨inputFile⟩
    match parseProgram src with
    | .error e => IO.eprintln s!"parse error: {e}"; return 1
    | .ok prog =>
      if !prog.wellFormed then IO.eprintln "well-formedness check failed"; return 1
      let tac := prog.compileToTAC
      let tyCtx := prog.tyCtx
      let tac ← match applyPass "DCE" tyCtx (DCEOpt.optimize tyCtx) tac with
        | .ok p => pure p | .error e => IO.eprintln e; return 1
      let cert := { LICMOpt.optimize tyCtx tac with tyCtx := tyCtx }
      IO.println s!"=== LICM Certificate ==="
      IO.println s!"orig size: {cert.orig.size}  trans size: {cert.trans.size}"
      let inLoop := LICMOpt.findLoopPCs tac
      let hoistable := LICMOpt.findHoistable tac inLoop
      IO.println s!"hoistable: {hoistable.length}"
      for (pc, loopHead, x, v) in hoistable do
        IO.println s!"  pc={pc} loopHead={loopHead} {x} := {repr v}"
      IO.println s!"\n=== Verbose Check ==="
      for (name, result) in checkCertificateVerboseExec cert do
        IO.println s!"  {name}: {if result then "ok" else "FAIL"}"
      return 0
  | _ =>
    IO.eprintln "Usage: compiler <file.w>               -- print assembly to stdout"
    IO.eprintln "       compiler <file.w> -S <file.s>   -- structured pipeline (logs stages, writes .s)"
    IO.eprintln "       compiler <file.w> -o <out>      -- compile to binary"
    IO.eprintln "       compiler <file.w> -r            -- compile and run"
    return 1
