-- Copyright (c) 2026 Martin Rinard
import CredibleCompilation.CodeGen

/-- Certificate audit driver.

    Runs the standard optimization pass list pass-by-pass over a `.w` file using
    `applyPass`, reporting for each pass whether its certificate was ACCEPTED
    (and the size change) or REJECTED (with the failing check names or the
    orig-mismatch reason). On rejection the pass is skipped (program unchanged),
    mirroring the resilient `applyPasses` driver, so downstream passes are still
    audited.

    A REJECTED line where the pass genuinely tried to change the program is a
    silent-optimization-drop: the compiler stays correct but the optimization is
    lost, and it points at a certificate-checker incompleteness or a pass bug.

    Replicate `checkInvariantsPreservedExec`'s inner loop with logging: report the
    first `(pc → pc', atom)` whose post-state value disagrees, on both orig and trans. -/
def diagnoseInvPreserved (cert : ECertificate) : IO Unit := do
  let check (tag : String) (prog : Prog) (inv : Array EInv) : IO Bool := do
    for pc in List.range prog.size do
      match prog[pc]? with
      | some instr =>
        let inv_pre := inv.getD pc ([] : EInv)
        let invMap := FastVarMap.ofList inv_pre
        let fuel := sdFuel inv_pre
        for pc' in instr.successors pc do
          for atom in inv.getD pc' ([] : EInv) do
            if !checkInvAtomFast invMap fuel instr atom then
              let (ss, _) := execSymbolic ([] : SymStore) ([] : SymArrayMem) instr
              let lhs := (ssGet ss atom.1).simplifyDeepFastEarly fuel invMap
              let rhs := (atom.2.substSym ss).simplifyDeepFastEarly fuel invMap
              IO.println s!"    [{tag}] FAIL pc={pc} -> pc'={pc'}  instr={repr instr}"
              IO.println s!"        atom var={atom.1}  atomExpr={repr atom.2}"
              IO.println s!"        pre-inv={repr inv_pre}"
              IO.println s!"        lhs(simplified)={repr lhs}"
              IO.println s!"        rhs(simplified)={repr rhs}"
              return false
      | none => pure ()
    return true
  let _ ← check "orig" cert.orig cert.inv_orig
  let _ ← check "trans" cert.trans cert.inv_trans
  pure ()

/-- Compact view of a relation: only the pairs where the two sides differ. -/
def compactRel (rel : EExprRel) : String :=
  String.intercalate " " (rel.filterMap fun (eo, et) =>
    if eo == et then none else some s!"({repr eo}={repr et})")

/-- Dump the whole transformed program with per-PC pc_orig and (non-identity) rel. -/
def dumpCert (cert : ECertificate) : IO Unit := do
  IO.println "    --- trans program (tpc: instr | pc_orig | rel diffs) ---"
  for tpc in List.range cert.trans.size do
    let instr := cert.trans[tpc]?.getD .halt
    let ic := cert.instrCerts.getD tpc default
    IO.println s!"    {tpc}: {repr instr}  | po={ic.pc_orig} | rel: {compactRel ic.rel}"
    for tc in ic.transitions do
      IO.println s!"         -> labels={tc.origLabels} rel_next: {compactRel tc.rel_next}"

/-- Dump the orig program (compact: pc + instruction) for control-flow inspection. -/
def dumpOrig (cert : ECertificate) : IO Unit := do
  IO.println "    --- orig program (opc: instr | inv_orig) ---"
  for opc in List.range cert.orig.size do
    let inv := cert.inv_orig.getD opc ([] : EInv)
    let invStr := String.intercalate " " (inv.map fun (v, e) => s!"{v}={repr e}")
    IO.println s!"    o{opc}: {repr (cert.orig[opc]?.getD .halt)}  | {invStr}"

/-- Replicate `checkAllTransitionsExec`'s inner loop with logging: for the first
    transformed transition with no satisfying `tc`, dump per-`tc` which sub-check
    (rel / rel_next / origPath / relConsistency) failed. -/
def diagnoseAllTransitions (cert : ECertificate) : IO Unit := do
  for pc_t in List.range cert.trans.size do
    match cert.trans[pc_t]? with
    | some .halt => pure ()
    | some instr =>
      match cert.instrCerts[pc_t]? with
      | some ic =>
        let inv_orig := cert.inv_orig.getD ic.pc_orig ([] : EInv)
        let invMap := FastVarMap.ofList inv_orig
        let fuel := sdFuel inv_orig
        for pc_t' in instr.successors pc_t do
          let ic' := cert.instrCerts.getD pc_t' default
          let branchInfo := match instr with
            | .ifgoto b l =>
              match b.mapVarsRel ic.rel with
              | some origCond => if !(l == pc_t + 1) then some (origCond, pc_t' == l) else none
              | none => none
            | _ => none
          let anyOk := ic.transitions.any fun tc =>
            tc.rel == ic.rel && tc.rel_next == ic'.rel &&
            checkOrigPathFast cert.orig ([] : SymStore) ([] : SymArrayMem) invMap fuel ic.pc_orig tc.origLabels ic'.pc_orig branchInfo &&
            checkRelConsistency cert.orig ic.pc_orig tc.origLabels instr inv_orig tc.rel tc.rel_next
          if !anyOk then
            IO.println s!"    [all_trans] FAIL pc_t={pc_t} -> pc_t'={pc_t'}  instr={repr instr}"
            IO.println s!"        ic.pc_orig={ic.pc_orig}  ic'.pc_orig={ic'.pc_orig}  #transitions={ic.transitions.length}"
            IO.println s!"        ic.rel={repr ic.rel}"
            IO.println s!"        ic'.rel={repr ic'.rel}"
            for tc in ic.transitions do
              let c1 := tc.rel == ic.rel
              let c2 := tc.rel_next == ic'.rel
              let c3 := checkOrigPathFast cert.orig ([] : SymStore) ([] : SymArrayMem) invMap fuel ic.pc_orig tc.origLabels ic'.pc_orig branchInfo
              let c4 := checkRelConsistency cert.orig ic.pc_orig tc.origLabels instr inv_orig tc.rel tc.rel_next
              IO.println s!"        tc origLabels={tc.origLabels} rel?={c1} rel_next?={c2} origPath?={c3} relConsist?={c4}"
            return ()
      | none => IO.println s!"    [all_trans] no instrCert at pc_t={pc_t}"
    | none => pure ()

/-- Audit a single pass: run it, log ACCEPTED / REJECTED (+ optional `-diag`
    diagnostics) / rejected-but-noop, and return the (possibly unchanged)
    program. Mirrors `applyPass`'s resilient semantics: a rejected pass is
    skipped and the program is left as-is. -/
def auditOnePass (tyCtx : TyCtx) (diag : Bool) (name : String)
    (pass : Prog → ECertificate) (p : Prog) : IO Prog := do
  let cert := { pass p with tyCtx := tyCtx }
  let changed := cert.trans.code != p.code
  match applyPass name tyCtx pass p with
  | .ok p' =>
    if p'.code != p.code then
      IO.println s!"  {name}: ACCEPTED  {p.size} -> {p'.size}"
    pure p'
  | .error e =>
    -- Only interesting when the pass actually proposed a change.
    if changed then
      IO.println s!"  {name}: REJECTED (proposed {p.size} -> {cert.trans.size})  {e}"
      if diag then
        diagnoseInvPreserved cert
        diagnoseAllTransitions cert
        if name == "Peephole" || name == "FMAFusion" || name == "RegAlloc" then dumpOrig cert
    else
      IO.println s!"  {name}: rejected-but-noop  {e}"
    pure p

/-- Audit a list of passes once, threading the program through. Logging mirror
    of `applyPasses`. -/
def auditPassList (tyCtx : TyCtx) (diag : Bool)
    (passes : List (String × (Prog → ECertificate))) (p0 : Prog) : IO Prog := do
  let mut p := p0
  for (name, pass) in passes do
    p ← auditOnePass tyCtx diag name pass p
  return p

/-- Audit `passes` repeatedly, stopping when the program code is unchanged after
    a full iteration (fixed point) or `maxIter` iterations have run. Logging
    mirror of `applyPassesUntilFixedOrN`. -/
def auditClusterFixpoint (tyCtx : TyCtx) (diag : Bool)
    (passes : List (String × (Prog → ECertificate))) (maxIter : Nat)
    (p0 : Prog) : IO Prog := do
  let mut p := p0
  let mut done := false
  for iter in [0:maxIter] do
    if !done then
      IO.println s!"  -- LICM cluster iteration {iter + 1}/{maxIter} --"
      let p' ← auditPassList tyCtx diag passes p
      if p'.code == p.code then
        IO.println s!"  -- cluster fixed point reached after {iter + 1} iteration(s) --"
        done := true
      p := p'
  return p

/-- Audit the production pipeline (`applyStandardPipelineFixpoint`) pass-by-pass:
    prologue (`prefixPasses`) once, then the LICM cluster to a fixed point
    (≤ 5 iterations), then epilogue (`suffixPasses`) once. This mirrors the
    shipped driver exactly, so every certificate audited is one production
    actually checks, in the same order — including a 5th cluster iteration that
    the flat unrolled `standardPasses` (4 unrolls) would never reach. -/
def auditPasses (tyCtx : TyCtx) (diag : Bool) (p0 : Prog) : IO Prog := do
  IO.println "  == prologue (prefixPasses) =="
  let p ← auditPassList tyCtx diag (prefixPasses tyCtx) p0
  IO.println "  == loop (licmClusterPasses, fixed point ≤ 5) =="
  let p ← auditClusterFixpoint tyCtx diag (licmClusterPasses tyCtx) 5 p
  IO.println "  == epilogue (suffixPasses) =="
  auditPassList tyCtx diag (suffixPasses tyCtx) p

def main (args : List String) : IO UInt32 := do
  let diag := args.contains "-diag"
  let licmdump := args.contains "-licmdump"
  let args := (args.filter (· != "-diag")).filter (· != "-licmdump")
  if licmdump then
    match args with
    | [inputFile] =>
      let src ← IO.FS.readFile ⟨inputFile⟩
      match parseProgram src with
      | .error e => IO.eprintln s!"parse error: {e}"; return 1
      | .ok prog =>
        let tyCtx := prog.tyCtx
        let tac := prog.compileToTAC
        let dce := match applyPass "DCE" tyCtx (DCEOpt.optimize tyCtx) tac with
          | .ok p => p | .error _ => tac
        let cert := { LICMOpt.optimize tyCtx dce with tyCtx := tyCtx }
        IO.println s!"=== LICM cert dump: orig {cert.orig.size} trans {cert.trans.size} ==="
        let av := _root_.collectAllVars cert.orig cert.trans
        IO.println s!"allVars ({av.length}, uniq {av.eraseDups.length}): {av}"
        IO.println "--- orig program + inv_orig ---"
        for opc in List.range cert.orig.size do
          let inv := cert.inv_orig.getD opc ([] : EInv)
          let invStr := String.intercalate " " (inv.map fun (v, e) => s!"({v}={repr e})")
          IO.println s!"  o{opc}: {repr (cert.orig[opc]?.getD .halt)}  inv: {invStr}"
        dumpCert cert
        IO.println "=== failing transitions ==="
        diagnoseAllTransitions cert
        return 0
    | _ => IO.eprintln "usage: certaudit -licmdump <file.w>"; return 1
  match args with
  | [inputFile] =>
    let src ← IO.FS.readFile ⟨inputFile⟩
    match parseProgram src with
    | .error e => IO.eprintln s!"parse error: {e}"; return 1
    | .ok prog =>
      if !prog.wellFormed then IO.eprintln "well-formedness check failed"; return 1
      let tyCtx := prog.tyCtx
      let tac := prog.compileToTAC
      IO.println s!"=== Cert audit: {inputFile}  (TAC size {tac.size}) ==="
      let p ← auditPasses tyCtx diag tac
      IO.println s!"final size: {p.size}"
      -- Also confirm verified codegen still succeeds on the result.
      match verifiedGenerateAsm tyCtx p with
      | .ok r => IO.println s!"codegen OK: {r.bodyFlat.size} ARM instrs"
      | .error e => IO.println s!"codegen FAILED: {e}"
      return 0
  | _ => IO.eprintln "usage: certaudit <file.w>"; return 1
