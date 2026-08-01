-- Copyright (c) 2026 Martin Rinard
import CredibleCompilation.CodeGen

/-! # Certificate-mutation soundness tester

    Tests the TRUSTED certificate checker's *soundness* (does it REJECT wrong
    transforms?), complementing the completeness work (does it ACCEPT correct
    ones?). Method: take a VALID certificate `(orig, trans, rel...)` that the
    checker accepts, then corrupt the TRANSFORMED program `trans` in a
    behaviour-changing way. By the checker's soundness theorem, accepting
    `(orig, trans', rel)` would assert `orig ⊑ trans'`; if `trans'` actually
    computes something different, an ACCEPT is a soundness hole.

    For every mutation we report ACCEPT/REJECT. A correct checker rejects every
    behaviour-changing mutation; the only legitimate ACCEPTs are mutations of
    dead/observably-irrelevant instructions. Accepted mutants are emitted as ARM
    assembly (`verifiedGenerateAsm` on the mutated trans) so a shell driver can
    run them and confirm whether the output actually diverges from the correct
    program — a divergence under ACCEPT is a real hole. -/

namespace CertMutate

/-- Cycle a binary op to a different one (changes the computed value). -/
def nextOp : BinOp → BinOp
  | .add => .sub | .sub => .mul | .mul => .add
  | .band => .bor | .bor => .bxor | .bxor => .band
  | .shl => .shr | .shr => .shl
  | .div => .mod | .mod => .div

/-- Behaviour-changing mutations of a single TAC instruction. Returns `none`
    when the mutation does not apply to this instruction. -/
def mutateInstr (kind : String) : TAC → Option TAC
  | .const x (.int v) => if kind == "const" then some (.const x (.int (v + 1))) else none
  | .binop x op a b   => if kind == "binop" then some (.binop x (nextOp op) a b)
                         else if kind == "swap" && a != b then some (.binop x op b a) else none
  | .goto l           => if kind == "goto" then some (.goto (l + 1)) else none
  | _ => none

/-- Replace instruction `i` in the transformed program. -/
def mutateCert (cert : ECertificate) (kind : String) (i : Nat) : Option ECertificate :=
  match cert.trans.code[i]? with
  | some instr =>
    match mutateInstr kind instr with
    | some instr' =>
      let code' := cert.trans.code.set! i instr'
      some { cert with trans := { cert.trans with code := code' } }
    | none => none
  | none => none

/-- Build a rich, accepted baseline certificate for `tac`, trying passes in order.
    Returns the first whose cert the checker accepts AND that changed the code. -/
def baselineCert (tyCtx : TyCtx) (tac : Prog) : Option (String × ECertificate) :=
  let cands : List (String × ECertificate) :=
    [ ("RegAlloc", { RegAllocOpt.optimize tyCtx tac with tyCtx := tyCtx }),
      ("CSE",      { CSEOpt.optimize tyCtx tac with tyCtx := tyCtx }),
      ("ConstProp",{ ConstPropOpt.optimize tyCtx tac with tyCtx := tyCtx }),
      ("LICM",     { LICMOpt.optimize tyCtx tac with tyCtx := tyCtx }) ]
  cands.find? fun (_, c) => checkCertificateExec c && c.trans.code != c.orig.code

def main (args : List String) : IO UInt32 := do
  let dbg := args.contains "-dbg"
  match args.filter (· != "-dbg") with
  | [inputFile, asmDir] =>
    let src ← IO.FS.readFile ⟨inputFile⟩
    match parseProgram src with
    | .error e => IO.eprintln s!"parse error: {e}"; return 1
    | .ok prog =>
      if !prog.wellFormed then IO.eprintln "not well-formed"; return 1
      let tyCtx := prog.tyCtx
      let tac := prog.compileToTAC
      match baselineCert tyCtx tac with
      | none => IO.println "no accepted non-identity baseline cert"; return 0
      | some (passName, cert) =>
        -- Emit the correct (baseline) trans asm for the driver's oracle.
        match verifiedGenerateAsm tyCtx cert.trans with
        | .ok r => match formatVerifiedAsm r cert.trans with
                   | .ok asm => IO.FS.writeFile ⟨s!"{asmDir}/correct.s"⟩ asm
                   | .error _ => pure ()
        | .error _ => pure ()
        let mut accepted := 0
        let mut rejected := 0
        for kind in ["const", "binop", "swap", "goto"] do
          for i in List.range cert.trans.code.size do
            match mutateCert cert kind i with
            | none => pure ()
            | some m =>
              if checkCertificateExec m then
                accepted := accepted + 1
                if dbg then
                  IO.println s!"  DBG {kind} pc={i}: {repr (cert.trans.code[i]?.getD .halt)} -> {repr (m.trans.code[i]?.getD .halt)}"
                  IO.println s!"  DBG mapped pc_orig={(cert.instrCerts.getD i default).pc_orig} orig={repr (cert.orig.code[(cert.instrCerts.getD i default).pc_orig]?.getD .halt)}"
                  IO.println s!"  DBG ic.rel={repr (cert.instrCerts.getD i default).rel}"
                  for (nm, b) in checkCertificateVerboseExec m do
                    if !b then IO.println s!"  DBG   FAILED-CHECK {nm}"
                -- emit asm of the mutated trans (if codegen succeeds) for the driver
                match verifiedGenerateAsm tyCtx m.trans with
                | .ok r => match formatVerifiedAsm r m.trans with
                           | .ok asm =>
                             IO.FS.writeFile ⟨s!"{asmDir}/accept_{kind}_{i}.s"⟩ asm
                             IO.println s!"ACCEPT {passName} {kind} pc={i}  -> accept_{kind}_{i}.s"
                           | .error _ => IO.println s!"ACCEPT {passName} {kind} pc={i}  (codegen-format failed)"
                | .error _ => IO.println s!"ACCEPT {passName} {kind} pc={i}  (codegen failed)"
              else
                rejected := rejected + 1
        IO.println s!"=== {inputFile}: baseline={passName} accepted={accepted} rejected={rejected} ==="
        return 0
  | _ => IO.eprintln "usage: certmutate <file.w> <asmOutDir>"; return 1

end CertMutate

def main (args : List String) : IO UInt32 := CertMutate.main args
