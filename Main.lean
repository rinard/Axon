-- Copyright (c) 2026 Martin Rinard
import CCTests.Examples.ExecExamples
import CCTests.Examples.ConstPropOptExamples
import CCTests.Examples.CSEOptExamples
import CCTests.Examples.DCEOptExamples
import CCTests.Examples.LICMOptExamples
import CCTests.Examples.PeepholeOptExamples
import CCTests.Examples.WhileExamples

def main : IO Unit := do
  IO.println "=== Credible Compilation Certificate Checker ==="
  IO.println ""
  IO.println "--- Hand-written certificates ---"
  let examples : List (String × Bool) := [
    ("Constant Propagation", checkCertificateExec ConstProp.cert),
    ("Copy Propagation", checkCertificateExec CopyProp.cert),
    ("Common Subexpression Elimination", checkCertificateExec CSE.cert),
    ("Dead Code Elimination", checkCertificateExec DCE.cert),
    ("Loop-Invariant Code Motion", checkCertificateExec LICM.cert),
    ("Induction Variable Elimination", checkCertificateExec IVE.cert),
    ("Bad Example (buggy transform)", checkCertificateExec BadExample.cert)
  ]
  for (name, result) in examples do
    let status := if result then "PASS" else "FAIL"
    IO.println s!"  {name}: {status}"
  IO.println ""
  IO.println "--- Automatic constant propagation ---"
  let cpCerts : List (String × ECertificate) := [
    ("Chain propagation", ConstPropOptExamples.simpleCert),
    ("Constant folding", ConstPropOptExamples.foldCert),
    ("Branch elimination", ConstPropOptExamples.branchCert),
    ("Loop (no change)", ConstPropOptExamples.loopCert)
  ]
  for (name, cert) in cpCerts do
    let status := if checkCertificateExec cert then "PASS" else "FAIL"
    IO.println s!"  {name}: {status}"
  IO.println ""
  IO.println "--- Automatic CSE ---"
  let cseCerts : List (String × ECertificate) := [
    ("Simple reuse", CSEOptExamples.simpleCert),
    ("Chained reuse", CSEOptExamples.chainCert),
    ("Kill (no change)", CSEOptExamples.killCert)
  ]
  for (name, cert) in cseCerts do
    let status := if checkCertificateExec cert then "PASS" else "FAIL"
    IO.println s!"  {name}: {status}"
  IO.println ""
  IO.println "--- Automatic DCE ---"
  let dceCerts : List (String × ECertificate) := [
    ("Dead branch (always taken)", DCEOptExamples.deadBranchCert),
    ("Dead fallthrough (always false)", DCEOptExamples.deadFallthroughCert),
    ("Goto skips dead block", DCEOptExamples.gotoSkipCert)
  ]
  for (name, cert) in dceCerts do
    let status := if checkCertificateExec cert then "PASS" else "FAIL"
    IO.println s!"  {name}: {status}"
  IO.println ""
  IO.println "--- Automatic LICM ---"
  let licmCerts : List (String × ECertificate) := [
    ("Classic loop-invariant recomputation", LICMOptExamples.classicCert),
    ("Straight-line redundant recomputation", LICMOptExamples.straightCert)
  ]
  for (name, cert) in licmCerts do
    let status := if checkCertificateExec cert then "PASS" else "FAIL"
    IO.println s!"  {name}: {status}"
  IO.println ""
  IO.println "--- Automatic Peephole ---"
  let peepCert := PeepholeOptExamples.licmCert
  let status := if checkCertificateExec peepCert then "PASS" else "FAIL"
  IO.println s!"  LICM cleanup ({PeepholeOptExamples.licmProg.size} → {peepCert.trans.size} instrs): {status}"
  IO.println ""
  IO.println "--- While language (source → TAC → optimize → check) ---"
  let whileCerts : List (String × ECertificate) := [
    ("Sum 1..n", WhileSum.cert),
    ("Factorial", WhileFactorial.cert),
    ("Max of two", WhileMax.cert),
    ("Constant expression", WhileConstExpr.cert),
    ("Absolute value", WhileAbsVal.cert),
    ("Nested loops", WhileNested.cert)
  ]
  for (name, cert) in whileCerts do
    let status := if checkCertificateExec cert then "PASS" else "FAIL"
    IO.println s!"  {name} ({cert.orig.size} → {cert.trans.size} instrs): {status}"
  IO.println ""
  IO.println "--- Verbose: Bad Example ---"
  for (name, result) in checkCertificateVerboseExec BadExample.cert do
    let mark := if result then "ok" else "FAIL"
    IO.println s!"  {name}: {mark}"
