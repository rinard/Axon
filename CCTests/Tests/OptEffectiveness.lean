-- Copyright (c) 2026 Martin Rinard
import CredibleCompilation.CodeGen

instance : Inhabited IO.Error := ⟨IO.Error.userError ""⟩

/-!
# Optimization Effectiveness Tests

Each test constructs a TAC program where a specific optimization should fire,
runs the pass, and asserts:
  1. The certificate is valid (`checkCertificateExec`)
  2. The optimization actually changed the program

This catches regressions where an optimization silently becomes a no-op.
-/

-- ============================================================
-- § 1. ConstProp: fold known constants
-- ============================================================

/-- `x := 3; y := 4; z := x + y` → z should be folded to `const z 7`. -/
private def constPropProg : Prog :=
  { code := #[TAC.const "x" (.int 3),
              TAC.const "y" (.int 4),
              TAC.binop "z" .add "x" "y",
              TAC.halt],
    observable := ["z"] }
def constPropTyCtx : TyCtx := fun _ => .int

#eval! do
  let cert := ConstPropOpt.optimize constPropTyCtx constPropProg
  assert! checkCertificateExec cert
  assert! cert.trans.code != cert.orig.code
  -- z := x + y should become const z 7
  assert! cert.trans[2]? == some (TAC.const "z" (.int 7))

-- ============================================================
-- § 2. DCE: remove unreachable code after branch elimination
-- ============================================================

/-- ConstProp resolves the branch; DCE removes the unreachable else-arm. -/
private def dceProg : Prog :=
  { code := #[TAC.const "x" (.int 1),
              TAC.goto 3,          -- after constprop resolves ifgoto
              TAC.const "r" (.int 99),  -- unreachable
              TAC.const "r" (.int 42),
              TAC.halt],
    observable := ["r"] }
def dceTyCtx : TyCtx := fun _ => .int

#eval! do
  let cert := DCEOpt.optimize dceTyCtx dceProg
  assert! checkCertificateExec cert
  assert! cert.trans.size < cert.orig.size

-- ============================================================
-- § 3. DAE: eliminate dead assignments
-- ============================================================

/-- `x := 10; x := 5; r := x` → first assignment is dead.
    After ConstProp folds everything, x:=10 becomes dead with known
    trans-side value 0 (init). DAE replaces it with goto. -/
private def daeProg : Prog :=
  { code := #[TAC.const "x" (.int 10),
              TAC.const "x" (.int 5),
              TAC.copy "r" "x",
              TAC.halt],
    observable := ["r"] }
def daeTyCtx : TyCtx := fun _ => .int

#eval! do
  -- First run ConstProp so DAE has constant info
  let cp := ConstPropOpt.optimize daeTyCtx daeProg
  assert! checkCertificateExec cp
  let cert := DAEOpt.optimize daeTyCtx cp.trans
  assert! checkCertificateExec cert
  assert! cert.trans.code != cert.orig.code
  -- The dead `const x 10` (now at some PC) should become a goto
  let hasGoto := cert.trans.code.any fun instr =>
    match instr with | .goto _ => true | _ => false
  assert! hasGoto

-- ============================================================
-- § 4. CSE: reuse common subexpressions
-- ============================================================

/-- `a := x + y; b := x + y` → second becomes `copy b a`. -/
private def cseProg : Prog :=
  { code := #[TAC.const "x" (.int 3),
              TAC.const "y" (.int 4),
              TAC.binop "a" .add "x" "y",
              TAC.binop "b" .add "x" "y",
              TAC.halt],
    observable := ["a", "b"] }
def cseTyCtx : TyCtx := fun _ => .int

#eval! do
  let cert := CSEOpt.optimize cseTyCtx cseProg
  assert! checkCertificateExec cert
  assert! cert.trans.code != cert.orig.code
  -- Second binop should become a copy
  assert! cert.trans[3]? == some (TAC.copy "b" "a")

-- ============================================================
-- § 5. LICM: remove redundant loop-body recomputation
-- ============================================================

/-- Loop body recomputes __t1 := 42 on every iteration → LICM should hoist it. -/
private def licmProg : Prog :=
  { code := #[TAC.const "i" (.int 0),                     -- 0
              TAC.ifgoto (.cmp .lt (.var "i") (.lit 5)) 3, -- 1: loop test
              TAC.halt,                                    -- 2
              TAC.const "__t1" (.int 42),                  -- 3: redundant const in loop
              TAC.binop "i" .add "i" "__t1",               -- 4
              TAC.goto 1],                                 -- 5
    observable := ["i"] }
def licmTyCtx : TyCtx := fun _ => .int

#eval! do
  let cert := LICMOpt.optimize licmTyCtx licmProg
  assert! checkCertificateExec cert
  assert! cert.trans.code != cert.orig.code

-- ============================================================
-- § 6. Peephole: compact goto chains and goto(pc+1)
-- ============================================================

/-- goto(pc+1) nops should be removed, shrinking the program. -/
private def peepholeProg : Prog :=
  { code := #[TAC.const "x" (.int 1),   -- 0
              TAC.goto 2,                -- 1: nop goto(1+1)
              TAC.goto 3,                -- 2: nop goto(2+1)
              TAC.copy "r" "x",          -- 3
              TAC.halt],                 -- 4
    observable := ["r"] }
def peepholeTyCtx : TyCtx := fun _ => .int

#eval! do
  let cert := PeepholeOpt.optimize peepholeTyCtx peepholeProg
  assert! checkCertificateExec cert
  assert! cert.trans.size < cert.orig.size

-- ============================================================
-- § 7. Full pipeline: DAE + Peephole compact dead assignments
-- ============================================================

/-- Dead assignment eliminated by DAE, then goto compacted by Peephole. -/
private def fullPipelineProg : Prog :=
  { code := #[TAC.const "x" (.int 10),
              TAC.const "x" (.int 5),
              TAC.copy "r" "x",
              TAC.halt],
    observable := ["r"] }
def fullPipelineTyCtx : TyCtx := fun _ => .int

#eval!
  let p := fullPipelineProg
  let cert_cp := ConstPropOpt.optimize fullPipelineTyCtx p
  assert! checkCertificateExec cert_cp
  let cert_dae := DAEOpt.optimize fullPipelineTyCtx cert_cp.trans
  assert! checkCertificateExec cert_dae
  assert! cert_dae.trans.code != cert_dae.orig.code  -- DAE fired
  let cert_ph := PeepholeOpt.optimize fullPipelineTyCtx cert_dae.trans
  assert! checkCertificateExec cert_ph
  -- DAE introduced a goto, Peephole compacted it → smaller program
  assert! cert_ph.trans.size < fullPipelineProg.size
  true

-- ============================================================
-- § 8. DAE with floats: dead float assignment eliminated
-- ============================================================

/-- `a := 1.5; a := 3.0; r := a` → first float assignment is dead. -/
private def daeFloatProg : Prog :=
  { code := #[TAC.const "a" (.float (floatToBits 1.5)),
              TAC.const "a" (.float (floatToBits 3.0)),
              TAC.copy "r" "a",
              TAC.halt],
    observable := ["r"] }
def daeFloatTyCtx : TyCtx := fun _ => .float

#eval!
  let cp := ConstPropOpt.optimize daeFloatTyCtx daeFloatProg
  assert! checkCertificateExec cp
  let cert := DAEOpt.optimize daeFloatTyCtx cp.trans
  assert! checkCertificateExec cert
  assert! cert.trans.code != cert.orig.code
  true

-- ============================================================
-- § 9. RegAlloc: register allocation assigns registers
-- ============================================================

/-- A program with several int variables that should get register assignments.
    The identity certificate should be valid, and the coloring should assign
    at least one register. -/
private def regAllocProg : Prog :=
  { code := #[TAC.const "a" (.int 3),
              TAC.const "b" (.int 7),
              TAC.binop "c" .add "a" "b",
              TAC.binop "d" .mul "c" "a",
              TAC.binop "e" .sub "d" "b",
              TAC.binop "r" .add "e" "c",
              TAC.halt],
    observable := ["r"] }
def regAllocTyCtx : TyCtx := fun _ => .int

#eval!
  let cert := RegAllocOpt.optimize regAllocTyCtx regAllocProg
  assert! checkCertificateExec cert
  -- TAC-level renaming: programs differ (register names in code)
  assert! cert.trans.code != cert.orig.code
  -- Coloring assigns registers
  let coloring := RegAllocOpt.computeColoring regAllocTyCtx regAllocProg
  assert! !coloring.isEmpty
  true
