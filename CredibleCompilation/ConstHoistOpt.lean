-- Copyright (c) 2026 Martin Rinard
import CredibleCompilation.ConstPropOpt

/-!
# Constant Hoisting Optimizer

Detects `const x v` instructions where ConstProp analysis shows `x` already
holds `v`, and replaces them with `goto (pc+1)`.  Peephole then compacts
consecutive gotos.  This hoists loop-invariant constant materializations
(e.g., `const __ft0 1.0` repeated every iteration) out of loops.

Uses only ConstProp invariants — completely independent of CSE analysis.
-/

namespace ConstHoistOpt

-- ============================================================
-- § 1. Redundancy detection
-- ============================================================

/-- A `const x v` is redundant if ConstProp shows x already holds v. -/
def isRedundantConst (cm : ConstPropOpt.ConstMap) (instr : TAC) : Bool :=
  match instr with
  | .const x v => ConstPropOpt.cmLookup cm x == some v
  | _ => false

-- ============================================================
-- § 2. Transformation
-- ============================================================

/-- Replace redundant const instructions with `goto (pc + 1)`. -/
def transformProg (prog : Prog) (consts : Array (Option ConstPropOpt.ConstMap)) : Prog :=
  let arr := (List.range prog.size).map fun i =>
    match prog[i]?, consts[i]? with
    | some instr, some (some cm) =>
      if isRedundantConst cm instr then .goto (i + 1) else instr
    | some instr, _ => instr
    | none, _ => .halt
  { code := arr.toArray, observable := prog.observable, arrayDecls := prog.arrayDecls }

-- ============================================================
-- § 3. Certificate generation
-- ============================================================

/-- Build invariant arrays from ConstProp analysis.
    Both programs share the same invariants (1:1 PC mapping). -/
def buildInvariants (consts : Array (Option ConstPropOpt.ConstMap)) : Array EInv :=
  consts.map fun
    | some cm => ConstPropOpt.constMapToInv cm
    | none    => []

-- ============================================================
-- § 4. Main entry point
-- ============================================================

def optimize (tyCtx : TyCtx) (prog : Prog) : ECertificate :=
  let consts := ConstPropOpt.analyze prog
  let trans := transformProg prog consts
  let inv := buildInvariants consts
  let instrCerts := _root_.buildInstrCerts1to1 trans (_root_.collectAllVars prog trans)
  let haltCerts := _root_.buildHaltCerts instrCerts trans
  { orig := prog
    trans := trans
    tyCtx := tyCtx
    inv_orig := inv
    inv_trans := inv
    instrCerts := instrCerts
    haltCerts := haltCerts
    measure := Array.replicate trans.size 0 }

end ConstHoistOpt
