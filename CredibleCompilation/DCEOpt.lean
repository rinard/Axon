-- Copyright (c) 2026 Martin Rinard
import CredibleCompilation.ExecChecker

/-!
# Dead Code Elimination Optimizer

Takes a TAC program, computes reachable PCs from the entry point via plain
successor edges, removes unreachable instructions, and produces an
`ECertificate` that the executable checker can verify.

After ConstProp has already resolved deterministic branches to `goto`,
DCE only needs basic reachability — no invariants required.
-/

namespace DCEOpt

-- ============================================================
-- § 1. Transform instructions
-- ============================================================
-- Reachability is `_root_.reachable` from `ExecChecker`.

/-- Transform a single original instruction: remap labels. -/
def transformInstr (prog : Prog) (revMap : Array Nat) (origPC : Nat) : TAC :=
  match prog[origPC]? with
  | some (.const x n)      => .const x n
  | some (.copy x y)       => .copy x y
  | some (.binop x op y z) => .binop x op y z
  | some (.boolop x b)     => .boolop x b
  | some (.arrLoad x arr idx ty)   => .arrLoad x arr idx ty
  | some (.arrStore arr idx val ty) => .arrStore arr idx val ty
  | some (.fbinop x op y z) => .fbinop x op y z
  | some (.intToFloat x y) => .intToFloat x y
  | some (.floatToInt x y) => .floatToInt x y
  | some (.floatUnary x op y) => .floatUnary x op y
  | some (.fternop x op a b c) => .fternop x op a b c
  | some (.print fmt vs) => .print fmt vs
  | some (.printInt v)   => .printInt v
  | some (.printBool v)  => .printBool v
  | some (.printFloat v) => .printFloat v
  | some (.printString lit) => .printString lit
  | some .halt             => .halt
  | some (.goto l)         => .goto (revMap.getD l 0)
  | some (.ifgoto b l)     => .ifgoto b (revMap.getD l 0)
  | none => .halt

/-- Build the compacted program from reachable PCs. -/
def transformProg (prog : Prog) (origMap : Array Nat) (revMap : Array Nat) : Prog :=
  let arr := (List.range origMap.size).map fun i =>
    match origMap[i]? with
    | some pc => transformInstr prog revMap pc
    | none => .halt
  { code := arr.toArray, observable := prog.observable,
    arrayDecls := prog.arrayDecls }

-- ============================================================
-- § 2. Certificate generation
-- ============================================================

/-- Build per-instruction certificates.
    Each trans instruction corresponds to exactly one orig instruction step. -/
def buildInstrCerts (origMap : Array Nat) (trans : Prog) (allVars : List Var) : Array EInstrCert :=
  let idRel : EExprRel := allVars.map fun v => (.var v, .var v)
  let arr := (List.range trans.size).map fun i =>
    let origPC := origMap.getD i 0
    match trans[i]? with
    | some .halt =>
      { pc_orig := origPC, rel := idRel, transitions := ([] : List ETransCorr) }
    | some (.const _ _) | some (.copy _ _) | some (.binop _ _ _ _) | some (.boolop _ _)
    | some (.arrLoad _ _ _ _) | some (.arrStore _ _ _ _)
    | some (.fbinop _ _ _ _) | some (.intToFloat _ _) | some (.floatToInt _ _) | some (.floatUnary _ _ _)
    | some (.fternop _ _ _ _ _)
    | some (.print _ _) | some (.printInt _) | some (.printBool _) | some (.printFloat _) | some (.printString _) =>
      let nextOrigPC := origMap.getD (i + 1) 0
      { pc_orig := origPC, rel := idRel,
        transitions := [{ origLabels := (nextOrigPC :: []), rel := idRel, rel_next := idRel }] }
    | some (.goto l) =>
      let targetOrigPC := origMap.getD l 0
      { pc_orig := origPC, rel := idRel,
        transitions := [{ origLabels := (targetOrigPC :: []), rel := idRel, rel_next := idRel }] }
    | some (.ifgoto _ l) =>
      let takenOrigPC := origMap.getD l 0
      let fallOrigPC := origMap.getD (i + 1) 0
      { pc_orig := origPC, rel := idRel,
        transitions := [{ origLabels := (takenOrigPC :: []), rel := idRel, rel_next := idRel },
                        { origLabels := (fallOrigPC :: []), rel := idRel, rel_next := idRel }] }
    | none => default
  arr.toArray

-- ============================================================
-- § 3. Main entry point
-- ============================================================

/-- Run dead code elimination on `prog` and produce a certified transformation.
    Uses empty invariants — after ConstProp resolves branches to `goto`,
    basic reachability suffices. -/
def optimize (tyCtx : TyCtx) (prog : Prog) : ECertificate :=
  let reached := _root_.reachable prog
  let origMap := _root_.buildOrigMap reached
  let revMap := _root_.buildRevMap origMap prog.size
  let trans := transformProg prog origMap revMap
  let instrCerts := buildInstrCerts origMap trans (_root_.collectAllVars prog trans)
  let haltCerts := _root_.buildHaltCerts instrCerts trans
  { orig := prog
    trans := trans
    tyCtx := tyCtx
    inv_orig := Array.replicate prog.size ([] : EInv)
    inv_trans := Array.replicate trans.size ([] : EInv)
    instrCerts := instrCerts
    haltCerts := haltCerts
    measure := Array.replicate trans.size 0 }

end DCEOpt
