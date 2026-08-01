-- Copyright (c) 2026 Martin Rinard
import CredibleCompilation.ExecChecker

/-!
# Peephole Optimizer

Removes syntactic no-ops (`goto (pc+1)` and `copy x x`) and compacts the
program, producing an `ECertificate` that the executable checker can verify.

Useful as a post-pass after LICM, which replaces redundant recomputations
with `goto (pc+1)`.

## What it optimizes

1. **goto (pc+1)** — redundant jump to the next instruction → removed
2. **copy x x** — self-copy with no effect → removed

Labels in remaining instructions are remapped to account for the removal.
The original execution path through removed no-ops is recorded in the
certificate's `origLabels` so the checker can verify that the skip is valid.
-/

namespace PeepholeOpt

-- ============================================================
-- § 1. No-op detection
-- ============================================================

/-- Detect syntactically redundant instructions.
    Never removes PC 0 (checker requires `instrCerts[0].pc_orig == 0`). -/
def isNop (prog : Prog) (pc : Nat) : Bool :=
  if pc == 0 then false
  else match prog[pc]? with
  | some (.goto l)   =>
    -- A `goto (pc+1)` is normally a removable no-op. EXCEPT when it is the
    -- fall-through of a preceding `ifgoto`: removing it would skip-merge the
    -- ifgoto's taken-target onto its fall-through PC, producing a degenerate
    -- `ifgoto` whose target equals its fall-through. The certificate checker
    -- cannot validate the original path across such a branch for a runtime
    -- condition (it has no `branchInfo` to resolve which arm was taken), so it
    -- would reject the whole pass. Keep this one goto to preserve the branch.
    l == pc + 1 && !(match prog[pc-1]? with | some (.ifgoto _ _) => true | _ => false)
  | some (.copy x y) => x == y
  | _ => false

-- ============================================================
-- § 2. Skip array
-- ============================================================

/-- For each PC, the first non-removed PC at or after it.
    Computed right-to-left in one pass. -/
def buildSkipArr (removed : Array Bool) : Array Nat :=
  let n := removed.size
  let (arr, _) := (List.range n).foldr (fun i (arr, nextSkip) =>
    if removed.getD i false then (arr.set! i nextSkip, nextSkip)
    else (arr.set! i i, i)
  ) (Array.replicate n n, n)
  arr

-- ============================================================
-- § 3. Mapping arrays (uses shared buildOrigMap / buildRevMap)
-- ============================================================

/-- Negate a removed-array into a kept-array for `buildOrigMap`. -/
def removedToKept (removed : Array Bool) : Array Bool :=
  removed.map (!·)

-- ============================================================
-- § 4. Transformation
-- ============================================================

/-- Remap goto/ifgoto labels through the skip array and reverse map. -/
def transformInstr (instr : TAC) (skipArr : Array Nat)
    (revMap : Array Nat) : TAC :=
  match instr with
  | .goto l    => .goto (revMap.getD (skipArr.getD l l) 0)
  | .ifgoto b l => .ifgoto b (revMap.getD (skipArr.getD l l) 0)
  | other      => other

/-- Build the compacted program. -/
def transformProg (prog : Prog) (origMap : Array Nat)
    (skipArr : Array Nat) (revMap : Array Nat) : Prog :=
  { code := ((List.range origMap.size).map fun i =>
    match origMap[i]? with
    | some pc =>
      match prog[pc]? with
      | some instr => transformInstr instr skipArr revMap
      | none => .halt
    | none => .halt).toArray, observable := prog.observable, arrayDecls := prog.arrayDecls }

-- ============================================================
-- § 5. Orig-path builder
-- ============================================================

/-- Build a path `[start, start+1, ..., end_]` (inclusive). -/
def buildPath (start end_ : Nat) : List Nat :=
  if start > end_ then [end_]
  else (List.range (end_ - start + 1)).map (· + start)

-- ============================================================
-- § 6. Certificate generation
-- ============================================================

/-- Build per-instruction certificates.
    The `origLabels` for each transition include intermediate PCs
    of removed no-ops that the original execution passes through. -/
def buildInstrCerts (prog : Prog) (origMap : Array Nat)
    (skipArr : Array Nat) (trans : Prog) (allVars : List Var) : Array EInstrCert :=
  let idRel : EExprRel := allVars.map fun v => (.var v, .var v)
  ((List.range trans.size).map fun i =>
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
        transitions := [{ origLabels := buildPath (origPC + 1) nextOrigPC, rel := idRel, rel_next := idRel }] }
    | some (.goto _) =>
      let origTarget := match prog[origPC]? with
        | some (.goto l) => l
        | _ => origPC + 1
      let finalOrigTarget := skipArr.getD origTarget origTarget
      { pc_orig := origPC, rel := idRel,
        transitions := [{ origLabels := buildPath origTarget finalOrigTarget, rel := idRel, rel_next := idRel }] }
    | some (.ifgoto _ _) =>
      let origTaken := match prog[origPC]? with
        | some (.ifgoto _ l) => l
        | _ => origPC
      let takenFinal := skipArr.getD origTaken origTaken
      let fallFinal := origMap.getD (i + 1) 0
      { pc_orig := origPC, rel := idRel,
        transitions := [{ origLabels := buildPath origTaken takenFinal, rel := idRel, rel_next := idRel },
                        { origLabels := buildPath (origPC + 1) fallFinal, rel := idRel, rel_next := idRel }] }
    | none => default).toArray

-- ============================================================
-- § 7. Main entry point
-- ============================================================

/-- Run peephole optimization: remove `goto (pc+1)` and `copy x x`,
    compact the program, and produce a certified transformation. -/
def optimize (tyCtx : TyCtx) (prog : Prog) : ECertificate :=
  let n := prog.size
  let removed := ((List.range n).map (isNop prog)).toArray
  let origMap := _root_.buildOrigMap (removedToKept removed)
  let revMap := _root_.buildRevMap origMap n
  let skipArr := buildSkipArr removed
  let trans := transformProg prog origMap skipArr revMap
  let instrCerts := buildInstrCerts prog origMap skipArr trans (_root_.collectAllVars prog trans)
  let haltCerts := _root_.buildHaltCerts instrCerts trans
  { orig := prog
    trans := trans
    tyCtx := tyCtx
    inv_orig := Array.replicate n ([] : EInv)
    inv_trans := Array.replicate trans.size ([] : EInv)
    instrCerts := instrCerts
    haltCerts := haltCerts
    measure := Array.replicate trans.size 0 }

end PeepholeOpt
