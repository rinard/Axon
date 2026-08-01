-- Copyright (c) 2026 Martin Rinard
import CredibleCompilation.ExecChecker

/-!
# Constant Propagation Optimizer

Takes a TAC program and a list of observable variables, performs forward
constant propagation, and produces an `ECertificate` that the executable
checker can verify.

## What it optimizes

1. **copy x y** where y has a known constant value c → **const x c**
2. **binop x op y z** where both y and z are known constants → **const x (op.eval a b)**
3. **ifgoto b l** where the condition evaluates to a known boolean →
   **goto l** (always taken) or **goto (pc+1)** (always falls through)
-/

namespace ConstPropOpt

-- ============================================================
-- § 1. Constant map
-- ============================================================

/-- Map from variables to their known constant values. No duplicate keys. -/
abbrev ConstMap := List (Var × Value)

def cmLookup (cm : ConstMap) (v : Var) : Option Value :=
  (cm.find? (fun p => p.1 == v)).map Prod.snd

def cmSet (cm : ConstMap) (x : Var) (n : Value) : ConstMap :=
  (x, n) :: cm.filter (fun p => !(p.1 == x))

def cmRemove (cm : ConstMap) (x : Var) : ConstMap :=
  cm.filter (fun p => !(p.1 == x))

/-- Intersection: keep only entries present in both maps with the same value. -/
def cmMerge (a b : ConstMap) : ConstMap :=
  a.filter fun (v, val) => b.any fun (v', val') => v == v' && val == val'

/-- Semantic equality: same set of (var, val) pairs (order-independent). -/
def cmBeq (a b : ConstMap) : Bool :=
  a.length == b.length &&
  a.all fun (v, val) => b.any fun (v', val') => v == v' && val == val'

-- ============================================================
-- § 2. Boolean expression evaluation under ConstMap
-- ============================================================

def evalBoolConst (cm : ConstMap) : BoolExpr → Option Bool
  | .lit b => some b
  | .bvar x =>
    match cmLookup cm x with
    | some (.bool b) => some b
    | _ => none
  | .cmp op a b =>
    match a, b with
    | .var x, .var y =>
      match cmLookup cm x, cmLookup cm y with
      | some (.int va), some (.int vb) => some (op.eval va vb)
      | _, _ => none
    | .var x, .lit n =>
      match cmLookup cm x with
      | some (.int va) => some (op.eval va n)
      | _ => none
    | .lit n, .var y =>
      match cmLookup cm y with
      | some (.int vb) => some (op.eval n vb)
      | _ => none
    | .lit va, .lit vb => some (op.eval va vb)
    | _, _ => none
  | .fcmp _op _a _b => none
  | .not e => evalBoolConst cm e |>.map (!·)
  | .bexpr _ => none

-- ============================================================
-- § 3. Transfer function
-- ============================================================

/-- Update the constant map after executing one instruction. -/
def transfer (cm : ConstMap) (instr : TAC) : ConstMap :=
  match instr with
  | .const x n => cmSet cm x n
  | .copy x y =>
    match cmLookup cm y with
    | some v => cmSet cm x v
    | none   => cmRemove cm x
  | .binop x op y z =>
    match cmLookup cm y, cmLookup cm z with
    | some (.int a), some (.int b) =>
      if op.safe a b then cmSet cm x (.int (op.eval a b))
      else cmRemove cm x
    | _, _           => cmRemove cm x
  | .boolop x _ => cmRemove cm x
  | .arrLoad x _ _ _ => cmRemove cm x
  | .fbinop x _ _ _ => cmRemove cm x
  | .intToFloat x _ => cmRemove cm x
  | .floatToInt x _ => cmRemove cm x
  | .floatUnary x _ _ => cmRemove cm x
  | .fternop x _ _ _ _ => cmRemove cm x
  | _ => cm

-- ============================================================
-- § 4. Forward dataflow analysis (worklist)
-- ============================================================

/-- Process one worklist entry: propagate constants from `pc` to its successors.
    Returns updated constants array and new worklist entries. -/
private def propagate (prog : Prog) (consts : Array (Option ConstMap))
    (pc : Nat) : Array (Option ConstMap) × List Nat :=
  match prog[pc]?, consts[pc]? with
  | some instr, some (some cm) =>
    let out := transfer cm instr
    let succs := instr.successors pc
    succs.foldl (fun (cs, wl) pc' =>
      if pc' < cs.size then
        match cs[pc']? with
        | some none | none =>
          (cs.set! pc' (some out), pc' :: wl)
        | some (some old) =>
          let merged := cmMerge old out
          if cmBeq merged old then (cs, wl)
          else (cs.set! pc' (some merged), pc' :: wl)
      else (cs, wl)
    ) (consts, [])
  | _, _ => (consts, [])

/-- Run the worklist algorithm. -/
private partial def analyzeLoop (prog : Prog) (consts : Array (Option ConstMap))
    (worklist : List Nat) : Array (Option ConstMap) :=
  match worklist with
  | [] => consts
  | pc :: rest =>
    let (consts', newWork) := propagate prog consts pc
    analyzeLoop prog consts' (rest ++ newWork)

/-- Forward constant propagation analysis.
    Returns `Option ConstMap` per PC (`none` = unreachable).

    Two phases. Phase 1 is the usual reachable forward analysis from PC 0. Phase 2
    seeds every still-unreachable PC with the `top` (empty) const map and
    re-propagates. This is required for certificate validity WITHOUT compaction:
    the checker validates EVERY physical transition, including those leaving a
    statically-unreachable PC (e.g. `mn := 9` in a constant-false branch). If such
    a dead edge's effect never reached the merge, the merge would keep the live
    edge's constant (`mn = 4`) and the certificate would assert an invariant that
    fails on the physical dead edge. Phase 2 propagates the dead edge too, so the
    merge is weakened (here `mn` becomes unknown) and every invariant holds on all
    physical predecessors. The branch fold itself is unaffected (it only needs the
    condition constant at the reachable `ifgoto`); the single-pass cross-merge
    precision lost here is recovered by DCE removing the dead arm and the LICM
    cluster re-running ConstProp on the cleaned program. -/
def analyze (prog : Prog) : Array (Option ConstMap) :=
  if prog.size == 0 then #[]
  else
    let init := (Array.replicate prog.size (none : Option ConstMap)).set! 0 (some [])
    let reached := analyzeLoop prog init (0 :: [])
    let deadPCs := (List.range prog.size).filter fun pc =>
      match reached[pc]? with | some none => true | _ => false
    let seeded := deadPCs.foldl (fun arr pc => arr.set! pc (some [])) reached
    analyzeLoop prog seeded deadPCs

-- ============================================================
-- § 5. Program transformation
-- ============================================================

/-- Transform a single instruction using known constants at its PC. -/
def transformInstr (cm : ConstMap) (instr : TAC) (pc : Nat) : TAC :=
  match instr with
  | .copy x y =>
    match cmLookup cm y with
    | some c => .const x c
    | none   => instr
  | .binop x op y z =>
    match cmLookup cm y, cmLookup cm z with
    | some (.int a), some (.int b) =>
      if op.safe a b then .const x (.int (op.eval a b)) else instr
    | _, _           => instr
  | .ifgoto b l =>
    match evalBoolConst cm b with
    | some true  => .goto l
    | some false => .goto (pc + 1)
    | none       => instr
  | other => other

/-- Transform the entire program. -/
def transformProg (prog : Prog) (consts : Array (Option ConstMap)) : Prog :=
  let arr := (List.range prog.size).map fun i =>
    match prog[i]?, consts[i]? with
    | some instr, some (some cm) => transformInstr cm instr i
    | some instr, _ => instr
    | none, _ => .halt  -- unreachable
  { code := arr.toArray, observable := prog.observable, arrayDecls := prog.arrayDecls }

-- ============================================================
-- § 6. Certificate generation
-- ============================================================

/-- Convert a ConstMap to an EInv (invariant). -/
def constMapToInv (cm : ConstMap) : EInv :=
  cm.map fun (v, val) => (v, match val with | .int n => .lit n | .bool b => .blit b | .float f => .flit f)

/-- Build the invariant arrays. Both programs share the same invariants
    since the transformation preserves all variable values. -/
def buildInvariants (consts : Array (Option ConstMap)) : Array EInv :=
  consts.map fun
    | some cm => constMapToInv cm
    | none    => []


-- ============================================================
-- § 7. Main entry point
-- ============================================================

/-- Run constant propagation on `prog` and produce a certified transformation.
    The result is an `ECertificate` that `checkCertificateExec` will accept. -/
def optimize (tyCtx : TyCtx) (prog : Prog) : ECertificate :=
  let consts := analyze prog
  let trans := transformProg prog consts
  let inv := buildInvariants consts
  -- NOTE: We deliberately do NOT compact away unreachable PCs here. `transformProg`
  -- is a structure-preserving rewrite (one trans instruction per orig instruction,
  -- folding `ifgoto`→`goto` in place), so `trans` is aligned 1-to-1 with the input
  -- `prog`. Keeping `orig := prog` (uncompacted) is required by the pipeline driver
  -- (`applyPass`), which only accepts a certificate whose `orig.code` equals the
  -- program it was handed. Compacting `orig` made `orig.code ≠ prog.code` precisely
  -- when folding created unreachable code (a constant branch) — ConstProp's signature
  -- case — causing the whole certificate to be rejected and the optimization silently
  -- dropped. Dead-code removal is left to the separate, independently-certified DCE
  -- pass that runs immediately after ConstProp in the pipeline.
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

end ConstPropOpt
