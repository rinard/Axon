-- Copyright (c) 2026 Martin Rinard
import CredibleCompilation.ConstPropOpt

/-!
# Dead Assignment Elimination Optimizer

Takes a TAC program, performs backward liveness analysis, and eliminates
dead assignments (writes to variables never subsequently read) by replacing
them with `goto (pc+1)`. The subsequent Peephole pass removes these gotos.

## What it optimizes

**const x n**, **copy x y**, **boolop x be**, **fbinop x op y z**,
**intToFloat x y**, **floatToInt x y** where `x` is not live after the
instruction → **goto (pc+1)**

Only eliminates error-free instructions. `binop` with `div`/`mod` and
`arrLoad` are kept even if dead (they can produce runtime errors).

## Certificate strategy

Uses **expression relations** to track dead variables' trans-side constant
values, following the IVE2 pattern. When orig executes a dead assignment
`x := e` and trans skips it (goto), the trans-side `x` retains its previous
constant value `c`. The expression relation records `(.lit c, .var x)`.
-/

namespace DAEOpt

-- ============================================================
-- § 1. Backward liveness analysis
-- ============================================================

/-- Compute predecessors for each PC from the program's successor edges. -/
def buildPredecessors (prog : Prog) : Array (List Nat) :=
  let init := Array.replicate prog.size ([] : List Nat)
  (List.range prog.size).foldl (fun preds pc =>
    match prog[pc]? with
    | some instr =>
      (instr.successors pc).foldl (fun preds' succ =>
        if succ < preds'.size then
          preds'.set! succ (pc :: (preds'.getD succ ([] : List Nat)))
        else preds'
      ) preds
    | none => preds
  ) init

/-- Variable defined by an instruction (the write target), if any. -/
def instrDef (instr : TAC) : Option Var :=
  match instr with
  | .const x _      => some x
  | .copy x _       => some x
  | .binop x _ _ _  => some x
  | .boolop x _     => some x
  | .fbinop x _ _ _ => some x
  | .intToFloat x _ => some x
  | .floatToInt x _ => some x
  | .floatUnary x _ _ => some x
  | .fternop x _ _ _ _ => some x
  | .arrLoad x _ _ _ => some x
  | .print _ _ => none
  | _ => none

/-- Variables used (read) by an instruction. -/
def instrUse (instr : TAC) : List Var :=
  match instr with
  | .const _ _       => []
  | .copy _ y        => [y]
  | .binop _ _ y z   => [y, z]
  | .boolop _ be     => be.vars
  | .fbinop _ _ y z  => [y, z]
  | .intToFloat _ y  => [y]
  | .floatToInt _ y  => [y]
  | .floatUnary _ _ y => [y]
  | .fternop _ _ a b c => [a, b, c]
  | .arrLoad _ _ idx _ => [idx]
  | .arrStore _ idx val _ => [idx, val]
  | .goto _          => []
  | .ifgoto be _     => be.vars
  | .halt            => []
  | .print _ vs     => vs
  | .printInt v     => [v]
  | .printBool v    => [v]
  | .printFloat v   => [v]
  | .printString _  => []

/-- Remove a variable from a list. -/
private def listRemove (xs : List Var) (v : Var) : List Var :=
  xs.filter (· != v)

/-- Add a variable to a list if not already present. -/
private def listAdd (xs : List Var) (v : Var) : List Var :=
  if xs.contains v then xs else v :: xs

/-- Union of two variable lists (set union). -/
private def listUnion (a b : List Var) : List Var :=
  b.foldl listAdd a

/-- Transfer function (backward): liveIn = use ∪ (liveOut \ def). -/
def livenessTransfer (instr : TAC) (liveOut : List Var) : List Var :=
  let afterKill := match instrDef instr with
    | some x => listRemove liveOut x
    | none   => liveOut
  listUnion afterKill (instrUse instr)

/-- Backward liveness analysis using a worklist algorithm.
    Returns `liveOut` for each PC: variables live immediately after that PC. -/
partial def analyzeLiveness (prog : Prog) : Array (List Var) :=
  if prog.size == 0 then #[]
  else
    let preds := buildPredecessors prog
    -- Initialize: at halt PCs, liveOut = observable; everywhere else, empty
    let init := (List.range prog.size).foldl (fun arr pc =>
      match prog[pc]? with
      | some .halt => arr.set! pc prog.observable
      | _ => arr
    ) (Array.replicate prog.size ([] : List Var))
    -- Worklist: start from all PCs
    let worklist := List.range prog.size
    livenessLoop prog preds init worklist
where
  livenessLoop (prog : Prog) (preds : Array (List Nat))
      (liveOut : Array (List Var)) (worklist : List Nat) : Array (List Var) :=
    match worklist with
    | [] => liveOut
    | pc :: rest =>
      -- liveIn at pc = transfer(instr[pc], liveOut[pc])
      let liveIn := match prog[pc]? with
        | some instr => livenessTransfer instr (liveOut.getD pc ([] : List Var))
        | none => ([] : List Var)
      -- For each predecessor p of pc, liveOut[p] should include liveIn
      let (liveOut', newWork) := (preds.getD pc ([] : List Nat)).foldl (fun (lo, wl) p =>
        let oldLiveOut := lo.getD p ([] : List Var)
        let merged := listUnion oldLiveOut liveIn
        if merged.length == oldLiveOut.length then (lo, wl)
        else (lo.set! p merged, p :: wl)
      ) (liveOut, rest)
      livenessLoop prog preds liveOut' newWork

-- ============================================================
-- § 2. Dead assignment detection
-- ============================================================

/-- Is the instruction at this PC a dead, error-free assignment?
    Dead = writes to a variable not in liveOut.
    Error-free = not binop div/mod, not arrLoad. -/
def isDead (instr : TAC) (liveOut : List Var) : Bool :=
  match instr with
  | .const x _      => !liveOut.contains x
  | .copy x _       => !liveOut.contains x
  | .boolop x _     => !liveOut.contains x
  | .fbinop x _ _ _ => !liveOut.contains x
  | .intToFloat x _ => !liveOut.contains x
  | .floatToInt x _ => !liveOut.contains x
  | .floatUnary x _ _ => !liveOut.contains x
  | .fternop x _ _ _ _ => !liveOut.contains x
  -- binop: only eliminate add/sub/mul (not div/mod which can error)
  | .binop x op _ _ =>
    match op with
    | .div | .mod => false
    | _ => !liveOut.contains x
  -- arrLoad can bounds-error, arrStore has side effects → never eliminate
  | .arrLoad _ _ _ _ => false
  | .arrStore _ _ _ _ => false
  | .goto _ | .ifgoto _ _ | .halt => false
  | .print _ _ => false  -- side effect, never eliminate
  | .printInt _ => false -- side effect, never eliminate
  | .printBool _ => false -- side effect, never eliminate
  | .printFloat _ => false -- side effect, never eliminate
  | .printString _ => false -- side effect, never eliminate

-- ============================================================
-- § 3. Trans-side value tracking via ConstProp
-- ============================================================

/-- Determine the trans-side constant value of variable `x` at PC `pc`.
    After DAE replaces instruction at `pc` with goto, trans doesn't modify `x`,
    so `x` retains its value from the trans-side constant map at `pc`. -/
def transConstValue (consts : Array (Option ConstPropOpt.ConstMap)) (pc : Nat) (x : Var)
    : Option Value :=
  match consts[pc]? with
  | some (some cm) => ConstPropOpt.cmLookup cm x
  | _ => none

-- ============================================================
-- § 4. Transformation
-- ============================================================

/-- Mark which PCs are dead assignments with known trans-side constants. -/
def findDeadPCs (prog : Prog) (liveOut : Array (List Var))
    (consts : Array (Option ConstPropOpt.ConstMap)) : Array Bool :=
  (List.range prog.size).foldl (fun arr pc =>
    match prog[pc]? with
    | some instr =>
      if isDead instr (liveOut.getD pc ([] : List Var)) then
        match instrDef instr with
        | some x =>
          match transConstValue consts pc x with
          | some _ => arr.set! pc true
          | none   => arr
        | none => arr
      else arr
    | none => arr
  ) (Array.replicate prog.size false)

/-- Transform: replace dead assignments with goto (pc+1). -/
def transformProg (prog : Prog) (deadPCs : Array Bool) : Prog :=
  let arr := (List.range prog.size).map fun pc =>
    if deadPCs.getD pc false then .goto (pc + 1)
    else match prog[pc]? with
    | some instr => instr
    | none => .halt
  { code := arr.toArray, observable := prog.observable,
    arrayDecls := prog.arrayDecls }

/-- Simplify ifgotos whose condition is determined by ConstProp analysis. -/
def simplifyKnownBranches (prog : Prog)
    (consts : Array (Option ConstPropOpt.ConstMap)) : Prog :=
  let arr := (List.range prog.size).map fun pc =>
    match prog[pc]? with
    | some (.ifgoto b l) =>
      match consts[pc]? with
      | some (some cm) =>
        match ConstPropOpt.evalBoolConst cm b with
        | some true  => .goto l
        | some false => .goto (pc + 1)
        | none       => .ifgoto b l
      | _ => .ifgoto b l
    | some instr => instr
    | none => .halt
  { code := arr.toArray, observable := prog.observable,
    arrayDecls := prog.arrayDecls }

-- ============================================================
-- § 5. Expression relation computation
-- ============================================================

/-- Forward analysis to compute expression relations at each PC.
    At a dead assignment to `x`, add `(.lit c, .var x)` where `c` is the
    trans-side constant. Drop entries when `x` is reassigned by a live instr.
    At merge points, take intersection. -/
partial def computeRels (prog : Prog) (deadPCs : Array Bool)
    (consts : Array (Option ConstPropOpt.ConstMap)) : Array EExprRel :=
  if prog.size == 0 then #[]
  else
    let allVars := _root_.collectAllVars prog prog
    let idRel : EExprRel := allVars.map fun v => (.var v, .var v)
    let init := (Array.replicate prog.size (none : Option EExprRel)).set! 0 (some idRel)
    let reached := relLoop prog deadPCs consts init (0 :: ([] : List Nat))
    -- Second phase (mirrors `ConstPropOpt.analyze`): seed every still-unreachable
    -- PC with `idRel` (the identity/top relation) and re-propagate, so the
    -- relation is consistent across EVERY physical edge — including those leaving
    -- a statically-dead PC, which the certificate checker still validates.
    let deadUnreached := (List.range prog.size).filter fun pc =>
      match reached[pc]? with | some none => true | _ => false
    let seeded := deadUnreached.foldl (fun arr pc => arr.set! pc (some idRel)) reached
    let result := relLoop prog deadPCs consts seeded deadUnreached
    result.map fun
      | some rel => rel
      | none => ([] : EExprRel)
where
  relMerge (a b : EExprRel) : EExprRel :=
    a.filter fun (eo, et) => b.any fun (eo', et') => eo == eo' && et == et'
  relBeq (a b : EExprRel) : Bool :=
    a.length == b.length && a.all fun (eo, et) => b.any fun (eo', et') => eo == eo' && et == et'
  relTransfer (rel : EExprRel) (pc : Nat) (instr : TAC)
      (deadPCs : Array Bool) (consts : Array (Option ConstPropOpt.ConstMap)) : EExprRel :=
    if deadPCs.getD pc false then
      -- Dead assignment to x: DAE deletes the store in `trans` (it becomes a `goto`),
      -- while `orig` still performs it. So after this PC, orig `x` holds `c` but trans
      -- `x` holds its old value — they DIVERGE. Because `x` is dead (never observed),
      -- this is sound, but the relation must not claim anything about `x`: drop every
      -- `x` entry and add none. (A previous version asserted `(.lit c, .var x)` — trans
      -- `x = c` — which is false once the establishing store is removed, and whose
      -- trans-side `x` is then uncovered by `rel_pre`, so the checker rejected it. `x`
      -- re-enters the relation as identity at its next LIVE definition, below.)
      match instrDef instr with
      | some x => rel.filter fun (_, et) => et != .var x
      | none => rel
    else
      -- Live instruction: if it writes to x, replace non-identity entries with identity
      -- (both orig and trans execute the same instruction, so x maps to itself)
      match instrDef instr with
      | some x =>
        let rel' := rel.filter fun (_, et) => et != .var x
        (.var x, .var x) :: rel'
      | none => rel
  relLoop (prog : Prog) (deadPCs : Array Bool)
      (consts : Array (Option ConstPropOpt.ConstMap))
      (rels : Array (Option EExprRel)) (worklist : List Nat) : Array (Option EExprRel) :=
    match worklist with
    | [] => rels
    | pc :: rest =>
      match prog[pc]?, rels[pc]? with
      | some instr, some (some rel) =>
        let out := relTransfer rel pc instr deadPCs consts
        let succs := instr.successors pc
        let (rels', newWork) := succs.foldl (fun (arr, wl) pc' =>
          if pc' < arr.size then
            match arr[pc']? with
            | some none | none =>
              (arr.set! pc' (some out), pc' :: wl)
            | some (some old) =>
              let merged := relMerge old out
              if relBeq merged old then (arr, wl)
              else (arr.set! pc' (some merged), pc' :: wl)
          else (arr, wl)
        ) (rels, rest)
        relLoop prog deadPCs consts rels' newWork
      | _, _ => relLoop prog deadPCs consts rels rest

-- ============================================================
-- § 6. Certificate generation
-- ============================================================

/-- Build instrCerts for DAE. 1:1 PC mapping with expression relations.
    At dead assignment PCs, orig path goes through orig instruction while
    trans executes goto(pc+1). -/
def buildInstrCerts (trans : Prog) (rels : Array EExprRel) : Array EInstrCert :=
  let arr := (List.range trans.size).map fun i =>
    let rel := rels.getD i ([] : EExprRel)
    let relNext (target : Nat) : EExprRel := rels.getD target ([] : EExprRel)
    match trans[i]? with
    | some .halt =>
      { pc_orig := i, rel := rel, transitions := ([] : List ETransCorr) }
    | some (.goto l) =>
      { pc_orig := i, rel := rel,
        transitions := [{ origLabels := [l], rel := rel, rel_next := relNext l }] }
    | some (.ifgoto _ l) =>
      { pc_orig := i, rel := rel,
        transitions := [{ origLabels := [l], rel := rel, rel_next := relNext l },
                        { origLabels := [i + 1], rel := rel, rel_next := relNext (i + 1) }] }
    | some _ =>
      { pc_orig := i, rel := rel,
        transitions := [{ origLabels := [i + 1], rel := rel, rel_next := relNext (i + 1) }] }
    | none => default
  arr.toArray

-- ============================================================
-- § 7. Main entry point
-- ============================================================

/-- Run dead assignment elimination on `prog` and produce a certified
    transformation. -/
def optimize (tyCtx : TyCtx) (prog : Prog) : ECertificate :=
  let liveOut := analyzeLiveness prog
  let consts := ConstPropOpt.analyze prog
  let deadPCs := findDeadPCs prog liveOut consts
  let trans0 := transformProg prog deadPCs
  let constsT := ConstPropOpt.analyze trans0
  let rels := computeRels prog deadPCs constsT
  let inv_orig := ConstPropOpt.buildInvariants consts
  let inv_trans := ConstPropOpt.buildInvariants constsT
  -- Simplify ifgotos with known conditions
  let trans := simplifyKnownBranches trans0 consts
  let instrCerts := buildInstrCerts trans rels
  let haltCerts := (List.range trans.size).map fun i =>
    { pc_orig := i, rel := rels.getD i ([] : EExprRel) : EHaltCert }
  { orig := prog
    trans := trans
    tyCtx := tyCtx
    inv_orig := inv_orig
    inv_trans := inv_trans
    instrCerts := instrCerts
    haltCerts := haltCerts.toArray
    measure := Array.replicate trans.size 0 }

end DAEOpt
