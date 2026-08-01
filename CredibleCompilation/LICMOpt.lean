-- Copyright (c) 2026 Martin Rinard
import CredibleCompilation.ConstPropOpt
import CredibleCompilation.DAEOpt

/-!
# Loop-Invariant Code Motion Optimizer

Hoists loop-invariant `const` instructions by inserting them before the
INNERMOST loop header and replacing the in-loop original with `goto (pc+1)`.

Each invocation hoists consts from ONE loop header only. Run repeatedly
to hoist across nested loops — each pass lifts consts one loop level out.

## Certificate strategy

Uses `(lit c, var x)` pairs in the expression relation for hoisted variables.
- origVal = `(lit c).substSym origSS` = `lit c` (literals self-evaluate)
- transVal = `(var x).substSym transSS .substSym preSubst` = `lit c` (via preSubst)
Both sides always equal `lit c` regardless of orig's state for x.
-/

namespace LICMOpt

-- ============================================================
-- § 1. Loop detection
-- ============================================================

def findLoopPCs (prog : Prog) : Array Bool :=
  let arr := Array.replicate prog.size false
  (List.range prog.size).foldl (fun arr pc =>
    match prog[pc]? with
    | some instr =>
      (instr.successors pc).foldl (fun arr target =>
        if target ≤ pc then
          (List.range (pc - target + 1)).foldl (fun arr offset =>
            arr.set! (target + offset) true
          ) arr
        else arr
      ) arr
    | none => arr
  ) arr

/-- Find the OUTERMOST loop header containing `pc`. -/
def findOutermostHeader (prog : Prog) (pc : Nat) : Option Nat :=
  let backEdges := (List.range prog.size).foldl (fun acc spc =>
    match prog[spc]? with
    | some instr =>
      (instr.successors spc).foldl (fun acc target =>
        if target ≤ spc then acc ++ [(target, spc)] else acc
      ) acc
    | none => acc
  ) ([] : List (Nat × Nat))
  let candidates := backEdges.filterMap fun (header, tail) =>
    if header ≤ pc && pc ≤ tail then some header else none
  -- Return the SMALLEST (outermost) header
  candidates.foldl (fun best h => match best with | none => some h | some b => some (min b h)) none

/-- A loop [header, tail] is reducible iff the header is the only entry from outside. -/
def isReducibleLoop (prog : Prog) (header tail : Nat) : Bool :=
  (List.range prog.size).all fun pc =>
    if pc >= header && pc <= tail then true  -- inside loop: ok
    else match prog[pc]? with
    | some instr =>
      (instr.successors pc).all fun target =>
        target < header || target > tail || target == header  -- only enter at header
    | none => true

-- ============================================================
-- § 2. Hoistable detection (single header only)
-- ============================================================

private def isTmp (v : Var) : Bool :=
  v.startsWith "__t" || v.startsWith "__ft"

/-- Find hoistable consts for ONE loop header only (the innermost).
    Returns list of (header, constPC, variable, value), all with same header. -/
def findHoistable (prog : Prog) (inLoop : Array Bool) : List (Nat × Nat × Var × Value) :=
  let candidates := (List.range prog.size).filterMap fun pc =>
    if !(inLoop.getD pc false) then none
    else match prog[pc]? with
    | some (.const x v) =>
      if !isTmp x then none
      else match findOutermostHeader prog pc with
      | none => none
      | some header =>
        -- Find the back-edge tail for this header and check reducibility
        let backEdgeTail := (List.range prog.size).foldl (fun best spc =>
          match prog[spc]? with
          | some instr =>
            if (instr.successors spc).any (· == header) && header ≤ spc then
              match best with | none => some spc | some b => some (max b spc)
            else best
          | none => best) (none : Option Nat)
        if !(backEdgeTail.any (isReducibleLoop prog header ·)) then none else
        let usedBefore := (List.range (pc - header)).any fun offset =>
          match prog[header + offset]? with
          | some instr => (DAEOpt.instrUse instr).contains x
          | none => false
        if usedBefore then none else some (header, pc, x, v)
    | _ => none
  -- Reject variables with conflicting values, then deduplicate
  let conflicting := candidates.filter fun (_, _, x, v) =>
    candidates.any fun (_, _, x', v') => x' == x && v' != v
  let conflictVars := conflicting.map fun (_, _, x, _) => x
  let filtered := candidates.filter fun (_, _, x, _) => !conflictVars.contains x
  let deduped := filtered.foldl (fun acc (h, pc, x, v) =>
    if acc.any (fun (_, _, x', _) => x' == x) then acc
    else acc ++ [(h, pc, x, v)]
  ) ([] : List (Nat × Nat × Var × Value))
  deduped

-- ============================================================
-- § 3. PC mapping
-- ============================================================

private def countsPerHeader (hoistable : List (Nat × Nat × Var × Value)) : List (Nat × Nat) :=
  hoistable.foldl (fun acc (h, _, _, _) =>
    match acc.find? (fun (h', _) => h' == h) with
    | some _ => acc.map (fun (h', n) => if h' == h then (h', n + 1) else (h', n))
    | none => acc ++ [(h, 1)]
  ) ([] : List (Nat × Nat))

def computePCMap (progSize : Nat) (hoistable : List (Nat × Nat × Var × Value)) : Array Nat :=
  let perHeader := countsPerHeader hoistable
  let (arr, _) := (List.range progSize).foldl (fun (arr, offset) origPC =>
    let insertHere := match perHeader.find? (fun (h, _) => h == origPC) with
      | some (_, n) => n | none => 0
    (arr.push (origPC + offset + insertHere), offset + insertHere)
  ) (Array.mkEmpty progSize, 0)
  arr

def buildOrigPCMap (progSize : Nat) (pcMap : Array Nat) (transSize : Nat)
    (hoistable : List (Nat × Nat × Var × Value)) : Array Nat :=
  let arr := Array.replicate transSize 0
  let arr := (List.range progSize).foldl (fun arr origPC =>
    arr.set! (pcMap.getD origPC origPC) origPC
  ) arr
  let perHeader := countsPerHeader hoistable
  perHeader.foldl (fun arr (h, count) =>
    let headerTrans := pcMap.getD h h
    (List.range count).foldl (fun arr offset =>
      arr.set! (headerTrans - count + offset) h
    ) arr
  ) arr

def isHoisted (trans : Prog) (origPCMap : Array Nat) (tpc : Nat) : Bool :=
  if tpc + 1 >= origPCMap.size then false
  else
    origPCMap.getD tpc tpc == origPCMap.getD (tpc + 1) (tpc + 1) &&
    match trans[tpc]? with | some (.const _ _) => true | _ => false

-- ============================================================
-- § 4. Transformation
-- ============================================================

def buildTrans (prog : Prog) (hoistable : List (Nat × Nat × Var × Value)) : Prog :=
  let pcMap := computePCMap prog.size hoistable
  let mapPC (origPC : Nat) : Nat := pcMap.getD origPC origPC
  let constsForHeader (h : Nat) : List TAC :=
    (hoistable.filter fun (h', _, _, _) => h' == h).map fun (_, _, x, v) => .const x v
  let replacedPCs := hoistable.map fun (_, pc, _, _) => pc
  -- For each hoisted header `h`: its loop tail (max back-edge source) and inserted-const
  -- count. The `count` consts occupy `[mapPC h - count, mapPC h - 1]` (the preheader) and
  -- `mapPC h` is the header instruction after them. Placement rule for an edge `spc → h`:
  --   * back-edge (source inside the loop, `h ≤ spc ≤ tail`): target `mapPC h` — SKIP the
  --     preheader, so the hoisted consts run once, not once per iteration;
  --   * entry/bypass edge (source outside `[h, tail]`, incl. a non-fall-through goto into
  --     the header): target `mapPC h - count` — route THROUGH the preheader, so the hoisted
  --     value is established on this path too.
  -- Establishing the value on every entry path (not just the fall-through) is what lets the
  -- existing certificate certify the hoist even when the header has a bypass entry — no
  -- checker/proof change, just a better placement. Fall-through entries already pass through
  -- the inline consts.
  let headerInfo : List (Nat × Nat × Nat) :=
    (countsPerHeader hoistable).map fun (h, count) =>
      let tail := ((List.range prog.size).foldl (fun best spc =>
        match prog[spc]? with
        | some instr =>
          if (instr.successors spc).any (· == h) && h ≤ spc then
            match best with | none => some spc | some b => some (max b spc)
          else best
        | none => best) (none : Option Nat)).getD h
      (h, tail, count)
  let remapTarget (spc l : Nat) : Nat :=
    match headerInfo.find? (fun (h, _, _) => h == l) with
    | some (h, tail, count) =>
      if h ≤ spc && spc ≤ tail then mapPC h      -- back-edge: skip preheader
      else mapPC h - count                        -- entry/bypass: route through preheader
    | none => mapPC l
  let newCode := (List.range prog.size).foldl (fun acc origPC =>
    let toInsert := constsForHeader origPC
    let instr := prog.code.getD origPC .halt
    let adjusted := if replacedPCs.contains origPC then
      TAC.goto (mapPC origPC + 1)
    else match instr with
      | .goto l => .goto (remapTarget origPC l)
      | .ifgoto be l => .ifgoto be (remapTarget origPC l)
      | other => other
    acc ++ toInsert ++ [adjusted]
  ) ([] : List TAC)
  { code := newCode.toArray,
    observable := prog.observable, arrayDecls := prog.arrayDecls }

-- ============================================================
-- § 5. Certificate with (lit c, var x) rel
-- ============================================================

/-- Forward must-analysis: at each trans PC, the set of hoisted variables whose
    inserted `const` has executed on EVERY path reaching that PC. A hoisted var is
    set once and never redefined, so the only transfer is "at a hoisted `const x _`,
    add x"; joins intersect. CFG-correct (unlike a PC-linear scan + global override),
    so a branch jumping OVER a later hoisted block does not claim that block's vars
    at the target — making the certificate's per-PC relation exactly match the real
    dataflow, which is what `checkRelConsistency` validates. -/
private partial def hoistLoop (trans : Prog) (origPCMap : Array Nat)
    (states : Array (Option (List Var))) (wl : List Nat) : Array (Option (List Var)) :=
  match wl with
  | [] => states
  | pc :: rest =>
    match trans[pc]?, states[pc]? with
    | some instr, some (some sin) =>
      let out := match instr with
        | .const x _ => if isHoisted trans origPCMap pc && !sin.contains x then x :: sin else sin
        | _ => sin
      let (states', newWork) := (instr.successors pc).foldl (fun (arr, w) pc' =>
        if pc' < arr.size then
          match arr[pc']? with
          | some none | none => (arr.set! pc' (some out), pc' :: w)
          | some (some old) =>
            let merged := old.filter (out.contains ·)  -- must-merge = intersection
            if merged.length == old.length then (arr, w)
            else (arr.set! pc' (some merged), pc' :: w)
        else (arr, w)) (states, rest)
      hoistLoop trans origPCMap states' newWork
    | _, _ => hoistLoop trans origPCMap states rest

private def hoistedSetAt (trans : Prog) (origPCMap : Array Nat) : Array (List Var) :=
  if trans.size == 0 then #[]
  else
    let init := (Array.replicate trans.size (none : Option (List Var))).set! 0 (some [])
    (hoistLoop trans origPCMap init (0 :: [])).map fun
      | some s => s
      | none   => []

private def buildInstrCerts (trans : Prog) (origPCMap : Array Nat)
    (allVars : List Var) (_hoistedVars : List (Var × Value)) : Array EInstrCert :=
  let hset := hoistedSetAt trans origPCMap
  let liveOut := DAEOpt.analyzeLiveness trans
  let litExprOf : Value → Expr
    | .int n => .lit n | .bool b => .blit b | .float f => .flit f
  -- Value of each hoisted variable, read from its inserted `const` in `trans`.
  let hoistedValMap : List (Var × Value) := (List.range trans.size).filterMap fun tpc =>
    if isHoisted trans origPCMap tpc then
      match trans[tpc]? with | some (.const x v) => some (x, v) | _ => none
    else none
  -- rel at a PC: for each LIVE variable, identity, plus `(lit, var)` for each hoisted
  -- var established there. Dead variables are dropped: a hoisted var that is dead at a
  -- relocated `goto`/loop-exit merge would otherwise carry the hoisted literal on one
  -- path and the original (un-hoisted) value on another — a divergence that is sound
  -- only because the variable is dead, but which an identity rel pair cannot express.
  let relAtPC (tpc : Nat) : EExprRel :=
    let est := hset.getD tpc ([] : List Var)
    let live := match trans[tpc]? with
      | some instr => DAEOpt.livenessTransfer instr (liveOut.getD tpc ([] : List Var))
      | none       => ([] : List Var)
    allVars.filterMap fun v =>
      if !live.contains v then none
      else match (if est.contains v then hoistedValMap.find? (fun (hv, _) => hv == v) else none) with
        | some (_, val) => some (litExprOf val, .var v)
        | none          => some (.var v, .var v)
  let arr := (List.range trans.size).map fun tpc =>
    let pc_orig := origPCMap.getD tpc tpc
    let rel := relAtPC tpc
    match trans[tpc]? with
    | some .halt =>
      { pc_orig := pc_orig, rel := rel, transitions := ([] : List ETransCorr) }
    | some (.goto l) =>
      let origTarget := origPCMap.getD l l
      { pc_orig := pc_orig, rel := rel,
        transitions := [{ origLabels := [origTarget], rel := rel, rel_next := relAtPC l }] }
    | some (.ifgoto _ l) =>
      let origTarget := origPCMap.getD l l
      { pc_orig := pc_orig, rel := rel,
        transitions := [{ origLabels := [origTarget], rel := rel, rel_next := relAtPC l },
                        { origLabels := [origPCMap.getD (tpc + 1) (tpc + 1)],
                          rel := rel, rel_next := relAtPC (tpc + 1) }] }
    | some _ =>
      if isHoisted trans origPCMap tpc then
        { pc_orig := pc_orig, rel := rel,
          transitions := [{ origLabels := [], rel := rel, rel_next := relAtPC (tpc + 1) }] }
      else
        let origNext := origPCMap.getD (tpc + 1) (tpc + 1)
        { pc_orig := pc_orig, rel := rel,
          transitions := [{ origLabels := [origNext], rel := rel, rel_next := relAtPC (tpc + 1) }] }
    | none => default
  arr.toArray

/-- Keep only hoists whose preheader DOMINATES the hoisted const's original slot.
    In the built `trans` the var must be established (`hoistedSetAt`, the CFG-correct
    must-analysis) at the trans position of its now-`goto`-replaced original const.
    A non-dominating hoist — the loop header is reached by a path that bypasses the
    inserted preheader (e.g. a non-fall-through entry, or a nested-loop structure) —
    is *unsound to certify*: the relation cannot assert the hoisted value at the
    in-loop slot, so `checkRelConsistency` rejects. Such a hoist produces a broken
    transformation anyway (the consts never run on that path), so dropping it loses
    no real optimization while leaving every dominating (certifiable) hoist intact.
    Iterated to a fixpoint: removing one hoist can change the dominance of another. -/
partial def dominatingHoists (prog : Prog)
    (hoistable : List (Nat × Nat × Var × Value)) : List (Nat × Nat × Var × Value) :=
  if hoistable.isEmpty then hoistable
  else
    let trans := buildTrans prog hoistable
    let pcMap := computePCMap prog.size hoistable
    let origPCMap := buildOrigPCMap prog.size pcMap trans.size hoistable
    let hset := hoistedSetAt trans origPCMap
    let liveOut := DAEOpt.analyzeLiveness trans
    -- A hoist of `x` is certifiable iff at EVERY PC where `x` is live, `x` is also
    -- established (`hset`) — i.e. the preheader dominates `x`'s whole live range, so
    -- the relation always carries `(lit, x)` and never falls back to a mismatching
    -- identity. Anywhere `x` is live but not must-set, the relation cannot assert its
    -- hoisted value and `checkRelConsistency` rejects.
    let dominates := fun (x : Var) =>
      (List.range trans.size).all fun tpc =>
        let live := match trans[tpc]? with
          | some i => DAEOpt.livenessTransfer i (liveOut.getD tpc ([] : List Var))
          | none   => ([] : List Var)
        !(live.contains x) || (hset.getD tpc ([] : List Var)).contains x
    let kept := hoistable.filter fun (_, _, x, _) => dominates x
    if kept.length == hoistable.length then hoistable
    else dominatingHoists prog kept

def numHoistable (prog : Prog) : Nat :=
  let inLoop := findLoopPCs prog
  (findHoistable prog inLoop).length

def optimize (tyCtx : TyCtx) (prog : Prog) : ECertificate :=
  let inLoop := findLoopPCs prog
  let hoistable := dominatingHoists prog (findHoistable prog inLoop)
  if hoistable.isEmpty then
    -- Nothing to hoist: valid identity certificate
    let allVars := _root_.collectAllVars prog prog
    let instrCerts := _root_.buildInstrCerts1to1 prog allVars
    let haltCerts := _root_.buildHaltCerts instrCerts prog
    { orig := prog, trans := prog, tyCtx := tyCtx,
      inv_orig := Array.replicate prog.size ([] : EInv),
      inv_trans := Array.replicate prog.size ([] : EInv),
      instrCerts := instrCerts, haltCerts := haltCerts,
      measure := Array.replicate prog.size 0 }
  else
  let trans := buildTrans prog hoistable
  let pcMap := computePCMap prog.size hoistable
  let origPCMap := buildOrigPCMap prog.size pcMap trans.size hoistable
  let allVars := _root_.collectAllVars prog trans
  let hoistedVars := hoistable.map fun (_, _, x, v) => (x, v)
  let consts_orig := ConstPropOpt.analyze prog
  let inv_orig := ConstPropOpt.buildInvariants consts_orig
  let consts_trans := ConstPropOpt.analyze trans
  let inv_trans := ConstPropOpt.buildInvariants consts_trans
  let instrCerts := buildInstrCerts trans origPCMap allVars hoistedVars
  let haltCerts := _root_.buildHaltCerts instrCerts trans
  let measure := (List.range trans.size).map fun tpc =>
    if isHoisted trans origPCMap tpc then
      let opc := origPCMap.getD tpc tpc
      let remaining := (List.range (trans.size - tpc - 1)).filter fun offset =>
        isHoisted trans origPCMap (tpc + 1 + offset) &&
        origPCMap.getD (tpc + 1 + offset) 0 == opc
      remaining.length + 1
    else 0
  { orig := prog, trans := trans, tyCtx := tyCtx,
    inv_orig := inv_orig, inv_trans := inv_trans,
    instrCerts := instrCerts, haltCerts := haltCerts,
    measure := measure.toArray }

end LICMOpt
