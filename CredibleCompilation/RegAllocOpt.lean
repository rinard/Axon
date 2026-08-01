-- Copyright (c) 2026 Martin Rinard
import CredibleCompilation.DAEOpt

/-!
# Register Allocation Optimizer

Computes graph-coloring register allocation for TAC programs. Variables are
assigned to ARM64 registers when possible; remaining variables are spilled
to the stack.

The TAC program is unchanged (identity transformation). Register assignments
are consumed by CodeGen to emit register-aware instructions.

## Register budget

| Pool | Registers | Count |
|------|-----------|-------|
| Int scratch | x0, x1, x2 | 3 |
| Addr scratch | x8 | 1 |
| Int caller-saved | x3-x7, x9-x15 | 12 |
| Int callee-saved | x19-x28 | 10 |
| Reserved         | x16-x17 (IP0/IP1), x18 (platform) | 3 |
| Float scratch | d0, d1, d2 | 3 |
| Float allocatable | d3-d15 | 13 |

## Algorithm: graph coloring

1. Backward liveness analysis (reuse `DAEOpt.analyzeLiveness`)
2. Build interference graph: two variables interfere if either is defined at a
   PC where the other is live-out (and when both are live-out at some PC).
   Separate graphs for int and float variables.
3. Simplify: repeatedly remove nodes with degree < K, push onto stack
4. Spill selection: if no node has degree < K, spill the variable with
   the longest live range
5. Color: pop from stack, assign lowest-numbered available register
-/

namespace RegAllocOpt

-- ============================================================
-- § 1. Liveness helpers
-- ============================================================

/-- Collect all variables that appear in any liveOut set. -/
def collectLiveVars (liveOut : Array (List Var)) : List Var :=
  liveOut.foldl (fun acc lo =>
    lo.foldl (fun a v => if a.contains v then a else a ++ [v]) acc
  ) ([] : List Var)

/-- Compute the live range length for each variable (number of PCs where live). -/
def computeLiveRanges (liveOut : Array (List Var)) : List (Var × Nat) :=
  let vars := collectLiveVars liveOut
  vars.map fun v =>
    let range := liveOut.foldl (fun count lo =>
      if lo.contains v then count + 1 else count
    ) 0
    (v, range)

-- ============================================================
-- § 2. Interference graph
-- ============================================================

/-- Build interference graph. Two variables interfere when either is **defined** at a
    PC where the other is **live-out** (Chaitin's def-vs-liveOut rule), as well as when
    both are live-out at some PC. The def-vs-liveOut edge is essential for soundness: a
    variable can be defined yet immediately dead (a dead store), so it appears in NO
    liveOut set — yet its definition still WRITES its register and would clobber any
    live variable sharing that register. Omitting this edge lets such a dead def share a
    register with a value that is live across it, producing an allocation the
    certificate checker (correctly) rejects. Returns adjacency list. -/
def buildInterference (prog : Prog) (vars : List Var) (liveOut : Array (List Var))
    : List (Var × List Var) :=
  let defAt : Array (Option Var) :=
    ((List.range prog.size).map fun pc => (prog[pc]?).bind DAEOpt.instrDef).toArray
  vars.map fun v =>
    let neighbors := vars.filter fun w =>
      v != w && (List.range prog.size).any fun pc =>
        let lo := liveOut.getD pc ([] : List Var)
        (lo.contains v && lo.contains w)
          || (defAt.getD pc none == some v && lo.contains w)
          || (defAt.getD pc none == some w && lo.contains v)
    (v, neighbors)

/-- Remove a node and all its edges from the graph. -/
def removeNode (graph : List (Var × List Var)) (v : Var) : List (Var × List Var) :=
  graph.filterMap fun (w, nbrs) =>
    if w == v then none
    else some (w, nbrs.filter (· != v))

/-- Get neighbors of a node in the graph. -/
def neighbors (graph : List (Var × List Var)) (v : Var) : List Var :=
  match graph.find? (fun (x, _) => x == v) with
  | some (_, nbrs) => nbrs
  | none => []

-- ============================================================
-- § 2b. Loop-depth analysis (back-edge counting)
-- ============================================================

/-- Find back edges: PCs where a successor target ≤ source PC.
    Returns a list of (header, latch) pairs. -/
def findBackEdges (prog : Prog) : List (Nat × Nat) :=
  (List.range prog.size).foldl (fun (acc : List (Nat × Nat)) pc =>
    match prog[pc]? with
    | some instr =>
      (instr.successors pc).foldl (fun acc' succ =>
        if succ ≤ pc then (succ, pc) :: acc' else acc'
      ) acc
    | none => acc
  ) ([] : List (Nat × Nat))

/-- Loop depth at each PC = number of back-edge ranges (header, latch)
    that contain that PC, where the range is [header, latch] inclusive.
    Nested loops naturally accumulate depth. -/
def computeLoopDepth (prog : Prog) : Array Nat :=
  let backEdges := findBackEdges prog
  ((List.range prog.size).map fun pc =>
    backEdges.foldl (fun d (hdr, latch) =>
      if hdr ≤ pc && pc ≤ latch then d + 1 else d) 0
  ).toArray

/-- Chaitin-style spill cost per variable: sum over uses of `10^loop_depth`.
    A variable used inside a depth-2 loop counts each use as 100; depth-1 as 10. -/
def computeUseCost (prog : Prog) (loopDepth : Array Nat) : List (Var × Nat) :=
  (List.range prog.size).foldl (fun (acc : List (Var × Nat)) pc =>
    match prog[pc]? with
    | some instr =>
      let depth := loopDepth.getD pc 0
      let weight := 10 ^ depth
      (DAEOpt.instrUse instr).foldl (fun acc' v =>
        match acc'.find? (fun (x, _) => x == v) with
        | some _ => acc'.map fun (x, c) => if x == v then (x, c + weight) else (x, c)
        | none => (v, weight) :: acc'
      ) acc
    | none => acc
  ) ([] : List (Var × Nat))

-- ============================================================
-- § 3. Graph coloring with spill selection
-- ============================================================

/-- Find the lowest non-negative integer not in the used set. -/
private def lowestAvailable (used : List Nat) : Nat :=
  let rec go (n : Nat) (fuel : Nat) : Nat :=
    match fuel with
    | 0 => n
    | fuel + 1 => if used.contains n then go (n + 1) fuel else n
  go 0 (used.length + 1)

/-- Look up Chaitin spill cost for a variable. -/
private def costOf (useCost : List (Var × Nat)) (v : Var) : Nat :=
  match useCost.find? (fun (x, _) => x == v) with
  | some (_, c) => c
  | none => 0

/-- Look up degree (neighbor count) for a variable in the current graph. -/
private def degreeOf (graph : List (Var × List Var)) (v : Var) : Nat :=
  match graph.find? (fun (x, _) => x == v) with
  | some (_, nbrs) => nbrs.length
  | none => 0

/-- Select the best variable to spill: minimize Chaitin cost / degree.
    A variable with few uses (low cost) and many interferences (high degree)
    is the best spill candidate — spilling frees many neighbors at little
    runtime cost. Loop-resident variables have inflated cost via 10^depth
    weighting (computeUseCost) so they are spilled last. -/
private def selectSpill (graph : List (Var × List Var)) (useCost : List (Var × Nat)) : Var :=
  let graphVars := graph.map Prod.fst
  match graphVars with
  | [] => ""
  | v :: rest =>
    rest.foldl (fun best w =>
      let bestC := costOf useCost best
      let bestD := degreeOf graph best
      let wC := costOf useCost w
      let wD := degreeOf graph w
      -- Compare cost/degree via cross-multiplication: w wins if
      --   wC / wD < bestC / bestD  ⟺  wC * bestD < bestC * wD
      -- (using max(_,1) on degree to avoid div-by-zero; matters at the leaves)
      if wC * (max bestD 1) < bestC * (max wD 1) then w else best
    ) v

/-- Graph coloring with spill selection.
    Returns (coloring: var → color index, spilled: list of spilled vars).
    Caller-saved registers are listed first in intRegNums/floatRegNums,
    so `lowestAvailable` naturally prioritizes them. -/
partial def graphColor (graph : List (Var × List Var)) (K : Nat)
    (useCost : List (Var × Nat))
    : List (Var × Nat) × List Var :=
  if graph.isEmpty then ([], [])
  else
    -- Try simplify: find node with degree < K
    match graph.find? (fun (_, nbrs) => nbrs.length < K) with
    | some (v, _) =>
      let nbrs_v := neighbors graph v
      let graph' := removeNode graph v
      let (coloring, spilled) := graphColor graph' K useCost
      -- Assign lowest color not used by colored neighbors
      let usedColors := coloring.filterMap fun (w, c) =>
        if nbrs_v.contains w then some c else none
      let color := lowestAvailable usedColors
      ((v, color) :: coloring, spilled)
    | none =>
      -- All nodes have degree ≥ K → spill the lowest-cost variable
      let spillVar := selectSpill graph useCost
      let graph' := removeNode graph spillVar
      let (coloring, spilled) := graphColor graph' K useCost
      (coloring, spillVar :: spilled)

-- ============================================================
-- § 4. Register mapping
-- ============================================================

/-- Integer allocatable registers: x3-x8, x9-x15 (caller-saved), x19-x28 (callee-saved).
    Caller-saved listed first so graph coloring prefers them under low pressure.
    x0-x2 reserved as scratch,
    x16-x17 reserved (linker scratch IP0/IP1), x18 reserved (platform register). -/
def intRegNums : Array Nat :=
  #[3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,   -- caller-saved (13)
    19, 20, 21, 22, 23, 24, 25, 26, 27, 28]          -- callee-saved (10)

/-- Float allocatable registers: d3-d15 (13 total).
    d0-d2 reserved as scratch (d2 used by fcmp/fbinop fallback). -/
def floatRegNums : Array Nat := #[3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- Compute register allocation for a program.
    Returns a list of (variable_name, register_name) pairs.
    Register names are like "ir3", "br10", "fr5", etc. -/
def computeColoring (tyCtx : TyCtx) (prog : Prog) : List (Var × String) :=
  if prog.size == 0 then []
  else
    let liveOut := DAEOpt.analyzeLiveness prog
    let allVars := collectLiveVars liveOut
    if allVars.isEmpty then []
    else
      -- Chaitin spill cost: each use weighted by 10^loop_depth at that PC.
      -- This biases the spill heuristic away from loop-resident variables.
      let loopDepth := computeLoopDepth prog
      let useCost := computeUseCost prog loopDepth
      -- Separate int+bool (xN registers) from float (dN registers).
      -- Int and bool share the same physical registers but get different
      -- name prefixes (__ir vs __br) so the type context can derive types.
      -- We add type-conflict edges: int and bool variables always
      -- interfere, forcing each register color to have a single type.
      let intBoolVars := allVars.filter fun v => tyCtx v != .float
      let floatVars := allVars.filter fun v => tyCtx v == .float
      -- Build interference graph with type-conflict edges
      let baseGraph := buildInterference prog intBoolVars liveOut
      -- Add edges between every int-bool pair (different types must not share a color)
      let intBoolGraph := baseGraph.map fun (v, nbrs) =>
        let extraNbrs := intBoolVars.filter fun w =>
          v != w && tyCtx v != tyCtx w && !nbrs.contains w
        (v, nbrs ++ extraNbrs)
      let floatGraph := buildInterference prog floatVars liveOut
      -- Color each graph. Caller-saved registers are listed first in
      -- intRegNums/floatRegNums, so lowestAvailable naturally prioritizes them.
      -- CodeGen inserts save/restore around call sites for live caller-saved regs.
      let (intBoolColoring, _) := graphColor intBoolGraph intRegNums.size useCost
      let (floatColoring, _) := graphColor floatGraph floatRegNums.size useCost
      -- Determine the type of each color from the first variable that uses it
      let colorTypes := intBoolColoring.foldl (fun (acc : List (Nat × VarTy)) (v, c) =>
        if acc.any (fun (c', _) => c' == c) then acc
        else (c, tyCtx v) :: acc
      ) ([] : List (Nat × VarTy))
      -- Map color indices to register names, using type-based prefixes:
      --   __ir{N} for int, __br{N} for bool, __fr{N} for float.
      -- This naming convention lets the type context derive types from names.
      let intBoolMap := intBoolColoring.filterMap fun (v, c) =>
        if h : c < intRegNums.size then
          let pfx := if tyCtx v == .bool then "br" else "ir"
          some (v, s!"{pfx}{intRegNums[c]}")
        else none
      let floatMap := floatColoring.filterMap fun (v, c) =>
        if h : c < floatRegNums.size then some (v, s!"fr{floatRegNums[c]}")
        else none
      intBoolMap ++ floatMap

-- ============================================================
-- § 5. TAC-level renaming
-- ============================================================

/-- Map a variable name through the coloring.
    Colored variables get register-prefixed names (__ir{N}, __br{N}, or __fr{N});
    spilled variables keep their original names. -/
def renameVar (coloring : List (Var × String)) (v : Var) : Var :=
  match coloring.find? (fun (x, _) => x == v) with
  | some (_, reg) => s!"__{reg}"
  | none => v

/-- Rename all variables in a TAC instruction using the coloring. -/
def renameInstr (coloring : List (Var × String)) (instr : TAC) : TAC :=
  let r := renameVar coloring
  match instr with
  | .const x v       => .const (r x) v
  | .copy x y        => .copy (r x) (r y)
  | .binop x op y z  => .binop (r x) op (r y) (r z)
  | .boolop x be     => .boolop (r x) (renameBoolExpr coloring be)
  | .arrLoad x arr idx ty => .arrLoad (r x) arr (r idx) ty
  | .arrStore arr idx val ty => .arrStore arr (r idx) (r val) ty
  | .fbinop x op y z => .fbinop (r x) op (r y) (r z)
  | .intToFloat x y  => .intToFloat (r x) (r y)
  | .floatToInt x y  => .floatToInt (r x) (r y)
  | .floatUnary x op y => .floatUnary (r x) op (r y)
  | .fternop x op a b c => .fternop (r x) op (r a) (r b) (r c)
  | .goto l          => .goto l
  | .ifgoto be l     => .ifgoto (renameBoolExpr coloring be) l
  | .halt            => .halt
  | .print fmt vs    => .print fmt (vs.map r)
  | .printInt v      => .printInt (r v)
  | .printBool v     => .printBool (r v)
  | .printFloat v    => .printFloat (r v)
  | .printString lit => .printString lit
where
  renameBoolExpr (coloring : List (Var × String)) (be : BoolExpr) : BoolExpr :=
    let r := renameVar coloring
    match be with
    | .lit b       => .lit b
    | .bvar v      => .bvar (r v)
    | .cmp op a b  => .cmp op (renameExprVars r a) (renameExprVars r b)
    | .not e       => .not (renameBoolExpr coloring e)
    | .fcmp op a b => .fcmp op (renameExprVars r a) (renameExprVars r b)
    | .bexpr e     => .bexpr (renameExprVars r e)
  renameExprVars (r : Var → Var) : Expr → Expr
    | .var v  => .var (r v)
    | .lit n  => .lit n
    | .flit f => .flit f
    | .blit b => .blit b
    | e       => e  -- complex Expr: shouldn't occur in BoolExpr operands

/-- Generate copy-back instructions for observable variables that were renamed.
    Returns `copy origName regName` for each observable that has a coloring entry. -/
def copyBackInstrs (coloring : List (Var × String)) (observables : List Var) : List TAC :=
  observables.filterMap fun v =>
    match coloring.find? (fun (x, _) => x == v) with
    | some (_, reg) => some (.copy v (s!"__{reg}"))  -- copy r __ir3
    | none => none

/-- Compute the PC offset array: for each original PC, how many extra instructions
    were inserted before it due to halt expansion. -/
def computePCMap (prog : Prog) (copyBacks : List TAC) : Array Nat :=
  let numCopyBacks := copyBacks.length
  let arr := (List.range prog.size).foldl (fun (acc : Array Nat × Nat) origPC =>
    let (arr, offset) := acc
    let arr' := arr.push (origPC + offset)
    match prog[origPC]? with
    | some .halt => (arr', offset + numCopyBacks)
    | _ => (arr', offset)
  ) (#[], 0)
  arr.1

/-- Build the renamed program from the coloring with copy-back before halts.
    ALL variables are renamed (including observables), but copy-back instructions
    are inserted before each halt to restore observable values to their original names.
    PCs are adjusted for the inserted instructions. -/
def renameProg (prog : Prog) (coloring : List (Var × String)) : Prog :=
  let copyBacks := copyBackInstrs coloring prog.observable
  let pcMap := computePCMap prog copyBacks
  let mapPC (origPC : Nat) : Nat := pcMap.getD origPC origPC
  let newCode := (List.range prog.size).foldl (fun acc origPC =>
    let instr := prog.code.getD origPC .halt
    let renamed := renameInstr coloring instr
    -- Adjust goto/ifgoto targets
    let adjusted : TAC := match renamed with
      | .goto l => .goto (mapPC l)
      | .ifgoto be l => .ifgoto be (mapPC l)
      | other => other
    match adjusted with
    | TAC.halt =>
      -- Insert copy-backs before halt
      acc ++ copyBacks ++ [TAC.halt]
    | i => acc ++ [i]
  ) ([] : List TAC)
  { code := newCode.toArray
    observable := prog.observable
    arrayDecls := prog.arrayDecls }

-- ============================================================
-- § 6. Expression relation computation (forward worklist)
-- ============================================================

/-- Compute expression relations on the ORIG program.
    At each orig PC, the relation tracks `(.var origName, .var regName)` pairs.
    We use the orig instruction to determine the defined variable, then look up
    its register name in the coloring. This correctly handles register reuse
    (e.g., x3 used for a, d, e, r at different PCs). -/
partial def computeOrigRels (prog : Prog) (coloring : List (Var × String))
    : Array EExprRel :=
  if prog.size == 0 then #[]
  else
    let init := (Array.replicate prog.size (none : Option EExprRel)).set! 0 (some ([] : EExprRel))
    let result := relLoop prog coloring init (0 :: ([] : List Nat))
    result.map fun
      | some rel => rel
      | none => ([] : EExprRel)
where
  relMerge (a b : EExprRel) : EExprRel :=
    a.filter fun (eo, et) => b.any fun (eo', et') => eo == eo' && et == et'
  relBeq (a b : EExprRel) : Bool :=
    a.length == b.length && a.all fun (eo, et) => b.any fun (eo', et') => eo == eo' && et == et'
  relTransfer (rel : EExprRel) (_pc : Nat) (instr : TAC) (coloring : List (Var × String)) : EExprRel :=
    match DAEOpt.instrDef instr with
    | some origVar =>
      let regVar := renameVar coloring origVar
      -- Drop old entries whose trans side is this register (handles register reuse)
      let rel' := rel.filter fun (_, et) => et != .var regVar
      if regVar != origVar then
        -- Colored: add (.var origName, .var regName)
        (.var origVar, .var regVar) :: rel'
      else
        -- Identity: add (.var v, .var v) so free-variable coverage holds
        (.var origVar, .var origVar) :: rel'
    | none => rel
  relLoop (prog : Prog) (coloring : List (Var × String))
      (rels : Array (Option EExprRel)) (worklist : List Nat) : Array (Option EExprRel) :=
    match worklist with
    | [] => rels
    | pc :: rest =>
      match prog[pc]?, rels[pc]? with
      | some instr, some (some rel) =>
        let out := relTransfer rel pc instr coloring
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
        relLoop prog coloring rels' newWork
      | _, _ => relLoop prog coloring rels rest

/-- Map orig-PC-indexed rels to trans-PC-indexed rels.
    Non-copy-back PCs get the rel from the corresponding orig PC.
    Copy-back groups (before each halt) are processed sequentially:
    each copy-back `copy origName regName` removes the `(*, .var regName)`
    entry from the flowing relation. -/
private def isCB (trans : Prog) (origPCMap : Array Nat) (tpc : Nat) : Bool :=
  let opc := origPCMap.getD tpc tpc
  let nextOpc := origPCMap.getD (tpc + 1) (tpc + 1)
  opc == nextOpc && match trans[tpc]? with | some (.copy _ _) => true | _ => false

def mapRelsToTrans (origRels : Array EExprRel) (origPCMap : Array Nat)
    (trans : Prog) : Array EExprRel :=
  -- First pass: assign base rels from orig
  let baseRels : Array EExprRel := ((List.range trans.size).map fun tpc =>
    let opc := origPCMap.getD tpc tpc
    origRels.getD opc ([] : EExprRel)).toArray
  -- Second pass: for copy-back sequences, flow the rel forward
  -- After each `copy dest src`, replace the rename pair (orig, .var src) with
  -- an identity pair (.var dest, .var dest) since dest now holds orig's value.
  (List.range trans.size).foldl (fun (rels : Array EExprRel) tpc =>
    let curIsCB := isCB trans origPCMap tpc
    let prevIsCB := tpc > 0 && isCB trans origPCMap (tpc - 1)
    if curIsCB && prevIsCB then
      -- Continuing copy-back sequence: apply previous copy's effect
      match trans[tpc - 1]? with
      | some (.copy dest src) =>
        let prevRel := rels.getD (tpc - 1) ([] : EExprRel)
        let filtered := prevRel.filter fun (_, et) => et != Expr.var src
        rels.set! tpc ((.var dest, .var dest) :: filtered)
      | _ => rels
    else if !curIsCB && prevIsCB then
      -- Halt right after copy-backs: apply final copy's effect
      match trans[tpc - 1]? with
      | some (.copy dest src) =>
        let prevRel := rels.getD (tpc - 1) ([] : EExprRel)
        let filtered := prevRel.filter fun (_, et) => et != Expr.var src
        rels.set! tpc ((.var dest, .var dest) :: filtered)
      | _ => rels
    else
      rels
  ) baseRels

-- ============================================================
-- § 7. Certificate generation
-- ============================================================

/-- Build the reverse PC map: for each trans PC, what is the corresponding orig PC.
    Copy-back instructions before a halt share the halt's orig PC. -/
def buildRevPCMap (prog : Prog) (pcMap : Array Nat) (transSize : Nat) : Array Nat :=
  let arr := Array.replicate transSize 0
  -- For each orig PC, fill its trans PC and any copy-back PCs before the next orig PC
  (List.range prog.size).foldl (fun arr origPC =>
    let transPC := pcMap.getD origPC origPC
    -- Fill from transPC to the next orig PC's transPC (or transSize)
    let nextTransPC := if origPC + 1 < pcMap.size then pcMap.getD (origPC + 1) transSize
                       else transSize
    (List.range (nextTransPC - transPC)).foldl (fun arr offset =>
      arr.set! (transPC + offset) origPC
    ) arr
  ) arr

/-- Build instrCerts for RegAlloc with PC mapping from orig to trans.
    Copy-back instructions use zero-step orig paths (origLabels = []). -/
def buildRegAllocInstrCerts (trans : Prog) (rels : Array EExprRel)
    (origPCMap : Array Nat) : Array EInstrCert :=
  let arr := (List.range trans.size).map fun i =>
    let rel := rels.getD i ([] : EExprRel)
    let relNext (target : Nat) : EExprRel := rels.getD target ([] : EExprRel)
    let pc_orig := origPCMap.getD i i
    match trans[i]? with
    | some .halt =>
      { pc_orig := pc_orig, rel := rel, transitions := ([] : List ETransCorr) }
    | some (.goto l) =>
      let origTarget := origPCMap.getD l l
      { pc_orig := pc_orig, rel := rel,
        transitions := [{ origLabels := [origTarget], rel := rel, rel_next := relNext l }] }
    | some (.ifgoto _ l) =>
      let origTarget := origPCMap.getD l l
      let origFall := origPCMap.getD (i + 1) (i + 1)
      { pc_orig := pc_orig, rel := rel,
        transitions := [{ origLabels := [origTarget], rel := rel, rel_next := relNext l },
                        { origLabels := [origFall], rel := rel, rel_next := relNext (i + 1) }] }
    | some _ =>
      if isCB trans origPCMap i then
        -- Copy-back: zero-step orig path (empty labels, stay at same orig PC)
        { pc_orig := pc_orig, rel := rel,
          transitions := [{ origLabels := [], rel := rel, rel_next := relNext (i + 1) }] }
      else
        let origNext := origPCMap.getD (i + 1) (i + 1)
        { pc_orig := pc_orig, rel := rel,
          transitions := [{ origLabels := [origNext], rel := rel, rel_next := relNext (i + 1) }] }
    | none => default
  arr.toArray

-- ============================================================
-- § 8. Main entry point
-- ============================================================

/-- Register allocation as an optimization pass. Renames TAC variables to
    register names (__ir{N}/__br{N}/__fr{N}) and produces a certificate with
    expression relations tracking the renaming. -/
def optimize (tyCtx : TyCtx) (prog : Prog) : ECertificate :=
  let coloring := computeColoring tyCtx prog
  let trans := renameProg prog coloring
  let copyBacks := copyBackInstrs coloring prog.observable
  let pcMap := computePCMap prog copyBacks
  let origPCMap := buildRevPCMap prog pcMap trans.size
  let origRels := computeOrigRels prog coloring
  let rels := mapRelsToTrans origRels origPCMap trans
  let consts_orig := ConstPropOpt.analyze prog
  let inv_orig := ConstPropOpt.buildInvariants consts_orig
  let consts_trans := ConstPropOpt.analyze trans
  let inv_trans := ConstPropOpt.buildInvariants consts_trans
  let instrCerts := buildRegAllocInstrCerts trans rels origPCMap
  let haltCerts := buildHaltCerts instrCerts trans
  -- Measures: copy-back PCs count down to 0 at halt
  -- For a group of N copy-backs before halt, measures are N, N-1, ..., 1, 0
  let measure := (List.range trans.size).map fun tpc =>
    if isCB trans origPCMap tpc then
      -- Count how many copy-backs remain after this one (including halt)
      let remaining := (List.range (trans.size - tpc)).filter fun offset =>
        isCB trans origPCMap (tpc + offset)
      remaining.length
    else 0
  { orig := prog
    trans := trans
    tyCtx := tyCtx
    inv_orig := inv_orig
    inv_trans := inv_trans
    instrCerts := instrCerts
    haltCerts := haltCerts
    measure := measure.toArray }

end RegAllocOpt
