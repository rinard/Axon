-- Copyright (c) 2026 Martin Rinard
import CredibleCompilation.ExecChecker

/-!
# Common Subexpression Elimination Optimizer

Takes a TAC program and a list of observable variables, performs forward
available-expression analysis, and produces an `ECertificate` that the
executable checker can verify.

## What it optimizes

**binop x op y z** where the expression `y op z` was already computed into
some variable `w` (and neither `w`, `y`, nor `z` has been reassigned since)
→ **copy x w**

This includes **cross-constant matching**: `k + _t1` and `k + _t2` are
recognized as the same expression when both `_t1` and `_t2` are known
constants with the same value.  This is common because `compileExpr`
allocates a fresh temp for each literal occurrence.

## Analysis state

The analysis tracks two structures per PC:

- **AvailSet** — available expressions (result := lhs op rhs) with a
  fully-expanded `invExpr` used for the certificate invariant.
- **ConstMap** — known constant bindings (var → value) from `const` instructions.

Matching uses `expandVarFull` / `expandExprConsts` to substitute constants
into both the target expression and stored `invExpr`, so semantically
equivalent expressions compare equal regardless of which temp holds a constant.

## Invariant strategy

The certificate invariant at each PC contains atoms `(w, expanded_expr)` for
each available expression, **plus** atoms `(v, .lit n)` for each known constant.
The `invExpr` stored in `AvailEntry` uses raw `.var` references (identity
expansion), and the checker's `simplifyDeep` recurses through `.var` lookups
to resolve chains through the invariant at verification time.
-/

namespace CSEOpt

-- ============================================================
-- § 1. Available expressions
-- ============================================================

/-- Tag distinguishing integer vs float binary operations for CSE. -/
inductive AvailOp where
  | int   : BinOp → AvailOp
  | float : FloatBinOp → AvailOp
  deriving Repr, BEq

/-- An available expression entry: `result := lhs op rhs`.
    `invExpr` is the fully-expanded form for the certificate invariant. -/
structure AvailEntry where
  op      : AvailOp
  lhs     : Var
  rhs     : Var
  result  : Var
  invExpr : Expr
  deriving Repr

instance : BEq AvailEntry where
  beq a b := a.op == b.op && a.lhs == b.lhs && a.rhs == b.rhs &&
             a.result == b.result && a.invExpr == b.invExpr

abbrev AvailSet := List AvailEntry

/-- Map from variables to their known constant values. -/
abbrev ConstMap := List (Var × Value)

/-- Kill a variable from the constant map. -/
def constKill (cm : ConstMap) (x : Var) : ConstMap :=
  cm.filter fun (v, _) => v != x

/-- Intersection of two constant maps: keep entries present in both. -/
def constMerge (a b : ConstMap) : ConstMap :=
  a.filter fun (v, val) => b.any fun (v', val') => v == v' && val == val'

/-- Semantic equality for constant maps (order-independent). -/
def constBeq (a b : ConstMap) : Bool :=
  a.length == b.length && a.all fun (v, val) => b.any fun (v', val') => v == v' && val == val'

/-- Does the expression reference variable `x`? -/
def exprRefsVar (e : Expr) (x : Var) : Bool :=
  match e with
  | .var v     => v == x
  | .bin _ a b => exprRefsVar a x || exprRefsVar b x
  | .fbin _ a b => exprRefsVar a x || exprRefsVar b x
  | .intToFloat a => exprRefsVar a x
  | .floatToInt a => exprRefsVar a x
  | .floatUnary _ a => exprRefsVar a x
  | .lit _     => false
  | .blit _    => false
  | .flit _    => false
  | _          => false

/-- Kill all entries that reference variable `x` as operand, result,
    or anywhere in the expanded invariant expression. -/
def killVar (avail : AvailSet) (x : Var) : AvailSet :=
  avail.filter fun e => !(e.lhs == x || e.rhs == x || e.result == x || exprRefsVar e.invExpr x)

/-- Expand a variable through the available set only (for certificate invariants).
    Does NOT expand constants — the checker can verify `.var` references directly. -/
def expandVarCert (_avail : AvailSet) (v : Var) : Expr := .var v

/-- Substitute known constants into an expression (for matching only). -/
def expandExprConsts (cm : ConstMap) : Expr → Expr
  | .var v =>
    match cm.find? (fun (v', _) => v == v') with
    | some (_, .int n)   => .lit n
    | some (_, .float f) => .flit f
    | some (_, .bool b)  => .blit b
    | none               => .var v
  | .bin op a b   => .bin op (expandExprConsts cm a) (expandExprConsts cm b)
  | .fbin op a b  => .fbin op (expandExprConsts cm a) (expandExprConsts cm b)
  | e => e

/-- Expand a variable through the available set and constant map (for matching).
    Returns a fully-expanded expression with constants substituted. -/
def expandVarFull (avail : AvailSet) (cm : ConstMap) (v : Var) : Expr :=
  match avail.find? (fun e => e.result == v) with
  | some e => expandExprConsts cm e.invExpr
  | none   =>
    match cm.find? (fun (v', _) => v == v') with
    | some (_, .int n)   => .lit n
    | some (_, .float f) => .flit f
    | some (_, .bool b)  => .blit b
    | none => .var v

/-- Expand every variable leaf of an expression one level through the available
    set + constant map (mapping each `result` var to its `invExpr`, constants to
    their values). Makes a stored entry's `invExpr` comparable to a freshly
    `expandVarFull`-expanded target, so a NESTED redundancy matches — e.g. the entry
    `u = __t1 * __t2` canonicalizes to `(a+i)*(b+i)`, the same form a later
    `__t3 * __t4` (with `__t3 = a+i`, `__t4 = b+i`) expands to. -/
def expandExprViaAvail (avail : AvailSet) (cm : ConstMap) : Expr → Expr
  | .var v       => expandVarFull avail cm v
  | .bin op a b  => .bin op (expandExprViaAvail avail cm a) (expandExprViaAvail avail cm b)
  | .fbin op a b => .fbin op (expandExprViaAvail avail cm a) (expandExprViaAvail avail cm b)
  | e            => e

/-- Find an available computation matching the expanded form of `lhs op rhs`.
    Uses constant + available-set expansion so that e.g. `k + _t1` and `k + _t2`
    match when both `_t1`/`_t2` are the same constant, AND a nested redundancy like
    `(a+i)*(b+i)` recomputed via fresh temps matches the available product. -/
def findAvail (avail : AvailSet) (cm : ConstMap) (op : AvailOp) (lhs rhs : Var) : Option AvailEntry :=
  let eLhs := expandVarFull avail cm lhs
  let eRhs := expandVarFull avail cm rhs
  let targetExpr := match op with
    | .int o => Expr.bin o eLhs eRhs
    | .float o => match o, eLhs with
      | .fadd, .fbin .fmul _ _ => Expr.fbin .fadd eRhs eLhs
      | _, _ => Expr.fbin o eLhs eRhs
  avail.find? fun e =>
    e.op == op && expandExprViaAvail avail cm e.invExpr == targetExpr

/-- Intersection: keep entries present in both sets (all fields equal). -/
def availMerge (a b : AvailSet) : AvailSet :=
  a.filter fun e => b.any (· == e)

/-- Semantic equality (order-independent). -/
def availBeq (a b : AvailSet) : Bool :=
  a.length == b.length && a.all fun e => b.any (· == e)

/-- Combined CSE analysis state: available expressions + known constants. -/
abbrev CSEState := AvailSet × ConstMap

-- ============================================================
-- § 2. Transfer function
-- ============================================================

/-- Update available expressions and constant map after executing one instruction. -/
def transfer (st : CSEState) (instr : TAC) : CSEState :=
  let (avail, cm) := st
  match instr with
  | .const x v =>
    (killVar avail x, (x, v) :: constKill cm x)
  | .copy x _  => (killVar avail x, constKill cm x)
  | .binop x op y z =>
    let avail' := killVar avail x
    let cm' := constKill cm x
    if x == y || x == z then (avail', cm')
    else
      let invExpr := Expr.bin op (expandVarCert avail' y) (expandVarCert avail' z)
      ({ op := .int op, lhs := y, rhs := z, result := x, invExpr } :: avail', cm')
  | .fbinop x fop y z =>
    let avail' := killVar avail x
    let cm' := constKill cm x
    if x == y || x == z then (avail', cm')
    else
      let a' := expandVarCert avail' y
      let b' := expandVarCert avail' z
      -- Normalize fadd with fmul on left: swap to match simplify's normalization
      let invExpr := match fop, a' with
        | .fadd, .fbin .fmul _ _ => Expr.fbin .fadd b' a'
        | _, _ => Expr.fbin fop a' b'
      ({ op := .float fop, lhs := y, rhs := z, result := x, invExpr } :: avail', cm')
  | .boolop x _        => (killVar avail x, constKill cm x)
  | .arrLoad x _ _ _   => (killVar avail x, constKill cm x)
  | .intToFloat x _    => (killVar avail x, constKill cm x)
  | .floatToInt x _    => (killVar avail x, constKill cm x)
  | .floatUnary x _ _  => (killVar avail x, constKill cm x)
  | .fternop x _ _ _ _ => (killVar avail x, constKill cm x)
  | _ => (avail, cm)

-- ============================================================
-- § 3. Forward analysis (worklist)
-- ============================================================

/-- One propagate step. `inWl[pc']` tracks whether pc' is already in the
    worklist; we skip re-adding it. Equality-after-merge uses a length compare:
    `availMerge`/`constMerge` produce a subset of `oldAv`/`oldCm` (filter), so
    equal length implies equal as a list — saves an O(n²) per-edge check. -/
private def propagate (prog : Prog) (states : Array (Option CSEState))
    (inWl : Array Bool) (pc : Nat) :
    Array (Option CSEState) × Array Bool × List Nat :=
  let inWl := inWl.set! pc false
  match prog[pc]?, states[pc]? with
  | some instr, some (some st) =>
    let out := transfer st instr
    let succs := instr.successors pc
    succs.foldl (fun (arr, iw, wl) pc' =>
      if pc' < arr.size then
        match arr[pc']? with
        | some none | none =>
          let arr' := arr.set! pc' (some out)
          if iw[pc']? == some true then (arr', iw, wl)
          else (arr', iw.set! pc' true, pc' :: wl)
        | some (some (oldAv, oldCm)) =>
          let (outAv, outCm) := out
          let mergedAv := availMerge oldAv outAv
          let mergedCm := constMerge oldCm outCm
          if mergedAv.length == oldAv.length && mergedCm.length == oldCm.length
          then (arr, iw, wl)
          else
            let arr' := arr.set! pc' (some (mergedAv, mergedCm))
            if iw[pc']? == some true then (arr', iw, wl)
            else (arr', iw.set! pc' true, pc' :: wl)
      else (arr, iw, wl)
    ) (states, inWl, [])
  | _, _ => (states, inWl, [])

/-- Worklist driver. LIFO order (`newWork ++ rest`) keeps each pop O(1) instead
    of paying O(|rest|) per `++`, and tends to converge dataflow in fewer
    iterations on natural CFGs. -/
private partial def analyzeLoop (prog : Prog) (states : Array (Option CSEState))
    (inWl : Array Bool) (worklist : List Nat) : Array (Option CSEState) :=
  match worklist with
  | [] => states
  | pc :: rest =>
    let (states', inWl', newWork) := propagate prog states inWl pc
    analyzeLoop prog states' inWl' (newWork ++ rest)

/-- Forward available-expression analysis.
    Returns `Option CSEState` per PC (`none` = unreachable).

    Two phases, mirroring `ConstProp.analyze`. Phase 1 is the usual reachable
    forward analysis from PC 0. Phase 2 seeds every still-unreachable PC with the
    `top` state (empty available set, empty const map) and re-propagates. A merge
    fed by a physically-dead edge must intersect with that edge's contribution;
    if phase 1 never visited the dead predecessor, the merge keeps available
    expressions that are not in fact available on that edge, and the certificate's
    `invariants_preserved` check fails on the physical dead edge. Phase 2
    propagates the dead edge too, so the merge correctly drops those expressions.
    Correctness-safe: it only removes (never adds) available expressions, so CSE
    becomes slightly less aggressive at such merges but every cert stays valid. -/
def analyze (prog : Prog) : Array (Option CSEState) :=
  if prog.size == 0 then #[]
  else
    let init := (Array.replicate prog.size (none : Option CSEState)).set! 0 (some ([], []))
    let inWl := (Array.replicate prog.size false).set! 0 true
    let reached := analyzeLoop prog init inWl (0 :: [])
    let deadPCs := (List.range prog.size).filter fun pc =>
      match reached[pc]? with | some none => true | _ => false
    let seeded := deadPCs.foldl (fun arr pc => arr.set! pc (some ([], []))) reached
    let inWl2 := deadPCs.foldl (fun arr pc => arr.set! pc true)
      (Array.replicate prog.size false)
    analyzeLoop prog seeded inWl2 deadPCs

-- ============================================================
-- § 4. Transformation
-- ============================================================

/-- Transform a single instruction using available expressions at its PC. -/
def transformInstr (st : CSEState) (instr : TAC) : TAC :=
  let (avail, cm) := st
  match instr with
  | .binop x op y z =>
    match findAvail avail cm (.int op) y z with
    | some e => if x == e.result then instr else .copy x e.result
    | none   => instr
  | .fbinop x fop y z =>
    match findAvail avail cm (.float fop) y z with
    | some e => if x == e.result then instr else .copy x e.result
    | none   => instr
  | other => other

/-- Transform the entire program. -/
def transformProg (prog : Prog) (states : Array (Option CSEState)) : Prog :=
  let arr := (List.range prog.size).map fun i =>
    match prog[i]?, states[i]? with
    | some instr, some (some st) => transformInstr st instr
    | some instr, _              => instr
    | none, _                    => .halt
  { code := arr.toArray, observable := prog.observable, arrayDecls := prog.arrayDecls }

-- ============================================================
-- § 5. Certificate generation
-- ============================================================

/-- Convert a CSE state to an EInv (invariant).
    Includes both available expressions and known constant bindings,
    so the checker can verify CSE across different temps for the same constant.
    The checker's `simplifyDeep` recurses through `.var` lookup results,
    so avail entries no longer need pre-simplification. -/
def stateToInv (st : CSEState) : EInv :=
  let (avail, cm) := st
  let constInv : EInv := cm.map fun (v, val) => match val with
    | .int n   => (v, Expr.lit n)
    | .float f => (v, Expr.flit f)
    | .bool b  => (v, Expr.blit b)
  let availInv := avail.map fun e => (e.result, e.invExpr)
  availInv ++ constInv

/-- Build invariant arrays from the analysis result. -/
def buildInvariants (states : Array (Option CSEState)) : Array EInv :=
  states.map fun
    | some st => stateToInv st
    | none    => []


-- ============================================================
-- § 6. Main entry point
-- ============================================================

/-- Run CSE on `prog` and produce a certified transformation.
    The result is an `ECertificate` that `checkCertificateExec` will accept. -/
def optimize (tyCtx : TyCtx) (prog : Prog) : ECertificate :=
  let states := analyze prog
  let trans := transformProg prog states
  let inv := buildInvariants states
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

end CSEOpt
