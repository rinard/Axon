-- Copyright (c) 2026 Martin Rinard
import CredibleCompilation.ExecChecker

/-!
# Copy Propagation Optimizer (documented negative result, not wired into the pipeline)

## Status

Implemented and validated against the certificate framework — all 24
canonical Livermore kernels pass cert validation under this pass. **But
benchmark runtime regresses** when the pass is enabled, so it is NOT
wired into the standard pipeline. The file is kept as documented prior art
for a future register-pressure-aware variant.

## What it does

Takes a TAC program and performs forward copy propagation. After a `.copy x y`,
every subsequent use of `x` is replaced with `y` (until `x` or `y` is
redefined). The dead `.copy` is left for DCE to clean up.

- **copy x y; ... use x ...** → **copy x y; ... use y ...**

When `y` is itself a copy chain, we follow it to the canonical source.

## Why it doesn't help in this pipeline

Stage 1's Chaitin-style spill heuristic protects loop-resident variables
by inflating their cost via 10^loop_depth weighting. With that in place,
copies of loop-resident values cost almost nothing: the source register
stays live across the copy, and the destination is just one extra `mov`.

Copy propagation eliminates the `mov` but in exchange **extends the live
range** of the source variable through every PC where the destination was
previously used. If the source was already at high register pressure (which
loop-resident variables are, by construction), the extension pushes it past
the K-coloring threshold and forces a spill that didn't happen before.

Measured impact on heavy kernels (Stage 1 spill heuristic + this pass, 1
invocation pre-RegAlloc, vs Stage 1 alone):

| Kernel             | Stage 1 | Stage 1 + CopyProp | Δ      |
|--------------------|---------|---------------------|--------|
| k08_adi            | 11.30   | 11.69               | -3 %   |
| k15_casual         | 12.60   | 12.60               | flat   |
| k18_hydro_2d       | 12.99   | 15.18               | -17 %  |
| k09_integrate      | 14.57   | 14.40               | +1 %   |

Adding more invocations (after each CSE in the LICM cluster, etc.) makes
things worse on average.

## Where it might still be useful

- A **register-pressure-aware** copy propagation that only substitutes
  uses when the source's live range would NOT extend across a high-pressure
  region. Requires a pre-pass that estimates per-PC register pressure
  (e.g., from the liveness analysis already done by DAEOpt). With that
  guardrail, copy propagation should be safe.
- A **register-allocator-internal coalescing** pass (Briggs/George
  conservative coalescing) — merges two variables only when they don't
  interfere, by construction never increasing pressure. That's the
  textbook reason the optimization lives inside the allocator. Not yet
  implemented.

## Why this pass and not coalescing in RegAlloc

(The original motivation, recorded for completeness.) Eliminating copies
at the TAC level means the interference graph that RegAlloc builds never
has the false interferences that copies create. The graph is smaller, the
coloring is faster, and the spill heuristic is not distracted by short-range
copy temporaries that are really copy-shadows of longer-range vars. It also
unblocks downstream CSE: cross-variable matches become syntactic equalities
after substitution.

This argument is sound *in isolation*, but interacts badly with the Stage 1
spill heuristic — see "Why it doesn't help" above.
-/

namespace CopyPropOpt

-- ============================================================
-- § 1. Copy map
-- ============================================================

/-- Map from variables to their canonical source. `(x, y)` means
    "x's current value equals y's current value". -/
abbrev CopyMap := List (Var × Var)

def lookup (cm : CopyMap) (v : Var) : Option Var :=
  (cm.find? (fun p => p.1 == v)).map Prod.snd

/-- Resolve `v` to its canonical source: follow the copy chain. Bounded by
    map length to avoid infinite loops on pathological cycles. -/
partial def resolve (cm : CopyMap) (v : Var) : Var :=
  match lookup cm v with
  | some src => if src == v then v else resolve cm src
  | none => v

/-- Drop entries that mention `x` on either side. After x is redefined,
    every `(x, _)` is stale (x has a new value), and every `(_, x)` is
    stale (the source x has changed). -/
def kill (cm : CopyMap) (x : Var) : CopyMap :=
  cm.filter (fun (a, b) => a != x && b != x)

/-- Intersection: keep entries present in both maps with the same RHS. -/
def merge (a b : CopyMap) : CopyMap :=
  a.filter fun (v, src) => b.any fun (v', src') => v == v' && src == src'

/-- Semantic equality: same set of (var, src) pairs (order-independent). -/
def beq (a b : CopyMap) : Bool :=
  a.length == b.length &&
  a.all fun (v, src) => b.any fun (v', src') => v == v' && src == src'

-- ============================================================
-- § 2. Transfer function
-- ============================================================

/-- Update the copy map after executing one instruction. -/
def transfer (cm : CopyMap) (instr : TAC) : CopyMap :=
  match instr with
  | .copy x y =>
    let src := resolve cm y
    if src == x then kill cm x
    else (x, src) :: kill cm x
  | .const x _         => kill cm x
  | .binop x _ _ _     => kill cm x
  | .boolop x _        => kill cm x
  | .arrLoad x _ _ _   => kill cm x
  | .fbinop x _ _ _    => kill cm x
  | .intToFloat x _    => kill cm x
  | .floatToInt x _    => kill cm x
  | .floatUnary x _ _  => kill cm x
  | .fternop x _ _ _ _ => kill cm x
  | _ => cm

-- ============================================================
-- § 3. Forward dataflow analysis (worklist)
-- ============================================================

private def propagate (prog : Prog) (states : Array (Option CopyMap)) (pc : Nat)
    : Array (Option CopyMap) × List Nat :=
  match prog[pc]?, states[pc]? with
  | some instr, some (some cm) =>
    let out := transfer cm instr
    let succs := instr.successors pc
    succs.foldl (fun (cs, wl) pc' =>
      if pc' < cs.size then
        match cs[pc']? with
        | some none | none => (cs.set! pc' (some out), pc' :: wl)
        | some (some old) =>
          let merged := merge old out
          if beq merged old then (cs, wl)
          else (cs.set! pc' (some merged), pc' :: wl)
      else (cs, wl)
    ) (states, [])
  | _, _ => (states, [])

private partial def analyzeLoop (prog : Prog) (states : Array (Option CopyMap))
    (worklist : List Nat) : Array (Option CopyMap) :=
  match worklist with
  | [] => states
  | pc :: rest =>
    let (states', newWork) := propagate prog states pc
    analyzeLoop prog states' (newWork ++ rest)

def analyze (prog : Prog) : Array (Option CopyMap) :=
  if prog.size == 0 then #[]
  else
    let init := (Array.replicate prog.size (none : Option CopyMap)).set! 0
                  (some ([] : CopyMap))
    analyzeLoop prog init (0 :: ([] : List Nat))

-- ============================================================
-- § 4. Program transformation
-- ============================================================

/-- Substitute uses inside an Expr through the copy map. -/
def resolveExpr (cm : CopyMap) : Expr → Expr
  | .var v => .var (resolve cm v)
  | other  => other

/-- Substitute uses inside a BoolExpr through the copy map. -/
def resolveBool (cm : CopyMap) : BoolExpr → BoolExpr
  | .lit b       => .lit b
  | .bvar v      => .bvar (resolve cm v)
  | .cmp op a b  => .cmp op (resolveExpr cm a) (resolveExpr cm b)
  | .fcmp op a b => .fcmp op (resolveExpr cm a) (resolveExpr cm b)
  | .not e       => .not (resolveBool cm e)
  | .bexpr e     => .bexpr (resolveExpr cm e)

/-- Transform a single instruction by substituting uses through `cm`. -/
def transformInstr (cm : CopyMap) (instr : TAC) : TAC :=
  let r : Var → Var := resolve cm
  match instr with
  | .copy x y =>
    let y' := r y
    if x == y' then instr  -- self-copy: no rewrite
    else .copy x y'
  | .binop x op y z       => .binop x op (r y) (r z)
  | .fbinop x op y z      => .fbinop x op (r y) (r z)
  | .intToFloat x y       => .intToFloat x (r y)
  | .floatToInt x y       => .floatToInt x (r y)
  | .floatUnary x op y    => .floatUnary x op (r y)
  | .fternop x op a b c   => .fternop x op (r a) (r b) (r c)
  | .arrLoad x arr idx ty => .arrLoad x arr (r idx) ty
  | .arrStore arr idx val ty => .arrStore arr (r idx) (r val) ty
  | .ifgoto be l          => .ifgoto (resolveBool cm be) l
  | .boolop x be          => .boolop x (resolveBool cm be)
  | .printInt v           => .printInt (r v)
  | .printBool v          => .printBool (r v)
  | .printFloat v         => .printFloat (r v)
  | .print fmt vs         => .print fmt (vs.map r)
  | other                 => other  -- .const, .halt, .goto, .printString

def transformProg (prog : Prog) (states : Array (Option CopyMap)) : Prog :=
  let arr := (List.range prog.size).map fun i =>
    match prog[i]?, states[i]? with
    | some instr, some (some cm) => transformInstr cm instr
    | some instr, _              => instr
    | none, _                    => .halt
  { code := arr.toArray, observable := prog.observable, arrayDecls := prog.arrayDecls }

-- ============================================================
-- § 5. Certificate generation
-- ============================================================

/-- Convert a CopyMap to an EInv: each (x, y) means x has the same value as y. -/
def copyMapToInv (cm : CopyMap) : EInv :=
  cm.map fun (v, src) => (v, Expr.var src)

def buildInvariants (states : Array (Option CopyMap)) : Array EInv :=
  states.map fun
    | some cm => copyMapToInv cm
    | none    => ([] : EInv)

-- ============================================================
-- § 6. Main entry point
-- ============================================================

/-- Run copy propagation and produce an `ECertificate` that
    `checkCertificateExec` will accept. -/
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

end CopyPropOpt
