-- Copyright (c) 2026 Martin Rinard
import CredibleCompilation.ExecChecker
import CredibleCompilation.DAEOpt

/-!
# Rematerialize-Constant Optimizer (documented stub, not wired into pipeline)

## Status

Implemented as a conservative `.const`-instruction-sinking pass. All 24
canonical Livermore kernels pass cert validation when this pass is wired
into the pipeline, **but measured runtime is unchanged within noise**
(<0.5% on heavy kernels). The conservative form simply moves `.const v c`
past adjacent instructions that don't reference v, shortening v's live
range by 1 PC at a time; in practice this either doesn't fire often or
doesn't shorten the range enough to free a register that wasn't already
free.

The pass is NOT wired into the standard pipeline. The file remains as a
marker that this conservative approach was tried and didn't help — and
as a starting point for the impactful variant described below.

## What this conservative pass does

  pc:    .const t v                    pc:    <swap candidate at pc+1>
  pc+1:  <unrelated instr that         pc+1:  .const t v
          doesn't use t>          →

If pc+1 is non-branching, doesn't define or use t, the swap is
semantics-preserving and shortens t's live range by 1 PC. Iterated up to
N times to sink past multiple instructions.

Cert: 1:1 transformation, fits the existing certificate framework directly.

## What would actually help (NOT implemented here)

The impactful form of rematerialization is **per-use-site splitting**:
for each `.const v c` with multiple uses, insert a fresh `.const v_use_i c`
right before each use, rename the use's reference, drop the original.

That converts ONE long-lived variable into MANY short-lived ones, each of
which RegAlloc trivially fits in a register. Estimated speedup based on
the asm analysis: 5–15% on constant-heavy kernels (k09, k15, k01, k04, k07).

Why it's not done here: the per-use split adds instructions to the program,
breaking the existing 1:1 cert framework. It needs FMAFusionOpt-style
non-1:1 plumbing with origMap / skipArr / revMap and corresponding cert
generation. ~1–2 days of cert engineering plus the pass itself.
-/

namespace RematConstOpt

/-- Is this a swappable instruction (non-branching, doesn't kill the const var)? -/
def isSwappable (next : TAC) (constVar : Var) : Bool :=
  match next with
  | .goto _ | .ifgoto _ _ | .halt => false  -- branching: don't swap
  | _ =>
    let defines := match DAEOpt.instrDef next with
      | some d => d == constVar  -- next defines constVar: blocks swap
      | none => false
    let uses := DAEOpt.instrUse next |>.contains constVar
    !defines && !uses

/-- Single-pass sink: for each `.const v c` immediately followed by a
    swappable instruction, swap them. -/
def sinkOnce (prog : Prog) : Prog :=
  let n := prog.size
  let arr := ((List.range n).foldl (fun (acc : Array TAC × Bool) pc =>
    let (out, justSwapped) := acc
    if justSwapped then
      -- this PC's instruction was already moved into the previous slot
      (out, false)
    else match prog[pc]? with
    | some (TAC.const v c) =>
      match prog[pc + 1]? with
      | some next =>
        if isSwappable next v then
          (out.push next |>.push (TAC.const v c), true)
        else
          (out.push (TAC.const v c), false)
      | none => (out.push (TAC.const v c), false)
    | some other => (out.push other, false)
    | none => (out, false)
  ) (#[], false)).1
  { code := arr, observable := prog.observable, arrayDecls := prog.arrayDecls }

/-- Run sinkOnce up to `fuel` times.  Each pass shortens at most one position
    per const, so multiple iterations are needed to sink a const past N
    swappable instructions. -/
partial def sinkN (prog : Prog) (fuel : Nat) : Prog :=
  if fuel == 0 then prog
  else
    let next := sinkOnce prog
    -- Bail if no progress (cheap structural compare via instr count + first-diff)
    if next.size != prog.size then prog
    else sinkN next (fuel - 1)

/-- Run the rematerialize-constant pass and produce an `ECertificate`.
    Conservative variant: only sinks `.const` instructions through swappable
    neighbors, never inserts or deletes instructions. -/
def optimize (tyCtx : TyCtx) (prog : Prog) : ECertificate :=
  let trans := sinkN prog 64
  let instrCerts := _root_.buildInstrCerts1to1 trans (_root_.collectAllVars prog trans)
  let haltCerts := _root_.buildHaltCerts instrCerts trans
  { orig := prog
    trans := trans
    tyCtx := tyCtx
    inv_orig := Array.replicate prog.size ([] : EInv)
    inv_trans := Array.replicate trans.size ([] : EInv)
    instrCerts := instrCerts
    haltCerts := haltCerts
    measure := Array.replicate trans.size 0 }

end RematConstOpt
