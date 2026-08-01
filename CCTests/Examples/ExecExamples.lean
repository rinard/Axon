-- Copyright (c) 2026 Martin Rinard
import CredibleCompilation.ExecChecker
import CredibleCompilation.CopyPropOpt
import CredibleCompilation.CSEOpt
import CredibleCompilation.LICMOpt

/-!
# Executable Certificate Examples

Each example demonstrates a specific compiler optimization verified by the
executable certificate checker.  The checker returns `true` for correct
transformations and `false` for buggy ones.

## Optimizations covered

1. **Constant propagation** — propagate known constants through copies
2. **Copy propagation** — replace uses of a copied variable with the original
3. **Common subexpression elimination (CSE)** — reuse already-computed values
4. **Dead code elimination** — remove unreachable code after always-taken branches
5. **Loop-invariant code motion (LICM)** — remove redundant loop-invariant
   recomputation from loop bodies
6. **Induction variable elimination (IVE)** — replace recomputation with
   incremental update using reassociation
-/

-- ============================================================
-- Helpers
-- ============================================================

-- Helper: build an ETransCorr with empty relation
private abbrev tc (labels : List Label) : ETransCorr := { origLabels := labels }
-- Helper: build identity pairs from a list of observable variables
private def obsRel (obs : List Var) : EExprRel :=
  obs.map fun v => (.var v, .var v)
-- Helper: build an ETransCorr whose target has observable identity pairs
private abbrev tcObs (labels : List Label) (obs : EExprRel) : ETransCorr :=
  { origLabels := labels, rel_next := obs }
-- Helper: build an EInstrCert with empty relation
private abbrev ic (pc : Label) (trans : List ETransCorr) : EInstrCert :=
  { pc_orig := pc, transitions := trans }
-- Helper: build an EInstrCert for a halt label with observable identity pairs
private abbrev icObs (pc : Label) (obs : EExprRel) : EInstrCert :=
  { pc_orig := pc, rel := obs, transitions := [] }
-- Helper: build an EHaltCert with empty relation
private abbrev hc (pc : Label) : EHaltCert := { pc_orig := pc }

-- ============================================================
-- § 1. Constant propagation (chain)
-- ============================================================

/-! ### Example 1: Constant propagation through a chain of copies

  Original:
    0: x := 7
    1: y := x          — copy (x is 7)
    2: z := y          — copy (y is 7)
    3: halt

  Transformed:
    0: x := 7
    1: y := 7          — propagated
    2: z := 7          — propagated
    3: halt

  Invariants: `x = 7` at labels ≥ 1, `y = 7` at labels ≥ 2.
-/
namespace ConstProp

def cert : ECertificate :=
  { orig  := { code := #[TAC.const "x" (.int 7), TAC.copy "y" "x", TAC.copy "z" "y", TAC.halt], observable := ["z"] }
    trans := { code := #[TAC.const "x" (.int 7), TAC.const "y" (.int 7), TAC.const "z" (.int 7), TAC.halt], observable := ["z"] }
    tyCtx := fun _ => .int
    inv_orig  := #[[], [("x", .lit 7)], [("x", .lit 7), ("y", .lit 7)],
                       [("x", .lit 7), ("y", .lit 7)]]
    inv_trans := #[[], [("x", .lit 7)], [("x", .lit 7), ("y", .lit 7)],
                       [("x", .lit 7), ("y", .lit 7)]]
    instrCerts := #[
      ic 0 ([tc [1]]),                            -- trans 0→1 : orig 0→1
      ic 1 ([tc [2]]),                            -- trans 1→2 : orig 1→2
      ic 2 ([tcObs [3] (obsRel ["z"])]),          -- trans 2→3 : orig 2→3
      icObs 3 (obsRel ["z"]) ]                    -- halt
    haltCerts := #[hc 0, hc 0, hc 0, hc 3]
    measure := #[0, 0, 0, 0] }

#eval! checkCertificateExec cert              -- true
#eval! checkCertificateVerboseExec cert

end ConstProp

-- ============================================================
-- § 2. Copy propagation
-- ============================================================

/-! ### Example 2: Copy propagation — replace copied variable with original

  Original:
    0: a := b          — copy
    1: c := a + d      — uses a (= b)
    2: halt

  Transformed:
    0: a := b          — same copy
    1: c := b + d      — replaced a with b
    2: halt

  Invariant: `a = b` at labels ≥ 1.
  Under this invariant, `a + d` simplifies to the same value as `b + d`.
-/
namespace CopyProp

def origProg : Prog :=
  { code := #[TAC.copy "a" "b", TAC.binop "c" .add "a" "d", TAC.halt], observable := ["c"] }

/-- Certificate produced by the real copy-propagation pass. It replaces the use of
    `a` in `c := a + d` with `b` (valid because `a = b`); the relational witnesses
    the checker's `all_transitions` needs are emitted by the pass. -/
def cert : ECertificate := CopyPropOpt.optimize (fun _ => .int) origProg

#eval! checkCertificateExec cert              -- true
#eval! checkCertificateVerboseExec cert

end CopyProp

-- ============================================================
-- § 3. Common subexpression elimination
-- ============================================================

/-! ### Example 3: CSE — reuse an already-computed expression

  Original:
    0: a := x + y
    1: b := x + y      — same as a
    2: c := a + b
    3: halt

  Transformed:
    0: a := x + y
    1: b := a           — CSE: reuse a
    2: c := a + b
    3: halt

  Invariant: `a = x + y` at labels ≥ 1.
-/
namespace CSE

def origProg : Prog :=
  { code := #[TAC.binop "a" .add "x" "y",
              TAC.binop "b" .add "x" "y",
              TAC.binop "c" .add "a" "b",
              TAC.halt], observable := ["c"] }

/-- Certificate produced by the real CSE pass. It rewrites the redundant
    `b := x + y` to `b := a` (valid because `a = x + y`); the relational
    witnesses the checker's `all_transitions` needs are emitted by the pass. -/
def cert : ECertificate := CSEOpt.optimize (fun _ => .int) origProg

#eval! checkCertificateExec cert              -- true
#eval! checkCertificateVerboseExec cert

end CSE

-- ============================================================
-- § 4. Bad example (buggy transformation)
-- ============================================================

/-! ### Bad Example: Incorrect constant propagation

  Original:
    0: x := 5
    1: y := x          — y gets 5
    2: halt

  Transformed (BUGGY):
    0: x := 5
    1: y := 3          — WRONG: should be 5
    2: halt

  Observable variable: y.  The checker rejects this because the symbolic
  effects don't match: orig produces y = 5 but trans produces y = 3.
-/
namespace BadExample

def cert : ECertificate :=
  { orig  := { code := #[TAC.const "x" (.int 5), TAC.copy "y" "x", TAC.halt], observable := ["y"] }
    trans := { code := #[TAC.const "x" (.int 5), TAC.const "y" (.int 3), TAC.halt], observable := ["y"] }
    tyCtx := fun _ => .int
    inv_orig  := #[[], [("x", .lit 5)], [("x", .lit 5)]]
    inv_trans := #[[], [("x", .lit 5)], [("x", .lit 5)]]
    instrCerts := #[
      ic 0 ([tc [1]]),
      ic 1 ([tcObs [2] (obsRel ["y"])]),
      icObs 2 (obsRel ["y"]) ]
    haltCerts := #[hc 0, hc 0, hc 2]
    measure := #[0, 0, 0] }

#eval! checkCertificateExec cert              -- false
#eval! checkCertificateVerboseExec cert       -- all_transitions fails

end BadExample

-- ============================================================
-- § 5. Dead code elimination
-- ============================================================

/-! ### Example 4: Dead code elimination — remove unreachable code

  Original:
    0: x := 1
    1: if x goto 3      — always taken (x = 1 ≠ 0)
    2: halt              — DEAD (unreachable)
    3: y := 5
    4: halt

  Transformed:
    0: x := 1
    1: y := 5            — branch + dead code removed
    2: halt

  Invariant: `x = 1` at labels ≥ 1.
  The checker's symbolic analysis resolves `computeNextPC` for the ifgoto:
  under invariant `x = 1`, the branch is always taken.
  Trans 1→2 maps to orig 1→3→4 (take branch, y := 5, reach halt).
-/
namespace DCE

def cert : ECertificate :=
  { orig  := { code := #[TAC.const "x" (.int 1),            -- 0
               TAC.ifgoto (.cmp .ne (.var "x") (.lit 0)) 3,     -- 1: always taken
               TAC.halt,                    -- 2: dead
               TAC.const "y" (.int 5),            -- 3
               TAC.halt], observable := ["y"] }                   -- 4
    trans := { code := #[TAC.const "x" (.int 1),            -- 0
               TAC.const "y" (.int 5),            -- 1: branch + dead code removed
               TAC.halt], observable := ["y"] }                   -- 2
    tyCtx := fun _ => .int
    inv_orig  := #[[], [("x", .lit 1)], [("x", .lit 1)],
                      [("x", .lit 1)], [("x", .lit 1)]]
    inv_trans := #[[], [("x", .lit 1)], [("x", .lit 1)]]
    instrCerts := #[
      ic 0 ([tc [1]]),                            -- trans 0→1 : orig 0→1
      ic 1 ([tcObs [3, 4] (obsRel ["y"])]),       -- trans 1→2 : orig 1→3→4
      icObs 4 (obsRel ["y"]) ]                    -- halt
    haltCerts := #[hc 0, hc 0, hc 4]
    measure := #[0, 0, 0] }

#eval! checkCertificateExec cert              -- true
#eval! checkCertificateVerboseExec cert

end DCE

-- ============================================================
-- § 6. Loop-invariant code motion (LICM)
-- ============================================================

/-! ### Example 5: LICM — remove redundant loop-invariant recomputation

  Original (8 instructions):
    0: one := 1
    1: t := a * b                  — initial computation
    2: if n goto 4
    3: halt
    4: s := s + t
    5: t := a * b                  — REDUNDANT: a, b unchanged in loop
    6: n := n - one
    7: goto 2

  Transformed (7 instructions — redundant recomputation removed):
    0: one := 1
    1: t := a * b
    2: if n goto 4
    3: halt
    4: s := s + t
    5: n := n - one
    6: goto 2

  Invariant: `t = a * b` throughout both programs (since a, b are never
  modified).  Trans 4→5 maps to orig 4→5→6 — the redundant `t := a * b`
  at orig 5 is a no-op under the invariant, so both paths produce the
  same effect.
-/
namespace LICM

def origProg : Prog :=
  { code := #[
      TAC.const "one" (.int 1),              -- 0
      TAC.binop "t" .mul "a" "b",    -- 1: t := a * b
      TAC.ifgoto (.cmp .ne (.var "n") (.lit 0)) 4,       -- 2: loop head
      TAC.halt,                       -- 3
      TAC.binop "s" .add "s" "t",    -- 4: loop body
      TAC.binop "t" .mul "a" "b",    -- 5: redundant recomputation
      TAC.binop "n" .sub "n" "one",  -- 6: n--
      TAC.goto 2 ],                   -- 7
    observable := ["s"] }

/-- Certificate produced by the real LICM pass. It removes the redundant
    in-loop recomputation `t := a * b` (loop-invariant); the relational and
    path witnesses the checker's `all_transitions` needs are emitted by the pass. -/
def cert : ECertificate := LICMOpt.optimize (fun _ => .int) origProg

#eval! checkCertificateExec cert              -- true
#eval! checkCertificateVerboseExec cert

end LICM

-- ============================================================
-- § 7. Induction variable elimination (IVE)
-- ============================================================

/-! ### Example 6: IVE — replace recomputation with incremental update

  Original (7 instructions):
    0: one := 1
    1: k := 100
    2: rem := k - i             — loop head: recompute rem = 100 - i
    3: if rem goto 5
    4: halt
    5: i := i + one
    6: goto 2

  Transformed (8 instructions):
    0: one := 1
    1: k := 100
    2: rem := k - i             — initial computation (same)
    3: if rem goto 5
    4: halt
    5: i := i + one
    6: rem := rem - one         — IVE: decrement instead of recompute
    7: goto 3                   — skip recomputation, jump to loop head

  After `i := i + one` (pc 5), the invariant `rem = 100 - i` becomes
  stale: `rem = 101 - i` (using the new `i`).  The IVE step
  `rem := rem - one` restores it: `(101 - i) - 1` simplifies to
  `100 - i` via the reassociation rule `(lit - var) - lit → (lit-lit) - var`.

  Trans 6→7 maps to orig 6→2→3 (goto, recompute rem, loop head).
  Trans 7→3 is a zero-step (orig already at the loop head) with a
  decreasing measure.
-/
namespace IVE

private def inv_1k : EInv := [("one", .lit 1), ("k", .lit 100)]
private def inv_loop : EInv :=
  [("one", .lit 1), ("k", .lit 100),
   ("rem", .bin .sub (.lit 100) (.var "i"))]
private def inv_post_inc : EInv :=
  [("one", .lit 1), ("k", .lit 100),
   ("rem", .bin .sub (.lit 101) (.var "i"))]

-- Cross-program relation at the loop points: identity on the live variables
-- (orig and trans share names and — by the invariants — equal values).
private def idRel : EExprRel :=
  [(.var "one", .var "one"), (.var "k", .var "k"),
   (.var "i", .var "i"), (.var "rem", .var "rem")]

-- Relation at trans pc 6 (aligned to orig pc 2, the recomputation).  Here the
-- trans `rem` holds the stale value `101 - i` (after `i++`, before the IVE
-- decrement), which on the orig side is the value about to be recomputed.
-- Mapping trans `rem` to `101 - i` lets `checkRelConsistency` prove the IVE
-- step `rem := rem - one` restores `rem = 100 - i` (matching orig's `k - i`)
-- using only the constants `one = 1`, `k = 100` known at orig pc 2.
private def r6 : EExprRel :=
  [(.var "one", .var "one"), (.var "k", .var "k"),
   (.var "i", .var "i"), (.bin .sub (.lit 101) (.var "i"), .var "rem")]

-- Helper: an ETransCorr carrying explicit pre/post relations.
private abbrev tcR (labels : List Label) (r r' : EExprRel) : ETransCorr :=
  { origLabels := labels, rel := r, rel_next := r' }
-- Helper: an EInstrCert carrying an explicit relation.
private abbrev icR (pc : Label) (r : EExprRel) (trans : List ETransCorr) : EInstrCert :=
  { pc_orig := pc, rel := r, transitions := trans }

def cert : ECertificate :=
  { orig := {
      code := #[
        TAC.const "one" (.int 1),              -- 0
        TAC.const "k" (.int 100),              -- 1
        TAC.binop "rem" .sub "k" "i",  -- 2: loop head — recompute rem
        TAC.ifgoto (.cmp .ne (.var "rem") (.lit 0)) 5,      -- 3
        TAC.halt,                       -- 4
        TAC.binop "i" .add "i" "one",  -- 5: i++
        TAC.goto 2 ],                   -- 6: back to recomputation
      observable := ["i"] }
    trans := {
      code := #[
        TAC.const "one" (.int 1),              -- 0
        TAC.const "k" (.int 100),              -- 1
        TAC.binop "rem" .sub "k" "i",  -- 2: initial rem (same)
        TAC.ifgoto (.cmp .ne (.var "rem") (.lit 0)) 5,      -- 3: loop head
        TAC.halt,                       -- 4
        TAC.binop "i" .add "i" "one",  -- 5: i++
        TAC.binop "rem" .sub "rem" "one", -- 6: IVE — countdown
        TAC.goto 3 ],                   -- 7: skip recomputation
      observable := ["i"] }
    tyCtx := fun _ => .int
    inv_orig := #[
      [],                          -- 0
      [("one", .lit 1)],          -- 1
      inv_1k,                      -- 2: before rem computed
      inv_loop,                    -- 3: rem = 100 - i
      inv_loop,                    -- 4
      inv_loop,                    -- 5
      inv_post_inc ]               -- 6: after i++, rem = 101 - i
    inv_trans := #[
      [],                          -- 0
      [("one", .lit 1)],          -- 1
      inv_1k,                      -- 2
      inv_loop,                    -- 3: rem = 100 - i
      inv_loop,                    -- 4
      inv_loop,                    -- 5
      inv_post_inc,                -- 6: after i++, rem = 101 - i
      inv_loop ]                   -- 7: after rem--, rem = 100 - i
    instrCerts := #[
      icR 0 idRel ([tcR [1] idRel idRel]),        -- trans 0→1 : orig 0→1
      icR 1 idRel ([tcR [2] idRel idRel]),        -- trans 1→2 : orig 1→2
      icR 2 idRel ([tcR [3] idRel idRel]),        -- trans 2→3 : orig 2→3
      icR 3 idRel ([tcR [5] idRel idRel,          -- trans 3→5 (taken) : orig 3→5
                    tcR [4] idRel idRel]),        -- trans 3→4 (halt)  : orig 3→4
      icR 4 idRel ([]),                           -- halt
      icR 5 idRel ([tcR [6, 2] idRel r6]),        -- trans 5→6 : orig 5→6→2 (i++)
      icR 2 r6 ([tcR [3] r6 idRel]),              -- trans 6→7 : orig 2→3 (the IVE step!)
      icR 3 idRel ([tcR [] idRel idRel]) ]        -- trans 7→3 : orig 3→3 (zero-step)
    haltCerts := #[hc 0, hc 0, hc 0, hc 0, hc 4, hc 0, hc 0, hc 0]
    measure := #[0, 0, 0, 0, 0, 0, 0, 1] }

#eval! checkCertificateExec cert              -- true
#eval! checkCertificateVerboseExec cert

end IVE
