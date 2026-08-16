-- Copyright (c) 2026 Martin Rinard
/-
Targeted regression test for the two cases that made multiply-defined (reused)
fmul temps uncertifiable, and that the old conservative single-def guard avoided
by simply declining to fuse them.

  A. reused temp, straight line -- `t` is the destination of TWO fused fmuls.
     The second definition is itself absorbed, so it does NOT re-synchronise
     orig and trans; divergence must continue past it.
  B. reused temp inside a loop -- the back edge carries divergence to PCs below
     the fmul, so a linear window `(p, r]` claims `(t,t)` where it does not hold.

Both must produce a certificate that `checkCertificateExec` accepts AND must
actually fuse (trans smaller than orig).

Build: lake build fmareused && ./.lake/build/bin/fmareused
-/
import CredibleCompilation.CodeGen

def ty : TyCtx := fun v =>
  if v == "i" || v == "n" || v == "one" then .int else .float

/-- A. `t` defined twice, both fmuls fused; straight line.
    The second definition of `t` is itself absorbed, so it must NOT be treated as
    re-synchronising orig and trans. -/
def progReused : Prog :=
  { code := #[
      .const "a" (.float 0), .const "b" (.float 1), .const "c" (.float 2),
      .const "d" (.float 3), .const "e" (.float 4),
      .fbinop "t" .fmul "b" "c",      -- 5  fused with 6
      .fbinop "x" .fadd "a" "t",      -- 6
      .fbinop "t" .fmul "d" "e",      -- 7  same temp `t`, fused with 8
      .fbinop "y" .fadd "x" "t",      -- 8
      .halt ],                        -- 9
    observable := ["x", "y"] }

/-- B. `t` defined twice inside a loop body, both fused. The back edge carries
    the divergence of `t` to PCs below the fmul. -/
def progLoopReused : Prog :=
  { code := #[
      .const "n" (.int 3),                                    -- 0
      .const "one" (.int 1),                                  -- 1
      .const "i" (.int 0),                                    -- 2
      .const "x" (.float 0), .const "y" (.float 0),           -- 3 4
      .const "b" (.float 1), .const "c" (.float 2),           -- 5 6
      .const "d" (.float 3), .const "e" (.float 4),           -- 7 8
      .ifgoto (.cmp .lt (.var "i") (.var "n")) 11,            -- 9
      .goto 17,                                               -- 10
      .fbinop "t" .fmul "b" "c",                              -- 11 fused with 12
      .fbinop "x" .fadd "x" "t",                              -- 12
      .fbinop "t" .fmul "d" "e",                              -- 13 same `t`, fused with 14
      .fbinop "y" .fadd "y" "t",                              -- 14
      .binop "i" .add "i" "one",                              -- 15
      .goto 9,                                                -- 16 -> back edge
      .halt ],                                                -- 17
    observable := ["x", "y"] }

def report (name : String) (p : Prog) : IO Bool := do
  let cert := { FMAFusionOpt.optimize ty p with tyCtx := ty }
  let ok := checkCertificateExec cert
  let fused := p.size - cert.trans.size
  let fails := (checkCertificateVerboseExec cert).filterMap
                 (fun (n, b) => if b then none else some n)
  IO.println s!"{name}: accepted={ok} orig_size={p.size} trans_size={cert.trans.size} \
fused={fused} fails={String.intercalate " " fails}"
  pure (ok && fused > 0)

def main : IO UInt32 := do
  let a ← report "A reused-temp straight-line" progReused
  let b ← report "B reused-temp in loop     " progLoopReused
  if a && b then
    IO.println "PASS: multiply-defined fmul temps fuse and certify"
    return 0
  else
    IO.println "FAIL"
    return 1
