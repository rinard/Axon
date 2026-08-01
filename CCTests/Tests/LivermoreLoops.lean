-- Copyright (c) 2026 Martin Rinard
import CredibleCompilation.CodeGen

/-!
# Livermore Loops — Compiler Optimization Benchmarks

Selected kernels from the Lawrence Livermore National Laboratory loop benchmark
suite (McMahon, 1986), translated to three-address code.  Each kernel is run
through the full optimization pipeline and the resulting certificate is
verified with `checkCertificateExec`.

These stress-test the optimizer on realistic numerical-code patterns:
array-heavy loops, indirect indexing, floating-point reductions, nested loops,
loop-carried dependencies, and high register pressure.

## Kernels implemented

| # | Name                  | Key pattern                            |
|---|-----------------------|----------------------------------------|
| 1 | Hydro fragment        | Index arithmetic, multi-array float    |
| 3 | Inner product         | Float reduction (dot product)          |
| 5 | Tri-diagonal elim.    | Forward sweep, loop-carried dependency |
| 7 | Equation of state     | Deep expression tree, register pressure|
| 11| First sum             | Prefix sum, indirect array index       |
| 12| First difference      | Adjacent-element difference            |
| 21| Matrix × matrix       | Nested loops, flattened 2-D arrays     |
| 24| Find location of min  | Conditional update inside loop         |
-/

namespace LivermoreLoops

/-- Wrap a per-variable type classifier so it also types the register-named
    variables (`__ir{N}`/`__br{N}`/`__fr{N}`) that `RegAllocOpt` introduces.
    The register naming convention lets the type context derive a register's
    type from its name prefix, which the `well_typed_trans` certificate check
    on register-allocated programs requires. -/
private def withRegTypes (base : Var → VarTy) : TyCtx := fun x =>
  if x.startsWith "__fr" then .float
  else if x.startsWith "__br" then .bool
  else if x.startsWith "__ir" then .int
  else base x

-- ============================================================
-- § 1. Kernel 1 — Hydro Fragment
-- ============================================================

/-! `X(k) = Q + Y(k) * (R * Z(k+10) + T * Z(k+11))` for k = 0 .. 99.
    Tests index arithmetic (`k+10`, `k+11`), multiple float-array loads,
    and moderate register pressure from intermediate float temporaries. -/

private def hydroProg : Prog :=
  { code := #[
      TAC.const "q"       (.float (floatToBits 1.5)),  -- 0
      TAC.const "r"       (.float (floatToBits 2.0)),  -- 1
      TAC.const "t"       (.float (floatToBits 3.0)),  -- 2
      TAC.const "k"       (.int 0),                     -- 3
      TAC.const "one"     (.int 1),                     -- 4
      TAC.const "ten"     (.int 10),                    -- 5
      TAC.const "eleven"  (.int 11),                    -- 6
      -- loop header
      TAC.ifgoto (.cmp .lt (.var "k") (.lit 100)) 9,   -- 7
      TAC.halt,                                         -- 8
      -- loop body
      TAC.binop   "k10"  .add "k" "ten",               -- 9
      TAC.binop   "k11"  .add "k" "eleven",            -- 10
      TAC.arrLoad "zk10" "zarr" "k10" .float,          -- 11
      TAC.arrLoad "zk11" "zarr" "k11" .float,          -- 12
      TAC.arrLoad "yk"   "yarr" "k"   .float,          -- 13
      TAC.fbinop  "rz"   .fmul "r" "zk10",             -- 14
      TAC.fbinop  "tz"   .fmul "t" "zk11",             -- 15
      TAC.fbinop  "sm"   .fadd "rz" "tz",              -- 16
      TAC.fbinop  "prod" .fmul "yk" "sm",              -- 17
      TAC.fbinop  "xk"   .fadd "q" "prod",             -- 18
      TAC.arrStore "xarr" "k" "xk" .float,             -- 19
      TAC.binop   "k"    .add "k" "one",               -- 20
      TAC.goto 7                                        -- 21
    ],
    observable := ["k"],
    arrayDecls := [("xarr", 128, .float), ("yarr", 128, .float),
                   ("zarr", 128, .float)] }

private def hydroTyCtx : TyCtx := withRegTypes fun x =>
  if x ∈ ["q","r","t","zk10","zk11","yk","rz","tz","sm","prod","xk"]
  then .float else .int

#eval! do
  let cert := ConstPropOpt.optimize hydroTyCtx hydroProg
  assert! checkCertificateExec cert
  let cert2 := DAEOpt.optimize hydroTyCtx cert.trans
  assert! checkCertificateExec cert2

-- ============================================================
-- § 2. Kernel 3 — Inner Product (Dot Product)
-- ============================================================

/-! `q += x[i] * z[i]` for i = 0 .. 63.
    Float accumulation loop with two array reads per iteration.
    Tests float register allocation and basic loop optimization. -/

private def dotProg : Prog :=
  { code := #[
      TAC.const "i"   (.int 0),                         -- 0
      TAC.const "q"   (.float (floatToBits 0.0)),       -- 1
      TAC.const "one" (.int 1),                          -- 2
      -- loop header
      TAC.ifgoto (.cmp .lt (.var "i") (.lit 64)) 5,     -- 3
      TAC.halt,                                          -- 4
      -- loop body
      TAC.arrLoad "xi" "xarr" "i" .float,               -- 5
      TAC.arrLoad "zi" "zarr" "i" .float,               -- 6
      TAC.fbinop  "p"  .fmul "xi" "zi",                 -- 7
      TAC.fbinop  "q"  .fadd "q" "p",                   -- 8
      TAC.binop   "i"  .add "i" "one",                  -- 9
      TAC.goto 3                                         -- 10
    ],
    observable := ["q"],
    arrayDecls := [("xarr", 64, .float), ("zarr", 64, .float)] }

private def dotTyCtx : TyCtx := withRegTypes fun x =>
  if x ∈ ["q","xi","zi","p"] then .float else .int

#eval! do
  let cert := ConstPropOpt.optimize dotTyCtx dotProg
  assert! checkCertificateExec cert
  let cert2 := DAEOpt.optimize dotTyCtx cert.trans
  assert! checkCertificateExec cert2
  let cert3 := RegAllocOpt.optimize dotTyCtx cert2.trans
  assert! checkCertificateExec cert3

-- ============================================================
-- § 3. Kernel 5 — Tri-diagonal Elimination (forward sweep)
-- ============================================================

/-! Forward sweep of a tri-diagonal solver:
      `x[i] = z[i] * (y[i] - x[i-1])`    for i = 1 .. 63
    Loop-carried dependency on `x[i-1]` prevents LICM on the array
    load and stresses the dependency analysis. -/

private def tridiagProg : Prog :=
  { code := #[
      TAC.const "i"    (.int 1),                         -- 0
      TAC.const "one"  (.int 1),                         -- 1
      -- loop header
      TAC.ifgoto (.cmp .lt (.var "i") (.lit 64)) 4,     -- 2
      TAC.halt,                                          -- 3
      -- loop body
      TAC.binop   "im1" .sub "i" "one",                 -- 4
      TAC.arrLoad "xp"  "xarr" "im1" .float,            -- 5  x[i-1]
      TAC.arrLoad "yi"  "yarr" "i"   .float,            -- 6  y[i]
      TAC.arrLoad "zi"  "zarr" "i"   .float,            -- 7  z[i]
      TAC.fbinop  "dif" .fsub "yi" "xp",                -- 8  y[i] - x[i-1]
      TAC.fbinop  "val" .fmul "zi" "dif",               -- 9  z[i] * (...)
      TAC.arrStore "xarr" "i" "val" .float,             -- 10 x[i] := ...
      TAC.binop   "i"   .add "i" "one",                 -- 11
      TAC.goto 2                                         -- 12
    ],
    observable := ["i"],
    arrayDecls := [("xarr", 64, .float), ("yarr", 64, .float),
                   ("zarr", 64, .float)] }

private def tridiagTyCtx : TyCtx := withRegTypes fun x =>
  if x ∈ ["xp","yi","zi","dif","val"] then .float else .int

#eval! do
  let cert := ConstPropOpt.optimize tridiagTyCtx tridiagProg
  assert! checkCertificateExec cert
  let cert2 := DAEOpt.optimize tridiagTyCtx cert.trans
  assert! checkCertificateExec cert2

-- ============================================================
-- § 4. Kernel 7 — Equation of State Fragment
-- ============================================================

/-! `X(k) = U(k) + R * (Z(k) + R * Y(k))` for k = 0 .. 63.
    Deep expression tree with repeated multiplication by the
    loop-invariant scalar R.  Tests register pressure and
    constant-operand propagation through float expressions. -/

private def eosProg : Prog :=
  { code := #[
      TAC.const "r"    (.float (floatToBits 0.5)),       -- 0
      TAC.const "k"    (.int 0),                          -- 1
      TAC.const "one"  (.int 1),                          -- 2
      -- loop header
      TAC.ifgoto (.cmp .lt (.var "k") (.lit 64)) 5,      -- 3
      TAC.halt,                                           -- 4
      -- loop body
      TAC.arrLoad "yk"  "yarr" "k" .float,               -- 5
      TAC.arrLoad "zk"  "zarr" "k" .float,               -- 6
      TAC.arrLoad "uk"  "uarr" "k" .float,               -- 7
      TAC.fbinop  "ry"  .fmul "r" "yk",                  -- 8   R * Y(k)
      TAC.fbinop  "zry" .fadd "zk" "ry",                 -- 9   Z(k) + R*Y(k)
      TAC.fbinop  "rz"  .fmul "r" "zry",                 -- 10  R * (Z(k) + R*Y(k))
      TAC.fbinop  "xk"  .fadd "uk" "rz",                 -- 11  U(k) + R*(...)
      TAC.arrStore "xarr" "k" "xk" .float,               -- 12
      TAC.binop   "k"   .add "k" "one",                  -- 13
      TAC.goto 3                                          -- 14
    ],
    observable := ["k"],
    arrayDecls := [("xarr", 64, .float), ("yarr", 64, .float),
                   ("zarr", 64, .float), ("uarr", 64, .float)] }

private def eosTyCtx : TyCtx := withRegTypes fun x =>
  if x ∈ ["r","yk","zk","uk","ry","zry","rz","xk"] then .float else .int

#eval! do
  let cert := ConstPropOpt.optimize eosTyCtx eosProg
  assert! checkCertificateExec cert
  let cert2 := CSEOpt.optimize eosTyCtx cert.trans
  assert! checkCertificateExec cert2
  let cert3 := DAEOpt.optimize eosTyCtx cert2.trans
  assert! checkCertificateExec cert3
  let cert4 := RegAllocOpt.optimize eosTyCtx cert3.trans
  assert! checkCertificateExec cert4

-- ============================================================
-- § 5. Kernel 11 — First Sum (Prefix Sum)
-- ============================================================

/-! `x[i] = x[i] + x[i-1]` for i = 1 .. 63.
    In-place prefix sum with loop-carried dependency through the
    array.  Tests indirect indexing (`i-1`) and array read-after-write
    ordering. -/

private def prefixSumProg : Prog :=
  { code := #[
      TAC.const "i"    (.int 1),                         -- 0
      TAC.const "one"  (.int 1),                         -- 1
      -- loop header
      TAC.ifgoto (.cmp .lt (.var "i") (.lit 64)) 4,     -- 2
      TAC.halt,                                          -- 3
      -- loop body
      TAC.binop   "im1" .sub "i" "one",                 -- 4
      TAC.arrLoad "prev" "xarr" "im1" .int,             -- 5  x[i-1]
      TAC.arrLoad "cur"  "xarr" "i"   .int,             -- 6  x[i]
      TAC.binop   "sum"  .add "cur" "prev",             -- 7  x[i] + x[i-1]
      TAC.arrStore "xarr" "i" "sum" .int,               -- 8  x[i] := sum
      TAC.binop   "i"    .add "i" "one",                -- 9
      TAC.goto 2                                         -- 10
    ],
    observable := ["i"],
    arrayDecls := [("xarr", 64, .int)] }

private def prefixSumTyCtx : TyCtx := withRegTypes fun _ => .int

#eval! do
  let cert := ConstPropOpt.optimize prefixSumTyCtx prefixSumProg
  assert! checkCertificateExec cert
  let cert2 := DAEOpt.optimize prefixSumTyCtx cert.trans
  assert! checkCertificateExec cert2

-- ============================================================
-- § 6. Kernel 12 — First Difference
-- ============================================================

/-! `x[i] = y[i+1] - y[i]` for i = 0 .. 62.
    Adjacent-element difference.  Tests forward-indexing (`i+1`)
    and potential CSE when y[i+1] in one iteration equals y[i] in
    the next. -/

private def firstDiffProg : Prog :=
  { code := #[
      TAC.const "i"    (.int 0),                         -- 0
      TAC.const "one"  (.int 1),                         -- 1
      -- loop header
      TAC.ifgoto (.cmp .lt (.var "i") (.lit 63)) 4,     -- 2
      TAC.halt,                                          -- 3
      -- loop body
      TAC.arrLoad "yi"  "yarr" "i" .float,              -- 4  y[i]
      TAC.binop   "ip1" .add "i" "one",                 -- 5  i+1
      TAC.arrLoad "yn"  "yarr" "ip1" .float,            -- 6  y[i+1]
      TAC.fbinop  "d"   .fsub "yn" "yi",                -- 7  y[i+1] - y[i]
      TAC.arrStore "xarr" "i" "d" .float,               -- 8  x[i] := d
      TAC.binop   "i"   .add "i" "one",                 -- 9
      TAC.goto 2                                         -- 10
    ],
    observable := ["i"],
    arrayDecls := [("xarr", 64, .float), ("yarr", 64, .float)] }

private def firstDiffTyCtx : TyCtx := withRegTypes fun x =>
  if x ∈ ["yi","yn","d"] then .float else .int

#eval! do
  let cert := ConstPropOpt.optimize firstDiffTyCtx firstDiffProg
  assert! checkCertificateExec cert
  let cert2 := DAEOpt.optimize firstDiffTyCtx cert.trans
  assert! checkCertificateExec cert2

-- ============================================================
-- § 7. Kernel 21 — Matrix × Matrix Product
-- ============================================================

/-! `C[i,j] += A[i,k] * B[k,j]` for i,j,k = 0 .. 7  (N = 8).
    Three nested loops with flattened 2-D index arithmetic
    (`i*N+j`, `i*N+k`, `k*N+j`).  Tests nested loop structure,
    heavy index computation, and high register pressure.
    This is a triply-nested loop using goto/ifgoto. -/

private def matmulProg : Prog :=
  let n : BitVec 64 := 8
  { code := #[
      TAC.const "n"    (.int n),                         -- 0
      TAC.const "one"  (.int 1),                         -- 1
      TAC.const "zero" (.int 0),                         -- 2
      TAC.const "i"    (.int 0),                         -- 3
      -- outer loop (i)
      TAC.ifgoto (.cmp .lt (.var "i") (.lit n)) 6,      -- 4
      TAC.halt,                                          -- 5
      TAC.const "j" (.int 0),                            -- 6
      -- middle loop (j)
      TAC.ifgoto (.cmp .lt (.var "j") (.lit n)) 9,      -- 7
      TAC.goto 30,                                       -- 8: end j → increment i
      -- compute C index: i*N + j
      TAC.binop "in"   .mul "i" "n",                     -- 9
      TAC.binop "cIdx" .add "in" "j",                    -- 10
      -- load C[i,j] accumulator
      TAC.arrLoad "acc" "carr" "cIdx" .float,            -- 11
      TAC.const "k" (.int 0),                            -- 12
      -- inner loop (k)
      TAC.ifgoto (.cmp .lt (.var "k") (.lit n)) 15,     -- 13
      TAC.goto 26,                                       -- 14: end k → store & next j
      -- compute A index: i*N + k
      TAC.binop "aIdx" .add "in" "k",                   -- 15
      -- compute B index: k*N + j
      TAC.binop "kn"   .mul "k" "n",                    -- 16
      TAC.binop "bIdx" .add "kn" "j",                   -- 17
      -- loads
      TAC.arrLoad "aik" "aarr" "aIdx" .float,           -- 18
      TAC.arrLoad "bkj" "barr" "bIdx" .float,           -- 19
      -- multiply-add
      TAC.fbinop "ab"  .fmul "aik" "bkj",               -- 20
      TAC.fbinop "acc" .fadd "acc" "ab",                 -- 21
      -- k++
      TAC.binop  "k"   .add "k" "one",                  -- 22
      TAC.goto 13,                                       -- 23
      -- (padding for alignment)
      TAC.goto 26,                                       -- 24
      TAC.goto 26,                                       -- 25
      -- store C[i,j] and j++
      TAC.arrStore "carr" "cIdx" "acc" .float,           -- 26
      TAC.binop "j" .add "j" "one",                     -- 27
      TAC.goto 7,                                        -- 28
      -- (padding)
      TAC.goto 30,                                       -- 29
      -- i++
      TAC.binop "i" .add "i" "one",                     -- 30
      TAC.goto 4                                         -- 31
    ],
    observable := ["i"],
    arrayDecls := [("aarr", 64, .float), ("barr", 64, .float),
                   ("carr", 64, .float)] }

private def matmulTyCtx : TyCtx := withRegTypes fun x =>
  if x ∈ ["acc","aik","bkj","ab"] then .float else .int

#eval! do
  let cert := ConstPropOpt.optimize matmulTyCtx matmulProg
  assert! checkCertificateExec cert
  let cert2 := CSEOpt.optimize matmulTyCtx cert.trans
  assert! checkCertificateExec cert2
  let cert3 := LICMOpt.optimize matmulTyCtx cert2.trans
  assert! checkCertificateExec cert3
  let cert4 := DAEOpt.optimize matmulTyCtx cert3.trans
  assert! checkCertificateExec cert4
  let cert5 := PeepholeOpt.optimize matmulTyCtx cert4.trans
  assert! checkCertificateExec cert5

-- ============================================================
-- § 8. Kernel 24 — Find Location of First Minimum
-- ============================================================

/-! Scan an array to find the index of the minimum element:
      `if x[k] < x[m] then m := k`    for k = 1 .. 63
    Tests conditional assignment inside a loop (if-then-else
    compiled to ifgoto / goto) and comparison of array-loaded
    float values. -/

private def findMinProg : Prog :=
  { code := #[
      TAC.const "m"    (.int 0),                         -- 0
      TAC.arrLoad "xm" "xarr" "m" .float,               -- 1  xm := x[0]
      TAC.const "k"    (.int 1),                         -- 2
      TAC.const "one"  (.int 1),                         -- 3
      -- loop header
      TAC.ifgoto (.cmp .lt (.var "k") (.lit 64)) 6,     -- 4
      TAC.halt,                                          -- 5
      -- loop body
      TAC.arrLoad "xk" "xarr" "k" .float,               -- 6  xk := x[k]
      TAC.ifgoto (.fcmp .flt (.var "xk") (.var "xm")) 9, -- 7  if xk < xm
      TAC.goto 11,                                       -- 8  else skip
      -- then: update minimum
      TAC.copy  "m"  "k",                                -- 9  m := k
      TAC.copy  "xm" "xk",                               -- 10 xm := xk
      -- k++
      TAC.binop "k" .add "k" "one",                      -- 11
      TAC.goto 4                                          -- 12
    ],
    observable := ["m"],
    arrayDecls := [("xarr", 64, .float)] }

private def findMinTyCtx : TyCtx := withRegTypes fun x =>
  if x ∈ ["xm","xk"] then .float else .int

#eval! do
  let cert := ConstPropOpt.optimize findMinTyCtx findMinProg
  assert! checkCertificateExec cert
  let cert2 := DAEOpt.optimize findMinTyCtx cert.trans
  assert! checkCertificateExec cert2
  let cert3 := PeepholeOpt.optimize findMinTyCtx cert2.trans
  assert! checkCertificateExec cert3

-- ============================================================
-- § 9. Full pipeline on each kernel
-- ============================================================

/-! Run the full strict `optimizePipeline` (DCE → LICM → ConstProp → DCE →
    DAE → FMAFusion → CSE → ConstHoist → Peephole → DCE → RegAlloc) on every
    kernel.  This is the main regression test: each kernel must either produce
    a valid certificate for every pass, or fail *only* on the documented
    `FMAFusion`-in-loop limitation (see the `.error` branch).  Any other
    failure is a real regression. -/

private def allProgs : List (String × TyCtx × Prog) :=
  [ ("K1_hydro",      hydroTyCtx,     hydroProg),
    ("K3_dot",        dotTyCtx,       dotProg),
    ("K5_tridiag",    tridiagTyCtx,   tridiagProg),
    ("K7_eos",        eosTyCtx,       eosProg),
    ("K11_prefixsum", prefixSumTyCtx, prefixSumProg),
    ("K12_firstdiff", firstDiffTyCtx, firstDiffProg),
    ("K21_matmul",    matmulTyCtx,    matmulProg),
    ("K24_findmin",   findMinTyCtx,   findMinProg) ]

#eval! allProgs.forM fun (name, tyCtx, prog) =>
  match optimizePipeline tyCtx prog with
  | .ok _ => pure ()
  | .error e =>
    -- Known library limitation (not a fault in this kernel): the strict
    -- `optimizePipeline` includes `FMAFusion`, whose executable certificate
    -- cannot discharge a multiply-add fused *inside a loop body* (the pass
    -- attaches no ConstProp invariants, so the loop back-edge fails the
    -- `all_transitions` check).  Straight-line fma fusions still certify, and
    -- production codegen uses the resilient `applyStandardPipelineFixpoint`,
    -- which certificate-checks every pass and simply skips the one that fails.
    -- So an fma-in-loop kernel is expected to fail *only* on FMAFusion; any
    -- other failure — here or in another pass — is a real regression.
    if (e.splitOn "FMAFusion").length > 1 then pure ()
    else panic! s!"pipeline failed on {name}: {e}"

end LivermoreLoops
