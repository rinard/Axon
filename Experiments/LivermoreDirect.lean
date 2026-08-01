-- Copyright (c) 2026 Martin Rinard
import CredibleCompilation.CodeGen

/-!
# Livermore Loops — direct AST → verified pipeline (no parser).

Each kernel below is hand-translated from the canonical netlib source
(`/tmp/livermore_orig/lloops.f`, kernels at lines 1752-2576; SIGNEL init
at lines 5013-5060) into a `WhileLang.Program` value. The AST is fed
straight into `compileProgramAst` — the unverified `parseProgram`
front end is bypassed. Each kernel is paired with a self-contained
canonical Fortran reference that gfortran-compiles for a checksum
comparison.

Run individual kernel:
    lake build livermore_direct
    .lake/build/bin/livermore_direct k03

Run all:
    .lake/build/bin/livermore_direct all
-/

-- ============================================================
-- § 0. Common AST helpers (concise constructors)
-- ============================================================

namespace LivermoreDirect

/-- Float literal. -/
abbrev fl  (f : Float)         : SExpr := .flit f
/-- Integer literal. -/
abbrev il  (n : Int)           : SExpr := .lit n
/-- Variable read (int / generic). -/
abbrev v   (x : String)        : SExpr := .var x
abbrev fadd (a b : SExpr)      : SExpr := .fbin .fadd a b
abbrev fsub (a b : SExpr)      : SExpr := .fbin .fsub a b
abbrev fmul (a b : SExpr)      : SExpr := .fbin .fmul a b
abbrev fdiv (a b : SExpr)      : SExpr := .fbin .fdiv a b
abbrev iadd (a b : SExpr)      : SExpr := .bin  .add  a b
abbrev isub (a b : SExpr)      : SExpr := .bin  .sub  a b
abbrev imul (a b : SExpr)      : SExpr := .bin  .mul  a b
abbrev imod (a b : SExpr)      : SExpr := .bin  .mod  a b
abbrev fread (arr : String) (i : SExpr) : SExpr := .farrRead arr i
abbrev iread (arr : String) (i : SExpr) : SExpr := .arrRead  arr i

/-- Loop `k = lo, hi` with structured `while`: emits `k := lo; while k <= hi { body; k := k+1 }`. -/
def fortranDo (k : String) (lo hi : SExpr) (body : Stmt) : Stmt :=
  .assign k lo ;;
  .loop (.cmp .le (v k) hi)
    (body ;; .assign k (iadd (v k) (il 1)))

/-- Canonical SIGNEL recurrence on a 1-D float array `arr` of length `n`,
    with SCALED = 0.1 (= 1/10), BIASED = 0 — verbatim from
    `lloops.f` lines 5036-5056. Resets FUZZ each call so the sequence
    is identical for every fresh call. -/
def signelFill (arr : String) (n : Int) : Stmt :=
  .fassign "fuzz" (fl 1.234500e-3) ;;
  .fassign "buzz" (fadd (fl 1.0) (v "fuzz")) ;;
  .fassign "fizz" (fmul (fl 1.1) (v "fuzz")) ;;
  fortranDo "k" (il 1) (il n)
    ( .fassign "buzz" (fadd (fmul (fsub (fl 1.0) (v "fuzz")) (v "buzz")) (v "fuzz")) ;;
      .fassign "fuzz" (fsub (fl 0.0) (v "fuzz")) ;;
      .farrWrite arr (v "k") (fmul (fsub (v "buzz") (v "fizz")) (fl 0.1)) )

/-- Equivalent SIGNEL Fortran source as a string — written once and
    used by every kernel reference program. The subroutine is identical
    to `lloops.f` SIGNEL with SCALED=0.1, BIASED=0 hard-coded. -/
def signelSubroutineFortran : String := "
      SUBROUTINE SIGNEL(V, N)
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      DIMENSION V(N)
      DOUBLE PRECISION FUZZ, BUZZ, FIZZ, ONE, SCALED
      SCALED = 1.0D0 / 10.0D0
      FUZZ   = 1.234500D-3
      BUZZ   = 1.0D0 + FUZZ
      FIZZ   = 1.1D0 * FUZZ
      ONE    = 1.0D0
      DO 1 K = 1, N
        BUZZ = (ONE - FUZZ) * BUZZ + FUZZ
        FUZZ = -FUZZ
        V(K) = (BUZZ - FIZZ) * SCALED
    1 CONTINUE
      RETURN
      END
"

end LivermoreDirect

-- ============================================================
-- § 1. Kernel registry — each entry: (name, ast Program, fortran source)
-- ============================================================

namespace LivermoreDirect

/-- A kernel registration: AST program + matching standalone Fortran source. -/
structure Kernel where
  name        : String
  program     : Program
  fortranSrc  : String

end LivermoreDirect

-- ============================================================
-- § 2. K03 — INNER PRODUCT
--   Canonical kernel:  Q = SUM_{k=1..n} Z(k) * X(k)
--   (kernels_only.f K3, lloops.f lines 1999-2009)
-- ============================================================

namespace LivermoreDirect.K03

private def N      : Int := 1001
private def NREPS  : Int := 2
private def ASIZE  : Nat := 1002

open LivermoreDirect in
def kernelBody : Stmt :=
  .fassign "q" (fl 0.0) ;;
  fortranDo "k" (il 1) (il N)
    ( .fassign "q" (fadd (v "q") (fmul (fread "z" (v "k")) (fread "x" (v "k")))) )

open LivermoreDirect in
def program : Program where
  decls :=
    [ ("k", .int), ("rep", .int), ("q", .float)
    , ("fuzz", .float), ("buzz", .float), ("fizz", .float) ]
  arrayDecls := [ ("z", ASIZE, .float), ("x", ASIZE, .float) ]
  body :=
    signelFill "z" N ;;
    signelFill "x" N ;;
    fortranDo "rep" (il 1) (il NREPS) kernelBody ;;
    .printFloat (v "q") ;; .printString "\n"

def fortranSrc : String := s!"
      PROGRAM K03REF
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      INTEGER REP
      PARAMETER (N = {N}, NREPS = {NREPS})
      DIMENSION Z(N), X(N)
      CALL SIGNEL(Z, N)
      CALL SIGNEL(X, N)
      DO 100 REP = 1, NREPS
        Q = 0.0D0
        DO 3 K = 1, N
    3     Q = Q + Z(K) * X(K)
  100 CONTINUE
      WRITE(*,'(F0.6)') Q
      END
" ++ LivermoreDirect.signelSubroutineFortran

def kernel : LivermoreDirect.Kernel :=
  { name := "k03", program := program, fortranSrc := fortranSrc }

end LivermoreDirect.K03

-- ============================================================
-- § /SPACER/ helper — SIGNEL-fill a 39-element spacer array and
-- expose canonical scalar names by index. Mirrors the COMMON /SPACER/
-- declaration at lloops.f:1813-1816.
--    Index → name:
--    1..9   A11..A33  10 AR  11 BR  12 C0   13 CR   14 DI   15 DK
--    16..22 DM22..DM28 23 DN 24 E3   25 E6   26 EXPMAX 27 FLX
--    28 Q   29 QA      30 R  31 RI   32 S    33 SCALE 34 SIG
--    35 STB5 36 T      37 XNC 38 XNEI 39 XNM
-- ============================================================

namespace LivermoreDirect

/-- Load named spacer scalars from the SIGNEL-filled `spacer` array. -/
def loadSpacers (entries : List (String × Int)) : Stmt :=
  entries.foldr (fun (name, idx) acc =>
    .fassign name (fread "spacer" (il idx)) ;; acc) .skip

/-- Fortran snippet to declare/fill SPACER(39) and pull named scalars. -/
def loadSpacersFortran (entries : List (String × Int)) : String :=
  entries.foldl (fun acc (name, idx) => acc ++ s!"      {name} = SPACER({idx})\n") ""

end LivermoreDirect

-- ============================================================
-- § K01 — HYDRO FRAGMENT
--   Canonical:  X(k) = Q + Y(k) * (R*ZX(k+10) + T*ZX(k+11))  for k=1..n
--   We use a separate Z(1012) (no EQUIVALENCE alias) — both AST and
--   Fortran reference allocate explicitly.
-- ============================================================

namespace LivermoreDirect.K01

private def N : Int := 1001
private def NREPS : Int := 2

open LivermoreDirect in
def program : Program where
  decls :=
    [ ("k", .int), ("rep", .int)
    , ("q", .float), ("r", .float), ("t", .float)
    , ("fuzz", .float), ("buzz", .float), ("fizz", .float) ]
  arrayDecls :=
    [ ("x", 1002, .float), ("y", 1002, .float), ("z", 1013, .float)
    , ("spacer", 40, .float) ]
  body :=
    signelFill "spacer" 39 ;;
    loadSpacers [("q", 28), ("r", 30), ("t", 36)] ;;
    signelFill "y" N ;;
    signelFill "z" 1012 ;;
    fortranDo "rep" (il 1) (il NREPS)
      ( fortranDo "k" (il 1) (il N)
          ( .farrWrite "x" (v "k")
              (fadd (v "q")
                (fmul (fread "y" (v "k"))
                  (fadd (fmul (v "r") (fread "z" (iadd (v "k") (il 10))))
                        (fmul (v "t") (fread "z" (iadd (v "k") (il 11))))))) ) ) ;;
    .printFloat (fread "x" (il 1)) ;; .printString "\n"

def fortranSrc : String :=
  let loads := LivermoreDirect.loadSpacersFortran [("Q", 28), ("R", 30), ("T", 36)]
  s!"
      PROGRAM K01REF
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      INTEGER REP
      PARAMETER (N = {N}, NREPS = {NREPS})
      DIMENSION X(N), Y(N), Z(1012), SPACER(39)
      CALL SIGNEL(SPACER, 39)
{loads}      CALL SIGNEL(Y, N)
      CALL SIGNEL(Z, 1012)
      DO 100 REP = 1, NREPS
        DO 1 K = 1, N
    1     X(K) = Q + Y(K) * (R*Z(K+10) + T*Z(K+11))
  100 CONTINUE
      WRITE(*,'(F0.6)') X(1)
      END
" ++ LivermoreDirect.signelSubroutineFortran

def kernel : LivermoreDirect.Kernel :=
  { name := "k01", program := program, fortranSrc := fortranSrc }

end LivermoreDirect.K01

-- ============================================================
-- § K05 — TRI-DIAGONAL ELIMINATION (no-vec)
--   Canonical: X(i) = Z(i) * (Y(i) - X(i-1))   for i=2..n
-- ============================================================

namespace LivermoreDirect.K05

private def N : Int := 1001
private def NREPS : Int := 2

open LivermoreDirect in
def program : Program where
  decls :=
    [ ("k", .int), ("rep", .int)
    , ("fuzz", .float), ("buzz", .float), ("fizz", .float) ]
  arrayDecls :=
    [ ("x", 1002, .float), ("y", 1002, .float), ("z", 1002, .float) ]
  body :=
    signelFill "x" N ;; signelFill "y" N ;; signelFill "z" N ;;
    fortranDo "rep" (il 1) (il NREPS)
      ( fortranDo "k" (il 2) (il N)
          ( .farrWrite "x" (v "k")
              (fmul (fread "z" (v "k"))
                (fsub (fread "y" (v "k")) (fread "x" (isub (v "k") (il 1))))) ) ) ;;
    .printFloat (fread "x" (il N)) ;; .printString "\n"

def fortranSrc : String := s!"
      PROGRAM K05REF
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      INTEGER REP
      PARAMETER (N = {N}, NREPS = {NREPS})
      DIMENSION X(N), Y(N), Z(N)
      CALL SIGNEL(X, N)
      CALL SIGNEL(Y, N)
      CALL SIGNEL(Z, N)
      DO 100 REP = 1, NREPS
        DO 5 I = 2, N
    5     X(I) = Z(I) * (Y(I) - X(I-1))
  100 CONTINUE
      WRITE(*,'(F0.6)') X(N)
      END
" ++ LivermoreDirect.signelSubroutineFortran

def kernel : LivermoreDirect.Kernel :=
  { name := "k05", program := program, fortranSrc := fortranSrc }

end LivermoreDirect.K05

-- ============================================================
-- § K07 — EQUATION OF STATE FRAGMENT
--   Canonical:  X(k) = U(k) + R*(Z(k) + R*Y(k))
--                    + T*(U(k+3) + R*(U(k+2) + R*U(k+1))
--                    +    T*(U(k+6) + Q*(U(k+5) + Q*U(k+4))))
-- ============================================================

namespace LivermoreDirect.K07

private def N : Int := 995
private def NREPS : Int := 2

open LivermoreDirect in
def program : Program where
  decls :=
    [ ("k", .int), ("rep", .int)
    , ("q", .float), ("r", .float), ("t", .float)
    , ("fuzz", .float), ("buzz", .float), ("fizz", .float) ]
  arrayDecls :=
    [ ("x", 1002, .float), ("y", 1002, .float), ("z", 1002, .float)
    , ("u", 1002, .float), ("spacer", 40, .float) ]
  body :=
    signelFill "spacer" 39 ;;
    loadSpacers [("q", 28), ("r", 30), ("t", 36)] ;;
    signelFill "y" 1001 ;; signelFill "z" 1001 ;; signelFill "u" 1001 ;;
    fortranDo "rep" (il 1) (il NREPS)
      ( fortranDo "k" (il 1) (il N)
          ( .farrWrite "x" (v "k")
              (fadd
                (fadd (fread "u" (v "k"))
                  (fmul (v "r") (fadd (fread "z" (v "k"))
                                      (fmul (v "r") (fread "y" (v "k"))))))
                (fmul (v "t")
                  (fadd
                    (fadd (fread "u" (iadd (v "k") (il 3)))
                      (fmul (v "r")
                        (fadd (fread "u" (iadd (v "k") (il 2)))
                              (fmul (v "r") (fread "u" (iadd (v "k") (il 1)))))))
                    (fmul (v "t")
                      (fadd (fread "u" (iadd (v "k") (il 6)))
                        (fmul (v "q")
                          (fadd (fread "u" (iadd (v "k") (il 5)))
                                (fmul (v "q") (fread "u" (iadd (v "k") (il 4))))))))))) ) ) ;;
    .printFloat (fread "x" (il 1)) ;; .printString "\n"

def fortranSrc : String :=
  let loads := LivermoreDirect.loadSpacersFortran [("Q", 28), ("R", 30), ("T", 36)]
  s!"
      PROGRAM K07REF
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      INTEGER REP
      PARAMETER (N = {N}, NREPS = {NREPS})
      DIMENSION X(1001), Y(1001), Z(1001), U(1001), SPACER(39)
      CALL SIGNEL(SPACER, 39)
{loads}      CALL SIGNEL(Y, 1001)
      CALL SIGNEL(Z, 1001)
      CALL SIGNEL(U, 1001)
      DO 100 REP = 1, NREPS
        DO 7 K = 1, N
        X(K) = U(K) + R*(Z(K) + R*Y(K)) +
     1         T*(U(K+3) + R*(U(K+2) + R*U(K+1)) +
     2         T*(U(K+6) + Q*(U(K+5) + Q*U(K+4))))
    7   CONTINUE
  100 CONTINUE
      WRITE(*,'(F0.6)') X(1)
      END
" ++ LivermoreDirect.signelSubroutineFortran

def kernel : LivermoreDirect.Kernel :=
  { name := "k07", program := program, fortranSrc := fortranSrc }

end LivermoreDirect.K07

-- ============================================================
-- § K11 — FIRST SUM (PARTIAL SUMS)
--   Canonical:  X(1) = Y(1); X(k) = X(k-1) + Y(k)  for k=2..n
-- ============================================================

namespace LivermoreDirect.K11

private def N : Int := 1001
private def NREPS : Int := 2

open LivermoreDirect in
def program : Program where
  decls := [ ("k", .int), ("rep", .int), ("fuzz", .float), ("buzz", .float), ("fizz", .float) ]
  arrayDecls := [ ("x", 1002, .float), ("y", 1002, .float) ]
  body :=
    signelFill "y" N ;;
    fortranDo "rep" (il 1) (il NREPS)
      ( .farrWrite "x" (il 1) (fread "y" (il 1)) ;;
        fortranDo "k" (il 2) (il N)
          ( .farrWrite "x" (v "k")
              (fadd (fread "x" (isub (v "k") (il 1))) (fread "y" (v "k"))) ) ) ;;
    .printFloat (fread "x" (il N)) ;; .printString "\n"

def fortranSrc : String := s!"
      PROGRAM K11REF
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      INTEGER REP
      PARAMETER (N = {N}, NREPS = {NREPS})
      DIMENSION X(N), Y(N)
      CALL SIGNEL(Y, N)
      DO 100 REP = 1, NREPS
        X(1) = Y(1)
        DO 11 K = 2, N
   11     X(K) = X(K-1) + Y(K)
  100 CONTINUE
      WRITE(*,'(F0.6)') X(N)
      END
" ++ LivermoreDirect.signelSubroutineFortran

def kernel : LivermoreDirect.Kernel :=
  { name := "k11", program := program, fortranSrc := fortranSrc }

end LivermoreDirect.K11

-- ============================================================
-- § K12 — FIRST DIFFERENCE
--   Canonical: X(k) = Y(k+1) - Y(k)  for k=1..n  (n=1000)
-- ============================================================

namespace LivermoreDirect.K12

private def N : Int := 1000
private def NREPS : Int := 2

open LivermoreDirect in
def program : Program where
  decls := [ ("k", .int), ("rep", .int), ("fuzz", .float), ("buzz", .float), ("fizz", .float) ]
  arrayDecls := [ ("x", 1001, .float), ("y", 1002, .float) ]
  body :=
    signelFill "y" 1001 ;;
    fortranDo "rep" (il 1) (il NREPS)
      ( fortranDo "k" (il 1) (il N)
          ( .farrWrite "x" (v "k")
              (fsub (fread "y" (iadd (v "k") (il 1))) (fread "y" (v "k"))) ) ) ;;
    .printFloat (fread "x" (il 1)) ;; .printString "\n"

def fortranSrc : String := s!"
      PROGRAM K12REF
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      INTEGER REP
      PARAMETER (N = {N}, NREPS = {NREPS})
      DIMENSION X(N), Y(1001)
      CALL SIGNEL(Y, 1001)
      DO 100 REP = 1, NREPS
        DO 12 K = 1, N
   12     X(K) = Y(K+1) - Y(K)
  100 CONTINUE
      WRITE(*,'(F0.6)') X(1)
      END
" ++ LivermoreDirect.signelSubroutineFortran

def kernel : LivermoreDirect.Kernel :=
  { name := "k12", program := program, fortranSrc := fortranSrc }

end LivermoreDirect.K12

-- ============================================================
-- § K22 — PLANCKIAN DISTRIBUTION
--   Canonical (with the IF guard CARE'd out per netlib source):
--     U(N) = 0.99 * EXPMAX * V(N)
--     DO 22 k = 1, N
--       Y(k) = U(k) / V(k)
--       W(k) = X(k) / (EXP(Y(k)) - 1.0)
-- ============================================================

namespace LivermoreDirect.K22

private def N : Int := 1001
private def NREPS : Int := 2

open LivermoreDirect in
def program : Program where
  decls :=
    [ ("k", .int), ("rep", .int), ("expmax", .float), ("fw", .float)
    , ("fuzz", .float), ("buzz", .float), ("fizz", .float) ]
  arrayDecls :=
    [ ("u", 1002, .float), ("v", 1002, .float), ("w", 1002, .float)
    , ("x", 1002, .float), ("y", 1002, .float), ("spacer", 40, .float) ]
  body :=
    signelFill "spacer" 39 ;;
    loadSpacers [("expmax", 26)] ;;
    .fassign "fw" (fl 1.0) ;;
    .fassign "expmax" (fl 20.0) ;;       -- canonical line: EXPMAX = 20.0d0 (lloops.f:5483)
    signelFill "u" N ;; signelFill "v" N ;; signelFill "w" N ;;
    signelFill "x" N ;; signelFill "y" N ;;
    -- U(N) = 0.99 * EXPMAX * V(N)
    .farrWrite "u" (il N)
      (fmul (fmul (fl 0.99) (v "expmax")) (fread "v" (il N))) ;;
    fortranDo "rep" (il 1) (il NREPS)
      ( fortranDo "k" (il 1) (il N)
          ( .farrWrite "y" (v "k") (fdiv (fread "u" (v "k")) (fread "v" (v "k"))) ;;
            .farrWrite "w" (v "k")
              (fdiv (fread "x" (v "k"))
                    (fsub (.floatUnary .exp (fread "y" (v "k"))) (v "fw"))) ) ) ;;
    .printFloat (fread "w" (il 51)) ;; .printString "\n"

def fortranSrc : String := s!"
      PROGRAM K22REF
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      INTEGER REP
      PARAMETER (N = {N}, NREPS = {NREPS})
      DIMENSION U(N), V(N), W(N), X(N), Y(N), SPACER(39)
      CALL SIGNEL(SPACER, 39)
      EXPMAX = 20.0D0
      FW = 1.0D0
      CALL SIGNEL(U, N)
      CALL SIGNEL(V, N)
      CALL SIGNEL(W, N)
      CALL SIGNEL(X, N)
      CALL SIGNEL(Y, N)
      U(N) = 0.99D0 * EXPMAX * V(N)
      DO 100 REP = 1, NREPS
        DO 22 K = 1, N
          Y(K) = U(K)/V(K)
   22     W(K) = X(K)/(EXP(Y(K)) - FW)
  100 CONTINUE
      WRITE(*,'(F0.6)') W(51)
      END
" ++ LivermoreDirect.signelSubroutineFortran

def kernel : LivermoreDirect.Kernel :=
  { name := "k22", program := program, fortranSrc := fortranSrc }

end LivermoreDirect.K22

-- ============================================================
-- § K24 — FIND LOCATION OF FIRST MINIMUM
--   Canonical:  X(n/2) = -1e10
--               m = 1; DO 24 k=2,n  IF(X(k) < X(m)) m = k
--   Observable: m  (and X(m)).  Array reads pulled into scalar
--   temps so the comparison itself reads no array (avoids the
--   checker's checkBoolExprNoArrRead constraint).
-- ============================================================

namespace LivermoreDirect.K24

private def N : Int := 1001
private def NREPS : Int := 2

open LivermoreDirect in
def program : Program where
  decls :=
    [ ("k", .int), ("rep", .int), ("m", .int)
    , ("xk", .float), ("xm", .float)
    , ("fuzz", .float), ("buzz", .float), ("fizz", .float) ]
  arrayDecls := [ ("x", 1002, .float) ]
  body :=
    signelFill "x" N ;;
    .farrWrite "x" (il (N/2)) (fl (-1.0e10)) ;;
    fortranDo "rep" (il 1) (il NREPS)
      ( .assign "m" (il 1) ;;
        fortranDo "k" (il 2) (il N)
          ( .fassign "xk" (fread "x" (v "k")) ;;
            .fassign "xm" (fread "x" (v "m")) ;;
            .ite (.fcmp .flt (v "xk") (v "xm"))
              (.assign "m" (v "k")) .skip ) ) ;;
    .printInt   (v "m")            ;; .printString "\n"

def fortranSrc : String := s!"
      PROGRAM K24REF
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      INTEGER REP
      PARAMETER (N = {N}, NREPS = {NREPS})
      DIMENSION X(N)
      CALL SIGNEL(X, N)
      X(N/2) = -1.0D10
      DO 100 REP = 1, NREPS
        M = 1
        DO 24 K = 2, N
          IF (X(K) .LT. X(M)) M = K
   24   CONTINUE
  100 CONTINUE
      WRITE(*,'(I0)') M
      END
" ++ LivermoreDirect.signelSubroutineFortran

def kernel : LivermoreDirect.Kernel :=
  { name := "k24", program := program, fortranSrc := fortranSrc }

end LivermoreDirect.K24

-- ============================================================
-- § Helpers for column-major 2-D / 3-D index flattening (Fortran convention).
-- ============================================================

namespace LivermoreDirect

/-- 2-D column-major index, 1-based: idx2(rows, i, k) = i + rows*(k-1). -/
def idx2 (rows : Int) (i k : SExpr) : SExpr :=
  iadd i (imul (il rows) (isub k (il 1)))

/-- 3-D column-major index: idx3(d1, d2, i, j, k) = i + d1*(j-1) + d1*d2*(k-1). -/
def idx3 (d1 d2 : Int) (i j k : SExpr) : SExpr :=
  iadd (iadd i (imul (il d1) (isub j (il 1)))) (imul (il (d1*d2)) (isub k (il 1)))

end LivermoreDirect

-- ============================================================
-- § K06 — GENERAL LINEAR RECURRENCE
--   Canonical:  DO 6 i=2,n: W(i)=0.01; DO 6 k=1,i-1: W(i)=W(i)+B(i,k)*W(i-k)
--   B is 2-D (64,64) flattened column-major.
-- ============================================================

namespace LivermoreDirect.K06

private def N : Int := 64
private def NREPS : Int := 2

open LivermoreDirect in
def program : Program where
  decls :=
    [ ("i", .int), ("k", .int), ("rep", .int)
    , ("fuzz", .float), ("buzz", .float), ("fizz", .float) ]
  arrayDecls := [ ("w", 65, .float), ("b", 64*64+1, .float) ]
  body :=
    signelFill "b" (64*64) ;;
    fortranDo "rep" (il 1) (il NREPS)
      ( fortranDo "i" (il 2) (il N)
          ( .farrWrite "w" (v "i") (fl 0.01) ;;
            fortranDo "k" (il 1) (isub (v "i") (il 1))
              ( .farrWrite "w" (v "i")
                  (fadd (fread "w" (v "i"))
                    (fmul (fread "b" (idx2 64 (v "i") (v "k")))
                          (fread "w" (isub (v "i") (v "k"))))) ) ) ) ;;
    .printFloat (fread "w" (il N)) ;; .printString "\n"

def fortranSrc : String := s!"
      PROGRAM K06REF
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      INTEGER REP
      PARAMETER (N = {N}, NREPS = {NREPS})
      DIMENSION W(N), B(N,N)
      CALL SIGNEL(B, N*N)
      DO 100 REP = 1, NREPS
        DO 6 I = 2, N
          W(I) = 0.01D0
          DO 6 K = 1, I-1
            W(I) = W(I) + B(I,K) * W(I-K)
    6   CONTINUE
  100 CONTINUE
      WRITE(*,'(F0.6)') W(N)
      END
" ++ LivermoreDirect.signelSubroutineFortran

def kernel : LivermoreDirect.Kernel :=
  { name := "k06", program := program, fortranSrc := fortranSrc }

end LivermoreDirect.K06

-- ============================================================
-- § K09 — INTEGRATE PREDICTORS
--   PX(1,k) = DM28*PX(13,k) + DM27*PX(12,k) + ... + DM22*PX(7,k)
--           + C0*(PX(5,k)+PX(6,k)) + PX(3,k)
--   PX is 2-D (25,101).
-- ============================================================

namespace LivermoreDirect.K09

private def N : Int := 101
private def NREPS : Int := 2

open LivermoreDirect in
private def pxij (i : Int) (k : SExpr) : SExpr := idx2 25 (il i) k

open LivermoreDirect in
def program : Program where
  decls :=
    [ ("k", .int), ("rep", .int)
    , ("c0", .float), ("dm22", .float), ("dm23", .float), ("dm24", .float)
    , ("dm25", .float), ("dm26", .float), ("dm27", .float), ("dm28", .float)
    , ("fuzz", .float), ("buzz", .float), ("fizz", .float) ]
  arrayDecls := [ ("px", 25*101+1, .float), ("spacer", 40, .float) ]
  body :=
    signelFill "spacer" 39 ;;
    loadSpacers [("c0", 12), ("dm22", 16), ("dm23", 17), ("dm24", 18),
                 ("dm25", 19), ("dm26", 20), ("dm27", 21), ("dm28", 22)] ;;
    signelFill "px" (25*101) ;;
    fortranDo "rep" (il 1) (il NREPS)
      ( fortranDo "k" (il 1) (il N)
          ( .farrWrite "px" (pxij 1 (v "k"))
              (fadd
                (fadd
                  (fadd
                    (fadd (fmul (v "dm28") (fread "px" (pxij 13 (v "k"))))
                          (fmul (v "dm27") (fread "px" (pxij 12 (v "k")))))
                    (fadd (fmul (v "dm26") (fread "px" (pxij 11 (v "k"))))
                          (fmul (v "dm25") (fread "px" (pxij 10 (v "k"))))))
                  (fadd
                    (fadd (fmul (v "dm24") (fread "px" (pxij 9 (v "k"))))
                          (fmul (v "dm23") (fread "px" (pxij 8 (v "k")))))
                    (fmul (v "dm22") (fread "px" (pxij 7 (v "k"))))))
                (fadd
                  (fmul (v "c0")
                    (fadd (fread "px" (pxij 5 (v "k"))) (fread "px" (pxij 6 (v "k")))))
                  (fread "px" (pxij 3 (v "k"))))) ) ) ;;
    .printFloat (fread "px" (pxij 1 (il 1))) ;; .printString "\n"

def fortranSrc : String :=
  let loads := LivermoreDirect.loadSpacersFortran
    [("C0", 12), ("DM22", 16), ("DM23", 17), ("DM24", 18),
     ("DM25", 19), ("DM26", 20), ("DM27", 21), ("DM28", 22)]
  s!"
      PROGRAM K09REF
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      INTEGER REP
      PARAMETER (N = {N}, NREPS = {NREPS})
      DIMENSION PX(25,N), SPACER(39)
      CALL SIGNEL(SPACER, 39)
{loads}      CALL SIGNEL(PX, 25*N)
      DO 100 REP = 1, NREPS
        DO 9 K = 1, N
        PX(1,K) = DM28*PX(13,K) + DM27*PX(12,K) + DM26*PX(11,K) +
     1            DM25*PX(10,K) + DM24*PX(9,K)  + DM23*PX(8,K)  +
     2            DM22*PX(7,K)  + C0*(PX(5,K) + PX(6,K)) + PX(3,K)
    9   CONTINUE
  100 CONTINUE
      WRITE(*,'(F0.6)') PX(1,1)
      END
" ++ LivermoreDirect.signelSubroutineFortran

def kernel : LivermoreDirect.Kernel :=
  { name := "k09", program := program, fortranSrc := fortranSrc }

end LivermoreDirect.K09

-- ============================================================
-- § K10 — DIFFERENCE PREDICTORS
--   AR/BR/CR cascade through PX/CX rows 5..13, writing PX(14,k) at end.
-- ============================================================

namespace LivermoreDirect.K10

private def N : Int := 101
private def NREPS : Int := 2

open LivermoreDirect in
private def pxij (i : Int) (k : SExpr) : SExpr := idx2 25 (il i) k

open LivermoreDirect in
def program : Program where
  decls :=
    [ ("k", .int), ("rep", .int)
    , ("ar", .float), ("br", .float), ("cr", .float)
    , ("fuzz", .float), ("buzz", .float), ("fizz", .float) ]
  arrayDecls :=
    [ ("px", 25*101+1, .float), ("cx", 25*101+1, .float) ]
  body :=
    signelFill "px" (25*101) ;;
    signelFill "cx" (25*101) ;;
    fortranDo "rep" (il 1) (il NREPS)
      ( fortranDo "k" (il 1) (il N)
          ( .fassign "ar" (fread "cx" (pxij 5 (v "k")))           ;;
            .fassign "br" (fsub (v "ar") (fread "px" (pxij 5 (v "k"))))  ;;
            .farrWrite "px" (pxij 5 (v "k")) (v "ar") ;;
            .fassign "cr" (fsub (v "br") (fread "px" (pxij 6 (v "k"))))  ;;
            .farrWrite "px" (pxij 6 (v "k")) (v "br") ;;
            .fassign "ar" (fsub (v "cr") (fread "px" (pxij 7 (v "k"))))  ;;
            .farrWrite "px" (pxij 7 (v "k")) (v "cr") ;;
            .fassign "br" (fsub (v "ar") (fread "px" (pxij 8 (v "k"))))  ;;
            .farrWrite "px" (pxij 8 (v "k")) (v "ar") ;;
            .fassign "cr" (fsub (v "br") (fread "px" (pxij 9 (v "k"))))  ;;
            .farrWrite "px" (pxij 9 (v "k")) (v "br") ;;
            .fassign "ar" (fsub (v "cr") (fread "px" (pxij 10 (v "k")))) ;;
            .farrWrite "px" (pxij 10 (v "k")) (v "cr") ;;
            .fassign "br" (fsub (v "ar") (fread "px" (pxij 11 (v "k")))) ;;
            .farrWrite "px" (pxij 11 (v "k")) (v "ar") ;;
            .fassign "cr" (fsub (v "br") (fread "px" (pxij 12 (v "k")))) ;;
            .farrWrite "px" (pxij 12 (v "k")) (v "br") ;;
            .farrWrite "px" (pxij 14 (v "k"))
              (fsub (v "cr") (fread "px" (pxij 13 (v "k")))) ;;
            .farrWrite "px" (pxij 13 (v "k")) (v "cr") ) ) ;;
    .printFloat (fread "px" (pxij 14 (il 1))) ;; .printString "\n"

def fortranSrc : String := s!"
      PROGRAM K10REF
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      INTEGER REP
      PARAMETER (N = {N}, NREPS = {NREPS})
      DIMENSION PX(25,N), CX(25,N)
      CALL SIGNEL(PX, 25*N)
      CALL SIGNEL(CX, 25*N)
      DO 100 REP = 1, NREPS
        DO 10 K = 1, N
          AR      =      CX(5,K)
          BR      = AR - PX(5,K)
          PX(5,K) = AR
          CR      = BR - PX(6,K)
          PX(6,K) = BR
          AR      = CR - PX(7,K)
          PX(7,K) = CR
          BR      = AR - PX(8,K)
          PX(8,K) = AR
          CR      = BR - PX(9,K)
          PX(9,K) = BR
          AR      = CR - PX(10,K)
          PX(10,K)= CR
          BR      = AR - PX(11,K)
          PX(11,K)= AR
          CR      = BR - PX(12,K)
          PX(12,K)= BR
          PX(14,K)= CR - PX(13,K)
          PX(13,K)= CR
   10   CONTINUE
  100 CONTINUE
      WRITE(*,'(F0.6)') PX(14,1)
      END
" ++ LivermoreDirect.signelSubroutineFortran

def kernel : LivermoreDirect.Kernel :=
  { name := "k10", program := program, fortranSrc := fortranSrc }

end LivermoreDirect.K10

-- ============================================================
-- § K21 — MATRIX × MATRIX
--   DO 21 k=1,25; DO 21 i=1,25; DO 21 j=1,n
--     PX(i,j) = PX(i,j) + VY(i,k) * CX(k,j)
-- ============================================================

namespace LivermoreDirect.K21

private def N : Int := 25
private def NREPS : Int := 2

open LivermoreDirect in
def program : Program where
  decls :=
    [ ("i", .int), ("j", .int), ("k", .int), ("rep", .int)
    , ("fuzz", .float), ("buzz", .float), ("fizz", .float) ]
  arrayDecls :=
    [ ("px", 25*101+1, .float), ("vy", 101*25+1, .float), ("cx", 25*101+1, .float) ]
  body :=
    signelFill "px" (25*101) ;;
    signelFill "vy" (101*25) ;;
    signelFill "cx" (25*101) ;;
    fortranDo "rep" (il 1) (il NREPS)
      ( fortranDo "k" (il 1) (il 25)
          ( fortranDo "i" (il 1) (il 25)
              ( fortranDo "j" (il 1) (il N)
                  ( .farrWrite "px" (idx2 25 (v "i") (v "j"))
                      (fadd (fread "px" (idx2 25 (v "i") (v "j")))
                        (fmul (fread "vy" (idx2 101 (v "i") (v "k")))
                              (fread "cx" (idx2 25 (v "k") (v "j"))))) ) ) ) ) ;;
    .printFloat (fread "px" (idx2 25 (il 1) (il 1))) ;; .printString "\n"

def fortranSrc : String := s!"
      PROGRAM K21REF
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      INTEGER REP
      PARAMETER (N = {N}, NREPS = {NREPS})
      DIMENSION PX(25,101), VY(101,25), CX(25,101)
      CALL SIGNEL(PX, 25*101)
      CALL SIGNEL(VY, 101*25)
      CALL SIGNEL(CX, 25*101)
      DO 100 REP = 1, NREPS
        DO 21 K = 1, 25
        DO 21 I = 1, 25
        DO 21 J = 1, N
        PX(I,J) = PX(I,J) + VY(I,K) * CX(K,J)
   21   CONTINUE
  100 CONTINUE
      WRITE(*,'(F0.6)') PX(1,1)
      END
" ++ LivermoreDirect.signelSubroutineFortran

def kernel : LivermoreDirect.Kernel :=
  { name := "k21", program := program, fortranSrc := fortranSrc }

end LivermoreDirect.K21

-- ============================================================
-- § K23 — 2-D IMPLICIT HYDRODYNAMICS
--   ZA(k,j) = ZA(k,j) + fw*(QA - ZA(k,j))   with QA composed of
--   eight stencil reads of ZA, ZR, ZB, ZU, ZV, ZZ.
-- ============================================================

namespace LivermoreDirect.K23

private def N : Int := 101
private def NREPS : Int := 2

open LivermoreDirect in
def program : Program where
  decls :=
    [ ("j", .int), ("k", .int), ("rep", .int)
    , ("fw", .float), ("qa", .float)
    , ("fuzz", .float), ("buzz", .float), ("fizz", .float) ]
  arrayDecls :=
    [ ("za", 101*7+1, .float), ("zb", 101*7+1, .float), ("zp", 101*7+1, .float)
    , ("zr", 101*7+1, .float), ("zu", 101*7+1, .float), ("zv", 101*7+1, .float)
    , ("zz", 101*7+1, .float) ]
  body :=
    signelFill "za" (101*7) ;; signelFill "zb" (101*7) ;; signelFill "zp" (101*7) ;;
    signelFill "zr" (101*7) ;; signelFill "zu" (101*7) ;; signelFill "zv" (101*7) ;;
    signelFill "zz" (101*7) ;;
    .fassign "fw" (fl 0.175) ;;
    fortranDo "rep" (il 1) (il NREPS)
      ( fortranDo "j" (il 2) (il 6)
          ( fortranDo "k" (il 2) (il N)
              ( .fassign "qa"
                  (fadd (fadd (fadd (fadd
                    (fmul (fread "za" (idx2 101 (v "k") (iadd (v "j") (il 1))))
                          (fread "zr" (idx2 101 (v "k") (v "j"))))
                    (fmul (fread "za" (idx2 101 (v "k") (isub (v "j") (il 1))))
                          (fread "zb" (idx2 101 (v "k") (v "j")))))
                    (fmul (fread "za" (idx2 101 (iadd (v "k") (il 1)) (v "j")))
                          (fread "zu" (idx2 101 (v "k") (v "j")))))
                    (fmul (fread "za" (idx2 101 (isub (v "k") (il 1)) (v "j")))
                          (fread "zv" (idx2 101 (v "k") (v "j")))))
                    (fread "zz" (idx2 101 (v "k") (v "j"))) ) ;;
                .farrWrite "za" (idx2 101 (v "k") (v "j"))
                  (fadd (fread "za" (idx2 101 (v "k") (v "j")))
                        (fmul (v "fw")
                          (fsub (v "qa") (fread "za" (idx2 101 (v "k") (v "j")))))) ) ) ) ;;
    .printFloat (fread "za" (idx2 101 (il 51) (il 4))) ;; .printString "\n"

def fortranSrc : String := s!"
      PROGRAM K23REF
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      INTEGER REP
      PARAMETER (N = {N}, NREPS = {NREPS})
      DIMENSION ZA(101,7), ZB(101,7), ZP(101,7), ZR(101,7),
     1          ZU(101,7), ZV(101,7), ZZ(101,7)
      CALL SIGNEL(ZA, 101*7)
      CALL SIGNEL(ZB, 101*7)
      CALL SIGNEL(ZP, 101*7)
      CALL SIGNEL(ZR, 101*7)
      CALL SIGNEL(ZU, 101*7)
      CALL SIGNEL(ZV, 101*7)
      CALL SIGNEL(ZZ, 101*7)
      FW = 0.175D0
      DO 100 REP = 1, NREPS
        DO 23 J = 2, 6
        DO 23 K = 2, N
        QA = ZA(K,J+1)*ZR(K,J) + ZA(K,J-1)*ZB(K,J) +
     1       ZA(K+1,J)*ZU(K,J) + ZA(K-1,J)*ZV(K,J) + ZZ(K,J)
   23   ZA(K,J) = ZA(K,J) + FW*(QA - ZA(K,J))
  100 CONTINUE
      WRITE(*,'(F0.6)') ZA(51,4)
      END
" ++ LivermoreDirect.signelSubroutineFortran

def kernel : LivermoreDirect.Kernel :=
  { name := "k23", program := program, fortranSrc := fortranSrc }

end LivermoreDirect.K23

-- ============================================================
-- § K02 — ICCG EXCERPT
--   Halving-II outer loop + stride-2 inner loop.
--   X(i) = X(k) - V(k)*X(k-1) - V(k+1)*X(k+1)
-- ============================================================

namespace LivermoreDirect.K02

private def N : Int := 1001
private def NREPS : Int := 2

open LivermoreDirect in
def program : Program where
  decls :=
    [ ("k", .int), ("i", .int), ("ii", .int), ("ipnt", .int), ("ipntp", .int)
    , ("rep", .int)
    , ("fuzz", .float), ("buzz", .float), ("fizz", .float) ]
  arrayDecls := [ ("x", 2003, .float), ("v", 2003, .float) ]
  body :=
    signelFill "x" 2002 ;; signelFill "v" 2002 ;;
    fortranDo "rep" (il 1) (il NREPS)
      ( .assign "ii"    (il N) ;;
        .assign "ipntp" (il 0) ;;
        -- outer: while II > 1
        .loop (.cmp .lt (il 1) (v "ii"))
          ( .assign "ipnt"  (v "ipntp") ;;
            .assign "ipntp" (iadd (v "ipntp") (v "ii")) ;;
            .assign "ii"    (.bin .div (v "ii") (il 2)) ;;
            .assign "i"     (iadd (v "ipntp") (il 1)) ;;
            -- inner: k = ipnt+2, ipntp, step 2
            .assign "k" (iadd (v "ipnt") (il 2)) ;;
            .loop (.cmp .le (v "k") (v "ipntp"))
              ( .assign "i" (iadd (v "i") (il 1)) ;;
                .farrWrite "x" (v "i")
                  (fsub (fsub (fread "x" (v "k"))
                          (fmul (fread "v" (v "k"))
                                (fread "x" (isub (v "k") (il 1)))))
                        (fmul (fread "v" (iadd (v "k") (il 1)))
                              (fread "x" (iadd (v "k") (il 1))))) ;;
                .assign "k" (iadd (v "k") (il 2)) ) ) ) ;;
    .printFloat (fread "x" (il N)) ;; .printString "\n"

def fortranSrc : String := s!"
      PROGRAM K02REF
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      INTEGER REP
      PARAMETER (N = {N}, NREPS = {NREPS})
      DIMENSION X(2002), V(2002)
      CALL SIGNEL(X, 2002)
      CALL SIGNEL(V, 2002)
      DO 100 REP = 1, NREPS
        II = N
        IPNTP = 0
  222   IPNT = IPNTP
        IPNTP = IPNTP + II
        II = II/2
        I = IPNTP+1
        DO 2 K = IPNT+2, IPNTP, 2
          I = I + 1
    2     X(I) = X(K) - V(K)*X(K-1) - V(K+1)*X(K+1)
        IF (II .GT. 1) GOTO 222
  100 CONTINUE
      WRITE(*,'(F0.6)') X(N)
      END
" ++ LivermoreDirect.signelSubroutineFortran

def kernel : LivermoreDirect.Kernel :=
  { name := "k02", program := program, fortranSrc := fortranSrc }

end LivermoreDirect.K02

-- ============================================================
-- § K18 — 2-D EXPLICIT HYDRODYNAMICS
--   3 phases over k=2..6, j=2..n   (n=101)
-- ============================================================

namespace LivermoreDirect.K18

private def N : Int := 101
private def NREPS : Int := 2

open LivermoreDirect in
def program : Program where
  decls :=
    [ ("j", .int), ("k", .int), ("rep", .int)
    , ("s", .float), ("t", .float)
    , ("fuzz", .float), ("buzz", .float), ("fizz", .float) ]
  arrayDecls :=
    [ ("za", 101*7+1, .float), ("zb", 101*7+1, .float), ("zp", 101*7+1, .float)
    , ("zq", 101*7+1, .float), ("zr", 101*7+1, .float), ("zm", 101*7+1, .float)
    , ("zu", 101*7+1, .float), ("zv", 101*7+1, .float), ("zz", 101*7+1, .float) ]
  body :=
    signelFill "za" (101*7) ;; signelFill "zb" (101*7) ;; signelFill "zp" (101*7) ;;
    signelFill "zq" (101*7) ;; signelFill "zr" (101*7) ;; signelFill "zm" (101*7) ;;
    signelFill "zu" (101*7) ;; signelFill "zv" (101*7) ;; signelFill "zz" (101*7) ;;
    .fassign "t" (fl 0.0037) ;;
    .fassign "s" (fl 0.0041) ;;
    fortranDo "rep" (il 1) (il NREPS)
      ( -- Phase 1: ZA, ZB
        fortranDo "k" (il 2) (il 6)
          ( fortranDo "j" (il 2) (il N)
              ( .farrWrite "za" (idx2 101 (v "j") (v "k"))
                  (fdiv
                    (fmul
                      (fsub (fsub (fadd (fread "zp" (idx2 101 (isub (v "j") (il 1)) (iadd (v "k") (il 1))))
                                        (fread "zq" (idx2 101 (isub (v "j") (il 1)) (iadd (v "k") (il 1)))))
                                  (fread "zp" (idx2 101 (isub (v "j") (il 1)) (v "k"))))
                            (fread "zq" (idx2 101 (isub (v "j") (il 1)) (v "k"))))
                      (fadd (fread "zr" (idx2 101 (v "j") (v "k")))
                            (fread "zr" (idx2 101 (isub (v "j") (il 1)) (v "k")))))
                    (fadd (fread "zm" (idx2 101 (isub (v "j") (il 1)) (v "k")))
                          (fread "zm" (idx2 101 (isub (v "j") (il 1)) (iadd (v "k") (il 1)))))) ;;
                .farrWrite "zb" (idx2 101 (v "j") (v "k"))
                  (fdiv
                    (fmul
                      (fsub (fsub (fadd (fread "zp" (idx2 101 (isub (v "j") (il 1)) (v "k")))
                                        (fread "zq" (idx2 101 (isub (v "j") (il 1)) (v "k"))))
                                  (fread "zp" (idx2 101 (v "j") (v "k"))))
                            (fread "zq" (idx2 101 (v "j") (v "k"))))
                      (fadd (fread "zr" (idx2 101 (v "j") (v "k")))
                            (fread "zr" (idx2 101 (v "j") (isub (v "k") (il 1))))))
                    (fadd (fread "zm" (idx2 101 (v "j") (v "k")))
                          (fread "zm" (idx2 101 (isub (v "j") (il 1)) (v "k"))))) ) ) ;;
        -- Phase 2: ZU, ZV
        fortranDo "k" (il 2) (il 6)
          ( fortranDo "j" (il 2) (il N)
              ( .farrWrite "zu" (idx2 101 (v "j") (v "k"))
                  (fadd (fread "zu" (idx2 101 (v "j") (v "k")))
                    (fmul (v "s")
                      (fadd (fadd (fadd
                        (fmul (fread "za" (idx2 101 (v "j") (v "k")))
                              (fsub (fread "zz" (idx2 101 (v "j") (v "k")))
                                    (fread "zz" (idx2 101 (iadd (v "j") (il 1)) (v "k")))))
                        (fmul (fsub (fl 0.0) (fread "za" (idx2 101 (isub (v "j") (il 1)) (v "k"))))
                              (fsub (fread "zz" (idx2 101 (v "j") (v "k")))
                                    (fread "zz" (idx2 101 (isub (v "j") (il 1)) (v "k"))))))
                        (fmul (fsub (fl 0.0) (fread "zb" (idx2 101 (v "j") (v "k"))))
                              (fsub (fread "zz" (idx2 101 (v "j") (v "k")))
                                    (fread "zz" (idx2 101 (v "j") (isub (v "k") (il 1)))))))
                        (fmul (fread "zb" (idx2 101 (v "j") (iadd (v "k") (il 1))))
                              (fsub (fread "zz" (idx2 101 (v "j") (v "k")))
                                    (fread "zz" (idx2 101 (v "j") (iadd (v "k") (il 1))))))))) ;;
                .farrWrite "zv" (idx2 101 (v "j") (v "k"))
                  (fadd (fread "zv" (idx2 101 (v "j") (v "k")))
                    (fmul (v "s")
                      (fadd (fadd (fadd
                        (fmul (fread "za" (idx2 101 (v "j") (v "k")))
                              (fsub (fread "zr" (idx2 101 (v "j") (v "k")))
                                    (fread "zr" (idx2 101 (iadd (v "j") (il 1)) (v "k")))))
                        (fmul (fsub (fl 0.0) (fread "za" (idx2 101 (isub (v "j") (il 1)) (v "k"))))
                              (fsub (fread "zr" (idx2 101 (v "j") (v "k")))
                                    (fread "zr" (idx2 101 (isub (v "j") (il 1)) (v "k"))))))
                        (fmul (fsub (fl 0.0) (fread "zb" (idx2 101 (v "j") (v "k"))))
                              (fsub (fread "zr" (idx2 101 (v "j") (v "k")))
                                    (fread "zr" (idx2 101 (v "j") (isub (v "k") (il 1)))))))
                        (fmul (fread "zb" (idx2 101 (v "j") (iadd (v "k") (il 1))))
                              (fsub (fread "zr" (idx2 101 (v "j") (v "k")))
                                    (fread "zr" (idx2 101 (v "j") (iadd (v "k") (il 1))))))))) ) ) ;;
        -- Phase 3: ZR, ZZ
        fortranDo "k" (il 2) (il 6)
          ( fortranDo "j" (il 2) (il N)
              ( .farrWrite "zr" (idx2 101 (v "j") (v "k"))
                  (fadd (fread "zr" (idx2 101 (v "j") (v "k")))
                        (fmul (v "t") (fread "zu" (idx2 101 (v "j") (v "k"))))) ;;
                .farrWrite "zz" (idx2 101 (v "j") (v "k"))
                  (fadd (fread "zz" (idx2 101 (v "j") (v "k")))
                        (fmul (v "t") (fread "zv" (idx2 101 (v "j") (v "k"))))) ) ) ) ;;
    .printFloat (fread "zu" (idx2 101 (il 51) (il 4))) ;; .printString "\n"

def fortranSrc : String := s!"
      PROGRAM K18REF
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      INTEGER REP
      PARAMETER (N = {N}, NREPS = {NREPS})
      DIMENSION ZA(101,7), ZB(101,7), ZP(101,7), ZQ(101,7), ZR(101,7),
     1          ZM(101,7), ZU(101,7), ZV(101,7), ZZ(101,7)
      CALL SIGNEL(ZA, 101*7)
      CALL SIGNEL(ZB, 101*7)
      CALL SIGNEL(ZP, 101*7)
      CALL SIGNEL(ZQ, 101*7)
      CALL SIGNEL(ZR, 101*7)
      CALL SIGNEL(ZM, 101*7)
      CALL SIGNEL(ZU, 101*7)
      CALL SIGNEL(ZV, 101*7)
      CALL SIGNEL(ZZ, 101*7)
      T = 0.0037D0
      S = 0.0041D0
      DO 100 REP = 1, NREPS
        DO 70 K = 2, 6
        DO 70 J = 2, N
        ZA(J,K) = (ZP(J-1,K+1)+ZQ(J-1,K+1)-ZP(J-1,K)-ZQ(J-1,K))
     1          *(ZR(J,K)+ZR(J-1,K))/(ZM(J-1,K)+ZM(J-1,K+1))
        ZB(J,K) = (ZP(J-1,K)+ZQ(J-1,K)-ZP(J,K)-ZQ(J,K))
     1          *(ZR(J,K)+ZR(J,K-1))/(ZM(J,K)+ZM(J-1,K))
   70   CONTINUE
        DO 72 K = 2, 6
        DO 72 J = 2, N
        ZU(J,K) = ZU(J,K)+S*(ZA(J,K)*(ZZ(J,K)-ZZ(J+1,K))
     1                    -ZA(J-1,K)*(ZZ(J,K)-ZZ(J-1,K))
     2                    -ZB(J,K)*(ZZ(J,K)-ZZ(J,K-1))
     3                    +ZB(J,K+1)*(ZZ(J,K)-ZZ(J,K+1)))
        ZV(J,K) = ZV(J,K)+S*(ZA(J,K)*(ZR(J,K)-ZR(J+1,K))
     1                    -ZA(J-1,K)*(ZR(J,K)-ZR(J-1,K))
     2                    -ZB(J,K)*(ZR(J,K)-ZR(J,K-1))
     3                    +ZB(J,K+1)*(ZR(J,K)-ZR(J,K+1)))
   72   CONTINUE
        DO 75 K = 2, 6
        DO 75 J = 2, N
          ZR(J,K) = ZR(J,K) + T*ZU(J,K)
          ZZ(J,K) = ZZ(J,K) + T*ZV(J,K)
   75   CONTINUE
  100 CONTINUE
      WRITE(*,'(F0.6)') ZU(51,4)
      END
" ++ LivermoreDirect.signelSubroutineFortran

def kernel : LivermoreDirect.Kernel :=
  { name := "k18", program := program, fortranSrc := fortranSrc }

end LivermoreDirect.K18

-- ============================================================
-- § K04 — BANDED LINEAR EQUATIONS
--   Outer: k = 7, 1001, m  (m=497)
--   Inner: j = 5, n, 5
-- ============================================================

namespace LivermoreDirect.K04

private def N : Int := 1001
private def NREPS : Int := 2

open LivermoreDirect in
def program : Program where
  decls :=
    [ ("k", .int), ("j", .int), ("lw", .int), ("m", .int), ("rep", .int)
    , ("temp", .float)
    , ("fuzz", .float), ("buzz", .float), ("fizz", .float) ]
  arrayDecls := [ ("xz", 1502, .float), ("y", 1002, .float) ]
  body :=
    signelFill "xz" 1500 ;; signelFill "y" N ;;
    .assign "m" (il 497) ;;
    fortranDo "rep" (il 1) (il NREPS)
      ( .assign "k" (il 7) ;;
        .loop (.cmp .le (v "k") (il N))
          ( .assign "lw" (isub (v "k") (il 6)) ;;
            .fassign "temp" (fread "xz" (isub (v "k") (il 1))) ;;
            -- inner: j = 5, n, 5
            .assign "j" (il 5) ;;
            .loop (.cmp .le (v "j") (il N))
              ( .fassign "temp"
                  (fsub (v "temp") (fmul (fread "xz" (v "lw")) (fread "y" (v "j")))) ;;
                .assign "lw" (iadd (v "lw") (il 1)) ;;
                .assign "j"  (iadd (v "j")  (il 5)) ) ;;
            .farrWrite "xz" (isub (v "k") (il 1)) (fmul (fread "y" (il 5)) (v "temp")) ;;
            .assign "k" (iadd (v "k") (v "m")) ) ) ;;
    .printFloat (fread "xz" (il 6)) ;; .printString "\n"

def fortranSrc : String := s!"
      PROGRAM K04REF
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      INTEGER REP
      PARAMETER (N = {N}, NREPS = {NREPS})
      DIMENSION XZ(1500), Y(N)
      CALL SIGNEL(XZ, 1500)
      CALL SIGNEL(Y, N)
      M = 497
      DO 100 REP = 1, NREPS
        DO 404 K = 7, N, M
          LW = K - 6
          TEMP = XZ(K-1)
          DO 4 J = 5, N, 5
            TEMP = TEMP - XZ(LW) * Y(J)
    4       LW = LW + 1
          XZ(K-1) = Y(5) * TEMP
  404   CONTINUE
  100 CONTINUE
      WRITE(*,'(F0.6)') XZ(6)
      END
" ++ LivermoreDirect.signelSubroutineFortran

def kernel : LivermoreDirect.Kernel :=
  { name := "k04", program := program, fortranSrc := fortranSrc }

end LivermoreDirect.K04

-- ============================================================
-- § K08 — A.D.I. INTEGRATION   (3-D arrays U1/U2/U3 (5,101,2))
-- ============================================================

namespace LivermoreDirect.K08

private def N : Int := 100
private def NREPS : Int := 2
-- 3-D U?(5,101,2): flatten size 5*101*2 + 1 = 1011
private def U3SIZE : Nat := 5*101*2 + 1

open LivermoreDirect in
private def u3 (i j k : SExpr) : SExpr := idx3 5 101 i j k

open LivermoreDirect in
def program : Program where
  decls :=
    [ ("k", .int), ("kx", .int), ("ky", .int)
    , ("nl1", .int), ("nl2", .int), ("rep", .int)
    , ("fw", .float), ("a11", .float), ("a12", .float), ("a13", .float)
    , ("a21", .float), ("a22", .float), ("a23", .float)
    , ("a31", .float), ("a32", .float), ("a33", .float), ("sig", .float)
    , ("fuzz", .float), ("buzz", .float), ("fizz", .float) ]
  arrayDecls :=
    [ ("u1", U3SIZE, .float), ("u2", U3SIZE, .float), ("u3", U3SIZE, .float)
    , ("du1", 102, .float), ("du2", 102, .float), ("du3", 102, .float)
    , ("spacer", 40, .float) ]
  body :=
    signelFill "spacer" 39 ;;
    loadSpacers
      [ ("a11", 1), ("a12", 2), ("a13", 3)
      , ("a21", 4), ("a22", 5), ("a23", 6)
      , ("a31", 7), ("a32", 8), ("a33", 9), ("sig", 34) ] ;;
    signelFill "u1" (5*101*2) ;; signelFill "u2" (5*101*2) ;; signelFill "u3" (5*101*2) ;;
    .assign "nl1" (il 1) ;;
    .assign "nl2" (il 2) ;;
    .fassign "fw" (fl 2.0) ;;
    fortranDo "rep" (il 1) (il NREPS)
      ( fortranDo "kx" (il 2) (il 3)
          ( fortranDo "ky" (il 2) (il N)
              ( -- DU1(ky) = U1(kx,ky+1,nl1) - U1(kx,ky-1,nl1)
                .farrWrite "du1" (v "ky")
                  (fsub (fread "u1" (u3 (v "kx") (iadd (v "ky") (il 1)) (v "nl1")))
                        (fread "u1" (u3 (v "kx") (isub (v "ky") (il 1)) (v "nl1")))) ;;
                .farrWrite "du2" (v "ky")
                  (fsub (fread "u2" (u3 (v "kx") (iadd (v "ky") (il 1)) (v "nl1")))
                        (fread "u2" (u3 (v "kx") (isub (v "ky") (il 1)) (v "nl1")))) ;;
                .farrWrite "du3" (v "ky")
                  (fsub (fread "u3" (u3 (v "kx") (iadd (v "ky") (il 1)) (v "nl1")))
                        (fread "u3" (u3 (v "kx") (isub (v "ky") (il 1)) (v "nl1")))) ;;
                -- U1(kx,ky,nl2) = U1(kx,ky,nl1) + A11*DU1 + A12*DU2 + A13*DU3 +
                --                 SIG*(U1(kx+1,ky,nl1) - fw*U1(kx,ky,nl1) + U1(kx-1,ky,nl1))
                .farrWrite "u1" (u3 (v "kx") (v "ky") (v "nl2"))
                  (fadd (fadd (fadd (fadd
                    (fread "u1" (u3 (v "kx") (v "ky") (v "nl1")))
                    (fmul (v "a11") (fread "du1" (v "ky"))))
                    (fmul (v "a12") (fread "du2" (v "ky"))))
                    (fmul (v "a13") (fread "du3" (v "ky"))))
                    (fmul (v "sig")
                      (fadd (fsub (fread "u1" (u3 (iadd (v "kx") (il 1)) (v "ky") (v "nl1")))
                                  (fmul (v "fw") (fread "u1" (u3 (v "kx") (v "ky") (v "nl1")))))
                            (fread "u1" (u3 (isub (v "kx") (il 1)) (v "ky") (v "nl1")))))) ;;
                .farrWrite "u2" (u3 (v "kx") (v "ky") (v "nl2"))
                  (fadd (fadd (fadd (fadd
                    (fread "u2" (u3 (v "kx") (v "ky") (v "nl1")))
                    (fmul (v "a21") (fread "du1" (v "ky"))))
                    (fmul (v "a22") (fread "du2" (v "ky"))))
                    (fmul (v "a23") (fread "du3" (v "ky"))))
                    (fmul (v "sig")
                      (fadd (fsub (fread "u2" (u3 (iadd (v "kx") (il 1)) (v "ky") (v "nl1")))
                                  (fmul (v "fw") (fread "u2" (u3 (v "kx") (v "ky") (v "nl1")))))
                            (fread "u2" (u3 (isub (v "kx") (il 1)) (v "ky") (v "nl1")))))) ;;
                .farrWrite "u3" (u3 (v "kx") (v "ky") (v "nl2"))
                  (fadd (fadd (fadd (fadd
                    (fread "u3" (u3 (v "kx") (v "ky") (v "nl1")))
                    (fmul (v "a31") (fread "du1" (v "ky"))))
                    (fmul (v "a32") (fread "du2" (v "ky"))))
                    (fmul (v "a33") (fread "du3" (v "ky"))))
                    (fmul (v "sig")
                      (fadd (fsub (fread "u3" (u3 (iadd (v "kx") (il 1)) (v "ky") (v "nl1")))
                                  (fmul (v "fw") (fread "u3" (u3 (v "kx") (v "ky") (v "nl1")))))
                            (fread "u3" (u3 (isub (v "kx") (il 1)) (v "ky") (v "nl1")))))) ) ) ) ;;
    .printFloat (fread "u1" (u3 (il 2) (il 2) (il 2))) ;; .printString "\n"

def fortranSrc : String :=
  let loads := LivermoreDirect.loadSpacersFortran
    [("A11", 1), ("A12", 2), ("A13", 3),
     ("A21", 4), ("A22", 5), ("A23", 6),
     ("A31", 7), ("A32", 8), ("A33", 9), ("SIG", 34)]
  s!"
      PROGRAM K08REF
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      INTEGER REP
      PARAMETER (N = {N}, NREPS = {NREPS})
      DIMENSION U1(5,101,2), U2(5,101,2), U3(5,101,2)
      DIMENSION DU1(101), DU2(101), DU3(101), SPACER(39)
      CALL SIGNEL(SPACER, 39)
{loads}      CALL SIGNEL(U1, 5*101*2)
      CALL SIGNEL(U2, 5*101*2)
      CALL SIGNEL(U3, 5*101*2)
      NL1 = 1
      NL2 = 2
      FW = 2.0D0
      DO 100 REP = 1, NREPS
        DO 8 KX = 2, 3
        DO 8 KY = 2, N
          DU1(KY) = U1(KX,KY+1,NL1) - U1(KX,KY-1,NL1)
          DU2(KY) = U2(KX,KY+1,NL1) - U2(KX,KY-1,NL1)
          DU3(KY) = U3(KX,KY+1,NL1) - U3(KX,KY-1,NL1)
          U1(KX,KY,NL2) = U1(KX,KY,NL1) + A11*DU1(KY) +
     1                  A12*DU2(KY) + A13*DU3(KY) +
     2     SIG*(U1(KX+1,KY,NL1) - FW*U1(KX,KY,NL1) + U1(KX-1,KY,NL1))
          U2(KX,KY,NL2) = U2(KX,KY,NL1) + A21*DU1(KY) +
     1                  A22*DU2(KY) + A23*DU3(KY) +
     2     SIG*(U2(KX+1,KY,NL1) - FW*U2(KX,KY,NL1) + U2(KX-1,KY,NL1))
          U3(KX,KY,NL2) = U3(KX,KY,NL1) + A31*DU1(KY) +
     1                  A32*DU2(KY) + A33*DU3(KY) +
     2     SIG*(U3(KX+1,KY,NL1) - FW*U3(KX,KY,NL1) + U3(KX-1,KY,NL1))
    8   CONTINUE
  100 CONTINUE
      WRITE(*,'(F0.6)') U1(2,2,2)
      END
" ++ LivermoreDirect.signelSubroutineFortran

def kernel : LivermoreDirect.Kernel :=
  { name := "k08", program := program, fortranSrc := fortranSrc }

end LivermoreDirect.K08

-- ============================================================
-- § K19 — GENERAL LINEAR RECURRENCE (no-vec)
--   Two passes: forward (k=1..n) then reverse (i=1..n, k=n-i+1).
-- ============================================================

namespace LivermoreDirect.K19

private def N : Int := 101
private def NREPS : Int := 2

open LivermoreDirect in
def program : Program where
  decls :=
    [ ("k", .int), ("i", .int), ("rep", .int), ("stb5", .float)
    , ("fuzz", .float), ("buzz", .float), ("fizz", .float) ]
  arrayDecls :=
    [ ("b5", 102, .float), ("sa", 102, .float), ("sb", 102, .float)
    , ("spacer", 40, .float) ]
  body :=
    signelFill "spacer" 39 ;;
    loadSpacers [("stb5", 35)] ;;
    signelFill "b5" N ;; signelFill "sa" N ;; signelFill "sb" N ;;
    fortranDo "rep" (il 1) (il NREPS)
      ( -- forward pass
        fortranDo "k" (il 1) (il N)
          ( .farrWrite "b5" (v "k")
              (fadd (fread "sa" (v "k")) (fmul (v "stb5") (fread "sb" (v "k")))) ;;
            .fassign "stb5" (fsub (fread "b5" (v "k")) (v "stb5")) ) ;;
        -- reverse pass
        fortranDo "i" (il 1) (il N)
          ( .assign "k" (iadd (isub (il N) (v "i")) (il 1)) ;;
            .farrWrite "b5" (v "k")
              (fadd (fread "sa" (v "k")) (fmul (v "stb5") (fread "sb" (v "k")))) ;;
            .fassign "stb5" (fsub (fread "b5" (v "k")) (v "stb5")) ) ) ;;
    .printFloat (fread "b5" (il N)) ;; .printString "\n"

def fortranSrc : String :=
  let loads := LivermoreDirect.loadSpacersFortran [("STB5", 35)]
  s!"
      PROGRAM K19REF
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      INTEGER REP
      PARAMETER (N = {N}, NREPS = {NREPS})
      DIMENSION B5(N), SA(N), SB(N), SPACER(39)
      CALL SIGNEL(SPACER, 39)
{loads}      CALL SIGNEL(B5, N)
      CALL SIGNEL(SA, N)
      CALL SIGNEL(SB, N)
      DO 100 REP = 1, NREPS
        DO 191 K = 1, N
          B5(K) = SA(K) + STB5*SB(K)
          STB5  = B5(K) - STB5
  191   CONTINUE
        DO 193 I = 1, N
          K = N - I + 1
          B5(K) = SA(K) + STB5*SB(K)
          STB5  = B5(K) - STB5
  193   CONTINUE
  100 CONTINUE
      WRITE(*,'(F0.6)') B5(N)
      END
" ++ LivermoreDirect.signelSubroutineFortran

def kernel : LivermoreDirect.Kernel :=
  { name := "k19", program := program, fortranSrc := fortranSrc }

end LivermoreDirect.K19

-- ============================================================
-- § K20 — DISCRETE ORDINATES TRANSPORT
--   IF (DI .NE. 0.0) DN = MAX(S, MIN(Z(k)/DI, T))
-- ============================================================

namespace LivermoreDirect.K20

private def N : Int := 1000
private def NREPS : Int := 2

open LivermoreDirect in
def program : Program where
  decls :=
    [ ("k", .int), ("rep", .int)
    , ("di", .float), ("dn", .float), ("dw", .float)
    , ("dk", .float), ("s", .float), ("t", .float)
    , ("fuzz", .float), ("buzz", .float), ("fizz", .float) ]
  arrayDecls :=
    [ ("x", 1002, .float), ("y", 1002, .float), ("z", 1002, .float)
    , ("u", 1002, .float), ("vv", 1002, .float), ("w", 1002, .float)
    , ("g", 1002, .float), ("xx", 1002, .float), ("vx", 1002, .float)
    , ("spacer", 40, .float) ]
  body :=
    signelFill "spacer" 39 ;;
    loadSpacers [("dk", 15), ("s", 32), ("t", 36)] ;;
    .fassign "dw" (fl 0.2) ;;
    signelFill "x" 1001 ;; signelFill "y" 1001 ;; signelFill "z" 1001 ;;
    signelFill "u" 1001 ;; signelFill "vv" 1001 ;; signelFill "w" 1001 ;;
    signelFill "g" 1001 ;; signelFill "xx" 1001 ;; signelFill "vx" 1001 ;;
    fortranDo "rep" (il 1) (il NREPS)
      ( fortranDo "k" (il 1) (il N)
          ( .fassign "di"
              (fsub (fread "y" (v "k"))
                    (fdiv (fread "g" (v "k"))
                          (fadd (fread "xx" (v "k")) (v "dk")))) ;;
            .fassign "dn" (v "dw") ;;
            .ite (.fcmp .fne (v "di") (fl 0.0))
              ( .fassign "dn"
                  (.fbin .fmax (v "s")
                    (.fbin .fmin (fdiv (fread "z" (v "k")) (v "di")) (v "t"))) )
              .skip ;;
            .farrWrite "x" (v "k")
              (fdiv
                (fadd
                  (fmul (fadd (fread "w" (v "k"))
                              (fmul (fread "vv" (v "k")) (v "dn")))
                        (fread "xx" (v "k")))
                  (fread "u" (v "k")))
                (fadd (fread "vx" (v "k")) (fmul (fread "vv" (v "k")) (v "dn")))) ;;
            .farrWrite "xx" (iadd (v "k") (il 1))
              (fadd (fmul (fsub (fread "x" (v "k")) (fread "xx" (v "k"))) (v "dn"))
                    (fread "xx" (v "k"))) ) ) ;;
    .printFloat (fread "x" (il N)) ;; .printString "\n"

def fortranSrc : String :=
  let loads := LivermoreDirect.loadSpacersFortran [("DK", 15), ("S", 32), ("T", 36)]
  s!"
      PROGRAM K20REF
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      INTEGER REP
      PARAMETER (N = {N}, NREPS = {NREPS})
      DIMENSION X(N+1), Y(N+1), Z(N+1), U(N+1), VV(N+1), W(N+1)
      DIMENSION G(N+1), XX(N+1), VX(N+1), SPACER(39)
      CALL SIGNEL(SPACER, 39)
{loads}      DW = 0.2D0
      CALL SIGNEL(X, N+1)
      CALL SIGNEL(Y, N+1)
      CALL SIGNEL(Z, N+1)
      CALL SIGNEL(U, N+1)
      CALL SIGNEL(VV, N+1)
      CALL SIGNEL(W, N+1)
      CALL SIGNEL(G, N+1)
      CALL SIGNEL(XX, N+1)
      CALL SIGNEL(VX, N+1)
      DO 100 REP = 1, NREPS
        DO 20 K = 1, N
          DI = Y(K) - G(K)/(XX(K)+DK)
          DN = DW
          IF (DI .NE. 0.0D0) DN = MAX(S, MIN(Z(K)/DI, T))
          X(K) = ((W(K) + VV(K)*DN)*XX(K) + U(K))/(VX(K) + VV(K)*DN)
          XX(K+1) = (X(K) - XX(K))*DN + XX(K)
   20   CONTINUE
  100 CONTINUE
      WRITE(*,'(F0.6)') X(N)
      END
" ++ LivermoreDirect.signelSubroutineFortran

def kernel : LivermoreDirect.Kernel :=
  { name := "k20", program := program, fortranSrc := fortranSrc }

end LivermoreDirect.K20

-- ============================================================
-- § K13 — 2-D PIC (Particle In Cell)
--   Mixed integer/float; uses MOD2N(x, 2^n) = IAND(x, 2^n - 1).
--   For our standalone test, integer arrays E, F are initialized
--   to all 1s so that  i2 + E[i2+32]  lands in [1,64] (valid H index)
--   without OOB. Both AST and Fortran do the same init.
-- ============================================================

namespace LivermoreDirect.K13

private def N : Int := 64
private def NREPS : Int := 2

open LivermoreDirect in
private def p4 (i : Int) (k : SExpr) : SExpr := idx2 4 (il i) k
open LivermoreDirect in
private def m64 (i k : SExpr) : SExpr := idx2 64 i k

open LivermoreDirect in
def program : Program where
  decls :=
    [ ("k", .int), ("rep", .int)
    , ("i1", .int), ("j1", .int), ("i2", .int), ("j2", .int)
    , ("fw", .float)
    , ("fuzz", .float), ("buzz", .float), ("fizz", .float) ]
  arrayDecls :=
    [ ("p", 4*64+1, .float)
    , ("b", 64*64+1, .float), ("c", 64*64+1, .float), ("h", 64*64+1, .float)
    , ("y", 97, .float), ("z", 97, .float)
    , ("e", 97, .int), ("f", 97, .int) ]
  body :=
    signelFill "p" (4*64) ;; signelFill "b" (64*64) ;; signelFill "c" (64*64) ;;
    signelFill "h" (64*64) ;; signelFill "y" 96 ;; signelFill "z" 96 ;;
    -- E[i] = F[i] = 1  (initialise integer auxiliaries deterministically)
    fortranDo "k" (il 1) (il 96)
      ( .arrWrite "e" (v "k") (il 1) ;; .arrWrite "f" (v "k") (il 1) ) ;;
    .fassign "fw" (fl 1.0) ;;
    fortranDo "rep" (il 1) (il NREPS)
      ( fortranDo "k" (il 1) (il N)
          ( .assign "i1" (.floatToInt (fread "p" (p4 1 (v "k")))) ;;
            .assign "j1" (.floatToInt (fread "p" (p4 2 (v "k")))) ;;
            .assign "i1" (iadd (il 1) (.bin .band (v "i1") (il 63))) ;;
            .assign "j1" (iadd (il 1) (.bin .band (v "j1") (il 63))) ;;
            .farrWrite "p" (p4 3 (v "k"))
              (fadd (fread "p" (p4 3 (v "k"))) (fread "b" (m64 (v "i1") (v "j1")))) ;;
            .farrWrite "p" (p4 4 (v "k"))
              (fadd (fread "p" (p4 4 (v "k"))) (fread "c" (m64 (v "i1") (v "j1")))) ;;
            .farrWrite "p" (p4 1 (v "k"))
              (fadd (fread "p" (p4 1 (v "k"))) (fread "p" (p4 3 (v "k")))) ;;
            .farrWrite "p" (p4 2 (v "k"))
              (fadd (fread "p" (p4 2 (v "k"))) (fread "p" (p4 4 (v "k")))) ;;
            .assign "i2" (.floatToInt (fread "p" (p4 1 (v "k")))) ;;
            .assign "j2" (.floatToInt (fread "p" (p4 2 (v "k")))) ;;
            .assign "i2" (.bin .band (v "i2") (il 63)) ;;
            .assign "j2" (.bin .band (v "j2") (il 63)) ;;
            .farrWrite "p" (p4 1 (v "k"))
              (fadd (fread "p" (p4 1 (v "k"))) (fread "y" (iadd (v "i2") (il 32)))) ;;
            .farrWrite "p" (p4 2 (v "k"))
              (fadd (fread "p" (p4 2 (v "k"))) (fread "z" (iadd (v "j2") (il 32)))) ;;
            .assign "i2" (iadd (v "i2") (iread "e" (iadd (v "i2") (il 32)))) ;;
            .assign "j2" (iadd (v "j2") (iread "f" (iadd (v "j2") (il 32)))) ;;
            .farrWrite "h" (m64 (v "i2") (v "j2"))
              (fadd (fread "h" (m64 (v "i2") (v "j2"))) (v "fw")) ) ) ;;
    .printFloat (fread "p" (p4 1 (il 1))) ;; .printString "\n"

def fortranSrc : String := s!"
      PROGRAM K13REF
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      INTEGER REP, E, F
      PARAMETER (N = {N}, NREPS = {NREPS})
      DIMENSION P(4,64), B(64,64), C(64,64), H(64,64)
      DIMENSION Y(96), Z(96), E(96), F(96)
      CALL SIGNEL(P, 4*64)
      CALL SIGNEL(B, 64*64)
      CALL SIGNEL(C, 64*64)
      CALL SIGNEL(H, 64*64)
      CALL SIGNEL(Y, 96)
      CALL SIGNEL(Z, 96)
      DO 50 I = 1, 96
        E(I) = 1
   50   F(I) = 1
      FW = 1.0D0
      DO 100 REP = 1, NREPS
        DO 13 K = 1, N
          I1 = INT(P(1,K))
          J1 = INT(P(2,K))
          I1 = 1 + IAND(I1, 63)
          J1 = 1 + IAND(J1, 63)
          P(3,K) = P(3,K) + B(I1,J1)
          P(4,K) = P(4,K) + C(I1,J1)
          P(1,K) = P(1,K) + P(3,K)
          P(2,K) = P(2,K) + P(4,K)
          I2 = INT(P(1,K))
          J2 = INT(P(2,K))
          I2 = IAND(I2, 63)
          J2 = IAND(J2, 63)
          P(1,K) = P(1,K) + Y(I2+32)
          P(2,K) = P(2,K) + Z(J2+32)
          I2 = I2 + E(I2+32)
          J2 = J2 + F(J2+32)
          H(I2,J2) = H(I2,J2) + FW
   13   CONTINUE
  100 CONTINUE
      WRITE(*,'(F0.6)') P(1,1)
      END
" ++ LivermoreDirect.signelSubroutineFortran

def kernel : LivermoreDirect.Kernel :=
  { name := "k13", program := program, fortranSrc := fortranSrc }

end LivermoreDirect.K13

-- ============================================================
-- § K14 — 1-D PIC
--   Initial GRD(k) = real(k) so INT(GRD(k)) = k stays a valid index.
-- ============================================================

namespace LivermoreDirect.K14

private def N : Int := 1001
private def NREPS : Int := 2

open LivermoreDirect in
def program : Program where
  decls :=
    [ ("k", .int), ("rep", .int), ("flx", .float), ("fw", .float)
    , ("fuzz", .float), ("buzz", .float), ("fizz", .float) ]
  arrayDecls :=
    [ ("vx",   1002, .float), ("xx",   1002, .float)
    , ("ix",   1002, .int  ), ("xi",   1002, .float)
    , ("ex1",  1002, .float), ("dex1", 1002, .float)
    , ("ex",   1002, .float), ("dex",  1002, .float)
    , ("grd",  1002, .float), ("ir",   1002, .int  )
    , ("rx",   1002, .float), ("rh",   2050, .float)
    , ("spacer", 40, .float) ]
  body :=
    signelFill "spacer" 39 ;;
    loadSpacers [("flx", 27)] ;;
    .fassign "fw" (fl 1.0) ;;
    -- GRD(k) = real(k)  (deterministic, in-bounds)
    fortranDo "k" (il 1) (il N)
      ( .farrWrite "grd" (v "k") (.intToFloat (v "k")) ) ;;
    signelFill "ex" N ;; signelFill "dex" N ;; signelFill "rh" 2049 ;;
    fortranDo "rep" (il 1) (il NREPS)
      ( fortranDo "k" (il 1) (il N)
          ( .farrWrite "vx" (v "k") (fl 0.0) ;;
            .farrWrite "xx" (v "k") (fl 0.0) ;;
            .arrWrite  "ix" (v "k") (.floatToInt (fread "grd" (v "k"))) ;;
            .farrWrite "xi" (v "k") (.intToFloat (iread "ix" (v "k"))) ;;
            .farrWrite "ex1"  (v "k") (fread "ex"  (iread "ix" (v "k"))) ;;
            .farrWrite "dex1" (v "k") (fread "dex" (iread "ix" (v "k"))) ) ;;
        fortranDo "k" (il 1) (il N)
          ( .farrWrite "vx" (v "k")
              (fadd (fadd (fread "vx" (v "k")) (fread "ex1" (v "k")))
                    (fmul (fsub (fread "xx" (v "k")) (fread "xi" (v "k")))
                          (fread "dex1" (v "k")))) ;;
            .farrWrite "xx" (v "k")
              (fadd (fadd (fread "xx" (v "k")) (fread "vx" (v "k"))) (v "flx")) ;;
            .arrWrite  "ir" (v "k") (.floatToInt (fread "xx" (v "k"))) ;;
            .farrWrite "rx" (v "k")
              (fsub (fread "xx" (v "k")) (.intToFloat (iread "ir" (v "k")))) ;;
            .arrWrite  "ir" (v "k") (iadd (.bin .band (iread "ir" (v "k")) (il 2047)) (il 1)) ;;
            .farrWrite "xx" (v "k")
              (fadd (fread "rx" (v "k")) (.intToFloat (iread "ir" (v "k")))) ) ;;
        fortranDo "k" (il 1) (il N)
          ( .farrWrite "rh" (iread "ir" (v "k"))
              (fadd (fread "rh" (iread "ir" (v "k")))
                    (fsub (v "fw") (fread "rx" (v "k")))) ;;
            .farrWrite "rh" (iadd (iread "ir" (v "k")) (il 1))
              (fadd (fread "rh" (iadd (iread "ir" (v "k")) (il 1))) (fread "rx" (v "k"))) ) ) ;;
    .printFloat (fread "rh" (il 1)) ;; .printString "\n"

def fortranSrc : String :=
  let loads := LivermoreDirect.loadSpacersFortran [("FLX", 27)]
  s!"
      PROGRAM K14REF
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      INTEGER REP, IX, IR
      PARAMETER (N = {N}, NREPS = {NREPS})
      DIMENSION VX(N), XX(N), IX(N), XI(N), EX1(N), DEX1(N)
      DIMENSION EX(N), DEX(N), GRD(N), IR(N), RX(N), RH(2050)
      DIMENSION SPACER(39)
      CALL SIGNEL(SPACER, 39)
{loads}      FW = 1.0D0
      DO 50 K = 1, N
   50   GRD(K) = REAL(K)
      CALL SIGNEL(EX, N)
      CALL SIGNEL(DEX, N)
      CALL SIGNEL(RH, 2049)
      DO 100 REP = 1, NREPS
        DO 141 K = 1, N
          VX(K) = 0.0D0
          XX(K) = 0.0D0
          IX(K) = INT(GRD(K))
          XI(K) = REAL(IX(K))
          EX1(K)  = EX(IX(K))
  141     DEX1(K) = DEX(IX(K))
        DO 142 K = 1, N
          VX(K) = VX(K) + EX1(K) + (XX(K) - XI(K))*DEX1(K)
          XX(K) = XX(K) + VX(K) + FLX
          IR(K) = XX(K)
          RX(K) = XX(K) - IR(K)
          IR(K) = IAND(IR(K), 2047) + 1
  142     XX(K) = RX(K) + IR(K)
        DO 14 K = 1, N
          RH(IR(K))   = RH(IR(K))   + FW - RX(K)
   14     RH(IR(K)+1) = RH(IR(K)+1) + RX(K)
  100 CONTINUE
      WRITE(*,'(F0.6)') RH(1)
      END
" ++ LivermoreDirect.signelSubroutineFortran

def kernel : LivermoreDirect.Kernel :=
  { name := "k14", program := program, fortranSrc := fortranSrc }

end LivermoreDirect.K14

-- ============================================================
-- § K17 — IMPLICIT, CONDITIONAL COMPUTATION
--   Original uses goto labels 60/61/62. We restructure as a
--   state-machine over a `at60 : bool` flag.  Equivalent CFG;
--   verifiable by inspection against the canonical Fortran.
-- ============================================================

namespace LivermoreDirect.K17

private def N : Int := 101
private def NREPS : Int := 2

open LivermoreDirect in
def program : Program where
  decls :=
    [ ("k", .int), ("j", .int), ("ink", .int), ("rep", .int)
    , ("scale", .float), ("xnm", .float), ("e6", .float), ("e3", .float)
    , ("xnei", .float), ("xnc", .float)
    , ("at60", .bool), ("done", .bool)
    , ("fuzz", .float), ("buzz", .float), ("fizz", .float) ]
  arrayDecls :=
    [ ("vsp",  102, .float), ("vstp", 102, .float)
    , ("vxne", 102, .float), ("vxnd", 102, .float)
    , ("ve3",  102, .float), ("vlr",  102, .float), ("vlin", 102, .float) ]
  body :=
    signelFill "vsp" N ;; signelFill "vstp" N ;; signelFill "vxne" N ;;
    signelFill "vxnd" N ;; signelFill "ve3" N ;; signelFill "vlr" N ;;
    signelFill "vlin" N ;;
    fortranDo "rep" (il 1) (il NREPS)
      ( .assign "k"     (il N) ;;
        .assign "j"     (il 1) ;;
        .assign "ink"   (il (-1)) ;;
        .fassign "scale" (fdiv (fl 5.0) (fl 3.0)) ;;
        .fassign "xnm"   (fdiv (fl 1.0) (fl 3.0)) ;;
        .fassign "e6"    (fdiv (fl 1.03) (fl 3.07)) ;;
        .bassign "at60"  (.lit false) ;;        -- start at label 61
        .bassign "done"  (.lit false) ;;
        .loop (.not (.bvar "done"))
          ( .ite (.bvar "at60")
              -- branch: emulate label 60
              ( .fassign "e6"
                  (fadd (fmul (v "xnm") (fread "vsp" (v "k"))) (fread "vstp" (v "k"))) ;;
                .farrWrite "vxne" (v "k") (v "e6") ;;
                .fassign "xnm" (v "e6") ;;
                .farrWrite "ve3" (v "k") (v "e6") ;;
                .assign "k" (iadd (v "k") (v "ink")) ;;
                .ite (.cmp .eq (v "k") (v "j"))
                  (.bassign "done" (.lit true))
                  (.bassign "at60" (.lit false)) )
              -- branch: emulate label 61
              ( .fassign "e3"
                  (fadd (fmul (v "xnm") (fread "vlr" (v "k"))) (fread "vlin" (v "k"))) ;;
                .fassign "xnei" (fread "vxne" (v "k")) ;;
                .farrWrite "vxnd" (v "k") (v "e6") ;;
                .fassign "xnc" (fmul (v "scale") (v "e3")) ;;
                -- IF (XNM > XNC) GOTO 60  ─ rewrite using (xnc < xnm)
                .ite (.or (.fcmp .flt (v "xnc") (v "xnm")) (.fcmp .flt (v "xnc") (v "xnei")))
                  (.bassign "at60" (.lit true))
                  (.farrWrite "ve3" (v "k") (v "e3") ;;
                   .fassign "e6" (fsub (fadd (v "e3") (v "e3")) (v "xnm")) ;;
                   .farrWrite "vxne" (v "k") (fsub (fadd (v "e3") (v "e3")) (v "xnei")) ;;
                   .fassign "xnm" (v "e6") ;;
                   .assign "k" (iadd (v "k") (v "ink")) ;;
                   .ite (.cmp .eq (v "k") (v "j"))
                     (.bassign "done" (.lit true)) .skip) ) ) ) ;;
    .printFloat (fread "vxne" (il N)) ;; .printString "\n"

def fortranSrc : String := s!"
      PROGRAM K17REF
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      INTEGER REP
      PARAMETER (N = {N}, NREPS = {NREPS})
      DIMENSION VSP(N), VSTP(N), VXNE(N), VXND(N)
      DIMENSION VE3(N), VLR(N), VLIN(N)
      CALL SIGNEL(VSP, N)
      CALL SIGNEL(VSTP, N)
      CALL SIGNEL(VXNE, N)
      CALL SIGNEL(VXND, N)
      CALL SIGNEL(VE3, N)
      CALL SIGNEL(VLR, N)
      CALL SIGNEL(VLIN, N)
      DO 100 REP = 1, NREPS
        K = N
        J = 1
        INK = -1
        SCALE = 5.0D0/3.0D0
        XNM   = 1.0D0/3.0D0
        E6    = 1.03D0/3.07D0
        GOTO 61
   60   E6 = XNM*VSP(K) + VSTP(K)
        VXNE(K) = E6
        XNM = E6
        VE3(K) = E6
        K = K + INK
        IF (K .EQ. J) GOTO 62
   61   E3 = XNM*VLR(K) + VLIN(K)
        XNEI = VXNE(K)
        VXND(K) = E6
        XNC = SCALE*E3
        IF (XNM  .GT. XNC) GOTO 60
        IF (XNEI .GT. XNC) GOTO 60
        VE3(K) = E3
        E6 = E3 + E3 - XNM
        VXNE(K) = E3 + E3 - XNEI
        XNM = E6
        K = K + INK
        IF (K .NE. J) GOTO 61
   62   CONTINUE
  100 CONTINUE
      WRITE(*,'(F0.6)') VXNE(N)
      END
" ++ LivermoreDirect.signelSubroutineFortran

def kernel : LivermoreDirect.Kernel :=
  { name := "k17", program := program, fortranSrc := fortranSrc }

end LivermoreDirect.K17

-- ============================================================
-- § K15 — CASUAL FORTRAN (development version)
--   Original uses arithmetic IFs and label gotos.  Each arithmetic IF
--   is rewritten as a structured if/else (since both ">0" and "=0"
--   branches in the canonical map to the same target, the trichotomy
--   collapses to two branches).  Array reads in conditions are pulled
--   into scalar temps before comparison (per checkBoolExprNoArrRead).
-- ============================================================

namespace LivermoreDirect.K15

private def N : Int := 101
private def NREPS : Int := 2

open LivermoreDirect in
def program : Program where
  decls :=
    [ ("j", .int), ("k", .int), ("ng", .int), ("nz", .int), ("rep", .int)
    , ("ar", .float), ("br", .float), ("t", .float), ("r", .float), ("s", .float)
    , ("vhj1", .float), ("vh0", .float), ("vfj", .float), ("vfm", .float)
    , ("a", .float), ("b", .float), ("vg", .float), ("vh", .float)
    , ("fuzz", .float), ("buzz", .float), ("fizz", .float) ]
  arrayDecls :=
    [ ("vy", 101*7+1, .float), ("vh", 101*7+1, .float), ("vf", 101*7+1, .float)
    , ("vg", 101*7+1, .float), ("vs", 101*7+1, .float) ]
  body :=
    signelFill "vh" (101*7) ;; signelFill "vf" (101*7) ;; signelFill "vg" (101*7) ;;
    .assign "ng" (il 7) ;;
    .assign "nz" (il N) ;;
    .fassign "ar" (fl 0.0530) ;;
    .fassign "br" (fl 0.0730) ;;
    fortranDo "rep" (il 1) (il NREPS)
      ( fortranDo "j" (il 2) (v "ng")
          ( fortranDo "k" (il 2) (v "nz")
              ( -- IF (j-NG) 31,30,30  →  if j>=NG then label-30 else label-31
                .ite (.cmp .le (v "ng") (v "j"))
                  (.farrWrite "vy" (idx2 101 (v "k") (v "j")) (fl 0.0))
                  ( -- T branch:  IF (VH[k,j+1]-VH[k,j]) 33,33,32 →
                    -- "diff>0 ⇒ 32 (T=AR)" else 33 (T=BR)
                    .fassign "vhj1" (fread "vh" (idx2 101 (v "k") (iadd (v "j") (il 1)))) ;;
                    .fassign "vh0"  (fread "vh" (idx2 101 (v "k") (v "j"))) ;;
                    .ite (.fcmp .flt (v "vh0") (v "vhj1"))
                      (.fassign "t" (v "ar")) (.fassign "t" (v "br")) ;;
                    -- R/S branch: IF (VF[k,j]-VF[k-1,j]) 35,36,36 →
                    -- diff<0 ⇒ 35; diff>=0 ⇒ 36
                    .fassign "vfj" (fread "vf" (idx2 101 (v "k") (v "j"))) ;;
                    .fassign "vfm" (fread "vf" (idx2 101 (isub (v "k") (il 1)) (v "j"))) ;;
                    .ite (.fcmp .flt (v "vfj") (v "vfm"))
                      ( .fassign "a" (fread "vh" (idx2 101 (isub (v "k") (il 1)) (v "j"))) ;;
                        .fassign "b" (fread "vh" (idx2 101 (isub (v "k") (il 1)) (iadd (v "j") (il 1)))) ;;
                        .fassign "r" (.fbin .fmax (v "a") (v "b")) ;;
                        .fassign "s" (v "vfm") )
                      ( .fassign "a" (fread "vh" (idx2 101 (v "k") (v "j"))) ;;
                        .fassign "b" (fread "vh" (idx2 101 (v "k") (iadd (v "j") (il 1)))) ;;
                        .fassign "r" (.fbin .fmax (v "a") (v "b")) ;;
                        .fassign "s" (v "vfj") ) ;;
                    .fassign "vg" (fread "vg" (idx2 101 (v "k") (v "j"))) ;;
                    .farrWrite "vy" (idx2 101 (v "k") (v "j"))
                      (fdiv (fmul (.floatUnary .sqrt
                                    (fadd (fmul (v "vg") (v "vg")) (fmul (v "r") (v "r"))))
                                  (v "t"))
                            (v "s")) ;;
                    -- IF (k-NZ) 40,39,39  →  k>=NZ ⇒ 39 (VS=0) else 40
                    .ite (.cmp .le (v "nz") (v "k"))
                      (.farrWrite "vs" (idx2 101 (v "k") (v "j")) (fl 0.0))
                      ( -- IF (VF[k,j]-VF[k,j-1]) 41,42,42  →  <0 ⇒ 41 else 42
                        .fassign "vfj" (fread "vf" (idx2 101 (v "k") (v "j"))) ;;
                        .fassign "vfm" (fread "vf" (idx2 101 (v "k") (isub (v "j") (il 1)))) ;;
                        .ite (.fcmp .flt (v "vfj") (v "vfm"))
                          ( .fassign "a" (fread "vg" (idx2 101 (v "k") (isub (v "j") (il 1)))) ;;
                            .fassign "b" (fread "vg" (idx2 101 (iadd (v "k") (il 1)) (isub (v "j") (il 1)))) ;;
                            .fassign "r" (.fbin .fmax (v "a") (v "b")) ;;
                            .fassign "s" (v "vfm") ;;
                            .fassign "t" (v "br") )
                          ( .fassign "a" (fread "vg" (idx2 101 (v "k") (v "j"))) ;;
                            .fassign "b" (fread "vg" (idx2 101 (iadd (v "k") (il 1)) (v "j"))) ;;
                            .fassign "r" (.fbin .fmax (v "a") (v "b")) ;;
                            .fassign "s" (v "vfj") ;;
                            .fassign "t" (v "ar") ) ;;
                        .fassign "vh" (fread "vh" (idx2 101 (v "k") (v "j"))) ;;
                        .farrWrite "vs" (idx2 101 (v "k") (v "j"))
                          (fdiv (fmul (.floatUnary .sqrt
                                        (fadd (fmul (v "vh") (v "vh")) (fmul (v "r") (v "r"))))
                                      (v "t"))
                                (v "s")) ) ) ) ) ) ;;
    .printFloat (fread "vy" (idx2 101 (il 2) (il 2))) ;; .printString "\n"

def fortranSrc : String := s!"
      PROGRAM K15REF
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      INTEGER REP
      PARAMETER (N = {N}, NREPS = {NREPS})
      DIMENSION VY(N,7), VH(N,7), VF(N,7), VG(N,7), VS(N,7)
      CALL SIGNEL(VH, N*7)
      CALL SIGNEL(VF, N*7)
      CALL SIGNEL(VG, N*7)
      NG = 7
      NZ = N
      AR = 0.05300D0
      BR = 0.07300D0
      DO 100 REP = 1, NREPS
        DO 45  J = 2, NG
        DO 45  K = 2, NZ
          IF (J .GE. NG) THEN
            VY(K,J) = 0.0D0
          ELSE
            IF (VH(K,J+1) .GT. VH(K,J)) THEN
              T = AR
            ELSE
              T = BR
            ENDIF
            IF (VF(K,J) .LT. VF(K-1,J)) THEN
              R = MAX(VH(K-1,J), VH(K-1,J+1))
              S = VF(K-1,J)
            ELSE
              R = MAX(VH(K,J), VH(K,J+1))
              S = VF(K,J)
            ENDIF
            VY(K,J) = SQRT(VG(K,J)**2 + R*R)*T/S
            IF (K .GE. NZ) THEN
              VS(K,J) = 0.0D0
            ELSE
              IF (VF(K,J) .LT. VF(K,J-1)) THEN
                R = MAX(VG(K,J-1), VG(K+1,J-1))
                S = VF(K,J-1)
                T = BR
              ELSE
                R = MAX(VG(K,J), VG(K+1,J))
                S = VF(K,J)
                T = AR
              ENDIF
              VS(K,J) = SQRT(VH(K,J)**2 + R*R)*T/S
            ENDIF
          ENDIF
   45   CONTINUE
  100 CONTINUE
      WRITE(*,'(F0.6)') VY(2,2)
      END
" ++ LivermoreDirect.signelSubroutineFortran

def kernel : LivermoreDirect.Kernel :=
  { name := "k15", program := program, fortranSrc := fortranSrc }

end LivermoreDirect.K15

-- ============================================================
-- § K16 — MONTE CARLO SEARCH LOOP
--   Original is a goto labyrinth. We initialise ZONE(1)=1 so the
--   "restart at 410" branch never fires (m always wraps to 1 = i1
--   ⇒ exit-480), allowing a flat structured rewrite over the inner
--   DO 470 loop with a `done` break flag and `goto440/445/455`
--   dispatch flags.  Observable: k2 + k3.
-- ============================================================

namespace LivermoreDirect.K16

private def N : Int := 75
private def NREPS : Int := 2

open LivermoreDirect in
def program : Program where
  decls :=
    [ ("k", .int), ("rep", .int), ("m", .int), ("i1", .int)
    , ("ii", .int), ("lb", .int), ("k2", .int), ("k3", .int)
    , ("j2", .int), ("j4", .int), ("j5", .int), ("z", .int), ("ksum", .int)
    , ("r", .float), ("s", .float), ("t", .float)
    , ("diff", .float), ("expr", .float), ("tmp", .float)
    , ("cmpval", .float)
    , ("done", .bool), ("g440", .bool), ("g445", .bool)
    , ("g480", .bool), ("g485", .bool), ("g455", .bool)
    , ("fuzz", .float), ("buzz", .float), ("fizz", .float) ]
  arrayDecls :=
    [ ("plan", 301, .float), ("d", 301, .float), ("zone", 301, .int)
    , ("spacer", 40, .float) ]
  body :=
    signelFill "spacer" 39 ;;
    loadSpacers [("r", 30), ("s", 32), ("t", 36)] ;;
    signelFill "plan" 300 ;; signelFill "d" 300 ;;
    -- init ZONE deterministically; ZONE(1)=1 ⇒ restart-410 path inert
    fortranDo "k" (il 1) (il 300)
      ( .arrWrite "zone" (v "k") (iadd (imod (imul (isub (v "k") (il 1)) (il 13)) (il 100)) (il 1)) ) ;;
    .arrWrite "zone" (il 1) (il 1) ;;
    .assign "ii" (.bin .div (il N) (il 3)) ;;
    .assign "lb" (iadd (v "ii") (v "ii")) ;;
    .assign "k2" (il 0) ;; .assign "k3" (il 0) ;;
    fortranDo "rep" (il 1) (il NREPS)
      ( .assign "m"  (il 1) ;;
        .assign "i1" (v "m") ;;
        -- 410:
        .assign "j2" (iadd (imul (iadd (il N) (il N)) (isub (v "m") (il 1))) (il 1)) ;;
        .assign "k"  (il 1) ;;
        .bassign "done" (.lit false) ;;
        .loop (.and (.not (.bvar "done")) (.cmp .le (v "k") (il N)))
          ( .assign "k2" (iadd (v "k2") (il 1)) ;;
            .assign "j4" (iadd (v "j2") (iadd (v "k") (v "k"))) ;;
            .assign "j5" (iread "zone" (v "j4")) ;;
            .bassign "g440" (.lit false) ;; .bassign "g445" (.lit false) ;;
            .bassign "g480" (.lit false) ;; .bassign "g485" (.lit false) ;;
            .bassign "g455" (.lit false) ;;
            -- initial dispatch: IF (j5 - n) 420, 475, 450
            .ite (.cmp .lt (v "j5") (il N))
              ( -- j5 < n: 420 → 415 chain selecting 425/430/435
                .ite (.cmp .lt (v "j5") (isub (il N) (v "lb")))
                  (.fassign "cmpval" (v "t"))
                  (.ite (.cmp .lt (v "j5") (isub (il N) (v "ii")))
                    (.fassign "cmpval" (v "s"))
                    (.fassign "cmpval" (v "r"))) ;;
                .fassign "diff" (fsub (fread "plan" (v "j5")) (v "cmpval")) ;;
                .ite (.fcmp .flt (v "diff") (fl 0.0))
                  (.bassign "g445" (.lit true))
                  (.ite (.fcmp .feq (v "diff") (fl 0.0))
                    (.bassign "g480" (.lit true))
                    (.bassign "g440" (.lit true))) )
              ( .ite (.cmp .eq (v "j5") (il N))
                  -- j5 == n → 475 exit
                  (.bassign "g480" (.lit true))
                  -- j5 > n → 450 (D-cascade)
                  ( .assign "k3" (iadd (v "k3") (il 1)) ;;
                    -- expr = D[j5] - (D[j5-1]*(T-D[j5-2])^2 + (S-D[j5-3])^2 + (R-D[j5-4])^2)
                    .fassign "tmp" (fsub (v "t") (fread "d" (isub (v "j5") (il 2)))) ;;
                    .fassign "expr"
                      (fsub (fread "d" (v "j5"))
                            (fadd (fadd
                              (fmul (fread "d" (isub (v "j5") (il 1)))
                                    (fmul (v "tmp") (v "tmp")))
                              (let q := fsub (v "s") (fread "d" (isub (v "j5") (il 3))); fmul q q))
                              (let q := fsub (v "r") (fread "d" (isub (v "j5") (il 4))); fmul q q))) ;;
                    .ite (.fcmp .flt (v "expr") (fl 0.0))
                      (.bassign "g445" (.lit true))
                      (.ite (.fcmp .feq (v "expr") (fl 0.0))
                        (.bassign "g480" (.lit true))
                        (.bassign "g440" (.lit true))) ) ) ;;
            -- 440: IF ZONE[j4-1] 455,485,470
            .ite (.bvar "g440")
              ( .assign "z" (iread "zone" (isub (v "j4") (il 1))) ;;
                .ite (.cmp .lt (v "z") (il 0))
                  (.bassign "g455" (.lit true))
                  (.ite (.cmp .eq (v "z") (il 0))
                    (.bassign "g485" (.lit true))
                    .skip) )
              .skip ;;
            -- 445: IF ZONE[j4-1] 470,485,455
            .ite (.bvar "g445")
              ( .assign "z" (iread "zone" (isub (v "j4") (il 1))) ;;
                .ite (.cmp .lt (v "z") (il 0))
                  .skip
                  (.ite (.cmp .eq (v "z") (il 0))
                    (.bassign "g485" (.lit true))
                    (.bassign "g455" (.lit true))) )
              .skip ;;
            -- 455: m += 1; if m > ZONE[1]: m=1; if i1==m: 480 exit
            -- (with ZONE(1)=1 this always exits, so we don't need to encode the restart)
            .ite (.bvar "g455")
              ( .assign "m" (iadd (v "m") (il 1)) ;;
                .assign "z" (iread "zone" (il 1)) ;;
                .ite (.cmp .lt (v "z") (v "m"))
                  (.assign "m" (il 1)) .skip ;;
                .ite (.cmp .eq (v "i1") (v "m"))
                  (.bassign "g480" (.lit true)) .skip )
              .skip ;;
            .ite (.or (.bvar "g480") (.bvar "g485"))
              (.bassign "done" (.lit true)) .skip ;;
            .assign "k" (iadd (v "k") (il 1)) ) ) ;;
    .assign "ksum" (iadd (v "k2") (v "k3")) ;;
    .printInt (v "ksum") ;; .printString "\n"

def fortranSrc : String :=
  let loads := LivermoreDirect.loadSpacersFortran [("R", 30), ("S", 32), ("T", 36)]
  s!"
      PROGRAM K16REF
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      INTEGER REP, ZONE
      PARAMETER (N = {N}, NREPS = {NREPS})
      DIMENSION PLAN(300), D(300), ZONE(300), SPACER(39)
      CALL SIGNEL(SPACER, 39)
{loads}      CALL SIGNEL(PLAN, 300)
      CALL SIGNEL(D, 300)
      DO 50 J = 1, 300
   50   ZONE(J) = MOD((J-1)*13, 100) + 1
      ZONE(1) = 1
      II = N/3
      LB = II + II
      K2 = 0
      K3 = 0
      DO 1000 REP = 1, NREPS
        M = 1
        I1 = M
  410   J2 = (N+N)*(M-1) + 1
        DO 470 K = 1, N
          K2 = K2 + 1
          J4 = J2 + K + K
          J5 = ZONE(J4)
          IF (J5-N      ) 420, 475, 450
  415     IF (J5-N+II   ) 430, 425, 425
  420     IF (J5-N+LB   ) 435, 415, 415
  425     IF (PLAN(J5)-R) 445, 480, 440
  430     IF (PLAN(J5)-S) 445, 480, 440
  435     IF (PLAN(J5)-T) 445, 480, 440
  440     IF (ZONE(J4-1)) 455, 485, 470
  445     IF (ZONE(J4-1)) 470, 485, 455
  450     K3 = K3 + 1
          IF (D(J5)-(D(J5-1)*(T-D(J5-2))**2+(S-D(J5-3))**2
     1                          +(R-D(J5-4))**2)) 445, 480, 440
  455     M = M + 1
          IF (M-ZONE(1)) 465, 465, 460
  460     M = 1
  465     IF (I1-M) 410, 480, 410
  470   CONTINUE
  475   CONTINUE
  480   CONTINUE
  485   CONTINUE
 1000 CONTINUE
      WRITE(*,'(I0)') K2 + K3
      END
" ++ LivermoreDirect.signelSubroutineFortran

def kernel : LivermoreDirect.Kernel :=
  { name := "k16", program := program, fortranSrc := fortranSrc }

end LivermoreDirect.K16

-- ============================================================
-- § N. Driver: registry + main
-- ============================================================

namespace LivermoreDirect

def allKernels : List Kernel :=
  [ K01.kernel, K02.kernel, K03.kernel, K04.kernel, K05.kernel
  , K06.kernel, K07.kernel, K08.kernel, K09.kernel, K10.kernel
  , K11.kernel, K12.kernel, K13.kernel, K14.kernel, K15.kernel
  , K16.kernel, K17.kernel, K18.kernel, K19.kernel, K20.kernel
  , K21.kernel, K22.kernel, K23.kernel, K24.kernel ]

private def writeRuntimeLocal : IO String := do
  let path := "/tmp/credible_runtime.c"
  let src ← IO.FS.readFile ⟨"Compiler/runtime.c"⟩
  IO.FS.writeFile ⟨path⟩ src
  return path

/-- Normalize a printed float so that gfortran's `F0.6` (`.101987`) and
    libc's `%f` (`0.101987`) compare equal. Strip whitespace, drop leading
    `+`, then prepend `0` to a leading `.` or `-.`. -/
private def normalize (raw : String) : String :=
  let s : String := (raw.foldl (fun acc c => if c == ' ' || c == '\n' || c == '\t' then acc else acc.push c) "")
  let s := if s.startsWith "+" then s.drop 1 |>.toString else s
  if s.startsWith "." then "0" ++ s
  else if s.startsWith "-." then "-0" ++ (s.drop 1 |>.toString)
  else s

private def compileProgToAsm (prog : Program) (noOpt : Bool) : Except String String := do
  let r ← compileProgramAst prog noOpt
  let opt :=
    if noOpt then prog.compileToTAC
    else applyStandardPipelineFixpoint prog.tyCtx prog.compileToTAC
  formatVerifiedAsm r opt

/-- Run a single kernel: AST → asm → link → run; also Fortran → gfortran → run.
    Returns true if outputs match. -/
def runKernel (k : Kernel) : IO Bool := do
  let dir := s!"/tmp/livermore_direct/{k.name}"
  let asmPath := s!"{dir}/{k.name}.s"
  let binPath := s!"{dir}/{k.name}_ast"
  let fSrc    := s!"{dir}/{k.name}_ref.f"
  let fBin    := s!"{dir}/{k.name}_ref"
  let _ ← IO.Process.output { cmd := "mkdir", args := #["-p", dir] }
  -- AST → assembly via verified pipeline
  if !k.program.wellFormed then
    IO.println s!"  [{k.name}] FAIL — program not well-formed"
    return false
  match compileProgToAsm k.program (noOpt := false) with
  | .error e =>
    IO.println s!"  [{k.name}] FAIL — verified pipeline error: {e}"
    return false
  | .ok asm =>
    IO.FS.writeFile ⟨asmPath⟩ asm
    let runtimePath ← writeRuntimeLocal
    let cc ← IO.Process.output { cmd := "cc", args := #["-o", binPath, asmPath, runtimePath] }
    if cc.exitCode != 0 then
      IO.println s!"  [{k.name}] FAIL — link error\n{cc.stderr}"
      return false
    -- Run AST binary
    let astRun ← IO.Process.output { cmd := binPath, args := #[] }
    if astRun.exitCode != 0 then
      IO.println s!"  [{k.name}] FAIL — AST binary exit {astRun.exitCode}\n{astRun.stderr}"
      return false
    let astOut := normalize astRun.stdout
    -- Fortran reference
    IO.FS.writeFile ⟨fSrc⟩ k.fortranSrc
    let gf ← IO.Process.output { cmd := "gfortran", args := #["-O2", "-w", "-o", fBin, fSrc] }
    if gf.exitCode != 0 then
      IO.println s!"  [{k.name}] FAIL — gfortran error\n{gf.stderr}"
      return false
    let fRun ← IO.Process.output { cmd := fBin, args := #[] }
    if fRun.exitCode != 0 then
      IO.println s!"  [{k.name}] FAIL — Fortran binary exit\n{fRun.stderr}"
      return false
    let fOut := normalize fRun.stdout
    let ok := astOut == fOut
    let mark := if ok then "OK  " else "FAIL"
    IO.println s!"  [{k.name}] {mark}  ast={astOut}  fortran={fOut}"
    return ok

end LivermoreDirect

def main (args : List String) : IO UInt32 := do
  let target := args.headD "all"
  let kernels := LivermoreDirect.allKernels
  let selected :=
    if target == "all" then kernels
    else kernels.filter (·.name == target)
  if selected.isEmpty then
    IO.eprintln s!"unknown kernel: {target}"
    IO.eprintln s!"available: {String.intercalate " " (kernels.map (·.name))}"
    return 1
  let mut pass := 0
  let mut fail := 0
  for k in selected do
    if (← LivermoreDirect.runKernel k) then pass := pass + 1
    else fail := fail + 1
  IO.println s!""
  IO.println s!"=== {pass} pass, {fail} fail (out of {selected.length}) ==="
  return if fail == 0 then 0 else 1
