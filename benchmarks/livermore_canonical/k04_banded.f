C     Kernel 4 -- Banded linear equations (canonical)
C     From "The Livermore Fortran Kernels" (UCRL-53745), F.H. McMahon, 1986
C     XZ is the canonical EQUIVALENCE name; here treated as a single
C     array of length 1201 (covers X(1001) with overflow into Z).
C
      PROGRAM K04
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      INTEGER REP
      DIMENSION XZ(1201), Y(1001)
C
C     Initialize Y
C
      FUZZ  = 1.2345D-3
      BUZZ  = 1.0D0 + FUZZ
      FIZZ  = 1.1D0 * FUZZ
      DO 10 K = 1, 1001
          BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
          FUZZ = -FUZZ
          Y(K) = (BUZZ - FIZZ) * 0.1D0
   10 CONTINUE
C
      N = 1001
      M = (1001 - 7) / 2
C
      DO 200 REP = 1, 14000000
C         Reset XZ each rep
          FUZZ  = 1.2345D-3
          BUZZ  = 1.0D0 + FUZZ
          FIZZ  = 1.1D0 * FUZZ
          DO 20 K = 1, 1201
              BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
              FUZZ = -FUZZ
              XZ(K) = (BUZZ - FIZZ) * 0.1D0
   20     CONTINUE
C
C         Kernel loop
C
          DO 100 K = 7, 1001, M
              LW = K - 6
              TEMP = XZ(K-1)
              DO 90 J = 5, N, 5
                  TEMP = TEMP - XZ(LW) * Y(J)
                  LW = LW + 1
   90         CONTINUE
              XZ(K-1) = Y(5) * TEMP
  100     CONTINUE
  200 CONTINUE
C
      WRITE(*,900) XZ(7)
  900 FORMAT('xz(7) = ', E25.15)
      END
