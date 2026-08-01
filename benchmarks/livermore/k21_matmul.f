C     Kernel 21 -- Matrix*Matrix Product
C     From "The Livermore Fortran Kernels" (UCRL-53745), F.H. McMahon, 1986
C
      PROGRAM K21
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      DIMENSION PX(25,101), VY(101,25), CX(25,101)
C
C     Initialize PX to zero
C
      DO 6 J = 1, 101
         DO 5 I = 1, 25
            PX(I,J) = 0.0D0
    5    CONTINUE
    6 CONTINUE
C
C     Initialize CX using SIGNEL
C
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      SCALED = 0.1D0
      DO 12 J = 1, 101
         DO 11 I = 1, 25
            BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
            FUZZ = -FUZZ
            CX(I,J) = (BUZZ - FIZZ) * SCALED
   11    CONTINUE
   12 CONTINUE
C
C     Initialize VY using SIGNEL
C
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 14 J = 1, 25
         DO 13 I = 1, 101
            BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
            FUZZ = -FUZZ
            VY(I,J) = (BUZZ - FIZZ) * SCALED
   13    CONTINUE
   14 CONTINUE
C
      N = 101
C
C     Kernel 21: Matrix*Matrix Product
C     PX(i,j) += sum_k VY(k,i) * CX(k,j)
C     C code: px[j][i] += vy[k][i] * cx[j][k]
C     In Fortran (column-major): PX(I,J) += VY(K,I) * CX(K,J)
C     where I=1..25, J=1..N, K=1..25
C
      DO 500 IREP = 1, 2476000
C
C        Reset PX
         DO 106 J = 1, 101
            DO 105 I = 1, 25
               PX(I,J) = 0.0D0
  105       CONTINUE
  106    CONTINUE
C
         DO 300 K = 1, 25
            DO 200 I = 1, 25
               DO 100 J = 1, N
                  PX(I,J) = PX(I,J) + VY(K,I) * CX(K,J)
  100          CONTINUE
  200       CONTINUE
  300    CONTINUE
  500 CONTINUE
C
      WRITE(*,900) PX(13,51)
  900 FORMAT('K21 matmul: px(13,51) = ', E23.15E3)
      END
