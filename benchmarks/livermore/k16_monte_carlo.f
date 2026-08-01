C     Kernel 16 -- Monte Carlo search loop
C     From "The Livermore Fortran Kernels" (UCRL-53745), F.H. McMahon, 1986
C
C     This is the original Fortran kernel with GOTO-based control flow.
C     The loop searches zone/plan/d arrays using a Monte Carlo pattern
C     with labeled jumps for break/continue/restart semantics.
C
      PROGRAM K16
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      INTEGER ZONE
      DIMENSION D(300), PLAN(300), ZONE(300)

      N  = 75
      II = N/3
      LB = II+II

C     Initialize arrays (simplified SIGNEL)
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 10 I = 1, 300
         BUZZ = (1.0D0 - FUZZ)*BUZZ + FUZZ
         FUZZ = -FUZZ
         D(I)    = (BUZZ - FIZZ)*0.1D0
         PLAN(I) = (BUZZ - FIZZ)*0.1D0
   10 CONTINUE
      DO 15 I = 1, 300
         ZONE(I) = MOD(I-1, N+1)
   15 CONTINUE
      ZONE(1) = 5

C     Spacer init for r,s,t (simplified)
      R = 0.05D0
      S = 0.05D0
      T = 0.05D0

      DO 500 IREP = 1, 162000000
         I1 = 1
         M  = 1
         K2 = 0
         K3 = 0

C        -- Entry point for restart with new M
  410    J2 = (N+N)*(M-1) + 1
         DO 470 K = 1, N
            K2 = K2 + 1
            J4 = J2 + K + K
            J5 = ZONE(J4-1)
            IF (J5 .LT. N) THEN
               IF (J5+LB .LT. N) THEN
                  TMP = PLAN(J5) - T
               ELSE IF (J5+II .LT. N) THEN
                  TMP = PLAN(J5) - S
               ELSE
                  TMP = PLAN(J5) - R
               END IF
            ELSE IF (J5 .EQ. N) THEN
               GO TO 480
            ELSE
               K3 = K3 + 1
               TMP = D(J5-1) - (D(J5-2)*(T-D(J5-3))*(T-D(J5-3))
     &              +(S-D(J5-4))*(S-D(J5-4))
     &              +(R-D(J5-5))*(R-D(J5-5)))
            END IF

            IF (TMP .LT. 0.0D0) THEN
               IF (ZONE(J4-2) .LT. 0) GO TO 470
               IF (ZONE(J4-2) .EQ. 0) GO TO 480
            ELSE IF (TMP .GT. 0.0D0) THEN
               IF (ZONE(J4-2) .GT. 0) GO TO 470
               IF (ZONE(J4-2) .EQ. 0) GO TO 480
            ELSE
               GO TO 480
            END IF

            M = M + 1
            IF (M .GT. ZONE(1)) M = 1
            IF (I1-M) 410, 480, 410
  470    CONTINUE
  480    CONTINUE
  500 CONTINUE

      WRITE(*,*) 'K16 monte carlo: k2 =', K2, ', k3 =', K3
      END
