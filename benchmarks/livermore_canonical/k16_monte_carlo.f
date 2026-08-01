C     Kernel 16 -- Monte Carlo search loop (canonical)
C     From "The Livermore Fortran Kernels" (UCRL-53745), F.H. McMahon, 1986
C     Canonical body: lines 351-385 of the kernels listing.
C     R, S, T pulled from canonical SPACER positions 30, 32, 36.
C
      PROGRAM K16
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      INTEGER REP, ZONE
      DIMENSION D(300), PLAN(300), ZONE(300)
      DIMENSION SPACER(39)
C
C     SPACER -> R, S, T at positions 30, 32, 36
C
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 5 K = 1, 39
         BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
         FUZZ = -FUZZ
         SPACER(K) = (BUZZ - FIZZ) * 0.1D0
    5 CONTINUE
      R = SPACER(30)
      S = SPACER(32)
      T = SPACER(36)
C
C     PLAN, D via SIGNEL (independent streams)
C
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 10 I = 1, 300
         BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
         FUZZ = -FUZZ
         PLAN(I) = (BUZZ - FIZZ) * 0.1D0
   10 CONTINUE
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 12 I = 1, 300
         BUZZ = (1.0D0 - FUZZ) * BUZZ + FUZZ
         FUZZ = -FUZZ
         D(I) = (BUZZ - FIZZ) * 0.1D0
   12 CONTINUE
C
C     ZONE(i) = (i-1) mod (n+1); ZONE(1) = 5
C
      N  = 75
      II = N / 3
      LB = II + II
      DO 15 I = 1, 300
         ZONE(I) = MOD(I-1, N+1)
   15 CONTINUE
      ZONE(1) = 5
C
C     Kernel 16 body (canonical state machine, lines 357-385)
C
      DO 500 REP = 1, 400000000
         M  = 1
         I1 = M
         K2 = 0
         K3 = 0
  410    J2 = (N+N)*(M-1) + 1
         DO 470 K = 1, N
            K2 = K2 + 1
            J4 = J2 + K + K
            J5 = ZONE(J4)
            IF (J5 .LT. N) GO TO 420
            IF (J5 .EQ. N) GO TO 475
            GO TO 450
  415       IF (J5 .LT. N - II) GO TO 430
            GO TO 425
  420       IF (J5 .LT. N - LB) GO TO 435
            GO TO 415
  425       TMP = PLAN(J5) - R
            GO TO 446
  430       TMP = PLAN(J5) - S
            GO TO 446
  435       TMP = PLAN(J5) - T
            GO TO 446
  440       IF (ZONE(J4-1) .LT. 0) GO TO 455
            IF (ZONE(J4-1) .EQ. 0) GO TO 485
            GO TO 470
  445       IF (ZONE(J4-1) .LT. 0) GO TO 470
            IF (ZONE(J4-1) .EQ. 0) GO TO 485
            GO TO 455
  446       IF (TMP .LT. 0.0D0) GO TO 445
            IF (TMP .EQ. 0.0D0) GO TO 480
            GO TO 440
  450       K3 = K3 + 1
            DEXPR = D(J5) - (D(J5-1)*(T-D(J5-2))**2
     &                       + (S-D(J5-3))**2
     &                       + (R-D(J5-4))**2)
            IF (DEXPR .LT. 0.0D0) GO TO 445
            IF (DEXPR .EQ. 0.0D0) GO TO 480
            GO TO 440
  455       M = M + 1
            IF (M .GT. ZONE(1)) GO TO 460
            GO TO 465
  460       M = 1
  465       IF (I1 .EQ. M) GO TO 480
            GO TO 410
  470    CONTINUE
  475    CONTINUE
  480    CONTINUE
  485    CONTINUE
  500 CONTINUE
C
      WRITE(*,910) K2
      WRITE(*,920) K3
  910 FORMAT('k2 = ', I20)
  920 FORMAT('k3 = ', I20)
      END
