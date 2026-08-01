C     Kernel 17 -- Implicit, conditional computation
C     From "The Livermore Fortran Kernels" (UCRL-53745), F.H. McMahon, 1986
C
C     This kernel uses GOTO-based control flow to implement an implicit
C     conditional computation with two interleaved code paths (labels 60/61)
C     and a forward exit (label 62).
C
      PROGRAM K17
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      DIMENSION VSP(101), VSTP(101), VXNE(101), VXND(101)
      DIMENSION VE3(101), VLR(101), VLIN(101)

      N = 101

C     Initialize arrays (simplified SIGNEL)
      FUZZ = 1.2345D-3
      BUZZ = 1.0D0 + FUZZ
      FIZZ = 1.1D0 * FUZZ
      DO 10 K = 1, N
         BUZZ = (1.0D0 - FUZZ)*BUZZ + FUZZ
         FUZZ = -FUZZ
         VSP(K)  = (BUZZ - FIZZ)*0.1D0
         VSTP(K) = (BUZZ - FIZZ)*0.1D0
         VXNE(K) = (BUZZ - FIZZ)*0.1D0
         VXND(K) = (BUZZ - FIZZ)*0.1D0
         VE3(K)  = (BUZZ - FIZZ)*0.1D0
         VLR(K)  = (BUZZ - FIZZ)*0.1D0
         VLIN(K) = (BUZZ - FIZZ)*0.1D0
   10 CONTINUE

      DO 500 IREP = 1, 23048000
         I   = N - 1
         J   = 0
         INK = -1
         SCALE = 5.0D0/3.0D0
         XNM   = 1.0D0/3.0D0
         E6    = 1.03D0/3.07D0
         GO TO 61

   60    E6      = XNM*VSP(I+1) + VSTP(I+1)
         VXNE(I+1) = E6
         XNM     = E6
         VE3(I+1)  = E6
         I       = I + INK
         IF (I.EQ.J) GO TO 62

   61    E3      = XNM*VLR(I+1) + VLIN(I+1)
         XNEI    = VXNE(I+1)
         VXND(I+1) = E6
         XNC     = SCALE*E3
         IF (XNM .GT. XNC) GO TO 60
         IF (XNEI .GT. XNC) GO TO 60
         VE3(I+1)  = E3
         E6      = E3 + E3 - XNM
         VXNE(I+1) = E3 + E3 - XNEI
         XNM     = E6
         I       = I + INK
         IF (I.NE.J) GO TO 61

   62    CONTINUE
  500 CONTINUE

      WRITE(*,*) 'K17 implicit cond: ve3(51) =', VE3(51)
      END
