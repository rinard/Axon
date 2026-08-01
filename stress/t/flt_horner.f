      PROGRAM FHORNER
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      INTEGER*8 I,N
      DIMENSION COEF(0:7)
      COEF(0)=1.0D0
      COEF(1)=-(3.0D0)
      COEF(2)=2.0D0
      COEF(3)=0.5D0
      COEF(4)=-(1.25D0)
      N=5
      X=1.7D0
      ACC=0.0D0
      I=N-1
   10 IF (I.LT.0) GOTO 20
        C=COEF(I)
        ACC=ACC*X+C
        I=I-1
        GOTO 10
   20 CONTINUE
      WRITE(*,'(A,F0.6)') 'p= ',ACC
      END
