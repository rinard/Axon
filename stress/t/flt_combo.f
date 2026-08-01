      PROGRAM FCOMBO
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      X=3.0D0
      Y=4.0D0
      D=SQRT(X*X+Y*Y)
      WRITE(*,'(A,F0.6)') 'd= ',D
      A=EXP(LOG(7.5D0))
      WRITE(*,'(A,F0.6)') 'a= ',A
      B=(2.0D0**0.5D0)*(2.0D0**0.5D0)
      WRITE(*,'(A,F0.6)') 'b= ',B
      R=MAX(SIN(1.0D0),COS(1.0D0))
      WRITE(*,'(A,F0.6)') 'r= ',R
      R=ABS(-(SQRT(2.0D0)))
      WRITE(*,'(A,F0.6)') 'r= ',R
      END
