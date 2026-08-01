      PROGRAM FSQRT
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      X=2.0D0
      Y=SQRT(X)
      WRITE(*,'(A,F0.6)') 'y= ',Y
      X=1000000.0D0
      Y=SQRT(X)
      WRITE(*,'(A,F0.6)') 'y= ',Y
      END
