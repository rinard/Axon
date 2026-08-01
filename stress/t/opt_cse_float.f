      PROGRAM OCSEF
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      X=2.5D0
      Y=4.0D0
      Z=1.5D0
      P=(X+Y)*Z
      Q=(X+Y)*Z+X
      R=(X+Y)*Z*Z
      WRITE(*,'(A,F0.6)') 'p=',P
      WRITE(*,'(A,F0.6)') 'q=',Q
      WRITE(*,'(A,F0.6)') 'r=',R
      END
