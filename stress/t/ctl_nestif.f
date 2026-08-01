      PROGRAM CTLNESTIF
      INTEGER*8 X,R
      X=37
      IF (X.LT.10) THEN
        R=1
      ELSE IF (X.LT.20) THEN
        R=2
      ELSE IF (X.LT.30) THEN
        R=3
      ELSE IF (X.LT.40) THEN
        R=4
      ELSE IF (X.LT.50) THEN
        R=5
      ELSE
        R=6
      END IF
      WRITE(*,'(A,I0)') 'r=',R
      END
