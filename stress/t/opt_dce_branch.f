      PROGRAM ODCEB
      INTEGER*8 X,R,DEAD,K
      X=42
      R=0
      DEAD=0
      IF (1.EQ.1) THEN
        R=R+100
      ELSE
        DEAD=DEAD+999
        R=R-50
      END IF
      IF (0.EQ.1) THEN
        DEAD=DEAD+7
        R=R*3
      ELSE
        R=R+5
      END IF
      K=2+2
      IF (K.EQ.5) THEN
        R=R+1000
      ELSE
        R=R+1
      END IF
      WRITE(*,'(A,I0)') 'r=',R
      WRITE(*,'(A,I0)') 'dead=',DEAD
      END
