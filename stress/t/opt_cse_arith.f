      PROGRAM OCSEA
      INTEGER*8 X,Y,Z,P,Q,R
      X=17
      Y=23
      Z=4
      P=(X+Y)*Z
      Q=(X+Y)*Z+1
      R=(X+Y)*Z-(X+Y)
      WRITE(*,'(A,I0)') 'p=',P
      WRITE(*,'(A,I0)') 'q=',Q
      WRITE(*,'(A,I0)') 'r=',R
      END
