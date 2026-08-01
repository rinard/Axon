      PROGRAM CTLMMM
      INTEGER*8 A,B,C,MN,MX,MED,SUM
      A=17
      B=4
      C=9
      IF (A.LT.B) THEN
        MN=A
      ELSE
        MN=B
      END IF
      IF (C.LT.MN) THEN
        MN=C
      END IF
      IF (A.GT.B) THEN
        MX=A
      ELSE
        MX=B
      END IF
      IF (C.GT.MX) THEN
        MX=C
      END IF
      SUM=A+B+C
      MED=SUM-MN-MX
      WRITE(*,'(A,I0)') 'mn=',MN
      WRITE(*,'(A,I0)') 'mx=',MX
      WRITE(*,'(A,I0)') 'med=',MED
      END
