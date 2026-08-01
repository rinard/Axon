      PROGRAM ODCEDV
      INTEGER*8 A,B,C,USED,I
      A=10
      B=20
      C=30
      USED=0
      I=0
   10 IF (I.GE.100) GOTO 20
      A=A+1
      B=B*2
      C=C-3
      USED=USED+I
      I=I+1
      GOTO 10
   20 CONTINUE
      WRITE(*,'(A,I0)') 'used=',USED
      END
