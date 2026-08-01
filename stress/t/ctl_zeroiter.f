      PROGRAM CTLZERO
      INTEGER*8 I,C,N
      C=0
      N=0
      I=5
   10 IF (I.GE.5) GOTO 20
      C=C+1
      I=I+1
      GOTO 10
   20 CONTINUE
      I=0
   30 IF (I.LE.10) GOTO 40
      C=C+100
      I=I+1
      GOTO 30
   40 CONTINUE
      I=0
   50 IF (I.GE.N) GOTO 60
      C=C+1000
      I=I+1
      GOTO 50
   60 CONTINUE
      WRITE(*,'(A,I0)') 'c=',C
      END
