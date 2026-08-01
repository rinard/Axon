      PROGRAM INTPOWER
      INTEGER*8 BASE,IEXX,R,I
      BASE=3
      IEXX=40
      R=1
      I=0
   10 IF (I.GE.IEXX) GOTO 20
      R=R*BASE
      I=I+1
      GOTO 10
   20 CONTINUE
      WRITE(*,'(A,I0)') 'p1=',R
      BASE=7
      IEXX=25
      R=1
      I=0
   30 IF (I.GE.IEXX) GOTO 40
      R=R*BASE
      I=I+1
      GOTO 30
   40 CONTINUE
      WRITE(*,'(A,I0)') 'p2=',R
      END
