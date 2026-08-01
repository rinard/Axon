      PROGRAM ARRTRANSP
      INTEGER*8 ROWS,COLS,R,C,T,S,OK,A,B
      INTEGER*8 M(0:23),TR(0:23)
      ROWS=4
      COLS=6
      R=0
   10 IF (R.GE.ROWS) GOTO 30
      C=0
   20 IF (C.GE.COLS) GOTO 25
      M(R*COLS+C)=R*10+C
      C=C+1
      GOTO 20
   25 CONTINUE
      R=R+1
      GOTO 10
   30 CONTINUE
      R=0
   40 IF (R.GE.ROWS) GOTO 60
      C=0
   50 IF (C.GE.COLS) GOTO 55
      T=M(R*COLS+C)
      TR(C*ROWS+R)=T
      C=C+1
      GOTO 50
   55 CONTINUE
      R=R+1
      GOTO 40
   60 CONTINUE
      OK=1
      R=0
   70 IF (R.GE.ROWS) GOTO 90
      C=0
   80 IF (C.GE.COLS) GOTO 85
      A=M(R*COLS+C)
      B=TR(C*ROWS+R)
      IF (A.NE.B) OK=0
      C=C+1
      GOTO 80
   85 CONTINUE
      R=R+1
      GOTO 70
   90 CONTINUE
      S=0
      R=0
  100 IF (R.GE.COLS*ROWS) GOTO 110
      T=TR(R)
      S=S+T
      R=R+1
      GOTO 100
  110 CONTINUE
      WRITE(*,'(A,I0)') 'ok=',OK
      WRITE(*,'(A,I0)') 'tsum=',S
      T=TR(1*ROWS+0)
      WRITE(*,'(A,I0)') 't10=',T
      END
