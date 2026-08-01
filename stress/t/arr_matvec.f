      PROGRAM ARRMATVEC
      INTEGER*8 N,R,C,ACC,A,X,T,S
      INTEGER*8 M(0:35),V(0:5),Y(0:5)
      N=6
      R=0
   10 IF (R.GE.N) GOTO 30
      V(R)=R+1
      C=0
   20 IF (C.GE.N) GOTO 25
      M(R*N+C)=(R+1)*(C+1)-R
      C=C+1
      GOTO 20
   25 CONTINUE
      R=R+1
      GOTO 10
   30 CONTINUE
      R=0
   40 IF (R.GE.N) GOTO 60
      ACC=0
      C=0
   50 IF (C.GE.N) GOTO 55
      A=M(R*N+C)
      X=V(C)
      ACC=ACC+A*X
      C=C+1
      GOTO 50
   55 CONTINUE
      Y(R)=ACC
      R=R+1
      GOTO 40
   60 CONTINUE
      S=0
      R=0
   70 IF (R.GE.N) GOTO 80
      T=Y(R)
      S=S+T
      R=R+1
      GOTO 70
   80 CONTINUE
      WRITE(*,'(A,I0)') 'ysum=',S
      T=Y(0)
      WRITE(*,'(A,I0)') 'y0=',T
      T=Y(5)
      WRITE(*,'(A,I0)') 'y5=',T
      END
