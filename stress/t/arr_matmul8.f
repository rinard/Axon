      PROGRAM ARRMATMUL8
      INTEGER*8 N,R,C,K,ACC,A,B,T,S
      INTEGER*8 AR(0:63),BR(0:63),CR(0:63)
      N=8
      R=0
   10 IF (R.GE.N) GOTO 30
      C=0
   20 IF (C.GE.N) GOTO 25
      AR(R*N+C)=MOD((R+1)*(C+2),13_8)
      BR(R*N+C)=MOD(R*3+C+1,11_8)
      C=C+1
      GOTO 20
   25 CONTINUE
      R=R+1
      GOTO 10
   30 CONTINUE
      R=0
   40 IF (R.GE.N) GOTO 70
      C=0
   50 IF (C.GE.N) GOTO 65
      ACC=0
      K=0
   55 IF (K.GE.N) GOTO 60
      A=AR(R*N+K)
      B=BR(K*N+C)
      ACC=ACC+A*B
      K=K+1
      GOTO 55
   60 CONTINUE
      CR(R*N+C)=ACC
      C=C+1
      GOTO 50
   65 CONTINUE
      R=R+1
      GOTO 40
   70 CONTINUE
      S=0
      R=0
   80 IF (R.GE.N) GOTO 90
      T=CR(R*N+R)
      S=S+T
      R=R+1
      GOTO 80
   90 CONTINUE
      WRITE(*,'(A,I0)') 'diag=',S
      T=CR(0)
      WRITE(*,'(A,I0)') 'c00=',T
      T=CR(63)
      WRITE(*,'(A,I0)') 'c77=',T
      END
