      PROGRAM INTFIB
      INTEGER*8 A,B,T,I,N
      A=0
      B=1
      N=90
      I=0
   10 IF (I.GE.N) GOTO 20
      T=A+B
      A=B
      B=T
      I=I+1
      GOTO 10
   20 CONTINUE
      WRITE(*,'(A,I0)') 'fib90=',A
      WRITE(*,'(A,I0)') 'fib91=',B
      END
