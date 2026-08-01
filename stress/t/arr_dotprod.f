      PROGRAM ARRDOTPROD
      INTEGER*8 I,N,A,B,DOT,T
      INTEGER*8 U(0:31),W(0:31)
      N=32
      I=0
   10 IF (I.GE.N) GOTO 20
      U(I)=I-16
      W(I)=2*I+3
      I=I+1
      GOTO 10
   20 CONTINUE
      DOT=0
      I=0
   30 IF (I.GE.N) GOTO 40
      A=U(I)
      B=W(I)
      DOT=DOT+A*B
      I=I+1
      GOTO 30
   40 CONTINUE
      WRITE(*,'(A,I0)') 'dot=',DOT
      T=U(31)
      WRITE(*,'(A,I0)') 'u31=',T
      T=W(0)
      WRITE(*,'(A,I0)') 'w0=',T
      END
