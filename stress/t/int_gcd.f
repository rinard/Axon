      PROGRAM INTGCD
      INTEGER*8 A,B,T
      A=1071
      B=462
   10 IF (B.EQ.0) GOTO 20
      T=MOD(A,B)
      A=B
      B=T
      GOTO 10
   20 CONTINUE
      WRITE(*,'(A,I0)') 'gcd=',A
      A=123456
      B=7890
   30 IF (B.EQ.0) GOTO 40
      T=MOD(A,B)
      A=B
      B=T
      GOTO 30
   40 CONTINUE
      WRITE(*,'(A,I0)') 'gcd2=',A
      END
