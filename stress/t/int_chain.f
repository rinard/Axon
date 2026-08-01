      PROGRAM INTCHAIN
      INTEGER*8 A,B,C,D,E,R
      A=1234567
      B=-7654321
      C=9999
      D=-333
      E=2718281
      R=A*B+C*D-E*A+B*C-D*E+A*C-B*D
      WRITE(*,'(A,I0)') 'r1=',R
      R=A-B-C-D-E
      WRITE(*,'(A,I0)') 'r2=',R
      R=A+B*C-D+E*A-B+C*D-E+A
      WRITE(*,'(A,I0)') 'r3=',R
      R=MOD((((A+B)*C+D)*E-A),1000000007_8)
      WRITE(*,'(A,I0)') 'r4=',R
      END
