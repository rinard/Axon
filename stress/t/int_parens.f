      PROGRAM INTPARENS
      INTEGER*8 A,B,C,R,S,T
      A=5
      B=3
      C=7
      R=(A+B)*(C-A)-B*C+(A*B*C)/2
      S=((A-B)*C+(A+C)*B)*(C-B)-A
      T=A+B*C-(A-B)*(C+A)/B+MOD(C,A)
      WRITE(*,'(A,I0)') 'r=',R
      WRITE(*,'(A,I0)') 's=',S
      WRITE(*,'(A,I0)') 't=',T
      END
