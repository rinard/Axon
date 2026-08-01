      PROGRAM OCFOLD
      INTEGER*8 A,B,C,D,E,F
      A=5
      B=A+3
      C=B*2
      D=C-A
      E=(A+B+C+D)*2
      F=MOD(E,7_8)+ISHFT(C,1)-ISHFT(D,-1)
      WRITE(*,'(A,I0)') 'a=',A
      WRITE(*,'(A,I0)') 'e=',E
      WRITE(*,'(A,I0)') 'f=',F
      END
