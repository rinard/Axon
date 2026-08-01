      PROGRAM OCOPY
      INTEGER*8 A,B,C,D,E,R
      A=99
      B=A
      C=B
      D=C
      E=D+A
      R=A+B+C+D+E
      WRITE(*,'(A,I0)') 'r=',R
      WRITE(*,'(A,I0)') 'e=',E
      END
