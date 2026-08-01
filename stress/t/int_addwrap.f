      PROGRAM INTADDWRAP
      INTEGER*8 A,B,C,D
      A=9223372036854775807_8
      B=A+1_8
      C=A+A
      D=-9223372036854775807_8
      D=D-2_8
      WRITE(*,'(A,I0)') 'b=',B
      WRITE(*,'(A,I0)') 'c=',C
      WRITE(*,'(A,I0)') 'd=',D
      END
