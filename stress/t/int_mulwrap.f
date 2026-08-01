      PROGRAM INTMULWRAP
      INTEGER*8 A,B,C,E
      A=3037000500_8
      B=A*A
      C=9223372036854775807_8
      C=C*3_8
      E=-9223372036854775807_8-1_8
      E=E*E
      WRITE(*,'(A,I0)') 'b=',B
      WRITE(*,'(A,I0)') 'c=',C
      WRITE(*,'(A,I0)') 'e=',E
      END
