      PROGRAM INTPREC
      INTEGER*8 A,B,C,D
      A=ISHFT(1_8+2_8,3)
      B=IAND(16_8+8_8,12_8)
      C=IOR(IEOR(5_8,3_8),8_8)
      D=ISHFT(1_8,4+1)
      WRITE(*,'(A,I0)') 'a=',A
      WRITE(*,'(A,I0)') 'b=',B
      WRITE(*,'(A,I0)') 'c=',C
      WRITE(*,'(A,I0)') 'd=',D
      END
