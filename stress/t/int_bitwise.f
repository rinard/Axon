      PROGRAM INTBITWISE
      INTEGER*8 A,B,C,D,E,F,G
      A=6148914691236517205_8
      B=3074457345618258602_8
      C=IAND(A,B)
      D=IOR(A,B)
      E=IEOR(A,B)
      F=NOT(A)
      G=NOT(0_8)
      WRITE(*,'(A,I0)') 'c=',C
      WRITE(*,'(A,I0)') 'd=',D
      WRITE(*,'(A,I0)') 'e=',E
      WRITE(*,'(A,I0)') 'f=',F
      WRITE(*,'(A,I0)') 'g=',G
      END
