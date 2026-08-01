      PROGRAM INTSHIFT
      INTEGER*8 A,B,C,D,E,F,G
      A=ISHFT(1_8,10)
      B=ISHFT(1_8,62)
      C=ISHFT(-1_8,4)
      D=SHIFTA(-1024_8,3)
      E=SHIFTA(1024_8,3)
      F=-9223372036854775807_8-1_8
      F=SHIFTA(F,60)
      G=SHIFTA(255_8,0)
      WRITE(*,'(A,I0)') 'a=',A
      WRITE(*,'(A,I0)') 'b=',B
      WRITE(*,'(A,I0)') 'c=',C
      WRITE(*,'(A,I0)') 'd=',D
      WRITE(*,'(A,I0)') 'e=',E
      WRITE(*,'(A,I0)') 'f=',F
      WRITE(*,'(A,I0)') 'g=',G
      END
