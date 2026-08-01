      PROGRAM INTDIVSIGN
      INTEGER*8 A,B,C,D,E,F,G,H
      A=-7_8/2_8
      B=7_8/(-2_8)
      C=(-7_8)/(-2_8)
      D=7_8/2_8
      E=MOD(-7_8,3_8)
      F=MOD(7_8,-3_8)
      G=MOD(-7_8,-3_8)
      H=MOD(7_8,3_8)
      WRITE(*,'(A,I0)') 'a=',A
      WRITE(*,'(A,I0)') 'b=',B
      WRITE(*,'(A,I0)') 'c=',C
      WRITE(*,'(A,I0)') 'd=',D
      WRITE(*,'(A,I0)') 'e=',E
      WRITE(*,'(A,I0)') 'f=',F
      WRITE(*,'(A,I0)') 'g=',G
      WRITE(*,'(A,I0)') 'h=',H
      END
