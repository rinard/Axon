      PROGRAM OPEEP
      INTEGER*8 X,A,B,C,D,E
      X=41
      A=X+0
      B=A*1
      C=B-0
      D=C*2
      E=D+D*0
      E=E+IAND(X,X)-IOR(X,X)+IEOR(X,0_8)
      WRITE(*,'(A,I0)') 'a=',A
      WRITE(*,'(A,I0)') 'd=',D
      WRITE(*,'(A,I0)') 'e=',E
      END
