      PROGRAM OCPLOOP
      INTEGER*8 A,B,C,D,I,S
      S=0
      I=0
   10 IF (I.GE.150) GOTO 20
      A=I+1
      B=A
      C=B
      D=C+B
      S=S+A+B+C+D
      I=I+1
      GOTO 10
   20 CONTINUE
      WRITE(*,'(A,I0)') 's=',S
      END
