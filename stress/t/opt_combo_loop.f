      PROGRAM OCOMBO
      INTEGER*8 A,B,C,I,S,INV,T1,T2,CP
      A=4
      B=6
      C=A+2
      S=0
      I=0
   10 IF (I.GE.300) GOTO 20
      INV=A*B
      CP=INV
      T1=(A+B)*C
      T2=(A+B)*C+CP
      S=S+T1-T2+I
      I=I+1
      GOTO 10
   20 CONTINUE
      WRITE(*,'(A,I0)') 's=',S
      WRITE(*,'(A,I0)') 'inv=',INV
      END
