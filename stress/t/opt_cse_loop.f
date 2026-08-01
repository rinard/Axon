      PROGRAM OCSEL
      INTEGER*8 A,B,I,S,U,V
      A=6
      B=9
      S=0
      I=0
   10 IF (I.GE.200) GOTO 20
      U=(A+I)*(B+I)
      V=(A+I)*(B+I)+A
      S=S+U-V
      I=I+1
      GOTO 10
   20 CONTINUE
      WRITE(*,'(A,I0)') 's=',S
      END
