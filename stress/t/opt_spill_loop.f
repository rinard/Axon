      PROGRAM OSPLOOP
      INTEGER*8 B0,B1,B2,B3,B4,B5,B6,B7,B8,B9
      INTEGER*8 B10,B11,B12,B13,B14,B15,B16,B17,B18,B19
      INTEGER*8 B20,B21,B22,B23,I,ACC
      B0=1
      B1=2
      B2=3
      B3=4
      B4=5
      B5=6
      B6=7
      B7=8
      B8=9
      B9=10
      B10=11
      B11=12
      B12=13
      B13=14
      B14=15
      B15=16
      B16=17
      B17=18
      B18=19
      B19=20
      B20=21
      B21=22
      B22=23
      B23=24
      ACC=0
      I=0
   10 IF (I.GE.50) GOTO 20
      ACC=ACC+B0+B1+B2+B3+B4+B5+B6+B7+B8+B9+B10+B11
      ACC=ACC+B12+B13+B14+B15+B16+B17+B18+B19+B20+B21+B22+B23
      ACC=ACC+I+B0*B23
      I=I+1
      GOTO 10
   20 CONTINUE
      WRITE(*,'(A,I0)') 'acc=',ACC
      WRITE(*,'(A,I0)') 'b0=',B0
      WRITE(*,'(A,I0)') 'b23=',B23
      END
