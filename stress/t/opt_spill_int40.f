      PROGRAM OSP40
      INTEGER*8 A0,A1,A2,A3,A4,A5,A6,A7,A8,A9
      INTEGER*8 A10,A11,A12,A13,A14,A15,A16,A17,A18,A19
      INTEGER*8 A20,A21,A22,A23,A24,A25,A26,A27,A28,A29
      INTEGER*8 A30,A31,A32,A33,A34,A35,A36,A37,A38,A39
      INTEGER*8 ACC,I
      A0=1
      A1=1
      A2=2
      A3=3
      A4=5
      A5=8
      A6=13
      A7=21
      A8=34
      A9=55
      A10=2
      A11=4
      A12=6
      A13=8
      A14=10
      A15=12
      A16=14
      A17=16
      A18=18
      A19=20
      A20=3
      A21=6
      A22=9
      A23=12
      A24=15
      A25=18
      A26=21
      A27=24
      A28=27
      A29=30
      A30=5
      A31=10
      A32=15
      A33=20
      A34=25
      A35=30
      A36=35
      A37=40
      A38=45
      A39=50
      ACC=0
      I=0
   10 IF (I.GE.7) GOTO 20
      ACC=ACC+A0+A39+A1+A38+A2+A37+A3+A36+A4+A35
      ACC=ACC+A5+A34+A6+A33+A7+A32+A8+A31+A9+A30
      ACC=ACC+A10+A29+A11+A28+A12+A27+A13+A26+A14+A25
      ACC=ACC+A15+A24+A16+A23+A17+A22+A18+A21+A19+A20
      ACC=ACC+I*A0+A20*A21
      I=I+1
      GOTO 10
   20 CONTINUE
      WRITE(*,'(A,I0)') 'acc=',ACC
      WRITE(*,'(A,I0)') 'a0=',A0
      WRITE(*,'(A,I0)') 'a20=',A20
      WRITE(*,'(A,I0)') 'a39=',A39
      END
