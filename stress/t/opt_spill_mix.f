      PROGRAM OSPMIX
      IMPLICIT DOUBLE PRECISION (G)
      INTEGER*8 I0,I1,I2,I3,I4,I5,I6,I7,I8,I9
      INTEGER*8 I10,I11,I12,I13,I14,I15,ISUM
      DOUBLE PRECISION G0,G1,G2,G3,G4,G5,G6,G7,G8,G9
      DOUBLE PRECISION G10,G11,G12,G13,G14,G15,FSUM
      I0=1
      I1=2
      I2=3
      I3=4
      I4=5
      I5=6
      I6=7
      I7=8
      I8=9
      I9=10
      I10=11
      I11=12
      I12=13
      I13=14
      I14=15
      I15=16
      G0=1.25D0
      G1=2.25D0
      G2=3.25D0
      G3=4.25D0
      G4=5.25D0
      G5=6.25D0
      G6=7.25D0
      G7=8.25D0
      G8=9.25D0
      G9=10.25D0
      G10=11.25D0
      G11=12.25D0
      G12=13.25D0
      G13=14.25D0
      G14=15.25D0
      G15=16.25D0
      ISUM=I0+I1+I2+I3+I4+I5+I6+I7+I8+I9+I10+I11+I12+I13+I14+I15
      FSUM=G0+G1+G2+G3+G4+G5+G6+G7+G8+G9+G10+G11+G12+G13+G14+G15
      ISUM=ISUM+I0*I15+I7*I8
      FSUM=FSUM+G0*G15+G7*G8
      WRITE(*,'(A,I0)') 'isum=',ISUM
      WRITE(*,'(A,F0.6)') 'fsum=',FSUM
      WRITE(*,'(A,I0)') 'i0=',I0
      WRITE(*,'(A,F0.6)') 'g15=',G15
      END
