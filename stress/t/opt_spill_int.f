      PROGRAM OSPINT
      INTEGER*8 V0,V1,V2,V3,V4,V5,V6,V7,V8,V9
      INTEGER*8 V10,V11,V12,V13,V14,V15,V16,V17,V18,V19
      INTEGER*8 V20,V21,V22,V23,V24,V25,V26,V27,V28,V29,S
      V0=1
      V1=2
      V2=3
      V3=4
      V4=5
      V5=6
      V6=7
      V7=8
      V8=9
      V9=10
      V10=11
      V11=12
      V12=13
      V13=14
      V14=15
      V15=16
      V16=17
      V17=18
      V18=19
      V19=20
      V20=21
      V21=22
      V22=23
      V23=24
      V24=25
      V25=26
      V26=27
      V27=28
      V28=29
      V29=30
      S=V0+V1+V2+V3+V4+V5+V6+V7+V8+V9+V10+V11+V12+V13+V14+V15+
     &  V16+V17+V18+V19+V20+V21+V22+V23+V24+V25+V26+V27+V28+V29
      S=S+V0*V29+V1*V28+V2*V27+V14*V15
      WRITE(*,'(A,I0)') 's=',S
      WRITE(*,'(A,I0)') 'v0=',V0
      WRITE(*,'(A,I0)') 'v15=',V15
      WRITE(*,'(A,I0)') 'v29=',V29
      END
