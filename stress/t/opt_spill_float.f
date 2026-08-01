      PROGRAM OSPFLT
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      F0=1.5D0
      F1=2.5D0
      F2=3.5D0
      F3=4.5D0
      F4=5.5D0
      F5=6.5D0
      F6=7.5D0
      F7=8.5D0
      F8=9.5D0
      F9=10.5D0
      F10=11.5D0
      F11=12.5D0
      F12=13.5D0
      F13=14.5D0
      F14=15.5D0
      F15=16.5D0
      F16=17.5D0
      F17=18.5D0
      F18=19.5D0
      F19=20.5D0
      SUM=F0+F1+F2+F3+F4+F5+F6+F7+F8+F9+F10+F11+F12+F13+F14+F15+
     &  F16+F17+F18+F19
      SUM=SUM+F0*F19+F1*F18+F9*F10
      WRITE(*,'(A,F0.6)') 'sum=',SUM
      WRITE(*,'(A,F0.6)') 'f0=',F0
      WRITE(*,'(A,F0.6)') 'f10=',F10
      WRITE(*,'(A,F0.6)') 'f19=',F19
      END
