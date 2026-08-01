      PROGRAM FNEWTON
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      INTEGER*8 I,N
      TARGET=612.0D0
      G=25.0D0
      N=20
      DO 10 I=0,N-1
        T=TARGET/G
        G=0.5D0*(G+T)
   10 CONTINUE
      WRITE(*,'(A,F0.6)') 'g= ',G
      WRITE(*,'(A,F0.6)') 'ref= ',SQRT(TARGET)
      END
