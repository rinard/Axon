      PROGRAM FNORM
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      INTEGER*8 I,N
      DIMENSION A(0:63)
      N=20
      SCALE=1.5D0
      DO 10 I=0,N-1
        A(I)=DBLE(I)-5.0D0
   10 CONTINUE
      DO 20 I=0,N-1
        A(I)=A(I)*SCALE
   20 CONTINUE
      SS=0.0D0
      DO 30 I=0,N-1
        T=A(I)*A(I)
        SS=SS+T
   30 CONTINUE
      ANORM=SQRT(SS)
      WRITE(*,'(A,F0.6)') 'norm= ',ANORM
      END
