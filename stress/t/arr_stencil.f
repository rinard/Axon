      PROGRAM ARRSTENCIL
      INTEGER*8 W,H,R,C,ACC,T,S,MX
      INTEGER*8 G(0:34),O(0:34)
      W=7
      H=5
      R=0
   10 IF (R.GE.H) GOTO 30
      C=0
   20 IF (C.GE.W) GOTO 25
      G(R*W+C)=MOD(R*W+C,9_8)
      C=C+1
      GOTO 20
   25 CONTINUE
      R=R+1
      GOTO 10
   30 CONTINUE
      R=0
   40 IF (R.GE.H) GOTO 70
      C=0
   50 IF (C.GE.W) GOTO 65
      ACC=0
      T=G(R*W+C)
      ACC=ACC+T
      IF (R.GT.0) THEN
        T=G((R-1)*W+C)
        ACC=ACC+T
      ENDIF
      IF (R.LT.H-1) THEN
        T=G((R+1)*W+C)
        ACC=ACC+T
      ENDIF
      IF (C.GT.0) THEN
        T=G(R*W+(C-1))
        ACC=ACC+T
      ENDIF
      IF (C.LT.W-1) THEN
        T=G(R*W+(C+1))
        ACC=ACC+T
      ENDIF
      O(R*W+C)=ACC
      C=C+1
      GOTO 50
   65 CONTINUE
      R=R+1
      GOTO 40
   70 CONTINUE
      S=0
      MX=0
      R=0
   80 IF (R.GE.H*W) GOTO 90
      T=O(R)
      S=S+T
      IF (T.GT.MX) MX=T
      R=R+1
      GOTO 80
   90 CONTINUE
      WRITE(*,'(A,I0)') 'stencil_sum=',S
      WRITE(*,'(A,I0)') 'stencil_max=',MX
      T=O(2*W+3)
      WRITE(*,'(A,I0)') 'center=',T
      T=O(0)
      WRITE(*,'(A,I0)') 'corner=',T
      END
