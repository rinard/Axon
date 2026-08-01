var i0:int,i1:int,i2:int,i3:int,i4:int,i5:int,i6:int,i7:int,i8:int,i9:int,i10:int,i11:int,i12:int,i13:int,i14:int,i15:int,g0:float,g1:float,g2:float,g3:float,g4:float,g5:float,g6:float,g7:float,g8:float,g9:float,g10:float,g11:float,g12:float,g13:float,g14:float,g15:float,isum:int,fsum:float;
i0:=1; i1:=2; i2:=3; i3:=4; i4:=5; i5:=6; i6:=7; i7:=8;
i8:=9; i9:=10; i10:=11; i11:=12; i12:=13; i13:=14; i14:=15; i15:=16;
g0:=1.25; g1:=2.25; g2:=3.25; g3:=4.25; g4:=5.25; g5:=6.25; g6:=7.25; g7:=8.25;
g8:=9.25; g9:=10.25; g10:=11.25; g11:=12.25; g12:=13.25; g13:=14.25; g14:=15.25; g15:=16.25;
isum := i0+i1+i2+i3+i4+i5+i6+i7+i8+i9+i10+i11+i12+i13+i14+i15;
fsum := g0+g1+g2+g3+g4+g5+g6+g7+g8+g9+g10+g11+g12+g13+g14+g15;
isum := isum + i0*i15 + i7*i8;
fsum := fsum + g0*g15 + g7*g8;
printString("isum="); printInt(isum); printString("\n");
printString("fsum="); printFloat(fsum); printString("\n");
printString("i0="); printInt(i0); printString("\n");
printString("g15="); printFloat(g15); printString("\n")
