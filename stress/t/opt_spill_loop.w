var b0:int,b1:int,b2:int,b3:int,b4:int,b5:int,b6:int,b7:int,b8:int,b9:int,b10:int,b11:int,b12:int,b13:int,b14:int,b15:int,b16:int,b17:int,b18:int,b19:int,b20:int,b21:int,b22:int,b23:int,i:int,acc:int;
b0:=1; b1:=2; b2:=3; b3:=4; b4:=5; b5:=6; b6:=7; b7:=8;
b8:=9; b9:=10; b10:=11; b11:=12; b12:=13; b13:=14; b14:=15; b15:=16;
b16:=17; b17:=18; b18:=19; b19:=20; b20:=21; b21:=22; b22:=23; b23:=24;
acc := 0;
i := 0;
while (i < 50) {
  acc := acc + b0 + b1 + b2 + b3 + b4 + b5 + b6 + b7 + b8 + b9 + b10 + b11;
  acc := acc + b12 + b13 + b14 + b15 + b16 + b17 + b18 + b19 + b20 + b21 + b22 + b23;
  acc := acc + i + b0 * b23;
  i := i + 1
};
printString("acc="); printInt(acc); printString("\n");
printString("b0="); printInt(b0); printString("\n");
printString("b23="); printInt(b23); printString("\n")
