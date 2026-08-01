var a:int, b:int, c:int, i:int, s:int, inv:int, t1:int, t2:int, cp:int;
a := 4;
b := 6;
c := a + 2;
s := 0;
i := 0;
while (i < 300) {
  inv := a * b;
  cp := inv;
  t1 := (a + b) * c;
  t2 := (a + b) * c + cp;
  s := s + t1 - t2 + i;
  i := i + 1
};
printString("s="); printInt(s); printString("\n");
printString("inv="); printInt(inv); printString("\n")
