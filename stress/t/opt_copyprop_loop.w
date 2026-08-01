var a:int, b:int, c:int, d:int, i:int, s:int;
s := 0;
i := 0;
while (i < 150) {
  a := i + 1;
  b := a;
  c := b;
  d := c + b;
  s := s + a + b + c + d;
  i := i + 1
};
printString("s="); printInt(s); printString("\n")
