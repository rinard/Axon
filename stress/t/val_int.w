var n : int, s : int, i : int, p : int;
n := 20;
s := 0;
i := 1;
p := 1;
while (i <= n) {
  s := s + i;
  p := p * i;
  i := i + 1
};
printString("sum="); printInt(s); printString("\n");
printString("fact="); printInt(p); printString("\n")
