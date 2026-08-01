var s : int, i : int, n : int, alt : int;
s := 0;
i := 1;
n := 1000;
while (i <= n) {
  s := s + i * i;
  i := i + 1
};
printString("sumsq="); printInt(s); printString("\n");
alt := 0;
i := 1;
while (i <= n) {
  alt := alt + (-1) * i;
  s := s - i;
  i := i + 1
};
printString("alt="); printInt(alt); printString("\n")
