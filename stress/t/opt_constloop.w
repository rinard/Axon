var n : int, m : int, i : int, s : int;
n := 10;
m := n * 2;
s := 0;
i := 0;
while (i < m) {
  s := s + i * n;
  i := i + 1
};
printString("m="); printInt(m); printString("\n");
printString("s="); printInt(s); printString("\n")
