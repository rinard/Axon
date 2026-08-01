var a : int, b : int, i : int, s : int, t : int;
a := 7;
b := 13;
s := 0;
i := 0;
while (i < 1000) {
  t := a * b;
  s := s + t + i;
  i := i + 1
};
printString("s="); printInt(s); printString("\n");
printString("t="); printInt(t); printString("\n")
