var a : int, b : int, i : int, s : int, u : int, v : int;
a := 6;
b := 9;
s := 0;
i := 0;
while (i < 200) {
  u := (a + i) * (b + i);
  v := (a + i) * (b + i) + a;
  s := s + u - v;
  i := i + 1
};
printString("s="); printInt(s); printString("\n")
