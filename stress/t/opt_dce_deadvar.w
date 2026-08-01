var a : int, b : int, c : int, used : int, i : int;
a := 10;
b := 20;
c := 30;
used := 0;
i := 0;
while (i < 100) {
  a := a + 1;
  b := b * 2;
  c := c - 3;
  used := used + i;
  i := i + 1
};
printString("used="); printInt(used); printString("\n")
