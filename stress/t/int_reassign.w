var x : int, y : int, i : int;
x := 1000000007;
x := x + 1000000007;
x := x * 2;
x := x - 3;
x := -x;
y := 9223372036854775806;
y := y + 1;
y := y + 1;
i := 0;
while (i < 50) {
  x := x + 1;
  x := x * 2;
  x := x - i;
  i := i + 1
};
printString("x="); printInt(x); printString("\n");
printString("y="); printInt(y); printString("\n")
