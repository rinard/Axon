var a : int, b : int, t : int, i : int, n : int;
a := 0;
b := 1;
n := 90;
i := 0;
while (i < n) {
  t := a + b;
  a := b;
  b := t;
  i := i + 1
};
printString("fib90="); printInt(a); printString("\n");
printString("fib91="); printInt(b); printString("\n")
