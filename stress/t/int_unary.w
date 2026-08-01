var a : int, b : int, c : int, d : int, x : int, cnt : int;
a := 42;
b := -(-a);
c := ~(~a);
d := -a - 1;
d := ~a - d;
x := -9223372036854775807;
x := x - 1;
x := -x;
printString("b="); printInt(b); printString("\n");
printString("c="); printInt(c); printString("\n");
printString("d="); printInt(d); printString("\n");
printString("x="); printInt(x); printString("\n");
cnt := 0;
a := -5;
while (a <= 5) {
  if (a < 0) { cnt := cnt - a } else { cnt := cnt + a };
  a := a + 1
};
printString("cnt="); printInt(cnt); printString("\n")
