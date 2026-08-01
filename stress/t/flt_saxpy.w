var i : int, n : int, a : float, sum : float, t : float;
array x[64] : float, y[64] : float;
n := 40;
a := 2.5;
i := 0;
while (i < n) {
  x[i] := intToFloat(i) * 0.25;
  y[i] := intToFloat(i) + 1.0;
  i := i + 1
};
i := 0;
while (i < n) {
  y[i] := a * x[i] + y[i];
  i := i + 1
};
sum := 0.0;
i := 0;
while (i < n) {
  t := y[i];
  sum := sum + t;
  i := i + 1
};
printString("sum= "); printFloat(sum); printString("\n")
