var i : int, n : int, dot : float, p : float;
array u[64] : float, v[64] : float;
n := 32;
i := 0;
while (i < n) {
  u[i] := intToFloat(i) * 0.5 - 1.0;
  v[i] := intToFloat(i) * 0.1 + 2.0;
  i := i + 1
};
dot := 0.0;
i := 0;
while (i < n) {
  p := u[i] * v[i];
  dot := dot + p;
  i := i + 1
};
printString("dot= "); printFloat(dot); printString("\n")
