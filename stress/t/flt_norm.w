var i : int, n : int, ss : float, norm : float, t : float, scale : float;
array a[64] : float;
n := 20;
scale := 1.5;
i := 0;
while (i < n) {
  a[i] := intToFloat(i) - 5.0;
  i := i + 1
};
i := 0;
while (i < n) {
  a[i] := a[i] * scale;
  i := i + 1
};
ss := 0.0;
i := 0;
while (i < n) {
  t := a[i] * a[i];
  ss := ss + t;
  i := i + 1
};
norm := sqrt(ss);
printString("norm= "); printFloat(norm); printString("\n")
