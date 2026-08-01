var i : int, n : int, acc : float, x : float, t : float;
array a[64] : float;
n := 50;
i := 0;
x := 1.5;
while (i < n) {
  a[i] := intToFloat(i) * 0.5 + 1.0;
  i := i + 1
};
acc := 0.0;
i := 0;
while (i < n) {
  t := a[i] * a[i];
  acc := acc + t;
  i := i + 1
};
acc := sqrt(acc);
printString("acc="); printFloat(acc); printString("\n")
