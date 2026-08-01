var k : int, n : int, sum : float, d : float, kf : float;
n := 5000;
sum := 0.0;
k := 1;
while (k < n) {
  kf := intToFloat(k);
  d := kf * kf;
  sum := sum + 1.0 / d;
  k := k + 1
};
printString("sum= "); printFloat(sum); printString("\n")
