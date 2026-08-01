var k : int, j : int, lw : int, m : int, rep : int, temp : float,
    fuzz : float, buzz : float, fizz : float;
array x[1202] : float, y[1002] : float;

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
k := 1;
while (k <= 1001) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  y[k] := (buzz - fizz) * 0.1;
  k := k + 1
};

m := (1001 - 7) / 2;

rep := 1;
while (rep <= 11250000) {
  fuzz := 0.001234500;
  buzz := 1.0 + fuzz;
  fizz := 1.1 * fuzz;
  k := 1;
  while (k <= 1001) {
    buzz := (1.0 - fuzz) * buzz + fuzz;
    fuzz := 0.0 - fuzz;
    x[k] := (buzz - fizz) * 0.1;
    k := k + 1
  };
  k := 7;
  while (k <= 1001) {
    lw := k - 6;
    temp := x[k];
    j := 5;
    while (j <= 1001) {
      temp := temp - x[lw] * y[j];
      lw := lw + 1;
      j := j + 5
    };
    x[k] := y[5] * temp;
    k := k + m
  };
  rep := rep + 1
};
printFloat(x[7]); printString("\n")
