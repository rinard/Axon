var k : int, rep : int,
    fuzz : float, buzz : float, fizz : float;
array x[1001] : float, y[1002] : float;

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

rep := 1;
while (rep <= 41000000) {
  k := 1;
  while (k <= 1000) {
    x[k] := y[k + 1] - y[k];
    k := k + 1
  };
  rep := rep + 1
};
printFloat(x[1]); printString("\n")
