var k : int, rep : int, q : float,
    fuzz : float, buzz : float, fizz : float;
array z[1002] : float, x[1002] : float;

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
k := 1;
while (k <= 1001) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  z[k] := (buzz - fizz) * 0.1;
  k := k + 1
};

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

rep := 1;
while (rep <= 31726000) {
  q := 0.0;
  k := 1;
  while (k <= 1001) {
    q := q + z[k] * x[k];
    k := k + 1
  };
  rep := rep + 1
};
printFloat(q); printString("\n")
