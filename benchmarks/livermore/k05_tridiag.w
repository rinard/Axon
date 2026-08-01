var i : int, rep : int,
    fuzz : float, buzz : float, fizz : float;
array x[1002] : float, y[1002] : float, z[1002] : float;

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
i := 1;
while (i <= 1001) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  y[i] := (buzz - fizz) * 0.1;
  i := i + 1
};

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
i := 1;
while (i <= 1001) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  z[i] := (buzz - fizz) * 0.1;
  i := i + 1
};

rep := 1;
while (rep <= 7770000) {
  fuzz := 0.001234500;
  buzz := 1.0 + fuzz;
  fizz := 1.1 * fuzz;
  i := 1;
  while (i <= 1001) {
    buzz := (1.0 - fuzz) * buzz + fuzz;
    fuzz := 0.0 - fuzz;
    x[i] := (buzz - fizz) * 0.1;
    i := i + 1
  };
  i := 2;
  while (i <= 1001) {
    x[i] := z[i] * (y[i] - x[i - 1]);
    i := i + 1
  };
  rep := rep + 1
};
printFloat(x[501]); printString("\n")
