var k : int, rep : int, q : float, r : float, t : float,
    fuzz : float, buzz : float, fizz : float;
array x[1002] : float, u[1002] : float, z[1002] : float, y[1002] : float,
      spacer[40] : float;

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
k := 1;
while (k <= 39) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  spacer[k] := (buzz - fizz) * 0.1;
  k := k + 1
};
q := spacer[28];
r := spacer[30];
t := spacer[36];

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
k := 1;
while (k <= 1001) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  u[k] := (buzz - fizz) * 0.1;
  k := k + 1
};

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
  y[k] := (buzz - fizz) * 0.1;
  k := k + 1
};

rep := 1;
while (rep <= 17000000) {
  k := 1;
  while (k <= 995) {
    x[k] := u[k] + r * (z[k] + r * y[k])
          + t * (u[k + 3] + r * (u[k + 2] + r * u[k + 1])
          + t * (u[k + 6] + q * (u[k + 5] + q * u[k + 4])));
    k := k + 1
  };
  rep := rep + 1
};
printFloat(x[1]); printString("\n")
