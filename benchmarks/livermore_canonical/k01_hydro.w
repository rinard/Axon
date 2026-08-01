var q : float, r : float, t : float, k : int, rep : int,
    fuzz : float, buzz : float, fizz : float;
array x[1002] : float, y[1002] : float, z[1013] : float,
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
  y[k] := (buzz - fizz) * 0.1;
  k := k + 1
};

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
k := 1;
while (k <= 1012) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  z[k] := (buzz - fizz) * 0.1;
  k := k + 1
};

rep := 1;
while (rep <= 38000000) {
  k := 1;
  while (k <= 1001) {
    x[k] := q + y[k] * (r * z[k + 10] + t * z[k + 11]);
    k := k + 1
  };
  rep := rep + 1
};
printFloat(x[1]); printString("\n")
