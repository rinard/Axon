var k : int, rep : int, expmax : float, fw : float,
    fuzz : float, buzz : float, fizz : float;
array u[102] : float, v[102] : float, w[102] : float,
      x[102] : float, y[102] : float;

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
k := 1;
while (k <= 101) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  u[k] := (buzz - fizz) * 0.1;
  k := k + 1
};

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
k := 1;
while (k <= 101) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  v[k] := (buzz - fizz) * 0.1;
  if (v[k] <= 0.0) { v[k] := 1.0 } else { skip };
  k := k + 1
};

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
k := 1;
while (k <= 101) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  x[k] := (buzz - fizz) * 0.1;
  k := k + 1
};

k := 1;
while (k <= 101) {
  y[k] := 0.0;
  w[k] := 0.0;
  k := k + 1
};

rep := 1;
while (rep <= 51900000) {
  expmax := 20.0;
  fw := 1.0;
  u[101] := 0.99 * expmax * v[101];
  k := 1;
  while (k <= 101) {
    y[k] := u[k] / v[k];
    w[k] := x[k] / (exp(y[k]) - fw);
    k := k + 1
  };
  rep := rep + 1
};
printFloat(w[51]); printString("\n")
