var k : int, rep : int, expmax : float,
    fuzz : float, buzz : float, fizz : float;
array u[1002] : float, v[1002] : float, x[1002] : float,
      y[1002] : float, w[1002] : float, spacer[40] : float;

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
expmax := spacer[26];

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
  v[k] := (buzz - fizz) * 0.1;
  if (v[k] <= 0.0) { v[k] := 1.0 } else { skip };
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
  if (x[k] <= 0.0) { x[k] := 0.01 } else { skip };
  k := k + 1
};

k := 1;
while (k <= 1001) {
  y[k] := 0.0;
  w[k] := 0.0;
  k := k + 1
};

rep := 1;
while (rep <= 48640000) {
  expmax := 20.0;
  u[101] := 0.99 * expmax * v[101];
  k := 1;
  while (k <= 101) {
    y[k] := u[k] / v[k];
    w[k] := x[k] / (exp(y[k]) - 1.0);
    k := k + 1
  };
  rep := rep + 1
};
printFloat(w[51]); printString("\n")
