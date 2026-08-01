var k : int, rep : int, dk : float, s : float, t : float, di : float, dn : float,
    fuzz : float, buzz : float, fizz : float;
array x[1002] : float, y[1002] : float, z[1002] : float,
      w[1002] : float, v[1002] : float, u[1002] : float,
      g[1002] : float, xx[1002] : float, vx[1002] : float,
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
dk := spacer[15];
s := spacer[32];
t := spacer[36];

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
  w[k] := (buzz - fizz) * 0.1;
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
  k := k + 1
};

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
  g[k] := (buzz - fizz) * 0.1;
  k := k + 1
};

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
k := 1;
while (k <= 1001) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  xx[k] := (buzz - fizz) * 0.1 + 1.0;
  k := k + 1
};

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
k := 1;
while (k <= 1001) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  vx[k] := (buzz - fizz) * 0.1 + 2.0;
  k := k + 1
};

rep := 1;
while (rep <= 1570000) {
  fuzz := 0.001234500;
  buzz := 1.0 + fuzz;
  fizz := 1.1 * fuzz;
  k := 1;
  while (k <= 1001) {
    buzz := (1.0 - fuzz) * buzz + fuzz;
    fuzz := 0.0 - fuzz;
    xx[k] := (buzz - fizz) * 0.1 + 1.0;
    k := k + 1
  };
  k := 1;
  while (k <= 1000) {
    di := y[k] - g[k] / (xx[k] + dk);
    dn := 0.2;
    if (di < 0.0) {
      dn := z[k] / di;
      if (t < dn) { dn := t } else { skip };
      if (s > dn) { dn := s } else { skip }
    } else {
      if (di > 0.0) {
        dn := z[k] / di;
        if (t < dn) { dn := t } else { skip };
        if (s > dn) { dn := s } else { skip }
      } else {
        skip
      }
    };
    x[k] := ((w[k] + v[k] * dn) * xx[k] + u[k]) / (vx[k] + v[k] * dn);
    xx[k + 1] := (x[k] - xx[k]) * dn + xx[k];
    k := k + 1
  };
  rep := rep + 1
};
printFloat(x[1]); printString("\n")
