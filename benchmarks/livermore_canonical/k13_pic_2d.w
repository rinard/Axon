var rep : int, k : int, i : int, j : int,
    i1 : int, j1 : int, i2 : int, j2 : int, n : int,
    ds : float, dw : float, fw : float,
    fuzz : float, buzz : float, fizz : float;
array p[257] : float, b[4097] : float, c[4097] : float,
      h[16385] : float, y[1002] : float, z[1002] : float,
      e[97] : int, f[97] : int;

ds := 1.0;
dw := 0.5;
j := 1;
while (j <= 4) {
  k := 1;
  while (k <= 64) {
    p[(k - 1) * 4 + j] := ds;
    ds := ds + dw;
    k := k + 1
  };
  j := j + 1
};

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
j := 1;
while (j <= 64) {
  i := 1;
  while (i <= 64) {
    buzz := (1.0 - fuzz) * buzz + fuzz;
    fuzz := 0.0 - fuzz;
    b[(j - 1) * 64 + i] := (buzz - fizz) * 0.1;
    i := i + 1
  };
  j := j + 1
};

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
j := 1;
while (j <= 64) {
  i := 1;
  while (i <= 64) {
    buzz := (1.0 - fuzz) * buzz + fuzz;
    fuzz := 0.0 - fuzz;
    c[(j - 1) * 64 + i] := (buzz - fizz) * 0.1;
    i := i + 1
  };
  j := j + 1
};

j := 1;
while (j <= 128) {
  i := 1;
  while (i <= 128) {
    h[(j - 1) * 128 + i] := 0.0;
    i := i + 1
  };
  j := j + 1
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

i := 1;
while (i <= 96) {
  e[i] := (i - 1) % 64;
  f[i] := (i - 1) % 64;
  i := i + 1
};

n := 64;
fw := 1.0;
rep := 1;
while (rep <= 33800000) {
  k := 1;
  while (k <= n) {
    i1 := floatToInt(p[(k - 1) * 4 + 1]);
    j1 := floatToInt(p[(k - 1) * 4 + 2]);
    i1 := 1 + (i1 % 64);
    j1 := 1 + (j1 % 64);
    p[(k - 1) * 4 + 3] := p[(k - 1) * 4 + 3] + b[(j1 - 1) * 64 + i1];
    p[(k - 1) * 4 + 4] := p[(k - 1) * 4 + 4] + c[(j1 - 1) * 64 + i1];
    p[(k - 1) * 4 + 1] := p[(k - 1) * 4 + 1] + p[(k - 1) * 4 + 3];
    p[(k - 1) * 4 + 2] := p[(k - 1) * 4 + 2] + p[(k - 1) * 4 + 4];
    i2 := floatToInt(p[(k - 1) * 4 + 1]);
    j2 := floatToInt(p[(k - 1) * 4 + 2]);
    i2 := i2 % 64;
    j2 := j2 % 64;
    p[(k - 1) * 4 + 1] := p[(k - 1) * 4 + 1] + y[i2 + 32];
    p[(k - 1) * 4 + 2] := p[(k - 1) * 4 + 2] + z[j2 + 32];
    i2 := i2 + e[i2 + 32];
    j2 := j2 + f[j2 + 32];
    h[(j2 - 1) * 128 + i2] := h[(j2 - 1) * 128 + i2] + fw;
    k := k + 1
  };
  rep := rep + 1
};
printFloat(p[(1 - 1) * 4 + 1]); printString("\n")
