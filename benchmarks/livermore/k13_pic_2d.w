var ip : int, rep : int, i1 : int, j1 : int, i2 : int, j2 : int,
    ds : float, dw : float, fuzz : float, buzz : float, fizz : float,
    i : int, j : int, k : int;
array p[257] : float, b[4097] : float, c[4097] : float, h[6177] : float,
      y[1002] : float, z[1002] : float, e[97] : int, f[97] : int;

ds := 1.0;
dw := 0.5;
j := 1;
while (j <= 4) {
  k := 1;
  while (k <= 64) {
    p[(j - 1) * 64 + k] := ds;
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
while (j <= 64) {
  i := 1;
  while (i <= 64) {
    h[(j - 1) * 64 + i] := 0.0;
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

rep := 1;
while (rep <= 2570000) {
  ds := 1.0;
  dw := 0.5;
  j := 1;
  while (j <= 4) {
    k := 1;
    while (k <= 64) {
      p[(j - 1) * 64 + k] := ds;
      ds := ds + dw;
      k := k + 1
    };
    j := j + 1
  };
  j := 1;
  while (j <= 64) {
    i := 1;
    while (i <= 64) {
      h[(j - 1) * 64 + i] := 0.0;
      i := i + 1
    };
    j := j + 1
  };
  ip := 1;
  while (ip <= 64) {
    i1 := floatToInt(p[(1 - 1) * 64 + ip]);
    j1 := floatToInt(p[(2 - 1) * 64 + ip]);
    i1 := i1 & 63;
    j1 := j1 & 63;
    p[(3 - 1) * 64 + ip] := p[(3 - 1) * 64 + ip] + b[(j1 + 1 - 1) * 64 + (i1 + 1)];
    p[(4 - 1) * 64 + ip] := p[(4 - 1) * 64 + ip] + c[(j1 + 1 - 1) * 64 + (i1 + 1)];
    p[(1 - 1) * 64 + ip] := p[(1 - 1) * 64 + ip] + p[(3 - 1) * 64 + ip];
    p[(2 - 1) * 64 + ip] := p[(2 - 1) * 64 + ip] + p[(4 - 1) * 64 + ip];
    i2 := floatToInt(p[(1 - 1) * 64 + ip]);
    j2 := floatToInt(p[(2 - 1) * 64 + ip]);
    i2 := (i2 & 63) - 1;
    j2 := (j2 & 63) - 1;
    p[(1 - 1) * 64 + ip] := p[(1 - 1) * 64 + ip] + y[i2 + 32];
    p[(2 - 1) * 64 + ip] := p[(2 - 1) * 64 + ip] + z[j2 + 32];
    i2 := i2 + e[i2 + 32];
    j2 := j2 + f[j2 + 32];
    h[(j2 + 1 - 1) * 64 + (i2 + 1)] := h[(j2 + 1 - 1) * 64 + (i2 + 1)] + 1.0;
    ip := ip + 1
  };
  rep := rep + 1
};
printFloat(p[(1 - 1) * 64 + 1]); printString("\n")
