var rep : int, k : int, j : int, t : float, s : float,
    fuzz : float, buzz : float, fizz : float;
array za[708] : float, zb[708] : float, zp[708] : float, zq[708] : float,
      zr[708] : float, zm[708] : float, zu[708] : float, zv[708] : float,
      zz[708] : float;

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
j := 1;
while (j <= 7) {
  k := 1;
  while (k <= 101) {
    buzz := (1.0 - fuzz) * buzz + fuzz;
    fuzz := 0.0 - fuzz;
    zp[(j - 1) * 101 + k] := (buzz - fizz) * 0.1;
    k := k + 1
  };
  j := j + 1
};

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
j := 1;
while (j <= 7) {
  k := 1;
  while (k <= 101) {
    buzz := (1.0 - fuzz) * buzz + fuzz;
    fuzz := 0.0 - fuzz;
    zq[(j - 1) * 101 + k] := (buzz - fizz) * 0.1;
    k := k + 1
  };
  j := j + 1
};

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
j := 1;
while (j <= 7) {
  k := 1;
  while (k <= 101) {
    buzz := (1.0 - fuzz) * buzz + fuzz;
    fuzz := 0.0 - fuzz;
    zr[(j - 1) * 101 + k] := (buzz - fizz) * 0.1;
    k := k + 1
  };
  j := j + 1
};

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
j := 1;
while (j <= 7) {
  k := 1;
  while (k <= 101) {
    buzz := (1.0 - fuzz) * buzz + fuzz;
    fuzz := 0.0 - fuzz;
    zm[(j - 1) * 101 + k] := (buzz - fizz) * 0.1 + 10.0;
    k := k + 1
  };
  j := j + 1
};

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
j := 1;
while (j <= 7) {
  k := 1;
  while (k <= 101) {
    buzz := (1.0 - fuzz) * buzz + fuzz;
    fuzz := 0.0 - fuzz;
    zz[(j - 1) * 101 + k] := (buzz - fizz) * 0.1;
    k := k + 1
  };
  j := j + 1
};

j := 1;
while (j <= 7) {
  k := 1;
  while (k <= 101) {
    za[(j - 1) * 101 + k] := 0.0;
    zb[(j - 1) * 101 + k] := 0.0;
    zu[(j - 1) * 101 + k] := 0.0;
    zv[(j - 1) * 101 + k] := 0.0;
    k := k + 1
  };
  j := j + 1
};

rep := 1;
while (rep <= 1382000) {
  t := 0.0037;
  s := 0.0041;

  k := 2;
  while (k <= 6) {
    j := 2;
    while (j <= 100) {
      za[(k - 1) * 101 + j] := (zp[(k + 1 - 1) * 101 + j - 1] + zq[(k + 1 - 1) * 101 + j - 1]
                - zp[(k - 1) * 101 + j - 1] - zq[(k - 1) * 101 + j - 1])
              * (zr[(k - 1) * 101 + j] + zr[(k - 1) * 101 + j - 1])
              / (zm[(k - 1) * 101 + j - 1] + zm[(k + 1 - 1) * 101 + j - 1]);
      zb[(k - 1) * 101 + j] := (zp[(k - 1) * 101 + j - 1] + zq[(k - 1) * 101 + j - 1]
                - zp[(k - 1) * 101 + j] - zq[(k - 1) * 101 + j])
              * (zr[(k - 1) * 101 + j] + zr[(k - 1 - 1) * 101 + j])
              / (zm[(k - 1) * 101 + j] + zm[(k - 1) * 101 + j - 1]);
      j := j + 1
    };
    k := k + 1
  };

  k := 2;
  while (k <= 6) {
    j := 2;
    while (j <= 100) {
      zu[(k - 1) * 101 + j] := zu[(k - 1) * 101 + j] + s * (za[(k - 1) * 101 + j] * (zz[(k - 1) * 101 + j] - zz[(k - 1) * 101 + j + 1])
                - za[(k - 1) * 101 + j - 1] * (zz[(k - 1) * 101 + j] - zz[(k - 1) * 101 + j - 1])
                - zb[(k - 1) * 101 + j] * (zz[(k - 1) * 101 + j] - zz[(k - 1 - 1) * 101 + j])
                + zb[(k + 1 - 1) * 101 + j] * (zz[(k - 1) * 101 + j] - zz[(k + 1 - 1) * 101 + j]));
      zv[(k - 1) * 101 + j] := zv[(k - 1) * 101 + j] + s * (za[(k - 1) * 101 + j] * (zr[(k - 1) * 101 + j] - zr[(k - 1) * 101 + j + 1])
                - za[(k - 1) * 101 + j - 1] * (zr[(k - 1) * 101 + j] - zr[(k - 1) * 101 + j - 1])
                - zb[(k - 1) * 101 + j] * (zr[(k - 1) * 101 + j] - zr[(k - 1 - 1) * 101 + j])
                + zb[(k + 1 - 1) * 101 + j] * (zr[(k - 1) * 101 + j] - zr[(k + 1 - 1) * 101 + j]));
      j := j + 1
    };
    k := k + 1
  };

  k := 2;
  while (k <= 6) {
    j := 2;
    while (j <= 100) {
      zr[(k - 1) * 101 + j] := zr[(k - 1) * 101 + j] + t * zu[(k - 1) * 101 + j];
      zz[(k - 1) * 101 + j] := zz[(k - 1) * 101 + j] + t * zv[(k - 1) * 101 + j];
      j := j + 1
    };
    k := k + 1
  };

  rep := rep + 1
};
printFloat(zu[(4 - 1) * 101 + 51]); printString("\n")
