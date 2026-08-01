var j : int, k : int, rep : int, qa : float,
    fuzz : float, buzz : float, fizz : float;
array za[708] : float, zr[708] : float, zb[708] : float,
      zu[708] : float, zv[708] : float, zz[708] : float;

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
j := 1;
while (j <= 7) {
  k := 1;
  while (k <= 101) {
    buzz := (1.0 - fuzz) * buzz + fuzz;
    fuzz := 0.0 - fuzz;
    za[(j - 1) * 101 + k] := (buzz - fizz) * 0.1;
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
    zb[(j - 1) * 101 + k] := (buzz - fizz) * 0.1;
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
    zu[(j - 1) * 101 + k] := (buzz - fizz) * 0.1;
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
    zv[(j - 1) * 101 + k] := (buzz - fizz) * 0.1;
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

rep := 1;
while (rep <= 8581000) {
  j := 2;
  while (j <= 6) {
    k := 2;
    while (k <= 100) {
      qa := za[j * 101 + k] * zr[(j - 1) * 101 + k] + za[(j - 2) * 101 + k] * zb[(j - 1) * 101 + k]
          + za[(j - 1) * 101 + k + 1] * zu[(j - 1) * 101 + k] + za[(j - 1) * 101 + k - 1] * zv[(j - 1) * 101 + k] + zz[(j - 1) * 101 + k];
      za[(j - 1) * 101 + k] := za[(j - 1) * 101 + k] + 0.175 * (qa - za[(j - 1) * 101 + k]);
      k := k + 1
    };
    j := j + 1
  };
  rep := rep + 1
};
printFloat(za[(4 - 1) * 101 + 51]); printString("\n")
