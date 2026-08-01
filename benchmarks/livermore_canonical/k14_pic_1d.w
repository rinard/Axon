var rep : int, k : int, i : int, n : int,
    flx : float, fw : float,
    fuzz : float, buzz : float, fizz : float;
array vx[1002] : float, xx[1002] : float, xi[1002] : float,
      ex1[1002] : float, dex1[1002] : float,
      ex[1002] : float, dex[1002] : float, grd[1002] : float,
      rx[1002] : float, rh[2050] : float,
      ix[1002] : int, ir[1002] : int,
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
flx := spacer[27];

i := 1;
while (i <= 1001) {
  grd[i] := intToFloat((i - 1) % 512) + 1.5;
  i := i + 1
};

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
k := 1;
while (k <= 1001) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  ex[k] := (buzz - fizz) * 0.1;
  k := k + 1
};

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
k := 1;
while (k <= 1001) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  dex[k] := (buzz - fizz) * 0.1;
  k := k + 1
};

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
k := 1;
while (k <= 2049) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  rh[k] := (buzz - fizz) * 0.1;
  k := k + 1
};

i := 1;
while (i <= 1001) {
  vx[i] := 0.0;
  xx[i] := 0.0;
  xi[i] := 0.0;
  ex1[i] := 0.0;
  dex1[i] := 0.0;
  rx[i] := 0.0;
  ix[i] := 0;
  ir[i] := 0;
  i := i + 1
};

n := 1001;
fw := 1.0;
rep := 1;
while (rep <= 2700000) {
  k := 1;
  while (k <= n) {
    vx[k] := 0.0;
    xx[k] := 0.0;
    ix[k] := floatToInt(grd[k]);
    xi[k] := intToFloat(ix[k]);
    ex1[k] := ex[ix[k]];
    dex1[k] := dex[ix[k]];
    k := k + 1
  };
  k := 1;
  while (k <= n) {
    vx[k] := vx[k] + ex1[k] + (xx[k] - xi[k]) * dex1[k];
    xx[k] := xx[k] + vx[k] + flx;
    ir[k] := floatToInt(xx[k]);
    rx[k] := xx[k] - intToFloat(ir[k]);
    ir[k] := (ir[k] & 2047) + 1;
    xx[k] := rx[k] + intToFloat(ir[k]);
    k := k + 1
  };
  k := 1;
  while (k <= n) {
    rh[ir[k]] := rh[ir[k]] + fw - rx[k];
    rh[ir[k] + 1] := rh[ir[k] + 1] + rx[k];
    k := k + 1
  };
  rep := rep + 1
};
printFloat(rh[1]); printString("\n")
