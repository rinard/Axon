var rep : int, k : int, j : int, ink : int, n : int, kk : int,
    scale : float, xnm : float, e3 : float, e6 : float,
    xnei : float, xnc : float, dw : float, fw : float, tw : float,
    fuzz : float, buzz : float, fizz : float,
    phase : int, done : int;
array vsp[102] : float, vstp[102] : float, vxne[102] : float,
      vxnd[102] : float, ve3[102] : float, vlr[102] : float,
      vlin[102] : float;

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
kk := 1;
while (kk <= 101) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  vsp[kk] := (buzz - fizz) * 0.1;
  kk := kk + 1
};

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
kk := 1;
while (kk <= 101) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  vstp[kk] := (buzz - fizz) * 0.1;
  kk := kk + 1
};

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
kk := 1;
while (kk <= 101) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  vxne[kk] := (buzz - fizz) * 0.1;
  kk := kk + 1
};

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
kk := 1;
while (kk <= 101) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  vxnd[kk] := (buzz - fizz) * 0.1;
  kk := kk + 1
};

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
kk := 1;
while (kk <= 101) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  ve3[kk] := (buzz - fizz) * 0.1;
  kk := kk + 1
};

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
kk := 1;
while (kk <= 101) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  vlr[kk] := (buzz - fizz) * 0.1;
  kk := kk + 1
};

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
kk := 1;
while (kk <= 101) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  vlin[kk] := (buzz - fizz) * 0.1;
  kk := kk + 1
};

n := 101;
rep := 1;
while (rep <= 66400000) {
  dw := 5.0 / 3.0;
  fw := 1.0 / 3.0;
  tw := 1.03 / 3.07;
  k := n;
  j := 1;
  ink := 0 - 1;
  scale := dw;
  xnm := fw;
  e6 := tw;
  phase := 1;
  done := 0;
  while (done == 0) {
    if (phase == 0) {
      e6 := xnm * vsp[k] + vstp[k];
      vxne[k] := e6;
      xnm := e6;
      ve3[k] := e6;
      k := k + ink;
      if (k == j) {
        done := 1
      } else {
        phase := 1
      }
    } else {
      e3 := xnm * vlr[k] + vlin[k];
      xnei := vxne[k];
      vxnd[k] := e6;
      xnc := scale * e3;
      if (xnm > xnc) {
        phase := 0
      } else {
        if (xnei > xnc) {
          phase := 0
        } else {
          ve3[k] := e3;
          e6 := e3 + e3 - xnm;
          vxne[k] := e3 + e3 - xnei;
          xnm := e6;
          k := k + ink;
          if (k == j) {
            done := 1
          } else {
            phase := 1
          }
        }
      }
    }
  };
  rep := rep + 1
};
printFloat(vxne[n]); printString("\n")
