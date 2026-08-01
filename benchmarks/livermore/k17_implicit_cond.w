var rep : int, i : int, j : int, ink : int, n : int, k : int,
    scale : float, xnm : float, e6 : float, e3 : float,
    xnei : float, xnc : float,
    fuzz : float, buzz : float, fizz : float,
    phase : int, done : int;
array vsp[102] : float, vstp[102] : float, vxne[102] : float,
      vxnd[102] : float, ve3[102] : float, vlr[102] : float,
      vlin[102] : float;

n := 101;

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
k := 1;
while (k <= n) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  vsp[k] := (buzz - fizz) * 0.1;
  vstp[k] := (buzz - fizz) * 0.1;
  vxne[k] := (buzz - fizz) * 0.1;
  vxnd[k] := (buzz - fizz) * 0.1;
  ve3[k] := (buzz - fizz) * 0.1;
  vlr[k] := (buzz - fizz) * 0.1;
  vlin[k] := (buzz - fizz) * 0.1;
  k := k + 1
};

rep := 1;
while (rep <= 23048000) {
  i := n - 1;
  j := 0;
  ink := 0 - 1;
  scale := 5.0 / 3.0;
  xnm := 1.0 / 3.0;
  e6 := 1.03 / 3.07;
  phase := 1;
  done := 0;
  while (done == 0) {
    if (phase == 0) {
      e6 := xnm * vsp[i + 1] + vstp[i + 1];
      vxne[i + 1] := e6;
      xnm := e6;
      ve3[i + 1] := e6;
      i := i + ink;
      if (i == j) {
        done := 1
      } else {
        phase := 1
      }
    } else {
      e3 := xnm * vlr[i + 1] + vlin[i + 1];
      xnei := vxne[i + 1];
      vxnd[i + 1] := e6;
      xnc := scale * e3;
      if (xnm > xnc) {
        phase := 0
      } else {
        if (xnei > xnc) {
          phase := 0
        } else {
          ve3[i + 1] := e3;
          e6 := e3 + e3 - xnm;
          vxne[i + 1] := e3 + e3 - xnei;
          xnm := e6;
          i := i + ink;
          if (i == j) {
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
printFloat(ve3[51]); printString("\n")
