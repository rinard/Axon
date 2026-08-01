var rep : int, kx : int, ky : int, nl1 : int, nl2 : int,
    a11 : float, a12 : float, a13 : float,
    a21 : float, a22 : float, a23 : float,
    a31 : float, a32 : float, a33 : float,
    sig : float, fw : float,
    idx : int, idx_yp : int, idx_ym : int, idx_xp : int, idx_xm : int,
    k1 : int, k2 : int, k3 : int,
    fuzz : float, buzz : float, fizz : float;
array u1[1011] : float, u2[1011] : float, u3[1011] : float,
      du1[102] : float, du2[102] : float, du3[102] : float,
      spacer[40] : float;

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
idx := 1;
while (idx <= 39) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  spacer[idx] := (buzz - fizz) * 0.1;
  idx := idx + 1
};
a11 := spacer[1];  a12 := spacer[2];  a13 := spacer[3];
a21 := spacer[4];  a22 := spacer[5];  a23 := spacer[6];
a31 := spacer[7];  a32 := spacer[8];  a33 := spacer[9];
sig := spacer[34];

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
k3 := 1;
while (k3 <= 2) {
  k2 := 1;
  while (k2 <= 101) {
    k1 := 1;
    while (k1 <= 5) {
      buzz := (1.0 - fuzz) * buzz + fuzz;
      fuzz := 0.0 - fuzz;
      u1[(k3 - 1) * 505 + (k2 - 1) * 5 + k1] := (buzz - fizz) * 0.1;
      k1 := k1 + 1
    };
    k2 := k2 + 1
  };
  k3 := k3 + 1
};

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
k3 := 1;
while (k3 <= 2) {
  k2 := 1;
  while (k2 <= 101) {
    k1 := 1;
    while (k1 <= 5) {
      buzz := (1.0 - fuzz) * buzz + fuzz;
      fuzz := 0.0 - fuzz;
      u2[(k3 - 1) * 505 + (k2 - 1) * 5 + k1] := (buzz - fizz) * 0.1;
      k1 := k1 + 1
    };
    k2 := k2 + 1
  };
  k3 := k3 + 1
};

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
k3 := 1;
while (k3 <= 2) {
  k2 := 1;
  while (k2 <= 101) {
    k1 := 1;
    while (k1 <= 5) {
      buzz := (1.0 - fuzz) * buzz + fuzz;
      fuzz := 0.0 - fuzz;
      u3[(k3 - 1) * 505 + (k2 - 1) * 5 + k1] := (buzz - fizz) * 0.1;
      k1 := k1 + 1
    };
    k2 := k2 + 1
  };
  k3 := k3 + 1
};

rep := 1;
while (rep <= 22600000) {
  nl1 := 1;
  nl2 := 2;
  fw := 2.0;
  kx := 2;
  while (kx <= 3) {
    ky := 2;
    while (ky <= 100) {
      idx_yp := (nl1 - 1) * 505 + ky * 5 + kx;
      idx_ym := (nl1 - 1) * 505 + (ky - 2) * 5 + kx;
      idx    := (nl1 - 1) * 505 + (ky - 1) * 5 + kx;
      idx_xp := (nl1 - 1) * 505 + (ky - 1) * 5 + kx + 1;
      idx_xm := (nl1 - 1) * 505 + (ky - 1) * 5 + kx - 1;
      du1[ky] := u1[idx_yp] - u1[idx_ym];
      du2[ky] := u2[idx_yp] - u2[idx_ym];
      du3[ky] := u3[idx_yp] - u3[idx_ym];
      u1[(nl2 - 1) * 505 + (ky - 1) * 5 + kx] := u1[idx]
        + a11 * du1[ky] + a12 * du2[ky] + a13 * du3[ky]
        + sig * (u1[idx_xp] - fw * u1[idx] + u1[idx_xm]);
      u2[(nl2 - 1) * 505 + (ky - 1) * 5 + kx] := u2[idx]
        + a21 * du1[ky] + a22 * du2[ky] + a23 * du3[ky]
        + sig * (u2[idx_xp] - fw * u2[idx] + u2[idx_xm]);
      u3[(nl2 - 1) * 505 + (ky - 1) * 5 + kx] := u3[idx]
        + a31 * du1[ky] + a32 * du2[ky] + a33 * du3[ky]
        + sig * (u3[idx_xp] - fw * u3[idx] + u3[idx_xm]);
      ky := ky + 1
    };
    kx := kx + 1
  };
  rep := rep + 1
};
printFloat(u1[(2 - 1) * 505 + (2 - 1) * 5 + 2]); printString("\n")
