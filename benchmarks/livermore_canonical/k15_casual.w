var rep : int, j : int, k : int, i : int, n : int, ng : int, nz : int,
    ar : float, br : float, r : float, s : float, t : float,
    fuzz : float, buzz : float, fizz : float;
array vy[708] : float, vh[708] : float, vf[708] : float,
      vg[708] : float, vs[708] : float;

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
j := 1;
while (j <= 7) {
  i := 1;
  while (i <= 101) {
    buzz := (1.0 - fuzz) * buzz + fuzz;
    fuzz := 0.0 - fuzz;
    vh[(j - 1) * 101 + i] := (buzz - fizz) * 0.1;
    i := i + 1
  };
  j := j + 1
};

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
j := 1;
while (j <= 7) {
  i := 1;
  while (i <= 101) {
    buzz := (1.0 - fuzz) * buzz + fuzz;
    fuzz := 0.0 - fuzz;
    vf[(j - 1) * 101 + i] := (buzz - fizz) * 0.1;
    if (vf[(j - 1) * 101 + i] <= 0.0) {
      vf[(j - 1) * 101 + i] := 0.001
    } else {
      skip
    };
    i := i + 1
  };
  j := j + 1
};

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
j := 1;
while (j <= 7) {
  i := 1;
  while (i <= 101) {
    buzz := (1.0 - fuzz) * buzz + fuzz;
    fuzz := 0.0 - fuzz;
    vg[(j - 1) * 101 + i] := (buzz - fizz) * 0.1;
    i := i + 1
  };
  j := j + 1
};

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
j := 1;
while (j <= 7) {
  i := 1;
  while (i <= 101) {
    buzz := (1.0 - fuzz) * buzz + fuzz;
    fuzz := 0.0 - fuzz;
    vs[(j - 1) * 101 + i] := (buzz - fizz) * 0.1;
    i := i + 1
  };
  j := j + 1
};

j := 1;
while (j <= 7) {
  i := 1;
  while (i <= 101) {
    vy[(j - 1) * 101 + i] := 0.0;
    i := i + 1
  };
  j := j + 1
};

n := 101;
rep := 1;
while (rep <= 6600000) {
  ng := 7;
  nz := n;
  ar := 0.053;
  br := 0.073;
  j := 2;
  while (j <= ng) {
    k := 2;
    while (k <= nz) {
      if (j >= ng) {
        vy[(j - 1) * 101 + k] := 0.0
      } else {
        if (vh[j * 101 + k] > vh[(j - 1) * 101 + k]) {
          t := ar
        } else {
          t := br
        };
        if (vf[(j - 1) * 101 + k] < vf[(j - 1) * 101 + k - 1]) {
          if (vh[(j - 1) * 101 + k - 1] > vh[j * 101 + k - 1]) {
            r := vh[(j - 1) * 101 + k - 1]
          } else {
            r := vh[j * 101 + k - 1]
          };
          s := vf[(j - 1) * 101 + k - 1]
        } else {
          if (vh[(j - 1) * 101 + k] > vh[j * 101 + k]) {
            r := vh[(j - 1) * 101 + k]
          } else {
            r := vh[j * 101 + k]
          };
          s := vf[(j - 1) * 101 + k]
        };
        vy[(j - 1) * 101 + k] := sqrt(vg[(j - 1) * 101 + k] * vg[(j - 1) * 101 + k] + r * r) * t / s;
        if (k >= nz) {
          vs[(j - 1) * 101 + k] := 0.0
        } else {
          if (vf[(j - 1) * 101 + k] < vf[(j - 2) * 101 + k]) {
            if (vg[(j - 2) * 101 + k] > vg[(j - 2) * 101 + k + 1]) {
              r := vg[(j - 2) * 101 + k]
            } else {
              r := vg[(j - 2) * 101 + k + 1]
            };
            s := vf[(j - 2) * 101 + k];
            t := br
          } else {
            if (vg[(j - 1) * 101 + k] > vg[(j - 1) * 101 + k + 1]) {
              r := vg[(j - 1) * 101 + k]
            } else {
              r := vg[(j - 1) * 101 + k + 1]
            };
            s := vf[(j - 1) * 101 + k];
            t := ar
          };
          vs[(j - 1) * 101 + k] := sqrt(vh[(j - 1) * 101 + k] * vh[(j - 1) * 101 + k] + r * r) * t / s
        }
      };
      k := k + 1
    };
    j := j + 1
  };
  rep := rep + 1
};
printFloat(vy[(2 - 1) * 101 + 2]); printString("\n")
