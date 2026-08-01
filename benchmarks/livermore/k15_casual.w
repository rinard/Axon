var rep : int, j : int, k : int, ar : float, br : float,
    r : float, s : float, t : float,
    fuzz : float, buzz : float, fizz : float;
array vy[2526] : float, vh[708] : float, vf[708] : float,
      vg[708] : float, vs[708] : float;

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
j := 1;
while (j <= 25) {
  k := 1;
  while (k <= 101) {
    buzz := (1.0 - fuzz) * buzz + fuzz;
    fuzz := 0.0 - fuzz;
    vy[(j - 1) * 101 + k] := (buzz - fizz) * 0.1;
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
    vh[(j - 1) * 101 + k] := (buzz - fizz) * 0.1;
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
    vf[(j - 1) * 101 + k] := (buzz - fizz) * 0.1;
    if (vf[(j - 1) * 101 + k] <= 0.0) { vf[(j - 1) * 101 + k] := 0.001 } else { skip };
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
    vg[(j - 1) * 101 + k] := (buzz - fizz) * 0.1;
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
    vs[(j - 1) * 101 + k] := (buzz - fizz) * 0.1;
    k := k + 1
  };
  j := j + 1
};

rep := 1;
while (rep <= 4249000) {
  ar := 0.053;
  br := 0.073;
  j := 2;
  while (j <= 7) {
    k := 2;
    while (k <= 101) {
      if (j >= 7) {
        vy[(j - 1) * 101 + k] := 0.0
      } else {
        if (vh[j * 101 + k] > vh[(j - 1) * 101 + k]) { t := ar } else { t := br };
        if (vf[(j - 1) * 101 + k] < vf[(j - 1) * 101 + k - 1]) {
          if (vh[(j - 1) * 101 + k - 1] > vh[j * 101 + k - 1]) { r := vh[(j - 1) * 101 + k - 1] } else { r := vh[j * 101 + k - 1] };
          s := vf[(j - 1) * 101 + k - 1]
        } else {
          if (vh[(j - 1) * 101 + k] > vh[j * 101 + k]) { r := vh[(j - 1) * 101 + k] } else { r := vh[j * 101 + k] };
          s := vf[(j - 1) * 101 + k]
        };
        vy[(j - 1) * 101 + k] := sqrt(vg[(j - 1) * 101 + k] * vg[(j - 1) * 101 + k] + r * r) * t / s;
        if (k >= 101) {
          vs[(j - 1) * 101 + k] := 0.0
        } else {
          if (vf[(j - 1) * 101 + k] < vf[(j - 2) * 101 + k]) {
            if (vg[(j - 2) * 101 + k] > vg[(j - 2) * 101 + k + 1]) { r := vg[(j - 2) * 101 + k] } else { r := vg[(j - 2) * 101 + k + 1] };
            s := vf[(j - 2) * 101 + k];
            t := br
          } else {
            if (vg[(j - 1) * 101 + k] > vg[(j - 1) * 101 + k + 1]) { r := vg[(j - 1) * 101 + k] } else { r := vg[(j - 1) * 101 + k + 1] };
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
printFloat(vy[(4 - 1) * 101 + 51]); printString("\n")
