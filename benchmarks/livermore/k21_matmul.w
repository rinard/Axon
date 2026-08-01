var i : int, j : int, k : int, rep : int,
    fuzz : float, buzz : float, fizz : float;
array px[2526] : float, vy[2526] : float, cx[2526] : float;

k := 1;
while (k <= 2525) {
  px[k] := 0.0;
  k := k + 1
};

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
j := 1;
while (j <= 101) {
  i := 1;
  while (i <= 25) {
    buzz := (1.0 - fuzz) * buzz + fuzz;
    fuzz := 0.0 - fuzz;
    cx[(j - 1) * 25 + i] := (buzz - fizz) * 0.1;
    i := i + 1
  };
  j := j + 1
};

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
j := 1;
while (j <= 25) {
  i := 1;
  while (i <= 101) {
    buzz := (1.0 - fuzz) * buzz + fuzz;
    fuzz := 0.0 - fuzz;
    vy[(j - 1) * 101 + i] := (buzz - fizz) * 0.1;
    i := i + 1
  };
  j := j + 1
};

rep := 1;
while (rep <= 2476000) {
  j := 1;
  while (j <= 101) {
    i := 1;
    while (i <= 25) {
      px[(j - 1) * 25 + i] := 0.0;
      i := i + 1
    };
    j := j + 1
  };
  k := 1;
  while (k <= 25) {
    i := 1;
    while (i <= 25) {
      j := 1;
      while (j <= 101) {
        px[(j - 1) * 25 + i] := px[(j - 1) * 25 + i] + vy[(i - 1) * 101 + k] * cx[(j - 1) * 25 + k];
        j := j + 1
      };
      i := i + 1
    };
    k := k + 1
  };
  rep := rep + 1
};
printFloat(px[(51 - 1) * 25 + 13]); printString("\n")
