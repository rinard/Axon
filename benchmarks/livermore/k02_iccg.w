var k : int, i : int, rep : int, ii : int, ipnt : int, ipntp : int,
    fuzz : float, buzz : float, fizz : float;
array x[1002] : float, v[1002] : float;

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
k := 1;
while (k <= 1001) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  v[k] := (buzz - fizz) * 0.1;
  k := k + 1
};

rep := 1;
while (rep <= 11495000) {
  fuzz := 0.001234500;
  buzz := 1.0 + fuzz;
  fizz := 1.1 * fuzz;
  k := 1;
  while (k <= 1001) {
    buzz := (1.0 - fuzz) * buzz + fuzz;
    fuzz := 0.0 - fuzz;
    x[k] := (buzz - fizz) * 0.1;
    k := k + 1
  };
  ii := 101;
  ipntp := 0;
  ipnt := ipntp;
  ipntp := ipntp + ii;
  ii := ii / 2;
  i := ipntp;
  k := ipnt + 2;
  while (k <= ipntp) {
    i := i + 1;
    x[i] := x[k] - v[k] * x[k - 1] - v[k + 1] * x[k + 1];
    k := k + 2
  };
  while (ii > 0) {
    ipnt := ipntp;
    ipntp := ipntp + ii;
    ii := ii / 2;
    i := ipntp;
    k := ipnt + 2;
    while (k <= ipntp) {
      i := i + 1;
      x[i] := x[k] - v[k] * x[k - 1] - v[k + 1] * x[k + 1];
      k := k + 2
    }
  };
  rep := rep + 1
};
printFloat(x[1]); printString("\n")
