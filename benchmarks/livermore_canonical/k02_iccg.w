var k : int, i : int, rep : int, ii : int, ipnt : int, ipntp : int, done : int,
    fuzz : float, buzz : float, fizz : float;
array x[2051] : float, v[2051] : float;

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
k := 1;
while (k <= 2050) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  v[k] := (buzz - fizz) * 0.1;
  k := k + 1
};

rep := 1;
while (rep <= 7500000) {
  fuzz := 0.001234500;
  buzz := 1.0 + fuzz;
  fizz := 1.1 * fuzz;
  k := 1;
  while (k <= 2050) {
    buzz := (1.0 - fuzz) * buzz + fuzz;
    fuzz := 0.0 - fuzz;
    x[k] := (buzz - fizz) * 0.1;
    k := k + 1
  };
  ii := 1001;
  ipntp := 0;
  done := 0;
  while (done == 0) {
    ipnt := ipntp;
    ipntp := ipntp + ii;
    ii := ii / 2;
    i := ipntp + 1;
    k := ipnt + 2;
    while (k <= ipntp) {
      i := i + 1;
      x[i] := x[k] - v[k] * x[k - 1] - v[k + 1] * x[k + 1];
      k := k + 2
    };
    if (ii <= 1) {
      done := 1
    } else {
      skip
    }
  };
  rep := rep + 1
};
printFloat(x[1001]); printString("\n")
