var i : int, k : int, rep : int,
    fuzz : float, buzz : float, fizz : float;
array w[1002] : float, b[4097] : float;

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
k := 1;
while (k <= 4096) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  b[k] := (buzz - fizz) * 0.1;
  k := k + 1
};

rep := 1;
while (rep <= 2781000) {
  i := 1;
  while (i <= 1001) {
    w[i] := 0.0;
    i := i + 1
  };
  w[1] := 0.01;
  i := 2;
  while (i <= 64) {
    k := 1;
    while (k <= i - 1) {
      w[i] := w[i] + b[(i - 1) * 64 + k] * w[i - k];
      k := k + 1
    };
    i := i + 1
  };
  rep := rep + 1
};
printFloat(w[64]); printString("\n")
