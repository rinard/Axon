var k : int, m : int, rep : int,
    fuzz : float, buzz : float, fizz : float;
array x[1002] : float;

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

rep := 1;
while (rep <= 30595000) {
  x[501] := 0.0 - 10000000000.0;
  m := 1;
  k := 2;
  while (k <= 1001) {
    if (x[k] < x[m]) {
      m := k
    } else {
      skip
    };
    k := k + 1
  };
  rep := rep + 1
};
printInt(m); printString("\n");
printFloat(x[m]); printString("\n")
