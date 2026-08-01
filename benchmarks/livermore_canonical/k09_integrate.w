var i : int, j : int, k : int, rep : int,
    c0 : float,
    dm22 : float, dm23 : float, dm24 : float, dm25 : float,
    dm26 : float, dm27 : float, dm28 : float,
    fuzz : float, buzz : float, fizz : float;
array px[2526] : float, spacer[40] : float;

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
i := 1;
while (i <= 39) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  spacer[i] := (buzz - fizz) * 0.1;
  i := i + 1
};
c0   := spacer[12];
dm22 := spacer[16]; dm23 := spacer[17]; dm24 := spacer[18];
dm25 := spacer[19]; dm26 := spacer[20]; dm27 := spacer[21];
dm28 := spacer[22];

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
j := 1;
while (j <= 101) {
  i := 1;
  while (i <= 25) {
    buzz := (1.0 - fuzz) * buzz + fuzz;
    fuzz := 0.0 - fuzz;
    px[(j - 1) * 25 + i] := (buzz - fizz) * 0.1;
    i := i + 1
  };
  j := j + 1
};

rep := 1;
while (rep <= 77700000) {
  k := 1;
  while (k <= 101) {
    px[(k - 1) * 25 + 1] := dm28 * px[(k - 1) * 25 + 13]
                          + dm27 * px[(k - 1) * 25 + 12]
                          + dm26 * px[(k - 1) * 25 + 11]
                          + dm25 * px[(k - 1) * 25 + 10]
                          + dm24 * px[(k - 1) * 25 + 9]
                          + dm23 * px[(k - 1) * 25 + 8]
                          + dm22 * px[(k - 1) * 25 + 7]
                          + c0 * (px[(k - 1) * 25 + 5] + px[(k - 1) * 25 + 6])
                          + px[(k - 1) * 25 + 3];
    k := k + 1
  };
  rep := rep + 1
};
printFloat(px[(1 - 1) * 25 + 1]); printString("\n")
