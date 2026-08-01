var i : int, j : int, rep : int,
    dm28 : float, dm27 : float, dm26 : float, dm25 : float,
    dm24 : float, dm23 : float, dm22 : float, c0 : float,
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
dm22 := spacer[16]; dm23 := spacer[17]; dm24 := spacer[18]; dm25 := spacer[19];
dm26 := spacer[20]; dm27 := spacer[21]; dm28 := spacer[22]; c0 := spacer[12];

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
j := 1;
while (j <= 25) {
  i := 1;
  while (i <= 101) {
    buzz := (1.0 - fuzz) * buzz + fuzz;
    fuzz := 0.0 - fuzz;
    px[(j - 1) * 101 + i] := (buzz - fizz) * 0.1;
    i := i + 1
  };
  j := j + 1
};

rep := 1;
while (rep <= 60639000) {
  i := 1;
  while (i <= 101) {
    px[(1 - 1) * 101 + i] := dm28 * px[(13 - 1) * 101 + i] + dm27 * px[(12 - 1) * 101 + i]
              + dm26 * px[(11 - 1) * 101 + i] + dm25 * px[(10 - 1) * 101 + i]
              + dm24 * px[(9 - 1) * 101 + i]  + dm23 * px[(8 - 1) * 101 + i]
              + dm22 * px[(7 - 1) * 101 + i]  + c0 * (px[(5 - 1) * 101 + i] + px[(6 - 1) * 101 + i])
              + px[(3 - 1) * 101 + i];
    i := i + 1
  };
  rep := rep + 1
};
printFloat(px[(1 - 1) * 101 + 51]); printString("\n")
