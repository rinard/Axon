var i : int, j : int, k : int, rep : int,
    ar : float, br : float, cr : float,
    fuzz : float, buzz : float, fizz : float;
array px[2526] : float, cx[2526] : float;

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

rep := 1;
while (rep <= 52000000) {
  k := 1;
  while (k <= 101) {
    ar             := cx[(k - 1) * 25 + 5];
    br             := ar - px[(k - 1) * 25 + 5];
    px[(k - 1) * 25 + 5]  := ar;
    cr             := br - px[(k - 1) * 25 + 6];
    px[(k - 1) * 25 + 6]  := br;
    ar             := cr - px[(k - 1) * 25 + 7];
    px[(k - 1) * 25 + 7]  := cr;
    br             := ar - px[(k - 1) * 25 + 8];
    px[(k - 1) * 25 + 8]  := ar;
    cr             := br - px[(k - 1) * 25 + 9];
    px[(k - 1) * 25 + 9]  := br;
    ar             := cr - px[(k - 1) * 25 + 10];
    px[(k - 1) * 25 + 10] := cr;
    br             := ar - px[(k - 1) * 25 + 11];
    px[(k - 1) * 25 + 11] := ar;
    cr             := br - px[(k - 1) * 25 + 12];
    px[(k - 1) * 25 + 12] := br;
    px[(k - 1) * 25 + 14] := cr - px[(k - 1) * 25 + 13];
    px[(k - 1) * 25 + 13] := cr;
    k := k + 1
  };
  rep := rep + 1
};
printFloat(px[(1 - 1) * 25 + 14]); printString("\n")
