var i : int, rep : int, ar : float, br : float, cr : float,
    fuzz : float, buzz : float, fizz : float;
array px[2526] : float, cx[2526] : float;

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
i := 1;
while (i <= 2525) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  px[i] := (buzz - fizz) * 0.1;
  i := i + 1
};

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
i := 1;
while (i <= 2525) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  cx[i] := (buzz - fizz) * 0.1;
  i := i + 1
};

rep := 1;
while (rep <= 48656000) {
  i := 1;
  while (i <= 101) {
    ar := cx[4 * 101 + i];
    br := ar - px[4 * 101 + i];
    px[4 * 101 + i] := ar;
    cr := br - px[5 * 101 + i];
    px[5 * 101 + i] := br;
    ar := cr - px[6 * 101 + i];
    px[6 * 101 + i] := cr;
    br := ar - px[7 * 101 + i];
    px[7 * 101 + i] := ar;
    cr := br - px[8 * 101 + i];
    px[8 * 101 + i] := br;
    ar := cr - px[9 * 101 + i];
    px[9 * 101 + i] := cr;
    br := ar - px[10 * 101 + i];
    px[10 * 101 + i] := ar;
    cr := br - px[11 * 101 + i];
    px[11 * 101 + i] := br;
    px[13 * 101 + i] := cr - px[12 * 101 + i];
    px[12 * 101 + i] := cr;
    i := i + 1
  };
  rep := rep + 1
};
printFloat(px[(5 - 1) * 101 + 51]); printString("\n")
