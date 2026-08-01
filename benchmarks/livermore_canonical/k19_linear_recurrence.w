var k : int, i : int, rep : int, stb5 : float, stb5_init : float, kb5i : int,
    fuzz : float, buzz : float, fizz : float;
array b5[102] : float, sa[102] : float, sb[102] : float,
      spacer[40] : float;

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
k := 1;
while (k <= 39) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  spacer[k] := (buzz - fizz) * 0.1;
  k := k + 1
};
stb5_init := spacer[35];

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
k := 1;
while (k <= 101) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  sa[k] := (buzz - fizz) * 0.1;
  k := k + 1
};

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
k := 1;
while (k <= 101) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  sb[k] := (buzz - fizz) * 0.1;
  k := k + 1
};

k := 1;
while (k <= 101) {
  b5[k] := 0.0;
  k := k + 1
};

rep := 1;
while (rep <= 39200000) {
  stb5 := stb5_init;
  kb5i := 0;
  k := 1;
  while (k <= 101) {
    b5[k + kb5i] := sa[k] + stb5 * sb[k];
    stb5 := b5[k + kb5i] - stb5;
    k := k + 1
  };
  i := 1;
  while (i <= 101) {
    k := 101 - i + 1;
    b5[k + kb5i] := sa[k] + stb5 * sb[k];
    stb5 := b5[k + kb5i] - stb5;
    i := i + 1
  };
  rep := rep + 1
};
printFloat(b5[101]); printString("\n")
