var i : int, j : int, k : int, s : int;
s := 0;
i := 0;
while (i < 5) {
  j := 0;
  while (j < 4) {
    k := 0;
    while (k < 3) {
      s := s + i * 100 + j * 10 + k;
      k := k + 1
    };
    j := j + 1
  };
  i := i + 1
};
printString("s="); printInt(s); printString("\n")
