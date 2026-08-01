var a : int, b : int, c : int, i : int, j : int, s : int, inv : int, t : int;
a := 3;
b := 5;
c := 11;
s := 0;
i := 0;
while (i < 50) {
  inv := a * b - c;
  j := 0;
  while (j < 20) {
    t := inv * 2 + a * c;
    s := s + t + i - j;
    j := j + 1
  };
  i := i + 1
};
printString("s="); printInt(s); printString("\n")
