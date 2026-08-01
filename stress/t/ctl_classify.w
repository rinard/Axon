var x : int, i : int, negc : int, zero : int, pos : int, big : int;
negc := 0;
zero := 0;
pos := 0;
big := 0;
i := 0;
while (i < 20) {
  x := (i * 7) % 11 - 5;
  if (x < 0) {
    negc := negc + 1
  } else {
    if (x == 0) {
      zero := zero + 1
    } else {
      if (x > 3) {
        big := big + 1
      } else {
        pos := pos + 1
      }
    }
  };
  i := i + 1
};
printString("negc="); printInt(negc); printString("\n");
printString("zero="); printInt(zero); printString("\n");
printString("pos="); printInt(pos); printString("\n");
printString("big="); printInt(big); printString("\n")
