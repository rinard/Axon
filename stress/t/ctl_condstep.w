var i : int, s : int;
s := 0;
i := 0;
while (i < 100) {
  s := s + i;
  if (i % 2 == 0) {
    i := i + 1
  } else {
    i := i + 3
  }
};
printString("s="); printInt(s); printString("\n");
printString("i="); printInt(i); printString("\n")
