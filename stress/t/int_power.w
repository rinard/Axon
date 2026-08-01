var base : int, ex : int, r : int, i : int;
base := 3;
ex := 40;
r := 1;
i := 0;
while (i < ex) {
  r := r * base;
  i := i + 1
};
printString("p1="); printInt(r); printString("\n");
base := 7;
ex := 25;
r := 1;
i := 0;
while (i < ex) {
  r := r * base;
  i := i + 1
};
printString("p2="); printInt(r); printString("\n")
