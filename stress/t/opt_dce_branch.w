var x : int, r : int, dead : int, k : int;
x := 42;
r := 0;
dead := 0;
if (1 == 1) {
  r := r + 100
} else {
  dead := dead + 999;
  r := r - 50
};
if (0 == 1) {
  dead := dead + 7;
  r := r * 3
} else {
  r := r + 5
};
k := 2 + 2;
if (k == 5) {
  r := r + 1000
} else {
  r := r + 1
};
printString("r="); printInt(r); printString("\n");
printString("dead="); printInt(dead); printString("\n")
