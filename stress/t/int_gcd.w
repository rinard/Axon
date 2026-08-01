var a : int, b : int, t : int, orig_a : int, orig_b : int;
a := 1071;
b := 462;
orig_a := a;
orig_b := b;
while (b != 0) {
  t := a % b;
  a := b;
  b := t
};
printString("gcd="); printInt(a); printString("\n");
a := 123456;
b := 7890;
while (b != 0) {
  t := a % b;
  a := b;
  b := t
};
printString("gcd2="); printInt(a); printString("\n")
