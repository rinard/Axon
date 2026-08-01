var a : float, b : float, i : int, s : float, t : float;
a := 3.0;
b := 1.5;
s := 0.0;
i := 0;
while (i < 100) {
  t := a * b + sqrt(a);
  s := s + t;
  i := i + 1
};
printString("s="); printFloat(s); printString("\n");
printString("t="); printFloat(t); printString("\n")
