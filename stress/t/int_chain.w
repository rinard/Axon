var a : int, b : int, c : int, d : int, e : int, r : int;
a := 1234567;
b := -7654321;
c := 9999;
d := -333;
e := 2718281;
r := a * b + c * d - e * a + b * c - d * e + a * c - b * d;
printString("r1="); printInt(r); printString("\n");
r := a - b - c - d - e;
printString("r2="); printInt(r); printString("\n");
r := a + b * c - d + e * a - b + c * d - e + a;
printString("r3="); printInt(r); printString("\n");
r := (((a + b) * c + d) * e - a) % 1000000007;
printString("r4="); printInt(r); printString("\n")
