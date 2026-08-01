var a : int, b : int, c : int, r : int, s : int, t : int;
a := 5;
b := 3;
c := 7;
r := (a + b) * (c - a) - b * c + (a * b * c) / 2;
s := ((a - b) * c + (a + c) * b) * (c - b) - a;
t := a + b * c - (a - b) * (c + a) / b + c % a;
printString("r="); printInt(r); printString("\n");
printString("s="); printInt(s); printString("\n");
printString("t="); printInt(t); printString("\n")
