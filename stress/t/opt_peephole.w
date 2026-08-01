var x : int, a : int, b : int, c : int, d : int, e : int;
x := 41;
a := x + 0;
b := a * 1;
c := b - 0;
d := c * 2;
e := d + d * 0;
e := e + (x & x) - (x | x) + (x ^ 0);
printString("a="); printInt(a); printString("\n");
printString("d="); printInt(d); printString("\n");
printString("e="); printInt(e); printString("\n")
