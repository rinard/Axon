var a : int, b : int, c : int, d : int, e : int, f : int;
a := 5;
b := a + 3;
c := b * 2;
d := c - a;
e := (a + b + c + d) * 2;
f := e % 7 + (c << 1) - (d >> 1);
printString("a="); printInt(a); printString("\n");
printString("e="); printInt(e); printString("\n");
printString("f="); printInt(f); printString("\n")
