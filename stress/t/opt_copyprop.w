var a : int, b : int, c : int, d : int, e : int, r : int;
a := 99;
b := a;
c := b;
d := c;
e := d + a;
r := a + b + c + d + e;
printString("r="); printInt(r); printString("\n");
printString("e="); printInt(e); printString("\n")
