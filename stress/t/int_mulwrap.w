var a : int, b : int, c : int, e : int;
a := 3037000500;
b := a * a;
c := 9223372036854775807;
c := c * 3;
e := -9223372036854775807;
e := e - 1;
e := e * e;
printString("b="); printInt(b); printString("\n");
printString("c="); printInt(c); printString("\n");
printString("e="); printInt(e); printString("\n")
