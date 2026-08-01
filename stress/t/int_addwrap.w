var a : int, b : int, c : int, d : int;
a := 9223372036854775807;
b := a + 1;
c := a + a;
d := -9223372036854775807;
d := d - 2;
printString("b="); printInt(b); printString("\n");
printString("c="); printInt(c); printString("\n");
printString("d="); printInt(d); printString("\n")
