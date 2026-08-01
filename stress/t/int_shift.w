var a : int, b : int, c : int, d : int, e : int, f : int, g : int;
a := 1 << 10;
b := 1 << 62;
c := -1 << 4;
d := -1024 >> 3;
e := 1024 >> 3;
f := -9223372036854775807;
f := f - 1;
f := f >> 60;
g := 255 >> 0;
printString("a="); printInt(a); printString("\n");
printString("b="); printInt(b); printString("\n");
printString("c="); printInt(c); printString("\n");
printString("d="); printInt(d); printString("\n");
printString("e="); printInt(e); printString("\n");
printString("f="); printInt(f); printString("\n");
printString("g="); printInt(g); printString("\n")
