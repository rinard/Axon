var x : float, y : float, z : float, p : float, q : float, r : float;
x := 2.5;
y := 4.0;
z := 1.5;
p := (x + y) * z;
q := (x + y) * z + x;
r := (x + y) * z * z;
printString("p="); printFloat(p); printString("\n");
printString("q="); printFloat(q); printString("\n");
printString("r="); printFloat(r); printString("\n")
