var i : int, j : int, x : float, y : float;
i := 5;
j := 2;
x := intToFloat(i / j);
printString("x= "); printFloat(x); printString("\n");
y := intToFloat(i) + 0.5;
printString("y= "); printFloat(y); printString("\n");
y := 3.0 * intToFloat(i) - intToFloat(j);
printString("y= "); printFloat(y); printString("\n");
x := 1.0 / intToFloat(i);
printString("x= "); printFloat(x); printString("\n");
y := intToFloat(i * j) + 0.25 * intToFloat(i);
printString("y= "); printFloat(y); printString("\n")
