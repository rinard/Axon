var a : float, b : float, mn : float, mx : float;
a := 3.5;
b := 7.25;
mn := fmin(a, b);
mx := fmax(a, b);
printString("mn= "); printFloat(mn); printString("\n");
printString("mx= "); printFloat(mx); printString("\n");
a := neg(2.0);
b := neg(8.0);
mn := fmin(a, b);
mx := fmax(a, b);
printString("mn= "); printFloat(mn); printString("\n");
printString("mx= "); printFloat(mx); printString("\n")
