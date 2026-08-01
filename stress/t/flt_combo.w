var x : float, y : float, d : float, a : float, b : float, r : float;
x := 3.0;
y := 4.0;
d := sqrt(x * x + y * y);
printString("d= "); printFloat(d); printString("\n");
a := exp(log(7.5));
printString("a= "); printFloat(a); printString("\n");
b := pow(2.0, 0.5) * pow(2.0, 0.5);
printString("b= "); printFloat(b); printString("\n");
r := fmax(sin(1.0), cos(1.0));
printString("r= "); printFloat(r); printString("\n");
r := abs(neg(sqrt(2.0)));
printString("r= "); printFloat(r); printString("\n")
