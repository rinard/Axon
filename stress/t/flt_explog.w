var x : float, e : float, l : float, l2 : float, l10 : float;
x := 2.5;
e := exp(x);
l := log(x);
printString("e= "); printFloat(e); printString("\n");
printString("l= "); printFloat(l); printString("\n");
x := 8.0;
l2 := log2(x);
printString("l2= "); printFloat(l2); printString("\n");
x := 1000.0;
l10 := log10(x);
printString("l10= "); printFloat(l10); printString("\n")
