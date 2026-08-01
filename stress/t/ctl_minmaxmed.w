var a : int, b : int, c : int, mn : int, mx : int, med : int, sum : int;
a := 17;
b := 4;
c := 9;
if (a < b) { mn := a } else { mn := b };
if (c < mn) { mn := c } else { mn := mn };
if (a > b) { mx := a } else { mx := b };
if (c > mx) { mx := c } else { mx := mx };
sum := a + b + c;
med := sum - mn - mx;
printString("mn="); printInt(mn); printString("\n");
printString("mx="); printInt(mx); printString("\n");
printString("med="); printInt(med); printString("\n")
