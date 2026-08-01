var i : int, n : int, target : float, g : float, t : float;
target := 612.0;
g := 25.0;
n := 20;
i := 0;
while (i < n) {
  t := target / g;
  g := 0.5 * (g + t);
  i := i + 1
};
printString("g= "); printFloat(g); printString("\n");
printString("ref= "); printFloat(sqrt(target)); printString("\n")
