var start : int, n : int, steps : int, totsteps : int, maxsteps : int, maxstart : int;
totsteps := 0;
maxsteps := 0;
maxstart := 0;
start := 1;
while (start <= 27) {
  n := start;
  steps := 0;
  while (n != 1 && steps < 1000) {
    if (n % 2 == 0) {
      n := n / 2
    } else {
      n := 3 * n + 1
    };
    steps := steps + 1
  };
  totsteps := totsteps + steps;
  if (steps > maxsteps) {
    maxsteps := steps;
    maxstart := start
  } else {
    maxsteps := maxsteps
  };
  start := start + 1
};
printString("totsteps="); printInt(totsteps); printString("\n");
printString("maxsteps="); printInt(maxsteps); printString("\n");
printString("maxstart="); printInt(maxstart); printString("\n")
