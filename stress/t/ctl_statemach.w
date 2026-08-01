var state : int, i : int, sym : int, accepts : int, steps : int;
state := 0;
accepts := 0;
steps := 0;
i := 0;
while (i < 40) {
  sym := (i * 3 + 1) % 3;
  if (state == 0) {
    if (sym == 0) { state := 1 } else { state := 0 }
  } else {
    if (state == 1) {
      if (sym == 1) { state := 2 } else { state := 0 }
    } else {
      if (state == 2) {
        if (sym == 2) { state := 0; accepts := accepts + 1 } else { state := 1 }
      } else {
        state := 0
      }
    }
  };
  steps := steps + 1;
  i := i + 1
};
printString("accepts="); printInt(accepts); printString("\n");
printString("state="); printInt(state); printString("\n")
