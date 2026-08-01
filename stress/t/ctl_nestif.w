var x : int, r : int;
x := 37;
if (x < 10) {
  r := 1
} else {
  if (x < 20) {
    r := 2
  } else {
    if (x < 30) {
      r := 3
    } else {
      if (x < 40) {
        r := 4
      } else {
        if (x < 50) {
          r := 5
        } else {
          r := 6
        }
      }
    }
  }
};
printString("r="); printInt(r); printString("\n")
