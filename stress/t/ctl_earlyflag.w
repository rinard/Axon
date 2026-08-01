var i : int, sum : int, done : bool, val : int, lastidx : int;
sum := 0;
done := false;
lastidx := 0;
i := 0;
while (i < 50) {
  if (done) {
    sum := sum + 0
  } else {
    val := i * i - 30;
    if (val > 100) {
      done := true;
      lastidx := i
    } else {
      sum := sum + val
    }
  };
  i := i + 1
};
printString("sum="); printInt(sum); printString("\n");
printString("lastidx="); printInt(lastidx); printString("\n")
