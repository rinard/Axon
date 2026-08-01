var i : int, n : int, acc : float;
n := 1000;
i := 1;
acc := 0.0;
while (i < n) {
  acc := acc + intToFloat(i) * 0.001;
  i := i + 1
};
printString("acc= "); printFloat(acc); printString("\n")
