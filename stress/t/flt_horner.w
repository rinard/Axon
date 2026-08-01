var i : int, n : int, x : float, acc : float, c : float;
array coef[8] : float;
coef[0] := 1.0;
coef[1] := neg(3.0);
coef[2] := 2.0;
coef[3] := 0.5;
coef[4] := neg(1.25);
n := 5;
x := 1.7;
acc := 0.0;
i := n - 1;
while (i >= 0) {
  c := coef[i];
  acc := acc * x + c;
  i := i - 1
};
printString("p= "); printFloat(acc); printString("\n")
