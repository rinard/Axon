var i : int, sum3 : int, sum5 : int, sumboth : int, cntev : int, x : int;
sum3 := 0;
sum5 := 0;
sumboth := 0;
cntev := 0;
i := 1;
while (i <= 100) {
  x := i;
  if (x % 3 == 0) { sum3 := sum3 + x } else { sum3 := sum3 + 0 };
  if (x % 5 == 0) { sum5 := sum5 + x } else { sum5 := sum5 + 0 };
  if (x % 3 == 0 && x % 5 == 0) { sumboth := sumboth + x } else { sumboth := sumboth + 0 };
  if (x % 2 == 0) { cntev := cntev + 1 } else { cntev := cntev + 0 };
  i := i + 1
};
printString("sum3="); printInt(sum3); printString("\n");
printString("sum5="); printInt(sum5); printString("\n");
printString("sumboth="); printInt(sumboth); printString("\n");
printString("cntev="); printInt(cntev); printString("\n")
