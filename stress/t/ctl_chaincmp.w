var x : int, inrange : int, outside : int, i : int, cnt : int;
cnt := 0;
i := 0;
while (i < 30) {
  x := i - 10;
  if (x >= 0 && x <= 9) {
    inrange := 1
  } else {
    inrange := 0
  };
  if (x < -5 || x > 15) {
    outside := 1
  } else {
    outside := 0
  };
  if (inrange == 1 && outside == 0) {
    cnt := cnt + 1
  } else {
    cnt := cnt + 0
  };
  i := i + 1
};
printString("cnt="); printInt(cnt); printString("\n")
