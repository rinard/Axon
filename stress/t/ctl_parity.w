var v : int, t : int, bits : int, par : int, oddpar : int, i : int;
oddpar := 0;
i := 0;
while (i < 64) {
  v := i * 2654435761;
  v := v & 1023;
  t := v;
  bits := 0;
  while (t != 0) {
    if ((t & 1) == 1) {
      bits := bits + 1
    } else {
      bits := bits + 0
    };
    t := t >> 1
  };
  par := bits % 2;
  if (par == 1) {
    oddpar := oddpar + 1
  } else {
    oddpar := oddpar + 0
  };
  i := i + 1
};
printString("oddpar="); printInt(oddpar); printString("\n")
