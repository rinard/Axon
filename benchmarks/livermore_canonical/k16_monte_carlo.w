var rep : int, k : int, i : int, n : int, ii : int, lb : int,
    m : int, i1 : int, j2 : int, j4 : int, j5 : int,
    k2 : int, k3 : int, zval : int,
    state : int, kbreak : int, kcont : int, restart : int,
    do455 : int,
    r : float, s : float, t : float, tmp : float, dexpr : float,
    fuzz : float, buzz : float, fizz : float;
array d[301] : float, plan[301] : float, zone[301] : int,
      spacer[40] : float;

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
k := 1;
while (k <= 39) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  spacer[k] := (buzz - fizz) * 0.1;
  k := k + 1
};
r := spacer[30];
s := spacer[32];
t := spacer[36];

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
i := 1;
while (i <= 300) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  plan[i] := (buzz - fizz) * 0.1;
  i := i + 1
};

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
i := 1;
while (i <= 300) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  d[i] := (buzz - fizz) * 0.1;
  i := i + 1
};

n := 75;
ii := n / 3;
lb := ii + ii;
i := 1;
while (i <= 300) {
  zone[i] := (i - 1) % (n + 1);
  i := i + 1
};
zone[1] := 5;

rep := 1;
while (rep <= 400000000) {
  m := 1;
  i1 := m;
  k2 := 0;
  k3 := 0;
  restart := 1;
  while (restart == 1) {
    restart := 0;
    j2 := (n + n) * (m - 1) + 1;
    k := 1;
    kbreak := 0;
    while (k <= n && kbreak == 0) {
      kcont := 0;
      do455 := 0;
      k2 := k2 + 1;
      j4 := j2 + k + k;
      j5 := zone[j4];
      if (j5 == n) {
        kbreak := 1
      } else {
        if (j5 < n) {
          if (j5 < n - lb) {
            tmp := plan[j5] - t
          } else {
            if (j5 < n - ii) {
              tmp := plan[j5] - s
            } else {
              tmp := plan[j5] - r
            }
          };
          if (tmp < 0.0) {
            zval := zone[j4 - 1];
            if (zval < 0) {
              kcont := 1
            } else {
              if (zval == 0) {
                kbreak := 1
              } else {
                do455 := 1
              }
            }
          } else {
            if (tmp > 0.0) {
              zval := zone[j4 - 1];
              if (zval < 0) {
                do455 := 1
              } else {
                if (zval == 0) {
                  kbreak := 1
                } else {
                  kcont := 1
                }
              }
            } else {
              kbreak := 1
            }
          }
        } else {
          k3 := k3 + 1;
          dexpr := d[j5] - (d[j5 - 1] * (t - d[j5 - 2]) * (t - d[j5 - 2])
                            + (s - d[j5 - 3]) * (s - d[j5 - 3])
                            + (r - d[j5 - 4]) * (r - d[j5 - 4]));
          if (dexpr < 0.0) {
            zval := zone[j4 - 1];
            if (zval < 0) {
              kcont := 1
            } else {
              if (zval == 0) {
                kbreak := 1
              } else {
                do455 := 1
              }
            }
          } else {
            if (dexpr > 0.0) {
              zval := zone[j4 - 1];
              if (zval < 0) {
                do455 := 1
              } else {
                if (zval == 0) {
                  kbreak := 1
                } else {
                  kcont := 1
                }
              }
            } else {
              kbreak := 1
            }
          }
        }
      };
      if (do455 == 1) {
        m := m + 1;
        if (m > zone[1]) { m := 1 } else { skip };
        if (i1 == m) {
          kbreak := 1
        } else {
          restart := 1;
          kbreak := 1
        }
      } else { skip };
      k := k + 1
    }
  };
  rep := rep + 1
};
printInt(k2); printString("\n");
printInt(k3); printString("\n")
