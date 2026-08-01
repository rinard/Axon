var rep : int, i : int, m : int, i1 : int, k : int, k2 : int, k3 : int,
    j2 : int, j4 : int, j5 : int, ii : int, lb : int, n : int,
    zval : int,
    r : float, s : float, t : float, tmp : float,
    fuzz : float, buzz : float, fizz : float,
    kbreak : int, kcont : int, restart : int;
array d[301] : float, plan[301] : float, zone[301] : int;

n := 75;
ii := n / 3;
lb := ii + ii;
r := 0.05;
s := 0.05;
t := 0.05;

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
i := 1;
while (i <= 300) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  d[i] := (buzz - fizz) * 0.1;
  plan[i] := (buzz - fizz) * 0.1;
  i := i + 1
};

i := 1;
while (i <= 300) {
  zone[i] := (i - 1) % (n + 1);
  i := i + 1
};
zone[1] := 5;

rep := 1;
while (rep <= 162000000) {
  i1 := 1;
  m := 1;
  k2 := 0;
  k3 := 0;
  kbreak := 0;
  restart := 1;
  while (restart == 1) {
    restart := 0;
    kbreak := 0;
    j2 := (n + n) * (m - 1) + 1;
    k := 1;
    while (k <= n && kbreak == 0) {
      kcont := 0;
      k2 := k2 + 1;
      j4 := j2 + k + k;
      j5 := zone[j4 - 1];
      if (j5 < n) {
        if (j5 + lb < n) {
          tmp := plan[j5] - t
        } else {
          if (j5 + ii < n) {
            tmp := plan[j5] - s
          } else {
            tmp := plan[j5] - r
          }
        }
      } else {
        if (j5 == n) {
          kbreak := 1
        } else {
          k3 := k3 + 1;
          tmp := d[j5 - 1] - (d[j5 - 2] * (t - d[j5 - 3]) * (t - d[j5 - 3])
                 + (s - d[j5 - 4]) * (s - d[j5 - 4])
                 + (r - d[j5 - 5]) * (r - d[j5 - 5]))
        }
      };
      if (kbreak == 0) {
        if (tmp < 0.0) {
          zval := zone[j4 - 2];
          if (zval < 0) {
            kcont := 1
          } else {
            if (zval == 0) {
              kbreak := 1
            } else {
              skip
            }
          }
        } else {
          if (tmp > 0.0) {
            zval := zone[j4 - 2];
            if (zval > 0) {
              kcont := 1
            } else {
              if (zval == 0) {
                kbreak := 1
              } else {
                skip
              }
            }
          } else {
            kbreak := 1
          }
        }
      } else { skip };
      if (kbreak == 0 && kcont == 0) {
        m := m + 1;
        if (m > zone[1]) { m := 1 } else { skip };
        if (i1 != m) {
          restart := 1;
          kbreak := 1
        } else {
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
