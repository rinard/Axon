var n : int, d : int, isprime : bool, primes : int, found : bool, firstdiv : int;
primes := 0;
firstdiv := 0;
n := 2;
while (n <= 60) {
  isprime := true;
  found := false;
  d := 2;
  while (d < n) {
    if (found) {
      d := n
    } else {
      if (n % d == 0) {
        isprime := false;
        found := true;
        firstdiv := firstdiv + d
      } else {
        d := d + 1
      }
    }
  };
  if (isprime) { primes := primes + 1 } else { primes := primes + 0 };
  n := n + 1
};
printString("primes="); printInt(primes); printString("\n");
printString("firstdiv="); printInt(firstdiv); printString("\n")
