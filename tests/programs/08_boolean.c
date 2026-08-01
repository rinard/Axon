#include <stdio.h>
#include <stdint.h>
int main() {
    int64_t x = 0, a = 0, b = 0, c = 0, d = 0;
    x = 5;
    a = (x < 10) ? 1 : 0;
    b = (x == 5) ? 1 : 0;
    c = (x < 3 || x > 4) ? 1 : 0;
    d = (a && b) ? 1 : 0;
    printf("%s = %ld\n", "x", x);
    printf("%s = %ld\n", "a", a);
    printf("%s = %ld\n", "b", b);
    printf("%s = %ld\n", "c", c);
    printf("%s = %ld\n", "d", d);
    return 0;
}
