#include <stdio.h>
#include <stdint.h>
int main() {
    int64_t a = 0, b = 0, m = 0;
    a = 7;
    b = 13;
    if (a < b) { m = b; } else { m = a; }
    printf("%s = %ld\n", "a", a);
    printf("%s = %ld\n", "b", b);
    printf("%s = %ld\n", "m", m);
    return 0;
}
