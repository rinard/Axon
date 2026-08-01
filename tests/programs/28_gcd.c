#include <stdio.h>
#include <stdint.h>
int main() {
    int64_t a = 0, b = 0, t = 0;
    a = 252;
    b = 105;
    while (b != 0) {
        t = b;
        b = a % b;
        a = t;
    }
    printf("%s = %ld\n", "a", a);
    printf("%s = %ld\n", "b", b);
    printf("%s = %ld\n", "t", t);
    return 0;
}
