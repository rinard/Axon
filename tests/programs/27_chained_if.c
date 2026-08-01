#include <stdio.h>
#include <stdint.h>
int main() {
    int64_t x = 0, r = 0;
    x = 42;
    if (x < 10) {
        r = 1;
    } else {
        if (x < 50) {
            r = 2;
        } else {
            r = 3;
        }
    }
    printf("%s = %ld\n", "x", x);
    printf("%s = %ld\n", "r", r);
    return 0;
}
