#include <stdio.h>
#include <stdint.h>
int main() {
    int64_t x = 0, y = 0, z = 0;
    x = 1;
    y = 2;
    if (x == 1) {
        z = 100;
    } else {
        z = 200;
        y = 999;
    }
    printf("%s = %ld\n", "x", x);
    printf("%s = %ld\n", "y", y);
    printf("%s = %ld\n", "z", z);
    return 0;
}
