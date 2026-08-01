#include <stdio.h>
#include <stdint.h>
int main() {
    int64_t x = 0, y = 0, r = 0;
    x = 10;
    y = 20;
    x = 5;
    r = x + y;
    printf("%s = %ld\n", "x", x);
    printf("%s = %ld\n", "y", y);
    printf("%s = %ld\n", "r", r);
    return 0;
}
