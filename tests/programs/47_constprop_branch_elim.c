#include <stdio.h>
#include <stdint.h>
int main() {
    int64_t x = 0, y = 0;
    x = 5;
    if (x == 5) { y = 1; } else { y = 2; }
    printf("%s = %ld\n", "x", x);
    printf("%s = %ld\n", "y", y);
    return 0;
}
