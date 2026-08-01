#include <stdio.h>
#include <stdint.h>
int main() {
    int64_t x = 0, y = 0;
    x = 9223372036854775807LL;
    y = (int64_t)((uint64_t)x + 1ULL);
    printf("%s = %ld\n", "x", x);
    printf("%s = %ld\n", "y", y);
    return 0;
}
