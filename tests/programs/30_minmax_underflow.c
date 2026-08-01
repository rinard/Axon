#include <stdio.h>
#include <stdint.h>
int main() {
    int64_t minval = 0, maxval = 0, s = 0, d = 0;
    minval = (int64_t)(-9223372036854775807LL - 1LL);
    maxval = 9223372036854775807LL;
    s = (int64_t)((uint64_t)minval + (uint64_t)maxval);
    d = (int64_t)((uint64_t)maxval - (uint64_t)minval);
    printf("%s = %ld\n", "minval", minval);
    printf("%s = %ld\n", "maxval", maxval);
    printf("%s = %ld\n", "s", s);
    printf("%s = %ld\n", "d", d);
    return 0;
}
