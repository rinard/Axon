#include <stdio.h>
#include <stdint.h>
int64_t flags[8];
int main() {
    int64_t i = 0, count = 0;
    flags[0] = 1;
    flags[1] = 0;
    flags[2] = 1;
    flags[3] = 1;
    flags[4] = 0;
    flags[5] = 1;
    flags[6] = 0;
    flags[7] = 1;
    i = 0;
    count = 0;
    while (i < 8) {
        if (flags[i]) { count = (int64_t)((uint64_t)count + (uint64_t)1); } else { count = (int64_t)((uint64_t)count + (uint64_t)0); }
        i = (int64_t)((uint64_t)i + (uint64_t)1);
    }
    printf("%s = %ld\n", "i", i);
    printf("%s = %ld\n", "count", count);
    return 0;
}
