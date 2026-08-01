#include <stdio.h>
#include <stdint.h>
int64_t flags[64];
int main() {
    int64_t i = 0, count = 0;
    i = 0;
    while (i < 64) {
        if (i / 3 * 3 == i) { flags[i] = 1; } else { flags[i] = 0; }
        i = i + 1;
    }
    i = 0;
    count = 0;
    while (i < 64) {
        if (flags[i]) { count = count + 1; } else { count = count + 0; }
        i = i + 1;
    }
    printf("multiples_of_3=%ld\n", (long)count);
    return 0;
}
