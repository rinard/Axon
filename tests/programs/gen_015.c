#include <stdio.h>
#include <stdint.h>
int64_t A[32];
int64_t B[32];
int main() {
    int64_t v0 = 0, v1 = 0, v2 = 0, v3 = 0, v4 = 0, v5 = 0;
    int64_t b0 = 0, b1 = 0;
    v4 = 5;
    v2 = -1;
    v0 = 3;
    A[0] = 100;
    A[1] = -1;
    A[2] = -1;
    A[3] = -5;
    B[0] = -1;
    while (v5 < 5) {
        v2 = (int64_t)((uint64_t)7 - (uint64_t)v1);
        v5 = v5 + 1;
    }
    v5 = (int64_t)((uint64_t)100 + (uint64_t)v3);
    A[20] = (int64_t)((uint64_t)(2 / 10) * (uint64_t)42);
    if (((v1 != (int64_t)((uint64_t)7 + (uint64_t)v5)) ? 1 : 0)) {
        B[25] = (int64_t)((uint64_t)v1 + (uint64_t)v1);
    } else {
        v0 = 10;
    }
    v3 = ((1 % 5) / 1);
    printf("%s = %ld\n", "v0", v0);
    printf("%s = %ld\n", "v1", v1);
    printf("%s = %ld\n", "v2", v2);
    printf("%s = %ld\n", "v3", v3);
    printf("%s = %ld\n", "v4", v4);
    printf("%s = %ld\n", "v5", v5);
    printf("%s = %ld\n", "b0", b0);
    printf("%s = %ld\n", "b1", b1);
    return 0;
}
