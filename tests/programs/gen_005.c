#include <stdio.h>
#include <stdint.h>
int64_t A[32];
int64_t B[32];
int main() {
    int64_t v0 = 0, v1 = 0, v2 = 0, v3 = 0, v4 = 0, v5 = 0;
    int64_t b0 = 0, b1 = 0;
    v4 = 10;
    v5 = -1;
    v0 = 3;
    A[0] = 0;
    A[1] = 10;
    A[2] = 0;
    B[0] = 7;
    B[1] = 10;
    v5 = (int64_t)((uint64_t)v0 * (uint64_t)(int64_t)((uint64_t)v2 - (uint64_t)v3));
    if ((((int64_t)((uint64_t)v4 * (uint64_t)10) >= v1) ? 1 : 0)) {
        B[28] = (int64_t)((uint64_t)42 * (uint64_t)v0);
    } else {
        B[15] = (int64_t)((uint64_t)3 + (uint64_t)v1);
    }
    if (((((v1 >= 42) ? 1 : 0) && ((v0 >= v1) ? 1 : 0)) ? 1 : 0)) {
        v1 = (int64_t)((uint64_t)v1 + (uint64_t)v4);
    } else {
        while (v3 < 10) {
            while (v5 < 7) {
                v4 = v1;
                v5 = v5 + 1;
            }
            v3 = v3 + 1;
        }
    }
    A[((int64_t)((uint64_t)(v2 % 32) + (uint64_t)32) % 32)] = (int64_t)((uint64_t)A[4] * (uint64_t)(int64_t)((uint64_t)v2 + (uint64_t)100));
    v3 = (int64_t)((uint64_t)v3 * (uint64_t)B[13]);
    while (v3 < 10) {
        while (v0 < 10) {
            b0 = ((v2 == 10) ? 1 : 0);
            v0 = v0 + 1;
        }
        v3 = v3 + 1;
    }
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
