#include <stdio.h>
#include <stdint.h>
int64_t A[32];
int64_t B[32];
int main() {
    int64_t v0 = 0, v1 = 0, v2 = 0, v3 = 0, v4 = 0, v5 = 0;
    int64_t b0 = 0, b1 = 0;
    v1 = 3;
    v2 = 3;
    v3 = 2;
    A[0] = 1;
    A[1] = 5;
    B[0] = 100;
    while (v5 < 9) {
        v2 = (int64_t)((uint64_t)v4 * (uint64_t)2);
        v5 = v5 + 1;
    }
    while (v4 < 3) {
        if (b1) {
            if (((v3 <= -1) ? 1 : 0)) {
                v2 = 42;
            } else {
                v2 = v1;
            }
        } else {
            if (((v3 != 5) ? 1 : 0)) {
                v3 = v4;
            } else {
                v1 = 3;
            }
        }
        v4 = v4 + 1;
    }
    while (v0 < 8) {
        while (v5 < 2) {
            if (((v2 < 1) ? 1 : 0)) {
                v1 = 5;
            } else {
                v3 = v1;
            }
            v5 = v5 + 1;
        }
        v0 = v0 + 1;
    }
    while (v0 < 7) {
        v4 = v3;
        v0 = v0 + 1;
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
