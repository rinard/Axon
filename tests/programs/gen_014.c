#include <stdio.h>
#include <stdint.h>
int64_t A[32];
int64_t B[32];
int main() {
    int64_t v0 = 0, v1 = 0, v2 = 0, v3 = 0, v4 = 0, v5 = 0;
    int64_t b0 = 0, b1 = 0;
    v0 = 0;
    v5 = 7;
    v1 = 3;
    A[0] = 0;
    A[1] = 2;
    A[2] = 5;
    B[0] = 2;
    if ((!((((v3 != 7) ? 1 : 0) && ((v3 < 100) ? 1 : 0)) ? 1 : 0))) {
        v4 = -5;
    } else {
        B[((int64_t)((uint64_t)(v0 % 32) + (uint64_t)32) % 32)] = 42;
    }
    while (v3 < 2) {
        B[5] = v1;
        v3 = v3 + 1;
    }
    v2 = (int64_t)((uint64_t)(v4 % 5) * (uint64_t)(1 % 10));
    if (((((((v3 <= 42) ? 1 : 0) && ((v3 <= 7) ? 1 : 0)) ? 1 : 0) && ((((v3 != 1) ? 1 : 0) || ((v3 == 7) ? 1 : 0)) ? 1 : 0)) ? 1 : 0)) {
        if (((-5 <= 1) ? 1 : 0)) {
            B[((int64_t)((uint64_t)(v4 % 32) + (uint64_t)32) % 32)] = v4;
        } else {
            if (((v2 != -5) ? 1 : 0)) {
                v3 = v2;
            } else {
                v2 = 1;
            }
        }
    } else {
        v3 = v0;
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
