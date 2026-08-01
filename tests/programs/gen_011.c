#include <stdio.h>
#include <stdint.h>
int64_t A[32];
int64_t B[32];
int main() {
    int64_t v0 = 0, v1 = 0, v2 = 0, v3 = 0, v4 = 0, v5 = 0;
    int64_t b0 = 0, b1 = 0;
    v3 = 0;
    v1 = 2;
    v5 = 100;
    A[0] = 1;
    A[1] = 42;
    A[2] = 1;
    B[0] = 0;
    B[1] = 2;
    B[2] = 10;
    B[3] = -5;
    while (v0 < 8) {
        while (v3 < 6) {
            if (((v5 != 1) ? 1 : 0)) {
                v2 = v4;
            } else {
                v2 = v5;
            }
            v3 = v3 + 1;
        }
        v0 = v0 + 1;
    }
    while (v0 < 10) {
        v5 = (int64_t)((uint64_t)3 - (uint64_t)10);
        v0 = v0 + 1;
    }
    B[((int64_t)((uint64_t)(v0 % 32) + (uint64_t)32) % 32)] = v0;
    v2 = A[((int64_t)((uint64_t)(v4 % 32) + (uint64_t)32) % 32)];
    if (((10 <= A[9]) ? 1 : 0)) {
        v5 = v2;
    } else {
        if (((((v2 != -5) ? 1 : 0) || ((v0 <= 42) ? 1 : 0)) ? 1 : 0)) {
            while (v4 < 5) {
                v5 = v5;
                v4 = v4 + 1;
            }
        } else {
            B[24] = 42;
        }
    }
    b1 = (!((((v0 == -5) ? 1 : 0) || ((v2 != 0) ? 1 : 0)) ? 1 : 0));
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
