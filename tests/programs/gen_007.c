#include <stdio.h>
#include <stdint.h>
int64_t A[32];
int64_t B[32];
int main() {
    int64_t v0 = 0, v1 = 0, v2 = 0, v3 = 0, v4 = 0, v5 = 0;
    int64_t b0 = 0, b1 = 0;
    v5 = -1;
    v2 = 0;
    v0 = 7;
    A[0] = -5;
    A[1] = 7;
    A[2] = 1;
    A[3] = 100;
    B[0] = 0;
    B[1] = 10;
    B[2] = 42;
    v2 = (int64_t)((uint64_t)(int64_t)((uint64_t)v5 - (uint64_t)v4) - (uint64_t)B[15]);
    while (v0 < 5) {
        while (v2 < 8) {
            if (((v2 != 0) ? 1 : 0)) {
                v3 = v1;
            } else {
                v1 = v2;
            }
            v2 = v2 + 1;
        }
        v0 = v0 + 1;
    }
    v4 = (int64_t)((uint64_t)(v1 / 5) - (uint64_t)(v5 / 5));
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
