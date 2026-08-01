#include <stdio.h>
#include <stdint.h>
int64_t A[32];
int64_t B[32];
int main() {
    int64_t v0 = 0, v1 = 0, v2 = 0, v3 = 0, v4 = 0, v5 = 0;
    int64_t b0 = 0, b1 = 0;
    v2 = -1;
    v4 = 1;
    v0 = 3;
    A[0] = 5;
    A[1] = -5;
    B[0] = 2;
    v4 = 0;
    B[14] = v2;
    if (((v2 >= (int64_t)((uint64_t)-1 * (uint64_t)10)) ? 1 : 0)) {
        if (((((v0 <= 0) ? 1 : 0) || ((v2 <= -1) ? 1 : 0)) ? 1 : 0)) {
            if (((v3 == 1) ? 1 : 0)) {
                v3 = v5;
            } else {
                v2 = v4;
            }
        } else {
            A[((int64_t)((uint64_t)(v5 % 32) + (uint64_t)32) % 32)] = v4;
        }
    } else {
        v1 = (int64_t)((uint64_t)v0 * (uint64_t)-1);
    }
    B[((int64_t)((uint64_t)(v1 % 32) + (uint64_t)32) % 32)] = (int64_t)((uint64_t)(int64_t)((uint64_t)v3 - (uint64_t)v2) - (uint64_t)(int64_t)((uint64_t)v3 + (uint64_t)v5));
    while (v4 < 1) {
        B[7] = (int64_t)((uint64_t)v0 - (uint64_t)10);
        v4 = v4 + 1;
    }
    B[((int64_t)((uint64_t)(v0 % 32) + (uint64_t)32) % 32)] = v4;
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
