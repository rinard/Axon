#include <stdio.h>
#include <stdint.h>
int64_t A[32];
int64_t B[32];
int main() {
    int64_t v0 = 0, v1 = 0, v2 = 0, v3 = 0, v4 = 0, v5 = 0;
    int64_t b0 = 0, b1 = 0;
    v4 = 42;
    v5 = 3;
    v1 = 5;
    A[0] = 42;
    A[1] = 0;
    A[2] = 10;
    A[3] = 7;
    B[0] = 2;
    B[1] = 42;
    B[2] = 2;
    B[3] = -1;
    B[((int64_t)((uint64_t)(v5 % 32) + (uint64_t)32) % 32)] = -5;
    B[16] = v1;
    B[((int64_t)((uint64_t)(v3 % 32) + (uint64_t)32) % 32)] = v3;
    v0 = A[((int64_t)((uint64_t)(v2 % 32) + (uint64_t)32) % 32)];
    v0 = (int64_t)((uint64_t)0 * (uint64_t)(int64_t)((uint64_t)0 + (uint64_t)v1));
    if ((!((5 >= -1) ? 1 : 0))) {
        while (v1 < 5) {
            v0 = v4;
            v1 = v1 + 1;
        }
    } else {
        b0 = b0;
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
