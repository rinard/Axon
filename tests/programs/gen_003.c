#include <stdio.h>
#include <stdint.h>
int64_t A[32];
int64_t B[32];
int main() {
    int64_t v0 = 0, v1 = 0, v2 = 0, v3 = 0, v4 = 0, v5 = 0;
    int64_t b0 = 0, b1 = 0;
    v0 = 3;
    v1 = 100;
    v4 = 42;
    A[0] = 10;
    A[1] = 2;
    B[0] = 42;
    B[1] = 3;
    B[2] = 1;
    A[0] = (int64_t)((uint64_t)v3 + (uint64_t)B[((int64_t)((uint64_t)(v1 % 32) + (uint64_t)32) % 32)]);
    b1 = ((v5 != (int64_t)((uint64_t)v5 * (uint64_t)v1)) ? 1 : 0);
    v0 = ((int64_t)((uint64_t)v4 + (uint64_t)100) / 1);
    while (v0 < 3) {
        v0 = (int64_t)((uint64_t)10 + (uint64_t)-1);
        v0 = v0 + 1;
    }
    if (((B[((int64_t)((uint64_t)(v1 % 32) + (uint64_t)32) % 32)] > (int64_t)((uint64_t)v2 - (uint64_t)v5)) ? 1 : 0)) {
        A[6] = 3;
    } else {
        A[((int64_t)((uint64_t)(v0 % 32) + (uint64_t)32) % 32)] = (int64_t)((uint64_t)v1 - (uint64_t)v5);
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
