#include <stdio.h>
#include <stdint.h>
int64_t A[32];
int64_t B[32];
int main() {
    int64_t v0 = 0, v1 = 0, v2 = 0, v3 = 0, v4 = 0, v5 = 0;
    int64_t b0 = 0, b1 = 0;
    v0 = 10;
    v2 = 3;
    v1 = 5;
    A[0] = 42;
    A[1] = 100;
    A[2] = 100;
    B[0] = 10;
    B[1] = 100;
    B[2] = 7;
    b1 = ((v5 == 1) ? 1 : 0);
    if (((((((v1 <= 42) ? 1 : 0) && ((v5 == -1) ? 1 : 0)) ? 1 : 0) || ((((v0 == 3) ? 1 : 0) || ((v1 == 7) ? 1 : 0)) ? 1 : 0)) ? 1 : 0)) {
        v0 = (int64_t)((uint64_t)5 + (uint64_t)100);
    } else {
        if (((((v0 < -1) ? 1 : 0) && ((v3 == 42) ? 1 : 0)) ? 1 : 0)) {
            A[((int64_t)((uint64_t)(v2 % 32) + (uint64_t)32) % 32)] = 42;
        } else {
            A[((int64_t)((uint64_t)(v5 % 32) + (uint64_t)32) % 32)] = 0;
        }
    }
    while (v2 < 2) {
        while (v0 < 9) {
            while (v3 < 9) {
                v3 = v3;
                v3 = v3 + 1;
            }
            v0 = v0 + 1;
        }
        v2 = v2 + 1;
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
