#include <stdio.h>
#include <stdint.h>
int64_t A[32];
int64_t B[32];
int main() {
    int64_t v0 = 0, v1 = 0, v2 = 0, v3 = 0, v4 = 0, v5 = 0;
    int64_t b0 = 0, b1 = 0;
    v5 = -5;
    v4 = 1;
    v2 = 2;
    A[0] = 1;
    A[1] = 1;
    A[2] = 100;
    B[0] = 5;
    B[1] = 5;
    if (((((v4 >= 5) ? 1 : 0) && (!((v0 == 0) ? 1 : 0))) ? 1 : 0)) {
        b0 = (!((v1 == 42) ? 1 : 0));
    } else {
        if (((1 < v0) ? 1 : 0)) {
            if (((v3 <= 2) ? 1 : 0)) {
                v0 = 5;
            } else {
                v2 = 3;
            }
        } else {
            if (((v4 == 10) ? 1 : 0)) {
                v4 = 2;
            } else {
                v1 = 10;
            }
        }
    }
    if ((((int64_t)((uint64_t)3 * (uint64_t)1) != (int64_t)((uint64_t)v3 + (uint64_t)5)) ? 1 : 0)) {
        v1 = v2;
    } else {
        while (v2 < 6) {
            if (((v5 != 100) ? 1 : 0)) {
                v2 = v0;
            } else {
                v1 = -1;
            }
            v2 = v2 + 1;
        }
    }
    v3 = v2;
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
