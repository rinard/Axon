#include <stdio.h>
#include <stdint.h>
int64_t A[1024], B[1024];
int main() {
    int64_t n = 0, i = 0, j = 0, t = 0, r = 0;
    n = 3;
    A[0] = 1; A[1] = 2; A[2] = 3;
    A[3] = 4; A[4] = 5; A[5] = 6;
    A[6] = 7; A[7] = 8; A[8] = 9;
    i = 0;
    while (i < n) {
        j = 0;
        while (j < n) {
            B[j * n + i] = A[i * n + j];
            j = j + 1;
        }
        i = i + 1;
    }
    r = B[0] * 100000000 + B[1] * 10000000 + B[2] * 1000000 +
        B[3] * 100000 + B[4] * 10000 + B[5] * 1000 +
        B[6] * 100 + B[7] * 10 + B[8];
    printf("%s = %ld\n", "n", n);
    printf("%s = %ld\n", "i", i);
    printf("%s = %ld\n", "j", j);
    printf("%s = %ld\n", "t", t);
    printf("%s = %ld\n", "r", r);
    return 0;
}
