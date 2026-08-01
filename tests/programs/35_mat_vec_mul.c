#include <stdio.h>
#include <stdint.h>
int64_t A[1024], X[1024], Y[1024];
int main() {
    int64_t n = 0, i = 0, k = 0, s = 0, r = 0;
    n = 4;
    A[0] = 1;  A[1] = 2;  A[2] = 3;  A[3] = 4;
    A[4] = 5;  A[5] = 6;  A[6] = 7;  A[7] = 8;
    A[8] = 9;  A[9] = 10; A[10] = 11; A[11] = 12;
    A[12] = 13; A[13] = 14; A[14] = 15; A[15] = 16;
    X[0] = 1; X[1] = 2; X[2] = 3; X[3] = 4;
    i = 0;
    while (i < n) {
        s = 0;
        k = 0;
        while (k < n) {
            s = s + A[i * n + k] * X[k];
            k = k + 1;
        }
        Y[i] = s;
        i = i + 1;
    }
    r = Y[0] * 1000000 + Y[1] * 10000 + Y[2] * 100 + Y[3];
    printf("%s = %ld\n", "n", n);
    printf("%s = %ld\n", "i", i);
    printf("%s = %ld\n", "k", k);
    printf("%s = %ld\n", "s", s);
    printf("%s = %ld\n", "r", r);
    return 0;
}
