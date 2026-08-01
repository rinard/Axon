#include <stdio.h>
#include <stdint.h>
int64_t A[1024], B[1024], C[1024];
int main() {
    int64_t n = 0, i = 0, j = 0, k = 0, s = 0, r = 0;
    n = 3;
    A[0] = 1; A[1] = 2; A[2] = 3;
    A[3] = 4; A[4] = 5; A[5] = 6;
    A[6] = 7; A[7] = 8; A[8] = 9;
    B[0] = 9; B[1] = 8; B[2] = 7;
    B[3] = 6; B[4] = 5; B[5] = 4;
    B[6] = 3; B[7] = 2; B[8] = 1;
    i = 0;
    while (i < n) {
        j = 0;
        while (j < n) {
            s = 0;
            k = 0;
            while (k < n) {
                s = s + A[i * n + k] * B[k * n + j];
                k = k + 1;
            }
            C[i * n + j] = s;
            j = j + 1;
        }
        i = i + 1;
    }
    r = C[0] * 100 + C[1] * 10 + C[2];
    printf("%s = %ld\n", "n", n);
    printf("%s = %ld\n", "i", i);
    printf("%s = %ld\n", "j", j);
    printf("%s = %ld\n", "k", k);
    printf("%s = %ld\n", "s", s);
    printf("%s = %ld\n", "r", r);
    return 0;
}
