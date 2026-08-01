#include <stdio.h>
#include <stdint.h>
int64_t A[1024], B[1024], C[1024];
int main() {
    int64_t i = 0, j = 0, k = 0, s = 0, r = 0;
    A[0] = 1; A[1] = 2;
    A[2] = 3; A[3] = 4;
    B[0] = 5; B[1] = 6;
    B[2] = 7; B[3] = 8;
    i = 0;
    while (i < 2) {
        j = 0;
        while (j < 2) {
            s = 0;
            k = 0;
            while (k < 2) {
                s = s + A[i * 2 + k] * B[k * 2 + j];
                k = k + 1;
            }
            C[i * 2 + j] = s;
            j = j + 1;
        }
        i = i + 1;
    }
    r = C[0] * 1000000 + C[1] * 10000 + C[2] * 100 + C[3];
    printf("%s = %ld\n", "i", i);
    printf("%s = %ld\n", "j", j);
    printf("%s = %ld\n", "k", k);
    printf("%s = %ld\n", "s", s);
    printf("%s = %ld\n", "r", r);
    return 0;
}
