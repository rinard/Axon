#include <stdio.h>
#include <stdint.h>
int64_t A[1024];
int main() {
    int64_t n = 0, i = 0, j = 0, t = 0, r = 0;
    n = 5;
    A[0] = 5;
    A[1] = 3;
    A[2] = 1;
    A[3] = 4;
    A[4] = 2;
    i = 0;
    while (i < n - 1) {
        j = 0;
        while (j < n - 1 - i) {
            if (A[j] > A[j + 1]) {
                t = A[j];
                A[j] = A[j + 1];
                A[j + 1] = t;
            }
            j = j + 1;
        }
        i = i + 1;
    }
    r = A[0] * 10000 + A[1] * 1000 + A[2] * 100 + A[3] * 10 + A[4];
    printf("%s = %ld\n", "n", n);
    printf("%s = %ld\n", "i", i);
    printf("%s = %ld\n", "j", j);
    printf("%s = %ld\n", "t", t);
    printf("%s = %ld\n", "r", r);
    return 0;
}
