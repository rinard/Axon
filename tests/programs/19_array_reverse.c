#include <stdio.h>
#include <stdint.h>
int64_t A[1024];
int main() {
    int64_t n = 0, i = 0, j = 0, t = 0;
    n = 5;
    A[0] = 1;
    A[1] = 2;
    A[2] = 3;
    A[3] = 4;
    A[4] = 5;
    i = 0;
    j = n - 1;
    while (i < j) {
        t = A[i];
        A[i] = A[j];
        A[j] = t;
        i = i + 1;
        j = j - 1;
    }
    t = A[0] * 10000 + A[1] * 1000 + A[2] * 100 + A[3] * 10 + A[4];
    printf("%s = %ld\n", "n", n);
    printf("%s = %ld\n", "i", i);
    printf("%s = %ld\n", "j", j);
    printf("%s = %ld\n", "t", t);
    return 0;
}
