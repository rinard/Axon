#include <stdio.h>
#include <stdint.h>
int64_t A[1024], X[1024], Y[1024];
int main() {
    int64_t n = 0, i = 0, k = 0, s = 0, checksum = 0;
    n = 32;
    i = 0;
    while (i < n) {
        X[i] = i + 1;
        k = 0;
        while (k < n) {
            A[i * n + k] = (i + k) % 10 + 1;
            k = k + 1;
        }
        i = i + 1;
    }
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
    checksum = 0;
    i = 0;
    while (i < n) {
        checksum = checksum + Y[i];
        i = i + 1;
    }
    printf("%s = %ld\n", "n", n);
    printf("%s = %ld\n", "i", i);
    printf("%s = %ld\n", "k", k);
    printf("%s = %ld\n", "s", s);
    printf("%s = %ld\n", "checksum", checksum);
    return 0;
}
