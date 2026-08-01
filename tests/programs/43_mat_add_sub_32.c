#include <stdio.h>
#include <stdint.h>
int64_t A[1024], B[1024], C[1024];
int main() {
    int64_t n = 0, i = 0, j = 0, idx = 0, checksum = 0;
    n = 32;
    i = 0;
    while (i < n) {
        j = 0;
        while (j < n) {
            idx = i * n + j;
            A[idx] = i * 5 + j * 3 + 1;
            B[idx] = i * 2 + j * 7 + 4;
            j = j + 1;
        }
        i = i + 1;
    }
    i = 0;
    while (i < n) {
        j = 0;
        while (j < n) {
            idx = i * n + j;
            C[idx] = A[idx] + B[idx];
            j = j + 1;
        }
        i = i + 1;
    }
    i = 0;
    while (i < n) {
        j = 0;
        while (j < n) {
            idx = i * n + j;
            C[idx] = C[idx] - A[idx];
            j = j + 1;
        }
        i = i + 1;
    }
    checksum = 0;
    i = 0;
    while (i < n) {
        j = 0;
        while (j < n) {
            checksum = checksum + C[i * n + j];
            j = j + 1;
        }
        i = i + 1;
    }
    printf("%s = %ld\n", "n", n);
    printf("%s = %ld\n", "i", i);
    printf("%s = %ld\n", "j", j);
    printf("%s = %ld\n", "idx", idx);
    printf("%s = %ld\n", "checksum", checksum);
    return 0;
}
