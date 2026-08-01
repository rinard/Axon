#include <stdio.h>
#include <stdint.h>
int64_t A[1024];
int main() {
    int64_t x = 0, y = 0, z = 0;
    A[0] = 10;
    A[1] = 20;
    A[2] = 30;
    x = A[0];
    y = A[1];
    z = A[2];
    printf("%s = %ld\n", "x", x);
    printf("%s = %ld\n", "y", y);
    printf("%s = %ld\n", "z", z);
    return 0;
}
