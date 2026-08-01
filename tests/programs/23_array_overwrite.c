#include <stdio.h>
#include <stdint.h>
int64_t A[1024];
int main() {
    int64_t x = 0;
    A[0] = 100;
    A[0] = 200;
    A[0] = 300;
    x = A[0];
    printf("%s = %ld\n", "x", x);
    return 0;
}
