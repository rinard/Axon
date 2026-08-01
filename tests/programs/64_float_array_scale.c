#include <stdio.h>
#include <stdint.h>
double A[4];
int main() {
    double factor = 0;
    int64_t i = 0;
    A[0] = 1.0;
    A[1] = 2.0;
    A[2] = 3.0;
    A[3] = 4.0;
    factor = 2.5;
    i = 0;
    while (i < 4) {
        A[i] = A[i] * factor;
        i = i + 1;
    }
    factor = A[0] + A[1] + A[2] + A[3];
    printf("%s = %f\n", "factor", factor);
    printf("%s = %ld\n", "i", i);
    return 0;
}
