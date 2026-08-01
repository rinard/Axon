#include <stdio.h>
#include <stdint.h>
double A[10];
int main() {
    double x = 0, y = 0, z = 0;
    A[0] = 1.5;
    A[1] = 2.5;
    A[2] = 4.0;
    x = A[0];
    y = A[1];
    z = A[2];
    printf("%s = %f\n", "x", x);
    printf("%s = %f\n", "y", y);
    printf("%s = %f\n", "z", z);
    return 0;
}
