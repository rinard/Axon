#include <stdio.h>
#include <stdint.h>
double A[5];
int main() {
    double s = 0;
    int64_t i = 0;
    A[0] = 1.0;
    A[1] = 2.0;
    A[2] = 3.0;
    A[3] = 4.0;
    A[4] = 5.0;
    s = 0.0;
    i = 0;
    while (i < 5) {
        s = s + A[i];
        i = i + 1;
    }
    printf("%s = %f\n", "s", s);
    printf("%s = %ld\n", "i", i);
    return 0;
}
