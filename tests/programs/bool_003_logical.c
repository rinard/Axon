#include <stdio.h>
#include <stdint.h>
int64_t a[4], b[4];
int main() {
    int64_t i = 0;
    a[0] = 1; b[0] = 1;
    a[1] = 1; b[1] = 0;
    a[2] = 0; b[2] = 1;
    a[3] = 0; b[3] = 0;
    i = 0;
    while (i < 4) {
        printf("and=%s or=%s\n",
               (a[i] && b[i]) ? "true" : "false",
               (a[i] || b[i]) ? "true" : "false");
        i = i + 1;
    }
    return 0;
}
