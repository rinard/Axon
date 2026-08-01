#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
int main() {
    int64_t a = 0, b = 0, c = 0;
    a = 10;
    b = 0;
    /* div by zero — should error */
    printf("error: division by zero\n");
    exit(1);
    return 0;
}
