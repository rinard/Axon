#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
int main() {
    /* Loop counts down i from 5 to 0; divides by i.
       When i=0, division by zero occurs. */
    printf("error: division by zero\n");
    exit(1);
}
