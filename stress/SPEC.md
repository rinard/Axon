<!-- Copyright (c) 2026 Martin Rinard -->
# Stress-test authoring spec

Goal: differential-test the verified Credible Compilation compiler. For each test
basename `T`, write three files into `stress/t/`:
- `T.w`  — While source (the Unit Under Test)
- `T.c`  — C reference
- `T.f`  — Fortran reference

**Protocol — C and Fortran are the SPEC; While is under test.**
- C and Fortran must agree with each other. If they don't, your reference is wrong — fix it.
- If C==F but While disagrees → that is a **candidate compiler bug**. Report it; do NOT
  edit C/F to match While.

## While language reference

Declarations (scalars first, then optional arrays):
```
var x : int, y : float, b : bool;
array A[100] : int, F[100] : float, B[100] : bool;
```
Statements separated by `;` (no trailing `;` before `}` or EOF). Statements:
- `x := expr`  /  `b := boolexpr`  /  `A[idx] := expr`  /  `B[idx] := boolexpr`
- `if (cond) { S } else { S }`   (else is REQUIRED; use `skip` for empty)
- `while (cond) { S }`
- `skip`
- Prints: `printInt(e)`, `printFloat(e)`, `printBool(b)`, `printString("literal")`

NO goto/labels in source (rejected by well-formedness). NO names starting with `__`.
All scalars auto-initialize to 0 / 0.0 / false. Arrays are NOT auto-initialized — set
elements before reading (read of unwritten element is undefined; avoid).

Int = signed 64-bit, wrapping (two's complement). Operators:
`+ - * / %` (div/mod truncate toward zero, C semantics), `<< >> & | ^`, unary `-`, `~` (bitwise not).
Comparisons `< <= > >= == !=`; logical `&& || !`. Bool literals `true`/`false`.

Float = IEEE double. Float builtins (all return float unless noted):
`intToFloat(e)`, `floatToInt(e)` (->int, truncates toward zero), `sqrt cos sin tan exp log log2 log10 abs neg round`(unary),
`pow(a,b) fmin(a,b) fmax(a,b)`. Mixing int and float in an arith op auto-promotes to float.

### Gotchas that cause SPURIOUS pass-drops (avoid in normal tests unless testing them)
- Do NOT read an array inside a boolean condition. Load into a scalar first:
  `t := A[i]; if (t < 5) {...}` — NOT `if (A[i] < 5) {...}`.
- Float comparisons: only one operand ordering is reliably supported. Prefer
  `var < literal` style; keep float conditions simple.

## Print/format matching
While runtime: `printInt`→`%ld`, `printFloat`→`%f` (6 decimals), `printBool`→`true`/`false`,
`printString`→raw. Make C use the same. Fortran: integers via `I0`, floats via `F0.6`
(harness compares floats numerically with tolerance, so exact text need not match for floats).

### C reference skeleton
```c
#include <stdio.h>
#include <stdint.h>
#include <math.h>
int main(void){
  int64_t i=0,n=0;  /* ints are int64_t */
  double x=0.0;     /* floats are double */
  /* ... mirror the While program ... */
  printf("%ld\n",(long)n);
  printf("%f\n",x);
  return 0;
}
```
For int wrapping in multiply/add that may overflow, use unsigned arithmetic to get
defined two's-complement wrap: `(int64_t)((uint64_t)a * (uint64_t)b)`.

### Fortran reference skeleton
```fortran
      PROGRAM T
      IMPLICIT DOUBLE PRECISION (A-H,O-Z)
      INTEGER*8 I,N
      DIMENSION A(0:99)
      ... mirror logic; use IF/GOTO for loops ...
      WRITE(*,'(A,I0)') 'label=',N
      WRITE(*,'(A,F0.6)') 'label=',X
      END
```
Keep Fortran array indexing matched to the While indexing you choose (0-based DIMENSION
A(0:N-1) keeps it identical to C/While 0-based).

## Validate before finishing
Run: `python3 stress/diff_test.py stress/t --filter <prefix> -v`
Every test must reach PASS or be reported as a genuine MISCOMPILE finding.
