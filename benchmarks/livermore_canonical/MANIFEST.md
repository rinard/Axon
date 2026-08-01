<!-- Copyright (c) 2026 Martin Rinard -->
# Canonical Livermore Loops — extraction manifest

This directory contains 24 standalone single-kernel programs in three languages
(Fortran, C, WhileLang), each with kernel bodies extracted **verbatim** from the
canonical netlib distribution at `https://www.netlib.org/benchmark/livermore`
(McMahon, UCRL-53745, 1986; last updated 1993, version mf528).

The canonical source is the `KERNEL` subroutine of `lloops.f` (lines 1752–2576);
extracted to `/tmp/livermore_orig/kernels_only.f`.

## Conventions

- **Array layout**: Fortran column-major preserved across all three languages.
  - `.c` uses `#define` macros: `#define ZA(j,k) za[((k)-1)*Nfast + (j)]`.
  - `.w` open-codes the index arithmetic, using the same variable names
    (canonical-Fortran's `j`/`k`/etc.) consistently across init and kernel.
- **Indexing**: 1-based throughout; `.c` and `.w` over-allocate by 1 element so
  index 0 is unused. `.f` uses native 1-based.
- **Initialization** uses the canonical SIGNEL pseudo-PRNG
  (`v[k] = (buzz - fizz) * 0.1` with the standard fuzz/buzz/fizz recurrence,
  matching `SUBROUTINE SIGNEL` at `lloops.f:5013`).
- **Spacer scalars** (Q, R, S, T, A11..A33, SIG, DM22..28, etc.) are pulled
  from a 39-element `spacer[]` array filled by SIGNEL with the same seed.
  Indices match the order in `/SPACER/` COMMON (`lloops.f:1813-1816`):

  ```
  position  scalar     position  scalar     position  scalar
   1        A11         14       DI         27       FLX
   2        A12         15       DK         28       Q
   3        A13         16       DM22       29       QA
   4        A21         17       DM23       30       R
   5        A22         18       DM24       31       RI
   6        A23         19       DM25       32       S
   7        A31         20       DM26       33       SCALE
   8        A32         21       DM27       34       SIG
   9        A33         22       DM28       35       STB5
  10        AR          23       DN         36       T
  11        BR          24       E3         37       XNC
  12        C0          25       E6         38       XNEI
  13        CR          26       EXPMAX     39       XNM
  ```

- **Timing wrapper**: each program is `<init>; <pre-loop setup>; rep=1; while
  rep<=NREPS { <kernel body>; rep=rep+1 }; <print checksum>`.
  NREPS calibrated per-kernel to land near 20s for FIL-O2.
- **Checksum**: each program prints one `<name> = <value>\n` line that is
  comparable across .f/.c/.w outputs. Comparator in `run_opt_compare.sh`
  matches by name.

## Per-kernel specs

| #  | Name              | n     | Arrays                                          | Spacer scalars         | Checksum       |
|----|-------------------|-------|-------------------------------------------------|------------------------|----------------|
| 01 | hydro             | 1001  | X, Y, Z(1012)                                   | Q, R, T                | X(1)           |
| 02 | iccg              | 1001  | X, V                                            | —                      | X(N)           |
| 03 | dot               | 1001  | Z, X                                            | —                      | Q              |
| 04 | banded            | 1001  | XZ alias of (X∪Z), Y                            | —                      | XZ(7)          |
| 05 | tridiag           | 1001  | X, Y, Z                                         | —                      | X(N)           |
| 06 | recurrence        | 64    | W(64), B(64,64)                                 | —                      | W(N)           |
| 07 | eos               | 995   | X, U(1001), Y, Z                                | Q, R, T                | X(1)           |
| 08 | adi               | 100   | U1, U2, U3 (5×101×2), DU1, DU2, DU3 (101)       | A11..A33, SIG          | U1(2,2,2)      |
| 09 | integrate         | 101   | PX(25,101)                                      | C0, DM22..DM28         | PX(1,1)        |
| 10 | diff_predict      | 101   | PX(25,101), CX(25,101)                          | —                      | PX(14,1)       |
| 11 | prefix_sum        | 1001  | X, Y                                            | —                      | X(N)           |
| 12 | first_diff        | 1000  | X, Y(1001)                                      | —                      | X(1)           |
| 13 | pic_2d            | 64    | P(4,64), B(64,64), C(64,64), H(64,64), Y, Z, E(96), F(96) | —          | P(1,1)         |
| 14 | pic_1d            | 1001  | VX, XX, IX, XI, EX1, DEX1, EX, DEX, GRD, IR, RX, RH(2048) | FLX     | RH(1)          |
| 15 | casual            | 101   | VY(101,7), VH(101,7), VF(101,7), VG(101,7), VS(101,7) | —                | VY(2,2)        |
| 16 | monte_carlo       | 75    | PLAN(300), D(300), ZONE(300)                    | R, S, T                | k2 + k3        |
| 17 | implicit_cond     | 101   | VSP, VSTP, VXNE, VXND, VE3, VLR, VLIN (101)     | —                      | VXNE(N)        |
| 18 | hydro_2d          | 101   | ZA, ZB, ZP, ZQ, ZR, ZM, ZU, ZV, ZZ (101×7)      | —                      | ZU(51,4)       |
| 19 | linear_recur      | 101   | B5(101), SA(101), SB(101)                       | STB5                   | B5(N)          |
| 20 | discrete_ord      | 1000  | X, Y, Z, U, V, W, G, XX(1001), VX(1001)         | DK, S, T               | X(N)           |
| 21 | matmul            | 25    | PX(25,101), VY(101,25), CX(25,101)              | —                      | PX(1,1)        |
| 22 | planck            | 101   | U, V, W, X, Y                                   | EXPMAX                 | W(51)          |
| 23 | hydro_implicit    | 101   | ZA, ZB, ZP, ZR, ZU, ZV, ZZ (101×7)              | —                      | ZA(51,4)       |
| 24 | find_min          | 1001  | X                                               | —                      | m, X(m)        |

## Initial NREPS estimates

Conservative starting points (will be calibrated to land near 20s for FIL-O2):

| #  | NREPS_init  | #  | NREPS_init  | #  | NREPS_init   |
|----|-------------|----|-------------|----|--------------|
| 01 | 26_000_000  | 09 | 6_000_000   | 17 | 23_000_000   |
| 02 | 1_500_000   | 10 | 6_000_000   | 18 | 1_400_000    |
| 03 | 31_700_000  | 11 | 30_000_000  | 19 | 13_000_000   |
| 04 | 25_000_000  | 12 | 35_000_000  | 20 | 4_000_000    |
| 05 | 1_500_000   | 13 | 2_600_000   | 21 | 100_000      |
| 06 | 30_000      | 14 | 14_000_000  | 22 | 48_640_000   |
| 07 | 20_000_000  | 15 | 600_000     | 23 | 8_000_000    |
| 08 | 1_000_000   | 16 | 162_000_000 | 24 | 30_600_000   |
