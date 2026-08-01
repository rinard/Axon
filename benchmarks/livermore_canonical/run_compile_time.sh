#!/bin/bash
# Copyright (c) 2026 Martin Rinard
#
# Compile-time measurements for canonical Livermore Loops.
# Times the compiler (not the resulting binary) across the same 8 variants
# as run_full.sh: gfortran -O{0,1,2}, clang -O{0,1,2}, FIL with -O0, FIL default.
# Wall-clock, best-of-$RUNS per variant.
#
# Usage:  ./run_compile_time.sh                 — all kernels, best of 3
#         ./run_compile_time.sh k03_dot k07_eos
#         RUNS=5 ./run_compile_time.sh          — override run count
#
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJ_DIR="$(cd "$SCRIPT_DIR/../.." && pwd)"
BUILD_DIR="$SCRIPT_DIR/build_compile_time"
RUNS=${RUNS:-3}

rm -rf "$BUILD_DIR"
mkdir -p "$BUILD_DIR"

COMPILER="$PROJ_DIR/.lake/build/bin/compiler"
if [ ! -x "$COMPILER" ]; then
  echo "Building FIL compiler …"
  (cd "$PROJ_DIR" && lake build compiler 2>&1 | tail -1)
fi

if ! command -v gfortran &>/dev/null; then
  echo "gfortran not found." >&2; exit 1
fi

best_of() {
  # Args: command + args. Runs $RUNS times, prints min wall-clock seconds.
  python3 -c "
import subprocess, sys, time
best = None
for _ in range($RUNS):
    t0 = time.monotonic()
    r = subprocess.run(sys.argv[1:], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    dt = time.monotonic() - t0
    if r.returncode != 0:
        print('—'); sys.exit(0)
    if best is None or dt < best:
        best = dt
print(f'{best:.4f}')
" "$@"
}

if [ $# -gt 0 ]; then
  KERNELS=("$@")
else
  KERNELS=()
  for f in "$SCRIPT_DIR"/k*.w; do
    KERNELS+=("$(basename "$f" .w)")
  done
fi

echo ""
echo "Compile-time wall-clock seconds, best of $RUNS runs"
echo ""
printf "%-22s %8s %8s %8s %8s %8s %8s %8s %8s\n" \
       "Kernel" "F-O0" "F-O1" "F-O2" "C-O0" "C-O1" "C-O2" "FIL" "FIL-O2"
printf "%-22s %8s %8s %8s %8s %8s %8s %8s %8s\n" \
       "──────────────────" "──────" "──────" "──────" "──────" "──────" "──────" "──────" "──────"

time_or_dash() {
  # $1 = source file, $2... = compile command (followed by output flag/path)
  local src="$1"; shift
  if [ ! -f "$src" ]; then echo "—"; return; fi
  best_of "$@"
}

for name in "${KERNELS[@]}"; do
  ffile="$SCRIPT_DIR/${name}.f"
  cfile="$SCRIPT_DIR/${name}.c"
  wfile="$SCRIPT_DIR/${name}.w"

  t_f0=$(time_or_dash "$ffile" gfortran -O0 -o "$BUILD_DIR/${name}_f_O0" "$ffile")
  t_f1=$(time_or_dash "$ffile" gfortran -O1 -o "$BUILD_DIR/${name}_f_O1" "$ffile")
  t_f2=$(time_or_dash "$ffile" gfortran -O2 -o "$BUILD_DIR/${name}_f_O2" "$ffile")
  t_c0=$(time_or_dash "$cfile" cc       -O0 -lm -o "$BUILD_DIR/${name}_c_O0" "$cfile")
  t_c1=$(time_or_dash "$cfile" cc       -O1 -lm -o "$BUILD_DIR/${name}_c_O1" "$cfile")
  t_c2=$(time_or_dash "$cfile" cc       -O2 -lm -o "$BUILD_DIR/${name}_c_O2" "$cfile")
  t_w0=$(time_or_dash "$wfile" "$COMPILER" "$wfile" -O0 -o "$BUILD_DIR/${name}_wl_O0")
  t_wo=$(time_or_dash "$wfile" "$COMPILER" "$wfile"     -o "$BUILD_DIR/${name}_wl_opt")

  printf "%-22s %8s %8s %8s %8s %8s %8s %8s %8s\n" \
    "$name" "$t_f0" "$t_f1" "$t_f2" "$t_c0" "$t_c1" "$t_c2" "$t_w0" "$t_wo"
done

echo ""
echo "Build artifacts in $BUILD_DIR (delete when done)."
