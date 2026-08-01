#!/bin/bash
# Copyright (c) 2026 Martin Rinard
#
# Full Livermore Loops timing: Fortran -O{0,1,2}, C -O{0,1,2}, WL -O0 + optimized.
# Wall-clock, best-of-3 per variant. Full rep counts.
#
# Usage:  ./run_full.sh                 — all kernels
#         ./run_full.sh k03_dot k05_tridiag
#         RUNS=5 ./run_full.sh          — override run count
#
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJ_DIR="$(cd "$SCRIPT_DIR/../.." && pwd)"
BUILD_DIR="$SCRIPT_DIR/build_full"
RUNS=${RUNS:-3}

mkdir -p "$BUILD_DIR"

# ── helpers ────────────────────────────────────────────────────

best_of() {
  # $1 = path to executable; runs $RUNS times, prints min wall-clock seconds.
  python3 -c "
import subprocess, sys, time
best = None
for _ in range($RUNS):
    t0 = time.monotonic()
    r = subprocess.run([sys.argv[1]], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    dt = time.monotonic() - t0
    if r.returncode != 0:
        print('—'); sys.exit(0)
    if best is None or dt < best:
        best = dt
print(f'{best:.4f}')
" "$1"
}

ratio() {
  # $1 = numerator, $2 = denominator (strings, may be '—')
  if [ "$1" = "—" ] || [ "$2" = "—" ]; then echo "—"; return; fi
  python3 -c "print(f'{float(\"$1\")/float(\"$2\"):.2f}x')"
}

# ── build compiler ─────────────────────────────────────────────

COMPILER="$PROJ_DIR/.lake/build/bin/compiler"
if [ ! -x "$COMPILER" ]; then
  echo "Building WhileLang compiler …"
  (cd "$PROJ_DIR" && lake build compiler 2>&1 | tail -1)
fi

if ! command -v gfortran &>/dev/null; then
  echo "gfortran not found — install it to run this script." >&2
  exit 1
fi

# ── determine kernels ──────────────────────────────────────────

if [ $# -gt 0 ]; then
  KERNELS=("$@")
else
  KERNELS=()
  for f in "$SCRIPT_DIR"/k*.w; do
    KERNELS+=("$(basename "$f" .w)")
  done
fi

# ── compile all variants ───────────────────────────────────────

echo "Compiling all variants …"
compile_fail=()
for name in "${KERNELS[@]}"; do
  wfile="$SCRIPT_DIR/${name}.w"
  cfile="$SCRIPT_DIR/${name}.c"
  ffile="$SCRIPT_DIR/${name}.f"

  if [ -f "$cfile" ]; then
    cc -O0 -lm -o "$BUILD_DIR/${name}_c_O0" "$cfile" 2>/dev/null || true
    cc -O1 -lm -o "$BUILD_DIR/${name}_c_O1" "$cfile" 2>/dev/null || true
    cc -O2 -lm -o "$BUILD_DIR/${name}_c_O2" "$cfile" 2>/dev/null || true
  fi

  if [ -f "$ffile" ]; then
    gfortran -O0 -o "$BUILD_DIR/${name}_f_O0" "$ffile" 2>/dev/null || true
    gfortran -O1 -o "$BUILD_DIR/${name}_f_O1" "$ffile" 2>/dev/null || true
    gfortran -O2 -o "$BUILD_DIR/${name}_f_O2" "$ffile" 2>/dev/null || true
  fi

  if [ -f "$wfile" ]; then
    if ! "$COMPILER" "$wfile" -O0 -o "$BUILD_DIR/${name}_wl_O0" 2>/dev/null; then
      compile_fail+=("${name} (WL-O0)")
    fi
    if ! "$COMPILER" "$wfile"     -o "$BUILD_DIR/${name}_wl_opt" 2>/dev/null; then
      compile_fail+=("${name} (WL-opt)")
    fi
  fi
done

if [ ${#compile_fail[@]} -gt 0 ]; then
  echo "  !! Compile failures:"
  printf '       %s\n' "${compile_fail[@]}"
fi

# ── run benchmarks ─────────────────────────────────────────────

echo ""
echo "Wall-clock seconds, best of $RUNS runs"
echo ""
printf "%-22s %8s %8s %8s %8s %8s %8s %8s %8s   %7s %7s\n" \
       "Kernel" "F-O0" "F-O1" "F-O2" "C-O0" "C-O1" "C-O2" "WL-O0" "WL-opt" "WL/F-O2" "WL/C-O2"
printf "%-22s %8s %8s %8s %8s %8s %8s %8s %8s   %7s %7s\n" \
       "──────────────────" "──────" "──────" "──────" "──────" "──────" "──────" "──────" "──────" \
       "───────" "───────"

time_or_dash() {
  # $1 = path; print best_of time if executable, else dash
  if [ -x "$1" ]; then best_of "$1"; else echo "—"; fi
}

for name in "${KERNELS[@]}"; do
  t_f0=$(time_or_dash "$BUILD_DIR/${name}_f_O0")
  t_f1=$(time_or_dash "$BUILD_DIR/${name}_f_O1")
  t_f2=$(time_or_dash "$BUILD_DIR/${name}_f_O2")
  t_c0=$(time_or_dash "$BUILD_DIR/${name}_c_O0")
  t_c1=$(time_or_dash "$BUILD_DIR/${name}_c_O1")
  t_c2=$(time_or_dash "$BUILD_DIR/${name}_c_O2")
  t_w0=$(time_or_dash "$BUILD_DIR/${name}_wl_O0")
  t_wo=$(time_or_dash "$BUILD_DIR/${name}_wl_opt")

  r_f2=$(ratio "$t_wo" "$t_f2")
  r_c2=$(ratio "$t_wo" "$t_c2")

  printf "%-22s %8s %8s %8s %8s %8s %8s %8s %8s   %7s %7s\n" \
         "$name" "$t_f0" "$t_f1" "$t_f2" "$t_c0" "$t_c1" "$t_c2" "$t_w0" "$t_wo" "$r_f2" "$r_c2"
done

echo ""
echo "WL-O0  : compiler invoked with -O0 (no optimization passes)"
echo "WL-opt : compiler invoked without -O0 (LICM, DCE, RegAlloc, …)"
echo "Ratios compare WL-opt against the corresponding O2 baseline."
echo "Build artifacts in $BUILD_DIR (delete when done)."
