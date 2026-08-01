#!/bin/bash
# Copyright (c) 2026 Martin Rinard
#
# Fast correctness sweep for canonical Livermore Loops.
# Reduces rep counts by $DIVISOR (default 1000), then builds and runs the
# three optimized variants exactly once each (gfortran -O2, clang -O2, FIL-O2)
# and compares the printed checksum across .f / .c / .w.
#
# Usage:  ./run_fast.sh                 — all kernels, divisor 1000
#         ./run_fast.sh k03_dot         — one kernel
#         DIVISOR=10000 ./run_fast.sh   — override divisor
#
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJ_DIR="$(cd "$SCRIPT_DIR/../.." && pwd)"
FAST_DIR="$SCRIPT_DIR/build_fast"
DIVISOR=${DIVISOR:-1000}

rm -rf "$FAST_DIR"
mkdir -p "$FAST_DIR/src"

# ── helpers ────────────────────────────────────────────────────

time_cmd() {
  # Stdout: wall-clock seconds. Stderr: program's stdout. Returns program rc.
  python3 -c "
import subprocess, sys, time
start = time.monotonic()
r = subprocess.run(sys.argv[1:], capture_output=True, text=True)
dt = time.monotonic() - start
print(f'{dt:.4f}')
print(r.stdout, end='', file=sys.stderr)
sys.exit(r.returncode)
" "$@"
}

# ── build compiler ─────────────────────────────────────────────

COMPILER="$PROJ_DIR/.lake/build/bin/compiler"
if [ ! -x "$COMPILER" ]; then
  echo "Building FIL compiler …"
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

# ── create reduced-rep source copies ──────────────────────────

echo "Creating reduced-rep sources (÷${DIVISOR}) …"
for name in "${KERNELS[@]}"; do
  wfile="$SCRIPT_DIR/${name}.w"
  ffile="$SCRIPT_DIR/${name}.f"
  cfile="$SCRIPT_DIR/${name}.c"

  if [ -f "$wfile" ]; then
    python3 -c "
import re, sys
text = open(sys.argv[1]).read()
def reduce(m):
    n = max(1, int(m.group(1)) // $DIVISOR)
    return f'while (rep <= {n})'
text = re.sub(r'while \(rep <= (\d+)\)', reduce, text)
open(sys.argv[2], 'w').write(text)
" "$wfile" "$FAST_DIR/src/${name}.w"
  fi

  if [ -f "$ffile" ]; then
    python3 -c "
import re, sys
text = open(sys.argv[1]).read()
def reduce(m):
    n = max(1, int(m.group(3)) // $DIVISOR)
    return f'DO {m.group(1)} {m.group(2)} = 1, {n}'
text = re.sub(r'DO\s+(\d+)\s+(REP|IREP)\s*=\s*1,\s*(\d+)', reduce, text)
open(sys.argv[2], 'w').write(text)
" "$ffile" "$FAST_DIR/src/${name}.f"
  fi

  if [ -f "$cfile" ]; then
    python3 -c "
import re, sys
text = open(sys.argv[1]).read()
def reduce(m):
    n = max(1, int(m.group(1)) // $DIVISOR)
    return f'#define NREPS {n}'
text = re.sub(r'#define\s+NREPS\s+(\d+)', reduce, text)
open(sys.argv[2], 'w').write(text)
" "$cfile" "$FAST_DIR/src/${name}.c"
  fi
done

cp "$SCRIPT_DIR/signel.h" "$FAST_DIR/src/signel.h" 2>/dev/null || true

# ── compile (only the three optimized variants) ────────────────

echo "Compiling …"
compile_fail=()
for name in "${KERNELS[@]}"; do
  wfile="$FAST_DIR/src/${name}.w"
  ffile="$FAST_DIR/src/${name}.f"
  cfile="$FAST_DIR/src/${name}.c"

  if [ -f "$ffile" ]; then
    gfortran -O2 -o "$FAST_DIR/${name}_f_O2" "$ffile" 2>/dev/null \
      || compile_fail+=("$name (f-O2)")
  fi

  if [ -f "$cfile" ]; then
    cc -O2 -lm -o "$FAST_DIR/${name}_c_O2" "$cfile" 2>/dev/null \
      || compile_fail+=("$name (c-O2)")
  fi

  if [ -f "$wfile" ]; then
    "$COMPILER" "$wfile" -o "$FAST_DIR/${name}_wl_opt" 2>/dev/null \
      || compile_fail+=("$name (wl-opt)")
  fi
done

if [ ${#compile_fail[@]} -gt 0 ]; then
  echo "  !! Compile failures:"
  printf '       %s\n' "${compile_fail[@]}"
fi

# ── run once and compare ───────────────────────────────────────

echo ""
printf "%-22s  %8s %8s %8s   %s\n" \
       "Kernel" "F-O2" "C-O2" "FIL-O2" "OK?"
printf "%-22s  %8s %8s %8s   %s\n" \
       "──────────────────" "────────" "────────" "────────" "──────"

pass=0; fail=0; skip=0

for name in "${KERNELS[@]}"; do
  run_one() {
    local v="$1"
    local bin="$FAST_DIR/${name}_${v}"
    local out_file="$FAST_DIR/${name}_${v}.out"
    if [ -x "$bin" ]; then
      local t
      t=$(time_cmd "$bin" 2>"$out_file") || t="ERR"
      echo "$t"
    else
      echo "—"
    fi
  }
  T_f2=$(run_one f_O2)
  T_c2=$(run_one c_O2)
  T_wo=$(run_one wl_opt)

  OUT_f2="$FAST_DIR/${name}_f_O2.out"
  OUT_c2="$FAST_DIR/${name}_c_O2.out"
  OUT_wo="$FAST_DIR/${name}_wl_opt.out"

  match=$(python3 -c "
import re, sys
num_re = r'[-+]?(?:\d+\.\d*|\.\d+|\d+)[eEdD][-+]?\d+|[-+]?\d+\.\d*|[-+]?\.\d+|[-+]?\d+'
def first(path):
    if not path: return None
    try:
        for line in open(path).read().splitlines():
            s = line.strip().lower()
            if s.startswith(('elapsed', 'time:', 'time ')):
                continue
            # If the line has an '=', take the rightmost part (value, not the LHS index)
            if '=' in line:
                line = line.rsplit('=', 1)[1]
            for m in re.finditer(num_re, line):
                tok = m.group(0).replace('d','e').replace('D','E')
                try:
                    return float(tok)
                except ValueError:
                    pass
    except FileNotFoundError:
        return None
    return None

paths = {
    'F-O2':  '$OUT_f2',
    'C-O2':  '$OUT_c2',
    'FIL-O2':'$OUT_wo',
}
vals = {k: first(p) for k,p in paths.items() if p}
vals = {k:v for k,v in vals.items() if v is not None}
if len(vals) < 2:
    print('—'); sys.exit()
ref_k = 'F-O2' if 'F-O2' in vals else next(iter(vals))
ref = vals[ref_k]
mism = []
for k,v in vals.items():
    if k == ref_k: continue
    if max(abs(ref),abs(v)) < 1e-5:
        continue
    if abs(ref-v)/max(abs(ref),abs(v),1e-15) >= 1e-4:
        mism.append(f'{k}={v:.6g}')
if mism:
    print('FAIL ' + 'vs'.join(mism) + f' ref({ref_k})={ref:.6g}')
else:
    print('ok')
")

  if [[ "$match" == ok* ]]; then
    ((pass++))
  elif [[ "$match" == "—" ]]; then
    ((skip++))
  else
    ((fail++))
  fi

  printf "%-22s  %8s %8s %8s   %s\n" \
    "$name" "$T_f2" "$T_c2" "$T_wo" "$match"
done

echo ""
echo "Results: $pass pass, $fail fail, $skip skip   (rep counts ÷${DIVISOR}, each variant run once)"
echo "Build artifacts in $FAST_DIR"
