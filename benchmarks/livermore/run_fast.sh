#!/bin/bash
# Copyright (c) 2026 Martin Rinard
#
# Fast smoke-test: reduced rep counts (÷1000) for quick correctness + timing check
# Creates temporary copies, builds, compares WL vs Fortran output, shows timing.
#
# Usage:  ./run_fast.sh            — all kernels
#         ./run_fast.sh k03_dot    — one kernel
#
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJ_DIR="$(cd "$SCRIPT_DIR/../.." && pwd)"
FAST_DIR="$SCRIPT_DIR/build_fast"
DIVISOR=1000   # divide rep counts by this

rm -rf "$FAST_DIR"
mkdir -p "$FAST_DIR/src"

# ── helpers ────────────────────────────────────────────────────

time_cmd() {
  # Prints wall-clock seconds to stdout, program output to stderr.
  # Returns the program's exit code.
  python3 -c "
import subprocess, sys, time
start = time.monotonic()
r = subprocess.run(sys.argv[1:], capture_output=True, text=True)
end = time.monotonic()
print(f'{end - start:.6f}')
print(r.stdout, end='', file=sys.stderr)
sys.exit(r.returncode)
" "$@"
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

# ── create reduced-rep source copies ──────────────────────────

echo "Creating reduced-rep sources (÷${DIVISOR}) …"
for name in "${KERNELS[@]}"; do
  wfile="$SCRIPT_DIR/${name}.w"
  ffile="$SCRIPT_DIR/${name}.f"

  if [ -f "$wfile" ]; then
    # Replace "while (rep <= NNNN)" with reduced count
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
    # Reduce the outer Fortran rep loop: "DO <label> (REP|IREP) = 1, N"
    python3 -c "
import re, sys
text = open(sys.argv[1]).read()
def reduce(m):
    n = max(1, int(m.group(3)) // $DIVISOR)
    return f'DO {m.group(1)} {m.group(2)} = 1, {n}'
text = re.sub(r'DO (\d+) (REP|IREP) = 1, (\d+)', reduce, text)
open(sys.argv[2], 'w').write(text)
" "$ffile" "$FAST_DIR/src/${name}.f"
  fi
done

# ── compile ────────────────────────────────────────────────────

echo "Compiling …"
compile_fail=()
for name in "${KERNELS[@]}"; do
  wfile="$FAST_DIR/src/${name}.w"
  ffile="$FAST_DIR/src/${name}.f"

  if [ -f "$ffile" ]; then
    gfortran -O0 -o "$FAST_DIR/${name}_f_O0" "$ffile" 2>/dev/null || true
    gfortran -O1 -o "$FAST_DIR/${name}_f_O1" "$ffile" 2>/dev/null || true
    gfortran -O2 -o "$FAST_DIR/${name}_f_O2" "$ffile" 2>/dev/null || true
  fi

  if [ -f "$wfile" ]; then
    if ! "$COMPILER" "$wfile" -o "$FAST_DIR/${name}_wl" 2>/dev/null; then
      compile_fail+=("$name")
    fi
  fi
done

if [ ${#compile_fail[@]} -gt 0 ]; then
  echo "  !! Compile failures: ${compile_fail[*]}"
fi

# ── run and compare ────────────────────────────────────────────

echo ""
printf "%-22s  %8s  %8s  %8s  %8s  %8s  %s\n" \
       "Kernel" "F-O0 (s)" "F-O1 (s)" "F-O2 (s)" "WL (s)" "WL/F-O2" "Match?"
printf "%-22s  %8s  %8s  %8s  %8s  %8s  %s\n" \
       "──────────────────" "────────" "────────" "────────" "────────" "───────" "──────"

pass=0
fail=0
skip=0

for name in "${KERNELS[@]}"; do
  t_f0="—"
  t_f1="—"
  t_f2="—"
  t_wl="—"
  ratio="—"
  match="—"

  # Run Fortran -O0/-O1/-O2; capture F-O2 output for correctness check
  if [ -x "$FAST_DIR/${name}_f_O0" ]; then
    t_f0=$(time_cmd "$FAST_DIR/${name}_f_O0" 2>/dev/null)
  fi
  if [ -x "$FAST_DIR/${name}_f_O1" ]; then
    t_f1=$(time_cmd "$FAST_DIR/${name}_f_O1" 2>/dev/null)
  fi
  if [ -x "$FAST_DIR/${name}_f_O2" ]; then
    t_f2=$(time_cmd "$FAST_DIR/${name}_f_O2" 2>"$FAST_DIR/${name}_f_O2.out")
  fi

  # Run WL and capture output
  wl_ok=true
  if [ -x "$FAST_DIR/${name}_wl" ]; then
    if ! t_wl=$(time_cmd "$FAST_DIR/${name}_wl" 2>"$FAST_DIR/${name}_wl.out"); then
      wl_ok=false
    fi
  fi

  # Correctness: compare WL vs F-O2 numeric output
  if [ -x "$FAST_DIR/${name}_wl" ]; then
    if $wl_ok && [ -f "$FAST_DIR/${name}_wl.out" ] && [ -s "$FAST_DIR/${name}_wl.out" ] \
       && [ -f "$FAST_DIR/${name}_f_O2.out" ] && [ -s "$FAST_DIR/${name}_f_O2.out" ]; then
      match=$(python3 -c "
import re
# Only match floats (must contain '.' or an exponent) so integer labels like
# 'K3', 'x(7)', 'p(1,1)' in Fortran headers are ignored.
num_re = r'[-+]?(?:\d+\.\d*|\.\d+|\d+)(?:[eEdD][-+]?\d+)|[-+]?\d+\.\d*|[-+]?\.\d+'
def nums(path):
    out = []
    for line in open(path).read().strip().splitlines():
        s = line.strip().lower()
        if s.startswith(('elapsed', 'time')): continue
        for m in re.finditer(num_re, line):
            tok = m.group(0).replace('d', 'e').replace('D', 'E')
            try:
                float(tok); out.append(tok)
            except ValueError:
                pass
    return out
fn, wn = nums('$FAST_DIR/${name}_f_O2.out'), nums('$FAST_DIR/${name}_wl.out')
if not fn or not wn:
    print('ok?')
else:
    # WL and Fortran both print only what the program explicitly prints;
    # compare the first numeric token in each output.
    f, w = float(fn[0]), float(wn[0])
    # WL prints floats with %f (~6 decimal places), so values below ~1e-5
    # are indistinguishable from zero. Treat as match if both are that small.
    if max(abs(f), abs(w)) < 1e-5:
        print('ok')
    elif abs(f - w) / max(abs(f), abs(w), 1e-15) < 1e-4:
        print('ok')
    else:
        print(f'MISMATCH {fn[0]} vs {wn[0]}')
")
      if [[ "$match" == ok* ]]; then
        ((pass++))
      else
        ((fail++))
      fi
    elif ! $wl_ok; then
      match="FAIL(run)"
      ((fail++))
    else
      match="FAIL"
      ((fail++))
    fi
  elif printf '%s\n' "${compile_fail[@]}" | grep -qx "$name" 2>/dev/null; then
    match="no-wl"
    ((skip++))
  else
    match="skip"
    ((skip++))
  fi

  # Compute ratio WL / F-O2
  if [ "$t_f2" != "—" ] && [ "$t_wl" != "—" ]; then
    ratio=$(python3 -c "print(f'{float(\"$t_wl\")/float(\"$t_f2\"):.1f}x')")
  fi

  printf "%-22s  %8s  %8s  %8s  %8s  %8s  %s\n" "$name" "$t_f0" "$t_f1" "$t_f2" "$t_wl" "$ratio" "$match"
done

echo ""
echo "Results: $pass pass, $fail fail, $skip skip (rep counts ÷${DIVISOR})"
echo "Temp files in $FAST_DIR (delete when done)"
