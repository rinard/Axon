#!/bin/bash
# Copyright (c) 2026 Martin Rinard
# Benchmark all Livermore kernels: C -O2, Fortran -O2, WhileLang
# 5 runs each, take fastest (minimum) time. Report after each kernel.
set -euo pipefail

DIR="$(cd "$(dirname "$0")" && pwd)"
BD="$DIR/build_bench5"

KERNELS=(
  k01_hydro k02_iccg k03_dot k04_banded k05_tridiag
  k06_recurrence k07_eos k08_adi k09_integrate k10_diff_predict
  k11_prefix_sum k12_first_diff k13_pic_2d k14_pic_1d k15_casual
  k16_monte_carlo k17_implicit_cond k18_hydro_2d k19_linear_recurrence k20_discrete_ord
  k21_matmul k22_planck k23_hydro_implicit k24_find_min
)

NRUNS=5

time_run() {
  # Returns "time output" — wall-clock seconds and captured stdout
  python3 -c "
import subprocess, sys, time
start = time.monotonic()
r = subprocess.run(sys.argv[1:], capture_output=True, text=True)
elapsed = time.monotonic() - start
print(f'{elapsed:.3f}')
print(r.stdout, end='', file=sys.stderr)
sys.exit(r.returncode)
" "$@"
}

min_time() {
  # Run binary $1 NRUNS times, print "min_time first_run_output"
  local bin="$1"
  local best=""
  local out=""
  for i in $(seq 1 $NRUNS); do
    local t
    t=$(time_run "$bin" 2>"$BD/tmp_out.txt") || { echo "ERR"; return; }
    if [ -z "$out" ]; then
      out=$(cat "$BD/tmp_out.txt")
    fi
    if [ -z "$best" ] || python3 -c "exit(0 if float('$t') < float('$best') else 1)"; then
      best="$t"
    fi
  done
  echo "$best"
  echo "$out" > "$BD/tmp_last_out.txt"
}

printf "\n%-22s  %8s  %8s  %8s  %8s  %8s  %s\n" \
  "Kernel" "F -O2" "C -O2" "WL" "WL/C" "WL/F" "Correct?"
printf "%-22s  %8s  %8s  %8s  %8s  %8s  %s\n" \
  "──────────────────" "──────" "──────" "──────" "──────" "──────" "────────"

for name in "${KERNELS[@]}"; do
  c_bin="$BD/${name}_c"
  f_bin="$BD/${name}_f"
  w_bin="$BD/${name}_wl"

  t_c="—"; t_f="—"; t_w="—"
  out_c=""; out_f=""; out_w=""
  ratio_wc="—"; ratio_wf="—"
  correct="—"

  # Run C -O2
  if [ -x "$c_bin" ]; then
    t_c=$(min_time "$c_bin")
    out_c=$(cat "$BD/tmp_last_out.txt" 2>/dev/null || true)
  fi

  # Run Fortran -O2
  if [ -x "$f_bin" ]; then
    t_f=$(min_time "$f_bin")
    out_f=$(cat "$BD/tmp_last_out.txt" 2>/dev/null || true)
  fi

  # Run WhileLang
  if [ -x "$w_bin" ]; then
    t_w=$(min_time "$w_bin")
    out_w=$(cat "$BD/tmp_last_out.txt" 2>/dev/null || true)
  fi

  # Correctness: compare WL printed values to C result values.
  # C output: 'elapsed: ...' line then result line(s) like 'x[1] = 0.101987'
  # WL output: bare numbers from printfloat/printint, then 'name = value' dump
  if [ "$t_c" != "—" ] && [ "$t_c" != "ERR" ] && [ "$t_w" != "—" ] && [ "$t_w" != "ERR" ]; then
    correct=$(python3 -c "
import re, sys
c_out = '''$out_c'''
w_out = '''$out_w'''
num_re = r'[-+]?[0-9]*\.?[0-9]+(?:[eE][-+]?[0-9]+)?'

# Parse C output: 'name = value' pairs (skip elapsed line)
c_vars = {}
for line in c_out.strip().splitlines():
    if line.startswith('elapsed'): continue
    for m in re.finditer(r'(\w+)\s*=\s*(' + num_re + r')', line):
        c_vars[m.group(1)] = m.group(2)

# Parse WL output: 'name = value' lines from compiled program
w_vars = {}
for line in w_out.strip().splitlines():
    m = re.match(r'(\w+)\s*=\s*(' + num_re + r')\s*$', line)
    if m: w_vars[m.group(1)] = m.group(2)

# Compare on shared variable names
shared = set(c_vars) & set(w_vars)
if not shared:
    c_nums = list(c_vars.values()) if c_vars else []
    w_nums = list(w_vars.values()) if w_vars else []
    if not c_nums or not w_nums:
        print('—'); sys.exit()
    shared_nums = list(zip(c_nums[-min(len(c_nums),len(w_nums)):],
                           w_nums[-min(len(c_nums),len(w_nums)):]))
else:
    shared_nums = [(c_vars[k], w_vars[k]) for k in sorted(shared)]

ok = True
for cs, ws in shared_nums:
    c, w = float(cs), float(ws)
    if c == 0 and w == 0: continue
    if abs(c) < 1e-15 and abs(w) < 1e-15: continue
    if abs(c - w) / max(abs(c), abs(w), 1e-15) >= 1e-4:
        print(f'MISMATCH {cs} vs {ws}')
        ok = False; break
if ok: print('ok')
")
  fi

  # Ratios
  if [ "$t_c" != "—" ] && [ "$t_c" != "ERR" ] && [ "$t_w" != "—" ] && [ "$t_w" != "ERR" ]; then
    ratio_wc=$(python3 -c "print(f'{float(\"$t_w\")/float(\"$t_c\"):.1f}x')")
  fi
  if [ "$t_f" != "—" ] && [ "$t_f" != "ERR" ] && [ "$t_w" != "—" ] && [ "$t_w" != "ERR" ]; then
    ratio_wf=$(python3 -c "print(f'{float(\"$t_w\")/float(\"$t_f\"):.1f}x')")
  fi

  printf "%-22s  %8s  %8s  %8s  %8s  %8s  %s\n" \
    "$name" "$t_f" "$t_c" "$t_w" "$ratio_wc" "$ratio_wf" "$correct"
done

# Clean up temp files
rm -f "$BD/tmp_out.txt" "$BD/tmp_last_out.txt"
