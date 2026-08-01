#!/bin/bash
# Copyright (c) 2026 Martin Rinard
# Compare WhileLang (optimized + unoptimized) vs clang -O0/-O1/-O2 and gfortran -O2
# on Livermore kernels. 5 runs each, take fastest (minimum) time.
set -euo pipefail

DIR="$(cd "$(dirname "$0")" && pwd)"
PROJ_DIR="$(cd "$DIR/../.." && pwd)"
BD="$DIR/build_opt_compare"
mkdir -p "$BD"

COMPILER="$PROJ_DIR/.lake/build/bin/compiler"
if [ ! -x "$COMPILER" ]; then
  echo "Building compiler..."
  (cd "$PROJ_DIR" && lake build compiler 2>&1 | tail -1)
fi

KERNELS=(
  k01_hydro k02_iccg k03_dot k04_banded k05_tridiag
  k06_recurrence k07_eos k08_adi k09_integrate k10_diff_predict
  k11_prefix_sum k12_first_diff k13_pic_2d k14_pic_1d k15_casual
  k16_monte_carlo k17_implicit_cond k18_hydro_2d k19_linear_recurrence k20_discrete_ord
  k21_matmul k22_planck k23_hydro_implicit k24_find_min
)

# Allow running a subset: ./run_opt_compare.sh k03_dot k07_eos
if [ $# -gt 0 ]; then
  KERNELS=("$@")
fi

NRUNS=${NRUNS:-1}

# ── compile all kernels ──────────────────────────────────────────
echo "Compiling kernels..."
for name in "${KERNELS[@]}"; do
  wfile="$DIR/${name}.w"
  cfile="$DIR/${name}.c"
  ffile="$DIR/${name}.f"

  # WhileLang optimized + unoptimized
  if [ -f "$wfile" ]; then
    "$COMPILER" "$wfile" -o "$BD/${name}_opt" 2>/dev/null || echo "  FAIL (WL opt): $name"
    "$COMPILER" "$wfile" -O0 -o "$BD/${name}_noopt" 2>/dev/null || echo "  FAIL (WL -O0): $name"
  fi

  # C at three optimization levels
  if [ -f "$cfile" ]; then
    cc -O0 -o "$BD/${name}_c0" "$cfile" 2>/dev/null || echo "  FAIL (C -O0): $name"
    cc -O1 -o "$BD/${name}_c1" "$cfile" 2>/dev/null || echo "  FAIL (C -O1): $name"
    cc -O2 -o "$BD/${name}_c2" "$cfile" 2>/dev/null || echo "  FAIL (C -O2): $name"
  fi

  # Fortran -O2
  if [ -f "$ffile" ] && command -v gfortran &>/dev/null; then
    gfortran -O2 -o "$BD/${name}_f2" "$ffile" 2>/dev/null || echo "  FAIL (F -O2): $name"
  fi
done
echo "Compilation done."
echo ""

# ── timing helpers ───────────────────────────────────────────────
time_run() {
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
  local bin="$1" best="" out=""
  for i in $(seq 1 $NRUNS); do
    local t
    t=$(time_run "$bin" 2>"$BD/tmp_out.txt") || { echo "ERR"; return; }
    [ -z "$out" ] && out=$(cat "$BD/tmp_out.txt")
    if [ -z "$best" ] || python3 -c "exit(0 if float('$t') < float('$best') else 1)"; then
      best="$t"
    fi
  done
  echo "$best"
  echo "$out" > "$BD/tmp_last_out.txt"
}

# ── run benchmarks ───────────────────────────────────────────────
printf "\n%-22s  %8s  %8s  %8s  %8s  %8s  %8s  %8s  %8s  %8s  %s\n" \
  "Kernel" "F -O2" "C -O0" "C -O1" "C -O2" "WL -O0" "WL opt" "WL/C-O0" "WL/C-O2" "WL/F-O2" "OK?"
printf "%-22s  %8s  %8s  %8s  %8s  %8s  %8s  %8s  %8s  %8s  %s\n" \
  "──────────────────" "──────" "──────" "──────" "──────" "──────" "──────" "──────" "──────" "──────" "───"

log_wl_c0=()
log_wl_c2=()
log_wl_f2=()

for name in "${KERNELS[@]}"; do
  t_f2="—"; t_c0="—"; t_c1="—"; t_c2="—"; t_noopt="—"; t_opt="—"
  ratio_c0="—"; ratio_c2="—"; ratio_f2="—"
  correct="—"
  out_opt=""; out_c2=""

  # Run Fortran -O2
  if [ -x "$BD/${name}_f2" ]; then
    t_f2=$(min_time "$BD/${name}_f2")
  fi

  # Run C variants
  for lvl in c0 c1 c2; do
    bin="$BD/${name}_${lvl}"
    if [ -x "$bin" ]; then
      eval "t_${lvl}=$(min_time "$bin")"
      [ "$lvl" = "c2" ] && out_c2=$(cat "$BD/tmp_last_out.txt" 2>/dev/null || true)
    fi
  done

  # Run WL variants
  if [ -x "$BD/${name}_noopt" ]; then
    t_noopt=$(min_time "$BD/${name}_noopt")
  fi
  if [ -x "$BD/${name}_opt" ]; then
    t_opt=$(min_time "$BD/${name}_opt")
    out_opt=$(cat "$BD/tmp_last_out.txt" 2>/dev/null || true)
  fi

  # Correctness: compare WL opt output to C -O2 output
  if [ "$t_opt" != "—" ] && [ "$t_opt" != "ERR" ] && \
     [ "$t_c2" != "—" ] && [ "$t_c2" != "ERR" ]; then
    correct=$(python3 -c "
import re, sys
# Match 'name[...] = val' (C), 'name(...) = val' (Fortran), or plain 'name = val'.
# Normalize keys by stripping index brackets so 'x[1]' and 'x(1)' compare.
num_re = r'[-+]?[0-9]*\.?[0-9]+(?:[eEdD][-+]?[0-9]+)?'
kv_re = re.compile(r'([A-Za-z_]\w*)\s*(?:\[[^\]]*\]|\([^)]*\))?\s*=\s*(' + num_re + r')')
float_tok_re = re.compile(
    r'[-+]?(?:\d+\.\d*|\.\d+|\d+)[eEdD][-+]?\d+|[-+]?\d+\.\d*|[-+]?\.\d+')
def parse(text):
    d = {}
    for line in text.strip().splitlines():
        s = line.strip().lower()
        if s.startswith(('elapsed', 'time')): continue
        for m in kv_re.finditer(line):
            d[m.group(1)] = m.group(2).replace('d', 'e').replace('D', 'E')
    return d
def float_tokens(text):
    out = []
    for line in text.strip().splitlines():
        s = line.strip().lower()
        if s.startswith(('elapsed', 'time')): continue
        for m in float_tok_re.finditer(line):
            tok = m.group(0).replace('d', 'e').replace('D', 'E')
            try:
                float(tok); out.append(tok)
            except ValueError:
                pass
    return out
def eq(va, vb):
    a, b = float(va), float(vb)
    if max(abs(a), abs(b)) < 1e-5: return True
    return abs(a - b) / max(abs(a), abs(b), 1e-15) < 1e-4
a, b = parse('''$out_opt'''), parse('''$out_c2''')
shared = set(a) & set(b)
if shared:
    ok = True
    for k in sorted(shared):
        if not eq(a[k], b[k]):
            print(f'MISMATCH {k}: {a[k]} vs {b[k]}'); ok = False; break
    if ok: print('ok')
else:
    # Fallback: compare first float-shaped numeric token from each output.
    fa, fb = float_tokens('''$out_opt'''), float_tokens('''$out_c2''')
    if not fa or not fb:
        print('—')
    elif eq(fa[0], fb[0]):
        print('ok')
    else:
        print(f'MISMATCH {fa[0]} vs {fb[0]}')
")
  fi

  # Ratios: WL-opt vs C-O0, C-O2, F-O2
  for pair in "c0:t_c0" "c2:t_c2" "f2:t_f2"; do
    tag="${pair%%:*}"; var="${pair##*:}"
    eval "tv=\$$var"
    if [ "$t_opt" != "—" ] && [ "$t_opt" != "ERR" ] && \
       [ "$tv" != "—" ] && [ "$tv" != "ERR" ]; then
      eval "ratio_${tag}=$(python3 -c "
import math
t_w, t_c = float('$t_opt'), float('$tv')
if t_c > 0:
    r = t_w / t_c
    print(f'{r:.1f}x')
    print(f'{math.log(r)}', file=open('$BD/tmp_lr_${tag}.txt','w'))
")"
      if [ -f "$BD/tmp_lr_${tag}.txt" ]; then
        eval "log_wl_${tag}+=(\"\$(cat '$BD/tmp_lr_${tag}.txt')\")"
      fi
    fi
  done

  printf "%-22s  %8s  %8s  %8s  %8s  %8s  %8s  %8s  %8s  %8s  %s\n" \
    "$name" "$t_f2" "$t_c0" "$t_c1" "$t_c2" "$t_noopt" "$t_opt" "$ratio_c0" "$ratio_c2" "$ratio_f2" "$correct"
done

# ── geometric means ──────────────────────────────────────────────
printf "\n"
for pair in "c0:WL-opt/C-O0" "c2:WL-opt/C-O2" "f2:WL-opt/F-O2"; do
  tag="${pair%%:*}"; label="${pair##*:}"
  eval "logs=(\"\${log_wl_${tag}[@]}\")" 2>/dev/null || logs=()
  if [ ${#logs[@]} -gt 0 ]; then
    gm=$(python3 -c "
import math
logs = [$(IFS=,; echo "${logs[*]}")]
print(f'{math.exp(sum(logs)/len(logs)):.2f}x')
")
    printf "  Geometric mean %-16s  %s\n" "$label" "$gm"
  fi
done

rm -f "$BD"/tmp_out.txt "$BD"/tmp_last_out.txt "$BD"/tmp_lr_*.txt
