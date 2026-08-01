#!/bin/bash
# Copyright (c) 2026 Martin Rinard
# Run the SPE exhaustive operator×boundary-operand enumeration in chunks (each a
# small, fast-compiling program), diffing While vs C. Pinpoints any bad combo.
set -uo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
C="$ROOT/stress/run_to.sh 120 $ROOT/.lake/build/bin/compiler"; GEN="$ROOT/stress/spe_gen.py"
NCH="${1:-16}"; D=$(mktemp -d); trap "rm -rf $D" EXIT
ok=0; bad=0
for k in $(seq 0 $((NCH-1))); do
  python3 "$GEN" "$D/s" "$k" "$NCH"
  $C "$D/s.w" -o "$D/w" 2>/dev/null || { echo "chunk $k WHILE-FAIL"; continue; }
  w=$("$D/w" 2>&1)
  cc -O2 -w -o "$D/c" "$D/s.c" 2>/dev/null || { echo "chunk $k C-FAIL"; continue; }
  c=$("$D/c" 2>&1)
  if [ "$w" = "$c" ]; then ok=$((ok+1)); else
    bad=$((bad+1)); echo "chunk $k DIVERGENCE"
    python3 - "$w" "$c" <<'PY'
import sys
w=sys.argv[1].split(); c=sys.argv[2].split()
for i,(a,b) in enumerate(zip(w,c)):
    if a!=b: print(f"  first diff at result #{i}: W={a} C={b}"); break
PY
    cp "$D/s.w" "$ROOT/stress/spe_fail_$k.w"
  fi
done
echo "=== SPE: $ok chunks match, $bad differ ==="
