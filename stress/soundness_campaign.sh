#!/bin/bash
# Copyright (c) 2026 Martin Rinard
# Checker-soundness campaign. For each program, corrupt a valid certificate's
# transformed program in behaviour-changing ways and confirm the checker REJECTS.
# Any ACCEPTed mutation is codegen'd + run; if its output differs from the correct
# program's, the checker accepted a non-refinement => SOUNDNESS HOLE.
# Usage: soundness_campaign.sh <dir-with-.w | --rand N>
set -uo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
CM="$ROOT/stress/run_to.sh 120 $ROOT/.lake/build/bin/certmutate"
RT="$ROOT/Compiler/runtime.c"
GEN="$ROOT/stress/csmith_gen.py"
D=$(mktemp -d); trap "rm -rf $D" EXIT

run_one() {  # $1 = .w file
  local w="$1" name; name=$(basename "$w" .w)
  rm -f "$D"/*.s
  local out; out=$($CM "$w" "$D" 2>&1)
  local acc rej
  acc=$(echo "$out" | grep -oE "accepted=[0-9]+" | cut -d= -f2)
  rej=$(echo "$out" | grep -oE "rejected=[0-9]+" | cut -d= -f2)
  TOTACC=$((TOTACC + ${acc:-0})); TOTREJ=$((TOTREJ + ${rej:-0}))
  [ "${acc:-0}" = "0" ] && return
  # there were ACCEPTs: get the correct output
  [ -f "$D/correct.s" ] || { echo "  $name: ${acc} ACCEPT but no correct.s"; return; }
  cc -o "$D/correct" "$D/correct.s" "$RT" 2>/dev/null || { echo "  $name: correct.s won't assemble"; return; }
  local O; O=$("$D/correct" 2>&1)
  while read -r line; do
    f=$(echo "$line" | grep -oE "accept_[a-z]+_[0-9]+\.s")
    [ -n "$f" ] || continue
    if cc -o "$D/m" "$D/$f" "$RT" 2>/dev/null; then
      Om=$("$D/m" 2>&1)
      if [ "$Om" != "$O" ]; then
        echo "  *** SOUNDNESS HOLE $name $f : correct=[$O] mutant=[$Om]"
        HOLES=$((HOLES+1)); cp "$w" "$ROOT/stress/sound_hole_${name}.w"
      fi
    fi
  done <<< "$(echo "$out" | grep '^ACCEPT')"
}

TOTACC=0; TOTREJ=0; HOLES=0; progs=0
if [ "${1:-}" = "--rand" ]; then
  N="${2:-50}"
  for s in $(seq 1 "$N"); do python3 "$GEN" "$s" "$D/r"; run_one "$D/r.w"; progs=$((progs+1)); done
else
  for w in "$1"/*.w; do [ -f "$w" ] || continue; run_one "$w"; progs=$((progs+1)); done
fi
echo ""
echo "=== Soundness campaign: $progs programs ==="
echo "  mutations rejected (checker caught): $TOTREJ"
echo "  mutations accepted:                  $TOTACC"
echo "  SOUNDNESS HOLES (accept + divergent): $HOLES"
