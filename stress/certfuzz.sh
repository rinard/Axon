#!/bin/bash
# Copyright (c) 2026 Martin Rinard
# Certificate-failure-focused fuzzing campaign. For each generated program, run
# `certaudit` and catalogue every certificate REJECTION by (pass, sub-checks).
# Novel (pass, sub-check) combinations get the program saved for investigation.
# Also does a lighter differential (miscompile) + soundness check periodically.
# Logs to stress/certfuzz.log; combo tally in stress/certfuzz_combos.txt.
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
C="$ROOT/.lake/build/bin/compiler"
CA="$ROOT/.lake/build/bin/certaudit"
CM="$ROOT/.lake/build/bin/certmutate"
GEN="$ROOT/stress/csmith_gen.py"
RT="$ROOT/Compiler/runtime.c"
LOG="$ROOT/stress/certfuzz.log"
COMBOS="$ROOT/stress/certfuzz_combos.txt"
SEEN="$ROOT/stress/certfuzz_seen.txt"
ALL="$ROOT/stress/certfuzz_all.txt"
D=$(mktemp -d); trap "rm -rf $D" EXIT
MAXSEED="${1:-1000000}"; TMO="${2:-20}"
: > "$COMBOS"; : > "$SEEN"; : > "$ALL"
run_to() { local s=$1; shift; "$@" & local p=$!
  ( sleep "$s"; kill -9 $p 2>/dev/null ) </dev/null >/dev/null 2>&1 & local t=$!
  wait $p 2>/dev/null; local rc=$?; kill $t 2>/dev/null; wait $t 2>/dev/null; return $rc; }
log() { echo "[$(date '+%H:%M:%S')] $*" | tee -a "$LOG"; }

log "=== certfuzz start (maxseed=$MAXSEED timeout=${TMO}s) ==="
progs=0; rejprogs=0; totrej=0; novel=0; miscomp=0; holes=0
s=0
while [ "$s" -lt "$MAXSEED" ]; do
  s=$((s+1))
  # mostly loop-capable medium programs (LICM/div coverage); 1/4 boundary
  mode=""; [ $((s % 4)) -eq 0 ] && mode="boundary"
  GENBUDGET=26 GENSTMT_LO=5 GENSTMT_HI=10 python3 "$GEN" "$s" "$D/p" $mode 2>/dev/null || continue
  out=$(run_to "$TMO" "$CA" "$D/p.w" 2>/dev/null)
  [ -z "$out" ] && continue   # timeout/parse-fail
  progs=$((progs+1))
  # parse REJECTED lines -> "Pass:[subchecks]"
  rejected=$(echo "$out" | grep "REJECTED" | sed -E 's/.*for ([A-Za-z]+): (\[[^]]*\]).*/\1:\2/' | sort -u)
  if [ -n "$rejected" ]; then
    rejprogs=$((rejprogs+1))
    while read -r combo; do
      [ -z "$combo" ] && continue
      totrej=$((totrej+1)); echo "$combo" >> "$ALL"
      if ! grep -qxF "$combo" "$SEEN"; then
        echo "$combo" >> "$SEEN"; novel=$((novel+1))
        log "NOVEL combo: $combo  (seed=$s)"
        safe=$(echo "$combo" | tr -c 'A-Za-z0-9' '_')
        cp "$D/p.w" "$ROOT/stress/certfuzz_${safe}_$s.w"
      fi
    done <<< "$rejected"
  fi
  # lighter differential miscompile check every 6th program
  if [ $((s % 6)) -eq 0 ]; then
    if run_to "$TMO" "$C" "$D/p.w" -o "$D/w" 2>/dev/null; then
      wout=$(run_to "$TMO" "$D/w" 2>&1); wrc=$?
      # Only compare when BOTH the While binary AND the C reference build and run
      # cleanly. The old `|| cout="$wout"` set cout=wout whenever the C ref failed to
      # build or exited non-zero, which made the `!=` guard unfalsifiable — nulling the
      # oracle on exactly the inputs the reference could not run.
      if cc -O2 -w -o "$D/c" "$D/p.c" 2>/dev/null; then
        cout=$("$D/c" 2>&1); crc=$?
        if [ "$wrc" -eq 0 ] && [ "$crc" -eq 0 ] && [ "$wout" != "$cout" ]; then
          miscomp=$((miscomp+1)); log "*** MISCOMPILE seed=$s W=[$wout] C=[$cout]"; cp "$D/p.w" "$ROOT/stress/certfuzz_miscompile_$s.w"; cp "$D/p.c" "$ROOT/stress/certfuzz_miscompile_$s.c"
        fi
      fi
    fi
  fi
  # soundness mutation every 25th
  if [ $((s % 25)) -eq 0 ]; then
    rm -f "$D"/*.s; mout=$(run_to "$TMO" "$CM" "$D/p.w" "$D" 2>/dev/null)
    if echo "$mout" | grep -q '^ACCEPT'; then
      run_to "$TMO" "$C" "$D/p.w" -o "$D/cw" 2>/dev/null && O=$("$D/cw" 2>&1) || O="__x__"
      while read -r f; do [ -f "$D/$f" ] || continue
        cc -o "$D/mm" "$D/$f" "$RT" 2>/dev/null || continue; Om=$("$D/mm" 2>&1)
        [ "$Om" != "$O" ] && [ "$O" != "__x__" ] && { holes=$((holes+1)); log "*** SOUNDNESS-HOLE seed=$s $f correct=[$O] mutant=[$Om]"; cp "$D/p.w" "$ROOT/stress/certfuzz_hole_$s.w"; }
      done <<< "$(echo "$mout" | grep -oE 'accept_[a-z]+_[0-9]+\.s')"
    fi
  fi
  if [ $((s % 50)) -eq 0 ]; then
    { echo "=== combo tally @ seed $s ==="; sort "$ALL" | uniq -c | sort -rn; } > "$COMBOS"
    log "progress: seed=$s audited=$progs reject-progs=$rejprogs total-rej=$totrej novel-combos=$novel miscompile=$miscomp holes=$holes"
  fi
done
