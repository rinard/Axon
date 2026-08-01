#!/usr/bin/env python3
# Copyright (c) 2026 Martin Rinard
"""T4 differential runner: for each seed, generate matched .w + .c (t4_gen.py), compile the
.w with the verified compiler and the .c, run both, and compare token-wise — **ints exact,
floats TOLERANT**. The float tolerance is deliberate: FMA fusion and reassociation produce
*correct* results that differ in the bottom bits, so a bit-exact float compare would flag
non-bugs. A gross float divergence (wrong instruction / control flow) or any int mismatch is a
candidate miscompile (RQ1b).

Usage: t4_run.py [N]
"""
import sys, os, subprocess, tempfile, math

def tok_eq(a, b, abs_tol=1e-4, rel_tol=1e-7):
    if a == b: return True
    try: fa, fb = float(a), float(b)
    except ValueError: return False
    if math.isnan(fa) and math.isnan(fb): return True
    if math.isinf(fa) or math.isinf(fb): return fa == fb
    return abs(fa - fb) <= max(abs_tol, rel_tol * max(abs(fa), abs(fb)))

def out_eq(ow, oc):
    ta, tb = ow.split(), oc.split()
    return len(ta) == len(tb) and all(tok_eq(a, b) for a, b in zip(ta, tb))
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
COMPILER = os.path.join(ROOT, ".lake/build/bin/compiler")
GEN = os.path.join(ROOT, "stress/t4_gen.py")

def run(cmd, timeout=30):
    try:
        p = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
        return p.returncode, p.stdout, p.stderr
    except subprocess.TimeoutExpired:
        return -1, "", "TIMEOUT"

def main():
    base = int(os.environ.get('SEED_BASE','0'))
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 50
    if not os.path.exists(COMPILER):
        print(f"compiler missing: {COMPILER} — run `lake build compiler`"); sys.exit(2)
    d = tempfile.mkdtemp(prefix="t4_")
    div = comp_err = ran = 0
    for seed in range(base, base + N):
        stem = os.path.join(d, f"t4_{seed}")
        subprocess.run([sys.executable, GEN, str(seed), stem], check=True)
        rcw, _, sew = run([COMPILER, stem + ".w", "-o", stem + ".wbin"])
        if rcw != 0:
            comp_err += 1; print(f"WHILE-COMPILE-FAIL seed={seed}: {sew.strip()[:200]}"); continue
        rcc, _, sec = run(["cc", "-O2", "-w",
                           "-o", stem + ".cbin", stem + ".c"])
        if rcc != 0:
            comp_err += 1; print(f"C-COMPILE-FAIL seed={seed}: {sec.strip()[:200]}"); continue
        _, ow, _ = run([stem + ".wbin"]); _, oc, _ = run([stem + ".cbin"]); ran += 1
        if not out_eq(ow, oc):
            div += 1
            print(f"DIVERGENCE seed={seed}:\n  while: {ow.strip()[:300]!r}\n  c    : {oc.strip()[:300]!r}")
            print(f"  (.w/.c kept at {stem}.w / {stem}.c)")
    print(f"=== T4: {ran} ran, {div} divergences, {comp_err} compile-fails ===")

if __name__ == "__main__":
    main()
