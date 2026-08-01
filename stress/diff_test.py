#!/usr/bin/env python3
# Copyright (c) 2026 Martin Rinard
"""3-way differential test harness for the Credible Compilation compiler.

For each test basename T in the given directory, expects T.w (While source) and
optionally T.c (C reference) and T.f (Fortran reference). Compiles & runs all
available versions, then compares stdout token-by-token with numeric awareness
(ints compared exactly, floats within tolerance).

Reports: PASS / MISCOMPILE (outputs differ) / COMPILE-FAIL / RUNTIME-FAIL / CRASH.

Usage: diff_test.py <dir> [--tol REL] [--filter SUBSTR] [--timeout SEC]
"""
import os, sys, subprocess, tempfile, shutil, re, argparse, math

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
COMPILER = os.path.join(ROOT, ".lake/build/bin/compiler")
RUNTIME = os.path.join(ROOT, "Compiler/runtime.c")

FLOAT_RE = re.compile(r'^[-+]?(\d+\.\d*|\.\d+|\d+)([eE][-+]?\d+)?$')

def tokenize(s):
    return s.split()

def tok_eq(a, b, rel_tol, abs_tol):
    if a == b:
        return True
    # Numeric comparison
    fa, fb = _to_float(a), _to_float(b)
    if fa is None or fb is None:
        return False
    if math.isnan(fa) and math.isnan(fb):
        return True
    if math.isinf(fa) or math.isinf(fb):
        return fa == fb
    return abs(fa - fb) <= max(abs_tol, rel_tol * max(abs(fa), abs(fb)))

def _to_float(t):
    # strip trailing punctuation a Fortran/C print might add (rare)
    if FLOAT_RE.match(t):
        try:
            return float(t)
        except ValueError:
            return None
    # also accept Fortran D-exponent
    t2 = t.replace('D', 'E').replace('d', 'e')
    if FLOAT_RE.match(t2):
        try:
            return float(t2)
        except ValueError:
            return None
    return None

def outputs_match(o1, o2, rel_tol, abs_tol):
    t1, t2 = tokenize(o1), tokenize(o2)
    if len(t1) != len(t2):
        return False, f"token count {len(t1)} vs {len(t2)}"
    for i, (a, b) in enumerate(zip(t1, t2)):
        if not tok_eq(a, b, rel_tol, abs_tol):
            return False, f"token {i}: {a!r} vs {b!r}"
    return True, ""

def run(cmd, timeout, stdin_inherit=False):
    try:
        p = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
        return p.returncode, p.stdout, p.stderr
    except subprocess.TimeoutExpired:
        return -999, "", "TIMEOUT"
    except Exception as e:
        return -998, "", str(e)

def compile_while(src, out, timeout):
    rc, so, se = run([COMPILER, src, "-o", out], timeout)
    return rc, se

def compile_c(src, out, timeout):
    rc, so, se = run(["cc", "-O2", "-w", "-o", out, src], timeout)
    return rc, se

def compile_f(src, out, timeout):
    rc, so, se = run(["gfortran", "-O2", "-w", "-o", out, src], timeout)
    return rc, se

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("dir")
    ap.add_argument("--tol", type=float, default=1e-6)
    ap.add_argument("--abstol", type=float, default=1e-9)
    ap.add_argument("--filter", default="")
    ap.add_argument("--timeout", type=float, default=30.0)
    ap.add_argument("-v", action="store_true")
    args = ap.parse_args()

    d = args.dir
    bases = sorted(set(f[:-2] for f in os.listdir(d) if f.endswith(".w")))
    bases = [b for b in bases if args.filter in b]

    tmp = tempfile.mkdtemp()
    results = {"PASS":0, "MISCOMPILE":0, "WHILE-FAIL":0, "C-FAIL":0, "F-FAIL":0,
               "WHILE-RUN":0, "TIMEOUT":0, "NO-REF":0}
    details = []
    try:
        for b in bases:
            wsrc = os.path.join(d, b + ".w")
            csrc = os.path.join(d, b + ".c")
            fsrc = os.path.join(d, b + ".f")
            wbin = os.path.join(tmp, b + "_w")
            cbin = os.path.join(tmp, b + "_c")
            fbin = os.path.join(tmp, b + "_f")

            rc, se = compile_while(wsrc, wbin, args.timeout)
            if rc != 0:
                results["WHILE-FAIL"] += 1
                details.append((b, "WHILE-FAIL", se.strip().split("\n")[-1][:200] if se.strip() else f"rc={rc}"))
                print(f"WHILE-FAIL  {b}  {se.strip().splitlines()[-1][:120] if se.strip() else rc}")
                continue
            wrc, wout, wse = run([wbin], args.timeout)
            if wrc == -999:
                results["TIMEOUT"] += 1; details.append((b,"TIMEOUT","while")); print(f"TIMEOUT     {b}"); continue
            if wrc != 0:
                results["WHILE-RUN"] += 1
                details.append((b, "WHILE-RUN", f"exit={wrc}"))
                print(f"WHILE-RUN   {b}  exit={wrc} {wout.strip()[:80]}")
                continue

            refs = []
            if os.path.exists(csrc):
                rc, se = compile_c(csrc, cbin, args.timeout)
                if rc != 0:
                    results["C-FAIL"] += 1; details.append((b,"C-FAIL",se.strip()[:160]))
                    print(f"C-FAIL      {b}  {se.strip().splitlines()[-1][:100] if se.strip() else rc}");
                else:
                    crc, cout, cse = run([cbin], args.timeout)
                    refs.append(("C", cout))
            if os.path.exists(fsrc):
                rc, se = compile_f(fsrc, fbin, args.timeout)
                if rc != 0:
                    results["F-FAIL"] += 1; details.append((b,"F-FAIL",se.strip()[:160]))
                    print(f"F-FAIL      {b}  {se.strip().splitlines()[-1][:100] if se.strip() else rc}")
                else:
                    frc, fout, fse = run([fbin], args.timeout)
                    refs.append(("F", fout))

            if not refs:
                results["NO-REF"] += 1
                print(f"NO-REF      {b}  (while ran ok, output: {wout.strip()[:60]})")
                continue

            mismatch = None
            for name, rout in refs:
                ok, why = outputs_match(wout, rout, args.tol, args.abstol)
                if not ok:
                    mismatch = (name, why, rout)
                    break
            if mismatch:
                results["MISCOMPILE"] += 1
                name, why, rout = mismatch
                details.append((b, "MISCOMPILE", f"vs {name}: {why}"))
                print(f"MISCOMPILE  {b}  vs {name}: {why}")
                if args.v:
                    print(f"   while: {wout.strip()[:120]}")
                    print(f"   {name}    : {rout.strip()[:120]}")
            else:
                results["PASS"] += 1
                if args.v:
                    print(f"PASS        {b}  ({'+'.join(n for n,_ in refs)})")
    finally:
        shutil.rmtree(tmp, ignore_errors=True)

    print("\n=== SUMMARY ===")
    for k, v in results.items():
        if v: print(f"  {k}: {v}")
    nbad = sum(results[k] for k in ("MISCOMPILE","WHILE-FAIL","C-FAIL","F-FAIL","WHILE-RUN"))
    print(f"  total tests: {len(bases)}")
    sys.exit(1 if results["MISCOMPILE"] else 0)

if __name__ == "__main__":
    main()
