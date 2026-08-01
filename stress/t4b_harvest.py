#!/usr/bin/env python3
# Copyright (c) 2026 Martin Rinard
"""T4b: harvest certificate-check failures (RQ4/RQ5). Generates T4 programs (t4_gen.py, int+float)
and runs `certaudit` on each, collecting REJECTED pass-certificate lines for post-hoc adjudication
(RQ4a too-strict vs RQ4b too-loose; RQ5a/5b). Usage: t4b_harvest.py [N]"""
import sys, os, subprocess, tempfile, re
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CERTAUDIT = os.path.join(ROOT, ".lake/build/bin/certaudit")
GEN = os.path.join(ROOT, "stress/t4_gen.py")

def main():
    base = int(os.environ.get('SEED_BASE','0'))
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 50
    if not os.path.exists(CERTAUDIT):
        print("build certaudit first: lake build certaudit"); sys.exit(2)
    d = tempfile.mkdtemp(prefix="t4b_")
    progs = rej = 0; by_pass = {}
    for seed in range(base, base + N):
        stem = os.path.join(d, f"t4b_{seed}")
        subprocess.run([sys.executable, GEN, str(seed), stem], check=True)
        try:
            p = subprocess.run([CERTAUDIT, stem + ".w"], capture_output=True, text=True, timeout=120)
        except subprocess.TimeoutExpired:
            print(f"TIMEOUT seed={seed}"); continue
        progs += 1
        for line in p.stdout.splitlines():
            m = re.search(r"(\w+): REJECTED", line)
            if m:
                rej += 1; by_pass[m.group(1)] = by_pass.get(m.group(1), 0) + 1
                print(f"REJECTED seed={seed}: {line.strip()}  (.w at {stem}.w)")
    print(f"=== T4b: {progs} programs, {rej} cert rejections; by pass: {by_pass} ===")

if __name__ == "__main__":
    main()
