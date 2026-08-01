#!/usr/bin/env python3
# Copyright (c) 2026 Martin Rinard
"""Csmith-style random While-program generator. Emits a random well-formed While
program AND a matching C reference from one shared random AST, so they are
equivalent by construction (no reference-authoring bugs). Avoids UB that would
desync the backends:
  - division/modulo: divisor forced nonzero -> `((e % 7) + 8)` (While traps on /0)
  - shifts: amount masked to 0..63           -> `(e & 63)`     (UB above 63)
  - +,-,*: two's-complement wrap; C uses uint64 casts to get defined wrap
Scalars only (clean differential signal). While uses `;` as a statement SEPARATOR;
C uses it as a terminator — rendered separately.

Usage: csmith_gen.py <seed> <out_stem>   # writes <out_stem>.w and <out_stem>.c
"""
import sys, random, os

NVARS = 6
MAXDEPTH = 4
# Overnight throughput: cap program size via env to avoid the O(n^2.5) compile wall.
BUDGET0 = int(os.environ.get("GENBUDGET", "40"))
NSTMT_LO = int(os.environ.get("GENSTMT_LO", "6"))
NSTMT_HI = int(os.environ.get("GENSTMT_HI", "14"))

def windent(s, n=2):
    pad = " " * n
    return "\n".join(pad + l for l in s.split("\n"))

# Boundary / corner int64 values (#4): extremes that stress wrap/shift/div edges.
BOUNDARY = [-9223372036854775808, 9223372036854775807, 0, -1, 1, 2, -2,
            4294967296, -4294967296, 9223372036854775806, -9223372036854775807,
            255, 256, 65535, 65536, 2147483647, -2147483648]

class G:
    def __init__(self, seed, boundary=False):
        self.r = random.Random(seed)
        self.vars = [f"v{i}" for i in range(NVARS)]
        self.loopc = 0
        self.extra = []
        # Swarm (#3): each program enables a random subset of features, so some
        # programs are e.g. shift-only or loop-free — exercising feature
        # interactions a uniform generator dilutes.
        allops = ["+","-","*","&","|","^","<<",">>","/","%"]
        k = self.r.randint(3, len(allops))
        self.ops = self.r.sample(allops, k)
        if "+" not in self.ops: self.ops.append("+")
        self.allow_loops = self.r.random() < 0.7
        self.allow_if = self.r.random() < 0.85
        self.boundary = boundary
        # Arrays (#: exercises BoundsOpt / bounds_preservation cert sub-check).
        # Power-of-two size so an index can be masked in-bounds with `& (SZ-1)`
        # (no signed-modulo-of-negative hazard); reads/writes stay defined in both
        # backends, and a checksum loop `A[i] for i<SZ` is the in-bounds pattern
        # BoundsOpt tries to prove.
        self.asz = 16
        self.allow_arr = self.r.random() < 0.6
        self.arrs = (["A0", "A1"][:self.r.randint(1, 2)]) if self.allow_arr else []

    def lit(self):
        if self.boundary and self.r.random() < 0.7:
            n = self.r.choice(BOUNDARY)
        else:
            n = self.r.randint(-50, 50)
        w = f"({n})" if n < 0 else str(n)
        # INT64_MIN cannot be written as a literal in C (magnitude overflows).
        c = "((int64_t)(-9223372036854775807LL - 1))" if n == -9223372036854775808 else f"((int64_t){n}LL)"
        return w, c

    # ---- expressions: (while_str, c_str) ----
    def aidx(self, depth):
        # an index expression masked into [0, asz) via `& (asz-1)`
        iw, ic = self.expr(depth)
        m = self.asz - 1
        return f"(({iw}) & {m})", f"(({ic}) & {m})"

    def expr(self, depth):
        r = self.r
        if depth <= 0 or r.random() < 0.35:
            if self.arrs and r.random() < 0.3:
                a = r.choice(self.arrs); iw, ic = self.aidx(0)
                return f"{a}[{iw}]", f"{a}[{ic}]"
            if r.random() < 0.6:
                v = r.choice(self.vars); return v, v
            return self.lit()
        op = r.choice(self.ops)
        aw, ac = self.expr(depth-1)
        bw, bc = self.expr(depth-1)
        if op in ("+","-","*"):
            return f"({aw} {op} {bw})", f"((int64_t)((uint64_t){ac} {op} (uint64_t){bc}))"
        if op in ("&","|","^"):
            return f"({aw} {op} {bw})", f"({ac} {op} {bc})"
        if op == "<<":
            # C left-shift of a negative/overflowing value is UB; do it unsigned to
            # match While's wrapping BitVec shl.
            return f"({aw} << ({bw} & 63))", f"((int64_t)((uint64_t){ac} << ({bc} & 63)))"
        if op == ">>":
            # arithmetic right shift (matches While's sshiftRight and clang int64_t >>)
            return f"({aw} >> ({bw} & 63))", f"({ac} >> ({bc} & 63))"
        # / or %: divisor forced to 2..14
        dw = f"((({bw} % 7) + 8))"; dc = f"((({bc} % 7) + 8))"
        return f"({aw} {op} {dw})", f"({ac} {op} {dc})"

    def cond(self, depth):
        r = self.r
        aw, ac = self.expr(depth); bw, bc = self.expr(depth)
        op = r.choice(["<","<=",">",">=","==","!="])
        bw_, bc_ = f"({aw} {op} {bw})", f"({ac} {op} {bc})"
        if depth > 1 and r.random() < 0.3:
            cw, cc = self.cond(depth-1)
            lop = r.choice(["&&","||"])
            return f"({bw_} {lop} {cw})", f"({bc_} {lop} {cc})"
        if r.random() < 0.15:
            return f"(!{bw_})", f"(!{bc_})"
        return bw_, bc_

    # ---- statements: (while_str, c_str). while_str has NO trailing ';'. ----
    def stmt(self, depth, budget):
        r = self.r
        ch = r.random()
        leaf = (depth <= 0 or budget[0] <= 0 or ch < 0.55
                or (not self.allow_if and not self.allow_loops))
        if leaf:
            budget[0] -= 1
            if self.arrs and r.random() < 0.35:  # array store
                a = r.choice(self.arrs); iw, ic = self.aidx(1); ew, ec = self.expr(MAXDEPTH)
                return f"{a}[{iw}] := {ew}", f"{a}[{ic}] = {ec};"
            v = r.choice(self.vars); ew, ec = self.expr(MAXDEPTH)
            return f"{v} := {ew}", f"{v} = {ec};"
        budget[0] -= 1
        if self.allow_if and (not self.allow_loops or ch < 0.78):  # if/else
            cw, cc = self.cond(2)
            tw, tc = self.block(depth-1, budget)
            ew, ec = self.block(depth-1, budget)
            w = f"if ({cw}) {{\n{windent(tw)}\n}} else {{\n{windent(ew)}\n}}"
            c = f"if ({cc}) {{\n{windent(tc)}\n}} else {{\n{windent(ec)}\n}}"
            return w, c
        # bounded while loop (counter is a fresh var; loop runs a fixed # of times)
        self.loopc += 1
        i = f"li{self.loopc}"; self.extra.append(i)
        cnt = r.randint(2, 8)
        bw, bc = self.block(depth-1, budget)
        w = (f"{i} := 0;\nwhile ({i} < {cnt}) {{\n{windent(bw)};\n  {i} := {i} + 1\n}}")
        c = (f"{i} = 0;\nwhile ({i} < {cnt}) {{\n{windent(bc)}\n  {i} = {i} + 1;\n}}")
        return w, c

    def block(self, depth, budget):
        n = self.r.randint(1, 3)
        ws, cs = [], []
        for _ in range(n):
            if budget[0] <= 0: break
            w, c = self.stmt(depth, budget); ws.append(w); cs.append(c)
        if not ws: ws, cs = ["skip"], [";"]
        return ";\n".join(ws), "\n".join(cs)

    def gen(self):
        budget = [BUDGET0]
        ws, cs = [], []
        for _ in range(self.r.randint(NSTMT_LO, NSTMT_HI)):
            if budget[0] <= 0: break
            w, c = self.stmt(3, budget); ws.append(w); cs.append(c)
        inits = [self.r.randint(-20, 20) for _ in self.vars]
        winit = [f"{v} := {n}" for v, n in zip(self.vars, inits)]
        cinit = [f"{v} = {n};" for v, n in zip(self.vars, inits)]
        # Checksum each array over an in-bounds loop (drives BoundsOpt elision),
        # appended to the statement stream so the array state is observable.
        cks_w, cks_c = [], []
        for ai, a in enumerate(self.arrs):
            ck = f"cks{ai}"; ix = f"ai{ai}"; self.extra += [ck, ix]
            cks_w.append(f"{ck} := 0;\n{ix} := 0;\nwhile ({ix} < {self.asz}) {{\n"
                         f"  {ck} := {ck} + {a}[{ix}];\n  {ix} := {ix} + 1\n}}")
            cks_c.append(f"{ck} = 0;\n{ix} = 0;\nwhile ({ix} < {self.asz}) {{\n"
                         f"  {ck} = {ck} + {a}[{ix}];\n  {ix} = {ix} + 1;\n}}")
        ws = ws + cks_w; cs = cs + cks_c

        wpr, cpr = [], []
        for v in self.vars:
            wpr += [f'printString("{v}=")', f"printInt({v})", 'printString(" ")']
            cpr.append(f'printf("{v}=%ld ",(long)(int64_t){v});')
        for ai, _ in enumerate(self.arrs):
            wpr += [f'printString("cks{ai}=")', f"printInt(cks{ai})", 'printString(" ")']
            cpr.append(f'printf("cks{ai}=%ld ",(long)(int64_t)cks{ai});')
        wpr.append('printString("\\n")'); cpr.append('printf("\\n");')

        allv = self.vars + self.extra
        wdecl = "var " + ", ".join(f"{v} : int" for v in allv) + ";"
        warr = ("array " + ", ".join(f"{a}[{self.asz}] : int" for a in self.arrs) + ";\n") if self.arrs else ""
        wprog = wdecl + "\n" + warr + ";\n".join(winit + ws + wpr) + "\n"
        cdecl = "  int64_t " + ", ".join(f"{v}=0" for v in allv) + ";"
        carr = "".join(f"  int64_t {a}[{self.asz}]={{0}};\n" for a in self.arrs)
        cbody = carr + "\n".join("  " + l for blk in (cinit + cs + cpr) for l in blk.split("\n"))
        cprog = ("#include <stdio.h>\n#include <stdint.h>\nint main(void){\n"
                 + cdecl + "\n" + cbody + "\n  return 0;\n}\n")
        return wprog, cprog

if __name__ == "__main__":
    seed = int(sys.argv[1]); stem = sys.argv[2]
    boundary = len(sys.argv) > 3 and sys.argv[3] == "boundary"
    g = G(seed, boundary=boundary); w, c = g.gen()
    open(stem + ".w", "w").write(w)
    open(stem + ".c", "w").write(c)
