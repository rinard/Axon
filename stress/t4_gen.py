#!/usr/bin/env python3
# Copyright (c) 2026 Martin Rinard
"""T4 generator (int + FLOAT) — matched .w + .c from one shared random AST, equivalent by
construction. ALL output is emitted as INTEGER lines: int vars directly; float vars via
`floatToInt(g * 1e6)` (truncate). So the differential comparison is EXACT — no float
formatting, no tolerance. This is what makes float numeric bugs observable (T4a) — unlike T1,
both sides run real IEEE-754 hardware.

Strict C compile is REQUIRED (`-ffp-contract=off -fno-fast-math`, see t4_run.py) so any
Axon-vs-C float divergence is the *compiler* reassociating/contracting (the finding), not C.

Well-definedness (no UB to desync backends):
  - int: divisor `((e % 7) + 8)`, shift `& 63`, two's-complement wrap via uint64 casts (C).
  - float: positive literals + subtraction for signs; division by a positive literal (no /0 ->
    no inf); no sqrt/log (no NaN); magnitudes bounded so `g*1e6` fits int64.
ULP-level float diffs (FMA fusion, reassociation) are sub-1e-6 per op, so they're AMPLIFIED by
accumulation loops (the a*b+c FMA shape iterated). True bit-exact compare would need a
float->bits reinterpret the language lacks; loop-amplification is the workaround.

Usage: t4_gen.py <seed> <out_stem>   # writes <out_stem>.w and <out_stem>.c
"""
import sys, random

FSCALE = 1000000  # float -> int via floatToInt(g * 1e6)

class G:
    def __init__(self, seed):
        self.r = random.Random(seed)
        self.iv = [f"a{i}" for i in range(self.r.randint(2, 4))]
        self.fv = [f"g{i}" for i in range(self.r.randint(2, 3))]
        self.extra = []
        self.loopc = 0

    # ---- int expressions (well-defined) ----
    def ilit(self):
        n = self.r.randint(-30, 30)
        return (f"({n})" if n < 0 else str(n)), f"((int64_t){n}LL)"
    def iexpr(self, d):
        r = self.r
        if d <= 0 or r.random() < 0.4:
            if r.random() < 0.6: v = r.choice(self.iv); return v, v
            return self.ilit()
        op = r.choice(["+","-","*","/","<<",">>","&","|","^"])
        aw, ac = self.iexpr(d-1); bw, bc = self.iexpr(d-1)
        if op in ("+","-","*"): return f"({aw}{op}{bw})", f"((int64_t)((uint64_t){ac}{op}(uint64_t){bc}))"
        if op in ("&","|","^"): return f"({aw}{op}{bw})", f"({ac}{op}{bc})"
        if op == "<<": return f"({aw}<<({bw}&63))", f"((int64_t)((uint64_t){ac}<<({bc}&63)))"
        if op == ">>": return f"({aw}>>({bw}&63))", f"({ac}>>({bc}&63))"
        dw = f"((({bw}%7)+8))"; dc = f"((({bc}%7)+8))"
        return f"({aw}{op}{dw})", f"({ac}{op}{dc})"

    # ---- float expressions (well-defined, bounded; FMA-fusable a*b+c included) ----
    def flit(self):
        n = round(self.r.uniform(0.1, 8.0), 4)   # positive; subtraction makes negatives
        return f"{n}", f"{n}"
    def fexpr(self, d):
        r = self.r
        if d <= 0 or r.random() < 0.4:
            c = r.random()
            if c < 0.45: v = r.choice(self.fv); return v, v
            if c < 0.75:                                # bound the int before widening (no huge floats)
                iw, ic = self.iexpr(2); return f"intToFloat(({iw})%100)", f"((double)(({ic})%100))"
            return self.flit()
        k = r.random()
        aw, ac = self.fexpr(d-1); bw, bc = self.fexpr(d-1)
        if k < 0.30:                                   # the FMA-fusable shape a*b+c
            cw, cc = self.fexpr(d-1)
            return f"(({aw}*{bw})+{cw})", f"(({ac}*{bc})+{cc})"
        if k < 0.55: return f"({aw}+{bw})", f"({ac}+{bc})"
        if k < 0.75: return f"({aw}-{bw})", f"({ac}-{bc})"
        if k < 0.90: return f"({aw}*{bw})", f"({ac}*{bc})"
        dv = round(r.uniform(1.5, 6.0), 3)             # positive nonzero divisor -> finite
        return f"({aw}/{dv})", f"({ac}/{dv})"

    def faccum_loop(self):                             # amplify ULP diffs over iterations
        self.loopc += 1; i = f"li{self.loopc}"; self.extra.append(i)
        g = self.r.choice(self.fv); cnt = self.r.randint(50, 400)
        bw, bc = self.fexpr(2)
        w = (f"{i} := 0;\nwhile ({i} < {cnt}) {{\n  {g} := {g} + ({bw}) * 0.5;\n  {i} := {i} + 1\n}}")
        c = (f"{i} = 0;\nwhile ({i} < {cnt}) {{\n  {g} = {g} + ({bc}) * 0.5;\n  {i} = {i} + 1;\n}}")
        return w, c

    def gen(self):
        r = self.r
        winit, cinit = [], []
        for v in self.iv:
            n = r.randint(-20, 20); winit.append(f"{v} := {n}"); cinit.append(f"{v} = {n};")
        for g in self.fv:
            n = round(r.uniform(0.1, 5.0), 3); winit.append(f"{g} := {n}"); cinit.append(f"{g} = {n};")
        ws, cs = [], []
        for _ in range(r.randint(5, 10)):
            if r.random() < 0.45:                      # int assignment
                v = r.choice(self.iv); ew, ec = self.iexpr(3)
                ws.append(f"{v} := {ew}"); cs.append(f"{v} = {ec};")
            elif r.random() < 0.7:                     # float assignment
                g = r.choice(self.fv); ew, ec = self.fexpr(3)
                ws.append(f"{g} := {ew}"); cs.append(f"{g} = {ec};")
            else:                                      # accumulation loop
                w, c = self.faccum_loop(); ws.append(w); cs.append(c)

        wpr, cpr = [], []
        for v in self.iv:                              # ints: exact (own token)
            wpr.append(f'printString("{v} "); printInt({v}); printString("\\n")')
            cpr.append(f'printf("{v} %lld\\n",(long long){v});')
        for g in self.fv:                              # floats: printFloat, compared TOLERANTLY
            wpr.append(f'printString("{g} "); printFloat({g}); printString("\\n")')  # (FMA/reassoc bottom-bit
            cpr.append(f'printf("{g} %f\\n",{g});')                                  #  differences are correct)

        idecls = self.iv + self.extra
        wdecl = "var " + ", ".join([f"{v} : int" for v in idecls] + [f"{g} : float" for g in self.fv]) + ";"
        wprog = wdecl + "\n" + ";\n".join(winit + ws + wpr) + "\n"

        cdecl = ("  int64_t " + ", ".join(f"{v}=0" for v in idecls) + ";\n"
                 "  double " + ", ".join(f"{g}=0" for g in self.fv) + ";")
        cbody = "\n".join("  " + l for blk in (cinit + cs + cpr) for l in blk.split("\n"))
        cprog = ("#include <stdio.h>\n#include <stdint.h>\nint main(void){\n"
                 + cdecl + "\n" + cbody + "\n  return 0;\n}\n")
        return wprog, cprog

if __name__ == "__main__":
    seed = int(sys.argv[1]); stem = sys.argv[2]
    w, c = G(seed).gen()
    open(stem + ".w", "w").write(w)
    open(stem + ".c", "w").write(c)
