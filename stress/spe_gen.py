#!/usr/bin/env python3
# Copyright (c) 2026 Martin Rinard
"""Skeletal Program Enumeration (#4): exhaustively enumerate the skeleton
`r := a <op> b` over all safe operators and all pairs of boundary operands,
emitting one big While program and a matching C reference that print every
result. A While-vs-C diff then pinpoints the exact (op, a, b) that desyncs.
Includes a/a, a/0-guarded, INT_MIN cases. Usage: spe_gen.py <out_stem>
"""
import sys

BVALS = [-9223372036854775808, 9223372036854775807, 0, -1, 1, 2, -2,
         4294967296, -4294967296]

def wlit(n):
    return f"({n})" if n < 0 else str(n)

def clit(n):
    return "(-9223372036854775807LL-1)" if n == -9223372036854775808 else f"({n}LL)"

def gen(chunk=0, nchunks=1):
    ws, cs = [], []
    def emit(we, ce):
        ws.append(f"r := {we}")
        ws.append("printInt(r); printString(\" \")")
        cs.append(f"  r = {ce};")
        cs.append('  printf("%ld ",(long)r);')
    idx = -1
    for a in BVALS:
        for b in BVALS:
            idx += 1
            if idx % nchunks != chunk:
                continue
            wa, wb, ca, cb = wlit(a), wlit(b), clit(a), clit(b)
            for op in ["+","-","*","&","|","^"]:
                if op in ("+","-","*"):
                    emit(f"({wa} {op} {wb})", f"((int64_t)((uint64_t){ca} {op} (uint64_t){cb}))")
                else:
                    emit(f"({wa} {op} {wb})", f"({ca} {op} {cb})")
            # shifts: amount masked 0..63; C left-shift unsigned
            emit(f"({wa} << ({wb} & 63))", f"((int64_t)((uint64_t){ca} << ({cb} & 63)))")
            emit(f"({wa} >> ({wb} & 63))", f"({ca} >> ({cb} & 63))")
            # division/modulo: divisor forced nonzero (same guard as the fuzzer)
            emit(f"({wa} / ((({wb} % 7) + 8)))", f"({ca} / ((({cb} % 7) + 8)))")
            emit(f"({wa} % ((({wb} % 7) + 8)))", f"({ca} % ((({cb} % 7) + 8)))")
    wprog = "var r : int;\n" + ";\n".join(ws) + ';;\nprintString("\\n")\n'
    # fix the trailing ';;' -> the last stmt already printed; join handles it
    wprog = "var r : int;\n" + ";\n".join(ws + ['printString("\\n")']) + "\n"
    cprog = ("#include <stdio.h>\n#include <stdint.h>\nint main(void){\n  int64_t r;\n"
             + "\n".join(cs) + '\n  printf("\\n");\n  return 0;\n}\n')
    return wprog, cprog

if __name__ == "__main__":
    stem = sys.argv[1]
    chunk = int(sys.argv[2]) if len(sys.argv) > 2 else 0
    nchunks = int(sys.argv[3]) if len(sys.argv) > 3 else 1
    w, c = gen(chunk, nchunks)
    open(stem + ".w", "w").write(w)
    open(stem + ".c", "w").write(c)
