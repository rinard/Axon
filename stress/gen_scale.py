#!/usr/bin/env python3
# Copyright (c) 2026 Martin Rinard
"""Scaling-limit generator. Emits matched While+C programs of a given 'kind' and
'size', for finding how large a program the compiler/checker can handle.

Kinds:
  vars   N  -> N simultaneously-live scalar ints, cross-mixed (register pressure)
  line   N  -> N straight-line dependent assignments (instruction count)
  array  N  -> one int array of size N, filled and summed (stack frame size)
  nest   N  -> N-deep nested while loops
  fvars  N  -> N simultaneously-live float vars (float register pressure)
"""
import sys

def emit_vars(n):
    # Seed from a runtime loop the constant-propagator cannot evaluate, so the
    # N variables are genuinely live -> forces real register pressure / spilling.
    w, c = [], []
    decls = ", ".join(f"v{i} : int" for i in range(n))
    w.append(f"var {decls}, seed : int, i : int;")
    w.append("seed := 0;")
    w.append("i := 0;")
    w.append("while (i < 37) {\n  seed := seed + i * 3;\n  i := i + 1\n};")
    for i in range(n):
        w.append(f"v{i} := seed + {i+1};")
    # two cross-mixing rounds so every var is live across the others
    for r in range(2):
        for i in range(n):
            j = (i + 1) % n
            w.append(f"v{i} := v{i} + v{j} * {r+2};")
    # print all
    for i in range(n):
        w.append(f'printInt(v{i}); printString(" ");')
    w.append('printString("\\n")')

    c.append("#include <stdio.h>\n#include <stdint.h>\nint main(void){")
    c.append("  int64_t " + ", ".join(f"v{i}" for i in range(n)) + ", seed=0, i;")
    c.append("  for(i=0;i<37;i++) seed=(int64_t)((uint64_t)seed+(uint64_t)i*3u);")
    for i in range(n):
        c.append(f"  v{i}=(int64_t)((uint64_t)seed+(uint64_t){i+1});")
    for r in range(2):
        for i in range(n):
            j = (i + 1) % n
            c.append(f"  v{i}=(int64_t)((uint64_t)v{i}+(uint64_t)v{j}*(uint64_t){r+2});")
    for i in range(n):
        c.append(f'  printf("%ld ",(long)v{i});')
    c.append('  printf("\\n"); return 0; }')
    return "\n".join(w), "\n".join(c)

def emit_line(n):
    prog = "var a : int, b : int, acc : int;\na := 1;\nb := 1;\nacc := 0;\n"
    stmts = []
    for i in range(n):
        stmts.append(f"acc := acc + a * {(i%7)+1} - b")
        stmts.append("a := a + 1")
        stmts.append("b := b + acc")
    stmts.append('printInt(acc); printString(" "); printInt(a); printString(" "); printInt(b); printString("\\n")')
    prog += ";\n".join(stmts)

    cc = ["#include <stdio.h>\n#include <stdint.h>\nint main(void){",
          "  int64_t a=1,b=1,acc=0;"]
    for i in range(n):
        cc.append(f"  acc=(int64_t)((uint64_t)acc+(uint64_t)a*(uint64_t){(i%7)+1}-(uint64_t)b);")
        cc.append("  a=a+1;")
        cc.append("  b=(int64_t)((uint64_t)b+(uint64_t)acc);")
    cc.append('  printf("%ld %ld %ld\\n",(long)acc,(long)a,(long)b); return 0; }')
    return prog, "\n".join(cc)

def emit_array(n):
    prog = f"var i : int, s : int;\narray A[{n}] : int;\n"
    stmts = ["i := 0",
             f"while (i < {n}) {{\n  A[i] := i * 3 - 7;\n  i := i + 1\n}}",
             "s := 0",
             "i := 0",
             f"while (i < {n}) {{\n  s := s + A[i];\n  i := i + 1\n}}",
             'printInt(s); printString("\\n")']
    prog += ";\n".join(stmts)
    cc = f"""#include <stdio.h>
#include <stdint.h>
int main(void){{
  int64_t i,s; static int64_t A[{n}];
  for(i=0;i<{n};i++) A[i]=(int64_t)((uint64_t)i*3u-7u);
  s=0;
  for(i=0;i<{n};i++) s=(int64_t)((uint64_t)s+(uint64_t)A[i]);
  printf("%ld\\n",(long)s); return 0; }}"""
    return prog, cc

def emit_nest(n):
    # N-deep nested loops each iterating a small fixed count
    decls = ", ".join(f"i{k} : int" for k in range(n)) + ", c : int"
    prog = f"var {decls};\nc := 0;\n"
    open_loops = ""
    indent = ""
    lines = []
    for k in range(n):
        lines.append(f"{indent}i{k} := 0;")
        lines.append(f"{indent}while (i{k} < 2) {{")
        indent += "  "
    lines.append(f"{indent}c := c + 1;")
    # close loops, incrementing counters
    for k in reversed(range(n)):
        indent = "  " * (k+1)
        lines.append(f"{indent}i{k} := i{k} + 1")
        indent2 = "  " * k
        lines.append(f"{indent2}}};")
    prog += "\n".join(lines) + '\nprintInt(c); printString("\\n")'
    cc = ["#include <stdio.h>\n#include <stdint.h>\nint main(void){",
          "  int64_t " + ", ".join(f"i{k}" for k in range(n)) + ", c=0;"]
    ind = "  "
    for k in range(n):
        cc.append(f"{ind}for(i{k}=0;i{k}<2;i{k}++){{")
        ind += "  "
    cc.append(f"{ind}c=c+1;")
    for k in reversed(range(n)):
        ind = "  "*(k+1)
        cc.append(ind+"}")
    cc.append('  printf("%ld\\n",(long)c); return 0; }')
    return prog, "\n".join(cc)

def emit_fvars(n):
    decls = ", ".join(f"f{i} : float" for i in range(n))
    prog = f"var {decls};\n"
    stmts = []
    for i in range(n):
        stmts.append(f"f{i} := intToFloat({i+1}) * 0.5")
    for r in range(2):
        for i in range(n):
            j=(i+1)%n
            stmts.append(f"f{i} := f{i} + f{j} * {r+2}.0")
    for i in range(n):
        stmts.append(f'printFloat(f{i}); printString(" ")')
    stmts.append('printString("\\n")')
    prog += ";\n".join(stmts)
    cc = ["#include <stdio.h>\nint main(void){",
          "  double " + ", ".join(f"f{i}" for i in range(n)) + ";"]
    for i in range(n):
        cc.append(f"  f{i}=(double)({i+1})*0.5;")
    for r in range(2):
        for i in range(n):
            j=(i+1)%n
            cc.append(f"  f{i}=f{i}+f{j}*{r+2}.0;")
    for i in range(n):
        cc.append(f'  printf("%f ",f{i});')
    cc.append('  printf("\\n"); return 0; }')
    return prog, "\n".join(cc)

KINDS = {"vars":emit_vars, "line":emit_line, "array":emit_array, "nest":emit_nest, "fvars":emit_fvars}

if __name__ == "__main__":
    kind, n, stem = sys.argv[1], int(sys.argv[2]), sys.argv[3]
    w, c = KINDS[kind](n)
    open(stem+".w","w").write(w+"\n")
    open(stem+".c","w").write(c+"\n")
