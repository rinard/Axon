#!/usr/bin/env python3
# Copyright (c) 2026 Martin Rinard
"""Generate random While + C test program pairs.

Usage:
    python3 tests/gen_tests.py [count] [seed]
    python3 tests/gen_tests.py 20        # 20 programs, random seed
    python3 tests/gen_tests.py 20 42     # 20 programs, seed 42

Programs are written to tests/programs/gen_NNN.{while,c}
"""

import random
import sys
import os

# --- Configuration ---
MAX_DEPTH = 3
MAX_STMTS = 6
MAX_LOOP_BOUND = 10
NUM_INT_VARS = 6
NUM_BOOL_VARS = 2
NUM_ARRAYS = 2
ARRAY_SIZE = 32  # keep small to avoid sparse access

INT_VARS = [f"v{i}" for i in range(NUM_INT_VARS)]
BOOL_VARS = [f"b{i}" for i in range(NUM_BOOL_VARS)]
ARRAY_NAMES = [chr(ord('A') + i) for i in range(NUM_ARRAYS)]

ALL_VARS = INT_VARS + BOOL_VARS  # declaration order

# --- AST nodes ---

class Expr:
    """Integer expression."""
    pass

class Lit(Expr):
    def __init__(self, n): self.n = n
    def to_while(self):
        return str(self.n) if self.n >= 0 else f"(0 - {-self.n})"
    def to_c(self): return str(self.n)

class Var(Expr):
    def __init__(self, name): self.name = name
    def to_while(self): return self.name
    def to_c(self): return self.name

class BinOp(Expr):
    def __init__(self, op, l, r): self.op = op; self.l = l; self.r = r
    def to_while(self): return f"({self.l.to_while()} {self.op} {self.r.to_while()})"
    def to_c(self):
        if self.op in ('+', '-', '*'):
            # Use unsigned cast for wrapping semantics
            return f"(int64_t)((uint64_t){self.l.to_c()} {self.op} (uint64_t){self.r.to_c()})"
        return f"({self.l.to_c()} {self.op} {self.r.to_c()})"

class ArrRead(Expr):
    def __init__(self, arr, idx): self.arr = arr; self.idx = idx
    def to_while(self): return f"{self.arr}[{self.idx.to_while()}]"
    def to_c(self): return f"{self.arr}[{self.idx.to_c()}]"

class BoolExpr:
    pass

class BoolLit(BoolExpr):
    def __init__(self, v): self.v = v
    def to_while(self): return "true" if self.v else "false"
    def to_c(self): return "1" if self.v else "0"

class Cmp(BoolExpr):
    def __init__(self, op, l, r): self.op = op; self.l = l; self.r = r
    def to_while(self): return f"{self.l.to_while()} {self.op} {self.r.to_while()}"
    def to_c(self):
        return f"(({self.l.to_c()} {self.op} {self.r.to_c()}) ? 1 : 0)"

class BoolNot(BoolExpr):
    def __init__(self, e): self.e = e
    def to_while(self): return f"!({self.e.to_while()})"
    def to_c(self): return f"(!{self.e.to_c()})"

class BoolAnd(BoolExpr):
    def __init__(self, a, b): self.a = a; self.b = b
    def to_while(self): return f"({self.a.to_while()}) && ({self.b.to_while()})"
    def to_c(self): return f"(({self.a.to_c()} && {self.b.to_c()}) ? 1 : 0)"

class BoolOr(BoolExpr):
    def __init__(self, a, b): self.a = a; self.b = b
    def to_while(self): return f"({self.a.to_while()}) || ({self.b.to_while()})"
    def to_c(self): return f"(({self.a.to_c()} || {self.b.to_c()}) ? 1 : 0)"

class BoolVar(BoolExpr):
    def __init__(self, name): self.name = name
    def to_while(self): return self.name
    def to_c(self): return self.name

class Stmt:
    pass

class Skip(Stmt):
    def to_while(self, ind=""): return f"{ind}skip"
    def to_c(self, ind=""): return f"{ind}/* skip */;"

class Assign(Stmt):
    def __init__(self, var, expr): self.var = var; self.expr = expr
    def to_while(self, ind=""): return f"{ind}{self.var} := {self.expr.to_while()}"
    def to_c(self, ind=""): return f"{ind}{self.var} = {self.expr.to_c()};"

class BAssign(Stmt):
    def __init__(self, var, expr): self.var = var; self.expr = expr
    def to_while(self, ind=""): return f"{ind}{self.var} := {self.expr.to_while()}"
    def to_c(self, ind=""): return f"{ind}{self.var} = {self.expr.to_c()};"

class ArrWrite(Stmt):
    def __init__(self, arr, idx, val): self.arr = arr; self.idx = idx; self.val = val
    def to_while(self, ind=""): return f"{ind}{self.arr}[{self.idx.to_while()}] := {self.val.to_while()}"
    def to_c(self, ind=""): return f"{ind}{self.arr}[{self.idx.to_c()}] = {self.val.to_c()};"

class Seq(Stmt):
    def __init__(self, stmts): self.stmts = stmts
    def to_while(self, ind=""):
        return (";\n").join(s.to_while(ind) for s in self.stmts)
    def to_c(self, ind=""):
        return "\n".join(s.to_c(ind) for s in self.stmts)

class IfElse(Stmt):
    def __init__(self, cond, s1, s2): self.cond = cond; self.s1 = s1; self.s2 = s2
    def to_while(self, ind=""):
        s1 = self.s1.to_while(ind + "  ")
        s2 = self.s2.to_while(ind + "  ")
        return f"{ind}if ({self.cond.to_while()}) {{\n{s1}\n{ind}}} else {{\n{s2}\n{ind}}}"
    def to_c(self, ind=""):
        s1 = self.s1.to_c(ind + "    ")
        s2 = self.s2.to_c(ind + "    ")
        return f"{ind}if ({self.cond.to_c()}) {{\n{s1}\n{ind}}} else {{\n{s2}\n{ind}}}"

class Loop(Stmt):
    """Bounded loop: while (counter < bound) { body; counter := counter + 1 }"""
    def __init__(self, counter, bound, body):
        self.counter = counter; self.bound = bound; self.body = body
    def to_while(self, ind=""):
        body_w = self.body.to_while(ind + "  ")
        inc = f"{ind}  {self.counter} := {self.counter} + 1"
        return (f"{ind}while ({self.counter} < {self.bound}) {{\n"
                f"{body_w};\n{inc}\n{ind}}}")
    def to_c(self, ind=""):
        body_c = self.body.to_c(ind + "    ")
        inc = f"{ind}    {self.counter} = {self.counter} + 1;"
        return (f"{ind}while ({self.counter} < {self.bound}) {{\n"
                f"{body_c}\n{inc}\n{ind}}}")


# --- Generators ---

def rand_lit():
    return Lit(random.choice([0, 1, 2, 3, 5, 7, 10, 42, 100, -1, -5]))

def rand_safe_array_idx(depth=0):
    """Generate an index expression guaranteed to be in [0, ARRAY_SIZE).
    Uses only non-negative sub-expressions to avoid signed modulo issues."""
    r = random.random()
    if r < 0.5:
        return Lit(random.randint(0, ARRAY_SIZE - 1))
    else:
        # Use a variable, but wrap: ((var % SIZE) + SIZE) % SIZE to handle negatives
        v = Var(random.choice(INT_VARS))
        return BinOp('%', BinOp('+', BinOp('%', v, Lit(ARRAY_SIZE)), Lit(ARRAY_SIZE)), Lit(ARRAY_SIZE))

def rand_int_expr(depth=0):
    if depth >= MAX_DEPTH:
        return random.choice([rand_lit(), Var(random.choice(INT_VARS))])
    r = random.random()
    if r < 0.2:
        return rand_lit()
    elif r < 0.5:
        return Var(random.choice(INT_VARS))
    elif r < 0.65:
        # Array read with safe bounded index
        arr = random.choice(ARRAY_NAMES)
        idx = rand_safe_array_idx(depth + 1)
        return ArrRead(arr, idx)
    else:
        op = random.choice(['+', '-', '*'])  # avoid div/mod to prevent div-by-zero
        return BinOp(op, rand_int_expr(depth + 1), rand_int_expr(depth + 1))

def rand_safe_divisor(depth=0):
    """Generate an expression guaranteed non-zero: literal or (expr | 1) trick.
    Since While has no bitwise OR, use (expr * expr + 1) which is always >= 1."""
    # Simplest: just use a non-zero literal
    return Lit(random.choice([1, 2, 3, 5, 7, 10]))

def rand_int_expr_with_div(depth=0):
    """Like rand_int_expr but sometimes includes div/mod with safe divisors."""
    if depth >= MAX_DEPTH:
        return random.choice([rand_lit(), Var(random.choice(INT_VARS))])
    r = random.random()
    if r < 0.15:
        return rand_lit()
    elif r < 0.4:
        return Var(random.choice(INT_VARS))
    elif r < 0.5:
        arr = random.choice(ARRAY_NAMES)
        idx = rand_safe_array_idx(depth + 1)
        return ArrRead(arr, idx)
    elif r < 0.6:
        op = random.choice(['/', '%'])
        return BinOp(op, rand_int_expr_with_div(depth + 1), rand_safe_divisor(depth + 1))
    else:
        op = random.choice(['+', '-', '*'])
        return BinOp(op, rand_int_expr_with_div(depth + 1), rand_int_expr_with_div(depth + 1))

def rand_bool_expr(depth=0):
    if depth >= MAX_DEPTH:
        return Cmp(random.choice(['<', '<=', '==', '!=']),
                   Var(random.choice(INT_VARS)), rand_lit())
    r = random.random()
    if r < 0.1:
        return BoolVar(random.choice(BOOL_VARS))
    elif r < 0.5:
        return Cmp(random.choice(['<', '<=', '==', '!=', '>', '>=']),
                   rand_int_expr(depth + 1), rand_int_expr(depth + 1))
    elif r < 0.65:
        return BoolNot(rand_bool_expr(depth + 1))
    elif r < 0.8:
        return BoolAnd(rand_bool_expr(depth + 1), rand_bool_expr(depth + 1))
    else:
        return BoolOr(rand_bool_expr(depth + 1), rand_bool_expr(depth + 1))

def rand_stmt(depth=0, available_counters=None):
    if available_counters is None:
        available_counters = list(INT_VARS)
    if depth >= MAX_DEPTH:
        v = random.choice(INT_VARS)
        return Assign(v, rand_int_expr_with_div(depth))
    r = random.random()
    if r < 0.3:
        v = random.choice(INT_VARS)
        return Assign(v, rand_int_expr_with_div(depth + 1))
    elif r < 0.4:
        v = random.choice(BOOL_VARS)
        return BAssign(v, rand_bool_expr(depth + 1))
    elif r < 0.55:
        arr = random.choice(ARRAY_NAMES)
        idx = rand_safe_array_idx(depth + 1)
        val = rand_int_expr_with_div(depth + 1)
        return ArrWrite(arr, idx, val)
    elif r < 0.75:
        cond = rand_bool_expr(depth + 1)
        s1 = rand_stmt(depth + 1, available_counters)
        s2 = rand_stmt(depth + 1, available_counters)
        return IfElse(cond, s1, s2)
    else:
        if not available_counters:
            v = random.choice(INT_VARS)
            return Assign(v, rand_int_expr_with_div(depth))
        counter = random.choice(available_counters)
        remaining = [c for c in available_counters if c != counter]
        bound = random.randint(1, MAX_LOOP_BOUND)
        body = rand_stmt(depth + 1, remaining)
        return Loop(counter, bound, body)

def rand_program(num_stmts=None):
    if num_stmts is None:
        num_stmts = random.randint(3, MAX_STMTS)
    stmts = []
    # Initialize some vars and arrays to non-zero
    for v in random.sample(INT_VARS, min(3, NUM_INT_VARS)):
        stmts.append(Assign(v, rand_lit()))
    for arr in ARRAY_NAMES:
        for i in range(random.randint(1, 4)):
            stmts.append(ArrWrite(arr, Lit(i), rand_lit()))
    # Random statements
    for _ in range(num_stmts):
        stmts.append(rand_stmt())
    return Seq(stmts)

def emit_while(prog):
    decls = ", ".join(
        [f"{v} : int" for v in INT_VARS] +
        [f"{v} : bool" for v in BOOL_VARS]
    )
    arr_decls = ", ".join(f"{a}[{ARRAY_SIZE}] : int" for a in ARRAY_NAMES)
    body = prog.to_while("")
    return f"var {decls};\narray {arr_decls};\n{body}\n"

def emit_c(prog):
    int_decls = ", ".join(f"{v} = 0" for v in INT_VARS)
    bool_decls = ", ".join(f"{v} = 0" for v in BOOL_VARS)
    arr_decls = "\n".join(f"int64_t {a}[{ARRAY_SIZE}];" for a in ARRAY_NAMES)
    body = prog.to_c("    ")
    prints = "\n".join(
        f'    printf("%s = %ld\\n", "{v}", {v});' for v in ALL_VARS
    )
    return f"""#include <stdio.h>
#include <stdint.h>
{arr_decls}
int main() {{
    int64_t {int_decls};
    int64_t {bool_decls};
{body}
{prints}
    return 0;
}}
"""

# --- Bounds-error test generation ---

def rand_oob_index():
    """Generate an index expression guaranteed to be out of bounds."""
    return Lit(random.choice([ARRAY_SIZE, ARRAY_SIZE + 1, ARRAY_SIZE * 2, 9999, -1, -5]))

def rand_bounds_error_program():
    """Generate a program that triggers an array bounds error.
    Some safe setup, then one out-of-bounds access."""
    stmts = []
    # Initialize some vars
    for v in random.sample(INT_VARS, min(2, NUM_INT_VARS)):
        stmts.append(Assign(v, Lit(random.randint(0, 10))))
    # Safe array inits
    arr = random.choice(ARRAY_NAMES)
    stmts.append(ArrWrite(arr, Lit(0), rand_lit()))
    # Out-of-bounds access (read or write)
    oob_idx = rand_oob_index()
    if random.random() < 0.5:
        stmts.append(Assign(INT_VARS[0], ArrRead(arr, oob_idx)))
    else:
        stmts.append(ArrWrite(arr, oob_idx, rand_lit()))
    return Seq(stmts)

NUM_BOUNDS_TESTS = 5

# --- Main ---

def main():
    count = int(sys.argv[1]) if len(sys.argv) > 1 else 10
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else random.randint(0, 999999)
    random.seed(seed)

    script_dir = os.path.dirname(os.path.abspath(__file__))
    prog_dir = os.path.join(script_dir, "programs")
    os.makedirs(prog_dir, exist_ok=True)

    print(f"Generating {count} test programs (seed={seed})...")
    for i in range(count):
        prog = rand_program()
        name = f"gen_{i:03d}"

        with open(os.path.join(prog_dir, f"{name}.while"), "w") as f:
            f.write(emit_while(prog))
        with open(os.path.join(prog_dir, f"{name}.c"), "w") as f:
            f.write(emit_c(prog))

    # Generate bounds-error tests (While-only, expected exit code 1)
    print(f"Generating {NUM_BOUNDS_TESTS} bounds-error tests...")
    for i in range(NUM_BOUNDS_TESTS):
        prog = rand_bounds_error_program()
        name = f"bounds_{i:03d}"
        with open(os.path.join(prog_dir, f"{name}.while"), "w") as f:
            f.write(emit_while(prog))

    print(f"Wrote {count} pairs to {prog_dir}/gen_*.{{while,c}}")
    print(f"Run: ./tests/run_tests.sh")

if __name__ == "__main__":
    main()
