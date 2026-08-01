#!/usr/bin/env python3
# Copyright (c) 2026 Martin Rinard
"""
Instrument Livermore Loops .s files with kernel-only timing.

Uses ARM64 CNTVCT_EL0 counter (24MHz on Apple Silicon).
Inserts timing around the rep loop only, excluding initialization.

Strategy: Find the pattern where `rep := 0` is followed by the rep loop
condition check (mov xN, #NREPS; cmp xM, xN; cset; eor; cbnz .Lexit).
Insert `mrs x19, CNTVCT_EL0` before the rep loop, and timing print
code at the exit label.
"""

import re
import sys
import os

# NREPS per kernel (from .w files)
NREPS = {
    'k01_hydro': 10000, 'k02_iccg': 10000, 'k03_dot': 10000,
    'k04_banded': 10000, 'k05_tridiag': 10000, 'k06_recurrence': 1000,
    'k07_eos': 10000, 'k08_adi': 10000, 'k09_integrate': 10000,
    'k10_diff_predict': 10000, 'k11_prefix_sum': 10000, 'k12_first_diff': 10000,
    'k13_pic_2d': 10000, 'k14_pic_1d': 10000, 'k15_casual': 10000,
    'k16_monte_carlo': 10000, 'k17_implicit_cond': 10000, 'k18_hydro_2d': 10000,
    'k19_linear_recurrence': 10000, 'k20_discrete_ord': 10000,
    'k21_matmul': 10000, 'k22_planck': 10000, 'k23_hydro_implicit': 100000,
    'k24_find_min': 10000,
}


def find_rep_loop(lines, nreps):
    """Find the rep loop condition check.

    Handles three patterns:
    1. `mov xN, #NREPS` then `cmp xM, xN` (single-instruction immediate)
    2. `movz xN, #lo; movk xN, #hi, lsl #16` then `cmp xM, xN` (large NREPS)
    3. `mov xN, #NREPS` then `mov xP, xN; cmp xM, xP` (indirect cmp via k16)

    Returns (rep_loop_label_idx, exit_label) or None.
    """
    candidates = []

    if nreps <= 65535:
        # Pattern 1 & 3: single mov #NREPS
        nreps_pattern = re.compile(rf'^\s+mov\s+(x\d+),\s+#({nreps})\s*$')
        for i, line in enumerate(lines):
            m = nreps_pattern.match(line)
            if m:
                candidates.append((i, m.group(1)))
    else:
        # Pattern 2: movz/movk for large constants
        lo = nreps & 0xFFFF
        hi = (nreps >> 16) & 0xFFFF
        movz_pattern = re.compile(rf'^\s+movz\s+(x\d+),\s+#{lo}\s*$')
        for i, line in enumerate(lines):
            m = movz_pattern.match(line)
            if m:
                reg = m.group(1)
                # Check next line for movk
                if i + 1 < len(lines):
                    movk_m = re.match(rf'^\s+movk\s+{reg},\s+#{hi},\s+lsl\s+#16\s*$', lines[i+1])
                    if movk_m:
                        candidates.append((i, reg))

    # For each candidate, check if it's followed by cmp/cset/eor/cbnz pattern
    for line_idx, nreps_reg in candidates:
        # Look at next few lines for cmp pattern (direct or indirect)
        for j in range(line_idx + 1, min(line_idx + 10, len(lines))):
            # Direct: cmp xM, xN
            cmp_m = re.match(rf'^\s+cmp\s+(x\d+),\s+{nreps_reg}\s*$', lines[j])
            if not cmp_m:
                # Indirect: mov xP, xN; cmp xM, xP
                mov_m = re.match(rf'^\s+mov\s+(x\d+),\s+{nreps_reg}\s*$', lines[j])
                if mov_m:
                    alias_reg = mov_m.group(1)
                    for jj in range(j + 1, min(j + 4, len(lines))):
                        cmp_m = re.match(rf'^\s+cmp\s+(x\d+),\s+{alias_reg}\s*$', lines[jj])
                        if cmp_m:
                            j = jj
                            break
                    else:
                        cmp_m = None
            if cmp_m:
                # Found the cmp. Look for cbnz to find exit label
                for k in range(j + 1, min(j + 4, len(lines))):
                    cbnz_m = re.match(r'^\s+cbnz\s+w0,\s+(\.L\w+)\s*$', lines[k])
                    if cbnz_m:
                        exit_label = cbnz_m.group(1)
                        # Find the label just before the mov #NREPS
                        # Walk backwards to find the .Lxx: label
                        label_idx = None
                        for b in range(line_idx - 1, max(line_idx - 5, -1), -1):
                            if re.match(r'^\.L\d+:\s*$', lines[b]):
                                label_idx = b
                                break
                        if label_idx is not None:
                            return (label_idx, exit_label)
    return None


def find_label_line(lines, label):
    """Find the line index of a label like .L76"""
    target = label + ':'
    for i, line in enumerate(lines):
        if line.strip() == target:
            return i
    return None


def instrument(lines, kernel_name, nreps):
    """Insert timing around the rep loop."""
    result = find_rep_loop(lines, nreps)
    if result is None:
        print(f"  WARNING: could not find rep loop in {kernel_name}", file=sys.stderr)
        return None

    rep_label_idx, exit_label = result
    exit_label_idx = find_label_line(lines, exit_label)
    if exit_label_idx is None:
        print(f"  WARNING: could not find exit label {exit_label} in {kernel_name}", file=sys.stderr)
        return None

    print(f"  {kernel_name}: rep loop at line {rep_label_idx+1} ({lines[rep_label_idx].strip()}), "
          f"exit at line {exit_label_idx+1} ({exit_label})", file=sys.stderr)

    # We also need to save/restore x19,x20 in the prologue/epilogue since
    # they're callee-saved and we're using them.
    # Find the prologue (str x30/x29) and epilogue (ldr x29/x30 before ret)

    # Build the instrumented file
    out = []
    zeroed_flag = False

    for i, line in enumerate(lines):
        # Insert x21=0 (timer flag) after the variable init comment
        if not zeroed_flag and '// Initialize all variables to 0' in line:
            out.append(line)
            out.append('  mov x21, #0  // timer started flag\n')
            zeroed_flag = True
            continue
        # Insert timing START right after the rep loop label
        # Runs every iteration but that's fine - the mrs is cheap (1 cycle)
        # and we always want the FIRST reading. Use x21 as "already started" flag.
        # x21 starts at 0 (we zero it in the prologue).
        if i == rep_label_idx:
            out.append(line)  # emit the label itself
            out.append('  // === TIMING START (once) ===\n')
            out.append('  cbnz x21, .Ltimer_skip\n')
            out.append('  mrs x19, CNTVCT_EL0\n')
            out.append('  mov x21, #1\n')
            out.append('.Ltimer_skip:\n')
            continue  # already emitted the label line

        # Insert timing END right after the exit label
        if i == exit_label_idx:
            out.append(line)  # emit the label itself first
            out.append('  // === TIMING END ===\n')
            out.append('  mrs x20, CNTVCT_EL0\n')
            out.append('  sub x20, x20, x19  // elapsed ticks\n')
            # Save all volatile regs we might clobber with printf
            # We need to save the state so the rest of the program works
            # Print raw ticks as integer - convert to seconds externally
            out.append('  // Save volatile regs for printf\n')
            out.append('  stp x0, x1, [sp, #-16]!\n')
            out.append('  stp x2, x3, [sp, #-16]!\n')
            out.append('  stp x4, x5, [sp, #-16]!\n')
            out.append('  stp x6, x7, [sp, #-16]!\n')
            out.append('  stp x8, x9, [sp, #-16]!\n')
            out.append('  stp x10, x11, [sp, #-16]!\n')
            out.append('  stp x12, x13, [sp, #-16]!\n')
            out.append('  stp x14, x15, [sp, #-16]!\n')
            out.append('  stp x16, x17, [sp, #-16]!\n')
            out.append('  str x18, [sp, #-16]!\n')
            out.append('  stp d0, d1, [sp, #-16]!\n')
            out.append('  stp d2, d3, [sp, #-16]!\n')
            out.append('  stp d4, d5, [sp, #-16]!\n')
            out.append('  stp d6, d7, [sp, #-16]!\n')
            out.append('  sub sp, sp, #16\n')
            out.append('  str x20, [sp]\n')
            out.append('  adrp x0, .Ltimer_fmt@PAGE\n')
            out.append('  add x0, x0, .Ltimer_fmt@PAGEOFF\n')
            out.append('  bl _printf\n')
            out.append('  add sp, sp, #16\n')
            out.append('  // Restore volatile regs\n')
            out.append('  ldp d6, d7, [sp], #16\n')
            out.append('  ldp d4, d5, [sp], #16\n')
            out.append('  ldp d2, d3, [sp], #16\n')
            out.append('  ldp d0, d1, [sp], #16\n')
            out.append('  ldr x18, [sp], #16\n')
            out.append('  ldp x16, x17, [sp], #16\n')
            out.append('  ldp x14, x15, [sp], #16\n')
            out.append('  ldp x12, x13, [sp], #16\n')
            out.append('  ldp x10, x11, [sp], #16\n')
            out.append('  ldp x8, x9, [sp], #16\n')
            out.append('  ldp x6, x7, [sp], #16\n')
            out.append('  ldp x4, x5, [sp], #16\n')
            out.append('  ldp x2, x3, [sp], #16\n')
            out.append('  ldp x0, x1, [sp], #16\n')
            out.append('\n')
            continue  # already emitted the label line

        out.append(line)

    # Add timer format string to the cstring section
    # Find the cstring section and add our format
    for i, line in enumerate(out):
        if '.Lbounds_msg:' in line or '.Ldiv_msg:' in line:
            # Find the next .asciz after this
            pass

    # Just add it after .Lbounds_msg's .asciz
    new_out = []
    added_fmt = False
    for line in out:
        new_out.append(line)
        if not added_fmt and '.asciz "error: array index out of bounds' in line:
            new_out.append('.Ltimer_fmt:\n')
            new_out.append('  .asciz "kernel_ticks: %lu\\n"\n')
            added_fmt = True
        elif not added_fmt and '.asciz "error: division by zero' in line:
            # Some files might not have bounds_msg, use div_msg
            pass

    if not added_fmt:
        # Try after div_msg
        final_out = []
        for line in new_out:
            final_out.append(line)
            if not added_fmt and '.asciz "error: division by zero' in line:
                final_out.append('.Ltimer_fmt:\n')
                final_out.append('  .asciz "kernel_ticks: %lu\\n"\n')
                added_fmt = True
        new_out = final_out

    if not added_fmt:
        # Last resort: add before .section __DATA
        final_out = []
        for line in new_out:
            if not added_fmt and '.section __DATA' in line:
                final_out.append('.Ltimer_fmt:\n')
                final_out.append('  .asciz "kernel_ticks: %lu\\n"\n')
                added_fmt = True
            final_out.append(line)
        new_out = final_out

    return new_out


def main():
    build_dir = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'build')
    timed_dir = os.path.join(build_dir, 'timed')
    os.makedirs(timed_dir, exist_ok=True)

    success = 0
    fail = 0

    for kernel_name, nreps in sorted(NREPS.items()):
        src = os.path.join(build_dir, f'{kernel_name}_wl.s')
        dst = os.path.join(timed_dir, f'{kernel_name}_wl.s')

        if not os.path.exists(src):
            print(f"  SKIP: {src} not found", file=sys.stderr)
            fail += 1
            continue

        with open(src) as f:
            lines = f.readlines()

        result = instrument(lines, kernel_name, nreps)
        if result is None:
            fail += 1
            continue

        with open(dst, 'w') as f:
            f.writelines(result)

        success += 1

    print(f"\nInstrumented {success} kernels, {fail} failures", file=sys.stderr)


if __name__ == '__main__':
    main()
