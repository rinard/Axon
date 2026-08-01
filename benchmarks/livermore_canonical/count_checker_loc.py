#!/usr/bin/env python3
# Copyright (c) 2026 Martin Rinard
"""
Count non-blank, non-comment lines in the certificate-checker code,
split into "executable" and "proof" buckets.

Files (the closure of the cert-checker; see project memory + file headers):
  ExecChecker.lean       -- the executable Bool-returning checker
  PropChecker.lean       -- the propositional reference checker
  SoundnessBridge.lean   -- proves checkCertificateExec → PCertificateValid

Classification rule (file + Lean kind):
  ExecChecker.lean
    theorem                                  → proof   (Fast/list equivalence
                                                        lemmas; not run at
                                                        runtime)
    def / abbrev / structure / inductive /
      instance / partial def                 → exec    (computable functions
                                                        and the data types
                                                        the checker walks)
  PropChecker.lean      → proof   (every decl here is on the Prop side:
                                   PInvariant := … → Prop, PCertificateValid,
                                   plus the supporting `def` aliases —
                                   none of these are executable in the
                                   runtime sense)
  SoundnessBridge.lean  → proof   (the file's purpose is exactly the
                                   Bool→Prop bridge; its few defs are
                                   translation helpers used only in
                                   theorem statements)

Line counting:
  * blank lines                                                    → skip
  * `-- …` line comments / `-- §` markers                          → skip
  * `/-! … -/` and `/- … -/` block comments (incl. multi-line)     → skip
  * trailing inline `-- …` comment is stripped; if the surviving
    visible portion is empty the line is skipped
  * everything else counts, attributed to the most recent top-level
    declaration's kind (or to "header" if before the first decl)

Decl-kind detection: regex on lines starting with optional modifiers
  (@[…], private, protected, noncomputable, partial, unsafe, mutual)
followed by one of theorem|lemma|def|abbrev|structure|inductive|
instance|example|class|axiom|opaque.
"""

import os, re
from collections import defaultdict

CHECKER_DIR = "/Users/mr/CredibleCompilation/CredibleCompilation"
FILES = ["ExecChecker.lean", "PropChecker.lean", "SoundnessBridge.lean"]

KINDS = ("theorem", "lemma", "def", "abbrev", "structure", "inductive",
         "instance", "example", "class", "axiom", "opaque")
MOD = (r"(?:@\[[^\]]*\]\s+)?"
       r"(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+|mutual\s+)*")
KIND_RE = re.compile(rf"^\s*{MOD}(?P<kind>{'|'.join(KINDS)})\b")

def classify(file_basename: str, kind: str) -> str:
    """Return 'exec' or 'proof' for a given (file, kind) pair."""
    if file_basename == "ExecChecker.lean":
        return "proof" if kind == "theorem" or kind == "lemma" else "exec"
    return "proof"  # PropChecker + SoundnessBridge: every decl is Prop-side

def count(path: str):
    buckets = defaultdict(int)
    in_block = False
    current_kind = None  # None ⇒ pre-first-decl ("header")
    with open(path) as fh:
        for raw in fh:
            line = raw.rstrip("\n")
            stripped = line.strip()

            if in_block:
                if "-/" in line:
                    in_block = False
                continue

            if stripped == "":
                continue
            if stripped.startswith("--"):
                continue
            if stripped.startswith("/-"):
                if "-/" not in stripped[2:]:
                    in_block = True
                continue

            # Strip inline trailing line-comment; check leftover.
            visible = stripped
            i = visible.find("--")
            if i >= 0:
                visible = visible[:i].rstrip()
                if visible == "":
                    continue

            m = KIND_RE.match(line)
            if m:
                current_kind = m.group("kind")
            bucket = "header" if current_kind is None \
                     else classify(os.path.basename(path), current_kind)
            buckets[bucket] += 1
    return buckets

def main():
    rows = []
    for fname in FILES:
        b = count(os.path.join(CHECKER_DIR, fname))
        rows.append((fname, b.get("exec", 0), b.get("proof", 0),
                     b.get("header", 0)))

    width = max(len(r[0]) for r in rows)
    print(f"{'file':<{width}}  {'exec':>6}  {'proof':>6}  {'header':>7}  {'total':>6}")
    print(f"{'-'*width}  {'-'*6}  {'-'*6}  {'-'*7}  {'-'*6}")
    sx = sp = sh = 0
    for fname, e, p, h in rows:
        print(f"{fname:<{width}}  {e:>6}  {p:>6}  {h:>7}  {e+p+h:>6}")
        sx += e; sp += p; sh += h
    print(f"{'-'*width}  {'-'*6}  {'-'*6}  {'-'*7}  {'-'*6}")
    total = sx + sp + sh
    pct_exec = 100.0 * sx / total if total else 0
    pct_proof = 100.0 * (sp + sh) / total if total else 0
    print(f"{'TOTAL':<{width}}  {sx:>6}  {sp:>6}  {sh:>7}  {total:>6}")
    print()
    print(f"Executable code (runtime path of the checker):  {sx} NCNB lines "
          f"({pct_exec:.1f} %)")
    print(f"Proof code (Prop spec + soundness theorems):    "
          f"{sp + sh} NCNB lines ({pct_proof:.1f} %)")
    print(f"  of which 'header' (imports / set_option /     "
          f"namespace / docstrings already excluded as comment): {sh} lines")

if __name__ == "__main__":
    main()
