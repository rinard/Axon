<!-- Copyright (c) 2026 Martin Rinard -->
# Axon

A verified optimizing compiler for a small imperative language, built in **Lean 4**.
Axon compiles `WhileLang` → three-address code (`TAC`) → **ARM64** assembly, and its
optimizer is verified by **translation validation** in the *credible compilation* style:
each optimization pass emits a machine-checkable **certificate**, and a **proven** checker
(`checkCertificateExec`) validates that certificate against a soundness theorem. A pass may
be written and tuned freely; if its certificate does not check, the transformed program is
rejected — so the trusted core never depends on any pass being correct.

## What is verified

The end-to-end capstone is
[`compileProgramAst_correctness`](CredibleCompilation/PipelineCorrectness.lean#L667): a
well-typed source program and the ARM64 program Axon produces exhibit the same observable
behavior — termination with equal outputs, divergence, and bounds/type-error outcomes are
all preserved, in both directions (`while_to_arm_correctness` and its converses give the
bidirectional statement).

The verified surface includes:

- **Front end** — parser, type system, and small-step semantics for `WhileLang`
  ([Parser.lean](CredibleCompilation/Parser.lean), [TypeSystem.lean](CredibleCompilation/TypeSystem.lean), [Semantics.lean](CredibleCompilation/Semantics.lean)).
- **Certificate checker** — the proven `checkCertificateExec` and the certificate algebra
  ([ExecChecker.lean](CredibleCompilation/ExecChecker.lean), [Core.lean](CredibleCompilation/Core.lean), [PropChecker.lean](CredibleCompilation/PropChecker.lean)).
- **Optimization passes** — constant/copy propagation, CSE, DCE, DAE, LICM, induction-variable
  elimination, rematerialization, constant hoisting, peephole, FMA fusion, register allocation,
  and a validated interval (bounds) analysis. Each emits a certificate; passes not wired into the
  default pipeline are retained as verified library code.
- **Back end** — code generation to ARM64 with a verified, encodability-checked instruction
  encoder ([AsmEnc.lean](CredibleCompilation/AsmEnc.lean)): immediate/offset forms carry their real
  AArch64 encodability constraints as theorems (`emitCmd_wf`), a legalizing emitter rewrites any
  out-of-range operand, and `decode_emitCmd` proves the encoding is a faithful round-trip.
- **ARM64 semantics & correctness** — a machine model and the simulation/behavior-exhaustion
  proofs relating TAC execution to ARM execution
  ([ArmSemantics.lean](CredibleCompilation/ArmSemantics.lean), [ArmCorrectness.lean](CredibleCompilation/ArmCorrectness.lean), [PipelineCorrectness.lean](CredibleCompilation/PipelineCorrectness.lean)).

### Axiom cleanliness

[`AxiomCheck.lean`](CredibleCompilation/AxiomCheck.lean) provides `#assert_clean_axioms`, a
build-failing gate: it fails `lake build` unless the named theorem depends only on
`propext`, `Classical.choice`, and `Quot.sound` (in particular, it rejects any `sorry`). It is
asserted on the encoder theorems, which are axiom-clean.

The whole-pipeline capstone is **not** clean under that gate, and this is disclosed honestly: it
depends on two floating-point **trust axioms** — `FloatBinOp.fadd_comm` (float-add commutativity,
which is unsound only in the presence of NaN operands) and `Flags.condHolds_float_correct` (the
IEEE compare-flag model) — plus `native_decide`'s compiler-trust axioms
(`Lean.ofReduceBool`/`Lean.trustCompiler`). These are the entire trusted mathematical base beyond
Lean's own.

## Building

Requires the Lean toolchain pinned in [`lean-toolchain`](lean-toolchain) (`leanprover/lean4:v4.28.0`),
installed via [`elan`](https://github.com/leanprover/elan), and Mathlib (pinned in
[`lakefile.toml`](lakefile.toml)).

```sh
lake exe cache get     # fetch prebuilt Mathlib artifacts (do this first)
lake build             # build and machine-check the verified library
lake build CCTests     # build the tests and worked examples (not in the default target)
```

## Executables

Built into `.lake/build/bin/` (e.g. `lake build compiler && ./.lake/build/bin/compiler foo.w -o foo`):

| Target | Root | Purpose |
| --- | --- | --- |
| `compiler` | [Compiler.lean](Compiler.lean) | Compile a `.w` program to an ARM64 executable |
| `checker` | [Main.lean](Main.lean) | Run the certificate checker over the bundled example certificates |
| `certaudit` | [Experiments/CertAudit.lean](Experiments/CertAudit.lean) | Audit the production fixpoint pipeline's certificates on a program |
| `certmutate` | [Experiments/CertMutate.lean](Experiments/CertMutate.lean) | Mutate certificates to probe checker soundness |
| `emi` | [Experiments/Emi.lean](Experiments/Emi.lean) | EMI-style equivalence-modulo-inputs testing |
| `t1`, `t1branch`, `t1stack`, `t1array` | [Harness/](Harness/) | Native co-simulation harnesses (TAC vs. ARM) |

## Layout

- [`CredibleCompilation/`](CredibleCompilation/) — the verified compiler library (front end, passes, checker, back end, proofs).
- [`Compiler.lean`](Compiler.lean), [`Main.lean`](Main.lean) — the compiler and checker entry points; [`Compiler/runtime.c`](Compiler/runtime.c) is the C runtime for typed-print calls.
- [`Experiments/`](Experiments/), [`Harness/`](Harness/) — testing tools and co-simulation harnesses.
- [`CCTests/`](CCTests/) — tests and worked examples.
- [`benchmarks/`](benchmarks/), [`tests/`](tests/), [`stress/`](stress/) — benchmark programs (Livermore loops), the differential test suite, and fuzzing/soundness campaigns.

## License

Dual-licensed: **GPLv3** for non-commercial use (including academic), or a commercial license.
See [LICENSE.md](LICENSE.md) for terms and contacts.
