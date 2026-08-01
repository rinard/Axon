-- Copyright (c) 2026 Martin Rinard
import CredibleCompilation.ArmSemantics

/-- Executable evaluator of the ARM operational semantics over the deterministic
    instruction set the compiler emits: integer / shift / control, array and stack
    memory, and the native float ops. Only the genuinely external instructions —
    print / library calls and the non-native (libcall) float-unary variant — fall
    through to `none`, since those step out to code outside the model. -/
def execStep (prog : ArmProg) (s : ArmState) : Option ArmState :=
  match prog[s.pc]? with
  | some (.mov rd imm)       => some (s.setReg rd imm |>.nextPC)
  | some (.movR rd rn)       => some (s.setReg rd (s.regs rn) |>.nextPC)
  | some (.movz rd imm16 sh) => some (s.setReg rd (BitVec.ofNat 64 (imm16 <<< sh.toUInt64).toNat) |>.nextPC)
  | some (.movk rd imm16 sh) => some (s.setReg rd (insertBits (s.regs rd) imm16 sh) |>.nextPC)
  | some (.ldr rd off)       => some (s.setReg rd (s.stack off) |>.nextPC)
  | some (.str rs off)       => some (s.setStack off (s.regs rs) |>.nextPC)
  | some (.addR rd rn rm)    => some (s.setReg rd (s.regs rn + s.regs rm) |>.nextPC)
  | some (.subR rd rn rm)    => some (s.setReg rd (s.regs rn - s.regs rm) |>.nextPC)
  | some (.mulR rd rn rm)    => some (s.setReg rd (s.regs rn * s.regs rm) |>.nextPC)
  | some (.sdivR rd rn rm)   => some (s.setReg rd (BitVec.sdiv (s.regs rn) (s.regs rm)) |>.nextPC)
  | some (.cmp rn rm)        => some { s with flags := Flags.mk (s.regs rn) (s.regs rm), pc := s.pc + 1 }
  | some (.cmpImm rn imm)    => some { s with flags := Flags.mk (s.regs rn) imm, pc := s.pc + 1 }
  | some (.cset rd c)        => some (s.setReg rd (if s.flags.condHolds c then (1 : BitVec 64) else 0) |>.nextPC)
  | some (.cbz rn lbl)       => some (if s.regs rn = 0 then { s with pc := lbl } else s.nextPC)
  | some (.cbnz rn lbl)      => some (if s.regs rn = 0 then s.nextPC else { s with pc := lbl })
  | some (.bCond c lbl)      => some (if s.flags.condHolds c then { s with pc := lbl } else s.nextPC)
  | some (.b lbl)            => some { s with pc := lbl }
  | some (.andImm rd rn imm) => some (s.setReg rd (s.regs rn &&& imm) |>.nextPC)
  | some (.andR rd rn rm)    => some (s.setReg rd (s.regs rn &&& s.regs rm) |>.nextPC)
  | some (.eorImm rd rn imm) => some (s.setReg rd (s.regs rn ^^^ imm) |>.nextPC)
  | some (.orrR rd rn rm)    => some (s.setReg rd (s.regs rn ||| s.regs rm) |>.nextPC)
  | some (.eorR rd rn rm)    => some (s.setReg rd (s.regs rn ^^^ s.regs rm) |>.nextPC)
  | some (.lslR rd rn rm)    => some (s.setReg rd (s.regs rn <<< ((s.regs rm).toNat % 64)) |>.nextPC)
  | some (.asrR rd rn rm)    => some (s.setReg rd (BitVec.sshiftRight (s.regs rn) ((s.regs rm).toNat % 64)) |>.nextPC)
  -- array memory
  | some (.arrLd rd arr ix)  => some (s.setReg rd (s.arrayMem arr (s.regs ix)) |>.nextPC)
  | some (.arrSt arr ix rv)  => some (s.setArrayMem arr (s.regs ix) (s.regs rv) |>.nextPC)
  | some (.farrLd fd arr ix) => some (s.setFReg fd (s.arrayMem arr (s.regs ix)) |>.nextPC)
  | some (.farrSt arr ix fv) => some (s.setArrayMem arr (s.regs ix) (s.fregs fv) |>.nextPC)
  -- float moves / stack
  | some (.fmovToFP fd rn)   => some (s.setFReg fd (s.regs rn) |>.nextPC)
  | some (.fmovRR fd fn)     => some (s.setFReg fd (s.fregs fn) |>.nextPC)
  | some (.fldr fd off)      => some (s.setFReg fd (s.stack off) |>.nextPC)
  | some (.fstr fs off)      => some (s.setStack off (s.fregs fs) |>.nextPC)
  -- float arithmetic (native)
  | some (.faddR fd fn fm)   => some (s.setFReg fd (FloatBinOp.eval .fadd (s.fregs fn) (s.fregs fm)) |>.nextPC)
  | some (.fsubR fd fn fm)   => some (s.setFReg fd (FloatBinOp.eval .fsub (s.fregs fn) (s.fregs fm)) |>.nextPC)
  | some (.fmulR fd fn fm)   => some (s.setFReg fd (FloatBinOp.eval .fmul (s.fregs fn) (s.fregs fm)) |>.nextPC)
  | some (.fdivR fd fn fm)   => some (s.setFReg fd (FloatBinOp.eval .fdiv (s.fregs fn) (s.fregs fm)) |>.nextPC)
  | some (.fminR fd fn fm)   => some (s.setFReg fd (FloatBinOp.eval .fmin (s.fregs fn) (s.fregs fm)) |>.nextPC)
  | some (.fmaxR fd fn fm)   => some (s.setFReg fd (FloatBinOp.eval .fmax (s.fregs fn) (s.fregs fm)) |>.nextPC)
  | some (.fmaddR fd fn fm fa) =>
      some (s.setFReg fd (FloatBinOp.eval .fadd (s.fregs fa) (FloatBinOp.eval .fmul (s.fregs fn) (s.fregs fm))) |>.nextPC)
  | some (.fmsubR fd fn fm fa) =>
      some (s.setFReg fd (FloatBinOp.eval .fsub (s.fregs fa) (FloatBinOp.eval .fmul (s.fregs fn) (s.fregs fm))) |>.nextPC)
  | some (.fcmpR fn fm)      => some { s with flags := Flags.mk (s.fregs fn) (s.fregs fm), pc := s.pc + 1 }
  | some (.scvtf fd rn)      => some (s.setFReg fd (intToFloatBv (s.regs rn)) |>.nextPC)
  | some (.fcvtzs rd fn)     => some (s.setReg rd (floatToIntBv (s.fregs fn)) |>.nextPC)
  | some (.floatUnaryInstr op fd fn) =>
      if op.isNative then some (s.setFReg fd (op.eval (s.fregs fn)) |>.nextPC) else none
  | _ => none

/-- Soundness: whenever the evaluator yields a state, the verified relation
    agrees. So an `execStep`-vs-machine divergence is a genuine model bug. -/
theorem execStep_sound {prog : ArmProg} {s s' : ArmState} :
    execStep prog s = some s' → ArmStep prog s s' := by
  unfold execStep
  intro h
  split at h <;>
    first
    | contradiction
    | ( injection h with h <;> subst h <;>
        first
        | exact .mov _ _ ‹_›       | exact .movR _ _ ‹_›
        | exact .movz _ _ _ ‹_›    | exact .movk _ _ _ ‹_›
        | exact .ldr _ _ ‹_›       | exact .str _ _ ‹_›
        | exact .addR _ _ _ ‹_›    | exact .subR _ _ _ ‹_›
        | exact .mulR _ _ _ ‹_›    | exact .sdivR _ _ _ ‹_›
        | exact .cmpRR _ _ ‹_›     | exact .cmpRI _ _ ‹_›
        | exact .cset _ _ ‹_›      | exact .branch _ ‹_›
        | exact .andImm _ _ _ ‹_›  | exact .andR _ _ _ ‹_›
        | exact .eorImm _ _ _ ‹_›  | exact .orrR _ _ _ ‹_›
        | exact .eorR _ _ _ ‹_›
        | exact .lslR _ _ _ ‹_›    | exact .asrR _ _ _ ‹_›
        | exact .arrLd _ _ _ ‹_›   | exact .arrSt _ _ _ ‹_›
        | exact .farrLd _ _ _ ‹_›  | exact .farrSt _ _ _ ‹_›
        | exact .fmovToFP _ _ ‹_›  | exact .fmovRR _ _ ‹_›
        | exact .fldr _ _ ‹_›      | exact .fstr _ _ ‹_›
        | exact .faddR _ _ _ ‹_›   | exact .fsubR _ _ _ ‹_›
        | exact .fmulR _ _ _ ‹_›   | exact .fdivR _ _ _ ‹_›
        | exact .fminR _ _ _ ‹_›   | exact .fmaxR _ _ _ ‹_›
        | exact .fmaddR _ _ _ _ ‹_›| exact .fmsubR _ _ _ _ ‹_›
        | exact .fcmpRR _ _ ‹_›    | exact .scvtf _ _ ‹_›
        | exact .fcvtzs _ _ ‹_› )
    | ( split at h <;>
        (try simp only [Bool.not_eq_true] at *) <;>
        injection h with h <;> subst h <;>
        first
        | exact .cbz_taken _ _ ‹_› ‹_›  | exact .cbz_fall _ _ ‹_› ‹_›
        | exact .cbnz_taken _ _ ‹_› ‹_› | exact .cbnz_fall _ _ ‹_› ‹_›
        | exact .bCond_taken _ _ ‹_› ‹_›| exact .bCond_fall _ _ ‹_› ‹_› )
    | ( split at h <;>
        first
        | contradiction
        | ( injection h with h <;> subst h <;> exact .floatUnaryNative _ _ _ ‹_› ‹_› ) )

/-- Run the evaluator for `n` steps. -/
def execRun (prog : ArmProg) (s : ArmState) : Nat → Option ArmState
  | 0     => some s
  | n + 1 => match execStep prog s with
             | some s' => execRun prog s' n
             | none    => none

/-- Multi-step soundness: an `n`-step evaluator run is an `n`-step model run. -/
theorem execRun_sound {prog : ArmProg} {s s' : ArmState} {n : Nat} :
    execRun prog s n = some s' → ArmStepsN prog s s' n := by
  induction n generalizing s with
  | zero => intro h; simp only [execRun, Option.some.injEq] at h; subst h; rfl
  | succ n ih =>
    intro h
    simp only [execRun] at h
    split at h
    · rename_i s'' he
      exact ⟨s'', execStep_sound he, ih h⟩
    · exact absurd h (by simp)
