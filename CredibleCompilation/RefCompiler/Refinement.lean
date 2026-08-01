-- Copyright (c) 2026 Martin Rinard
import CredibleCompilation.RefCompiler.Metatheory

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000

/-!
# Compiler Correctness: Refinement

Program-level refinement theorems connecting the While-to-TAC compiler
(defined in WhileLang.lean) to source semantics.
-/
-- ============================================================
-- § 13. Helpers for backward refinement
-- ============================================================

/-- Source interpreter returns `none` iff it doesn't return `some`. -/
private theorem interp_none_iff (s : Stmt) (fuel : Nat) (σ : Store) (am : ArrayMem)
    (decls : List (ArrayName × Nat × VarTy)) :
    s.interp fuel σ am decls = none ↔ ¬ ∃ r, s.interp fuel σ am decls = some r := by
  constructor
  · intro h ⟨r, hr⟩; simp [h] at hr
  · intro h; by_contra hc; push_neg at hc; exact h (Option.ne_none_iff_exists'.mp hc)
/-- No steps from any error: error (div/bounds) is a terminal configuration. -/
private theorem RefStepsN.no_step_error {p : Prog} {n : Nat} {c d : Cfg}
    (hErr : c.isError) (h : RefStepsN p (n + 1) c d) : False := by
  cases h with
  | step s _ => exact Step.no_step_from_isError hErr s
/-- No steps from typeError: typeError is a terminal configuration. -/
private theorem RefStepsN.no_step_typeError {p : Prog} {n : Nat} {σ : Store} {c : Cfg}
    (h : RefStepsN p (n + 1) (Cfg.typeError σ _xam) c) : False := by
  cases h with
  | step s _ => exact Step.no_step_from_typeError s
/-- If execution takes unbounded steps through `run` configs, it cannot error. -/
theorem no_error_of_unbounded {p : Prog} {pc : Nat} {σ : Store}
    (hunbounded : ∀ N, ∃ n, n ≥ N ∧ ∃ pc' σ',
      RefStepsN p n (Cfg.run pc σ _xam) (Cfg.run pc' σ' _xam)) :
    ∀ c_err, c_err.isError → ¬ (p ⊩ Cfg.run pc σ _xam ⟶* c_err) := by
  intro c_err hErr herr
  obtain ⟨n, hn⟩ := herr.to_RefStepsN
  obtain ⟨m, hm, pc', σ'', hrun⟩ := hunbounded (n + 1)
  have hsuffix := RefStepsN.det_prefix hn hrun (by omega)
  have hmn : m - n = (m - n - 1) + 1 := by omega
  exact RefStepsN.no_step_error hErr (hmn ▸ hsuffix)
/-- Extract `StepsN` from an `IsInfiniteExec`: the first `n` steps of an
    infinite execution give a deterministic `n`-step path. -/
private theorem inf_exec_to_StepsN {p : Prog} {f : Nat → Cfg}
    (hinf : IsInfiniteExec p f) :
    ∀ n, StepsN p (f 0) (f n) n := by
  intro n; induction n with
  | zero => rfl
  | succ n ih => exact StepsN_extend ih (hinf.2 n)
-- ============================================================
-- § 14. Refinement for Program.compileToTAC (with init code)
-- ============================================================


/-- The body code from `compileStmt` is embedded in `prog.compileToTAC`. -/
private theorem whileToTAC_body_codeAt (prog : Program) :
    RC.CodeAt (compileStmt prog.body prog.decls.length 0
      (collectLabels prog.body prog.decls.length)).1
      prog.compileToTAC prog.decls.length := by
  intro i hi; exact Program.compileToTAC_body_getElem prog i hi
/-- **Forward halt** for `prog.compileToTAC`: if the source terminates safely,
    `prog.compileToTAC` halts with a matching store. -/
theorem whileToTAC_halt (prog : Program) (fuel : Nat) (σ' : Store) (am' : ArrayMem)
    (htcs : prog.wellFormed = true)
    (hinterp : prog.body.interp fuel prog.initStore ArrayMem.init prog.arrayDecls = some (σ', am'))
    (hsafe : prog.body.safe fuel prog.initStore ArrayMem.init prog.arrayDecls) :
    ∃ σ_tac, haltsWithResult prog.compileToTAC 0 prog.initStore σ_tac ArrayMem.init am' ∧
      (∀ v, v.isTmp = false → v.isFTmp = false → v.isBTmp = false → σ_tac v = σ' v) := by
  have htc := Program.wellFormed_typeCheck prog htcs
  let labels := collectLabels prog.body prog.decls.length
  have htmpfree := Program.typeCheck_tmpFree prog htc
  have hftmpfree : prog.body.ftmpFree := Program.typeCheck_ftmpFree prog htc
  have hbtmpfree : prog.body.btmpFree := Program.typeCheck_btmpFree prog htc
  have hNoGoto := Program.typeCheck_noGoto prog htcs
  have hts := Program.typeCheck_initStore_typedStore prog htc
  have htypedv := Program.typeCheck_typedVars prog htc prog.initStore ArrayMem.init hts fuel
  have hcode := whileToTAC_body_codeAt prog
  have hinit := Program.compileToTAC_initExec prog (Program.typeCheck_noDups prog htc)
  obtain ⟨σ_tac, hexec, hagree⟩ :=
    compileStmt_correct prog.body fuel prog.initStore σ' ArrayMem.init am' prog.decls.length 0
      prog.compileToTAC prog.initStore hinterp htmpfree hftmpfree hbtmpfree hNoGoto hsafe htypedv (fun _ _ _ _ => rfl)
      (labels := labels) hcode
  have hhalt_instr : prog.compileToTAC[prog.decls.length +
      (compileStmt prog.body prog.decls.length 0 labels).1.length]? = some .halt := by
    exact Program.compileToTAC_halt_getElem prog
  have hfull : FragExec prog.compileToTAC 0 prog.initStore
      (prog.decls.length + (compileStmt prog.body prog.decls.length 0 labels).1.length)
      σ_tac ArrayMem.init am' :=
    FragExec.trans' hinit hexec
  exact ⟨σ_tac, FragExec.toHalt hfull hhalt_instr, hagree⟩
/-- **Forward error** for `prog.compileToTAC`: if `¬safe`, the compiled program
    cannot halt (it reaches an error). -/
theorem whileToTAC_error (prog : Program) (fuel : Nat)
    (htcs : prog.wellFormed = true)
    (hunsafe : ¬ prog.body.safe fuel prog.initStore ArrayMem.init prog.arrayDecls) :
    ¬ ∃ σ_tac am_h, haltsWithResult prog.compileToTAC 0 prog.initStore σ_tac ArrayMem.init am_h := by
  have htc := Program.wellFormed_typeCheck prog htcs
  intro ⟨σ_tac, am_h, hhalt⟩
  let labels := collectLabels prog.body prog.decls.length
  have htmpfree := Program.typeCheck_tmpFree prog htc
  have hftmpfree : prog.body.ftmpFree := Program.typeCheck_ftmpFree prog htc
  have hbtmpfree : prog.body.btmpFree := Program.typeCheck_btmpFree prog htc
  have hts := Program.typeCheck_initStore_typedStore prog htc
  have htypedv := Program.typeCheck_typedVars prog htc prog.initStore ArrayMem.init hts fuel
  have hcode := whileToTAC_body_codeAt prog
  have hinit := Program.compileToTAC_initExec prog (Program.typeCheck_noDups prog htc)
  obtain ⟨pc_s, σ_s, am_s, c_err, hfrag, herror, hisErr, _⟩ :=
    compileStmt_unsafe prog.body fuel prog.initStore ArrayMem.init prog.decls.length 0
      prog.compileToTAC prog.initStore htmpfree hftmpfree hbtmpfree (Program.typeCheck_noGoto prog htcs) hunsafe htypedv (fun _ _ _ _ => rfl)
      (labels := labels) hcode
  exact error_run_no_halt (FragExec.trans' hinit hfrag) herror hisErr hhalt
/-- **Forward error reachability** for `prog.compileToTAC`: if `¬safe`, the
    compiled program reaches some runtime-error state (div or bounds). -/
theorem whileToTAC_reaches_error (prog : Program) (fuel : Nat)
    (htcs : prog.wellFormed = true)
    (hunsafe : ¬ prog.body.safe fuel prog.initStore ArrayMem.init prog.arrayDecls) :
    ∃ c_err, c_err.isError ∧
      (prog.compileToTAC ⊩ Cfg.run 0 prog.initStore ArrayMem.init ⟶* c_err) := by
  have htc := Program.wellFormed_typeCheck prog htcs
  let labels := collectLabels prog.body prog.decls.length
  have htmpfree := Program.typeCheck_tmpFree prog htc
  have hftmpfree : prog.body.ftmpFree := Program.typeCheck_ftmpFree prog htc
  have hbtmpfree : prog.body.btmpFree := Program.typeCheck_btmpFree prog htc
  have hts := Program.typeCheck_initStore_typedStore prog htc
  have htypedv := Program.typeCheck_typedVars prog htc prog.initStore ArrayMem.init hts fuel
  have hcode := whileToTAC_body_codeAt prog
  have hinit := Program.compileToTAC_initExec prog (Program.typeCheck_noDups prog htc)
  obtain ⟨pc_s, σ_s, am_s, c_err, hfrag, herror, hisErr, _⟩ :=
    compileStmt_unsafe prog.body fuel prog.initStore ArrayMem.init prog.decls.length 0
      prog.compileToTAC prog.initStore htmpfree hftmpfree hbtmpfree (Program.typeCheck_noGoto prog htcs) hunsafe htypedv (fun _ _ _ _ => rfl)
      (labels := labels) hcode
  exact ⟨c_err, hisErr, Steps.trans (FragExec.trans' hinit hfrag)
    (Steps.step herror Steps.refl)⟩

/-- Cause-faithful version: if the source has `unsafeDiv` at some fuel, the
    compiled program reaches a specific `Cfg.errorDiv` state. -/
theorem whileToTAC_reaches_errorDiv (prog : Program) (fuel : Nat)
    (htcs : prog.wellFormed = true)
    (hud : prog.body.unsafeDiv fuel prog.initStore ArrayMem.init prog.arrayDecls) :
    ∃ σ' am', prog.compileToTAC ⊩ Cfg.run 0 prog.initStore ArrayMem.init ⟶*
      Cfg.errorDiv σ' am' := by
  have htc := Program.wellFormed_typeCheck prog htcs
  let labels := collectLabels prog.body prog.decls.length
  have htmpfree := Program.typeCheck_tmpFree prog htc
  have hftmpfree : prog.body.ftmpFree := Program.typeCheck_ftmpFree prog htc
  have hbtmpfree : prog.body.btmpFree := Program.typeCheck_btmpFree prog htc
  have hts := Program.typeCheck_initStore_typedStore prog htc
  have htypedv := Program.typeCheck_typedVars prog htc prog.initStore ArrayMem.init hts fuel
  have hcode := whileToTAC_body_codeAt prog
  have hinit := Program.compileToTAC_initExec prog (Program.typeCheck_noDups prog htc)
  have hunsafe : ¬ prog.body.safe fuel prog.initStore ArrayMem.init prog.arrayDecls := by
    intro h
    exact ((Stmt.safe_iff_not_unsafe prog.body fuel prog.initStore ArrayMem.init
      prog.arrayDecls).mp h).1 hud
  obtain ⟨_pc_s, _σ_s, _am_s, c_err, hfrag, herror, _hisErr, _, hdivC, _⟩ :=
    compileStmt_unsafe prog.body fuel prog.initStore ArrayMem.init prog.decls.length 0
      prog.compileToTAC prog.initStore htmpfree hftmpfree hbtmpfree
      (Program.typeCheck_noGoto prog htcs) hunsafe htypedv (fun _ _ _ _ => rfl)
      (labels := labels) hcode
  obtain ⟨σ', am', heq⟩ := hdivC hud
  refine ⟨σ', am', ?_⟩
  rw [← heq]
  exact Steps.trans (FragExec.trans' hinit hfrag) (Steps.step herror Steps.refl)

/-- Cause-faithful version: if the source has `unsafeBounds` at some fuel, the
    compiled program reaches a specific `Cfg.errorBounds` state. -/
theorem whileToTAC_reaches_errorBounds (prog : Program) (fuel : Nat)
    (htcs : prog.wellFormed = true)
    (hub : prog.body.unsafeBounds fuel prog.initStore ArrayMem.init prog.arrayDecls) :
    ∃ σ' am', prog.compileToTAC ⊩ Cfg.run 0 prog.initStore ArrayMem.init ⟶*
      Cfg.errorBounds σ' am' := by
  have htc := Program.wellFormed_typeCheck prog htcs
  let labels := collectLabels prog.body prog.decls.length
  have htmpfree := Program.typeCheck_tmpFree prog htc
  have hftmpfree : prog.body.ftmpFree := Program.typeCheck_ftmpFree prog htc
  have hbtmpfree : prog.body.btmpFree := Program.typeCheck_btmpFree prog htc
  have hts := Program.typeCheck_initStore_typedStore prog htc
  have htypedv := Program.typeCheck_typedVars prog htc prog.initStore ArrayMem.init hts fuel
  have hcode := whileToTAC_body_codeAt prog
  have hinit := Program.compileToTAC_initExec prog (Program.typeCheck_noDups prog htc)
  have hunsafe : ¬ prog.body.safe fuel prog.initStore ArrayMem.init prog.arrayDecls := by
    intro h
    exact ((Stmt.safe_iff_not_unsafe prog.body fuel prog.initStore ArrayMem.init
      prog.arrayDecls).mp h).2 hub
  obtain ⟨_pc_s, _σ_s, _am_s, c_err, hfrag, herror, _hisErr, _, _, hboundsC⟩ :=
    compileStmt_unsafe prog.body fuel prog.initStore ArrayMem.init prog.decls.length 0
      prog.compileToTAC prog.initStore htmpfree hftmpfree hbtmpfree
      (Program.typeCheck_noGoto prog htcs) hunsafe htypedv (fun _ _ _ _ => rfl)
      (labels := labels) hcode
  obtain ⟨σ', am', heq⟩ := hboundsC hub
  refine ⟨σ', am', ?_⟩
  rw [← heq]
  exact Steps.trans (FragExec.trans' hinit hfrag) (Steps.step herror Steps.refl)
/-- **Forward no-halt for safe divergence** in `prog.compileToTAC`: if the source
    diverges safely, the compiled program doesn't halt. -/
theorem whileToTAC_diverge (prog : Program)
    (htcs : prog.wellFormed = true)
    (hdiv : ∀ fuel, prog.body.interp fuel prog.initStore ArrayMem.init prog.arrayDecls = none)
    (hsafe : ∀ fuel, prog.body.safe fuel prog.initStore ArrayMem.init prog.arrayDecls) :
    ¬ ∃ σ_tac am_h, haltsWithResult prog.compileToTAC 0 prog.initStore σ_tac ArrayMem.init am_h := by
  have htc := Program.wellFormed_typeCheck prog htcs
  intro ⟨σ_tac, am_h, hhalt⟩
  let labels := collectLabels prog.body prog.decls.length
  have htmpfree := Program.typeCheck_tmpFree prog htc
  have hftmpfree : prog.body.ftmpFree := Program.typeCheck_ftmpFree prog htc
  have hbtmpfree : prog.body.btmpFree := Program.typeCheck_btmpFree prog htc
  have hts := Program.typeCheck_initStore_typedStore prog htc
  have htypedv : ∀ fuel, prog.body.typedVars fuel prog.initStore ArrayMem.init prog.arrayDecls :=
    fun fuel => Program.typeCheck_typedVars prog htc prog.initStore ArrayMem.init hts fuel
  have hcode := whileToTAC_body_codeAt prog
  have hinit := Program.compileToTAC_initExec prog (Program.typeCheck_noDups prog htc)
  have hunbounded := compileStmt_diverges prog.body prog.initStore ArrayMem.init
    prog.decls.length 0 prog.compileToTAC prog.initStore
    htmpfree hftmpfree hbtmpfree (Program.typeCheck_noGoto prog htcs) hdiv hsafe htypedv (fun _ _ _ _ => rfl) (labels := labels) hcode
  have hunbounded' : ∀ N, ∃ n, n ≥ N ∧ ∃ pc' σ' am',
      RefStepsN prog.compileToTAC n (Cfg.run 0 prog.initStore ArrayMem.init)
        (Cfg.run pc' σ' am') := by
    obtain ⟨k_init, hk_init⟩ := hinit.to_RefStepsN
    intro N
    obtain ⟨n, hn, pc', σ', am', hsteps⟩ := hunbounded (N)
    exact ⟨k_init + n, by omega, pc', σ', am', RefStepsN.trans hk_init hsteps⟩
  exact no_halt_of_unbounded_am hunbounded' σ_tac am_h hhalt
/-- **Forward no-halt for unsafe divergence** in `prog.compileToTAC`. -/
private theorem whileToTAC_no_halt_diverge_unsafe (prog : Program)
    (htcs : prog.wellFormed = true)
    (hdiv : ∀ fuel, prog.body.interp fuel prog.initStore ArrayMem.init prog.arrayDecls = none) :
    ¬ ∃ σ_tac am_h, haltsWithResult prog.compileToTAC 0 prog.initStore σ_tac ArrayMem.init am_h := by
  by_cases hsafe : ∀ fuel, prog.body.safe fuel prog.initStore ArrayMem.init prog.arrayDecls
  · exact whileToTAC_diverge prog htcs hdiv hsafe
  · push_neg at hsafe
    obtain ⟨fuel, hunsafe⟩ := hsafe
    exact whileToTAC_error prog fuel htcs hunsafe
-- ============================================================
-- § 15. Backward refinement
-- ============================================================

/-- Specialised `program_behavior` that fixes the initial array memory to
    `ArrayMem.init` (which is what `has_behavior` always produces). -/
def program_behavior_init (p : Prog) (σ₀ : Store) (b : Behavior) : Prop :=
  match b with
  | .halts σ'       => ∃ am', haltsWithResult p 0 σ₀ σ' ArrayMem.init am'
  | .errorDiv σ'    => ∃ am', p ⊩ Cfg.run 0 σ₀ ArrayMem.init ⟶* Cfg.errorDiv σ' am'
  | .errorBounds σ' => ∃ am', p ⊩ Cfg.run 0 σ₀ ArrayMem.init ⟶* Cfg.errorBounds σ' am'
  | .typeErrors σ'  => ∃ am', p ⊩ Cfg.run 0 σ₀ ArrayMem.init ⟶* Cfg.typeError σ' am'
  | .diverges       => ∃ f : Nat → Cfg, IsInfiniteExec p f ∧ f 0 = Cfg.run 0 σ₀ ArrayMem.init

/-- `program_behavior_init` implies `program_behavior`. -/
theorem program_behavior_of_init {p : Prog} {σ₀ : Store} {b : Behavior}
    (h : program_behavior_init p σ₀ b) : program_behavior p σ₀ b := by
  cases b with
  | halts _ => obtain ⟨am', hh⟩ := h; exact ⟨ArrayMem.init, am', hh⟩
  | errorDiv _ => obtain ⟨am', hh⟩ := h; exact ⟨ArrayMem.init, am', hh⟩
  | errorBounds _ => obtain ⟨am', hh⟩ := h; exact ⟨ArrayMem.init, am', hh⟩
  | typeErrors _ => obtain ⟨am', hh⟩ := h; exact ⟨ArrayMem.init, am', hh⟩
  | diverges => exact h

/-- **`has_behavior` with the initial-`ArrayMem` invariant exposed.**  Every
    stepClosed TAC program has a well-defined behavior whose witnesses start
    from `ArrayMem.init`.  Mirrors `has_behavior`'s structure exactly —
    the by_cases dispatches are identical; only the halts/errors/typeErrors
    witnesses are packaged into `program_behavior_init` (fixing `am` to
    `ArrayMem.init`) instead of `program_behavior` (leaving `am`
    existential). -/
theorem has_behavior_init (p : Prog) (σ₀ : Store) (hclosed : StepClosedInBounds p) :
    ∃ b, program_behavior_init p σ₀ b := by
  -- Local clone of PropChecker's StepsN_to_Steps' (it's private there).
  have stepsN_to_steps : ∀ {c c' : Cfg} {n : Nat}, StepsN p c c' n → (p ⊩ c ⟶* c') := by
    intro c c' n h
    induction n generalizing c with
    | zero => exact h ▸ .refl
    | succ n ih => obtain ⟨c'', hs, hm⟩ := h; exact .step hs (ih hm)
  by_cases h : ∃ n σ' am', StepsN p (Cfg.run 0 σ₀ ArrayMem.init) (Cfg.halt σ' am') n
  · obtain ⟨n, σ', am', hn⟩ := h
    exact ⟨.halts σ', am', stepsN_to_steps hn⟩
  · by_cases hed : ∃ n σ' am', StepsN p (Cfg.run 0 σ₀ ArrayMem.init) (Cfg.errorDiv σ' am') n
    · obtain ⟨_, σ', am', hn⟩ := hed
      exact ⟨.errorDiv σ', am', stepsN_to_steps hn⟩
    · by_cases heb : ∃ n σ' am', StepsN p (Cfg.run 0 σ₀ ArrayMem.init) (Cfg.errorBounds σ' am') n
      · obtain ⟨_, σ', am', hn⟩ := heb
        exact ⟨.errorBounds σ', am', stepsN_to_steps hn⟩
      · by_cases hte : ∃ n σ' am', StepsN p (Cfg.run 0 σ₀ ArrayMem.init) (Cfg.typeError σ' am') n
        · obtain ⟨_, σ', am', hn⟩ := hte
          exact ⟨.typeErrors σ', am', stepsN_to_steps hn⟩
        · -- Diverges: reuse has_behavior's .diverges branch (same construction).
          have h_run : ∀ n, ∃ pc σ am, StepsN p (Cfg.run 0 σ₀ ArrayMem.init) (Cfg.run pc σ am) n ∧ pc < p.size := by
            intro n; induction n with
            | zero => exact ⟨0, σ₀, ArrayMem.init, rfl, hclosed.1⟩
            | succ n ih =>
              obtain ⟨pc, σ, am, hn, hpc⟩ := ih
              obtain ⟨c', hstep⟩ := Step.progress_untyped p pc σ am hpc
              match c', hstep with
              | .halt σ' am', s => exact absurd ⟨n+1, σ', am', StepsN_extend hn s⟩ h
              | .errorDiv σ' am', s => exact absurd ⟨n+1, σ', am', StepsN_extend hn s⟩ hed
              | .errorBounds σ' am', s => exact absurd ⟨n+1, σ', am', StepsN_extend hn s⟩ heb
              | .typeError σ' am', s => exact absurd ⟨n+1, σ', am', StepsN_extend hn s⟩ hte
              | .run pc' σ' am', s => exact ⟨pc', σ', am', StepsN_extend hn s, hclosed.2 pc pc' σ σ' am am' hpc s⟩
          have g_spec : ∀ n, ∃ c, StepsN p (Cfg.run 0 σ₀ ArrayMem.init) c n ∧ ∃ pc σ am, c = Cfg.run pc σ am := by
            intro n; obtain ⟨pc, σ, am, hn, _⟩ := h_run n; exact ⟨_, hn, pc, σ, am, rfl⟩
          let g := fun n => (g_spec n).choose
          have g_stepsN : ∀ n, StepsN p (Cfg.run 0 σ₀ ArrayMem.init) (g n) n :=
            fun n => (g_spec n).choose_spec.1
          refine ⟨.diverges, g, ⟨⟨σ₀, ArrayMem.init, ?_⟩, fun n => ?_⟩, ?_⟩
          · exact (g_stepsN 0).symm
          · exact StepsN_det (g_stepsN n) (StepsN_split_last (g_stepsN (n+1))).choose_spec.1 ▸
              (StepsN_split_last (g_stepsN (n+1))).choose_spec.2
          · exact (g_stepsN 0).symm

/-- Convert `StepsN` to `RefStepsN`. -/
private theorem StepsN_to_RefStepsN {p : Prog} {c c' : Cfg} {n : Nat}
    (h : StepsN p c c' n) : RefStepsN p n c c' := by
  induction n generalizing c with
  | zero => exact h ▸ .refl
  | succ n ih => obtain ⟨c'', hs, hr⟩ := h; exact .step hs (ih hr)

/-- If `prog.compileToTAC` has an infinite execution from the initial state, the
    source program is safe at every fuel.  Suppose ∃ fuel where source is unsafe
    (div or bounds); cause-faithful forward gives a finite compileToTAC trace
    ending in errorDiv/errorBounds, contradicting infinite execution. -/
theorem source_safe_of_compileToTAC_diverges (prog : Program) (htcs : prog.wellFormed = true)
    {g : Nat → Cfg}
    (hg : IsInfiniteExec prog.compileToTAC g)
    (hg0 : g 0 = Cfg.run 0 prog.initStore ArrayMem.init) :
    ∀ fuel, prog.body.safe fuel prog.initStore ArrayMem.init prog.arrayDecls := by
  intro fuel
  by_contra hns
  rw [Stmt.not_safe_iff_unsafeDiv_or_unsafeBounds] at hns
  -- Common machinery: take any finite reach-error trace, contradict infinite g
  have contradict : ∀ {c_err : Cfg} (_hErr : c_err.isError),
      (prog.compileToTAC ⊩ Cfg.run 0 prog.initStore ArrayMem.init ⟶* c_err) → False := by
    intro c_err hErr hreach
    obtain ⟨k, hk⟩ := hreach.to_RefStepsN
    have hN := inf_exec_to_StepsN hg (k + 1)
    rw [hg0] at hN
    have hRefN : RefStepsN prog.compileToTAC (k + 1)
        (Cfg.run 0 prog.initStore ArrayMem.init) (g (k + 1)) :=
      StepsN_to_RefStepsN hN
    have hsuffix := RefStepsN.det_prefix hk hRefN (by omega)
    have heq : (k + 1) - k = 0 + 1 := by omega
    exact RefStepsN.no_step_error hErr (heq ▸ hsuffix)
  rcases hns with hud | hub
  · obtain ⟨σ', am', hreach⟩ := whileToTAC_reaches_errorDiv prog fuel htcs hud
    exact contradict (by simp [Cfg.isError]) hreach
  · obtain ⟨σ', am', hreach⟩ := whileToTAC_reaches_errorBounds prog fuel htcs hub
    exact contradict (by simp [Cfg.isError]) hreach

/-- Cast `RefStepsN` along an equality of step counts. -/
private theorem refStepsN_cast' {p : Prog} {n n' : Nat} {c c' : Cfg}
    (h : RefStepsN p n c c') (heq : n = n') : RefStepsN p n' c c' := heq ▸ h

/-- Get `some` witness from non-`none` option. -/
private theorem Option.some_of_ne_none {o : Option α} (h : o ≠ none) : ∃ a, o = some a := by
  cases o with
  | none => exact absurd rfl h
  | some a => exact ⟨a, rfl⟩

/-- Backward refinement: any observable behavior of `prog.compileToTAC` starting from
    `ArrayMem.init` corresponds to a behavior of the source program.
    For halting programs, both store (on non-temporary variables) and array memory match. -/
theorem whileToTAC_refinement (prog : Program) (htcs : prog.wellFormed = true)
    (b : Behavior)
    (hbeh : program_behavior_init prog.compileToTAC prog.initStore b) :
    match b with
    | .halts σ_tac => ∃ fuel σ' am_h am', prog.interp fuel = some (σ', am') ∧
        haltsWithResult prog.compileToTAC 0 prog.initStore σ_tac ArrayMem.init am_h ∧
        am_h = am' ∧
        ∀ v, v.isTmp = false → v.isFTmp = false → v.isBTmp = false → σ_tac v = σ' v
    | .errorDiv _ => ∃ fuel,
        prog.body.unsafeDiv fuel prog.initStore ArrayMem.init prog.arrayDecls
    | .errorBounds _ => ∃ fuel,
        prog.body.unsafeBounds fuel prog.initStore ArrayMem.init prog.arrayDecls
    | .typeErrors _ => False
    | .diverges => ∀ fuel, prog.interp fuel = none := by
  have htc := Program.wellFormed_typeCheck prog htcs
  cases b with
  | halts σ_tac =>
    simp only [program_behavior_init] at hbeh
    obtain ⟨am_h, hhalt⟩ := hbeh
    -- Source either terminates at some fuel or diverges at all fuels
    by_cases hdiv : ∀ fuel, prog.body.interp fuel prog.initStore ArrayMem.init prog.arrayDecls = none
    · -- Source diverges → compiled program cannot halt → contradiction
      exact absurd ⟨σ_tac, am_h, hhalt⟩ (whileToTAC_no_halt_diverge_unsafe prog htcs hdiv)
    · -- Source terminates at some fuel
      push_neg at hdiv
      obtain ⟨fuel, hfuel⟩ := hdiv
      obtain ⟨r, hinterp⟩ := Option.some_of_ne_none hfuel
      obtain ⟨σ', am'⟩ := r
      by_cases hsafe : prog.body.safe fuel prog.initStore ArrayMem.init prog.arrayDecls
      · -- Source terminates safely → forward halt → determinism gives store+array match
        obtain ⟨σ_fwd, hhalt_fwd, hagree⟩ :=
          whileToTAC_halt prog fuel σ' am' htcs hinterp hsafe
        obtain ⟨heq_σ, heq_am⟩ := haltsWithResult_unique hhalt hhalt_fwd
        subst heq_σ
        exact ⟨fuel, σ', am_h, am', hinterp, hhalt, heq_am, hagree⟩
      · -- not safe → compiled cannot halt → contradiction
        exact absurd ⟨σ_tac, am_h, hhalt⟩ (whileToTAC_error prog fuel htcs hsafe)
  | errorDiv σ_e =>
    simp only [program_behavior_init] at hbeh
    obtain ⟨am_e, herr_d⟩ := hbeh
    have ⟨c_err, hisErr, herr⟩ : ∃ c, c.isError ∧
        (prog.compileToTAC ⊩ Cfg.run 0 prog.initStore ArrayMem.init ⟶* c) :=
      ⟨_, by simp [Cfg.isError], herr_d⟩
    by_contra hall_div
    push_neg at hall_div
    by_cases hub : ∃ fuel, prog.body.unsafeBounds fuel prog.initStore ArrayMem.init prog.arrayDecls
    · -- Cross-cause: source is unsafeBounds, compile reaches errorBounds, contradicts errorDiv
      obtain ⟨fuel_b, hub'⟩ := hub
      obtain ⟨σ', am', hcompile_b⟩ := whileToTAC_reaches_errorBounds prog fuel_b htcs hub'
      have ed_terminal : ∀ d, ¬ Step prog.compileToTAC (Cfg.errorDiv σ_e am_e) d :=
        fun _ h => Step.no_step_from_isError (by simp [Cfg.isError]) h
      have eb_terminal : ∀ d, ¬ Step prog.compileToTAC (Cfg.errorBounds σ' am') d :=
        fun _ h => Step.no_step_from_isError (by simp [Cfg.isError]) h
      exact Cfg.noConfusion (Steps.stuck_det herr_d hcompile_b ed_terminal eb_terminal)
    · push_neg at hub
      have hall : ∀ fuel, prog.body.safe fuel prog.initStore ArrayMem.init prog.arrayDecls := by
        intro fuel
        exact (Stmt.safe_iff_not_unsafe prog.body fuel prog.initStore ArrayMem.init
          prog.arrayDecls).mpr ⟨hall_div fuel, hub fuel⟩
      by_cases hdiv : ∀ fuel, prog.body.interp fuel prog.initStore ArrayMem.init prog.arrayDecls = none
      · have htmpfree := Program.typeCheck_tmpFree prog htc
        have hftmpfree : prog.body.ftmpFree := Program.typeCheck_ftmpFree prog htc
        have hbtmpfree : prog.body.btmpFree := Program.typeCheck_btmpFree prog htc
        have hts := Program.typeCheck_initStore_typedStore prog htc
        have htypedv : ∀ fuel, prog.body.typedVars fuel prog.initStore ArrayMem.init prog.arrayDecls :=
          fun fuel => Program.typeCheck_typedVars prog htc prog.initStore ArrayMem.init hts fuel
        let labels := collectLabels prog.body prog.decls.length
        have hcode := whileToTAC_body_codeAt prog
        have hinit := Program.compileToTAC_initExec prog (Program.typeCheck_noDups prog htc)
        have hunbounded := compileStmt_diverges prog.body prog.initStore ArrayMem.init
          prog.decls.length 0 prog.compileToTAC prog.initStore
          htmpfree hftmpfree hbtmpfree (Program.typeCheck_noGoto prog htcs) hdiv hall htypedv (fun _ _ _ _ => rfl) (labels := labels) hcode
        have hunbounded' : ∀ N, ∃ n, n ≥ N ∧ ∃ pc' σ' am',
            RefStepsN prog.compileToTAC n (Cfg.run 0 prog.initStore ArrayMem.init)
              (Cfg.run pc' σ' am') := by
          obtain ⟨k_init, hk_init⟩ := hinit.to_RefStepsN
          intro N
          obtain ⟨n, hn, pc', σ', am', hsteps⟩ := hunbounded (N)
          exact ⟨k_init + n, by omega, pc', σ', am', RefStepsN.trans hk_init hsteps⟩
        obtain ⟨k_err, hk_err⟩ := herr.to_RefStepsN
        obtain ⟨m, hm, _pc', _σ'', _am'', hrun⟩ := hunbounded' (k_err + 1)
        have hsuffix := RefStepsN.det_prefix hk_err hrun (by omega)
        have hmk : m - k_err = (m - k_err - 1) + 1 := by omega
        exact RefStepsN.no_step_error hisErr (hmk ▸ hsuffix)
      · push_neg at hdiv
        obtain ⟨fuel, hfuel⟩ := hdiv
        obtain ⟨r, hinterp⟩ := Option.some_of_ne_none hfuel
        obtain ⟨σ', am'⟩ := r
        obtain ⟨σ_fwd, hhalt_fwd, _⟩ :=
          whileToTAC_halt prog fuel σ' am' htcs hinterp (hall fuel)
        have halt_terminal : ∀ d, ¬ Step prog.compileToTAC (Cfg.halt σ_fwd am') d :=
          fun _ h => Step.no_step_from_halt h
        have err_terminal : ∀ d, ¬ Step prog.compileToTAC c_err d :=
          fun _ h => Step.no_step_from_isError hisErr h
        have heq := Steps.stuck_det hhalt_fwd herr halt_terminal err_terminal
        cases c_err <;> simp [Cfg.isError] at hisErr <;> exact Cfg.noConfusion heq
  | errorBounds σ_e =>
    simp only [program_behavior_init] at hbeh
    obtain ⟨am_e, herr_b⟩ := hbeh
    have ⟨c_err, hisErr, herr⟩ : ∃ c, c.isError ∧
        (prog.compileToTAC ⊩ Cfg.run 0 prog.initStore ArrayMem.init ⟶* c) :=
      ⟨_, by simp [Cfg.isError], herr_b⟩
    by_contra hall_bounds
    push_neg at hall_bounds
    by_cases hud : ∃ fuel, prog.body.unsafeDiv fuel prog.initStore ArrayMem.init prog.arrayDecls
    · -- Cross-cause: source is unsafeDiv, compile reaches errorDiv, contradicts errorBounds
      obtain ⟨fuel_d, hud'⟩ := hud
      obtain ⟨σ', am', hcompile_d⟩ := whileToTAC_reaches_errorDiv prog fuel_d htcs hud'
      have eb_terminal : ∀ d, ¬ Step prog.compileToTAC (Cfg.errorBounds σ_e am_e) d :=
        fun _ h => Step.no_step_from_isError (by simp [Cfg.isError]) h
      have ed_terminal : ∀ d, ¬ Step prog.compileToTAC (Cfg.errorDiv σ' am') d :=
        fun _ h => Step.no_step_from_isError (by simp [Cfg.isError]) h
      exact Cfg.noConfusion (Steps.stuck_det herr_b hcompile_d eb_terminal ed_terminal)
    · push_neg at hud
      have hall : ∀ fuel, prog.body.safe fuel prog.initStore ArrayMem.init prog.arrayDecls := by
        intro fuel
        exact (Stmt.safe_iff_not_unsafe prog.body fuel prog.initStore ArrayMem.init
          prog.arrayDecls).mpr ⟨hud fuel, hall_bounds fuel⟩
      by_cases hdiv : ∀ fuel, prog.body.interp fuel prog.initStore ArrayMem.init prog.arrayDecls = none
      · have htmpfree := Program.typeCheck_tmpFree prog htc
        have hftmpfree : prog.body.ftmpFree := Program.typeCheck_ftmpFree prog htc
        have hbtmpfree : prog.body.btmpFree := Program.typeCheck_btmpFree prog htc
        have hts := Program.typeCheck_initStore_typedStore prog htc
        have htypedv : ∀ fuel, prog.body.typedVars fuel prog.initStore ArrayMem.init prog.arrayDecls :=
          fun fuel => Program.typeCheck_typedVars prog htc prog.initStore ArrayMem.init hts fuel
        let labels := collectLabels prog.body prog.decls.length
        have hcode := whileToTAC_body_codeAt prog
        have hinit := Program.compileToTAC_initExec prog (Program.typeCheck_noDups prog htc)
        have hunbounded := compileStmt_diverges prog.body prog.initStore ArrayMem.init
          prog.decls.length 0 prog.compileToTAC prog.initStore
          htmpfree hftmpfree hbtmpfree (Program.typeCheck_noGoto prog htcs) hdiv hall htypedv (fun _ _ _ _ => rfl) (labels := labels) hcode
        have hunbounded' : ∀ N, ∃ n, n ≥ N ∧ ∃ pc' σ' am',
            RefStepsN prog.compileToTAC n (Cfg.run 0 prog.initStore ArrayMem.init)
              (Cfg.run pc' σ' am') := by
          obtain ⟨k_init, hk_init⟩ := hinit.to_RefStepsN
          intro N
          obtain ⟨n, hn, pc', σ', am', hsteps⟩ := hunbounded (N)
          exact ⟨k_init + n, by omega, pc', σ', am', RefStepsN.trans hk_init hsteps⟩
        obtain ⟨k_err, hk_err⟩ := herr.to_RefStepsN
        obtain ⟨m, hm, _pc', _σ'', _am'', hrun⟩ := hunbounded' (k_err + 1)
        have hsuffix := RefStepsN.det_prefix hk_err hrun (by omega)
        have hmk : m - k_err = (m - k_err - 1) + 1 := by omega
        exact RefStepsN.no_step_error hisErr (hmk ▸ hsuffix)
      · push_neg at hdiv
        obtain ⟨fuel, hfuel⟩ := hdiv
        obtain ⟨r, hinterp⟩ := Option.some_of_ne_none hfuel
        obtain ⟨σ', am'⟩ := r
        obtain ⟨σ_fwd, hhalt_fwd, _⟩ :=
          whileToTAC_halt prog fuel σ' am' htcs hinterp (hall fuel)
        have halt_terminal : ∀ d, ¬ Step prog.compileToTAC (Cfg.halt σ_fwd am') d :=
          fun _ h => Step.no_step_from_halt h
        have err_terminal : ∀ d, ¬ Step prog.compileToTAC c_err d :=
          fun _ h => Step.no_step_from_isError hisErr h
        have heq := Steps.stuck_det hhalt_fwd herr halt_terminal err_terminal
        cases c_err <;> simp [Cfg.isError] at hisErr <;> exact Cfg.noConfusion heq
  | typeErrors σ_te =>
    simp only [program_behavior_init] at hbeh
    obtain ⟨am_te, hte⟩ := hbeh
    by_cases hdiv : ∀ fuel, prog.body.interp fuel prog.initStore ArrayMem.init prog.arrayDecls = none
    · by_cases hsafe_all : ∀ fuel, prog.body.safe fuel prog.initStore ArrayMem.init prog.arrayDecls
      · -- Source diverges safely → unbounded → typeError contradicts unbounded
        have htmpfree := Program.typeCheck_tmpFree prog htc
        have hftmpfree : prog.body.ftmpFree := Program.typeCheck_ftmpFree prog htc
        have hbtmpfree : prog.body.btmpFree := Program.typeCheck_btmpFree prog htc
        have hts := Program.typeCheck_initStore_typedStore prog htc
        have htypedv : ∀ fuel, prog.body.typedVars fuel prog.initStore ArrayMem.init prog.arrayDecls :=
          fun fuel => Program.typeCheck_typedVars prog htc prog.initStore ArrayMem.init hts fuel
        let labels := collectLabels prog.body prog.decls.length
        have hcode := whileToTAC_body_codeAt prog
        have hinit := Program.compileToTAC_initExec prog (Program.typeCheck_noDups prog htc)
        have hunbounded := compileStmt_diverges prog.body prog.initStore ArrayMem.init
          prog.decls.length 0 prog.compileToTAC prog.initStore
          htmpfree hftmpfree hbtmpfree (Program.typeCheck_noGoto prog htcs) hdiv hsafe_all htypedv (fun _ _ _ _ => rfl) (labels := labels) hcode
        have hunbounded' : ∀ N, ∃ n, n ≥ N ∧ ∃ pc' σ' am',
            RefStepsN prog.compileToTAC n (Cfg.run 0 prog.initStore ArrayMem.init)
              (Cfg.run pc' σ' am') := by
          obtain ⟨k_init, hk_init⟩ := hinit.to_RefStepsN
          intro N
          obtain ⟨n, hn, pc', σ', am', hsteps⟩ := hunbounded (N)
          exact ⟨k_init + n, by omega, pc', σ', am', RefStepsN.trans hk_init hsteps⟩
        obtain ⟨k_te, hk_te⟩ := hte.to_RefStepsN
        obtain ⟨m, hm, _pc', _σ'', _am'', hrun⟩ := hunbounded' (k_te + 1)
        have hsuffix := RefStepsN.det_prefix hk_te hrun (by omega)
        have hmk : m - k_te = (m - k_te - 1) + 1 := by omega
        exact RefStepsN.no_step_typeError (hmk ▸ hsuffix)
      · -- not all safe → error reachable → typeError contradicts error
        push_neg at hsafe_all
        obtain ⟨fuel, hunsafe⟩ := hsafe_all
        obtain ⟨c_err, hisErr, herr⟩ := whileToTAC_reaches_error prog fuel htcs hunsafe
        have err_terminal : ∀ d, ¬ Step prog.compileToTAC c_err d :=
          fun _ h => Step.no_step_from_isError hisErr h
        have te_terminal : ∀ d, ¬ Step prog.compileToTAC (Cfg.typeError σ_te am_te) d :=
          fun _ h => Step.no_step_from_typeError h
        have heq := Steps.stuck_det herr hte err_terminal te_terminal
        cases c_err <;> simp [Cfg.isError] at hisErr <;> exact Cfg.noConfusion heq
    · -- Source terminates at some fuel
      push_neg at hdiv
      obtain ⟨fuel, hfuel⟩ := hdiv
      obtain ⟨r, hinterp⟩ := Option.some_of_ne_none hfuel
      obtain ⟨σ', am'⟩ := r
      by_cases hsafe : prog.body.safe fuel prog.initStore ArrayMem.init prog.arrayDecls
      · obtain ⟨σ_fwd, hhalt_fwd, _⟩ :=
          whileToTAC_halt prog fuel σ' am' htcs hinterp hsafe
        have halt_terminal : ∀ d, ¬ Step prog.compileToTAC (Cfg.halt σ_fwd am') d :=
          fun _ h => Step.no_step_from_halt h
        have te_terminal : ∀ d, ¬ Step prog.compileToTAC (Cfg.typeError σ_te am_te) d :=
          fun _ h => Step.no_step_from_typeError h
        exact Cfg.noConfusion (Steps.stuck_det hhalt_fwd hte halt_terminal te_terminal)
      · obtain ⟨c_err, hisErr, herr⟩ := whileToTAC_reaches_error prog fuel htcs hsafe
        have err_terminal : ∀ d, ¬ Step prog.compileToTAC c_err d :=
          fun _ h => Step.no_step_from_isError hisErr h
        have te_terminal : ∀ d, ¬ Step prog.compileToTAC (Cfg.typeError σ_te am_te) d :=
          fun _ h => Step.no_step_from_typeError h
        have heq := Steps.stuck_det herr hte err_terminal te_terminal
        cases c_err <;> simp [Cfg.isError] at hisErr <;> exact Cfg.noConfusion heq
  | diverges =>
    simp only [program_behavior_init] at hbeh
    obtain ⟨f, hinf, hf0⟩ := hbeh
    intro fuel
    show prog.body.interp fuel prog.initStore ArrayMem.init prog.arrayDecls = none
    by_contra hfuel
    have ⟨r, hinterp⟩ : ∃ r, prog.body.interp fuel prog.initStore ArrayMem.init prog.arrayDecls = some r := by
      by_contra h
      exact hfuel ((interp_none_iff _ _ _ _ _).mpr h)
    obtain ⟨σ', am'⟩ := r
    by_cases hsafe : prog.body.safe fuel prog.initStore ArrayMem.init prog.arrayDecls
    · -- safe → forward halt → contradicts infinite exec
      obtain ⟨σ_fwd, hhalt_fwd, _⟩ :=
        whileToTAC_halt prog fuel σ' am' htcs hinterp hsafe
      obtain ⟨k, hk⟩ := hhalt_fwd.to_RefStepsN
      have hstepsN := inf_exec_to_StepsN hinf (k + 1)
      rw [hf0] at hstepsN
      have hstepsR := StepsN_to_RefStepsN hstepsN
      have hsuffix := RefStepsN.det_prefix hk hstepsR (by omega)
      have hmk : (k + 1) - k = ((k + 1) - k - 1) + 1 := by omega
      exact RefStepsN.no_step_halt (hmk ▸ hsuffix)
    · -- not safe → forward error → contradicts infinite exec
      obtain ⟨c_err, hisErr, herr⟩ := whileToTAC_reaches_error prog fuel htcs hsafe
      obtain ⟨k, hk⟩ := herr.to_RefStepsN
      have hstepsN := inf_exec_to_StepsN hinf (k + 1)
      rw [hf0] at hstepsN
      have hstepsR := StepsN_to_RefStepsN hstepsN
      have hsuffix := RefStepsN.det_prefix hk hstepsR (by omega)
      have hmk : (k + 1) - k = ((k + 1) - k - 1) + 1 := by omega
      exact RefStepsN.no_step_error hisErr (hmk ▸ hsuffix)
