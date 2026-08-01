-- Copyright (c) 2026 Martin Rinard
import CredibleCompilation.CodeGen
import CredibleCompilation.SoundnessBridge
import CredibleCompilation.RefCompiler.Refinement

/-!
# Pipeline Correctness

End-to-end correctness for the credible compilation pipeline:
While source → TAC → certified optimizations → ARM.

The theorems are parameterized over an arbitrary list of certificate-checked
optimization passes. Each pass either succeeds (certificate validates) and
transforms the program, or fails and leaves the program unchanged.

## Key theorems
- `applyPasses_preserves_halt_am`: pipeline preserves halting behavior with AM
- `applyPasses_preserves_error_am`: pipeline preserves error behavior with AM
- `while_to_arm_correctness`: full While→ARM for halting programs
- `while_to_arm_error_preservation`: full While→ARM for error programs
- `while_to_arm_divergence_preservation`: full While→ARM for diverging programs
-/

-- ============================================================
-- § 0. Code-equality implies behavioral equivalence
-- ============================================================

/-- `p[pc]?` depends only on `p.code`. -/
private theorem getElem?_of_code_eq {p q : Prog} (h : p.code = q.code) (pc : Nat) :
    p[pc]? = q[pc]? := by
  simp [Prog.getElem?_code, h]

/-- `arraySizeBv` depends only on `arrayDecls`. -/
private theorem arraySizeBv_of_decls_eq {p q : Prog}
    (h : p.arrayDecls = q.arrayDecls) (arr : ArrayName) :
    Prog.arraySizeBv p arr = Prog.arraySizeBv q arr := by
  unfold Prog.arraySizeBv; rw [h]

/-- A single step transfers across programs with the same code and arrayDecls. -/
theorem Step_of_code_arrayDecls_eq {p q : Prog}
    (hc : p.code = q.code) (ha : p.arrayDecls = q.arrayDecls)
    {c c' : Cfg} (hs : Step p c c') : Step q c c' := by
  have hg : ∀ pc, p[pc]? = q[pc]? := getElem?_of_code_eq hc
  have has : ∀ arr, Prog.arraySizeBv p arr = Prog.arraySizeBv q arr :=
    arraySizeBv_of_decls_eq ha
  cases hs with
  | const h => exact .const (hg _ ▸ h)
  | copy h => exact .copy (hg _ ▸ h)
  | binop h hy hz hs => exact .binop (hg _ ▸ h) hy hz hs
  | boolop h => exact .boolop (hg _ ▸ h)
  | goto h => exact .goto (hg _ ▸ h)
  | iftrue h hb => exact .iftrue (hg _ ▸ h) hb
  | iffall h hb => exact .iffall (hg _ ▸ h) hb
  | halt h => exact .halt (hg _ ▸ h)
  | binop_divByZero h hy hz hn => exact .binop_divByZero (hg _ ▸ h) hy hz hn
  | binop_typeError h ht => exact .binop_typeError (hg _ ▸ h) ht
  | arrLoad h hi hb => exact .arrLoad (hg _ ▸ h) hi (has _ ▸ hb)
  | arrStore h hi ht hb => exact .arrStore (hg _ ▸ h) hi ht (has _ ▸ hb)
  | arrLoad_boundsError h hi hb => exact .arrLoad_boundsError (hg _ ▸ h) hi (has _ ▸ hb)
  | arrStore_boundsError h hi ht hb => exact .arrStore_boundsError (hg _ ▸ h) hi ht (has _ ▸ hb)
  | arrLoad_typeError h ht => exact .arrLoad_typeError (hg _ ▸ h) ht
  | arrStore_typeError h ht => exact .arrStore_typeError (hg _ ▸ h) ht
  | fbinop h hy hz => exact .fbinop (hg _ ▸ h) hy hz
  | fbinop_typeError h ht => exact .fbinop_typeError (hg _ ▸ h) ht
  | fternop h hy hz hw => exact .fternop (hg _ ▸ h) hy hz hw
  | fternop_typeError h ht => exact .fternop_typeError (hg _ ▸ h) ht
  | intToFloat h hy => exact .intToFloat (hg _ ▸ h) hy
  | intToFloat_typeError h ht => exact .intToFloat_typeError (hg _ ▸ h) ht
  | floatToInt h hy => exact .floatToInt (hg _ ▸ h) hy
  | floatToInt_typeError h ht => exact .floatToInt_typeError (hg _ ▸ h) ht
  | floatUnary h hy => exact .floatUnary (hg _ ▸ h) hy
  | floatUnary_typeError h ht => exact .floatUnary_typeError (hg _ ▸ h) ht
  | print h => exact .print (hg _ ▸ h)
  | printInt h => exact .printInt (hg _ ▸ h)
  | printBool h => exact .printBool (hg _ ▸ h)
  | printFloat h => exact .printFloat (hg _ ▸ h)
  | printString h => exact .printString (hg _ ▸ h)

/-- Multi-step transfers across programs with the same code and arrayDecls. -/
theorem Steps_of_code_arrayDecls_eq {p q : Prog}
    (hc : p.code = q.code) (ha : p.arrayDecls = q.arrayDecls)
    {c c' : Cfg} (hs : Steps p c c') : Steps q c c' := by
  induction hs with
  | refl => exact .refl
  | step h _ ih => exact .step (Step_of_code_arrayDecls_eq hc ha h) ih

/-- `IsInfiniteExec` transfers across code-equal programs. -/
theorem IsInfiniteExec_of_code_eq {p q : Prog}
    (hc : p.code = q.code) (ha : p.arrayDecls = q.arrayDecls)
    {f} (h : IsInfiniteExec p f) : IsInfiniteExec q f :=
  ⟨h.1, fun n => Step_of_code_arrayDecls_eq hc ha (h.2 n)⟩

-- ============================================================
-- § 1. applyPass soundness
-- ============================================================

/-- If `applyPass` returns `.ok p'`, then the checker accepted the certificate
    (with the enforced tyCtx), the output is `(pass p).trans`, and orig matches
    input on code/obs/arr. -/
theorem applyPass_sound {name : String} {tyCtx : TyCtx} {pass : Prog → ECertificate} {p p' : Prog}
    (h : applyPass name tyCtx pass p = .ok p') :
    checkCertificateExec { pass p with tyCtx := tyCtx } = true ∧
    (pass p).trans = p' ∧
    (pass p).orig.code = p.code ∧
    (pass p).orig.observable = p.observable ∧
    (pass p).orig.arrayDecls = p.arrayDecls := by
  simp only [applyPass] at h
  by_cases hOrig : (pass p).orig.code != p.code || (pass p).orig.observable != p.observable ||
      (pass p).orig.arrayDecls != p.arrayDecls
  · simp [hOrig] at h
  · simp [hOrig] at h
    by_cases hCheck : checkCertificateExec { pass p with tyCtx := tyCtx }
    · simp [hCheck] at h
      simp [not_or, bne_iff_ne, ne_eq] at hOrig
      obtain ⟨⟨hc, hobs⟩, harr⟩ := hOrig
      exact ⟨hCheck, h, hc, hobs, harr⟩
    · simp [hCheck] at h

-- ============================================================
-- § 2. Single-pass halt/error/diverge with AM preservation
-- ============================================================

/-- Extract same_observable from checkCertificateExec. -/
private theorem same_obs_of_check (cert : ECertificate)
    (h : checkCertificateExec cert = true) :
    cert.orig.observable = cert.trans.observable := by
  unfold checkCertificateExec at h
  simp only [Bool.and_eq_true] at h
  exact beq_iff_eq.mp h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2

/-- A single optimization pass preserves halting with fixed initial AM.
    The final AM is the same for orig and trans (via determinism). -/
private theorem applyPass_preserves_halt_am {name : String} {tyCtx : TyCtx}
    {pass : Prog → ECertificate} {p p' : Prog}
    (h : applyPass name tyCtx pass p = .ok p')
    (σ₀ : Store) (hts : TypedStore tyCtx σ₀)
    {σ' : Store} {am₀ am' : ArrayMem}
    (hh : haltsWithResult p' 0 σ₀ σ' am₀ am') :
    ∃ σ_orig, haltsWithResult p 0 σ₀ σ_orig am₀ am' ∧
      ∀ v ∈ p.observable, σ' v = σ_orig v := by
  obtain ⟨hcheck, hTrans, hOrigCode, hOrigObs, hOrigArr⟩ := applyPass_sound h
  let cert := { pass p with tyCtx := tyCtx }
  have hvalid := soundness_bridge cert hcheck
  have hTransP : (toPCertificate cert).trans = p' := by simp [toPCertificate]; exact hTrans
  have hts' : TypedStore (toPCertificate cert).tyCtx σ₀ := by
    simp [toPCertificate]; exact hts
  have hhalt_cert : ∃ am', haltsWithResult (toPCertificate cert).trans 0 σ₀ σ' am₀ am' :=
    ⟨am', hTransP ▸ hh⟩
  obtain ⟨σ_o, am_f, hhalt_o, hhalt_t, hobs⟩ :=
    soundness_halt (toPCertificate cert) hvalid σ₀ σ' hts' hhalt_cert
  have ham : am_f = am' :=
    (haltsWithResult_unique (hTransP ▸ hhalt_t : haltsWithResult p' 0 σ₀ σ' am₀ am_f) hh).2
  subst ham
  have hOC : (toPCertificate cert).orig.code = p.code := by simp [toPCertificate]; exact hOrigCode
  have hOA : (toPCertificate cert).orig.arrayDecls = p.arrayDecls := by simp [toPCertificate]; exact hOrigArr
  have hOO : (toPCertificate cert).observable = p.observable := by
    simp [toPCertificate, PCertificate.observable]; exact hOrigObs
  exact ⟨σ_o, Steps_of_code_arrayDecls_eq hOC hOA hhalt_o,
    fun v hv => hobs v (hOO ▸ hv)⟩

/-- A single optimization pass preserves errors with fixed initial AM.
    Cause is preserved: div-by-zero stays div-by-zero, bounds stays bounds. -/
private theorem applyPass_preserves_error_am {name : String} {tyCtx : TyCtx}
    {pass : Prog → ECertificate} {p p' : Prog}
    (h : applyPass name tyCtx pass p = .ok p')
    (σ₀ : Store) (hts : TypedStore tyCtx σ₀)
    {σ' : Store} {am₀ am' : ArrayMem}
    (hbeh : (p' ⊩ Cfg.run 0 σ₀ am₀ ⟶* Cfg.errorDiv σ' am') ∨
            (p' ⊩ Cfg.run 0 σ₀ am₀ ⟶* Cfg.errorBounds σ' am')) :
    ∃ σ_o am_o', (p ⊩ Cfg.run 0 σ₀ am₀ ⟶* Cfg.errorDiv σ_o am_o') ∨
                 (p ⊩ Cfg.run 0 σ₀ am₀ ⟶* Cfg.errorBounds σ_o am_o') := by
  obtain ⟨hcheck, hTrans, hOrigCode, _, hOrigArr⟩ := applyPass_sound h
  let cert := { pass p with tyCtx := tyCtx }
  have hvalid := soundness_bridge cert hcheck
  have hTransP : (toPCertificate cert).trans = p' := by simp [toPCertificate]; exact hTrans
  have hts' : TypedStore (toPCertificate cert).tyCtx σ₀ := by
    simp [toPCertificate]; exact hts
  have herr_cert : ((toPCertificate cert).trans ⊩ Cfg.run 0 σ₀ am₀ ⟶* Cfg.errorDiv σ' am') ∨
                   ((toPCertificate cert).trans ⊩ Cfg.run 0 σ₀ am₀ ⟶* Cfg.errorBounds σ' am') := by
    rcases hbeh with hd | hb
    · exact .inl (hTransP ▸ hd)
    · exact .inr (hTransP ▸ hb)
  obtain ⟨σ_o, am_f, herr_orig⟩ := error_preservation _ hvalid σ₀ hts' herr_cert
  have hOC : (toPCertificate cert).orig.code = p.code := by simp [toPCertificate]; exact hOrigCode
  have hOA : (toPCertificate cert).orig.arrayDecls = p.arrayDecls := by simp [toPCertificate]; exact hOrigArr
  refine ⟨σ_o, am_f, ?_⟩
  rcases herr_orig with hd | hb
  · exact .inl (Steps_of_code_arrayDecls_eq hOC hOA hd)
  · exact .inr (Steps_of_code_arrayDecls_eq hOC hOA hb)

/-- A single optimization pass preserves divergence. -/
private theorem applyPass_preserves_diverge {name : String} {tyCtx : TyCtx}
    {pass : Prog → ECertificate} {p p' : Prog}
    (h : applyPass name tyCtx pass p = .ok p')
    (σ₀ : Store) (hts : TypedStore tyCtx σ₀)
    {f : Nat → Cfg}
    (hinf : IsInfiniteExec p' f) (hf0 : f 0 = Cfg.run 0 σ₀ ArrayMem.init) :
    ∃ g, IsInfiniteExec p g ∧ g 0 = Cfg.run 0 σ₀ ArrayMem.init := by
  obtain ⟨hcheck, hTrans, hOrigCode, _, hOrigArr⟩ := applyPass_sound h
  let cert := { pass p with tyCtx := tyCtx }
  have hvalid := soundness_bridge cert hcheck
  have hTransP : (toPCertificate cert).trans = p' := by simp [toPCertificate]; exact hTrans
  have hts' : TypedStore (toPCertificate cert).tyCtx σ₀ := by
    simp [toPCertificate]; exact hts
  have hinf' : IsInfiniteExec (toPCertificate cert).trans f := hTransP ▸ hinf
  obtain ⟨g, hg, hg0⟩ := soundness_diverge _ hvalid f σ₀ hts' hinf' hf0
  have hOC : (toPCertificate cert).orig.code = p.code := by simp [toPCertificate]; exact hOrigCode
  have hOA : (toPCertificate cert).orig.arrayDecls = p.arrayDecls := by simp [toPCertificate]; exact hOrigArr
  exact ⟨g, IsInfiniteExec_of_code_eq hOC hOA hg, hg0⟩

/-- Each pass preserves observable variable list. -/
private theorem obs_preserved_by_pass (n : String) (tyCtx : TyCtx)
    (pass : Prog → ECertificate) (q q' : Prog)
    (hap : applyPass n tyCtx pass q = .ok q') : q'.observable = q.observable := by
  obtain ⟨hcheck, hTrans, _, hOrigObs, _⟩ := applyPass_sound hap
  rw [← hTrans]
  have hSameObs := same_obs_of_check { pass q with tyCtx := tyCtx } hcheck
  simp at hSameObs
  rw [← hSameObs, hOrigObs]

-- ============================================================
-- § 3. applyPasses: inductive soundness
-- ============================================================

/-- `applyPasses` preserves observable variables across all passes. -/
theorem applyPasses_obs_eq (tyCtx : TyCtx)
    (passes : List (String × (Prog → ECertificate)))
    (p : Prog) :
    (applyPasses tyCtx passes p).observable = p.observable := by
  induction passes generalizing p with
  | nil => rfl
  | cons np rest ih =>
    simp only [applyPasses]
    obtain ⟨name, pass⟩ := np
    split
    · rename_i p' hap; rw [ih _, obs_preserved_by_pass name tyCtx pass p p' hap]
    · exact ih _

/-- `applyPasses` preserves halting behavior with fixed initial AM.
    `applyPass` enforces tyCtx on each certificate, so TypedStore is preserved
    without requiring any assumption on the passes. -/
theorem applyPasses_preserves_halt_am (tyCtx : TyCtx)
    (passes : List (String × (Prog → ECertificate)))
    (σ₀ : Store) (hts : TypedStore tyCtx σ₀)
    {σ' : Store} {am₀ am' : ArrayMem}
    (hHalt : haltsWithResult (applyPasses tyCtx passes p) 0 σ₀ σ' am₀ am') :
    ∃ σ_orig, haltsWithResult p 0 σ₀ σ_orig am₀ am' ∧
      ∀ v ∈ p.observable, σ' v = σ_orig v := by
  induction passes generalizing p σ' am' with
  | nil =>
    simp [applyPasses] at hHalt
    exact ⟨σ', hHalt, fun _ _ => rfl⟩
  | cons np rest ih =>
    simp only [applyPasses] at hHalt
    obtain ⟨name, pass⟩ := np
    split at hHalt
    · -- Pass succeeded
      rename_i p' hap
      obtain ⟨σ_mid, hHalt_mid, hobs_mid⟩ := ih hHalt
      obtain ⟨σ_orig, hHalt_orig, hobs_orig⟩ :=
        applyPass_preserves_halt_am hap σ₀ hts hHalt_mid
      have hobs_p' := obs_preserved_by_pass name tyCtx pass p p' hap
      exact ⟨σ_orig, hHalt_orig, fun v hv => by
        rw [hobs_mid v (hobs_p' ▸ hv), hobs_orig v hv]⟩
    · -- Pass failed: identity
      exact ih hHalt

/-- `applyPasses` preserves error behavior with fixed initial AM.
    Cause is preserved: div-by-zero stays div-by-zero, bounds stays bounds. -/
theorem applyPasses_preserves_error_am (tyCtx : TyCtx)
    (passes : List (String × (Prog → ECertificate)))
    (σ₀ : Store) (hts : TypedStore tyCtx σ₀)
    {σ' : Store} {am₀ am' : ArrayMem}
    (hErr : ((applyPasses tyCtx passes p) ⊩ Cfg.run 0 σ₀ am₀ ⟶* Cfg.errorDiv σ' am') ∨
            ((applyPasses tyCtx passes p) ⊩ Cfg.run 0 σ₀ am₀ ⟶* Cfg.errorBounds σ' am')) :
    ∃ σ_o am_o', (p ⊩ Cfg.run 0 σ₀ am₀ ⟶* Cfg.errorDiv σ_o am_o') ∨
                 (p ⊩ Cfg.run 0 σ₀ am₀ ⟶* Cfg.errorBounds σ_o am_o') := by
  induction passes generalizing p σ' am' with
  | nil =>
    simp [applyPasses] at hErr
    rcases hErr with hd | hb
    · exact ⟨σ', am', .inl hd⟩
    · exact ⟨σ', am', .inr hb⟩
  | cons np rest ih =>
    simp only [applyPasses] at hErr
    obtain ⟨name, pass⟩ := np
    split at hErr
    · rename_i p' hap
      obtain ⟨σ_mid, am_mid, hErr_mid⟩ := ih hErr
      exact applyPass_preserves_error_am hap σ₀ hts hErr_mid
    · exact ih hErr

/-- Cause-faithful version: a single optimization pass preserves `errorDiv`. -/
private theorem applyPass_preserves_errorDiv {name : String} {tyCtx : TyCtx}
    {pass : Prog → ECertificate} {p p' : Prog}
    (h : applyPass name tyCtx pass p = .ok p')
    (σ₀ : Store) (hts : TypedStore tyCtx σ₀)
    {σ' : Store} {am₀ am' : ArrayMem}
    (hbeh : p' ⊩ Cfg.run 0 σ₀ am₀ ⟶* Cfg.errorDiv σ' am') :
    ∃ σ_o am_o', p ⊩ Cfg.run 0 σ₀ am₀ ⟶* Cfg.errorDiv σ_o am_o' := by
  obtain ⟨hcheck, hTrans, hOrigCode, _, hOrigArr⟩ := applyPass_sound h
  let cert := { pass p with tyCtx := tyCtx }
  have hvalid := soundness_bridge cert hcheck
  have hTransP : (toPCertificate cert).trans = p' := by simp [toPCertificate]; exact hTrans
  have hts' : TypedStore (toPCertificate cert).tyCtx σ₀ := by
    simp [toPCertificate]; exact hts
  have herr_cert : (toPCertificate cert).trans ⊩ Cfg.run 0 σ₀ am₀ ⟶* Cfg.errorDiv σ' am' :=
    hTransP ▸ hbeh
  obtain ⟨σ_o, am_f, herr_orig⟩ := errorDiv_preservation _ hvalid σ₀ hts' herr_cert
  have hOC : (toPCertificate cert).orig.code = p.code := by simp [toPCertificate]; exact hOrigCode
  have hOA : (toPCertificate cert).orig.arrayDecls = p.arrayDecls := by simp [toPCertificate]; exact hOrigArr
  exact ⟨σ_o, am_f, Steps_of_code_arrayDecls_eq hOC hOA herr_orig⟩

/-- Cause-faithful version: a single optimization pass preserves `errorBounds`. -/
private theorem applyPass_preserves_errorBounds {name : String} {tyCtx : TyCtx}
    {pass : Prog → ECertificate} {p p' : Prog}
    (h : applyPass name tyCtx pass p = .ok p')
    (σ₀ : Store) (hts : TypedStore tyCtx σ₀)
    {σ' : Store} {am₀ am' : ArrayMem}
    (hbeh : p' ⊩ Cfg.run 0 σ₀ am₀ ⟶* Cfg.errorBounds σ' am') :
    ∃ σ_o am_o', p ⊩ Cfg.run 0 σ₀ am₀ ⟶* Cfg.errorBounds σ_o am_o' := by
  obtain ⟨hcheck, hTrans, hOrigCode, _, hOrigArr⟩ := applyPass_sound h
  let cert := { pass p with tyCtx := tyCtx }
  have hvalid := soundness_bridge cert hcheck
  have hTransP : (toPCertificate cert).trans = p' := by simp [toPCertificate]; exact hTrans
  have hts' : TypedStore (toPCertificate cert).tyCtx σ₀ := by
    simp [toPCertificate]; exact hts
  have herr_cert : (toPCertificate cert).trans ⊩ Cfg.run 0 σ₀ am₀ ⟶* Cfg.errorBounds σ' am' :=
    hTransP ▸ hbeh
  obtain ⟨σ_o, am_f, herr_orig⟩ := errorBounds_preservation _ hvalid σ₀ hts' herr_cert
  have hOC : (toPCertificate cert).orig.code = p.code := by simp [toPCertificate]; exact hOrigCode
  have hOA : (toPCertificate cert).orig.arrayDecls = p.arrayDecls := by simp [toPCertificate]; exact hOrigArr
  exact ⟨σ_o, am_f, Steps_of_code_arrayDecls_eq hOC hOA herr_orig⟩

/-- Cause-faithful version: `applyPasses` preserves `errorDiv` specifically. -/
theorem applyPasses_preserves_errorDiv (tyCtx : TyCtx)
    (passes : List (String × (Prog → ECertificate)))
    (σ₀ : Store) (hts : TypedStore tyCtx σ₀)
    {σ' : Store} {am₀ am' : ArrayMem}
    (hErr : (applyPasses tyCtx passes p) ⊩ Cfg.run 0 σ₀ am₀ ⟶* Cfg.errorDiv σ' am') :
    ∃ σ_o am_o', p ⊩ Cfg.run 0 σ₀ am₀ ⟶* Cfg.errorDiv σ_o am_o' := by
  induction passes generalizing p σ' am' with
  | nil =>
    simp [applyPasses] at hErr
    exact ⟨σ', am', hErr⟩
  | cons np rest ih =>
    simp only [applyPasses] at hErr
    obtain ⟨name, pass⟩ := np
    split at hErr
    · rename_i p' hap
      obtain ⟨σ_mid, am_mid, hErr_mid⟩ := ih hErr
      exact applyPass_preserves_errorDiv hap σ₀ hts hErr_mid
    · exact ih hErr

/-- Cause-faithful version: `applyPasses` preserves `errorBounds` specifically. -/
theorem applyPasses_preserves_errorBounds (tyCtx : TyCtx)
    (passes : List (String × (Prog → ECertificate)))
    (σ₀ : Store) (hts : TypedStore tyCtx σ₀)
    {σ' : Store} {am₀ am' : ArrayMem}
    (hErr : (applyPasses tyCtx passes p) ⊩ Cfg.run 0 σ₀ am₀ ⟶* Cfg.errorBounds σ' am') :
    ∃ σ_o am_o', p ⊩ Cfg.run 0 σ₀ am₀ ⟶* Cfg.errorBounds σ_o am_o' := by
  induction passes generalizing p σ' am' with
  | nil =>
    simp [applyPasses] at hErr
    exact ⟨σ', am', hErr⟩
  | cons np rest ih =>
    simp only [applyPasses] at hErr
    obtain ⟨name, pass⟩ := np
    split at hErr
    · rename_i p' hap
      obtain ⟨σ_mid, am_mid, hErr_mid⟩ := ih hErr
      exact applyPass_preserves_errorBounds hap σ₀ hts hErr_mid
    · exact ih hErr

/-- `applyPasses` preserves divergence. -/
theorem applyPasses_preserves_diverge (tyCtx : TyCtx)
    (passes : List (String × (Prog → ECertificate)))
    (σ₀ : Store) (hts : TypedStore tyCtx σ₀)
    {f : Nat → Cfg}
    (hinf : IsInfiniteExec (applyPasses tyCtx passes p) f)
    (hf0 : f 0 = Cfg.run 0 σ₀ ArrayMem.init) :
    ∃ g, IsInfiniteExec p g ∧ g 0 = Cfg.run 0 σ₀ ArrayMem.init := by
  induction passes generalizing p f with
  | nil =>
    simp [applyPasses] at hinf
    exact ⟨f, hinf, hf0⟩
  | cons np rest ih =>
    simp only [applyPasses] at hinf
    obtain ⟨name, pass⟩ := np
    split at hinf
    · rename_i p' hap
      obtain ⟨g, hg, hg0⟩ := ih hinf hf0
      exact applyPass_preserves_diverge hap σ₀ hts hg hg0
    · exact ih hinf hf0

-- ============================================================
-- § 4. ARM-to-While relation and full end-to-end (halts)
-- ============================================================

/-- The ARM program's observable output matches the While source output.
    For each observable variable with a layout entry, the ARM register or
    stack slot holds the encoded value from the source program's final store.
    Array memory also matches. -/
def ArmStateMatchesProgramState (s : ArmState) (layout : VarLayout)
    (observables : List Var) (σ_src : Store) (am : ArrayMem) : Prop :=
  (∀ v ∈ observables, ∀ loc, layout v = some loc →
    match loc with
    | .stack off => s.stack off = (σ_src v).encode
    | .ireg r    => s.regs r = (σ_src v).encode
    | .freg r    => s.fregs r = (σ_src v).encode) ∧
  s.arrayMem = am

/-- **Full end-to-end correctness (halts): While source → ARM.**

    If a well-typed While program is compiled, optimized, and code-generated
    to ARM, and the optimized TAC halts, then:
    1. The source While program terminates safely
    2. The ARM program reaches a final state whose observable registers/stack
       slots hold the source program's output values -/
theorem while_to_arm_correctness
    (prog : Program) (htcs : prog.wellFormed = true)
    (passes : List (String × (Prog → ECertificate)))
    {r : VerifiedAsmResult}
    (hGen : verifiedGenerateAsm prog.tyCtx (applyPasses prog.tyCtx passes prog.compileToTAC) = .ok r)
    {σ_opt : Store} {am_opt : ArrayMem}
    (hHalt : haltsWithResult (applyPasses prog.tyCtx passes prog.compileToTAC) 0
      (Store.typedInit prog.tyCtx) σ_opt ArrayMem.init am_opt) :
    ∃ fuel σ_src am_src s',
      prog.interp fuel = some (σ_src, am_src) ∧
      ArmSteps r.bodyFlat
        { regs := fun _ => 0, fregs := fun _ => 0, stack := fun _ => 0,
          pc := r.pcMap 0, flags := ⟨0, 0⟩ } s' ∧
      ArmStateMatchesProgramState s' r.layout prog.compileToTAC.observable σ_src am_src ∧
      s'.pc = r.haltFinal := by
  have htc := Program.wellFormed_typeCheck prog htcs
  have hInitEq : Store.typedInit prog.tyCtx = prog.initStore :=
    Program.typedInit_eq_initStore prog htc
  have hts : TypedStore prog.tyCtx (Store.typedInit prog.tyCtx) := TypedStore.typedInit _
  -- ARM simulation from TAC
  obtain ⟨s', hArm, hSimRel, hHaltPC⟩ := tacToArm_correctness hGen hHalt
  have hStateRel : ExtStateRel r.layout σ_opt s' := hSimRel.1
  have hAmRel : s'.arrayMem = am_opt := hSimRel.2
  -- Pipeline → original TAC halts with same final AM
  obtain ⟨σ_tac, hHalt_tac, hobs_tac⟩ :=
    applyPasses_preserves_halt_am prog.tyCtx passes _ hts hHalt
  have hHalt_init : haltsWithResult prog.compileToTAC 0 prog.initStore σ_tac ArrayMem.init am_opt :=
    hInitEq ▸ hHalt_tac
  have hbeh_tac : program_behavior_init prog.compileToTAC prog.initStore (.halts σ_tac) :=
    ⟨am_opt, hHalt_init⟩
  have hsrc := whileToTAC_refinement prog htcs (.halts σ_tac) hbeh_tac
  simp only at hsrc
  obtain ⟨fuel, σ_src, am_h, am_src, hinterp, hHalt_tac2, ham_eq, hobs_src⟩ := hsrc
  have ham_opt : am_h = am_opt := (haltsWithResult_unique hHalt_tac2 hHalt_init).2
  have hnt : Program.noTmpDecls prog.decls = true := by
    unfold Program.typeCheck at htc; simp only [Bool.and_eq_true] at htc; exact htc.1.2
  have hobs_eq := applyPasses_obs_eq prog.tyCtx passes prog.compileToTAC
  have hobs_match : ∀ v ∈ prog.compileToTAC.observable, σ_opt v = σ_src v := by
    intro v hv
    rw [hobs_tac v (hobs_eq ▸ hv)]
    have hv' : v ∈ prog.decls.map Prod.fst := by
      have : prog.compileToTAC.observable = prog.decls.map Prod.fst := by
        simp [Program.compileToTAC]
      rw [this] at hv; exact hv
    obtain ⟨⟨w, ty⟩, hp, hw⟩ := List.exists_of_mem_map hv'
    simp only at hw; subst hw
    simp only [Program.noTmpDecls, List.all_eq_true] at hnt
    have hntw := hnt ⟨w, ty⟩ hp
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hntw
    exact hobs_src w hntw.1.1 hntw.1.2 hntw.2
  refine ⟨fuel, σ_src, am_src, s', hinterp, hArm,
    ⟨fun v hv loc hloc => by
      have := hStateRel v loc hloc
      rw [hobs_match v hv] at this
      exact this,
    by rw [hAmRel, ← ham_opt, ham_eq]⟩, ?_⟩
  exact hHaltPC _ _ rfl

-- ============================================================
-- § 5. Full end-to-end: While source → ARM (errors)
-- ============================================================

/-- Cause-faithful source-side helper for `while_to_arm_div_preservation`. -/
private theorem while_to_arm_errorDiv_source_side
    (prog : Program) (htcs : prog.wellFormed = true)
    (passes : List (String × (Prog → ECertificate)))
    {σ_err : Store} {am_err : ArrayMem}
    (hErr : (applyPasses prog.tyCtx passes prog.compileToTAC) ⊩
        Cfg.run 0 (Store.typedInit prog.tyCtx) ArrayMem.init ⟶* Cfg.errorDiv σ_err am_err) :
    ∃ fuel, prog.body.unsafeDiv fuel prog.initStore ArrayMem.init prog.arrayDecls := by
  have htc := Program.wellFormed_typeCheck prog htcs
  have hInitEq : Store.typedInit prog.tyCtx = prog.initStore :=
    Program.typedInit_eq_initStore prog htc
  have hts : TypedStore prog.tyCtx (Store.typedInit prog.tyCtx) := TypedStore.typedInit _
  obtain ⟨σ_o, am_o', hErr_tac⟩ :=
    applyPasses_preserves_errorDiv prog.tyCtx passes _ hts hErr
  have hErr_init : program_behavior_init prog.compileToTAC prog.initStore (.errorDiv σ_o) :=
    ⟨am_o', hInitEq ▸ hErr_tac⟩
  exact whileToTAC_refinement prog htcs (.errorDiv σ_o) hErr_init

/-- Cause-faithful source-side helper for `while_to_arm_bounds_preservation`. -/
private theorem while_to_arm_errorBounds_source_side
    (prog : Program) (htcs : prog.wellFormed = true)
    (passes : List (String × (Prog → ECertificate)))
    {σ_err : Store} {am_err : ArrayMem}
    (hErr : (applyPasses prog.tyCtx passes prog.compileToTAC) ⊩
        Cfg.run 0 (Store.typedInit prog.tyCtx) ArrayMem.init ⟶* Cfg.errorBounds σ_err am_err) :
    ∃ fuel, prog.body.unsafeBounds fuel prog.initStore ArrayMem.init prog.arrayDecls := by
  have htc := Program.wellFormed_typeCheck prog htcs
  have hInitEq : Store.typedInit prog.tyCtx = prog.initStore :=
    Program.typedInit_eq_initStore prog htc
  have hts : TypedStore prog.tyCtx (Store.typedInit prog.tyCtx) := TypedStore.typedInit _
  obtain ⟨σ_o, am_o', hErr_tac⟩ :=
    applyPasses_preserves_errorBounds prog.tyCtx passes _ hts hErr
  have hErr_init : program_behavior_init prog.compileToTAC prog.initStore (.errorBounds σ_o) :=
    ⟨am_o', hInitEq ▸ hErr_tac⟩
  exact whileToTAC_refinement prog htcs (.errorBounds σ_o) hErr_init

/-- **While→ARM: division-by-zero cause.**

    If the optimized TAC reaches `errorDiv`, then (a) the source While program
    is unsafe at some fuel (div or bounds — the specific cause match is Phase 7
    work), and (b) the ARM program steps to a state whose PC is the verified
    `divS` sentinel. -/
theorem while_to_arm_div_preservation
    (prog : Program) (htcs : prog.wellFormed = true)
    (passes : List (String × (Prog → ECertificate)))
    {r : VerifiedAsmResult}
    (hGen : verifiedGenerateAsm prog.tyCtx (applyPasses prog.tyCtx passes prog.compileToTAC) = .ok r)
    {σ_err : Store} {am_err : ArrayMem}
    (hErr : (applyPasses prog.tyCtx passes prog.compileToTAC) ⊩
      Cfg.run 0 (Store.typedInit prog.tyCtx)
        ArrayMem.init ⟶* Cfg.errorDiv σ_err am_err) :
    (∃ fuel, prog.body.unsafeDiv fuel prog.initStore ArrayMem.init prog.arrayDecls) ∧
    (∃ s', ArmSteps r.bodyFlat
      { regs := fun _ => 0, fregs := fun _ => 0, stack := fun _ => 0,
        pc := r.pcMap 0, flags := ⟨0, 0⟩ } s' ∧
      s'.pc = r.divS) := by
  refine ⟨while_to_arm_errorDiv_source_side prog htcs passes hErr, ?_⟩
  obtain ⟨s', hArm, hRel, _⟩ := tacToArm_correctness hGen hErr
  exact ⟨s', hArm, hRel⟩

/-- **While→ARM: array-bounds-error cause.** -/
theorem while_to_arm_bounds_preservation
    (prog : Program) (htcs : prog.wellFormed = true)
    (passes : List (String × (Prog → ECertificate)))
    {r : VerifiedAsmResult}
    (hGen : verifiedGenerateAsm prog.tyCtx (applyPasses prog.tyCtx passes prog.compileToTAC) = .ok r)
    {σ_err : Store} {am_err : ArrayMem}
    (hErr : (applyPasses prog.tyCtx passes prog.compileToTAC) ⊩
      Cfg.run 0 (Store.typedInit prog.tyCtx)
        ArrayMem.init ⟶* Cfg.errorBounds σ_err am_err) :
    (∃ fuel, prog.body.unsafeBounds fuel prog.initStore ArrayMem.init prog.arrayDecls) ∧
    (∃ s', ArmSteps r.bodyFlat
      { regs := fun _ => 0, fregs := fun _ => 0, stack := fun _ => 0,
        pc := r.pcMap 0, flags := ⟨0, 0⟩ } s' ∧
      s'.pc = r.boundsS) := by
  refine ⟨while_to_arm_errorBounds_source_side prog htcs passes hErr, ?_⟩
  obtain ⟨s', hArm, hRel, _⟩ := tacToArm_correctness hGen hErr
  exact ⟨s', hArm, hRel⟩

-- ============================================================
-- § 6. Full end-to-end: While source → ARM (diverges)
-- ============================================================

/-- **Full end-to-end divergence preservation: While source → ARM.**

    If the optimized TAC diverges, then the source While program diverges
    (does not terminate at any fuel). -/
theorem while_to_arm_divergence_preservation
    (prog : Program) (htcs : prog.wellFormed = true)
    (passes : List (String × (Prog → ECertificate)))
    {f : Nat → Cfg}
    (hDiv : IsInfiniteExec (applyPasses prog.tyCtx passes prog.compileToTAC) f)
    (hf0 : f 0 = Cfg.run 0 (Store.typedInit prog.tyCtx) ArrayMem.init) :
    ∀ fuel, prog.interp fuel = none := by
  have htc := Program.wellFormed_typeCheck prog htcs
  have hInitEq : Store.typedInit prog.tyCtx = prog.initStore :=
    Program.typedInit_eq_initStore prog htc
  have hts : TypedStore prog.tyCtx (Store.typedInit prog.tyCtx) := TypedStore.typedInit _
  obtain ⟨g, hg, hg0⟩ :=
    applyPasses_preserves_diverge prog.tyCtx passes _ hts hDiv hf0
  have hdiv_init : program_behavior_init prog.compileToTAC prog.initStore .diverges :=
    ⟨g, hg, hInitEq ▸ hg0⟩
  exact whileToTAC_refinement prog htcs .diverges hdiv_init

-- ============================================================
-- § 6a. Structural lemmas: fixpoint-cluster pipelines = applyPasses
-- ============================================================

/-- `applyPasses` distributes over list append: running passes `l₁ ++ l₂` is the
    same as running `l₁` then `l₂`.  Used to flatten the
    `prefix → cluster → suffix` composition in
    `applyStandardPipelineFixpoint` into a single `applyPasses` call. -/
theorem applyPasses_append (tyCtx : TyCtx)
    (l₁ l₂ : List (String × (Prog → ECertificate))) (p : Prog) :
    applyPasses tyCtx (l₁ ++ l₂) p
      = applyPasses tyCtx l₂ (applyPasses tyCtx l₁ p) := by
  induction l₁ generalizing p with
  | nil => simp [applyPasses]
  | cons head tail ih =>
    obtain ⟨name, pass⟩ := head
    simp only [List.cons_append, applyPasses]
    exact ih _

/-- The bounded fixed-point iterator is equal to `applyPasses` over a
    suitable concatenation of the cluster's pass list (k copies for some
    `k ≤ n + 1`).  We do not commit to `k`; we just need the existential
    so downstream theorems about `applyPasses` apply. -/
theorem applyPassesUntilFixedOrN_eq_applyPasses (tyCtx : TyCtx)
    (passes : List (String × (Prog → ECertificate)))
    (n : Nat) (p : Prog) :
    ∃ allPasses,
      applyPassesUntilFixedOrN tyCtx passes n p
        = applyPasses tyCtx allPasses p := by
  induction n generalizing p with
  | zero =>
    refine ⟨[], ?_⟩
    simp [applyPassesUntilFixedOrN, applyPasses]
  | succ n' ih =>
    rw [applyPassesUntilFixedOrN]
    by_cases h : (applyPasses tyCtx passes p).code = p.code
    · -- Fixed point reached after one cluster iteration.
      simp [h]
      exact ⟨passes, rfl⟩
    · -- Not yet a fixed point; recurse.
      simp [h]
      obtain ⟨tailPasses, hTail⟩ := ih (applyPasses tyCtx passes p)
      refine ⟨passes ++ tailPasses, ?_⟩
      rw [applyPasses_append, hTail]

/-- `applyStandardPipelineFixpoint` is `applyPasses` over a single
    concatenated pass list (program-dependent — the cluster portion's
    length depends on how many iterations the fixed-point reached).
    With this, every theorem about `applyPasses tyCtx _ prog.compileToTAC`
    discharges the corresponding goal about `applyStandardPipelineFixpoint`. -/
theorem applyStandardPipelineFixpoint_eq_applyPasses (tyCtx : TyCtx) (p : Prog) :
    ∃ allPasses,
      applyStandardPipelineFixpoint tyCtx p
        = applyPasses tyCtx allPasses p := by
  obtain ⟨clusterPasses, hCluster⟩ :=
    applyPassesUntilFixedOrN_eq_applyPasses tyCtx (licmClusterPasses tyCtx) 5
      (applyPasses tyCtx (prefixPasses tyCtx) p)
  refine ⟨prefixPasses tyCtx ++ clusterPasses ++ suffixPasses tyCtx, ?_⟩
  show applyPasses tyCtx (suffixPasses tyCtx)
        (applyPassesUntilFixedOrN tyCtx (licmClusterPasses tyCtx) 5
          (applyPasses tyCtx (prefixPasses tyCtx) p))
       = applyPasses tyCtx (prefixPasses tyCtx ++ clusterPasses ++ suffixPasses tyCtx) p
  rw [applyPasses_append, applyPasses_append, hCluster]

-- ============================================================
-- § 6b. Connecting the driver to top-level correctness
-- ============================================================

/-- **Driver-to-theorem bridge: halts.**

    The compiler driver `compileProgramAst` runs the verified post-parse
    pipeline (well-formedness check → AST→TAC → optimizations → verified
    ARM codegen).  This theorem connects a successful driver run to the
    top-level `while_to_arm_correctness` guarantee:

    *If the driver returned `.ok r` and the optimized TAC halts, then the
    source `prog.interp` halts and the ARM program reaches a final state
    matching the source observables.*

    The proof is a thin wrapper: it extracts `prog.wellFormed = true` from
    the driver's success case, then applies `while_to_arm_correctness`. -/
theorem compileProgramAst_correctness
    {prog : Program} {noOpt : Bool} {r : VerifiedAsmResult}
    (hDriver : compileProgramAst prog noOpt = .ok r)
    {σ_opt : Store} {am_opt : ArrayMem}
    (hHalt : haltsWithResult
              (if noOpt then prog.compileToTAC
               else applyStandardPipelineFixpoint prog.tyCtx prog.compileToTAC)
              0 (Store.typedInit prog.tyCtx) σ_opt ArrayMem.init am_opt) :
    ∃ fuel σ_src am_src s',
      prog.interp fuel = some (σ_src, am_src) ∧
      ArmSteps r.bodyFlat
        { regs := fun _ => 0, fregs := fun _ => 0, stack := fun _ => 0,
          pc := r.pcMap 0, flags := ⟨0, 0⟩ } s' ∧
      ArmStateMatchesProgramState s' r.layout prog.compileToTAC.observable σ_src am_src ∧
      s'.pc = r.haltFinal := by
  unfold compileProgramAst at hDriver
  split at hDriver
  · rename_i hwf
    cases noOpt with
    | true =>
      simp at hDriver hHalt
      exact while_to_arm_correctness prog hwf
        ([] : List (String × (Prog → ECertificate))) hDriver hHalt
    | false =>
      simp at hDriver hHalt
      obtain ⟨allPasses, heq⟩ :=
        applyStandardPipelineFixpoint_eq_applyPasses prog.tyCtx prog.compileToTAC
      rw [heq] at hDriver hHalt
      exact while_to_arm_correctness prog hwf allPasses hDriver hHalt
  · simp at hDriver

/-- **Driver-to-theorem bridge: division-by-zero.**

    If the driver succeeds and the optimized TAC reaches `errorDiv`, then
    the source program is unsafe at some fuel and the ARM program steps to
    the verified `divS` sentinel. -/
theorem compileProgramAst_div_preservation
    {prog : Program} {noOpt : Bool} {r : VerifiedAsmResult}
    (hDriver : compileProgramAst prog noOpt = .ok r)
    {σ_err : Store} {am_err : ArrayMem}
    (hErr : (if noOpt then prog.compileToTAC
             else applyStandardPipelineFixpoint prog.tyCtx prog.compileToTAC) ⊩
        Cfg.run 0 (Store.typedInit prog.tyCtx)
          ArrayMem.init ⟶* Cfg.errorDiv σ_err am_err) :
    (∃ fuel, prog.body.unsafeDiv fuel prog.initStore ArrayMem.init prog.arrayDecls) ∧
    (∃ s', ArmSteps r.bodyFlat
      { regs := fun _ => 0, fregs := fun _ => 0, stack := fun _ => 0,
        pc := r.pcMap 0, flags := ⟨0, 0⟩ } s' ∧
      s'.pc = r.divS) := by
  unfold compileProgramAst at hDriver
  split at hDriver
  · rename_i hwf
    cases noOpt with
    | true =>
      simp at hDriver hErr
      exact while_to_arm_div_preservation prog hwf
        ([] : List (String × (Prog → ECertificate))) hDriver hErr
    | false =>
      simp at hDriver hErr
      obtain ⟨allPasses, heq⟩ :=
        applyStandardPipelineFixpoint_eq_applyPasses prog.tyCtx prog.compileToTAC
      rw [heq] at hDriver hErr
      exact while_to_arm_div_preservation prog hwf allPasses hDriver hErr
  · simp at hDriver

/-- **Driver-to-theorem bridge: array-bounds error.** -/
theorem compileProgramAst_bounds_preservation
    {prog : Program} {noOpt : Bool} {r : VerifiedAsmResult}
    (hDriver : compileProgramAst prog noOpt = .ok r)
    {σ_err : Store} {am_err : ArrayMem}
    (hErr : (if noOpt then prog.compileToTAC
             else applyStandardPipelineFixpoint prog.tyCtx prog.compileToTAC) ⊩
        Cfg.run 0 (Store.typedInit prog.tyCtx)
          ArrayMem.init ⟶* Cfg.errorBounds σ_err am_err) :
    (∃ fuel, prog.body.unsafeBounds fuel prog.initStore ArrayMem.init prog.arrayDecls) ∧
    (∃ s', ArmSteps r.bodyFlat
      { regs := fun _ => 0, fregs := fun _ => 0, stack := fun _ => 0,
        pc := r.pcMap 0, flags := ⟨0, 0⟩ } s' ∧
      s'.pc = r.boundsS) := by
  unfold compileProgramAst at hDriver
  split at hDriver
  · rename_i hwf
    cases noOpt with
    | true =>
      simp at hDriver hErr
      exact while_to_arm_bounds_preservation prog hwf
        ([] : List (String × (Prog → ECertificate))) hDriver hErr
    | false =>
      simp at hDriver hErr
      obtain ⟨allPasses, heq⟩ :=
        applyStandardPipelineFixpoint_eq_applyPasses prog.tyCtx prog.compileToTAC
      rw [heq] at hDriver hErr
      exact while_to_arm_bounds_preservation prog hwf allPasses hDriver hErr
  · simp at hDriver

/-- **Driver-to-theorem bridge: divergence.**

    If the driver succeeds and the optimized TAC diverges, then the source
    While program diverges (does not terminate at any fuel). -/
theorem compileProgramAst_divergence_preservation
    {prog : Program} {noOpt : Bool} {r : VerifiedAsmResult}
    (hDriver : compileProgramAst prog noOpt = .ok r)
    {f : Nat → Cfg}
    (hDiv : IsInfiniteExec
      (if noOpt then prog.compileToTAC
       else applyStandardPipelineFixpoint prog.tyCtx prog.compileToTAC) f)
    (hf0 : f 0 = Cfg.run 0 (Store.typedInit prog.tyCtx) ArrayMem.init) :
    ∀ fuel, prog.interp fuel = none := by
  unfold compileProgramAst at hDriver
  split at hDriver
  · rename_i hwf
    cases noOpt with
    | true =>
      simp at hDriver hDiv
      exact while_to_arm_divergence_preservation prog hwf
        ([] : List (String × (Prog → ECertificate))) hDiv hf0
    | false =>
      simp at hDriver hDiv
      obtain ⟨allPasses, heq⟩ :=
        applyStandardPipelineFixpoint_eq_applyPasses prog.tyCtx prog.compileToTAC
      rw [heq] at hDriver hDiv
      exact while_to_arm_divergence_preservation prog hwf allPasses hDiv hf0
  · simp at hDriver

-- ============================================================
-- § 7. Totality of generateAsm on the optimized pipeline
-- ============================================================

/-- Bridge: `checkStepClosed p` (all successors of every instruction in bounds)
    implies `checkSuccessorsInBounds_prog p` (only goto/ifgoto targets in bounds).
    The former is strictly stronger; the latter suffices for `checkBranchTargets`. -/
theorem checkSuccessorsInBounds_prog_of_stepClosed {p : Prog}
    (h : checkStepClosed p = true) :
    checkSuccessorsInBounds_prog p = true := by
  unfold checkStepClosed at h
  unfold checkSuccessorsInBounds_prog
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h ⊢
  obtain ⟨hpos, hAll⟩ := h
  refine ⟨hpos, ?_⟩
  intro pc hpc
  have hext := hAll pc hpc
  cases hp : p[pc]? with
  | none => simp
  | some instr =>
    rw [hp] at hext
    simp only at hext
    cases instr with
    | goto l => simp [TAC.successors, decide_eq_true_eq] at hext ⊢; exact hext
    | ifgoto _ l =>
      simp [TAC.successors, decide_eq_true_eq] at hext ⊢
      exact hext.1
    | _ => simp

/-- Helper: decompose `(a && b) = true` into the two conjuncts. -/
private theorem and_true_split {a b : Bool} (h : (a && b) = true) :
    a = true ∧ b = true := by simp [Bool.and_eq_true] at h; exact h

/-- Extract the four codegen prerequisites from `checkCertificateExec`: well-typed,
    codegen prereqs, branch targets, and simple bool ops — all on `cert.trans`.
    `checkCertificateExec` is a left-associative conjunction of 30 checks; we peel
    from the right, naming only the conjuncts we need. -/
private theorem invariants_of_checkCertificateExec {cert : ECertificate}
    (h : checkCertificateExec cert = true) :
    checkWellTypedProg cert.tyCtx cert.trans = true ∧
    checkCodegenPrereqs cert.tyCtx cert.trans = true ∧
    checkBranchTargets cert.trans.code = none ∧
    checkBoolExprSimpleOps cert.trans = true := by
  unfold checkCertificateExec at h
  have ⟨h29, hPrereqs_t⟩  := and_true_split h
  have ⟨h28, _⟩           := and_true_split h29
  have ⟨h27, _⟩           := and_true_split h28
  have ⟨h26, _⟩           := and_true_split h27
  have ⟨h25, _⟩           := and_true_split h26
  have ⟨h24, _⟩           := and_true_split h25
  have ⟨h23, _⟩           := and_true_split h24
  have ⟨h22, hSimple_t⟩   := and_true_split h23
  have ⟨h21, _⟩           := and_true_split h22
  have ⟨h20, _⟩           := and_true_split h21
  have ⟨h19, _⟩           := and_true_split h20
  have ⟨h18, hSIB⟩        := and_true_split h19
  have ⟨h17, _⟩           := and_true_split h18
  have ⟨h16, _⟩           := and_true_split h17
  have ⟨h15, _⟩           := and_true_split h16
  have ⟨h14, _⟩           := and_true_split h15
  have ⟨h13, _⟩           := and_true_split h14
  have ⟨h12, _⟩           := and_true_split h13
  have ⟨h11, _⟩           := and_true_split h12
  have ⟨h10, _⟩           := and_true_split h11
  have ⟨h9,  _⟩           := and_true_split h10
  have ⟨h8,  _⟩           := and_true_split h9
  have ⟨h7,  _⟩           := and_true_split h8
  have ⟨h6,  _⟩           := and_true_split h7
  have ⟨h5,  _⟩           := and_true_split h6
  have ⟨h4,  _⟩           := and_true_split h5
  have ⟨h3,  _⟩           := and_true_split h4
  have ⟨h2,  _⟩           := and_true_split h3
  have ⟨_,   hWT_t⟩       := and_true_split h2
  -- hSIB : checkSuccessorsInBounds cert = checkStepClosed cert.trans = true (by defn)
  exact ⟨hWT_t, hPrereqs_t,
    checkBranchTargets_of_successorsInBounds _ (checkSuccessorsInBounds_prog_of_stepClosed hSIB),
    hSimple_t⟩

/-- A single pass preserves the four codegen invariants: if the invariants hold
    at the input `p` and `applyPass` succeeds, they hold at the output `p'`. -/
theorem applyPass_preserves_invariants {name : String} {tyCtx : TyCtx}
    {pass : Prog → ECertificate} {p p' : Prog}
    (h : applyPass name tyCtx pass p = .ok p') :
    checkWellTypedProg tyCtx p' = true ∧
    checkCodegenPrereqs tyCtx p' = true ∧
    checkBranchTargets p'.code = none ∧
    checkBoolExprSimpleOps p' = true := by
  obtain ⟨hcheck, hTrans, _, _, _⟩ := applyPass_sound h
  have ⟨hWT, hPrereqs, hBranch, hSimple⟩ :=
    invariants_of_checkCertificateExec (cert := { pass p with tyCtx := tyCtx }) hcheck
  -- Record field projections reduce definitionally; rewrite .trans to p' via hTrans
  simp only [hTrans] at hWT hPrereqs hBranch hSimple
  exact ⟨hWT, hPrereqs, hBranch, hSimple⟩

/-- `applyPasses` preserves the four codegen invariants. Either a pass
    succeeds (and `applyPass_preserves_invariants` transfers them to the new
    program) or fails (and the program is unchanged). -/
theorem applyPasses_preserves_invariants (tyCtx : TyCtx)
    (passes : List (String × (Prog → ECertificate)))
    (p : Prog)
    (hWT : checkWellTypedProg tyCtx p = true)
    (hPrereqs : checkCodegenPrereqs tyCtx p = true)
    (hBranch : checkBranchTargets p.code = none)
    (hSimple : checkBoolExprSimpleOps p = true) :
    checkWellTypedProg tyCtx (applyPasses tyCtx passes p) = true ∧
    checkCodegenPrereqs tyCtx (applyPasses tyCtx passes p) = true ∧
    checkBranchTargets (applyPasses tyCtx passes p).code = none ∧
    checkBoolExprSimpleOps (applyPasses tyCtx passes p) = true := by
  induction passes generalizing p with
  | nil => simp [applyPasses]; exact ⟨hWT, hPrereqs, hBranch, hSimple⟩
  | cons np rest ih =>
    simp only [applyPasses]
    obtain ⟨name, pass⟩ := np
    split
    · rename_i p' hap
      obtain ⟨hWT', hPrereqs', hBranch', hSimple'⟩ :=
        applyPass_preserves_invariants hap
      exact ih p' hWT' hPrereqs' hBranch' hSimple'
    · exact ih p hWT hPrereqs hBranch hSimple

/-- End-to-end totality on the optimized pipeline: `verifiedGenerateAsm` succeeds
    for any well-typed source program after an arbitrary list of certificate-checked
    optimization passes. Each pass either validates (refining the program) or is
    skipped; the codegen invariants are preserved either way. -/
theorem generateAsm_total_with_passes (prog : Program) (htcs : prog.wellFormed = true)
    (passes : List (String × (Prog → ECertificate))) :
    ∃ asm, verifiedGenerateAsm prog.tyCtx
      (applyPasses prog.tyCtx passes prog.compileToTAC) = .ok asm := by
  have htc := prog.wellFormed_typeCheck htcs
  have hWT0 : checkWellTypedProg prog.tyCtx prog.compileToTAC = true :=
    checkWellTypedProg_complete (prog.compileToTAC_wellTyped htc)
  have hPrereqs0 := compileToTAC_codegenPrereqs prog htcs
  have hBranch0 := compileToTAC_checkBranchTargets prog
  have hSimple0 := compileToTAC_checkBoolExprSimpleOps prog
  obtain ⟨hWT, hPrereqs, hBranch, hSimple⟩ :=
    applyPasses_preserves_invariants prog.tyCtx passes prog.compileToTAC
      hWT0 hPrereqs0 hBranch0 hSimple0
  exact verifiedGenerateAsm_total prog.tyCtx _ hWT hPrereqs hBranch hSimple

/-- End-to-end totality on the no-optimization path. Corollary of
    `generateAsm_total_with_passes` at `passes = []`, where `applyPasses`
    is the identity definitionally. -/
theorem generateAsm_total (prog : Program) (htcs : prog.wellFormed = true) :
    ∃ asm, verifiedGenerateAsm prog.tyCtx prog.compileToTAC = .ok asm :=
  generateAsm_total_with_passes prog htcs ([] : List (String × (Prog → ECertificate)))

/-- **Driver totality.**  Well-formedness of the source `Program` suffices
    for the compiler driver to succeed: `compileProgramAst` returns
    `.ok asm` for some `asm : VerifiedAsmResult`.  The proof unfolds
    the driver, takes the `wellFormed` branch, and applies
    `generateAsm_total_with_passes` to the resulting pass list. -/
theorem compileProgramAst_total (prog : Program) (htcs : prog.wellFormed = true)
    (noOpt : Bool) :
    ∃ asm, compileProgramAst prog noOpt = .ok asm := by
  unfold compileProgramAst
  simp [htcs]
  cases noOpt with
  | true =>
    simp
    exact generateAsm_total_with_passes prog htcs
      ([] : List (String × (Prog → ECertificate)))
  | false =>
    simp
    obtain ⟨allPasses, heq⟩ :=
      applyStandardPipelineFixpoint_eq_applyPasses prog.tyCtx prog.compileToTAC
    rw [heq]
    exact generateAsm_total_with_passes prog htcs allPasses

-- ============================================================
-- § 8. Phase 6 — ARM behavior exhaustion
-- ============================================================

/-!
## Phase 6 — ARM behavior exhaustion (complete)

The theorem statements in this section realize Phase 6 (ARM behavior
exhaustion).  All proofs here are
**discharged** — this section contains no `sorry`/`admit` (confirmed by
`#print axioms` on the capstones, which depend only on the two float trust
axioms + the standard `propext`/`Classical.choice`/`Quot.sound`).

The once "load-bearing missing" lemma `bodyFlat_branch_target_bounded`
(every branch in `r.bodyFlat` targets a PC ≤ `r.boundsS`) is proven below,
as is the capstone `arm_behavior_exhaustive` (every ARM execution lands in
exactly one of {clean halt, div sentinel, bounds sentinel, divergence}) and
its feeders (`pcMap_le_haltS`, `sentinel_stuck`, `arm_step_det`, …).
-/

section Phase6Skeleton

/-- **Phase 6 feeder lemma: `pcMap l ≤ haltS`.**  Every live TAC PC maps to
    an ARM PC at or before `haltS` (the start of the halt-save block).
    Follows from `buildPcMap_eq_take_length` + `spec.pcMapLengths` +
    `spec.haltS_eq`: a prefix's flat-length is at most the whole
    list's flat-length. -/
theorem pcMap_le_haltS {tyCtx : TyCtx} {p : Prog} {r : VerifiedAsmResult}
    (spec : GenAsmSpec tyCtx p r) (l : Nat) (hl : l ≤ p.size) :
    r.pcMap l ≤ r.haltS := by
  obtain ⟨lengths, hSz, hEq, hLen⟩ := spec.pcMapLengths
  rw [hEq]
  have hlBody : l ≤ r.bodyPerPC.size := by
    rw [spec.bodySize]; exact hl
  rw [buildPcMap_eq_take_length r.bodyPerPC lengths hSz hLen l hlBody]
  rw [spec.haltS_eq]
  -- ((bodyPerPC.toList.take l).flatMap id).length
  --   ≤ (bodyPerPC.toList.flatMap id).length
  -- Because take l is a prefix, so its flatMap is a prefix of full flatMap.
  have : r.bodyPerPC.toList
      = r.bodyPerPC.toList.take l ++ r.bodyPerPC.toList.drop l :=
    (List.take_append_drop l _).symm
  conv_rhs => rw [this]
  rw [List.flatMap_append, List.length_append]
  omega

/-- **Phase 6 feeder lemma: branch-target bound from spec.**  `checkBranchTargets`
    (ensured by `spec.wellTypedProg` conjuncts) says every `.goto l` /
    `.ifgoto _ l` in `p.code` has `l < p.size`.  This lemma packages that
    decidable check as a propositional statement. -/
theorem checkBranchTargets_to_labels_in_bounds {p : Prog}
    (hBranch : checkBranchTargets p.code = none)
    {pc : Nat} (hpc : pc < p.size) :
    ∀ l, (p[pc] = TAC.goto l ∨ ∃ be, p[pc] = TAC.ifgoto be l) → l < p.size := by
  intro l hgoto
  simp only [checkBranchTargets] at hBranch
  split at hBranch
  · exact absurd hBranch (by intro h; cases h)
  · rename_i hFind
    have hNF := List.find?_eq_none.mp hFind
    have hpcMem : pc ∈ List.range p.size := List.mem_range.mpr (by simp [Prog.size_eq] at hpc; exact hpc)
    have := hNF pc hpcMem
    simp only [decide_eq_true_eq, Bool.not_eq_true] at this
    -- code.getD pc .halt = p[pc], and (l >= n) is what was checked
    have hGetD : p.code.getD pc .halt = p[pc] := by
      simp [Array.getD, Prog.size_eq] at *
      split
      · rfl
      · omega
    rw [hGetD] at this
    rcases hgoto with hg | ⟨be, hig⟩
    · rw [hg] at this
      simp only [decide_eq_true_eq] at this
      simp [Prog.size_eq] at *
      omega
    · rw [hig] at this
      simp only [decide_eq_true_eq] at this
      simp [Prog.size_eq] at *
      omega

/-- **Phase 6 helper: sentinel PCs are stuck.**  The three sentinels live at
    `bodyFlat.size`, `bodyFlat.size + 1`, `bodyFlat.size + 2`, so
    `bodyFlat[pc]? = none` at each; `ArmStep_stuck_of_none` finishes.

    Proof size: ~10 LOC.  Risk: trivial. -/
theorem sentinel_stuck {tyCtx : TyCtx} {p : Prog} {r : VerifiedAsmResult}
    (spec : GenAsmSpec tyCtx p r) {s : ArmState}
    (hS : s.pc = r.haltFinal ∨ s.pc = r.divS ∨ s.pc = r.boundsS) :
    ¬ ∃ s', ArmStep r.bodyFlat s s' := by
  -- Show r.bodyFlat[s.pc]? = none, then ArmStep_stuck_of_none finishes.
  -- bodyFlat.size = haltFinal (from the definition + haltS_eq + haltFinal_eq).
  have hSize : r.bodyFlat.size = r.haltFinal := by
    simp only [VerifiedAsmResult.bodyFlat, List.size_toArray,
      List.length_append, Array.length_toList]
    rw [spec.haltFinal_eq, spec.haltS_eq]
  -- Each sentinel PC is ≥ bodyFlat.size, so bodyFlat[pc]? = none.
  have hNone : r.bodyFlat[s.pc]? = none := by
    rw [Array.getElem?_eq_none_iff]
    rw [hSize]
    rcases hS with h | h | h
    · rw [h]
    · rw [h, spec.divS_eq]; omega
    · rw [h, spec.boundsS_eq]; omega
  exact ArmStep_stuck_of_none hNone

/-- **Sentinel distinctness: `haltFinal ≠ divS`.** -/
theorem haltFinal_ne_divS {tyCtx : TyCtx} {p : Prog} {r : VerifiedAsmResult}
    (spec : GenAsmSpec tyCtx p r) : r.haltFinal ≠ r.divS := by
  rw [spec.divS_eq]; omega

/-- **Sentinel distinctness: `haltFinal ≠ boundsS`.** -/
theorem haltFinal_ne_boundsS {tyCtx : TyCtx} {p : Prog} {r : VerifiedAsmResult}
    (spec : GenAsmSpec tyCtx p r) : r.haltFinal ≠ r.boundsS := by
  rw [spec.boundsS_eq]; omega

/-- **Sentinel distinctness: `divS ≠ boundsS`.** -/
theorem divS_ne_boundsS {tyCtx : TyCtx} {p : Prog} {r : VerifiedAsmResult}
    (spec : GenAsmSpec tyCtx p r) : r.divS ≠ r.boundsS := by
  rw [spec.divS_eq, spec.boundsS_eq]; omega

/-- Deterministic successor state as a pure function of `s` and the
    instruction at `s.pc`.  Under the deterministic-havoc pivot, every
    `ArmStep` rule computes its successor from the pre-state and
    instruction — no existential arguments.  Used to discharge
    `arm_step_det` via the projection trick from probe PD2. -/
private def armStepResult (s : ArmState) (i : ArmInstr) : ArmState :=
  match i with
  | .mov rd imm => s.setReg rd imm |>.nextPC
  | .movR rd rn => s.setReg rd (s.regs rn) |>.nextPC
  | .movz rd imm16 shift =>
      s.setReg rd (BitVec.ofNat 64 (imm16 <<< shift.toUInt64).toNat) |>.nextPC
  | .movk rd imm16 shift =>
      s.setReg rd (insertBits (s.regs rd) imm16 shift) |>.nextPC
  | .ldr rd off => s.setReg rd (s.stack off) |>.nextPC
  | .str rs off => s.setStack off (s.regs rs) |>.nextPC
  | .addR rd rn rm => s.setReg rd (s.regs rn + s.regs rm) |>.nextPC
  | .subR rd rn rm => s.setReg rd (s.regs rn - s.regs rm) |>.nextPC
  | .mulR rd rn rm => s.setReg rd (s.regs rn * s.regs rm) |>.nextPC
  | .sdivR rd rn rm => s.setReg rd (BitVec.sdiv (s.regs rn) (s.regs rm)) |>.nextPC
  | .cmp rn rm =>
      { s with flags := Flags.mk (s.regs rn) (s.regs rm), pc := s.pc + 1 }
  | .cmpImm rn imm =>
      { s with flags := Flags.mk (s.regs rn) imm, pc := s.pc + 1 }
  | .cset rd c =>
      s.setReg rd (if s.flags.condHolds c then (1 : BitVec 64) else 0) |>.nextPC
  | .cbz rn lbl =>
      if s.regs rn = (0 : BitVec 64) then { s with pc := lbl } else s.nextPC
  | .cbnz rn lbl =>
      if s.regs rn = (0 : BitVec 64) then s.nextPC else { s with pc := lbl }
  | .bCond c lbl =>
      if s.flags.condHolds c = true then { s with pc := lbl } else s.nextPC
  | .andImm rd rn imm => s.setReg rd (s.regs rn &&& imm) |>.nextPC
  | .andR rd rn rm => s.setReg rd (s.regs rn &&& s.regs rm) |>.nextPC
  | .eorImm rd rn imm => s.setReg rd (s.regs rn ^^^ imm) |>.nextPC
  | .orrR rd rn rm => s.setReg rd (s.regs rn ||| s.regs rm) |>.nextPC
  | .eorR rd rn rm => s.setReg rd (s.regs rn ^^^ s.regs rm) |>.nextPC
  | .lslR rd rn rm => s.setReg rd (s.regs rn <<< ((s.regs rm).toNat % 64)) |>.nextPC
  | .asrR rd rn rm =>
      s.setReg rd (BitVec.sshiftRight (s.regs rn) ((s.regs rm).toNat % 64)) |>.nextPC
  | .b lbl => { s with pc := lbl }
  | .printCall _ => s.havocCallerSaved (havocRegsFn s) (havocFRegsFn s) |>.nextPC
  | .callPrintI => s.havocCallerSaved (havocRegsFn s) (havocFRegsFn s) |>.nextPC
  | .callPrintB => s.havocCallerSaved (havocRegsFn s) (havocFRegsFn s) |>.nextPC
  | .callPrintF => s.havocCallerSaved (havocRegsFn s) (havocFRegsFn s) |>.nextPC
  | .callPrintS _ => s.havocCallerSaved (havocRegsFn s) (havocFRegsFn s) |>.nextPC
  | .arrLd dst arr idxReg =>
      s.setReg dst (s.arrayMem arr (s.regs idxReg)) |>.nextPC
  | .arrSt arr idxReg valReg =>
      s.setArrayMem arr (s.regs idxReg) (s.regs valReg) |>.nextPC
  | .fmovToFP fd rn => s.setFReg fd (s.regs rn) |>.nextPC
  | .fmovRR fd fn => s.setFReg fd (s.fregs fn) |>.nextPC
  | .fldr fd off => s.setFReg fd (s.stack off) |>.nextPC
  | .fstr fs off => s.setStack off (s.fregs fs) |>.nextPC
  | .faddR fd fn fm =>
      s.setFReg fd (FloatBinOp.eval .fadd (s.fregs fn) (s.fregs fm)) |>.nextPC
  | .fsubR fd fn fm =>
      s.setFReg fd (FloatBinOp.eval .fsub (s.fregs fn) (s.fregs fm)) |>.nextPC
  | .fmulR fd fn fm =>
      s.setFReg fd (FloatBinOp.eval .fmul (s.fregs fn) (s.fregs fm)) |>.nextPC
  | .fdivR fd fn fm =>
      s.setFReg fd (FloatBinOp.eval .fdiv (s.fregs fn) (s.fregs fm)) |>.nextPC
  | .fmaddR fd fn fm fa =>
      s.setFReg fd (FloatBinOp.eval .fadd (s.fregs fa)
        (FloatBinOp.eval .fmul (s.fregs fn) (s.fregs fm))) |>.nextPC
  | .fmsubR fd fn fm fa =>
      s.setFReg fd (FloatBinOp.eval .fsub (s.fregs fa)
        (FloatBinOp.eval .fmul (s.fregs fn) (s.fregs fm))) |>.nextPC
  | .fminR fd fn fm =>
      s.setFReg fd (FloatBinOp.eval .fmin (s.fregs fn) (s.fregs fm)) |>.nextPC
  | .fmaxR fd fn fm =>
      s.setFReg fd (FloatBinOp.eval .fmax (s.fregs fn) (s.fregs fm)) |>.nextPC
  | .callBinF fop fd fn fm =>
      s.havocCallerSaved (havocRegsFn s) (havocFRegsFn s)
        |>.setFReg fd (FloatBinOp.eval fop (s.fregs fn) (s.fregs fm)) |>.nextPC
  | .fcmpR fn fm =>
      { s with flags := fcmpFlags (s.fregs fn) (s.fregs fm), pc := s.pc + 1 }
  | .scvtf fd rn => s.setFReg fd (intToFloatBv (s.regs rn)) |>.nextPC
  | .fcvtzs rd fn => s.setReg rd (floatToIntBv (s.fregs fn)) |>.nextPC
  | .farrLd fd arr idxReg =>
      s.setFReg fd (s.arrayMem arr (s.regs idxReg)) |>.nextPC
  | .farrSt arr idxReg valFReg =>
      s.setArrayMem arr (s.regs idxReg) (s.fregs valFReg) |>.nextPC
  | .floatUnaryInstr op fd fn =>
      if op.isNative = true then
        s.setFReg fd (op.eval (s.fregs fn)) |>.nextPC
      else
        s.havocCallerSaved (havocRegsFn s) (havocFRegsFn s)
          |>.setFReg fd (op.eval (s.fregs fn)) |>.nextPC

/-- **ArmStep full-state projection.**  Every `ArmStep` fires with a
    specific instruction at `s.pc`, and the successor state equals
    `armStepResult` applied to `s` and that instruction.  Companion to
    `ArmStep.pc_eq_armNextPC` — strictly stronger, since state equality
    implies PC equality. -/
private theorem ArmStep.eq_armStepResult {prog : ArmProg} {s s' : ArmState}
    (h : ArmStep prog s s') :
    ∃ i, prog[s.pc]? = some i ∧ s' = armStepResult s i := by
  cases h with
  | mov rd imm hi => exact ⟨_, hi, rfl⟩
  | movR rd rn hi => exact ⟨_, hi, rfl⟩
  | movz rd imm sh hi => exact ⟨_, hi, rfl⟩
  | movk rd imm sh hi => exact ⟨_, hi, rfl⟩
  | ldr rd off hi => exact ⟨_, hi, rfl⟩
  | str rs off hi => exact ⟨_, hi, rfl⟩
  | addR _ _ _ hi => exact ⟨_, hi, rfl⟩
  | subR _ _ _ hi => exact ⟨_, hi, rfl⟩
  | mulR _ _ _ hi => exact ⟨_, hi, rfl⟩
  | sdivR _ _ _ hi => exact ⟨_, hi, rfl⟩
  | cmpRR _ _ hi => exact ⟨_, hi, rfl⟩
  | cmpRI _ _ hi => exact ⟨_, hi, rfl⟩
  | cset _ _ hi => exact ⟨_, hi, rfl⟩
  | cbz_taken rn lbl hi hz =>
    exact ⟨_, hi, by simp only [armStepResult, if_pos hz]⟩
  | cbz_fall rn lbl hi hnz =>
    exact ⟨_, hi, by simp only [armStepResult, if_neg hnz]⟩
  | cbnz_taken rn lbl hi hnz =>
    exact ⟨_, hi, by simp only [armStepResult, if_neg hnz]⟩
  | cbnz_fall rn lbl hi hz =>
    exact ⟨_, hi, by simp only [armStepResult, if_pos hz]⟩
  | bCond_taken c lbl hi hc =>
    exact ⟨_, hi, by simp only [armStepResult, if_pos hc]⟩
  | bCond_fall c lbl hi hc =>
    exact ⟨_, hi, by simp only [armStepResult, hc, if_false, Bool.false_eq_true]⟩
  | andImm _ _ _ hi => exact ⟨_, hi, rfl⟩
  | andR _ _ _ hi => exact ⟨_, hi, rfl⟩
  | eorImm _ _ _ hi => exact ⟨_, hi, rfl⟩
  | orrR _ _ _ hi => exact ⟨_, hi, rfl⟩
  | eorR _ _ _ hi => exact ⟨_, hi, rfl⟩
  | lslR _ _ _ hi => exact ⟨_, hi, rfl⟩
  | asrR _ _ _ hi => exact ⟨_, hi, rfl⟩
  | branch _ hi => exact ⟨_, hi, rfl⟩
  | printCall _ hi => exact ⟨_, hi, rfl⟩
  | callPrintI hi => exact ⟨_, hi, rfl⟩
  | callPrintB hi => exact ⟨_, hi, rfl⟩
  | callPrintF hi => exact ⟨_, hi, rfl⟩
  | callPrintS _ hi => exact ⟨_, hi, rfl⟩
  | arrLd _ _ _ hi => exact ⟨_, hi, rfl⟩
  | arrSt _ _ _ hi => exact ⟨_, hi, rfl⟩
  | fmovToFP _ _ hi => exact ⟨_, hi, rfl⟩
  | fmovRR _ _ hi => exact ⟨_, hi, rfl⟩
  | fldr _ _ hi => exact ⟨_, hi, rfl⟩
  | fstr _ _ hi => exact ⟨_, hi, rfl⟩
  | faddR _ _ _ hi => exact ⟨_, hi, rfl⟩
  | fsubR _ _ _ hi => exact ⟨_, hi, rfl⟩
  | fmulR _ _ _ hi => exact ⟨_, hi, rfl⟩
  | fdivR _ _ _ hi => exact ⟨_, hi, rfl⟩
  | fmaddR _ _ _ _ hi => exact ⟨_, hi, rfl⟩
  | fmsubR _ _ _ _ hi => exact ⟨_, hi, rfl⟩
  | fminR _ _ _ hi => exact ⟨_, hi, rfl⟩
  | fmaxR _ _ _ hi => exact ⟨_, hi, rfl⟩
  | callBinF _ _ _ _ hi => exact ⟨_, hi, rfl⟩
  | fcmpRR _ _ hi => exact ⟨_, hi, rfl⟩
  | scvtf _ _ hi => exact ⟨_, hi, rfl⟩
  | fcvtzs _ _ hi => exact ⟨_, hi, rfl⟩
  | farrLd _ _ _ hi => exact ⟨_, hi, rfl⟩
  | farrSt _ _ _ hi => exact ⟨_, hi, rfl⟩
  | floatUnaryNative _ _ _ hi hN =>
    exact ⟨_, hi, by simp only [armStepResult, if_pos hN]⟩
  | floatUnaryLibCall _ _ _ hi hN =>
    exact ⟨_, hi, by simp only [armStepResult, hN, if_false, Bool.false_eq_true]⟩

/-- **ARM step determinism.**  Under the deterministic-havoc pivot,
    two `ArmStep`s from the same pre-state produce identical successor
    states — not just identical PCs.  Proof: project both via
    `ArmStep.eq_armStepResult`, match instructions by `Option.some.inj`,
    rewrite. -/
private theorem arm_step_det {prog : ArmProg} {s s₁ s₂ : ArmState}
    (h1 : ArmStep prog s s₁) (h2 : ArmStep prog s s₂) : s₁ = s₂ := by
  obtain ⟨i1, hi1, he1⟩ := h1.eq_armStepResult
  obtain ⟨i2, hi2, he2⟩ := h2.eq_armStepResult
  have : i1 = i2 := Option.some.inj (hi1 ▸ hi2)
  rw [he1, he2, this]

/-- **Phase 6 helper: step-count state uniqueness.**  Two `ArmStepsN`
    traces from the same initial state, of the same length, end in the
    same state.  Direct induction on `n` using `arm_step_det`: at the
    inductive step both traces take a first `ArmStep` from `s₀`, which
    by determinism go to the same intermediate state.

    **Pivot payoff.**  Pre-pivot this lemma failed at the inductive
    step (two traces could land in different intermediate states
    because `ArmStep` was nondeterministic at havoc sites).  The
    deterministic-havoc pivot replaces the existential newRegs/newFregs
    with opaque oracles, restoring functional determinism and making
    this a direct induction (probe PD2 validated the scaling). -/
theorem step_count_state_uniqueness {prog : ArmProg} {s₀ : ArmState} :
    ∀ n (s₁ s₂ : ArmState),
      ArmStepsN prog s₀ s₁ n → ArmStepsN prog s₀ s₂ n → s₁ = s₂ := by
  intro n
  induction n generalizing s₀ with
  | zero =>
    intro s₁ s₂ h1 h2
    change s₀ = s₁ at h1
    change s₀ = s₂ at h2
    subst h1; subst h2; rfl
  | succ n ih =>
    intro s₁ s₂ h1 h2
    obtain ⟨m₁, hs₁, hr₁⟩ := h1
    obtain ⟨m₂, hs₂, hr₂⟩ := h2
    have hmid : m₁ = m₂ := arm_step_det hs₁ hs₂
    subst hmid
    exact ih _ _ hr₁ hr₂

/-- **Phase 6 helper: step-count PC uniqueness.**  Two `ArmStepsN` traces
    from the same initial state, of the same length, end at the same PC.
    Direct corollary of `step_count_state_uniqueness` via `.pc` projection. -/
theorem step_count_pc_uniqueness {prog : ArmProg} {s₀ : ArmState} :
    ∀ n (s₁ s₂ : ArmState),
      ArmStepsN prog s₀ s₁ n → ArmStepsN prog s₀ s₂ n → s₁.pc = s₂.pc := by
  intro n s₁ s₂ h1 h2
  exact congrArg ArmState.pc (step_count_state_uniqueness n s₁ s₂ h1 h2)

end Phase6Skeleton

-- ============================================================
-- § 9. Phase 7 — Backward theorems ARM → While (SKELETON)
-- ============================================================

/-!
## Phase 7 skeleton

Four backward theorems promoting ARM observations into source-side
conclusions.  Together with the existing forward theorems
(`while_to_arm_correctness`, `while_to_arm_div_preservation`,
`while_to_arm_bounds_preservation`, `while_to_arm_divergence_preservation`)
these establish full bidirectional end-to-end correctness.

Schema (Phase 7): apply source totality via
`pipelined_has_behavior`.  For each source-behavior bin, forward sim
places ARM in a specific sentinel.  Use sentinel distinctness (all three
`rfl`/`omega` from `spec.haltFinal_eq`, `spec.divS_eq`, `spec.boundsS_eq`)
and `step_count_pc_uniqueness` to rule out non-matching source bins.
The `typeErrors` source branch is excluded by pipeline-preserved
well-typedness.
-/

section Phase7Skeleton

/-- `checkCertificateExec cert = true` implies `checkStepClosed cert.trans = true`.
    Extracted from condition 6 (`checkSuccessorsInBounds`) of the big checker. -/
private theorem stepClosed_of_checkCertificateExec {cert : ECertificate}
    (h : checkCertificateExec cert = true) : checkStepClosed cert.trans = true := by
  unfold checkCertificateExec at h
  -- Peel the right-associated conjunction to reach hSIB (the 18th-from-the-top conjunct).
  have ⟨h29, _⟩         := and_true_split h
  have ⟨h28, _⟩         := and_true_split h29
  have ⟨h27, _⟩         := and_true_split h28
  have ⟨h26, _⟩         := and_true_split h27
  have ⟨h25, _⟩         := and_true_split h26
  have ⟨h24, _⟩         := and_true_split h25
  have ⟨h23, _⟩         := and_true_split h24
  have ⟨h22, _⟩         := and_true_split h23
  have ⟨h21, _⟩         := and_true_split h22
  have ⟨h20, _⟩         := and_true_split h21
  have ⟨h19, _⟩         := and_true_split h20
  have ⟨_, hSIB⟩        := and_true_split h19
  -- hSIB : checkSuccessorsInBounds cert = true; this unfolds to checkStepClosed cert.trans.
  exact hSIB

/-- A single pass preserves `StepClosedInBounds` (Prop form).  Extracted
    from the certificate checker's `checkSuccessorsInBounds` conjunct via
    `checkStepClosed_sound`. -/
theorem applyPass_preserves_stepClosedInBounds {name : String} {tyCtx : TyCtx}
    {pass : Prog → ECertificate} {p p' : Prog}
    (h : applyPass name tyCtx pass p = .ok p') :
    StepClosedInBounds p' := by
  obtain ⟨hcheck, hTrans, _, _, _⟩ := applyPass_sound h
  have hSC := stepClosed_of_checkCertificateExec
    (cert := { pass p with tyCtx := tyCtx }) hcheck
  simp only [hTrans] at hSC
  exact checkStepClosed_sound hSC

/-- `applyPasses` preserves `StepClosedInBounds` (Prop form). -/
theorem applyPasses_preserves_stepClosedInBounds (tyCtx : TyCtx)
    (passes : List (String × (Prog → ECertificate)))
    (p : Prog) (hSC : StepClosedInBounds p) :
    StepClosedInBounds (applyPasses tyCtx passes p) := by
  induction passes generalizing p with
  | nil => simp [applyPasses]; exact hSC
  | cons np rest ih =>
    simp only [applyPasses]
    obtain ⟨name, pass⟩ := np
    split
    · rename_i p' hap
      exact ih p' (applyPass_preserves_stepClosedInBounds hap)
    · exact ih p hSC

/-- **Phase 7 helper: pipelined TAC has a well-defined behavior.**
    Pushes `compileToTAC_stepClosed` through the passes via
    `applyPasses_preserves_stepClosedInBounds`, then appeals to
    `has_behavior`. -/
theorem pipelined_has_behavior
    (prog : Program) (htcs : prog.wellFormed = true)
    (passes : List (String × (Prog → ECertificate)))
    (σ₀ : Store) :
    ∃ b, program_behavior
      (applyPasses prog.tyCtx passes prog.compileToTAC) σ₀ b := by
  have htc := prog.wellFormed_typeCheck htcs
  have hSC0 : StepClosedInBounds prog.compileToTAC :=
    prog.compileToTAC_stepClosed htc
  have hSC := applyPasses_preserves_stepClosedInBounds prog.tyCtx passes _ hSC0
  exact has_behavior _ σ₀ hSC

/-- **Phase 7 helper: pipelined TAC does not reach `typeError`.**
    Well-typedness is preserved through passes (from
    `applyPasses_preserves_invariants`), `StepClosedInBounds`
    through `applyPasses_preserves_stepClosedInBounds`, and
    `type_safety` in TypeSystem.lean excludes `typeError` at runtime. -/
theorem pipelined_no_typeError
    (prog : Program) (htcs : prog.wellFormed = true)
    (passes : List (String × (Prog → ECertificate)))
    (σ' : Store) (am' : ArrayMem) :
    ¬ ((applyPasses prog.tyCtx passes prog.compileToTAC) ⊩
        Cfg.run 0 (Store.typedInit prog.tyCtx) ArrayMem.init ⟶* Cfg.typeError σ' am') := by
  have htc := prog.wellFormed_typeCheck htcs
  have hWT0 : checkWellTypedProg prog.tyCtx prog.compileToTAC = true :=
    checkWellTypedProg_complete (prog.compileToTAC_wellTyped htc)
  have hPrereqs0 := compileToTAC_codegenPrereqs prog htcs
  have hBranch0 := compileToTAC_checkBranchTargets prog
  have hSimple0 := compileToTAC_checkBoolExprSimpleOps prog
  obtain ⟨hWT, _, _, _⟩ :=
    applyPasses_preserves_invariants prog.tyCtx passes prog.compileToTAC
      hWT0 hPrereqs0 hBranch0 hSimple0
  have hWTP : WellTypedProg prog.tyCtx (applyPasses prog.tyCtx passes prog.compileToTAC) :=
    checkWellTypedProg_sound hWT
  have hSC : StepClosedInBounds (applyPasses prog.tyCtx passes prog.compileToTAC) :=
    applyPasses_preserves_stepClosedInBounds prog.tyCtx passes _
      (prog.compileToTAC_stepClosed htc)
  have hts : TypedStore prog.tyCtx (Store.typedInit prog.tyCtx) := TypedStore.typedInit _
  exact type_safety hWTP hts hSC

/-!
### Fix B' infrastructure — self-loop divergence

"Fix B'" handles source-level divergence by recognizing
its realization as a self-loop at the ARM level.  Given a TAC self-loop
(`.goto pc` or an `.ifgoto` whose guard evaluates to `true`) at pc, the
emitted ARM instruction is an unconditional branch back to the same PC,
so a single `ArmStep` returns to the current state.  From there
`ArmDiverges` follows immediately (witness every step count with the
repeating state itself).
-/

/-- **Fix B' primitive: ArmDiverges from a self-loop step.**  A single
    `ArmStep` that returns to the same state witnesses divergence: every
    length `n` has a trace (namely the one that repeats `s`). -/
theorem arm_self_loop_diverges {prog : ArmProg} {s : ArmState}
    (h : ArmStep prog s s) : ArmDiverges prog s := by
  intro n
  induction n with
  | zero => exact ⟨s, rfl⟩
  | succ k ih =>
    obtain ⟨s'', hk⟩ := ih
    exact ⟨s'', s, h, hk⟩

/-- **Fix B' primitive: ArmDiverges lifted through a prefix.**  If
    `init` reaches a self-loop state `s` in finitely many steps, then
    `init` diverges.  Case-splits on whether the target step count is
    inside the prefix (truncate) or past it (compose with repeated
    self-loop steps). -/
theorem arm_diverges_of_prefix_reaches_self_loop
    {prog : ArmProg} {init s : ArmState}
    (hReach : ArmSteps prog init s)
    (hSelf : ArmStep prog s s) : ArmDiverges prog init := by
  intro n
  obtain ⟨k, hK⟩ := ArmSteps_to_ArmStepsN hReach
  have hDiv : ArmDiverges prog s := arm_self_loop_diverges hSelf
  by_cases hnk : n ≤ k
  · have : ∃ m, k = n + m := ⟨k - n, by omega⟩
    obtain ⟨m, hm⟩ := this
    rw [hm] at hK
    exact ArmStepsN_prefix hK
  · obtain ⟨s', hDiv'⟩ := hDiv (n - k)
    have heq : k + (n - k) = n := by omega
    refine ⟨s', ?_⟩
    rw [← heq]
    exact ArmStepsN_trans hK hDiv'

/-- **Fix B' primitive: TAC `.goto pc` self-loop → ARM self-loop.**

    Given a TAC instruction `.goto pc` at PC pc (self-loop) and an ARM
    state `s` matching via `ExtSimRel`, the ARM code at `pcMap pc` is
    `.b (pcMap pc)` (from `spec.instrGen` + `verifiedGenInstr`
    unfolding), and executing it from `s` (whose `s.pc = pcMap pc`)
    yields `s` again.  Hence `ArmStep r.bodyFlat s s`. -/
theorem tac_goto_self_loop_implies_arm_self_loop
    {tyCtx : TyCtx} {p : Prog} {r : VerifiedAsmResult}
    (spec : GenAsmSpec tyCtx p r)
    {pc : Nat} {σ : Store} {am : ArrayMem} {s : ArmState}
    (hRel : ExtSimRel r.layout r.pcMap r.divS r.boundsS (.run pc σ am) s)
    (hPC : pc < p.size)
    (hGoto : p[pc] = TAC.goto pc) :
    ArmStep r.bodyFlat s s := by
  have hsPc : s.pc = r.pcMap pc := hRel.2.1
  have hNotLib : isLibCallTAC p[pc] = false := by rw [hGoto]; rfl
  have hNotPrint : ∀ fmt vs, p[pc] ≠ .print fmt vs := by
    intro fmt vs h; rw [hGoto] at h; exact TAC.noConfusion h
  have hGenInstr := spec.instrGen pc hPC hNotLib hNotPrint
  rw [hGoto] at hGenInstr
  have hBodyEq : r.bodyPerPC[pc]'(spec.bodySize ▸ hPC) = [ArmInstr.b (r.pcMap pc)] := by
    simp only [verifiedGenInstr, Option.some.injEq] at hGenInstr
    exact hGenInstr.symm
  obtain ⟨lengths, hLSz, hPcMap, hLenEq⟩ := spec.pcMapLengths
  have hCodeAt0 :=
    codeAt_of_bodyFlat' r lengths hLSz hLenEq pc (spec.bodySize ▸ hPC)
  rw [← hPcMap] at hCodeAt0
  rw [hBodyEq] at hCodeAt0
  have hCode : r.bodyFlat[r.pcMap pc]? = some (ArmInstr.b (r.pcMap pc)) :=
    hCodeAt0.head
  have hCode' : r.bodyFlat[s.pc]? = some (ArmInstr.b (r.pcMap pc)) := by
    rw [hsPc]; exact hCode
  have hStep := ArmStep.branch (r.pcMap pc) hCode'
  have hsEq : { s with pc := r.pcMap pc } = s := by rw [← hsPc]
  rw [hsEq] at hStep
  exact hStep

/-- **ArmStepsN split-at-prefix helper.**  A length-`(n+k)` ArmStepsN trace
    factors through a midpoint at length `n`.  Dual to `ArmStepsN_split_last`. -/
private theorem ArmStepsN_split_first {prog : ArmProg} :
    ∀ (n k : Nat) {s s' : ArmState},
      ArmStepsN prog s s' (n + k) →
      ∃ s_mid, ArmStepsN prog s s_mid n ∧ ArmStepsN prog s_mid s' k := by
  intro n k
  induction n with
  | zero =>
    intro s s' h
    rw [Nat.zero_add] at h
    exact ⟨s, rfl, h⟩
  | succ n ih =>
    intro s s' h
    rw [show n + 1 + k = (n + k) + 1 from by omega] at h
    obtain ⟨m, hStep, hRest⟩ := h
    obtain ⟨s_mid, h1, h2⟩ := ih hRest
    exact ⟨s_mid, ⟨m, hStep, h1⟩, h2⟩

/-- **Sentinel-state collision.**  Two `ArmSteps` from a common start ending
    at sentinel PCs force full-state equality (hence PC equality).  Generalizes
    `halt_state_observables_deterministic` to any pair of sentinel endpoints.
    Same proof shape: equalize lengths at the shorter via
    `step_count_state_uniqueness`, then surplus steps are ruled out by
    `sentinel_stuck`. -/
private theorem sentinel_state_unique
    {tyCtx : TyCtx} {p : Prog} {r : VerifiedAsmResult}
    (spec : GenAsmSpec tyCtx p r)
    {init s₁ s₂ : ArmState}
    (h₁ : ArmSteps r.bodyFlat init s₁)
    (hSent₁ : s₁.pc = r.haltFinal ∨ s₁.pc = r.divS ∨ s₁.pc = r.boundsS)
    (h₂ : ArmSteps r.bodyFlat init s₂)
    (hSent₂ : s₂.pc = r.haltFinal ∨ s₂.pc = r.divS ∨ s₂.pc = r.boundsS) :
    s₁ = s₂ := by
  have stuck : ∀ (d : Nat) (s s' : ArmState),
      (s.pc = r.haltFinal ∨ s.pc = r.divS ∨ s.pc = r.boundsS) →
      ArmStepsN r.bodyFlat s s' d → s = s' := by
    intro d s s' hs hN
    cases d with
    | zero => exact hN
    | succ _ =>
      obtain ⟨m, hStep, _⟩ := hN
      exact absurd ⟨m, hStep⟩ (sentinel_stuck spec hs)
  obtain ⟨k₁, hN₁⟩ := ArmSteps_to_ArmStepsN h₁
  obtain ⟨k₂, hN₂⟩ := ArmSteps_to_ArmStepsN h₂
  by_cases hle : k₁ ≤ k₂
  · have hd : k₂ = k₁ + (k₂ - k₁) := by omega
    rw [hd] at hN₂
    obtain ⟨s_mid, h_pre, h_suf⟩ := ArmStepsN_split_first k₁ (k₂ - k₁) hN₂
    have hmid := step_count_state_uniqueness k₁ s_mid s₁ h_pre hN₁
    rw [hmid] at h_suf
    exact stuck _ _ _ hSent₁ h_suf
  · push_neg at hle
    have hd : k₁ = k₂ + (k₁ - k₂) := by omega
    rw [hd] at hN₁
    obtain ⟨s_mid, h_pre, h_suf⟩ := ArmStepsN_split_first k₂ (k₁ - k₂) hN₁
    have hmid := step_count_state_uniqueness k₂ s_mid s₂ h_pre hN₂
    rw [hmid] at h_suf
    exact (stuck _ _ _ hSent₂ h_suf).symm

/-- **Phase 7 auxiliary: source divergence gives ARM divergence.**

    Given an infinite TAC execution of the pipelined program starting from
    `init`, produce `ArmDiverges r.bodyFlat (initArmState r)`.  This is the
    Step 2 composition theorem, needed
    by the `.diverges` branch of Phase 7a/b/c to rule out a source-diverges
    coexisting with a sentinel ARM reach.

    Proof strategy (plans §§Step 2 approach b + Step 1): for each `n`,
    forward sim of `StepsN (f 0) (f n)` via `tacToArm_correctness` produces
    `ArmStepsN init s_n m_n`.  Show the `m_n` sequence is unbounded OR
    a source self-loop produces an ARM cycle (multi-step Fix B').  In the
    former case, truncate via `ArmStepsN_prefix` to hit any target `N`.
    In the latter, `arm_diverges_of_prefix_reaches_cycle` (generalized
    Fix B') gives the conclusion directly.

    **Status: deferred.**  External analysis of `step_simulation`'s
    length-positive output + case-split on source self-loops requires
    substantial additional infrastructure.  Landed as a stated hypothesis
    so Phase 7a/b/c can close their `.diverges` branches. -/
private theorem source_diverges_gives_ArmDiverges_init
    (prog : Program) (htcs : prog.wellFormed = true)
    (passes : List (String × (Prog → ECertificate)))
    {r : VerifiedAsmResult}
    (hGen : verifiedGenerateAsm prog.tyCtx
      (applyPasses prog.tyCtx passes prog.compileToTAC) = .ok r)
    {f : Nat → Cfg}
    (hinf : IsInfiniteExec (applyPasses prog.tyCtx passes prog.compileToTAC) f)
    (hf0 : f 0 = Cfg.run 0 prog.initStore ArrayMem.init) :
    ArmDiverges r.bodyFlat (r.initArmState) := by
  intro N
  -- StepsN of any length extracted from IsInfiniteExec by induction
  have hStepsN_any : ∀ k, StepsN (applyPasses prog.tyCtx passes prog.compileToTAC)
      (f 0) (f k) k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => exact StepsN_extend ih (hinf.2 k)
  have hStepsN := hStepsN_any (N + 1)
  -- Connect f 0 = .run 0 prog.initStore ArrayMem.init to Store.typedInit form
  have htc := Program.wellFormed_typeCheck prog htcs
  have hInitEq : Store.typedInit prog.tyCtx = prog.initStore :=
    Program.typedInit_eq_initStore prog htc
  rw [hf0, ← hInitEq, show ArrayMem.init = (fun _ _ => 0) from rfl] at hStepsN
  -- f (N+1) is a .run config
  obtain ⟨pc_end, σ_end, am_end, hfend⟩ := inf_exec_is_run hinf (N + 1)
  rw [hfend] at hStepsN
  -- Apply length-tracked correctness
  obtain ⟨s_fwd, k, hArmN, hk_bound, _, _⟩ := tacToArm_correctness_N hGen hStepsN
  have hN1_le_k : N + 1 ≤ k := hk_bound pc_end σ_end am_end rfl
  -- Truncate to length N via ArmStepsN_prefix
  obtain ⟨d, hd⟩ : ∃ d, k = N + d := ⟨k - N, by omega⟩
  rw [hd] at hArmN
  exact ArmStepsN_prefix hArmN

/-- **Phase 7 helper: observable determinism at `haltFinal`.**  Under the
    deterministic-havoc pivot, any two ARM states at `haltFinal` reached
    from `init` are *equal* (not just observably equivalent).  Proof:
    equalize trace lengths via `step_count_state_uniqueness` at the
    shorter length; any surplus steps from a `haltFinal` state contradict
    `sentinel_stuck`. -/
theorem halt_state_observables_deterministic
    (prog : Program) (htcs : prog.wellFormed = true)
    (passes : List (String × (Prog → ECertificate)))
    {r : VerifiedAsmResult}
    (hGen : verifiedGenerateAsm prog.tyCtx
      (applyPasses prog.tyCtx passes prog.compileToTAC) = .ok r)
    {s₁ s₂ : ArmState}
    (h₁ : ArmSteps r.bodyFlat (r.initArmState) s₁) (hPC₁ : s₁.pc = r.haltFinal)
    (h₂ : ArmSteps r.bodyFlat (r.initArmState) s₂) (hPC₂ : s₂.pc = r.haltFinal) :
    (∀ v loc, r.layout v = some loc →
      (match loc with
       | .stack off => s₁.stack off = s₂.stack off
       | .ireg ir   => s₁.regs ir  = s₂.regs ir
       | .freg fr   => s₁.fregs fr = s₂.fregs fr)) ∧
    s₁.arrayMem = s₂.arrayMem := by
  have spec := verifiedGenerateAsm_spec hGen
  have stuck : ∀ (d : Nat) (s s' : ArmState), s.pc = r.haltFinal →
      ArmStepsN r.bodyFlat s s' d → s = s' := by
    intro d s s' hs hN
    cases d with
    | zero => exact hN
    | succ _ =>
      obtain ⟨m, hStep, _⟩ := hN
      exact absurd ⟨m, hStep⟩ (sentinel_stuck spec (.inl hs))
  obtain ⟨k₁, hN₁⟩ := ArmSteps_to_ArmStepsN h₁
  obtain ⟨k₂, hN₂⟩ := ArmSteps_to_ArmStepsN h₂
  have hEq : s₁ = s₂ := by
    by_cases hle : k₁ ≤ k₂
    · have hd : k₂ = k₁ + (k₂ - k₁) := by omega
      rw [hd] at hN₂
      obtain ⟨s_mid, h_pre, h_suf⟩ := ArmStepsN_split_first k₁ (k₂ - k₁) hN₂
      have hmid := step_count_state_uniqueness k₁ s_mid s₁ h_pre hN₁
      rw [hmid] at h_suf
      exact stuck _ _ _ hPC₁ h_suf
    · push_neg at hle
      have hd : k₁ = k₂ + (k₁ - k₂) := by omega
      rw [hd] at hN₁
      obtain ⟨s_mid, h_pre, h_suf⟩ := ArmStepsN_split_first k₂ (k₁ - k₂) hN₁
      have hmid := step_count_state_uniqueness k₂ s_mid s₂ h_pre hN₂
      rw [hmid] at h_suf
      exact (stuck _ _ _ hPC₂ h_suf).symm
  subst hEq
  refine ⟨fun _ loc _ => ?_, rfl⟩
  cases loc <;> rfl

/-- **Phase 7a — ARM halt implies source halt with matching observables.**

    Forward counterpart: `while_to_arm_correctness`.  Given an ARM trace
    ending at `haltFinal`, the source program halts safely and its output
    store + array memory match the ARM state's observables.

    Proof outline: apply `pipelined_has_behavior`; case on the source bin;
    use `while_to_arm_correctness`/`..._div`/`..._bounds` to place ARM
    in a specific sentinel for each non-matching bin; contradict via
    `step_count_pc_uniqueness` + sentinel distinctness.  For the
    `halts` bin, match observables via `halt_state_observables_deterministic`.
    `typeErrors` excluded via `pipelined_no_typeError`; `diverges` excluded
    via `ArmDiverges` reaching-vs-stuck argument (Phase 7a). -/
theorem arm_halts_implies_program_halts
    (prog : Program) (htcs : prog.wellFormed = true)
    (passes : List (String × (Prog → ECertificate)))
    {r : VerifiedAsmResult}
    (hGen : verifiedGenerateAsm prog.tyCtx
      (applyPasses prog.tyCtx passes prog.compileToTAC) = .ok r)
    {s : ArmState}
    (hArm : ArmSteps r.bodyFlat (r.initArmState) s)
    (hPC : s.pc = r.haltFinal) :
    ∃ fuel σ_src am_src,
      prog.run fuel = .halts σ_src am_src ∧
      ArmStateMatchesProgramState s r.layout prog.compileToTAC.observable σ_src am_src := by
  have htc := prog.wellFormed_typeCheck htcs
  have hSC : StepClosedInBounds (applyPasses prog.tyCtx passes prog.compileToTAC) :=
    applyPasses_preserves_stepClosedInBounds prog.tyCtx passes _
      (prog.compileToTAC_stepClosed htc)
  have spec := verifiedGenerateAsm_spec hGen
  obtain ⟨b, hbeh⟩ := has_behavior_init _ (Store.typedInit prog.tyCtx) hSC
  cases b with
  | halts σ_opt =>
    obtain ⟨am_opt, hhalt⟩ := hbeh
    obtain ⟨fuel, σ_src, am_src, s', hinterp, hArm', hMatch, hPC'⟩ :=
      while_to_arm_correctness prog htcs passes hGen hhalt
    have heq := sentinel_state_unique spec hArm (.inl hPC) hArm' (.inl hPC')
    subst heq
    exact ⟨fuel, σ_src, am_src, (Program.run_halts_iff prog fuel σ_src am_src).mpr hinterp, hMatch⟩
  | errorDiv σ_opt =>
    exfalso
    obtain ⟨am_opt, hErrDiv⟩ := hbeh
    obtain ⟨s', hArm', hPC'⟩ :=
      (while_to_arm_div_preservation prog htcs passes hGen hErrDiv).2
    have heq := sentinel_state_unique spec hArm (.inl hPC) hArm' (.inr (.inl hPC'))
    have : s.pc = s'.pc := congrArg ArmState.pc heq
    rw [hPC, hPC'] at this
    exact (haltFinal_ne_divS spec) this
  | errorBounds σ_opt =>
    exfalso
    obtain ⟨am_opt, hErrBounds⟩ := hbeh
    obtain ⟨s', hArm', hPC'⟩ :=
      (while_to_arm_bounds_preservation prog htcs passes hGen hErrBounds).2
    have heq := sentinel_state_unique spec hArm (.inl hPC) hArm' (.inr (.inr hPC'))
    have : s.pc = s'.pc := congrArg ArmState.pc heq
    rw [hPC, hPC'] at this
    exact (haltFinal_ne_boundsS spec) this
  | typeErrors σ_opt =>
    exfalso
    obtain ⟨am_opt, hte⟩ := hbeh
    exact absurd hte (pipelined_no_typeError prog htcs passes σ_opt am_opt)
  | diverges =>
    exfalso
    obtain ⟨f, hinf, hf0⟩ := hbeh
    have hInitEq : Store.typedInit prog.tyCtx = prog.initStore :=
      Program.typedInit_eq_initStore prog htc
    have hDiv : ArmDiverges r.bodyFlat (r.initArmState) :=
      source_diverges_gives_ArmDiverges_init prog htcs passes hGen hinf (hInitEq ▸ hf0)
    obtain ⟨n_reach, hN_reach⟩ := ArmSteps_to_ArmStepsN hArm
    obtain ⟨s_ext, hN_ext⟩ := hDiv (n_reach + 1)
    obtain ⟨s_mid, hN_mid, hStep_last⟩ := ArmStepsN_split_last hN_ext
    have hmid_eq : s_mid = s :=
      step_count_state_uniqueness n_reach s_mid s hN_mid hN_reach
    rw [hmid_eq] at hStep_last
    exact sentinel_stuck spec (.inl hPC) ⟨s_ext, hStep_last⟩

/-- **Phase 7b — ARM div-by-zero sentinel implies source unsafe (division).**

    Forward counterpart: `while_to_arm_div_preservation`.  Given an ARM
    trace ending at `divS`, the source program is unsafe at some fuel with
    cause = division by zero.

    Proof size: ~60 LOC. -/
theorem arm_div_implies_program_unsafe_div
    (prog : Program) (htcs : prog.wellFormed = true)
    (passes : List (String × (Prog → ECertificate)))
    {r : VerifiedAsmResult}
    (hGen : verifiedGenerateAsm prog.tyCtx
      (applyPasses prog.tyCtx passes prog.compileToTAC) = .ok r)
    {s : ArmState}
    (hArm : ArmSteps r.bodyFlat (r.initArmState) s)
    (hPC : s.pc = r.divS) :
    ∃ fuel, prog.run fuel = .divByZero := by
  have htc := prog.wellFormed_typeCheck htcs
  have hSC : StepClosedInBounds (applyPasses prog.tyCtx passes prog.compileToTAC) :=
    applyPasses_preserves_stepClosedInBounds prog.tyCtx passes _
      (prog.compileToTAC_stepClosed htc)
  have spec := verifiedGenerateAsm_spec hGen
  obtain ⟨b, hbeh⟩ := has_behavior_init _ (Store.typedInit prog.tyCtx) hSC
  cases b with
  | halts σ_opt =>
    exfalso
    obtain ⟨am_opt, hhalt⟩ := hbeh
    obtain ⟨_, _, _, s', _, hArm', _, hPC'⟩ :=
      while_to_arm_correctness prog htcs passes hGen hhalt
    have heq := sentinel_state_unique spec hArm (.inr (.inl hPC)) hArm' (.inl hPC')
    have : s.pc = s'.pc := congrArg ArmState.pc heq
    rw [hPC, hPC'] at this
    exact (haltFinal_ne_divS spec) this.symm
  | errorDiv σ_opt =>
    obtain ⟨am_opt, hErrDiv⟩ := hbeh
    obtain ⟨fuel, hud⟩ := while_to_arm_errorDiv_source_side prog htcs passes hErrDiv
    exact ⟨fuel, (Program.run_divByZero_iff prog fuel).mpr hud⟩
  | errorBounds σ_opt =>
    exfalso
    obtain ⟨am_opt, hErrBounds⟩ := hbeh
    obtain ⟨s', hArm', hPC'⟩ :=
      (while_to_arm_bounds_preservation prog htcs passes hGen hErrBounds).2
    have heq := sentinel_state_unique spec hArm (.inr (.inl hPC)) hArm' (.inr (.inr hPC'))
    have : s.pc = s'.pc := congrArg ArmState.pc heq
    rw [hPC, hPC'] at this
    exact (divS_ne_boundsS spec) this
  | typeErrors σ_opt =>
    obtain ⟨am_opt, hte⟩ := hbeh
    exact absurd hte (pipelined_no_typeError prog htcs passes σ_opt am_opt)
  | diverges =>
    exfalso
    obtain ⟨f, hinf, hf0⟩ := hbeh
    have hInitEq : Store.typedInit prog.tyCtx = prog.initStore :=
      Program.typedInit_eq_initStore prog htc
    have hDiv : ArmDiverges r.bodyFlat (r.initArmState) :=
      source_diverges_gives_ArmDiverges_init prog htcs passes hGen hinf (hInitEq ▸ hf0)
    obtain ⟨n_reach, hN_reach⟩ := ArmSteps_to_ArmStepsN hArm
    obtain ⟨s_ext, hN_ext⟩ := hDiv (n_reach + 1)
    obtain ⟨s_mid, hN_mid, hStep_last⟩ := ArmStepsN_split_last hN_ext
    have hmid_eq : s_mid = s :=
      step_count_state_uniqueness n_reach s_mid s hN_mid hN_reach
    rw [hmid_eq] at hStep_last
    exact sentinel_stuck spec (.inr (.inl hPC)) ⟨s_ext, hStep_last⟩

/-- **Phase 7c — ARM bounds sentinel implies source unsafe (bounds).**

    Symmetric to 7b; forward counterpart is `while_to_arm_bounds_preservation`.

    Proof size: ~60 LOC. -/
theorem arm_bounds_implies_program_unsafe_bounds
    (prog : Program) (htcs : prog.wellFormed = true)
    (passes : List (String × (Prog → ECertificate)))
    {r : VerifiedAsmResult}
    (hGen : verifiedGenerateAsm prog.tyCtx
      (applyPasses prog.tyCtx passes prog.compileToTAC) = .ok r)
    {s : ArmState}
    (hArm : ArmSteps r.bodyFlat (r.initArmState) s)
    (hPC : s.pc = r.boundsS) :
    ∃ fuel, prog.run fuel = .outOfBounds := by
  have htc := prog.wellFormed_typeCheck htcs
  have hSC : StepClosedInBounds (applyPasses prog.tyCtx passes prog.compileToTAC) :=
    applyPasses_preserves_stepClosedInBounds prog.tyCtx passes _
      (prog.compileToTAC_stepClosed htc)
  have spec := verifiedGenerateAsm_spec hGen
  obtain ⟨b, hbeh⟩ := has_behavior_init _ (Store.typedInit prog.tyCtx) hSC
  cases b with
  | halts σ_opt =>
    exfalso
    obtain ⟨am_opt, hhalt⟩ := hbeh
    obtain ⟨_, _, _, s', _, hArm', _, hPC'⟩ :=
      while_to_arm_correctness prog htcs passes hGen hhalt
    have heq := sentinel_state_unique spec hArm (.inr (.inr hPC)) hArm' (.inl hPC')
    have : s.pc = s'.pc := congrArg ArmState.pc heq
    rw [hPC, hPC'] at this
    exact (haltFinal_ne_boundsS spec) this.symm
  | errorDiv σ_opt =>
    exfalso
    obtain ⟨am_opt, hErrDiv⟩ := hbeh
    obtain ⟨s', hArm', hPC'⟩ :=
      (while_to_arm_div_preservation prog htcs passes hGen hErrDiv).2
    have heq := sentinel_state_unique spec hArm (.inr (.inr hPC)) hArm' (.inr (.inl hPC'))
    have : s.pc = s'.pc := congrArg ArmState.pc heq
    rw [hPC, hPC'] at this
    exact (divS_ne_boundsS spec) this.symm
  | errorBounds σ_opt =>
    obtain ⟨am_opt, hErrBounds⟩ := hbeh
    obtain ⟨fuel, hub⟩ := while_to_arm_errorBounds_source_side prog htcs passes hErrBounds
    exact ⟨fuel, (Program.run_outOfBounds_iff prog fuel).mpr hub⟩
  | typeErrors σ_opt =>
    obtain ⟨am_opt, hte⟩ := hbeh
    exact absurd hte (pipelined_no_typeError prog htcs passes σ_opt am_opt)
  | diverges =>
    exfalso
    obtain ⟨f, hinf, hf0⟩ := hbeh
    have hInitEq : Store.typedInit prog.tyCtx = prog.initStore :=
      Program.typedInit_eq_initStore prog htc
    have hDiv : ArmDiverges r.bodyFlat (r.initArmState) :=
      source_diverges_gives_ArmDiverges_init prog htcs passes hGen hinf (hInitEq ▸ hf0)
    obtain ⟨n_reach, hN_reach⟩ := ArmSteps_to_ArmStepsN hArm
    obtain ⟨s_ext, hN_ext⟩ := hDiv (n_reach + 1)
    obtain ⟨s_mid, hN_mid, hStep_last⟩ := ArmStepsN_split_last hN_ext
    have hmid_eq : s_mid = s :=
      step_count_state_uniqueness n_reach s_mid s hN_mid hN_reach
    rw [hmid_eq] at hStep_last
    exact sentinel_stuck spec (.inr (.inr hPC)) ⟨s_ext, hStep_last⟩

/-- **Phase 7d — ARM divergence implies source divergence.**

    Forward counterpart: `while_to_arm_divergence_preservation`.  `ArmDiverges`
    is taken as hypothesis (we do not construct it — Phase 6 builds it via
    König where needed).

    Proof outline: apply `pipelined_has_behavior`; for each non-`diverges`
    source bin, forward sim gives `ArmSteps init s_sent` at a sentinel;
    use `ArmDiverges` to pick a step count `n > (ArmStepsN-length of the
    forward trace)`, yielding `ArmStepsN init s' n` with an outgoing
    `ArmStep`; by `step_count_pc_uniqueness` the step-`n` state's PC is
    the sentinel's; `sentinel_stuck` contradicts the outgoing step.

    Proof size: ~40 LOC. -/
theorem arm_diverges_implies_program_diverges
    (prog : Program) (htcs : prog.wellFormed = true)
    (passes : List (String × (Prog → ECertificate)))
    {r : VerifiedAsmResult}
    (hGen : verifiedGenerateAsm prog.tyCtx
      (applyPasses prog.tyCtx passes prog.compileToTAC) = .ok r)
    (hDiv : ArmDiverges r.bodyFlat (r.initArmState)) :
    ∀ fuel, prog.run fuel = .outOfFuel := by
  have htc := prog.wellFormed_typeCheck htcs
  have hInitEq : Store.typedInit prog.tyCtx = prog.initStore :=
    Program.typedInit_eq_initStore prog htc
  have hts : TypedStore prog.tyCtx (Store.typedInit prog.tyCtx) := TypedStore.typedInit _
  have hSC : StepClosedInBounds (applyPasses prog.tyCtx passes prog.compileToTAC) :=
    applyPasses_preserves_stepClosedInBounds prog.tyCtx passes _
      (prog.compileToTAC_stepClosed htc)
  have spec := verifiedGenerateAsm_spec hGen
  have sentinel_contradict : ∀ {s_sent : ArmState}
      (_hReach : ArmSteps r.bodyFlat (r.initArmState) s_sent)
      (_hPC : s_sent.pc = r.haltFinal ∨ s_sent.pc = r.divS ∨ s_sent.pc = r.boundsS),
      False := by
    intro s_sent hReach hPC
    obtain ⟨n, hReachN⟩ := ArmSteps_to_ArmStepsN hReach
    obtain ⟨s_ext, hExtN⟩ := hDiv (n + 1)
    obtain ⟨s_mid, hN_mid, hStep_last⟩ := ArmStepsN_split_last hExtN
    have hmid_eq : s_mid = s_sent :=
      step_count_state_uniqueness n s_mid s_sent hN_mid hReachN
    rw [hmid_eq] at hStep_last
    exact sentinel_stuck spec hPC ⟨s_ext, hStep_last⟩
  obtain ⟨b, hbeh⟩ := has_behavior_init _ (Store.typedInit prog.tyCtx) hSC
  cases b with
  | halts σ_opt =>
    exfalso
    obtain ⟨am_opt, hhalt⟩ := hbeh
    obtain ⟨_, _, _, s', _, hArm, _, hPC⟩ :=
      while_to_arm_correctness prog htcs passes hGen hhalt
    exact sentinel_contradict hArm (.inl hPC)
  | errorDiv σ_opt =>
    exfalso
    obtain ⟨am_opt, hErrDiv⟩ := hbeh
    obtain ⟨s', hArm, hPC⟩ :=
      (while_to_arm_div_preservation prog htcs passes hGen hErrDiv).2
    exact sentinel_contradict hArm (.inr (.inl hPC))
  | errorBounds σ_opt =>
    exfalso
    obtain ⟨am_opt, hErrBounds⟩ := hbeh
    obtain ⟨s', hArm, hPC'⟩ :=
      (while_to_arm_bounds_preservation prog htcs passes hGen hErrBounds).2
    exact sentinel_contradict hArm (.inr (.inr hPC'))
  | typeErrors σ_opt =>
    exfalso
    obtain ⟨am', hte⟩ := hbeh
    exact absurd hte (pipelined_no_typeError prog htcs passes σ_opt am')
  | diverges =>
    obtain ⟨f, hinf, hf0⟩ := hbeh
    -- Source interp is none at all fuels (existing chain).
    have hinterp_none : ∀ fuel, prog.interp fuel = none :=
      while_to_arm_divergence_preservation prog htcs passes hinf hf0
    -- Source is safe at all fuels (new chain via compileToTAC infinite trace).
    obtain ⟨g, hg, hg0⟩ :=
      applyPasses_preserves_diverge prog.tyCtx passes _ hts hinf hf0
    have hsafe_all : ∀ fuel, prog.body.safe fuel prog.initStore ArrayMem.init prog.arrayDecls :=
      source_safe_of_compileToTAC_diverges prog htcs hg (hInitEq ▸ hg0)
    intro fuel
    exact (Program.run_outOfFuel_iff prog fuel).mpr ⟨hsafe_all fuel, hinterp_none fuel⟩

-- ============================================================
-- § 7e. Connecting the driver to backward refinement
-- ============================================================

/-- **Driver-to-theorem bridge: ARM halt implies source halt.**

    Backward dual of `compileProgramAst_correctness`.  If the driver returned
    `.ok r` and the ARM trace ends at `haltFinal`, then the source program
    halts safely with observables matching the ARM state. -/
theorem compileProgramAst_arm_halts_implies_program_halts
    {prog : Program} {noOpt : Bool} {r : VerifiedAsmResult}
    (hDriver : compileProgramAst prog noOpt = .ok r)
    {s : ArmState}
    (hArm : ArmSteps r.bodyFlat (r.initArmState) s)
    (hPC : s.pc = r.haltFinal) :
    ∃ fuel σ_src am_src,
      prog.run fuel = .halts σ_src am_src ∧
      ArmStateMatchesProgramState s r.layout prog.compileToTAC.observable σ_src am_src := by
  unfold compileProgramAst at hDriver
  split at hDriver
  · rename_i hwf
    cases noOpt with
    | true =>
      simp at hDriver
      exact arm_halts_implies_program_halts prog hwf
        ([] : List (String × (Prog → ECertificate))) hDriver hArm hPC
    | false =>
      simp at hDriver
      obtain ⟨allPasses, heq⟩ :=
        applyStandardPipelineFixpoint_eq_applyPasses prog.tyCtx prog.compileToTAC
      rw [heq] at hDriver
      exact arm_halts_implies_program_halts prog hwf allPasses hDriver hArm hPC
  · simp at hDriver

/-- **Driver-to-theorem bridge: ARM div-by-zero sentinel implies source unsafe (division).** -/
theorem compileProgramAst_arm_div_implies_program_unsafe_div
    {prog : Program} {noOpt : Bool} {r : VerifiedAsmResult}
    (hDriver : compileProgramAst prog noOpt = .ok r)
    {s : ArmState}
    (hArm : ArmSteps r.bodyFlat (r.initArmState) s)
    (hPC : s.pc = r.divS) :
    ∃ fuel, prog.run fuel = .divByZero := by
  unfold compileProgramAst at hDriver
  split at hDriver
  · rename_i hwf
    cases noOpt with
    | true =>
      simp at hDriver
      exact arm_div_implies_program_unsafe_div prog hwf
        ([] : List (String × (Prog → ECertificate))) hDriver hArm hPC
    | false =>
      simp at hDriver
      obtain ⟨allPasses, heq⟩ :=
        applyStandardPipelineFixpoint_eq_applyPasses prog.tyCtx prog.compileToTAC
      rw [heq] at hDriver
      exact arm_div_implies_program_unsafe_div prog hwf allPasses hDriver hArm hPC
  · simp at hDriver

/-- **Driver-to-theorem bridge: ARM bounds sentinel implies source unsafe (bounds).** -/
theorem compileProgramAst_arm_bounds_implies_program_unsafe_bounds
    {prog : Program} {noOpt : Bool} {r : VerifiedAsmResult}
    (hDriver : compileProgramAst prog noOpt = .ok r)
    {s : ArmState}
    (hArm : ArmSteps r.bodyFlat (r.initArmState) s)
    (hPC : s.pc = r.boundsS) :
    ∃ fuel, prog.run fuel = .outOfBounds := by
  unfold compileProgramAst at hDriver
  split at hDriver
  · rename_i hwf
    cases noOpt with
    | true =>
      simp at hDriver
      exact arm_bounds_implies_program_unsafe_bounds prog hwf
        ([] : List (String × (Prog → ECertificate))) hDriver hArm hPC
    | false =>
      simp at hDriver
      obtain ⟨allPasses, heq⟩ :=
        applyStandardPipelineFixpoint_eq_applyPasses prog.tyCtx prog.compileToTAC
      rw [heq] at hDriver
      exact arm_bounds_implies_program_unsafe_bounds prog hwf allPasses hDriver hArm hPC
  · simp at hDriver

/-- **Driver-to-theorem bridge: ARM divergence implies source divergence.** -/
theorem compileProgramAst_arm_diverges_implies_program_diverges
    {prog : Program} {noOpt : Bool} {r : VerifiedAsmResult}
    (hDriver : compileProgramAst prog noOpt = .ok r)
    (hDiv : ArmDiverges r.bodyFlat (r.initArmState)) :
    ∀ fuel, prog.run fuel = .outOfFuel := by
  unfold compileProgramAst at hDriver
  split at hDriver
  · rename_i hwf
    cases noOpt with
    | true =>
      simp at hDriver
      exact arm_diverges_implies_program_diverges prog hwf
        ([] : List (String × (Prog → ECertificate))) hDriver hDiv
    | false =>
      simp at hDriver
      obtain ⟨allPasses, heq⟩ :=
        applyStandardPipelineFixpoint_eq_applyPasses prog.tyCtx prog.compileToTAC
      rw [heq] at hDriver
      exact arm_diverges_implies_program_diverges prog hwf allPasses hDriver hDiv
  · simp at hDriver

end Phase7Skeleton

-- ============================================================
-- § 10. Phase 6 probes — validate branchTargetsBounded pattern
-- ============================================================

/-!
## Probes

Two per-`verifiedGenInstr`-case proofs that validate the pattern needed
for `bodyFlat_branch_target_bounded`.  Landing these on `main` before the
full 14-case sweep gives the next session a working blueprint to clone.

The probes don't require `GenAsmSpec` — they take the pcMap-bound and
sentinel-order hypotheses directly as arguments.  Full integration with
spec comes when `bodyFlat_branch_target_bounded` is assembled.
-/

section Phase6Probes

/-- **Probe 1 — `.goto`**.  The simplest branching case.  Output is
    `[ArmInstr.b (pcMap l)]`; target `pcMap l` is assumed `≤ boundsS`
    (eventually from `spec.pcMapLengths` + `spec.haltS_eq` +
    `spec.boundsS_eq`). -/
private theorem verifiedGenInstr_goto_branch_bounded
    (layout : VarLayout) (pcMap : Nat → Nat) (l : Nat)
    (haltS divS boundsS : Nat) (arrayDecls : List (ArrayName × Nat × VarTy))
    (safe : Bool) {instrs : List ArmInstr}
    (hGen : verifiedGenInstr layout pcMap (.goto l) haltS divS boundsS arrayDecls safe
      = some instrs)
    (hPcMapBound : pcMap l ≤ boundsS) :
    ∀ instr' ∈ instrs, ∀ lbl,
      (instr' = ArmInstr.b lbl ∨
       (∃ rn, instr' = ArmInstr.cbz rn lbl) ∨
       (∃ rn, instr' = ArmInstr.cbnz rn lbl) ∨
       (∃ c, instr' = ArmInstr.bCond c lbl)) →
      lbl ≤ boundsS := by
  -- Unfold: the `if !regConv || !inj then none else …` guard.
  simp only [verifiedGenInstr, Option.some.injEq] at hGen
  subst hGen
  intro instr' hmem lbl hbranch
  simp only [List.mem_singleton] at hmem
  subst hmem
  -- instr' = ArmInstr.b (pcMap l).
  rcases hbranch with h | ⟨rn, h⟩ | ⟨rn, h⟩ | ⟨c, h⟩
  · -- h : ArmInstr.b (pcMap l) = ArmInstr.b lbl
    cases h; exact hPcMapBound
  · exact ArmInstr.noConfusion h
  · exact ArmInstr.noConfusion h
  · exact ArmInstr.noConfusion h

/-- Helper for Probe 2: `vLoadVar` output contains no branch instructions. -/
private theorem vLoadVar_no_branches (layout : VarLayout) (v : Var) (tmp : ArmReg) :
    ∀ instr' ∈ vLoadVar layout v tmp,
      (∀ lbl, instr' ≠ ArmInstr.b lbl) ∧
      (∀ rn lbl, instr' ≠ ArmInstr.cbz rn lbl) ∧
      (∀ rn lbl, instr' ≠ ArmInstr.cbnz rn lbl) ∧
      (∀ c lbl, instr' ≠ ArmInstr.bCond c lbl) := by
  intro instr' hmem
  unfold vLoadVar at hmem
  rcases hl : layout v with _ | loc
  · rw [hl] at hmem; simp at hmem
  · rw [hl] at hmem
    cases loc with
    | stack _ =>
      simp at hmem; subst hmem
      refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> intro h <;> exact ArmInstr.noConfusion h
    | ireg r =>
      by_cases heq : r == tmp
      · simp [heq] at hmem
      · simp [heq] at hmem; subst hmem
        refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> intro h <;> exact ArmInstr.noConfusion h
    | freg _ => simp at hmem

/-- Helper for Probe 2: `vStoreVar` output contains no branch instructions. -/
private theorem vStoreVar_no_branches (layout : VarLayout) (v : Var) (tmp : ArmReg) :
    ∀ instr' ∈ vStoreVar layout v tmp,
      (∀ lbl, instr' ≠ ArmInstr.b lbl) ∧
      (∀ rn lbl, instr' ≠ ArmInstr.cbz rn lbl) ∧
      (∀ rn lbl, instr' ≠ ArmInstr.cbnz rn lbl) ∧
      (∀ c lbl, instr' ≠ ArmInstr.bCond c lbl) := by
  intro instr' hmem
  unfold vStoreVar at hmem
  rcases hl : layout v with _ | loc
  · rw [hl] at hmem; simp at hmem
  · rw [hl] at hmem
    cases loc with
    | stack _ =>
      simp at hmem; subst hmem
      refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> intro h <;> exact ArmInstr.noConfusion h
    | ireg r =>
      by_cases heq : r == tmp
      · simp [heq] at hmem
      · simp [heq] at hmem; subst hmem
        refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> intro h <;> exact ArmInstr.noConfusion h
    | freg _ => simp at hmem

/-- **Probe 2 — `.binop _ .div _ _`**.  Three-nest layout match + inner
    `op ∈ {.div, .mod}` branch.  The output, under the guard, is:

      `vLoadVar lv ++ vLoadVar rv ++ [.cbz rv_reg divLabel] ++ [.sdivR …] ++ vStoreVar dst`

    The only branch is the `.cbz`, targeting `divLabel = divS`.  Helpers
    `vLoadVar_no_branches` / `vStoreVar_no_branches` cover the non-branch
    sections; `.sdivR` is a singleton non-branch. -/
private theorem verifiedGenInstr_binop_div_branch_bounded
    (layout : VarLayout) (pcMap : Nat → Nat) (dst lv rv : Var)
    (haltS divS boundsS : Nat) (arrayDecls : List (ArrayName × Nat × VarTy))
    (safe : Bool) {instrs : List ArmInstr}
    (hGen : verifiedGenInstr layout pcMap (.binop dst .div lv rv)
      haltS divS boundsS arrayDecls safe = some instrs)
    (hRC : layout.regConventionSafe = true)
    (hII : layout.isInjective = true)
    (hDivBound : divS ≤ boundsS) :
    ∀ instr' ∈ instrs, ∀ lbl,
      (instr' = ArmInstr.b lbl ∨
       (∃ rn, instr' = ArmInstr.cbz rn lbl) ∨
       (∃ rn, instr' = ArmInstr.cbnz rn lbl) ∨
       (∃ c, instr' = ArmInstr.bCond c lbl)) →
      lbl ≤ boundsS := by
  -- Close cases uniformly by case-splitting on the branch-form disjunction
  -- against the specific `instr'` we know it to be.  The pattern factors
  -- into three reusable tactics: for a non-branch instruction, show all four
  -- disjuncts fail; for a cbz-with-divS, peel disjuncts to reach the cbz arm
  -- and return hDivBound; for an instruction drawn from vLoad/vStore, invoke
  -- the no-branches helper.
  simp [verifiedGenInstr, hRC, hII] at hGen
  -- The generated match is 3-way on `(layout lv, layout rv, layout dst)`
  -- with the `freg` arms emitting `none`.  Split-with-simp closes those.
  split at hGen <;> first | simp at hGen | skip
  all_goals (split at hGen <;> first | simp at hGen | skip)
  all_goals (split at hGen <;> first | simp at hGen | skip)
  -- At this point, in each all-non-freg branch, simp + split has left hGen
  -- as a raw list equation `<concrete list> = instrs`; `subst hGen` replaces
  -- `instrs` with the concrete list in the goal.
  all_goals (subst hGen)
  -- Prove the conclusion in each of the 8 surviving branches uniformly:
  -- the list is vLoadVar ++ vLoadVar ++ [.cbz _ divS] ++ [.sdivR _ _ _] ++ vStoreVar.
  all_goals (
    intro instr' hmem lbl hbranch
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with hLv | hRv | hCbz | hSdiv | hStore
    · have ⟨nb, nz, nnz, nbc⟩ := vLoadVar_no_branches layout lv _ instr' hLv
      rcases hbranch with h | ⟨rn, h⟩ | ⟨rn, h⟩ | ⟨c, h⟩
      · exact absurd h (nb _)
      · exact absurd h (nz rn _)
      · exact absurd h (nnz rn _)
      · exact absurd h (nbc c _)
    · have ⟨nb, nz, nnz, nbc⟩ := vLoadVar_no_branches layout rv _ instr' hRv
      rcases hbranch with h | ⟨rn, h⟩ | ⟨rn, h⟩ | ⟨c, h⟩
      · exact absurd h (nb _)
      · exact absurd h (nz rn _)
      · exact absurd h (nnz rn _)
      · exact absurd h (nbc c _)
    · -- .cbz _ divS
      subst hCbz
      rcases hbranch with h | ⟨rn, h⟩ | ⟨rn, h⟩ | ⟨c, h⟩
      · exact ArmInstr.noConfusion h
      · cases h; exact hDivBound
      · exact ArmInstr.noConfusion h
      · exact ArmInstr.noConfusion h
    · -- .sdivR _ _ _
      subst hSdiv
      rcases hbranch with h | ⟨rn, h⟩ | ⟨rn, h⟩ | ⟨c, h⟩
      all_goals exact ArmInstr.noConfusion h
    · have ⟨nb, nz, nnz, nbc⟩ := vStoreVar_no_branches layout dst _ instr' hStore
      rcases hbranch with h | ⟨rn, h⟩ | ⟨rn, h⟩ | ⟨c, h⟩
      · exact absurd h (nb _)
      · exact absurd h (nz rn _)
      · exact absurd h (nnz rn _)
      · exact absurd h (nbc c _))

end Phase6Probes

-- ============================================================
-- § 10b. Phase 6 derisk probes (session 2)
-- ============================================================

section Phase6Probes2

/-- The next PC after an ARM step, as a pure function of the state and
    instruction at `s.pc`.  Used to sidestep the 50×50 `cases`-of-`ArmStep`
    explosion in `arm_step_pc_det`: we project `ArmStep` down to this
    function, pair the two projections under the shared instruction, and
    get determinism for free. -/
private def armNextPC (s : ArmState) (i : ArmInstr) : Nat :=
  match i with
  | .b lbl => lbl
  | .cbz rn lbl => if s.regs rn = (0 : BitVec 64) then lbl else s.pc + 1
  | .cbnz rn lbl => if s.regs rn = (0 : BitVec 64) then s.pc + 1 else lbl
  | .bCond c lbl => if s.flags.condHolds c = true then lbl else s.pc + 1
  | _ => s.pc + 1

/-- **ArmStep PC projection.**  Every `ArmStep` fires with a specific
    instruction at `s.pc`, and the successor's PC is determined by
    `armNextPC` applied to `s` and that instruction.  Havoc rules
    (`printCall`, `callPrintI/B/F/S`, `callBinF`, `floatUnaryLibCall`)
    modify `regs`/`fregs` but not `pc`. -/
private theorem ArmStep.pc_eq_armNextPC {prog : ArmProg} {s s' : ArmState}
    (h : ArmStep prog s s') :
    ∃ i, prog[s.pc]? = some i ∧ s'.pc = armNextPC s i := by
  cases h with
  | mov rd imm hi => exact ⟨_, hi, rfl⟩
  | movR rd rn hi => exact ⟨_, hi, rfl⟩
  | movz rd imm sh hi => exact ⟨_, hi, rfl⟩
  | movk rd imm sh hi => exact ⟨_, hi, rfl⟩
  | ldr rd off hi => exact ⟨_, hi, rfl⟩
  | str rs off hi => exact ⟨_, hi, rfl⟩
  | addR _ _ _ hi => exact ⟨_, hi, rfl⟩
  | subR _ _ _ hi => exact ⟨_, hi, rfl⟩
  | mulR _ _ _ hi => exact ⟨_, hi, rfl⟩
  | sdivR _ _ _ hi => exact ⟨_, hi, rfl⟩
  | cmpRR _ _ hi => exact ⟨_, hi, rfl⟩
  | cmpRI _ _ hi => exact ⟨_, hi, rfl⟩
  | cset _ _ hi => exact ⟨_, hi, rfl⟩
  | cbz_taken rn lbl hi hz =>
    exact ⟨_, hi, by simp only [armNextPC, if_pos hz]⟩
  | cbz_fall rn lbl hi hnz =>
    exact ⟨_, hi, by simp only [armNextPC, if_neg hnz, ArmState.nextPC]⟩
  | cbnz_taken rn lbl hi hnz =>
    exact ⟨_, hi, by simp only [armNextPC, if_neg hnz]⟩
  | cbnz_fall rn lbl hi hz =>
    exact ⟨_, hi, by simp only [armNextPC, if_pos hz, ArmState.nextPC]⟩
  | bCond_taken c lbl hi hc =>
    exact ⟨_, hi, by simp only [armNextPC, if_pos hc]⟩
  | bCond_fall c lbl hi hc =>
    exact ⟨_, hi, by simp only [armNextPC, hc, ArmState.nextPC, if_false, Bool.false_eq_true]⟩
  | andImm _ _ _ hi => exact ⟨_, hi, rfl⟩
  | andR _ _ _ hi => exact ⟨_, hi, rfl⟩
  | eorImm _ _ _ hi => exact ⟨_, hi, rfl⟩
  | orrR _ _ _ hi => exact ⟨_, hi, rfl⟩
  | eorR _ _ _ hi => exact ⟨_, hi, rfl⟩
  | lslR _ _ _ hi => exact ⟨_, hi, rfl⟩
  | asrR _ _ _ hi => exact ⟨_, hi, rfl⟩
  | branch _ hi => exact ⟨_, hi, rfl⟩
  | printCall _ hi => exact ⟨_, hi, rfl⟩
  | callPrintI hi => exact ⟨_, hi, rfl⟩
  | callPrintB hi => exact ⟨_, hi, rfl⟩
  | callPrintF hi => exact ⟨_, hi, rfl⟩
  | callPrintS _ hi => exact ⟨_, hi, rfl⟩
  | arrLd _ _ _ hi => exact ⟨_, hi, rfl⟩
  | arrSt _ _ _ hi => exact ⟨_, hi, rfl⟩
  | fmovToFP _ _ hi => exact ⟨_, hi, rfl⟩
  | fmovRR _ _ hi => exact ⟨_, hi, rfl⟩
  | fldr _ _ hi => exact ⟨_, hi, rfl⟩
  | fstr _ _ hi => exact ⟨_, hi, rfl⟩
  | faddR _ _ _ hi => exact ⟨_, hi, rfl⟩
  | fsubR _ _ _ hi => exact ⟨_, hi, rfl⟩
  | fmulR _ _ _ hi => exact ⟨_, hi, rfl⟩
  | fdivR _ _ _ hi => exact ⟨_, hi, rfl⟩
  | fmaddR _ _ _ _ hi => exact ⟨_, hi, rfl⟩
  | fmsubR _ _ _ _ hi => exact ⟨_, hi, rfl⟩
  | fminR _ _ _ hi => exact ⟨_, hi, rfl⟩
  | fmaxR _ _ _ hi => exact ⟨_, hi, rfl⟩
  | callBinF _ _ _ _ hi => exact ⟨_, hi, rfl⟩
  | fcmpRR _ _ hi => exact ⟨_, hi, rfl⟩
  | scvtf _ _ hi => exact ⟨_, hi, rfl⟩
  | fcvtzs _ _ hi => exact ⟨_, hi, rfl⟩
  | farrLd _ _ _ hi => exact ⟨_, hi, rfl⟩
  | farrSt _ _ _ hi => exact ⟨_, hi, rfl⟩
  | floatUnaryNative _ _ _ hi _ => exact ⟨_, hi, rfl⟩
  | floatUnaryLibCall _ _ _ hi _ => exact ⟨_, hi, rfl⟩

/-- **Probe P2 — ARM step PC determinism.**  Two `ArmStep`s from the same
    initial state produce the same PC.  Follows from `ArmStep.pc_eq_armNextPC`
    applied to both and matching the instruction via `Option.some.inj`. -/
private theorem arm_step_pc_det {prog : ArmProg} {s s₁ s₂ : ArmState}
    (h1 : ArmStep prog s s₁) (h2 : ArmStep prog s s₂) :
    s₁.pc = s₂.pc := by
  obtain ⟨i1, hi1, hpc1⟩ := ArmStep.pc_eq_armNextPC h1
  obtain ⟨i2, hi2, hpc2⟩ := ArmStep.pc_eq_armNextPC h2
  have : i1 = i2 := Option.some.inj (hi1 ▸ hi2)
  rw [hpc1, hpc2, this]

/-- Helper: `formalLoadImm64` emits only non-branch instructions. -/
private theorem formalLoadImm64_no_branches (rd : ArmReg) (n : BitVec 64) :
    ∀ instr' ∈ formalLoadImm64 rd n,
      (∀ lbl, instr' ≠ ArmInstr.b lbl) ∧
      (∀ rn lbl, instr' ≠ ArmInstr.cbz rn lbl) ∧
      (∀ rn lbl, instr' ≠ ArmInstr.cbnz rn lbl) ∧
      (∀ c lbl, instr' ≠ ArmInstr.bCond c lbl) := by
  intro instr' hmem
  unfold formalLoadImm64 at hmem
  split at hmem
  · -- small case: [.mov rd n]
    simp at hmem; subst hmem
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> intro h <;> exact ArmInstr.noConfusion h
  · -- large case: base ++ k1 ++ k2 ++ k3 where all are movz/movk
    simp only [List.mem_append, List.mem_singleton] at hmem
    rcases hmem with ((hBase | hK1) | hK2) | hK3
    · subst hBase
      refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> intro heq <;> exact ArmInstr.noConfusion heq
    · split at hK1
      · simp at hK1; subst hK1
        refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> intro heq <;> exact ArmInstr.noConfusion heq
      · simp at hK1
    · split at hK2
      · simp at hK2; subst hK2
        refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> intro heq <;> exact ArmInstr.noConfusion heq
      · simp at hK2
    · split at hK3
      · simp at hK3; subst hK3
        refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> intro heq <;> exact ArmInstr.noConfusion heq
      · simp at hK3

/-- Helper: `vStoreVarFP` emits only non-branch instructions. -/
private theorem vStoreVarFP_no_branches (layout : VarLayout) (v : Var) (tmp : ArmFReg) :
    ∀ instr' ∈ vStoreVarFP layout v tmp,
      (∀ lbl, instr' ≠ ArmInstr.b lbl) ∧
      (∀ rn lbl, instr' ≠ ArmInstr.cbz rn lbl) ∧
      (∀ rn lbl, instr' ≠ ArmInstr.cbnz rn lbl) ∧
      (∀ c lbl, instr' ≠ ArmInstr.bCond c lbl) := by
  intro instr' hmem
  unfold vStoreVarFP at hmem
  rcases hl : layout v with _ | loc
  · rw [hl] at hmem; simp at hmem
  · rw [hl] at hmem
    cases loc with
    | stack _ =>
      simp at hmem; subst hmem
      refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> intro h <;> exact ArmInstr.noConfusion h
    | ireg _ => simp at hmem
    | freg r =>
      by_cases heq : r == tmp
      · simp [heq] at hmem
      · simp [heq] at hmem; subst hmem
        refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> intro h <;> exact ArmInstr.noConfusion h

/-- Helper: `vLoadVarFP` emits only non-branch instructions. -/
private theorem vLoadVarFP_no_branches (layout : VarLayout) (v : Var) (tmp : ArmFReg) :
    ∀ instr' ∈ vLoadVarFP layout v tmp,
      (∀ lbl, instr' ≠ ArmInstr.b lbl) ∧
      (∀ rn lbl, instr' ≠ ArmInstr.cbz rn lbl) ∧
      (∀ rn lbl, instr' ≠ ArmInstr.cbnz rn lbl) ∧
      (∀ c lbl, instr' ≠ ArmInstr.bCond c lbl) := by
  intro instr' hmem
  unfold vLoadVarFP at hmem
  rcases hl : layout v with _ | loc
  · rw [hl] at hmem; simp at hmem
  · rw [hl] at hmem
    cases loc with
    | stack _ =>
      simp at hmem; subst hmem
      refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> intro h <;> exact ArmInstr.noConfusion h
    | ireg _ => simp at hmem
    | freg r =>
      by_cases heq : r == tmp
      · simp [heq] at hmem
      · simp [heq] at hmem; subst hmem
        refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> intro h <;> exact ArmInstr.noConfusion h

/-- Helper: `verifiedGenBoolExpr` emits only non-branch instructions.
    By induction on `be`; each constructor dispatches to
    `vLoadVar`/`vLoadVarFP`/`formalLoadImm64` plus fixed non-branch
    instructions (`.mov`, `.andImm`, `.cmp`, `.cset`, `.fcmpR`, `.fmovToFP`,
    `.eorImm`). -/
private theorem verifiedGenBoolExpr_no_branches (layout : VarLayout) (be : BoolExpr) :
    ∀ instr' ∈ verifiedGenBoolExpr layout be,
      (∀ lbl, instr' ≠ ArmInstr.b lbl) ∧
      (∀ rn lbl, instr' ≠ ArmInstr.cbz rn lbl) ∧
      (∀ rn lbl, instr' ≠ ArmInstr.cbnz rn lbl) ∧
      (∀ c lbl, instr' ≠ ArmInstr.bCond c lbl) := by
  intro instr' hmem
  induction be generalizing instr' with
  | lit b =>
    unfold verifiedGenBoolExpr at hmem
    simp at hmem; subst hmem
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> intro h <;> exact ArmInstr.noConfusion h
  | bvar v =>
    unfold verifiedGenBoolExpr at hmem
    simp only [List.mem_append, List.mem_singleton] at hmem
    rcases hmem with h | h
    · exact vLoadVar_no_branches layout v .x0 _ h
    · subst h
      refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> intro heq <;> exact ArmInstr.noConfusion heq
  | cmp op a b =>
    unfold verifiedGenBoolExpr at hmem
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hmem
    -- instr' ∈ loadA ∨ loadB ∨ .cmp ∨ .cset
    have loadA_nb : ∀ i ∈ (match a with
        | .var v => vLoadVar layout v .x1 | .lit n => formalLoadImm64 .x1 n | _ => []),
        (∀ lbl, i ≠ ArmInstr.b lbl) ∧ (∀ rn lbl, i ≠ ArmInstr.cbz rn lbl) ∧
        (∀ rn lbl, i ≠ ArmInstr.cbnz rn lbl) ∧ (∀ c lbl, i ≠ ArmInstr.bCond c lbl) := by
      intro i hi
      split at hi
      · exact vLoadVar_no_branches layout _ .x1 _ hi
      · exact formalLoadImm64_no_branches .x1 _ _ hi
      · simp at hi
    have loadB_nb : ∀ i ∈ (match b with
        | .var v => vLoadVar layout v .x2 | .lit n => formalLoadImm64 .x2 n | _ => []),
        (∀ lbl, i ≠ ArmInstr.b lbl) ∧ (∀ rn lbl, i ≠ ArmInstr.cbz rn lbl) ∧
        (∀ rn lbl, i ≠ ArmInstr.cbnz rn lbl) ∧ (∀ c lbl, i ≠ ArmInstr.bCond c lbl) := by
      intro i hi
      split at hi
      · exact vLoadVar_no_branches layout _ .x2 _ hi
      · exact formalLoadImm64_no_branches .x2 _ _ hi
      · simp at hi
    rcases hmem with (hA | hB) | hCmp | hCset
    · exact loadA_nb _ hA
    · exact loadB_nb _ hB
    · subst hCmp
      refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> intro heq <;> exact ArmInstr.noConfusion heq
    · subst hCset
      refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> intro heq <;> exact ArmInstr.noConfusion heq
  | not e ih =>
    unfold verifiedGenBoolExpr at hmem
    simp only [List.mem_append, List.mem_singleton] at hmem
    rcases hmem with h | h
    · exact ih _ h
    · subst h
      refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> intro heq <;> exact ArmInstr.noConfusion heq
  | fcmp fop a b =>
    unfold verifiedGenBoolExpr at hmem
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hmem
    have loadA_nb : ∀ i ∈ (match a with
        | .var v => vLoadVarFP layout v .d1
        | .flit n => formalLoadImm64 .x0 n ++ [ArmInstr.fmovToFP .d1 .x0]
        | _ => []),
        (∀ lbl, i ≠ ArmInstr.b lbl) ∧ (∀ rn lbl, i ≠ ArmInstr.cbz rn lbl) ∧
        (∀ rn lbl, i ≠ ArmInstr.cbnz rn lbl) ∧ (∀ c lbl, i ≠ ArmInstr.bCond c lbl) := by
      intro i hi
      split at hi
      · exact vLoadVarFP_no_branches layout _ .d1 _ hi
      · simp only [List.mem_append, List.mem_singleton] at hi
        rcases hi with hLd | hFmov
        · exact formalLoadImm64_no_branches .x0 _ _ hLd
        · subst hFmov
          refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> intro heq <;> exact ArmInstr.noConfusion heq
      · simp at hi
    have loadB_nb : ∀ i ∈ (match b with
        | .var v => vLoadVarFP layout v .d2
        | .flit n => formalLoadImm64 .x0 n ++ [ArmInstr.fmovToFP .d2 .x0]
        | _ => []),
        (∀ lbl, i ≠ ArmInstr.b lbl) ∧ (∀ rn lbl, i ≠ ArmInstr.cbz rn lbl) ∧
        (∀ rn lbl, i ≠ ArmInstr.cbnz rn lbl) ∧ (∀ c lbl, i ≠ ArmInstr.bCond c lbl) := by
      intro i hi
      split at hi
      · exact vLoadVarFP_no_branches layout _ .d2 _ hi
      · simp only [List.mem_append, List.mem_singleton] at hi
        rcases hi with hLd | hFmov
        · exact formalLoadImm64_no_branches .x0 _ _ hLd
        · subst hFmov
          refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> intro heq <;> exact ArmInstr.noConfusion heq
      · simp at hi
    rcases hmem with (hA | hB) | hCmp | hCset
    · exact loadA_nb _ hA
    · exact loadB_nb _ hB
    · subst hCmp
      refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> intro heq <;> exact ArmInstr.noConfusion heq
    · subst hCset
      refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> intro heq <;> exact ArmInstr.noConfusion heq
  | bexpr e =>
    unfold verifiedGenBoolExpr at hmem
    split at hmem
    · rename_i v
      simp only [List.mem_append, List.mem_singleton] at hmem
      rcases hmem with h | h
      · exact vLoadVar_no_branches layout v .x0 _ h
      · subst h
        refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> intro heq <;> exact ArmInstr.noConfusion heq
    · simp at hmem

-- Helper: an instruction in a `match a with | .var v => vLoadVar ... | .lit n => formalLoadImm64 ... | _ => []`
-- output has no branch form. Used by the `.not (.cmp)` arm of verifiedGenInstr_ifgoto_branch_bounded.
private theorem match_var_lit_loadVar_no_branches
    (layout : VarLayout) (e : Expr) (tmp : ArmReg) {i : ArmInstr}
    (hi : i ∈ (match e with
              | .var v => vLoadVar layout v tmp
              | .lit n => formalLoadImm64 tmp n
              | _ => ([] : List ArmInstr))) :
    (∀ lbl, i ≠ ArmInstr.b lbl) ∧
    (∀ rn lbl, i ≠ ArmInstr.cbz rn lbl) ∧
    (∀ rn lbl, i ≠ ArmInstr.cbnz rn lbl) ∧
    (∀ c lbl, i ≠ ArmInstr.bCond c lbl) := by
  split at hi
  · exact vLoadVar_no_branches _ _ _ _ hi
  · exact formalLoadImm64_no_branches _ _ _ hi
  · simp at hi

-- Helper: float-load variant for the `.not (.fcmp)` arm — `.var` → vLoadVarFP,
-- `.flit` → formalLoadImm64 + fmovToFP, else [].
private theorem match_var_flit_loadFP_no_branches
    (layout : VarLayout) (e : Expr) (fr : ArmFReg) {i : ArmInstr}
    (hi : i ∈ (match e with
              | .var v => vLoadVarFP layout v fr
              | .flit n => formalLoadImm64 .x0 n ++ [ArmInstr.fmovToFP fr .x0]
              | _ => ([] : List ArmInstr))) :
    (∀ lbl, i ≠ ArmInstr.b lbl) ∧
    (∀ rn lbl, i ≠ ArmInstr.cbz rn lbl) ∧
    (∀ rn lbl, i ≠ ArmInstr.cbnz rn lbl) ∧
    (∀ c lbl, i ≠ ArmInstr.bCond c lbl) := by
  split at hi
  · exact vLoadVarFP_no_branches _ _ _ _ hi
  · simp only [List.mem_append, List.mem_singleton] at hi
    rcases hi with hLd | hFmov
    · exact formalLoadImm64_no_branches _ _ _ hLd
    · subst hFmov
      refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> intro heq <;> exact ArmInstr.noConfusion heq
  · simp at hi

private theorem verifiedGenInstr_ifgoto_branch_bounded
    (layout : VarLayout) (pcMap : Nat → Nat) (be : BoolExpr) (l : Nat)
    (haltS divS boundsS : Nat) (arrayDecls : List (ArrayName × Nat × VarTy))
    (safe : Bool) {instrs : List ArmInstr}
    (hGen : verifiedGenInstr layout pcMap (.ifgoto be l)
      haltS divS boundsS arrayDecls safe = some instrs)
    (hPcMapBound : pcMap l ≤ boundsS) :
    ∀ instr' ∈ instrs, ∀ lbl,
      (instr' = ArmInstr.b lbl ∨
       (∃ rn, instr' = ArmInstr.cbz rn lbl) ∨
       (∃ rn, instr' = ArmInstr.cbnz rn lbl) ∨
       (∃ c, instr' = ArmInstr.bCond c lbl)) →
      lbl ≤ boundsS := by
  simp only [verifiedGenInstr] at hGen
  split at hGen
  · exact absurd hGen (by intro h; cases h)
  · intro instr' hmem lbl hbranch
    split at hGen
    · -- .not (.cmp op a b) arm. Use fresh names to avoid conflicts with Expr `a`/`b`.
      rename_i e1 e2 cOp
      simp only [Option.some.injEq] at hGen
      subst hGen
      -- After subst, verify what e1/e2/cOp are. `cOp` should be CmpOp, e1/e2 Expr.
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with (hA | hB) | hCmp | hBCond
      · -- hA is about (match e1 with | .var => vLoadVar ... | .lit => formalLoadImm64 ... | _ => [])
        have ⟨nb, nz, nnz, nbc⟩ := match_var_lit_loadVar_no_branches layout e1 _ hA
        rcases hbranch with h | ⟨rn, h⟩ | ⟨rn, h⟩ | ⟨c, h⟩
        · exact absurd h (nb _)
        · exact absurd h (nz rn _)
        · exact absurd h (nnz rn _)
        · exact absurd h (nbc c _)
      · have ⟨nb, nz, nnz, nbc⟩ := match_var_lit_loadVar_no_branches layout e2 _ hB
        rcases hbranch with h | ⟨rn, h⟩ | ⟨rn, h⟩ | ⟨c, h⟩
        · exact absurd h (nb _)
        · exact absurd h (nz rn _)
        · exact absurd h (nnz rn _)
        · exact absurd h (nbc c _)
      · subst hCmp
        rcases hbranch with h | ⟨rn, h⟩ | ⟨rn, h⟩ | ⟨c, h⟩
        all_goals exact ArmInstr.noConfusion h
      · subst hBCond
        rcases hbranch with h | ⟨rn, h⟩ | ⟨rn, h⟩ | ⟨c, h⟩
        · exact ArmInstr.noConfusion h
        · exact ArmInstr.noConfusion h
        · exact ArmInstr.noConfusion h
        · cases h; exact hPcMapBound
    · -- .not (.fcmp fop a b) arm. Same rename convention as .cmp: oldest-first.
      rename_i e1 e2 fOp
      simp only [Option.some.injEq] at hGen
      subst hGen
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with hLoads | hFcmp | hBCond
      · -- instr' ∈ loads. Direct analysis: loadFP helper handles `.var` cleanly;
        -- `.flit` gets distributed by simp — inline analysis in each sub-case.
        -- Common continuation: given `(nb, nz, nnz, nbc)` for instr', close via hbranch.
        suffices hnb :
            (∀ lbl, instr' ≠ ArmInstr.b lbl) ∧
            (∀ rn lbl, instr' ≠ ArmInstr.cbz rn lbl) ∧
            (∀ rn lbl, instr' ≠ ArmInstr.cbnz rn lbl) ∧
            (∀ c lbl, instr' ≠ ArmInstr.bCond c lbl) by
          obtain ⟨nb, nz, nnz, nbc⟩ := hnb
          rcases hbranch with h | ⟨rn, h⟩ | ⟨rn, h⟩ | ⟨c, h⟩
          · exact absurd h (nb _)
          · exact absurd h (nz rn _)
          · exact absurd h (nnz rn _)
          · exact absurd h (nbc c _)
        -- Now prove the no-branches conjunction for instr' in loads.
        -- loads is either (match a,b) with swaps; analyze via cases on e1, e2.
        cases e1 with
        | var va =>
          cases e2 with
          | var vb =>
            -- loads = vLoadVarFP va ++ vLoadVarFP vb
            simp only [List.mem_append] at hLoads
            rcases hLoads with hA | hB
            · exact vLoadVarFP_no_branches _ _ _ _ hA
            · exact vLoadVarFP_no_branches _ _ _ _ hB
          | flit nb =>
            -- loads = vLoadVarFP va ++ (formalLoadImm64 .x0 nb ++ [fmovToFP ..])
            simp only [List.mem_append, List.mem_singleton] at hLoads
            rcases hLoads with hA | hImm | hFmov
            · exact vLoadVarFP_no_branches _ _ _ _ hA
            · exact formalLoadImm64_no_branches _ _ _ hImm
            · subst hFmov
              refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> intro heq <;>
                exact ArmInstr.noConfusion heq
          | _ =>
            -- loads = vLoadVarFP va ++ []
            simp only [List.mem_append, List.not_mem_nil, or_false] at hLoads
            exact vLoadVarFP_no_branches _ _ _ _ hLoads
        | flit na =>
          cases e2 with
          | var vb =>
            -- (e1, e2) = (.flit na, .var vb) swap — loads = loadB ++ loadA
            -- = vLoadVarFP vb ++ (formalLoadImm64 .x0 na ++ [fmovToFP ..])
            simp only [List.mem_append, List.mem_singleton] at hLoads
            rcases hLoads with hB | hImm | hFmov
            · exact vLoadVarFP_no_branches _ _ _ _ hB
            · exact formalLoadImm64_no_branches _ _ _ hImm
            · subst hFmov
              refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> intro heq <;>
                exact ArmInstr.noConfusion heq
          | flit nb =>
            -- loads = loadA ++ loadB = (formalLoadImm64 .x0 na ++ [fmov]) ++ (formalLoadImm64 .x0 nb ++ [fmov])
            simp only [List.mem_append, List.mem_singleton] at hLoads
            rcases hLoads with (hImmA | hFmovA) | (hImmB | hFmovB)
            · exact formalLoadImm64_no_branches _ _ _ hImmA
            · subst hFmovA
              refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> intro heq <;>
                exact ArmInstr.noConfusion heq
            · exact formalLoadImm64_no_branches _ _ _ hImmB
            · subst hFmovB
              refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> intro heq <;>
                exact ArmInstr.noConfusion heq
          | _ =>
            -- loads = (formalLoadImm64 .x0 na ++ [fmov]) ++ []
            simp only [List.mem_append, List.mem_singleton, List.not_mem_nil, or_false]
              at hLoads
            rcases hLoads with hImm | hFmov
            · exact formalLoadImm64_no_branches _ _ _ hImm
            · subst hFmov
              refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> intro heq <;>
                exact ArmInstr.noConfusion heq
        | _ =>
          -- e1 is neither .var nor .flit. loadA = []. loads = [] ++ loadB = loadB.
          simp only [List.mem_append, List.not_mem_nil, false_or] at hLoads
          exact match_var_flit_loadFP_no_branches layout e2 _ hLoads
      · subst hFcmp
        rcases hbranch with h | ⟨rn, h⟩ | ⟨rn, h⟩ | ⟨c, h⟩
        all_goals exact ArmInstr.noConfusion h
      · subst hBCond
        rcases hbranch with h | ⟨rn, h⟩ | ⟨rn, h⟩ | ⟨c, h⟩
        · exact ArmInstr.noConfusion h
        · exact ArmInstr.noConfusion h
        · exact ArmInstr.noConfusion h
        · cases h; exact hPcMapBound
    · -- fallback: verifiedGenBoolExpr be ++ [.cbnz .x0 (pcMap l)]
      simp only [Option.some.injEq] at hGen
      subst hGen
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with hBE | hCbnz
      · have ⟨nb, nz, nnz, nbc⟩ := verifiedGenBoolExpr_no_branches _ _ _ hBE
        rcases hbranch with h | ⟨rn, h⟩ | ⟨rn, h⟩ | ⟨c, h⟩
        · exact absurd h (nb _)
        · exact absurd h (nz rn _)
        · exact absurd h (nnz rn _)
        · exact absurd h (nbc c _)
      · subst hCbnz
        rcases hbranch with h | ⟨rn, h⟩ | ⟨rn, h⟩ | ⟨c, h⟩
        · exact ArmInstr.noConfusion h
        · exact ArmInstr.noConfusion h
        · cases h; exact hPcMapBound
        · exact ArmInstr.noConfusion h
/-
-- Attempted proof below — kept commented for reference.  The structural
-- issue is that Lean's elaborator generates `False.var` when reconstructing
-- the nested match pattern inside `have loadA_nb`'s type signature.  The
-- fallback arm (verifiedGenBoolExpr + [.cbnz]) compiles cleanly; the two
-- `.not` arms need restructuring.
  -- Unfold outer guard
  simp only [verifiedGenInstr] at hGen
  split at hGen
  · exact absurd hGen (by intro h; cases h)
  · -- guard passed; now the `if !be.hasSimpleOps` guard
    split at hGen
    · exact absurd hGen (by intro h; cases h)
    · -- be.hasSimpleOps = true; match on be
      -- Three-arm match: .not (.cmp), .not (.fcmp), fallback
      -- Generic closer: given instrs = <loads> ++ [cmp/fcmp non-branch, branch (pcMap l)]
      -- show all branch-form disjuncts in instrs give lbl ≤ boundsS.
      intro instr' hmem lbl hbranch
      split at hGen
      · -- .not (.cmp op a b) arm
        rename_i op a b
        simp only [Option.some.injEq] at hGen
        subst hGen
        -- instrs = loadA ++ loadB ++ [.cmp a_reg b_reg, .bCond cond.negate (pcMap l)]
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hmem
        -- Helper for loadA
        have loadA_nb : ∀ i ∈ (match a with
            | .var v => vLoadVar layout v (match a with | .var v => (match layout v with | some (.ireg r) => r | _ => .x1) | _ => .x1)
            | .lit n => formalLoadImm64 (match a with | .var v => (match layout v with | some (.ireg r) => r | _ => .x1) | _ => .x1) n
            | _ => []),
            (∀ lbl, i ≠ ArmInstr.b lbl) ∧ (∀ rn lbl, i ≠ ArmInstr.cbz rn lbl) ∧
            (∀ rn lbl, i ≠ ArmInstr.cbnz rn lbl) ∧ (∀ c lbl, i ≠ ArmInstr.bCond c lbl) := by
          intro i hi
          split at hi
          · exact vLoadVar_no_branches _ _ _ _ hi
          · exact formalLoadImm64_no_branches _ _ _ hi
          · simp at hi
        have loadB_nb : ∀ i ∈ (match b with
            | .var v => vLoadVar layout v (match b with | .var v => (match layout v with | some (.ireg r) => r | _ => .x2) | _ => .x2)
            | .lit n => formalLoadImm64 (match b with | .var v => (match layout v with | some (.ireg r) => r | _ => .x2) | _ => .x2) n
            | _ => []),
            (∀ lbl, i ≠ ArmInstr.b lbl) ∧ (∀ rn lbl, i ≠ ArmInstr.cbz rn lbl) ∧
            (∀ rn lbl, i ≠ ArmInstr.cbnz rn lbl) ∧ (∀ c lbl, i ≠ ArmInstr.bCond c lbl) := by
          intro i hi
          split at hi
          · exact vLoadVar_no_branches _ _ _ _ hi
          · exact formalLoadImm64_no_branches _ _ _ hi
          · simp at hi
        rcases hmem with (hA | hB) | hCmp | hBCond
        · have ⟨nb, nz, nnz, nbc⟩ := loadA_nb _ hA
          rcases hbranch with h | ⟨rn, h⟩ | ⟨rn, h⟩ | ⟨c, h⟩
          · exact absurd h (nb _)
          · exact absurd h (nz rn _)
          · exact absurd h (nnz rn _)
          · exact absurd h (nbc c _)
        · have ⟨nb, nz, nnz, nbc⟩ := loadB_nb _ hB
          rcases hbranch with h | ⟨rn, h⟩ | ⟨rn, h⟩ | ⟨c, h⟩
          · exact absurd h (nb _)
          · exact absurd h (nz rn _)
          · exact absurd h (nnz rn _)
          · exact absurd h (nbc c _)
        · subst hCmp
          rcases hbranch with h | ⟨rn, h⟩ | ⟨rn, h⟩ | ⟨c, h⟩
          all_goals exact ArmInstr.noConfusion h
        · subst hBCond
          rcases hbranch with h | ⟨rn, h⟩ | ⟨rn, h⟩ | ⟨c, h⟩
          · exact ArmInstr.noConfusion h
          · exact ArmInstr.noConfusion h
          · exact ArmInstr.noConfusion h
          · cases h; exact hPcMapBound
      · -- .not (.fcmp fop a b) arm
        rename_i fop a b
        simp only [Option.some.injEq] at hGen
        subst hGen
        -- instrs = loads ++ [.fcmpR, .bCond cond.negate (pcMap l)]
        -- where loads = (match a, b with .flit, .var => loadB ++ loadA | _, _ => loadA ++ loadB)
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hmem
        have loadA_nb : ∀ i ∈ (match a with
            | .var v => vLoadVarFP layout v (match a with | .var v => (match layout v with | some (.freg r) => r | _ => .d1) | _ => .d1)
            | .flit n => formalLoadImm64 .x0 n ++ [ArmInstr.fmovToFP (match a with | .var v => (match layout v with | some (.freg r) => r | _ => .d1) | _ => .d1) .x0]
            | _ => []),
            (∀ lbl, i ≠ ArmInstr.b lbl) ∧ (∀ rn lbl, i ≠ ArmInstr.cbz rn lbl) ∧
            (∀ rn lbl, i ≠ ArmInstr.cbnz rn lbl) ∧ (∀ c lbl, i ≠ ArmInstr.bCond c lbl) := by
          intro i hi
          split at hi
          · exact vLoadVarFP_no_branches _ _ _ _ hi
          · simp only [List.mem_append, List.mem_singleton] at hi
            rcases hi with hLd | hFmov
            · exact formalLoadImm64_no_branches _ _ _ hLd
            · subst hFmov
              refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> intro heq <;> exact ArmInstr.noConfusion heq
          · simp at hi
        have loadB_nb : ∀ i ∈ (match b with
            | .var v => vLoadVarFP layout v (match b with | .var v => (match layout v with | some (.freg r) => r | _ => .d2) | _ => .d2)
            | .flit n => formalLoadImm64 .x0 n ++ [ArmInstr.fmovToFP (match b with | .var v => (match layout v with | some (.freg r) => r | _ => .d2) | _ => .d2) .x0]
            | _ => []),
            (∀ lbl, i ≠ ArmInstr.b lbl) ∧ (∀ rn lbl, i ≠ ArmInstr.cbz rn lbl) ∧
            (∀ rn lbl, i ≠ ArmInstr.cbnz rn lbl) ∧ (∀ c lbl, i ≠ ArmInstr.bCond c lbl) := by
          intro i hi
          split at hi
          · exact vLoadVarFP_no_branches _ _ _ _ hi
          · simp only [List.mem_append, List.mem_singleton] at hi
            rcases hi with hLd | hFmov
            · exact formalLoadImm64_no_branches _ _ _ hLd
            · subst hFmov
              refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> intro heq <;> exact ArmInstr.noConfusion heq
          · simp at hi
        -- The `loads` structure: for the (.flit, .var) sub-pair, it's loadB ++ loadA; else loadA ++ loadB.
        -- Either way, both `loads_nb` and `loadB_nb` apply uniformly, so membership in `loads`
        -- falls into loadA or loadB.
        rcases hmem with (hLoad | hFcmp) | hBCond
        · -- instr' ∈ loads
          -- loads is either loadA ++ loadB or loadB ++ loadA depending on a, b.
          -- Split on the order then apply the helpers.
          cases a with
          | var va =>
            cases b with
            | var vb =>
              simp only [List.mem_append] at hLoad
              rcases hLoad with hA | hB
              · have ⟨nb, nz, nnz, nbc⟩ := loadA_nb _ hA
                rcases hbranch with h | ⟨rn, h⟩ | ⟨rn, h⟩ | ⟨c, h⟩
                · exact absurd h (nb _)
                · exact absurd h (nz rn _)
                · exact absurd h (nnz rn _)
                · exact absurd h (nbc c _)
              · have ⟨nb, nz, nnz, nbc⟩ := loadB_nb _ hB
                rcases hbranch with h | ⟨rn, h⟩ | ⟨rn, h⟩ | ⟨c, h⟩
                · exact absurd h (nb _)
                · exact absurd h (nz rn _)
                · exact absurd h (nnz rn _)
                · exact absurd h (nbc c _)
            | flit nb =>
              simp only [List.mem_append] at hLoad
              rcases hLoad with hA | hB
              · have ⟨nb, nz, nnz, nbc⟩ := loadA_nb _ hA
                rcases hbranch with h | ⟨rn, h⟩ | ⟨rn, h⟩ | ⟨c, h⟩
                · exact absurd h (nb _)
                · exact absurd h (nz rn _)
                · exact absurd h (nnz rn _)
                · exact absurd h (nbc c _)
              · have ⟨nb, nz, nnz, nbc⟩ := loadB_nb _ hB
                rcases hbranch with h | ⟨rn, h⟩ | ⟨rn, h⟩ | ⟨c, h⟩
                · exact absurd h (nb _)
                · exact absurd h (nz rn _)
                · exact absurd h (nnz rn _)
                · exact absurd h (nbc c _)
            | _ =>
              simp only [List.mem_append, List.not_mem_nil, or_false] at hLoad
              have ⟨nb, nz, nnz, nbc⟩ := loadA_nb _ hLoad
              rcases hbranch with h | ⟨rn, h⟩ | ⟨rn, h⟩ | ⟨c, h⟩
              · exact absurd h (nb _)
              · exact absurd h (nz rn _)
              · exact absurd h (nnz rn _)
              · exact absurd h (nbc c _)
          | flit na =>
            cases b with
            | var vb =>
              -- This is the (.flit, .var) special case: loads = loadB ++ loadA
              simp only [List.mem_append] at hLoad
              rcases hLoad with hB | hA
              · have ⟨nb, nz, nnz, nbc⟩ := loadB_nb _ hB
                rcases hbranch with h | ⟨rn, h⟩ | ⟨rn, h⟩ | ⟨c, h⟩
                · exact absurd h (nb _)
                · exact absurd h (nz rn _)
                · exact absurd h (nnz rn _)
                · exact absurd h (nbc c _)
              · have ⟨nb, nz, nnz, nbc⟩ := loadA_nb _ hA
                rcases hbranch with h | ⟨rn, h⟩ | ⟨rn, h⟩ | ⟨c, h⟩
                · exact absurd h (nb _)
                · exact absurd h (nz rn _)
                · exact absurd h (nnz rn _)
                · exact absurd h (nbc c _)
            | flit nb =>
              simp only [List.mem_append] at hLoad
              rcases hLoad with hA | hB
              · have ⟨nb, nz, nnz, nbc⟩ := loadA_nb _ hA
                rcases hbranch with h | ⟨rn, h⟩ | ⟨rn, h⟩ | ⟨c, h⟩
                · exact absurd h (nb _)
                · exact absurd h (nz rn _)
                · exact absurd h (nnz rn _)
                · exact absurd h (nbc c _)
              · have ⟨nb, nz, nnz, nbc⟩ := loadB_nb _ hB
                rcases hbranch with h | ⟨rn, h⟩ | ⟨rn, h⟩ | ⟨c, h⟩
                · exact absurd h (nb _)
                · exact absurd h (nz rn _)
                · exact absurd h (nnz rn _)
                · exact absurd h (nbc c _)
            | _ =>
              simp only [List.mem_append, List.not_mem_nil, or_false] at hLoad
              have ⟨nb, nz, nnz, nbc⟩ := loadA_nb _ hLoad
              rcases hbranch with h | ⟨rn, h⟩ | ⟨rn, h⟩ | ⟨c, h⟩
              · exact absurd h (nb _)
              · exact absurd h (nz rn _)
              · exact absurd h (nnz rn _)
              · exact absurd h (nbc c _)
          | _ =>
            simp only [List.mem_append, List.not_mem_nil, or_false, List.not_mem_nil] at hLoad
            -- With a matching neither .var nor .flit, loadA = []. Remaining is loadB.
            cases b with
            | var vb =>
              have ⟨nb, nz, nnz, nbc⟩ := loadB_nb _ hLoad
              rcases hbranch with h | ⟨rn, h⟩ | ⟨rn, h⟩ | ⟨c, h⟩
              · exact absurd h (nb _)
              · exact absurd h (nz rn _)
              · exact absurd h (nnz rn _)
              · exact absurd h (nbc c _)
            | flit nb =>
              have ⟨nb, nz, nnz, nbc⟩ := loadB_nb _ hLoad
              rcases hbranch with h | ⟨rn, h⟩ | ⟨rn, h⟩ | ⟨c, h⟩
              · exact absurd h (nb _)
              · exact absurd h (nz rn _)
              · exact absurd h (nnz rn _)
              · exact absurd h (nbc c _)
            | _ => simp at hLoad
        · -- instr' = .fcmpR
          subst hFcmp
          rcases hbranch with h | ⟨rn, h⟩ | ⟨rn, h⟩ | ⟨c, h⟩
          all_goals exact ArmInstr.noConfusion h
        · -- instr' = .bCond cond.negate (pcMap l)
          subst hBCond
          rcases hbranch with h | ⟨rn, h⟩ | ⟨rn, h⟩ | ⟨c, h⟩
          · exact ArmInstr.noConfusion h
          · exact ArmInstr.noConfusion h
          · exact ArmInstr.noConfusion h
          · cases h; exact hPcMapBound
      · -- Fallback arm: verifiedGenBoolExpr ++ [.cbnz .x0 (pcMap l)]
        simp only [Option.some.injEq] at hGen
        subst hGen
        simp only [List.mem_append, List.mem_singleton] at hmem
        rcases hmem with hGBE | hCbnz
        · have ⟨nb, nz, nnz, nbc⟩ := verifiedGenBoolExpr_no_branches layout be _ hGBE
          rcases hbranch with h | ⟨rn, h⟩ | ⟨rn, h⟩ | ⟨c, h⟩
          · exact absurd h (nb _)
          · exact absurd h (nz rn _)
          · exact absurd h (nnz rn _)
          · exact absurd h (nbc c _)
        · subst hCbnz
          rcases hbranch with h | ⟨rn, h⟩ | ⟨rn, h⟩ | ⟨c, h⟩
          · exact ArmInstr.noConfusion h
          · exact ArmInstr.noConfusion h
          · cases h; exact hPcMapBound
          · exact ArmInstr.noConfusion h
-/

/-! ### Per-TAC-constructor branch-target bounds

    Each theorem handles one TAC constructor's output. The aggregator
    `verifiedGenInstr_branch_target_bounded` below dispatches to these.
    Proofs are mechanical: unfold `verifiedGenInstr`, split on layout/op guards,
    and for each emitted instruction either invoke a `_no_branches` helper or
    directly dismiss via `ArmInstr.noConfusion`. -/

/-- Closer: given a non-branch witness for instr', close the `lbl ≤ boundsS` goal
    vacuously (all four branch-form disjuncts are false). -/
private theorem close_non_branch {instr' : ArmInstr} {lbl boundsS : Nat}
    (hnb : (∀ l, instr' ≠ ArmInstr.b l) ∧
           (∀ rn l, instr' ≠ ArmInstr.cbz rn l) ∧
           (∀ rn l, instr' ≠ ArmInstr.cbnz rn l) ∧
           (∀ c l, instr' ≠ ArmInstr.bCond c l))
    (hbranch : instr' = ArmInstr.b lbl ∨
               (∃ rn, instr' = ArmInstr.cbz rn lbl) ∨
               (∃ rn, instr' = ArmInstr.cbnz rn lbl) ∨
               (∃ c, instr' = ArmInstr.bCond c lbl)) :
    lbl ≤ boundsS := by
  obtain ⟨nb, nz, nnz, nbc⟩ := hnb
  rcases hbranch with h | ⟨rn, h⟩ | ⟨rn, h⟩ | ⟨c, h⟩
  · exact absurd h (nb _)
  · exact absurd h (nz rn _)
  · exact absurd h (nnz rn _)
  · exact absurd h (nbc c _)

/-- `.halt` emits `[.b haltLabel]`. The branch targets `haltS ≤ boundsS`. -/
private theorem verifiedGenInstr_halt_branch_bounded
    (layout : VarLayout) (pcMap : Nat → Nat)
    (haltS divS boundsS : Nat) (arrayDecls : List (ArrayName × Nat × VarTy))
    (safe : Bool) {instrs : List ArmInstr}
    (hGen : verifiedGenInstr layout pcMap TAC.halt
      haltS divS boundsS arrayDecls safe = some instrs)
    (hHaltBound : haltS ≤ boundsS) :
    ∀ instr' ∈ instrs, ∀ lbl,
      (instr' = ArmInstr.b lbl ∨
       (∃ rn, instr' = ArmInstr.cbz rn lbl) ∨
       (∃ rn, instr' = ArmInstr.cbnz rn lbl) ∨
       (∃ c, instr' = ArmInstr.bCond c lbl)) →
      lbl ≤ boundsS := by
  simp only [verifiedGenInstr] at hGen
  simp only [Option.some.injEq] at hGen
  subst hGen
  intro instr' hmem lbl hbranch
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  subst hmem
  rcases hbranch with h | ⟨rn, h⟩ | ⟨rn, h⟩ | ⟨c, h⟩
  · cases h; exact hHaltBound
  · exact ArmInstr.noConfusion h
  · exact ArmInstr.noConfusion h
  · exact ArmInstr.noConfusion h

/-- `.printString` emits `[.callPrintS lit]`. No branches. -/
private theorem verifiedGenInstr_printString_branch_bounded
    (layout : VarLayout) (pcMap : Nat → Nat) (lit : String)
    (haltS divS boundsS : Nat) (arrayDecls : List (ArrayName × Nat × VarTy))
    (safe : Bool) {instrs : List ArmInstr}
    (hGen : verifiedGenInstr layout pcMap (TAC.printString lit)
      haltS divS boundsS arrayDecls safe = some instrs) :
    ∀ instr' ∈ instrs, ∀ lbl,
      (instr' = ArmInstr.b lbl ∨
       (∃ rn, instr' = ArmInstr.cbz rn lbl) ∨
       (∃ rn, instr' = ArmInstr.cbnz rn lbl) ∨
       (∃ c, instr' = ArmInstr.bCond c lbl)) →
      lbl ≤ boundsS := by
  simp only [verifiedGenInstr] at hGen
  simp only [Option.some.injEq] at hGen
  subst hGen
  intro instr' hmem lbl hbranch
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  subst hmem
  refine close_non_branch ⟨?_, ?_, ?_, ?_⟩ hbranch <;> intros <;> intro h <;>
    exact ArmInstr.noConfusion h

/-- `.printInt v` emits `vLoadVar ++ [.callPrintI]`. No branches. -/
private theorem verifiedGenInstr_printInt_branch_bounded
    (layout : VarLayout) (pcMap : Nat → Nat) (v : Var)
    (haltS divS boundsS : Nat) (arrayDecls : List (ArrayName × Nat × VarTy))
    (safe : Bool) {instrs : List ArmInstr}
    (hGen : verifiedGenInstr layout pcMap (TAC.printInt v)
      haltS divS boundsS arrayDecls safe = some instrs) :
    ∀ instr' ∈ instrs, ∀ lbl,
      (instr' = ArmInstr.b lbl ∨
       (∃ rn, instr' = ArmInstr.cbz rn lbl) ∨
       (∃ rn, instr' = ArmInstr.cbnz rn lbl) ∨
       (∃ c, instr' = ArmInstr.bCond c lbl)) →
      lbl ≤ boundsS := by
  simp only [verifiedGenInstr] at hGen
  split at hGen
  · exact absurd hGen (by intro h; cases h)
  · simp only [Option.some.injEq] at hGen
    subst hGen
    intro instr' hmem lbl hbranch
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hmem
    refine close_non_branch ?_ hbranch
    rcases hmem with hLd | hCall
    · exact vLoadVar_no_branches _ _ _ _ hLd
    · subst hCall
      refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> intro heq <;>
        exact ArmInstr.noConfusion heq

/-- `.printBool v` emits `vLoadVar ++ [.callPrintB]`. No branches. -/
private theorem verifiedGenInstr_printBool_branch_bounded
    (layout : VarLayout) (pcMap : Nat → Nat) (v : Var)
    (haltS divS boundsS : Nat) (arrayDecls : List (ArrayName × Nat × VarTy))
    (safe : Bool) {instrs : List ArmInstr}
    (hGen : verifiedGenInstr layout pcMap (TAC.printBool v)
      haltS divS boundsS arrayDecls safe = some instrs) :
    ∀ instr' ∈ instrs, ∀ lbl,
      (instr' = ArmInstr.b lbl ∨
       (∃ rn, instr' = ArmInstr.cbz rn lbl) ∨
       (∃ rn, instr' = ArmInstr.cbnz rn lbl) ∨
       (∃ c, instr' = ArmInstr.bCond c lbl)) →
      lbl ≤ boundsS := by
  simp only [verifiedGenInstr] at hGen
  split at hGen
  · exact absurd hGen (by intro h; cases h)
  · simp only [Option.some.injEq] at hGen
    subst hGen
    intro instr' hmem lbl hbranch
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hmem
    refine close_non_branch ?_ hbranch
    rcases hmem with hLd | hCall
    · exact vLoadVar_no_branches _ _ _ _ hLd
    · subst hCall
      refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> intro heq <;>
        exact ArmInstr.noConfusion heq

/-- `.printFloat v` emits `vLoadVarFP ++ [.callPrintF]`. No branches. -/
private theorem verifiedGenInstr_printFloat_branch_bounded
    (layout : VarLayout) (pcMap : Nat → Nat) (v : Var)
    (haltS divS boundsS : Nat) (arrayDecls : List (ArrayName × Nat × VarTy))
    (safe : Bool) {instrs : List ArmInstr}
    (hGen : verifiedGenInstr layout pcMap (TAC.printFloat v)
      haltS divS boundsS arrayDecls safe = some instrs) :
    ∀ instr' ∈ instrs, ∀ lbl,
      (instr' = ArmInstr.b lbl ∨
       (∃ rn, instr' = ArmInstr.cbz rn lbl) ∨
       (∃ rn, instr' = ArmInstr.cbnz rn lbl) ∨
       (∃ c, instr' = ArmInstr.bCond c lbl)) →
      lbl ≤ boundsS := by
  simp only [verifiedGenInstr] at hGen
  split at hGen
  · exact absurd hGen (by intro h; cases h)
  · simp only [Option.some.injEq] at hGen
    subst hGen
    intro instr' hmem lbl hbranch
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hmem
    refine close_non_branch ?_ hbranch
    rcases hmem with hLd | hCall
    · exact vLoadVarFP_no_branches _ _ _ _ hLd
    · subst hCall
      refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> intro heq <;>
        exact ArmInstr.noConfusion heq

/-- `.print fmt args` always returns `none` (verifiedGenInstr doesn't handle print);
    so the hypothesis `= some instrs` is vacuous. -/
private theorem verifiedGenInstr_print_branch_bounded
    (layout : VarLayout) (pcMap : Nat → Nat) (fmt : String) (args : List Var)
    (haltS divS boundsS : Nat) (arrayDecls : List (ArrayName × Nat × VarTy))
    (safe : Bool) {instrs : List ArmInstr}
    (hGen : verifiedGenInstr layout pcMap (TAC.print fmt args)
      haltS divS boundsS arrayDecls safe = some instrs) :
    ∀ instr' ∈ instrs, ∀ lbl,
      (instr' = ArmInstr.b lbl ∨
       (∃ rn, instr' = ArmInstr.cbz rn lbl) ∨
       (∃ rn, instr' = ArmInstr.cbnz rn lbl) ∨
       (∃ c, instr' = ArmInstr.bCond c lbl)) →
      lbl ≤ boundsS := by
  simp only [verifiedGenInstr] at hGen
  exact absurd hGen (by intro h; cases h)

/-- `.copy dst src`: emits one of four forms — self-copy `[.movR .x0 .x0]`,
    freg-src `vStoreVarFP`, freg-dst `vLoadVar ++ [.fmovToFP]`, or
    int-int `vLoadVar ++ vStoreVar`. All non-branch. -/
private theorem verifiedGenInstr_copy_branch_bounded
    (layout : VarLayout) (pcMap : Nat → Nat) (dst src : Var)
    (haltS divS boundsS : Nat) (arrayDecls : List (ArrayName × Nat × VarTy))
    (safe : Bool) {instrs : List ArmInstr}
    (hGen : verifiedGenInstr layout pcMap (TAC.copy dst src)
      haltS divS boundsS arrayDecls safe = some instrs) :
    ∀ instr' ∈ instrs, ∀ lbl,
      (instr' = ArmInstr.b lbl ∨
       (∃ rn, instr' = ArmInstr.cbz rn lbl) ∨
       (∃ rn, instr' = ArmInstr.cbnz rn lbl) ∨
       (∃ c, instr' = ArmInstr.bCond c lbl)) →
      lbl ≤ boundsS := by
  simp only [verifiedGenInstr] at hGen
  intro instr' hmem lbl hbranch
  refine close_non_branch ?_ hbranch
  split at hGen
  · simp only [Option.some.injEq] at hGen; subst hGen
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem; subst hmem
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> intro h <;>
      exact ArmInstr.noConfusion h
  · split at hGen
    · simp only [Option.some.injEq] at hGen; subst hGen
      exact vStoreVarFP_no_branches _ _ _ _ hmem
    · split at hGen
      · simp only [Option.some.injEq] at hGen; subst hGen
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with hLd | hFmov
        · exact vLoadVar_no_branches _ _ _ _ hLd
        · subst hFmov
          refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> intro heq <;>
            exact ArmInstr.noConfusion heq
      · simp only [Option.some.injEq] at hGen; subst hGen
        simp only [List.mem_append] at hmem
        rcases hmem with hLd | hSt
        · exact vLoadVar_no_branches _ _ _ _ hLd
        · exact vStoreVar_no_branches _ _ _ _ hSt

/-- `.boolop dst be`: emits `verifiedGenBoolExpr ++ vStoreVar`. No branches. -/
private theorem verifiedGenInstr_boolop_branch_bounded
    (layout : VarLayout) (pcMap : Nat → Nat) (dst : Var) (be : BoolExpr)
    (haltS divS boundsS : Nat) (arrayDecls : List (ArrayName × Nat × VarTy))
    (safe : Bool) {instrs : List ArmInstr}
    (hGen : verifiedGenInstr layout pcMap (TAC.boolop dst be)
      haltS divS boundsS arrayDecls safe = some instrs) :
    ∀ instr' ∈ instrs, ∀ lbl,
      (instr' = ArmInstr.b lbl ∨
       (∃ rn, instr' = ArmInstr.cbz rn lbl) ∨
       (∃ rn, instr' = ArmInstr.cbnz rn lbl) ∨
       (∃ c, instr' = ArmInstr.bCond c lbl)) →
      lbl ≤ boundsS := by
  simp only [verifiedGenInstr] at hGen
  split at hGen
  · exact absurd hGen (by intro h; cases h)
  · -- Inner `if (match layout dst with | some (.freg _) => true | _ => false) then none else some X`
    -- Case-split on layout dst being a freg vs not.
    by_cases hF : ∃ r, List.lookup dst layout.entries = some (VarLoc.freg r)
    · obtain ⟨r, hR⟩ := hF
      simp only [hR] at hGen
      exact absurd hGen (by intro h; cases h)
    · -- layout dst is not a freg → the match evaluates to false → if takes else → some (...)
      have hNF : (match List.lookup dst layout.entries with
                  | some (VarLoc.freg _) => true | _ => false) = false := by
        rcases hL : List.lookup dst layout.entries with _ | loc
        · rfl
        · cases loc with
          | stack _ => rfl
          | ireg _ => rfl
          | freg r => exact absurd ⟨r, hL⟩ hF
      simp [hNF] at hGen
      obtain ⟨_, hGen⟩ := hGen
      subst hGen
      intro instr' hmem lbl hbranch
      refine close_non_branch ?_ hbranch
      simp only [List.mem_append] at hmem
      rcases hmem with hBE | hSt
      · exact verifiedGenBoolExpr_no_branches _ _ _ hBE
      · exact vStoreVar_no_branches _ _ _ _ hSt

/-- `.binop dst .mod lv rv`: mirror of the `.div` probe with a 3-instruction
    opInstr `[.sdivR, .mulR, .subR]` and the same cbz-to-divLabel branch. -/
private theorem verifiedGenInstr_binop_mod_branch_bounded
    (layout : VarLayout) (pcMap : Nat → Nat) (dst lv rv : Var)
    (haltS divS boundsS : Nat) (arrayDecls : List (ArrayName × Nat × VarTy))
    (safe : Bool) {instrs : List ArmInstr}
    (hGen : verifiedGenInstr layout pcMap (.binop dst .mod lv rv)
      haltS divS boundsS arrayDecls safe = some instrs)
    (hRC : layout.regConventionSafe = true)
    (hII : layout.isInjective = true)
    (hDivBound : divS ≤ boundsS) :
    ∀ instr' ∈ instrs, ∀ lbl,
      (instr' = ArmInstr.b lbl ∨
       (∃ rn, instr' = ArmInstr.cbz rn lbl) ∨
       (∃ rn, instr' = ArmInstr.cbnz rn lbl) ∨
       (∃ c, instr' = ArmInstr.bCond c lbl)) →
      lbl ≤ boundsS := by
  simp [verifiedGenInstr, hRC, hII] at hGen
  split at hGen <;> first | simp at hGen | skip
  all_goals (split at hGen <;> first | simp at hGen | skip)
  all_goals (split at hGen <;> first | simp at hGen | skip)
  all_goals (subst hGen)
  all_goals (
    intro instr' hmem lbl hbranch
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with hLv | hRv | hCbz | hSdiv | hMul | hSub | hStore
    · refine close_non_branch ?_ hbranch
      exact vLoadVar_no_branches _ _ _ _ hLv
    · refine close_non_branch ?_ hbranch
      exact vLoadVar_no_branches _ _ _ _ hRv
    · subst hCbz
      rcases hbranch with h | ⟨rn, h⟩ | ⟨rn, h⟩ | ⟨c, h⟩
      · exact ArmInstr.noConfusion h
      · cases h; exact hDivBound
      · exact ArmInstr.noConfusion h
      · exact ArmInstr.noConfusion h
    · subst hSdiv
      refine close_non_branch ?_ hbranch
      refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> intro heq <;> exact ArmInstr.noConfusion heq
    · subst hMul
      refine close_non_branch ?_ hbranch
      refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> intro heq <;> exact ArmInstr.noConfusion heq
    · subst hSub
      refine close_non_branch ?_ hbranch
      refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> intro heq <;> exact ArmInstr.noConfusion heq
    · refine close_non_branch ?_ hbranch
      exact vStoreVar_no_branches _ _ _ _ hStore)

/-- `.binop dst op lv rv` for `op ∉ {.div, .mod}`: emits
    `vLoadVar ++ vLoadVar ++ [opInstr_single] ++ vStoreVar`. No branches. -/
private theorem verifiedGenInstr_binop_std_branch_bounded
    (layout : VarLayout) (pcMap : Nat → Nat) (dst : Var) (op : BinOp) (lv rv : Var)
    (haltS divS boundsS : Nat) (arrayDecls : List (ArrayName × Nat × VarTy))
    (safe : Bool) {instrs : List ArmInstr}
    (hGen : verifiedGenInstr layout pcMap (TAC.binop dst op lv rv)
      haltS divS boundsS arrayDecls safe = some instrs)
    (hRC : layout.regConventionSafe = true)
    (hII : layout.isInjective = true)
    (hNeDiv : op ≠ .div)
    (hNeMod : op ≠ .mod) :
    ∀ instr' ∈ instrs, ∀ lbl,
      (instr' = ArmInstr.b lbl ∨
       (∃ rn, instr' = ArmInstr.cbz rn lbl) ∨
       (∃ rn, instr' = ArmInstr.cbnz rn lbl) ∨
       (∃ c, instr' = ArmInstr.bCond c lbl)) →
      lbl ≤ boundsS := by
  cases op
  all_goals first
    | (exact absurd rfl hNeDiv)
    | (exact absurd rfl hNeMod)
    | (
        simp [verifiedGenInstr, hRC, hII] at hGen
        split at hGen <;> first | simp at hGen | skip
        all_goals (split at hGen <;> first | simp at hGen | skip)
        all_goals (split at hGen <;> first | simp at hGen | skip)
        all_goals (subst hGen)
        all_goals (
          intro instr' hmem lbl hbranch
          refine close_non_branch ?_ hbranch
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hmem
          rcases hmem with hLv | hRv | hOp | hStore
          · exact vLoadVar_no_branches _ _ _ _ hLv
          · exact vLoadVar_no_branches _ _ _ _ hRv
          · subst hOp
            refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> intro heq <;>
              exact ArmInstr.noConfusion heq
          · exact vStoreVar_no_branches _ _ _ _ hStore))

/-- `.fbinop dst fop lv rv`: emits `vLoadVarFP ++ vLoadVarFP ++ [fpInstr] ++ vStoreVarFP`.
    `fpInstr` is one of the float binop / libcall instructions — all non-branch. -/
private theorem verifiedGenInstr_fbinop_branch_bounded
    (layout : VarLayout) (pcMap : Nat → Nat) (dst : Var) (fop : FloatBinOp) (lv rv : Var)
    (haltS divS boundsS : Nat) (arrayDecls : List (ArrayName × Nat × VarTy))
    (safe : Bool) {instrs : List ArmInstr}
    (hGen : verifiedGenInstr layout pcMap (TAC.fbinop dst fop lv rv)
      haltS divS boundsS arrayDecls safe = some instrs) :
    ∀ instr' ∈ instrs, ∀ lbl,
      (instr' = ArmInstr.b lbl ∨
       (∃ rn, instr' = ArmInstr.cbz rn lbl) ∨
       (∃ rn, instr' = ArmInstr.cbnz rn lbl) ∨
       (∃ c, instr' = ArmInstr.bCond c lbl)) →
      lbl ≤ boundsS := by
  simp only [verifiedGenInstr] at hGen
  split at hGen <;> simp at hGen
  -- survivors: only the `_, _, _` fall-through case (with `some (...) = some instrs`)
  subst hGen
  intro instr' hmem lbl hbranch
  refine close_non_branch ?_ hbranch
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with hLv | hRv | hOp | hStore
  · exact vLoadVarFP_no_branches _ _ _ _ hLv
  · exact vLoadVarFP_no_branches _ _ _ _ hRv
  · subst hOp
    cases fop <;> (
      refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> intro heq <;>
        exact ArmInstr.noConfusion heq)
  · exact vStoreVarFP_no_branches _ _ _ _ hStore

/-- `.intToFloat dst src`: emits `vLoadVar ++ [.scvtf] ++ vStoreVarFP`. No branches. -/
private theorem verifiedGenInstr_intToFloat_branch_bounded
    (layout : VarLayout) (pcMap : Nat → Nat) (dst src : Var)
    (haltS divS boundsS : Nat) (arrayDecls : List (ArrayName × Nat × VarTy))
    (safe : Bool) {instrs : List ArmInstr}
    (hGen : verifiedGenInstr layout pcMap (TAC.intToFloat dst src)
      haltS divS boundsS arrayDecls safe = some instrs) :
    ∀ instr' ∈ instrs, ∀ lbl,
      (instr' = ArmInstr.b lbl ∨
       (∃ rn, instr' = ArmInstr.cbz rn lbl) ∨
       (∃ rn, instr' = ArmInstr.cbnz rn lbl) ∨
       (∃ c, instr' = ArmInstr.bCond c lbl)) →
      lbl ≤ boundsS := by
  simp only [verifiedGenInstr] at hGen
  split at hGen <;> simp at hGen
  subst hGen
  intro instr' hmem lbl hbranch
  refine close_non_branch ?_ hbranch
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with hLd | hCvt | hSt
  · exact vLoadVar_no_branches _ _ _ _ hLd
  · subst hCvt
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> intro heq <;>
      exact ArmInstr.noConfusion heq
  · exact vStoreVarFP_no_branches _ _ _ _ hSt

/-- `.floatToInt dst src`: emits `vLoadVarFP ++ [.fcvtzs] ++ vStoreVar`. No branches. -/
private theorem verifiedGenInstr_floatToInt_branch_bounded
    (layout : VarLayout) (pcMap : Nat → Nat) (dst src : Var)
    (haltS divS boundsS : Nat) (arrayDecls : List (ArrayName × Nat × VarTy))
    (safe : Bool) {instrs : List ArmInstr}
    (hGen : verifiedGenInstr layout pcMap (TAC.floatToInt dst src)
      haltS divS boundsS arrayDecls safe = some instrs) :
    ∀ instr' ∈ instrs, ∀ lbl,
      (instr' = ArmInstr.b lbl ∨
       (∃ rn, instr' = ArmInstr.cbz rn lbl) ∨
       (∃ rn, instr' = ArmInstr.cbnz rn lbl) ∨
       (∃ c, instr' = ArmInstr.bCond c lbl)) →
      lbl ≤ boundsS := by
  simp only [verifiedGenInstr] at hGen
  split at hGen <;> simp at hGen
  subst hGen
  intro instr' hmem lbl hbranch
  refine close_non_branch ?_ hbranch
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with hLd | hCvt | hSt
  · exact vLoadVarFP_no_branches _ _ _ _ hLd
  · subst hCvt
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> intro heq <;>
      exact ArmInstr.noConfusion heq
  · exact vStoreVar_no_branches _ _ _ _ hSt

/-- `.floatUnary dst op src`: emits `vLoadVarFP ++ [.floatUnaryInstr] ++ vStoreVarFP`.
    No branches. -/
private theorem verifiedGenInstr_floatUnary_branch_bounded
    (layout : VarLayout) (pcMap : Nat → Nat) (dst : Var) (op : FloatUnaryOp) (src : Var)
    (haltS divS boundsS : Nat) (arrayDecls : List (ArrayName × Nat × VarTy))
    (safe : Bool) {instrs : List ArmInstr}
    (hGen : verifiedGenInstr layout pcMap (TAC.floatUnary dst op src)
      haltS divS boundsS arrayDecls safe = some instrs) :
    ∀ instr' ∈ instrs, ∀ lbl,
      (instr' = ArmInstr.b lbl ∨
       (∃ rn, instr' = ArmInstr.cbz rn lbl) ∨
       (∃ rn, instr' = ArmInstr.cbnz rn lbl) ∨
       (∃ c, instr' = ArmInstr.bCond c lbl)) →
      lbl ≤ boundsS := by
  simp only [verifiedGenInstr] at hGen
  split at hGen <;> simp at hGen
  subst hGen
  intro instr' hmem lbl hbranch
  refine close_non_branch ?_ hbranch
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with hLd | hOp | hSt
  · exact vLoadVarFP_no_branches _ _ _ _ hLd
  · subst hOp
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> intro heq <;>
      exact ArmInstr.noConfusion heq
  · exact vStoreVarFP_no_branches _ _ _ _ hSt

/-- `.fternop dst op a b c`: emits `vLoadVarFP×3 ++ [fpInstr] ++ vStoreVarFP`. No branches. -/
private theorem verifiedGenInstr_fternop_branch_bounded
    (layout : VarLayout) (pcMap : Nat → Nat) (dst : Var) (op : FloatTernOp) (a b c : Var)
    (haltS divS boundsS : Nat) (arrayDecls : List (ArrayName × Nat × VarTy))
    (safe : Bool) {instrs : List ArmInstr}
    (hGen : verifiedGenInstr layout pcMap (TAC.fternop dst op a b c)
      haltS divS boundsS arrayDecls safe = some instrs) :
    ∀ instr' ∈ instrs, ∀ lbl,
      (instr' = ArmInstr.b lbl ∨
       (∃ rn, instr' = ArmInstr.cbz rn lbl) ∨
       (∃ rn, instr' = ArmInstr.cbnz rn lbl) ∨
       (∃ c, instr' = ArmInstr.bCond c lbl)) →
      lbl ≤ boundsS := by
  simp only [verifiedGenInstr] at hGen
  split at hGen <;> simp at hGen
  subst hGen
  intro instr' hmem lbl hbranch
  refine close_non_branch ?_ hbranch
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with hA | hB | hC | hOp | hSt
  · exact vLoadVarFP_no_branches _ _ _ _ hA
  · exact vLoadVarFP_no_branches _ _ _ _ hB
  · exact vLoadVarFP_no_branches _ _ _ _ hC
  · subst hOp
    cases op <;> (
      refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> intro heq <;>
        exact ArmInstr.noConfusion heq)
  · exact vStoreVarFP_no_branches _ _ _ _ hSt

/-- `.arrLoad x arr idx ty`: emits `vLoadVar ++ boundsCheck ++ [load-instrs] ++ vStoreVar?`.
    The only branch is `.bCond .hs boundsLabel` inside `boundsCheck` (when not safe),
    targeting `boundsS ≤ boundsS` which is trivial. -/
private theorem verifiedGenInstr_arrLoad_branch_bounded
    (layout : VarLayout) (pcMap : Nat → Nat) (x : Var) (arr : ArrayName) (idx : Var) (ty : VarTy)
    (haltS divS boundsS : Nat) (arrayDecls : List (ArrayName × Nat × VarTy))
    (safe : Bool) {instrs : List ArmInstr}
    (hGen : verifiedGenInstr layout pcMap (TAC.arrLoad x arr idx ty)
      haltS divS boundsS arrayDecls safe = some instrs) :
    ∀ instr' ∈ instrs, ∀ lbl,
      (instr' = ArmInstr.b lbl ∨
       (∃ rn, instr' = ArmInstr.cbz rn lbl) ∨
       (∃ rn, instr' = ArmInstr.cbnz rn lbl) ∨
       (∃ c, instr' = ArmInstr.bCond c lbl)) →
      lbl ≤ boundsS := by
  have bc_nb : ∀ i ∈ (if safe then ([] : List ArmInstr)
      else [.cmpImm (match layout idx with | some (.ireg r) => r | _ => .x1)
              (arraySizeBv arrayDecls arr),
            .bCond .hs boundsS]), ∀ lbl,
      (i = ArmInstr.b lbl ∨ (∃ rn, i = ArmInstr.cbz rn lbl) ∨
       (∃ rn, i = ArmInstr.cbnz rn lbl) ∨ (∃ c, i = ArmInstr.bCond c lbl)) →
      lbl ≤ boundsS := by
    intro i hi lbl hbranch
    split at hi
    · simp at hi
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with hCmp | hBc
      · subst hCmp
        rcases hbranch with h | ⟨rn, h⟩ | ⟨rn, h⟩ | ⟨c, h⟩ <;> exact ArmInstr.noConfusion h
      · subst hBc
        rcases hbranch with h | ⟨rn, h⟩ | ⟨rn, h⟩ | ⟨c, h⟩
        · exact ArmInstr.noConfusion h
        · exact ArmInstr.noConfusion h
        · exact ArmInstr.noConfusion h
        · cases h; exact le_refl _
  -- Common tail for int/float cases (hmem: instr' ∈ loadIdx ++ boundsCheck ++ [arrLd] ++ storeVar)
  have close_int_float : ∀ (instrsX : List ArmInstr) (storeVar : List ArmInstr)
      (hStoreNB : ∀ i ∈ storeVar, (∀ l, i ≠ ArmInstr.b l) ∧ (∀ rn l, i ≠ ArmInstr.cbz rn l) ∧
                  (∀ rn l, i ≠ ArmInstr.cbnz rn l) ∧ (∀ c l, i ≠ ArmInstr.bCond c l))
      (arrLdInstr : ArmInstr) (hArrLdNB : (∀ l, arrLdInstr ≠ ArmInstr.b l) ∧
                  (∀ rn l, arrLdInstr ≠ ArmInstr.cbz rn l) ∧
                  (∀ rn l, arrLdInstr ≠ ArmInstr.cbnz rn l) ∧
                  (∀ c l, arrLdInstr ≠ ArmInstr.bCond c l))
      (heq : instrsX = vLoadVar layout idx (match layout idx with | some (.ireg r) => r | _ => .x1)
              ++ (if safe then [] else
                  [.cmpImm (match layout idx with | some (.ireg r) => r | _ => .x1)
                    (arraySizeBv arrayDecls arr),
                   .bCond .hs boundsS])
              ++ [arrLdInstr] ++ storeVar),
      ∀ instr' ∈ instrsX, ∀ lbl,
        (instr' = ArmInstr.b lbl ∨
         (∃ rn, instr' = ArmInstr.cbz rn lbl) ∨
         (∃ rn, instr' = ArmInstr.cbnz rn lbl) ∨
         (∃ c, instr' = ArmInstr.bCond c lbl)) →
        lbl ≤ boundsS := by
    intro instrsX storeVar hStoreNB arrLdInstr hArrLdNB heq
    rw [heq]
    intro instr' hmem lbl hbranch
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with ((hLd | hBc) | hArrLd) | hSt
    · refine close_non_branch ?_ hbranch
      exact vLoadVar_no_branches _ _ _ _ hLd
    · exact bc_nb _ hBc lbl hbranch
    · subst hArrLd
      exact close_non_branch hArrLdNB hbranch
    · refine close_non_branch ?_ hbranch
      exact hStoreNB _ hSt
  simp only [verifiedGenInstr] at hGen
  split at hGen
  -- Case 1: ty = .float
  · simp only [Option.some.injEq] at hGen
    apply close_int_float instrs _ (vStoreVarFP_no_branches _ _ _) _ _ hGen.symm
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> intro heq <;> exact ArmInstr.noConfusion heq
  -- Case 2: ty = .bool (has 3 instrs: arrLd, cmpImm, cset)
  · simp only [Option.some.injEq] at hGen
    subst hGen
    intro instr' hmem lbl hbranch
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with ((hLd | hBc) | hArrLd | hCmp | hCset) | hSt
    · refine close_non_branch ?_ hbranch
      exact vLoadVar_no_branches _ _ _ _ hLd
    · exact bc_nb _ hBc lbl hbranch
    · subst hArrLd
      refine close_non_branch ?_ hbranch
      refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> intro heq <;>
        exact ArmInstr.noConfusion heq
    · subst hCmp
      refine close_non_branch ?_ hbranch
      refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> intro heq <;>
        exact ArmInstr.noConfusion heq
    · subst hCset
      refine close_non_branch ?_ hbranch
      refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> intro heq <;>
        exact ArmInstr.noConfusion heq
    · refine close_non_branch ?_ hbranch
      exact vStoreVar_no_branches _ _ _ _ hSt
  -- Case 3: ty = .int
  · simp only [Option.some.injEq] at hGen
    apply close_int_float instrs _ (vStoreVar_no_branches _ _ _) _ _ hGen.symm
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> intro heq <;> exact ArmInstr.noConfusion heq

/-- `.arrStore arr idx val ty`: emits `vLoadVar ++ boundsCheck ++ vLoadVar? ++ [arrSt]`.
    Only branch is `.bCond .hs boundsLabel` in boundsCheck, bounded trivially. -/
private theorem verifiedGenInstr_arrStore_branch_bounded
    (layout : VarLayout) (pcMap : Nat → Nat) (arr : ArrayName) (idx val : Var) (ty : VarTy)
    (haltS divS boundsS : Nat) (arrayDecls : List (ArrayName × Nat × VarTy))
    (safe : Bool) {instrs : List ArmInstr}
    (hGen : verifiedGenInstr layout pcMap (TAC.arrStore arr idx val ty)
      haltS divS boundsS arrayDecls safe = some instrs) :
    ∀ instr' ∈ instrs, ∀ lbl,
      (instr' = ArmInstr.b lbl ∨
       (∃ rn, instr' = ArmInstr.cbz rn lbl) ∨
       (∃ rn, instr' = ArmInstr.cbnz rn lbl) ∨
       (∃ c, instr' = ArmInstr.bCond c lbl)) →
      lbl ≤ boundsS := by
  have bc_nb : ∀ i ∈ (if safe then ([] : List ArmInstr)
      else [.cmpImm (match layout idx with | some (.ireg r) => r | _ => .x1)
              (arraySizeBv arrayDecls arr),
            .bCond .hs boundsS]), ∀ lbl,
      (i = ArmInstr.b lbl ∨ (∃ rn, i = ArmInstr.cbz rn lbl) ∨
       (∃ rn, i = ArmInstr.cbnz rn lbl) ∨ (∃ c, i = ArmInstr.bCond c lbl)) →
      lbl ≤ boundsS := by
    intro i hi lbl hbranch
    split at hi
    · simp at hi
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with hCmp | hBc
      · subst hCmp
        rcases hbranch with h | ⟨rn, h⟩ | ⟨rn, h⟩ | ⟨c, h⟩ <;> exact ArmInstr.noConfusion h
      · subst hBc
        rcases hbranch with h | ⟨rn, h⟩ | ⟨rn, h⟩ | ⟨c, h⟩
        · exact ArmInstr.noConfusion h
        · exact ArmInstr.noConfusion h
        · exact ArmInstr.noConfusion h
        · cases h; exact le_refl _
  simp only [verifiedGenInstr] at hGen
  split at hGen
  · -- float branch
    simp only [Option.some.injEq] at hGen; subst hGen
    intro instr' hmem lbl hbranch
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with ((hLd | hBc) | hVal) | hArrSt
    · refine close_non_branch ?_ hbranch
      exact vLoadVar_no_branches _ _ _ _ hLd
    · exact bc_nb _ hBc lbl hbranch
    · refine close_non_branch ?_ hbranch
      exact vLoadVarFP_no_branches _ _ _ _ hVal
    · subst hArrSt
      refine close_non_branch ?_ hbranch
      refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> intro heq <;>
        exact ArmInstr.noConfusion heq
  · -- non-float (int/bool) branch
    simp only [Option.some.injEq] at hGen; subst hGen
    intro instr' hmem lbl hbranch
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with ((hLd | hBc) | hVal) | hArrSt
    · refine close_non_branch ?_ hbranch
      exact vLoadVar_no_branches _ _ _ _ hLd
    · exact bc_nb _ hBc lbl hbranch
    · refine close_non_branch ?_ hbranch
      exact vLoadVar_no_branches _ _ _ _ hVal
    · subst hArrSt
      refine close_non_branch ?_ hbranch
      refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> intro heq <;>
        exact ArmInstr.noConfusion heq

/-- `.const v val`: emits `[loadImm/mov] ++ [store-steps]`. No branches. -/
private theorem verifiedGenInstr_const_branch_bounded
    (layout : VarLayout) (pcMap : Nat → Nat) (v : Var) (val : Value)
    (haltS divS boundsS : Nat) (arrayDecls : List (ArrayName × Nat × VarTy))
    (safe : Bool) {instrs : List ArmInstr}
    (hGen : verifiedGenInstr layout pcMap (TAC.const v val)
      haltS divS boundsS arrayDecls safe = some instrs) :
    ∀ instr' ∈ instrs, ∀ lbl,
      (instr' = ArmInstr.b lbl ∨
       (∃ rn, instr' = ArmInstr.cbz rn lbl) ∨
       (∃ rn, instr' = ArmInstr.cbnz rn lbl) ∨
       (∃ c, instr' = ArmInstr.bCond c lbl)) →
      lbl ≤ boundsS := by
  cases val with
  | int n =>
    simp only [verifiedGenInstr] at hGen
    split at hGen <;> simp at hGen
    all_goals (
      subst hGen
      intro instr' hmem lbl hbranch
      refine close_non_branch ?_ hbranch
      simp only [List.mem_append] at hmem
      rcases hmem with hImm | hSt
      · exact formalLoadImm64_no_branches _ _ _ hImm
      · exact vStoreVar_no_branches _ _ _ _ hSt)
  | bool b =>
    simp only [verifiedGenInstr] at hGen
    split at hGen <;> simp at hGen
    all_goals (
      subst hGen
      intro instr' hmem lbl hbranch
      refine close_non_branch ?_ hbranch
      simp only [List.mem_cons] at hmem
      rcases hmem with hMov | hSt
      · subst hMov
        refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> intro heq <;>
          exact ArmInstr.noConfusion heq
      · exact vStoreVar_no_branches _ _ _ _ hSt)
  | float f =>
    simp only [verifiedGenInstr] at hGen
    split at hGen <;> simp at hGen
    all_goals (
      subst hGen
      intro instr' hmem lbl hbranch
      refine close_non_branch ?_ hbranch
      rw [List.mem_append] at hmem
      rcases hmem with hImm | hCons
      · exact formalLoadImm64_no_branches _ _ _ hImm
      · rw [List.mem_cons] at hCons
        rcases hCons with hFmov | hSt
        · subst hFmov
          refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> intro heq <;>
            exact ArmInstr.noConfusion heq
        · exact vStoreVarFP_no_branches _ _ _ _ hSt)

/-- **Aggregator**: every branch instruction emitted by `verifiedGenInstr` for any
    TAC constructor targets a label ≤ `boundsS`, assuming the standard bounds
    hypotheses on branch/sentinel labels. Dispatches to per-case helpers. -/
private theorem verifiedGenInstr_branch_target_bounded
    (layout : VarLayout) (pcMap : Nat → Nat) (instr : TAC)
    (haltS divS boundsS : Nat) (arrayDecls : List (ArrayName × Nat × VarTy))
    (safe : Bool) {instrs : List ArmInstr}
    (hGen : verifiedGenInstr layout pcMap instr
      haltS divS boundsS arrayDecls safe = some instrs)
    (hRC : layout.regConventionSafe = true)
    (hII : layout.isInjective = true)
    (hPcBound : ∀ l, (instr = TAC.goto l ∨ (∃ be, instr = TAC.ifgoto be l)) →
                pcMap l ≤ boundsS)
    (hHaltBound : haltS ≤ boundsS)
    (hDivBound : divS ≤ boundsS) :
    ∀ instr' ∈ instrs, ∀ lbl,
      (instr' = ArmInstr.b lbl ∨
       (∃ rn, instr' = ArmInstr.cbz rn lbl) ∨
       (∃ rn, instr' = ArmInstr.cbnz rn lbl) ∨
       (∃ c, instr' = ArmInstr.bCond c lbl)) →
      lbl ≤ boundsS := by
  cases instr with
  | const v val =>
    exact verifiedGenInstr_const_branch_bounded layout pcMap v val haltS divS boundsS
      arrayDecls safe hGen
  | copy dst src =>
    exact verifiedGenInstr_copy_branch_bounded layout pcMap dst src haltS divS boundsS
      arrayDecls safe hGen
  | binop dst op lv rv =>
    by_cases hDiv : op = BinOp.div
    · subst hDiv
      exact verifiedGenInstr_binop_div_branch_bounded layout pcMap dst lv rv haltS divS
        boundsS arrayDecls safe hGen hRC hII hDivBound
    · by_cases hMod : op = BinOp.mod
      · subst hMod
        exact verifiedGenInstr_binop_mod_branch_bounded layout pcMap dst lv rv haltS divS
          boundsS arrayDecls safe hGen hRC hII hDivBound
      · exact verifiedGenInstr_binop_std_branch_bounded layout pcMap dst op lv rv haltS
          divS boundsS arrayDecls safe hGen hRC hII hDiv hMod
  | boolop dst be =>
    exact verifiedGenInstr_boolop_branch_bounded layout pcMap dst be haltS divS boundsS
      arrayDecls safe hGen
  | goto l =>
    exact verifiedGenInstr_goto_branch_bounded layout pcMap l haltS divS boundsS
      arrayDecls safe hGen (hPcBound l (Or.inl rfl))
  | ifgoto be l =>
    exact verifiedGenInstr_ifgoto_branch_bounded layout pcMap be l haltS divS boundsS
      arrayDecls safe hGen (hPcBound l (Or.inr ⟨be, rfl⟩))
  | halt =>
    exact verifiedGenInstr_halt_branch_bounded layout pcMap haltS divS boundsS
      arrayDecls safe hGen hHaltBound
  | arrLoad x arr idx ty =>
    exact verifiedGenInstr_arrLoad_branch_bounded layout pcMap x arr idx ty haltS divS
      boundsS arrayDecls safe hGen
  | arrStore arr idx val ty =>
    exact verifiedGenInstr_arrStore_branch_bounded layout pcMap arr idx val ty haltS
      divS boundsS arrayDecls safe hGen
  | fbinop dst fop lv rv =>
    exact verifiedGenInstr_fbinop_branch_bounded layout pcMap dst fop lv rv haltS divS
      boundsS arrayDecls safe hGen
  | intToFloat dst src =>
    exact verifiedGenInstr_intToFloat_branch_bounded layout pcMap dst src haltS divS
      boundsS arrayDecls safe hGen
  | floatToInt dst src =>
    exact verifiedGenInstr_floatToInt_branch_bounded layout pcMap dst src haltS divS
      boundsS arrayDecls safe hGen
  | floatUnary dst op src =>
    exact verifiedGenInstr_floatUnary_branch_bounded layout pcMap dst op src haltS divS
      boundsS arrayDecls safe hGen
  | fternop dst op a b c =>
    exact verifiedGenInstr_fternop_branch_bounded layout pcMap dst op a b c haltS divS
      boundsS arrayDecls safe hGen
  | print fmt args =>
    exact verifiedGenInstr_print_branch_bounded layout pcMap fmt args haltS divS
      boundsS arrayDecls safe hGen
  | printInt v =>
    exact verifiedGenInstr_printInt_branch_bounded layout pcMap v haltS divS
      boundsS arrayDecls safe hGen
  | printBool v =>
    exact verifiedGenInstr_printBool_branch_bounded layout pcMap v haltS divS
      boundsS arrayDecls safe hGen
  | printFloat v =>
    exact verifiedGenInstr_printFloat_branch_bounded layout pcMap v haltS divS
      boundsS arrayDecls safe hGen
  | printString lit =>
    exact verifiedGenInstr_printString_branch_bounded layout pcMap lit haltS divS
      boundsS arrayDecls safe hGen

end Phase6Probes2

-- ============================================================
-- § 11. Phase 6 main — branch-target lift + behavior exhaustion
-- ============================================================

/-!
## Phase 6 main theorems

This section finalizes Phase 6. Consumes the per-TAC helpers from
`Phase6Probes2` via the aggregator `verifiedGenInstr_branch_target_bounded`,
plus new `_no_branches` helpers for the save/restore and halt-save
scaffolding, to prove:

- `bodyFlat_branch_target_bounded` — every branch in `r.bodyFlat`
  targets a label `≤ r.boundsS`.
- `arm_behavior_exhaustive` — every ARM execution lands in one of four
  bins (halt, divS, boundsS, diverges).

No downstream consumers — closing these strengthens Phase 6 on its own
without altering the top-level end-to-end correctness chain (verified
by `#print axioms` on all 12 top-level theorems, session 13 handoff).
-/

section Phase6Main

/-- `entriesToSaves` emits only `.str` and `.fstr` — no branches. -/
private theorem entriesToSaves_no_branches (entries : List CallerSaveEntry) :
    ∀ instr' ∈ entriesToSaves entries,
      (∀ lbl, instr' ≠ ArmInstr.b lbl) ∧
      (∀ rn lbl, instr' ≠ ArmInstr.cbz rn lbl) ∧
      (∀ rn lbl, instr' ≠ ArmInstr.cbnz rn lbl) ∧
      (∀ c lbl, instr' ≠ ArmInstr.bCond c lbl) := by
  intro instr' hmem
  induction entries with
  | nil => simp [entriesToSaves] at hmem
  | cons e rest ih =>
    cases e with
    | ireg r off =>
      simp only [entriesToSaves, List.mem_cons] at hmem
      rcases hmem with h | h
      · subst h
        refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> intro heq <;> exact ArmInstr.noConfusion heq
      · exact ih h
    | freg r off =>
      simp only [entriesToSaves, List.mem_cons] at hmem
      rcases hmem with h | h
      · subst h
        refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> intro heq <;> exact ArmInstr.noConfusion heq
      · exact ih h

/-- `entriesToRestores` emits only `.ldr` and `.fldr` — no branches. -/
private theorem entriesToRestores_no_branches (entries : List CallerSaveEntry) :
    ∀ instr' ∈ entriesToRestores entries,
      (∀ lbl, instr' ≠ ArmInstr.b lbl) ∧
      (∀ rn lbl, instr' ≠ ArmInstr.cbz rn lbl) ∧
      (∀ rn lbl, instr' ≠ ArmInstr.cbnz rn lbl) ∧
      (∀ c lbl, instr' ≠ ArmInstr.bCond c lbl) := by
  intro instr' hmem
  induction entries with
  | nil => simp [entriesToRestores] at hmem
  | cons e rest ih =>
    cases e with
    | ireg r off =>
      simp only [entriesToRestores, List.mem_cons] at hmem
      rcases hmem with h | h
      · subst h
        refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> intro heq <;> exact ArmInstr.noConfusion heq
      · exact ih h
    | freg r off =>
      simp only [entriesToRestores, List.mem_cons] at hmem
      rcases hmem with h | h
      · subst h
        refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> intro heq <;> exact ArmInstr.noConfusion heq
      · exact ih h

/-- A `.printCall lines` singleton is not a branch. -/
private theorem printCall_no_branches (lines : List String) :
    ∀ instr' ∈ [ArmInstr.printCall lines],
      (∀ lbl, instr' ≠ ArmInstr.b lbl) ∧
      (∀ rn lbl, instr' ≠ ArmInstr.cbz rn lbl) ∧
      (∀ rn lbl, instr' ≠ ArmInstr.cbnz rn lbl) ∧
      (∀ c lbl, instr' ≠ ArmInstr.bCond c lbl) := by
  intro instr' hmem
  simp only [List.mem_singleton] at hmem
  subst hmem
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> intro heq <;> exact ArmInstr.noConfusion heq

/-- `genHaltSaveOne` emits at most `.str` or `.fstr` — never branches. -/
private theorem genHaltSaveOne_no_branches (v : Var) (layout : VarLayout)
    (varMap : List (Var × Nat)) :
    ∀ instr' ∈ genHaltSaveOne v layout varMap,
      (∀ lbl, instr' ≠ ArmInstr.b lbl) ∧
      (∀ rn lbl, instr' ≠ ArmInstr.cbz rn lbl) ∧
      (∀ rn lbl, instr' ≠ ArmInstr.cbnz rn lbl) ∧
      (∀ c lbl, instr' ≠ ArmInstr.bCond c lbl) := by
  intro instr' hmem
  unfold genHaltSaveOne at hmem
  split at hmem
  · split at hmem
    · simp only [List.mem_singleton] at hmem
      subst hmem
      refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> intro heq <;> exact ArmInstr.noConfusion heq
    · simp at hmem
  · split at hmem
    · simp only [List.mem_singleton] at hmem
      subst hmem
      refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> intro heq <;> exact ArmInstr.noConfusion heq
    · simp at hmem
  · simp at hmem
  · simp at hmem

/-- `genHaltSave` emits only `.str` and `.fstr` — no branches. -/
private theorem genHaltSave_no_branches (observable : List Var) (layout : VarLayout)
    (varMap : List (Var × Nat)) :
    ∀ instr' ∈ genHaltSave observable layout varMap,
      (∀ lbl, instr' ≠ ArmInstr.b lbl) ∧
      (∀ rn lbl, instr' ≠ ArmInstr.cbz rn lbl) ∧
      (∀ rn lbl, instr' ≠ ArmInstr.cbnz rn lbl) ∧
      (∀ c lbl, instr' ≠ ArmInstr.bCond c lbl) := by
  intro instr' hmem
  simp only [genHaltSave, List.mem_flatMap] at hmem
  obtain ⟨v, _, hv⟩ := hmem
  exact genHaltSaveOne_no_branches v layout varMap instr' hv

/-- **Phase 6 helper: branch targets are bounded.**  For every branch
    instruction embedded in `r.bodyFlat`, its label target is ≤ `r.boundsS`.

    Proof structure (session 14):
      1. Extract `X ∈ r.bodyFlat.toList` from the branch-form hypothesis.
      2. Split `bodyFlat.toList = bodyPerPC.toList.flatMap id ++ haltSaveBlock.toList`.
      3. If X is in the flatMap prefix, find the block it lives in
         (via `List.mem_flatMap`), and therefore the TAC PC (via
         `Array.mem_iff_getElem` on `bodyPerPC.toList`).
      4. Dispatch on TAC type at that PC: print / lib-call / normal.
         Print and lib-call use spec fields + the save/restore and printCall
         `_no_branches` helpers for the wrapper pieces; the inner
         `verifiedGenInstr` output is handled via the Phase6Probes2 aggregator.
      5. If X is in the haltSaveBlock suffix, use `spec.haltSaveBlock_eq` +
         `genHaltSave_no_branches` to contradict the branch-form.

    Requires `hBranch : checkBranchTargets p.code = none` (passed in from the
    caller; derived from `verifiedGenerateAsm` success). -/
theorem bodyFlat_branch_target_bounded
    {tyCtx : TyCtx} {p : Prog} {r : VerifiedAsmResult}
    (spec : GenAsmSpec tyCtx p r)
    (hBranch : checkBranchTargets p.code = none) :
    ∀ (pc : Nat) (lbl : Nat),
      (r.bodyFlat[pc]? = some (ArmInstr.b lbl) ∨
       (∃ rn, r.bodyFlat[pc]? = some (ArmInstr.cbz rn lbl)) ∨
       (∃ rn, r.bodyFlat[pc]? = some (ArmInstr.cbnz rn lbl)) ∨
       (∃ c,  r.bodyFlat[pc]? = some (ArmInstr.bCond c lbl))) →
      lbl ≤ r.boundsS := by
  intro pc lbl hbranch
  -- Step 1: Package hbranch as ⟨X, getElem? = some X, X is a branch-form⟩.
  have ⟨X, hXAt, hXForm⟩ : ∃ X, r.bodyFlat[pc]? = some X ∧
      (X = ArmInstr.b lbl ∨
       (∃ rn, X = ArmInstr.cbz rn lbl) ∨
       (∃ rn, X = ArmInstr.cbnz rn lbl) ∨
       (∃ c,  X = ArmInstr.bCond c lbl)) := by
    rcases hbranch with h | ⟨rn, h⟩ | ⟨rn, h⟩ | ⟨c, h⟩
    · exact ⟨_, h, Or.inl rfl⟩
    · exact ⟨_, h, Or.inr <| Or.inl ⟨rn, rfl⟩⟩
    · exact ⟨_, h, Or.inr <| Or.inr <| Or.inl ⟨rn, rfl⟩⟩
    · exact ⟨_, h, Or.inr <| Or.inr <| Or.inr ⟨c, rfl⟩⟩
  -- Step 2: X is an element of bodyFlat.
  have hXMem : X ∈ r.bodyFlat := by
    rw [Array.mem_iff_getElem?]; exact ⟨pc, hXAt⟩
  have hXMemList : X ∈ r.bodyFlat.toList := Array.mem_toList_iff.mpr hXMem
  -- Step 3: Flat decomposition.
  have hFlatList : r.bodyFlat.toList =
      r.bodyPerPC.toList.flatMap id ++ r.haltSaveBlock.toList := by
    simp only [VerifiedAsmResult.bodyFlat, List.toList_toArray]
  rw [hFlatList, List.mem_append] at hXMemList
  -- Useful bounds: haltS ≤ boundsS, divS ≤ boundsS, haltFinal ≤ boundsS.
  have hHaltBound : r.haltS ≤ r.boundsS := by
    rw [spec.boundsS_eq, spec.haltFinal_eq]; omega
  have hDivBound : r.divS ≤ r.boundsS := by
    rw [spec.boundsS_eq, spec.divS_eq]; omega
  have hHaltFinalBound : r.haltFinal ≤ r.boundsS := by
    rw [spec.boundsS_eq]; omega
  -- Closer: from a non-branch witness for X, close lbl ≤ r.boundsS vacuously.
  have close_nb :
      (∀ lbl, X ≠ ArmInstr.b lbl) ∧
      (∀ rn lbl, X ≠ ArmInstr.cbz rn lbl) ∧
      (∀ rn lbl, X ≠ ArmInstr.cbnz rn lbl) ∧
      (∀ c lbl, X ≠ ArmInstr.bCond c lbl) → lbl ≤ r.boundsS := by
    intro ⟨nb, nz, nnz, nbc⟩
    rcases hXForm with h | ⟨rn, h⟩ | ⟨rn, h⟩ | ⟨c, h⟩
    · exact absurd h (nb _)
    · exact absurd h (nz rn _)
    · exact absurd h (nnz rn _)
    · exact absurd h (nbc c _)
  rcases hXMemList with hInBody | hInHalt
  · -- X in bodyPerPC prefix
    rw [List.mem_flatMap] at hInBody
    obtain ⟨block, hBlockMem, hXInBlock⟩ := hInBody
    simp only [id] at hXInBlock
    rw [Array.mem_toList_iff, Array.mem_iff_getElem] at hBlockMem
    obtain ⟨tac_pc, htac_pc_lt, hBlockEq⟩ := hBlockMem
    rw [← hBlockEq] at hXInBlock
    have htac_pc : tac_pc < p.size := spec.bodySize ▸ htac_pc_lt
    -- hPcBound for the aggregator: pcMap l ≤ boundsS for any live branch
    -- target l at p[tac_pc].
    have hPcBound : ∀ l,
        (p[tac_pc] = TAC.goto l ∨ ∃ be, p[tac_pc] = TAC.ifgoto be l) →
        r.pcMap l ≤ r.boundsS := by
      intro l hg
      have hlLt : l < p.size :=
        checkBranchTargets_to_labels_in_bounds hBranch htac_pc l hg
      have hlLe : l ≤ p.size := Nat.le_of_lt hlLt
      have h1 := pcMap_le_haltS spec l hlLe
      exact Nat.le_trans h1 hHaltBound
    -- Dispatch on TAC type at tac_pc
    by_cases hPrint : ∃ fmt vs, p[tac_pc] = TAC.print fmt vs
    · -- print: bodyPerPC[tac_pc] = saves ++ [.printCall lines] ++ restores
      obtain ⟨lines, hEq⟩ := spec.printSaveRestore tac_pc htac_pc hPrint
      rw [hEq] at hXInBlock
      rw [List.mem_append, List.mem_append] at hXInBlock
      apply close_nb
      rcases hXInBlock with (hInSaves | hInPrint) | hInRestores
      · exact entriesToSaves_no_branches _ X hInSaves
      · exact printCall_no_branches lines X hInPrint
      · exact entriesToRestores_no_branches _ X hInRestores
    · -- non-print
      have hNotPrint : ∀ fmt vs, p[tac_pc] ≠ TAC.print fmt vs := by
        intro fmt vs h; exact hPrint ⟨fmt, vs, h⟩
      by_cases hLib : isLibCallTAC p[tac_pc] = true
      · -- lib-call: bodyPerPC[tac_pc] = saves ++ baseInstrs ++ restores
        obtain ⟨baseInstrs, hGenInstr, hEq⟩ :=
          spec.callSiteSaveRestore tac_pc htac_pc hLib
        -- Derive hRC/hII from hGenInstr (verifiedGenInstr = none when either fails)
        have hRC : r.layout.regConventionSafe = true := spec.regConventionSafeBool
        have hII : r.layout.isInjective = true := spec.isInjectiveBool
        rw [hEq] at hXInBlock
        rw [List.mem_append, List.mem_append] at hXInBlock
        rcases hXInBlock with (hInSaves | hInBase) | hInRestores
        · exact close_nb (entriesToSaves_no_branches _ X hInSaves)
        · -- X ∈ baseInstrs, apply aggregator.
          have hLblBranch :
              X = ArmInstr.b lbl ∨
              (∃ rn, X = ArmInstr.cbz rn lbl) ∨
              (∃ rn, X = ArmInstr.cbnz rn lbl) ∨
              (∃ c, X = ArmInstr.bCond c lbl) := hXForm
          exact verifiedGenInstr_branch_target_bounded r.layout r.pcMap p[tac_pc]
            r.haltS r.divS r.boundsS p.arrayDecls (verifiedBoundsSafe p tac_pc)
            hGenInstr hRC hII
            hPcBound hHaltBound hDivBound X hInBase lbl hLblBranch
        · exact close_nb (entriesToRestores_no_branches _ X hInRestores)
      · -- normal case: bodyPerPC[tac_pc] = verifiedGenInstr output
        have hNotLib : isLibCallTAC p[tac_pc] = false := by
          cases h : isLibCallTAC p[tac_pc] <;> simp_all
        have hGenInstr := spec.instrGen tac_pc htac_pc hNotLib hNotPrint
        have hRC : r.layout.regConventionSafe = true := spec.regConventionSafeBool
        have hII : r.layout.isInjective = true := spec.isInjectiveBool
        have hLblBranch :
            X = ArmInstr.b lbl ∨
            (∃ rn, X = ArmInstr.cbz rn lbl) ∨
            (∃ rn, X = ArmInstr.cbnz rn lbl) ∨
            (∃ c, X = ArmInstr.bCond c lbl) := hXForm
        exact verifiedGenInstr_branch_target_bounded r.layout r.pcMap p[tac_pc]
          r.haltS r.divS r.boundsS p.arrayDecls (verifiedBoundsSafe p tac_pc)
          hGenInstr hRC hII
          hPcBound hHaltBound hDivBound X hXInBlock lbl hLblBranch
  · -- X in haltSaveBlock suffix
    rw [spec.haltSaveBlock_eq] at hInHalt
    exact close_nb (genHaltSave_no_branches _ _ _ X hInHalt)

/-- After any `ArmStep`, the new pc is either `s.pc + 1` (fall-through /
    non-branch) or a branch target `lbl`, where the instruction at `s.pc`
    is one of the branch forms with label `lbl`. -/
private theorem ArmStep_pc_analysis {prog : ArmProg} {s s' : ArmState}
    (h : ArmStep prog s s') :
    s'.pc = s.pc + 1 ∨
    ∃ lbl, s'.pc = lbl ∧
      (prog[s.pc]? = some (ArmInstr.b lbl) ∨
       (∃ rn, prog[s.pc]? = some (ArmInstr.cbz rn lbl)) ∨
       (∃ rn, prog[s.pc]? = some (ArmInstr.cbnz rn lbl)) ∨
       (∃ c, prog[s.pc]? = some (ArmInstr.bCond c lbl))) := by
  cases h with
  | cbz_taken rn lbl hi _ =>
    exact Or.inr ⟨lbl, rfl, Or.inr (Or.inl ⟨rn, hi⟩)⟩
  | cbnz_taken rn lbl hi _ =>
    exact Or.inr ⟨lbl, rfl, Or.inr (Or.inr (Or.inl ⟨rn, hi⟩))⟩
  | bCond_taken c lbl hi _ =>
    exact Or.inr ⟨lbl, rfl, Or.inr (Or.inr (Or.inr ⟨c, hi⟩))⟩
  | branch lbl hi =>
    exact Or.inr ⟨lbl, rfl, Or.inl hi⟩
  | _ => exact Or.inl rfl

/-- **Phase 6 main theorem: ARM behavior exhaustion.**  Every ARM execution
    from the pipeline's initial state lands in one of four bins: clean halt
    (`haltFinal`), div-by-zero sentinel (`divS`), bounds-error sentinel
    (`boundsS`), or divergence (`ArmDiverges`).

    Proof (classical `em` + König): dispatch the three sentinel cases via
    `by_cases`; if all three fail, build `ArmDiverges = ∀ n, ∃ s,
    ArmStepsN init s n` by induction on `n` with the invariant
    `s.pc ≤ boundsS`.  The inductive step uses `ArmStep_total_of_codeAt`
    (progress from `bodyFlat[pc]? = some _`), `bodyFlat_branch_target_bounded`
    (PC bound on branch targets), and the fall-through assumptions
    (s.pc ≠ haltFinal ∧ s.pc ≠ divS ∧ s.pc ≠ boundsS, derived from the
    negated sentinel hypotheses). -/
theorem arm_behavior_exhaustive
    (prog : Program) (htcs : prog.wellFormed = true)
    (passes : List (String × (Prog → ECertificate)))
    {r : VerifiedAsmResult}
    (hGen : verifiedGenerateAsm prog.tyCtx
      (applyPasses prog.tyCtx passes prog.compileToTAC) = .ok r) :
    (∃ s', ArmSteps r.bodyFlat (r.initArmState) s' ∧ s'.pc = r.haltFinal) ∨
    (∃ s', ArmSteps r.bodyFlat (r.initArmState) s' ∧ s'.pc = r.divS) ∨
    (∃ s', ArmSteps r.bodyFlat (r.initArmState) s' ∧ s'.pc = r.boundsS) ∨
    ArmDiverges r.bodyFlat (r.initArmState) := by
  classical
  set p := applyPasses prog.tyCtx passes prog.compileToTAC with hp_def
  -- Extract GenAsmSpec
  have spec : GenAsmSpec prog.tyCtx p r := verifiedGenerateAsm_spec hGen
  -- Extract `checkBranchTargets p.code = none` via pipeline invariant preservation
  have htc := prog.wellFormed_typeCheck htcs
  have hWT0 : checkWellTypedProg prog.tyCtx prog.compileToTAC = true :=
    checkWellTypedProg_complete (prog.compileToTAC_wellTyped htc)
  have hPrereqs0 := compileToTAC_codegenPrereqs prog htcs
  have hBranch0 := compileToTAC_checkBranchTargets prog
  have hSimple0 := compileToTAC_checkBoolExprSimpleOps prog
  obtain ⟨_, _, hBranch, _⟩ :=
    applyPasses_preserves_invariants prog.tyCtx passes prog.compileToTAC
      hWT0 hPrereqs0 hBranch0 hSimple0
  -- Shorthand
  set init := r.initArmState with hinit_def
  -- By classical excluded middle, dispatch sentinel-reach cases
  by_cases h1 : ∃ s', ArmSteps r.bodyFlat init s' ∧ s'.pc = r.haltFinal
  · exact Or.inl h1
  by_cases h2 : ∃ s', ArmSteps r.bodyFlat init s' ∧ s'.pc = r.divS
  · exact Or.inr (Or.inl h2)
  by_cases h3 : ∃ s', ArmSteps r.bodyFlat init s' ∧ s'.pc = r.boundsS
  · exact Or.inr (Or.inr (Or.inl h3))
  -- Fall-through: prove ArmDiverges
  refine Or.inr (Or.inr (Or.inr ?_))
  -- Key facts
  have hBodySize : r.bodyFlat.size = r.haltFinal := by
    simp only [VerifiedAsmResult.bodyFlat, List.size_toArray,
      List.length_append, Array.length_toList]
    rw [spec.haltFinal_eq, spec.haltS_eq]
  have hHaltBound : r.haltFinal ≤ r.boundsS := by
    rw [spec.boundsS_eq]; omega
  -- ArmDiverges: ∀ n, ∃ s, ArmStepsN bodyFlat init s n
  -- Strengthened invariant: also carry s.pc ≤ boundsS
  intro n
  suffices h : ∃ s, ArmStepsN r.bodyFlat init s n ∧ s.pc ≤ r.boundsS by
    obtain ⟨s, hs, _⟩ := h; exact ⟨s, hs⟩
  induction n with
  | zero =>
    refine ⟨init, ArmStepsN.refl_zero, ?_⟩
    show init.pc ≤ r.boundsS
    rw [hinit_def]
    show (r.initArmState).pc ≤ r.boundsS
    simp only [VerifiedAsmResult.initArmState]
    have := pcMap_le_haltS spec 0 (by simp)
    have hle : r.haltS ≤ r.boundsS := by
      rw [spec.boundsS_eq, spec.haltFinal_eq]; omega
    omega
  | succ n ih =>
    obtain ⟨s, hs_n, hPC_bound⟩ := ih
    have hArmSteps_init_s : ArmSteps r.bodyFlat init s := ArmStepsN_to_ArmSteps hs_n
    have hNeHalt : s.pc ≠ r.haltFinal := fun h => h1 ⟨s, hArmSteps_init_s, h⟩
    have hNeDiv : s.pc ≠ r.divS := fun h => h2 ⟨s, hArmSteps_init_s, h⟩
    have hNeBounds : s.pc ≠ r.boundsS := fun h => h3 ⟨s, hArmSteps_init_s, h⟩
    -- s.pc ≤ boundsS, ≠ {haltFinal, haltFinal+1, haltFinal+2} → s.pc < haltFinal
    have hPcLtHalt : s.pc < r.haltFinal := by
      rw [spec.divS_eq] at hNeDiv
      rw [spec.boundsS_eq] at hNeBounds
      rw [spec.boundsS_eq] at hPC_bound
      omega
    have hPcLtBody : s.pc < r.bodyFlat.size := hBodySize ▸ hPcLtHalt
    -- Get the instruction at s.pc
    obtain ⟨i, hi⟩ : ∃ i, r.bodyFlat[s.pc]? = some i := by
      rcases hlookup : r.bodyFlat[s.pc]? with _ | i
      · rw [Array.getElem?_eq_none_iff] at hlookup; omega
      · exact ⟨i, rfl⟩
    obtain ⟨s', hStep⟩ := ArmStep_total_of_codeAt hi
    have hs_n1 : ArmStepsN r.bodyFlat init s' (n + 1) := ArmStepsN_extend hs_n hStep
    refine ⟨s', hs_n1, ?_⟩
    -- Case on ArmStep_pc_analysis: either s'.pc = s.pc + 1 or s'.pc is a branch target
    rcases ArmStep_pc_analysis hStep with hFall | ⟨lbl, hPc_eq, hBrForm⟩
    · -- Fall-through: s'.pc = s.pc + 1 ≤ haltFinal ≤ boundsS
      rw [hFall]; omega
    · -- Branch: s'.pc = lbl, use bodyFlat_branch_target_bounded
      rw [hPc_eq]
      exact bodyFlat_branch_target_bounded spec hBranch s.pc lbl hBrForm

/-- **Source-side exhaustion**, derived from `arm_behavior_exhaustive` plus the
    four backward theorems.  For any well-formed source program that compiles
    successfully, `prog.run` lands in one of four bins: clean halt, div-by-zero,
    out-of-bounds, or fuel-exhausted at every fuel.  This is the source dual
    of `arm_behavior_exhaustive`. -/
theorem program_run_exhaustive
    (prog : Program) (htcs : prog.wellFormed = true)
    (passes : List (String × (Prog → ECertificate)))
    {r : VerifiedAsmResult}
    (hGen : verifiedGenerateAsm prog.tyCtx
      (applyPasses prog.tyCtx passes prog.compileToTAC) = .ok r) :
    (∃ fuel σ_src am_src, prog.run fuel = .halts σ_src am_src) ∨
    (∃ fuel, prog.run fuel = .divByZero) ∨
    (∃ fuel, prog.run fuel = .outOfBounds) ∨
    (∀ fuel, prog.run fuel = .outOfFuel) := by
  rcases arm_behavior_exhaustive prog htcs passes hGen with
    ⟨s, hArm, hPC⟩ | ⟨s, hArm, hPC⟩ | ⟨s, hArm, hPC⟩ | hDiv
  · obtain ⟨fuel, σ_src, am_src, hrun, _⟩ :=
      arm_halts_implies_program_halts prog htcs passes hGen hArm hPC
    exact Or.inl ⟨fuel, σ_src, am_src, hrun⟩
  · obtain ⟨fuel, hrun⟩ :=
      arm_div_implies_program_unsafe_div prog htcs passes hGen hArm hPC
    exact Or.inr (Or.inl ⟨fuel, hrun⟩)
  · obtain ⟨fuel, hrun⟩ :=
      arm_bounds_implies_program_unsafe_bounds prog htcs passes hGen hArm hPC
    exact Or.inr (Or.inr (Or.inl ⟨fuel, hrun⟩))
  · exact Or.inr (Or.inr (Or.inr
      (arm_diverges_implies_program_diverges prog htcs passes hGen hDiv)))

/-- **AST-level exhaustion: every program's `run` lands in one of four bins.**

    The disjunction follows by pigeonhole on `RunResult`'s four constructors:
    if no fuel produces halt/div/bounds, every fuel must produce `outOfFuel`.
    No compilation, type-checking, or even well-formedness needed — the
    statement is purely about the total `run` function.  Compare to
    `program_run_exhaustive` which uses well-formedness + a successful
    codegen to route through ARM exhaustion; this version skips all that. -/
theorem program_run_exhaustive_pure (prog : Program) :
    (∃ fuel σ_src am_src, prog.run fuel = .halts σ_src am_src) ∨
    (∃ fuel, prog.run fuel = .divByZero) ∨
    (∃ fuel, prog.run fuel = .outOfBounds) ∨
    (∀ fuel, prog.run fuel = .outOfFuel) := by
  classical
  by_cases h1 : ∃ fuel σ am, prog.run fuel = .halts σ am
  · exact Or.inl h1
  by_cases h2 : ∃ fuel, prog.run fuel = .divByZero
  · exact Or.inr (Or.inl h2)
  by_cases h3 : ∃ fuel, prog.run fuel = .outOfBounds
  · exact Or.inr (Or.inr (Or.inl h3))
  refine Or.inr (Or.inr (Or.inr ?_))
  intro fuel
  match hr : prog.run fuel with
  | .halts σ am => exact absurd ⟨fuel, σ, am, hr⟩ h1
  | .divByZero => exact absurd ⟨fuel, hr⟩ h2
  | .outOfBounds => exact absurd ⟨fuel, hr⟩ h3
  | .outOfFuel => rfl

/-- Wrapper for the well-formed case — included for parallelism with the
    other `_of_wellFormed` theorems, even though the hypothesis is unused. -/
theorem program_run_exhaustive_of_wellFormed
    (prog : Program) (_htcs : prog.wellFormed = true) :
    (∃ fuel σ_src am_src, prog.run fuel = .halts σ_src am_src) ∨
    (∃ fuel, prog.run fuel = .divByZero) ∨
    (∃ fuel, prog.run fuel = .outOfBounds) ∨
    (∀ fuel, prog.run fuel = .outOfFuel) :=
  program_run_exhaustive_pure prog

/-- **Driver-to-theorem bridge: ARM behavior exhaustion.**

    Driver wrapper for `arm_behavior_exhaustive`.  If the driver returns
    `.ok r`, the compiled ARM program either reaches `haltFinal`, `divS`,
    `boundsS`, or diverges.  Same four-case split, lifted from
    `verifiedGenerateAsm = .ok r` to `compileProgramAst prog noOpt = .ok r`. -/
theorem compileProgramAst_arm_behavior_exhaustive
    {prog : Program} {noOpt : Bool} {r : VerifiedAsmResult}
    (hDriver : compileProgramAst prog noOpt = .ok r) :
    (∃ s', ArmSteps r.bodyFlat (r.initArmState) s' ∧ s'.pc = r.haltFinal) ∨
    (∃ s', ArmSteps r.bodyFlat (r.initArmState) s' ∧ s'.pc = r.divS) ∨
    (∃ s', ArmSteps r.bodyFlat (r.initArmState) s' ∧ s'.pc = r.boundsS) ∨
    ArmDiverges r.bodyFlat (r.initArmState) := by
  unfold compileProgramAst at hDriver
  split at hDriver
  · rename_i hwf
    cases noOpt with
    | true =>
      simp at hDriver
      exact arm_behavior_exhaustive prog hwf
        ([] : List (String × (Prog → ECertificate))) hDriver
    | false =>
      simp at hDriver
      obtain ⟨allPasses, heq⟩ :=
        applyStandardPipelineFixpoint_eq_applyPasses prog.tyCtx prog.compileToTAC
      rw [heq] at hDriver
      exact arm_behavior_exhaustive prog hwf allPasses hDriver
  · simp at hDriver

/-- **Driver-to-theorem bridge: source-run exhaustion.**

    Driver wrapper for `program_run_exhaustive`.  If the driver returns
    `.ok r`, then for some fuel the source `prog.run` lands in exactly one
    of: clean halt, div-by-zero, out-of-bounds, or out-of-fuel at every
    fuel.  Source-side dual of `compileProgramAst_arm_behavior_exhaustive`. -/
theorem compileProgramAst_program_run_exhaustive
    {prog : Program} {noOpt : Bool} {r : VerifiedAsmResult}
    (hDriver : compileProgramAst prog noOpt = .ok r) :
    (∃ fuel σ_src am_src, prog.run fuel = .halts σ_src am_src) ∨
    (∃ fuel, prog.run fuel = .divByZero) ∨
    (∃ fuel, prog.run fuel = .outOfBounds) ∨
    (∀ fuel, prog.run fuel = .outOfFuel) := by
  unfold compileProgramAst at hDriver
  split at hDriver
  · rename_i hwf
    cases noOpt with
    | true =>
      simp at hDriver
      exact program_run_exhaustive prog hwf
        ([] : List (String × (Prog → ECertificate))) hDriver
    | false =>
      simp at hDriver
      obtain ⟨allPasses, heq⟩ :=
        applyStandardPipelineFixpoint_eq_applyPasses prog.tyCtx prog.compileToTAC
      rw [heq] at hDriver
      exact program_run_exhaustive prog hwf allPasses hDriver
  · simp at hDriver

end Phase6Main
