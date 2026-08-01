-- Copyright (c) 2026 Martin Rinard
import CredibleCompilation.Semantics

/-!
# Propositional PCertificate Checker for Credible Compilation

A Prop-based certificate checker that verifies: every behavior of a transformed
program has a corresponding behavior in the original program.

Based on the credible compilation framework (Rinard, MIT-LCS-TR-776).
-/

-- ============================================================
-- § 1. Invariants (Floyd-Hoare style properties)
-- ============================================================

/-- A predicate on stores and array memory, attached to a program point. -/
def PInvariant := Store → ArrayMem → Prop

/-- An invariant map assigns an invariant to each label in a program. -/
def PInvariantMap := Label → PInvariant

def PInvariantMap.locally_preserved (inv : PInvariantMap) (p : Prog)
    (pc : Label) (σ : Store) : Prop :=
  ∀ am, inv pc σ am →
  ∀ pc' σ' am', (p ⊩ Cfg.run pc σ am ⟶ Cfg.run pc' σ' am') → inv pc' σ' am'

def PInvariantMap.preserved (inv : PInvariantMap) (p : Prog) : Prop :=
  ∀ pc σ, inv.locally_preserved p pc σ

def PStoreRel := Store → ArrayMem → Store → ArrayMem → Prop

structure PTransCorr where
  origLabels    : List Label
  storeRel      : PStoreRel
  storeRel_next : PStoreRel

structure PInstrCert where
  pc_orig     : Label
  storeRel    : PStoreRel
  transitions : List PTransCorr

structure PHaltCert where
  pc_orig  : Label
  storeRel : PStoreRel

def PTransMeasure := Label → Store → Nat

structure PCertificate where
  orig        : Prog
  trans       : Prog
  tyCtx       : TyCtx
  inv_orig    : PInvariantMap
  inv_trans   : PInvariantMap
  instrCerts  : Label → PInstrCert
  haltCerts   : Label → PHaltCert
  measure     : PTransMeasure

abbrev PCertificate.observable (cert : PCertificate) : List Var := cert.orig.observable

-- ============================================================
-- § 6. PCertificate checking conditions
-- ============================================================

def checkInvariantsPreservedProp (cert : PCertificate) : Prop :=
  cert.inv_orig.preserved cert.orig ∧ cert.inv_trans.preserved cert.trans

def checkTransitionRelProp (Γ : TyCtx) (p_orig p_trans : Prog)
    (inv_orig : PInvariantMap) (inv_trans : PInvariantMap)
    (pc_t pc_t' : Label) (pc_o pc_o' : Label) (tc : PTransCorr) : Prop :=
  ∀ σ_t σ_t' σ_o am_t am_t' am_o,
    inv_trans pc_t σ_t am_t → inv_orig pc_o σ_o am_o → tc.storeRel σ_o am_o σ_t am_t →
    am_t = am_o → TypedStore Γ σ_o →
    (p_trans ⊩ Cfg.run pc_t σ_t am_t ⟶ Cfg.run pc_t' σ_t' am_t') →
    ∃ σ_o' am_o', (p_orig ⊩ Cfg.run pc_o σ_o am_o ⟶* Cfg.run pc_o' σ_o' am_o') ∧
      tc.storeRel_next σ_o' am_o' σ_t' am_t' ∧ am_t' = am_o'

def checkAllTransitionsProp (Γ : TyCtx) (cert : PCertificate) : Prop :=
  ∀ pc_t : Label, ∀ σ_t σ_t' : Store, ∀ pc_t' : Label, ∀ am_t am_t' : ArrayMem,
    cert.inv_trans pc_t σ_t am_t →
    (cert.trans ⊩ Cfg.run pc_t σ_t am_t ⟶ Cfg.run pc_t' σ_t' am_t') →
    let ic := cert.instrCerts pc_t; let ic' := cert.instrCerts pc_t'
    ∃ tc ∈ ic.transitions, tc.storeRel = ic.storeRel ∧ tc.storeRel_next = ic'.storeRel ∧
      checkTransitionRelProp Γ cert.orig cert.trans cert.inv_orig cert.inv_trans pc_t pc_t' ic.pc_orig ic'.pc_orig tc

def checkHaltCorrespondenceProp (cert : PCertificate) : Prop :=
  ∀ pc_t : Label, cert.trans[pc_t]? = some .halt →
    let ic := cert.instrCerts pc_t; cert.orig[ic.pc_orig]? = some .halt

def checkHaltObservableProp (cert : PCertificate) : Prop :=
  ∀ pc_t : Label, ∀ σ_t σ_o : Store, ∀ am_t am_o : ArrayMem, cert.trans[pc_t]? = some .halt →
    let ic := cert.instrCerts pc_t; ic.storeRel σ_o am_o σ_t am_t → ∀ v ∈ cert.observable, σ_t v = σ_o v

def checkErrorPreservationProp (cert : PCertificate) : Prop :=
  ∀ (pc_t : Label) (σ_t σ_o : Store) (am_t : ArrayMem) (am_o : ArrayMem),
    pc_t < cert.trans.size → (cert.instrCerts pc_t).storeRel σ_o am_o σ_t am_t →
    cert.inv_trans pc_t σ_t am_t → cert.inv_orig (cert.instrCerts pc_t).pc_orig σ_o am_o →
    TypedStore cert.tyCtx σ_o →
    ((cert.trans ⊩ Cfg.run pc_t σ_t am_t ⟶ Cfg.errorDiv σ_t am_t) →
      ∃ σ_o' am_o',
        cert.orig ⊩ Cfg.run (cert.instrCerts pc_t).pc_orig σ_o am_o ⟶* Cfg.errorDiv σ_o' am_o') ∧
    ((cert.trans ⊩ Cfg.run pc_t σ_t am_t ⟶ Cfg.errorBounds σ_t am_t) →
      ∃ σ_o' am_o',
        cert.orig ⊩ Cfg.run (cert.instrCerts pc_t).pc_orig σ_o am_o ⟶* Cfg.errorBounds σ_o' am_o')

def checkStartCorrespondenceProp (cert : PCertificate) : Prop :=
  (cert.instrCerts 0).pc_orig = 0 ∧ ∀ σ am, (cert.instrCerts 0).storeRel σ am σ am

def checkInvariantsAtStartProp (cert : PCertificate) : Prop :=
  (∀ σ am, cert.inv_trans 0 σ am) ∧ (∀ σ am, cert.inv_orig 0 σ am)

def IsInfiniteExec (p : Prog) (f : Nat → Cfg) : Prop :=
  (∃ σ₀ am₀, f 0 = Cfg.run 0 σ₀ am₀) ∧ ∀ n, p ⊩ f n ⟶ f (n + 1)

def checkNonterminationProp (cert : PCertificate) : Prop :=
  ∀ (pc_t pc_t' : Label) (σ_t σ_t' σ_o : Store) (am_t am_o : ArrayMem),
    cert.inv_trans pc_t σ_t am_t →
    cert.inv_orig (cert.instrCerts pc_t).pc_orig σ_o am_o →
    (cert.instrCerts pc_t).storeRel σ_o am_o σ_t am_t →
    (∃ c', (cert.trans ⊩ Cfg.run pc_t σ_t am_t ⟶ c') ∧ ∃ am_t', c' = Cfg.run pc_t' σ_t' am_t') →
    (cert.instrCerts pc_t).pc_orig = (cert.instrCerts pc_t').pc_orig →
    cert.measure pc_t' σ_t' < cert.measure pc_t σ_t

structure PCertificateValid (cert : PCertificate) : Prop where
  well_typed_orig  : WellTypedProg cert.tyCtx cert.orig
  well_typed_trans : WellTypedProg cert.tyCtx cert.trans
  same_observable  : cert.orig.observable = cert.trans.observable
  start_corr       : checkStartCorrespondenceProp cert
  start_inv        : checkInvariantsAtStartProp cert
  inv_preserved    : checkInvariantsPreservedProp cert
  transitions      : checkAllTransitionsProp cert.tyCtx cert
  halt_corr        : checkHaltCorrespondenceProp cert
  halt_obs         : checkHaltObservableProp cert
  nonterm          : checkNonterminationProp cert
  error_pres       : checkErrorPreservationProp cert
  step_closed      : StepClosedInBounds cert.trans

-- ============================================================
-- § 9. Soundness: simulation relation
-- ============================================================

def PSimRel (cert : PCertificate) (pc_t : Label) (σ_t : Store) (am_t : ArrayMem)
    (pc_o : Label) (σ_o : Store) (am_o : ArrayMem) : Prop :=
  let ic := cert.instrCerts pc_t
  ic.pc_orig = pc_o ∧ ic.storeRel σ_o am_o σ_t am_t ∧ am_t = am_o ∧
  cert.inv_trans pc_t σ_t am_t ∧ cert.inv_orig pc_o σ_o am_o ∧ TypedStore cert.tyCtx σ_o

theorem inv_preserved_steps {inv : PInvariantMap} {p : Prog}
    (hpres : inv.preserved p) {pc pc' : Label} {σ σ' : Store} {am am' : ArrayMem}
    (hsteps : p ⊩ Cfg.run pc σ am ⟶* Cfg.run pc' σ' am') (hinv : inv pc σ am) :
    inv pc' σ' am' := by
  suffices ∀ c c', Steps p c c' →
      ∀ pc σ am, c = Cfg.run pc σ am → inv pc σ am →
      ∀ pc' σ' am', c' = Cfg.run pc' σ' am' → inv pc' σ' am' from
    this _ _ hsteps pc σ am rfl hinv pc' σ' am' rfl
  intro c c' hsteps
  induction hsteps with
  | refl => intro pc σ am hc hinv pc' σ' am' hc'; rw [hc] at hc'; cases hc'; exact hinv
  | step hstep rest ih =>
    intro pc σ am hc hinv pc' σ' am' hc'; subst hc
    cases hstep with
    | halt h => cases rest with
      | refl => exact absurd hc' Cfg.noConfusion
      | step s _ => exact absurd s Step.no_step_from_halt
    | binop_divByZero h _ _ _ => cases rest with
      | refl => exact absurd hc' Cfg.noConfusion
      | step s _ => exact absurd s Step.no_step_from_errorDiv
    | binop_typeError h _ | arrLoad_typeError h _ | arrStore_typeError h _
    | fbinop_typeError h _ | intToFloat_typeError h _ | floatToInt_typeError h _
    | floatUnary_typeError h _ | fternop_typeError h _ => cases rest with
      | refl => exact absurd hc' Cfg.noConfusion
      | step s _ => exact absurd s Step.no_step_from_typeError
    | const h => exact ih _ _ _ rfl (hpres _ _ am hinv _ _ am (Step.const h)) _ _ _ hc'
    | copy h => exact ih _ _ _ rfl (hpres _ _ am hinv _ _ am (Step.copy h)) _ _ _ hc'
    | binop h hy hz hs => exact ih _ _ _ rfl (hpres _ _ am hinv _ _ am (Step.binop h hy hz hs)) _ _ _ hc'
    | boolop h => exact ih _ _ _ rfl (hpres _ _ am hinv _ _ am (Step.boolop h)) _ _ _ hc'
    | goto h => exact ih _ _ _ rfl (hpres _ _ am hinv _ _ am (Step.goto h)) _ _ _ hc'
    | iftrue h hne => exact ih _ _ _ rfl (hpres _ _ am hinv _ _ am (Step.iftrue h hne)) _ _ _ hc'
    | iffall h heq => exact ih _ _ _ rfl (hpres _ _ am hinv _ _ am (Step.iffall h heq)) _ _ _ hc'
    | arrLoad h hidx hb => exact ih _ _ _ rfl (hpres _ _ am hinv _ _ am (Step.arrLoad h hidx hb)) _ _ _ hc'
    | arrStore h hidx hv hb => exact ih _ _ _ rfl (hpres _ _ am hinv _ _ _ (Step.arrStore h hidx hv hb)) _ _ _ hc'
    | fbinop h hy hz => exact ih _ _ _ rfl (hpres _ _ am hinv _ _ am (Step.fbinop h hy hz)) _ _ _ hc'
    | fternop h ha hb hc => exact ih _ _ _ rfl (hpres _ _ am hinv _ _ am (Step.fternop h ha hb hc)) _ _ _ hc'
    | intToFloat h hy => exact ih _ _ _ rfl (hpres _ _ am hinv _ _ am (Step.intToFloat h hy)) _ _ _ hc'
    | floatToInt h hy => exact ih _ _ _ rfl (hpres _ _ am hinv _ _ am (Step.floatToInt h hy)) _ _ _ hc'
    | floatUnary h hy => exact ih _ _ _ rfl (hpres _ _ am hinv _ _ am (Step.floatUnary h hy)) _ _ _ hc'
    | print h => exact ih _ _ _ rfl (hpres _ _ am hinv _ _ am (Step.print h)) _ _ _ hc'
    | printInt h => exact ih _ _ _ rfl (hpres _ _ am hinv _ _ am (Step.printInt h)) _ _ _ hc'
    | printBool h => exact ih _ _ _ rfl (hpres _ _ am hinv _ _ am (Step.printBool h)) _ _ _ hc'
    | printFloat h => exact ih _ _ _ rfl (hpres _ _ am hinv _ _ am (Step.printFloat h)) _ _ _ hc'
    | printString h => exact ih _ _ _ rfl (hpres _ _ am hinv _ _ am (Step.printString h)) _ _ _ hc'
    | arrLoad_boundsError h _ _ => cases rest with
      | refl => exact absurd hc' Cfg.noConfusion
      | step s _ => exact absurd s Step.no_step_from_errorBounds
    | arrStore_boundsError h _ _ _ => cases rest with
      | refl => exact absurd hc' Cfg.noConfusion
      | step s _ => exact absurd s Step.no_step_from_errorBounds

theorem bound_of_getElem? {a : Array α} {i : Nat} {v : α}
    (h : a[i]? = some v) : i < a.size := by
  rw [getElem?_eq_some_iff] at h; exact h.1

theorem type_preservation_steps {Γ : TyCtx} {p : Prog} (hwtp : WellTypedProg Γ p)
    {pc pc' : Label} {σ σ' : Store} {am am' : ArrayMem}
    (hsteps : p ⊩ Cfg.run pc σ am ⟶* Cfg.run pc' σ' am') (hts : TypedStore Γ σ) :
    TypedStore Γ σ' := by
  suffices ∀ c c', Steps p c c' →
      ∀ pc σ am, c = Cfg.run pc σ am → TypedStore Γ σ →
      ∀ pc' σ' am', c' = Cfg.run pc' σ' am' → TypedStore Γ σ' from
    this _ _ hsteps pc σ am rfl hts pc' σ' am' rfl
  intro c c' hsteps
  induction hsteps with
  | refl => intro pc σ am hc hts pc' σ' am' hc'; rw [hc] at hc'; cases hc'; exact hts
  | step hstep rest ih =>
    intro pc σ am hc hts pc' σ' am' hc'; subst hc
    cases hstep with
    | halt h => cases rest with
      | refl => exact absurd hc' Cfg.noConfusion
      | step s _ => exact absurd s Step.no_step_from_halt
    | binop_divByZero h _ _ _ => cases rest with
      | refl => exact absurd hc' Cfg.noConfusion
      | step s _ => exact absurd s Step.no_step_from_errorDiv
    | binop_typeError h _ | arrLoad_typeError h _ | arrStore_typeError h _
    | fbinop_typeError h _ | intToFloat_typeError h _ | floatToInt_typeError h _
    | floatUnary_typeError h _ | fternop_typeError h _ => cases rest with
      | refl => exact absurd hc' Cfg.noConfusion
      | step s _ => exact absurd s Step.no_step_from_typeError
    | const h => exact ih _ _ _ rfl (type_preservation hwtp hts (bound_of_getElem? h) (Step.const (am := am) h)) _ _ _ hc'
    | copy h => exact ih _ _ _ rfl (type_preservation hwtp hts (bound_of_getElem? h) (Step.copy (am := am) h)) _ _ _ hc'
    | binop h hy hz hs => exact ih _ _ _ rfl (type_preservation hwtp hts (bound_of_getElem? h) (Step.binop (am := am) h hy hz hs)) _ _ _ hc'
    | boolop h => exact ih _ _ _ rfl (type_preservation hwtp hts (bound_of_getElem? h) (Step.boolop (am := am) h)) _ _ _ hc'
    | goto h => exact ih _ _ _ rfl (type_preservation hwtp hts (bound_of_getElem? h) (Step.goto (am := am) h)) _ _ _ hc'
    | iftrue h hne => exact ih _ _ _ rfl (type_preservation hwtp hts (bound_of_getElem? h) (Step.iftrue (am := am) h hne)) _ _ _ hc'
    | iffall h heq => exact ih _ _ _ rfl (type_preservation hwtp hts (bound_of_getElem? h) (Step.iffall (am := am) h heq)) _ _ _ hc'
    | arrLoad h hidx hb => exact ih _ _ _ rfl (type_preservation hwtp hts (bound_of_getElem? h) (Step.arrLoad (am := am) h hidx hb)) _ _ _ hc'
    | arrStore h hidx hv hb => exact ih _ _ _ rfl (type_preservation hwtp hts (bound_of_getElem? h) (Step.arrStore (am := am) h hidx hv hb)) _ _ _ hc'
    | fbinop h hy hz => exact ih _ _ _ rfl (type_preservation hwtp hts (bound_of_getElem? h) (Step.fbinop (am := am) h hy hz)) _ _ _ hc'
    | fternop h ha hb hc => exact ih _ _ _ rfl (type_preservation hwtp hts (bound_of_getElem? h) (Step.fternop (am := am) h ha hb hc)) _ _ _ hc'
    | intToFloat h hy => exact ih _ _ _ rfl (type_preservation hwtp hts (bound_of_getElem? h) (Step.intToFloat (am := am) h hy)) _ _ _ hc'
    | floatToInt h hy => exact ih _ _ _ rfl (type_preservation hwtp hts (bound_of_getElem? h) (Step.floatToInt (am := am) h hy)) _ _ _ hc'
    | floatUnary h hy => exact ih _ _ _ rfl (type_preservation hwtp hts (bound_of_getElem? h) (Step.floatUnary (am := am) h hy)) _ _ _ hc'
    | print h => exact ih _ _ _ rfl (type_preservation hwtp hts (bound_of_getElem? h) (Step.print (am := am) h)) _ _ _ hc'
    | printInt h => exact ih _ _ _ rfl (type_preservation hwtp hts (bound_of_getElem? h) (Step.printInt (am := am) h)) _ _ _ hc'
    | printBool h => exact ih _ _ _ rfl (type_preservation hwtp hts (bound_of_getElem? h) (Step.printBool (am := am) h)) _ _ _ hc'
    | printFloat h => exact ih _ _ _ rfl (type_preservation hwtp hts (bound_of_getElem? h) (Step.printFloat (am := am) h)) _ _ _ hc'
    | printString h => exact ih _ _ _ rfl (type_preservation hwtp hts (bound_of_getElem? h) (Step.printString (am := am) h)) _ _ _ hc'
    | arrLoad_boundsError h _ _ => cases rest with
      | refl => exact absurd hc' Cfg.noConfusion
      | step s _ => exact absurd s Step.no_step_from_errorBounds
    | arrStore_boundsError h _ _ _ => cases rest with
      | refl => exact absurd hc' Cfg.noConfusion
      | step s _ => exact absurd s Step.no_step_from_errorBounds

theorem step_sim {cert : PCertificate} (hvalid : PCertificateValid cert)
    {pc_t : Label} {σ_t σ_t' : Store} {am_t am_t' : ArrayMem}
    {pc_o : Label} {σ_o : Store} {pc_t' : Label} (am_o : ArrayMem)
    (hsim : PSimRel cert pc_t σ_t am_t pc_o σ_o am_o)
    (hstep : cert.trans ⊩ Cfg.run pc_t σ_t am_t ⟶ Cfg.run pc_t' σ_t' am_t') :
    ∃ pc_o' σ_o' am_o',
      (cert.orig ⊩ Cfg.run pc_o σ_o am_o ⟶* Cfg.run pc_o' σ_o' am_o') ∧
      PSimRel cert pc_t' σ_t' am_t' pc_o' σ_o' am_o' := by
  obtain ⟨hpc_orig, hrel_cons, ham_eq, hinv_t, hinv_o, hts_o⟩ := hsim
  have hall := hvalid.transitions pc_t σ_t σ_t' pc_t' am_t am_t' hinv_t hstep
  simp only at hall
  obtain ⟨tc, _, hrel1, hrel2, htrans⟩ := hall
  have hrel_tc : tc.storeRel σ_o am_o σ_t am_t := hrel1 ▸ hrel_cons
  subst hpc_orig
  obtain ⟨σ_o', am_o', horig_steps, hrel_next, ham_eq'⟩ :=
    htrans σ_t σ_t' σ_o am_t am_t' am_o hinv_t hinv_o hrel_tc ham_eq hts_o hstep
  refine ⟨(cert.instrCerts pc_t').pc_orig, σ_o', am_o', horig_steps, ?_⟩
  exact ⟨rfl, hrel2 ▸ hrel_next, ham_eq',
         hvalid.inv_preserved.2 pc_t σ_t am_t hinv_t pc_t' σ_t' am_t' hstep,
         inv_preserved_steps hvalid.inv_preserved.1 horig_steps hinv_o,
         type_preservation_steps hvalid.well_typed_orig horig_steps hts_o⟩

private theorem steps_to_halt_decompose {p : Prog} {pc₀ : Nat} {σ₀ : Store} {am₀ : ArrayMem}
    {σ_h : Store} {am_h : ArrayMem}
    (hsteps : p ⊩ Cfg.run pc₀ σ₀ am₀ ⟶* Cfg.halt σ_h am_h) :
    ∃ pc σ am, (p ⊩ Cfg.run pc₀ σ₀ am₀ ⟶* Cfg.run pc σ am) ∧
      p[pc]? = some .halt ∧ σ = σ_h ∧ am = am_h := by
  suffices h : ∀ c c', Steps p c c' →
      ∀ (pc₀ : Nat) (σ₀ : Store) (am₀ : ArrayMem), c = Cfg.run pc₀ σ₀ am₀ →
      ∀ (σ_h : Store) (am_h : ArrayMem), c' = Cfg.halt σ_h am_h →
      ∃ pc σ am, (p ⊩ Cfg.run pc₀ σ₀ am₀ ⟶* Cfg.run pc σ am) ∧
        p[pc]? = some .halt ∧ σ = σ_h ∧ am = am_h from
    h _ _ hsteps pc₀ σ₀ am₀ rfl σ_h am_h rfl
  intro c c' hsteps
  induction hsteps with
  | refl => intro pc₀ σ₀ am₀ hc σ_h am_h hc'; rw [hc] at hc'; exact absurd hc' Cfg.noConfusion
  | step hstep rest ih =>
    intro pc₀ σ₀ am₀ hc σ_h am_h hc'; subst hc
    cases hstep with
    | halt h =>
      cases rest with
      | refl => cases hc'; exact ⟨pc₀, σ₀, am₀, Steps.refl, h, rfl, rfl⟩
      | step s _ => exact absurd s Step.no_step_from_halt
    | binop_divByZero h _ _ _ => cases rest with
      | refl => exact absurd hc' Cfg.noConfusion
      | step s _ => exact absurd s Step.no_step_from_errorDiv
    | binop_typeError h _ | arrLoad_typeError h _ | arrStore_typeError h _
    | fbinop_typeError h _ | intToFloat_typeError h _ | floatToInt_typeError h _
    | floatUnary_typeError h _ | fternop_typeError h _ => cases rest with
      | refl => exact absurd hc' Cfg.noConfusion
      | step s _ => exact absurd s Step.no_step_from_typeError
    | const h =>
      obtain ⟨pc, σ, am, hpre, hhalt, heq_σ, heq_am⟩ := ih _ _ _ rfl _ _ hc'
      exact ⟨pc, σ, am, Steps.step (Step.const (σ := σ₀) (am := am₀) h) hpre, hhalt, heq_σ, heq_am⟩
    | copy h =>
      obtain ⟨pc, σ, am, hpre, hhalt, heq_σ, heq_am⟩ := ih _ _ _ rfl _ _ hc'
      exact ⟨pc, σ, am, Steps.step (Step.copy (σ := σ₀) (am := am₀) h) hpre, hhalt, heq_σ, heq_am⟩
    | binop h hy hz hs =>
      obtain ⟨pc, σ, am, hpre, hhalt, heq_σ, heq_am⟩ := ih _ _ _ rfl _ _ hc'
      exact ⟨pc, σ, am, Steps.step (Step.binop (am := am₀) h hy hz hs) hpre, hhalt, heq_σ, heq_am⟩
    | boolop h =>
      obtain ⟨pc, σ, am, hpre, hhalt, heq_σ, heq_am⟩ := ih _ _ _ rfl _ _ hc'
      exact ⟨pc, σ, am, Steps.step (Step.boolop (σ := σ₀) (am := am₀) h) hpre, hhalt, heq_σ, heq_am⟩
    | goto h =>
      obtain ⟨pc, σ, am, hpre, hhalt, heq_σ, heq_am⟩ := ih _ _ _ rfl _ _ hc'
      exact ⟨pc, σ, am, Steps.step (Step.goto (σ := σ₀) (am := am₀) h) hpre, hhalt, heq_σ, heq_am⟩
    | iftrue h hne =>
      obtain ⟨pc, σ, am, hpre, hhalt, heq_σ, heq_am⟩ := ih _ _ _ rfl _ _ hc'
      exact ⟨pc, σ, am, Steps.step (Step.iftrue (am := am₀) h hne) hpre, hhalt, heq_σ, heq_am⟩
    | iffall h heq' =>
      obtain ⟨pc, σ, am, hpre, hhalt, heq_σ, heq_am⟩ := ih _ _ _ rfl _ _ hc'
      exact ⟨pc, σ, am, Steps.step (Step.iffall (am := am₀) h heq') hpre, hhalt, heq_σ, heq_am⟩
    | arrLoad h hidx hb =>
      obtain ⟨pc, σ, am, hpre, hhalt, heq_σ, heq_am⟩ := ih _ _ _ rfl _ _ hc'
      exact ⟨pc, σ, am, Steps.step (Step.arrLoad (am := am₀) h hidx hb) hpre, hhalt, heq_σ, heq_am⟩
    | arrStore h hidx hv hb =>
      obtain ⟨pc, σ, am, hpre, hhalt, heq_σ, heq_am⟩ := ih _ _ _ rfl _ _ hc'
      exact ⟨pc, σ, am, Steps.step (Step.arrStore (am := am₀) h hidx hv hb) hpre, hhalt, heq_σ, heq_am⟩
    | fbinop h hy hz =>
      obtain ⟨pc, σ, am, hpre, hhalt, heq_σ, heq_am⟩ := ih _ _ _ rfl _ _ hc'
      exact ⟨pc, σ, am, Steps.step (Step.fbinop (am := am₀) h hy hz) hpre, hhalt, heq_σ, heq_am⟩
    | intToFloat h hy =>
      obtain ⟨pc, σ, am, hpre, hhalt, heq_σ, heq_am⟩ := ih _ _ _ rfl _ _ hc'
      exact ⟨pc, σ, am, Steps.step (Step.intToFloat (am := am₀) h hy) hpre, hhalt, heq_σ, heq_am⟩
    | floatToInt h hy =>
      obtain ⟨pc, σ, am, hpre, hhalt, heq_σ, heq_am⟩ := ih _ _ _ rfl _ _ hc'
      exact ⟨pc, σ, am, Steps.step (Step.floatToInt (am := am₀) h hy) hpre, hhalt, heq_σ, heq_am⟩
    | floatUnary h hy =>
      obtain ⟨pc, σ, am, hpre, hhalt, heq_σ, heq_am⟩ := ih _ _ _ rfl _ _ hc'
      exact ⟨pc, σ, am, Steps.step (Step.floatUnary (am := am₀) h hy) hpre, hhalt, heq_σ, heq_am⟩
    | fternop h ha hb hc =>
      obtain ⟨pc, σ, am, hpre, hhalt, heq_σ, heq_am⟩ := ih _ _ _ rfl _ _ hc'
      exact ⟨pc, σ, am, Steps.step (Step.fternop (am := am₀) h ha hb hc) hpre, hhalt, heq_σ, heq_am⟩
    | print h =>
      obtain ⟨pc, σ, am, hpre, hhalt, heq_σ, heq_am⟩ := ih _ _ _ rfl _ _ hc'
      exact ⟨pc, σ, am, Steps.step (Step.print (am := am₀) h) hpre, hhalt, heq_σ, heq_am⟩
    | printInt h =>
      obtain ⟨pc, σ, am, hpre, hhalt, heq_σ, heq_am⟩ := ih _ _ _ rfl _ _ hc'
      exact ⟨pc, σ, am, Steps.step (Step.printInt (am := am₀) h) hpre, hhalt, heq_σ, heq_am⟩
    | printBool h =>
      obtain ⟨pc, σ, am, hpre, hhalt, heq_σ, heq_am⟩ := ih _ _ _ rfl _ _ hc'
      exact ⟨pc, σ, am, Steps.step (Step.printBool (am := am₀) h) hpre, hhalt, heq_σ, heq_am⟩
    | printFloat h =>
      obtain ⟨pc, σ, am, hpre, hhalt, heq_σ, heq_am⟩ := ih _ _ _ rfl _ _ hc'
      exact ⟨pc, σ, am, Steps.step (Step.printFloat (am := am₀) h) hpre, hhalt, heq_σ, heq_am⟩
    | printString h =>
      obtain ⟨pc, σ, am, hpre, hhalt, heq_σ, heq_am⟩ := ih _ _ _ rfl _ _ hc'
      exact ⟨pc, σ, am, Steps.step (Step.printString (am := am₀) h) hpre, hhalt, heq_σ, heq_am⟩
    | arrLoad_boundsError h _ _ => cases rest with
      | refl => exact absurd hc' Cfg.noConfusion
      | step s _ => exact absurd s Step.no_step_from_errorBounds
    | arrStore_boundsError h _ _ _ => cases rest with
      | refl => exact absurd hc' Cfg.noConfusion
      | step s _ => exact absurd s Step.no_step_from_errorBounds

-- ============================================================
-- § StepsN infrastructure
-- ============================================================

def StepsN (p : Prog) : Cfg → Cfg → Nat → Prop
  | c, c', 0 => c = c'
  | c, c', n + 1 => ∃ c'', Step p c c'' ∧ StepsN p c'' c' n

theorem StepsN_det {p : Prog} {c : Cfg} {n : Nat} :
    ∀ {c' c''}, StepsN p c c' n → StepsN p c c'' n → c' = c'' := by
  induction n generalizing c with
  | zero => intro _ _ h1 h2; exact h1.symm.trans h2
  | succ n ih =>
    intro _ _ h1 h2; obtain ⟨c1, hs1, hr1⟩ := h1; obtain ⟨c2, hs2, hr2⟩ := h2
    have := Step.deterministic hs1 hs2; subst this; exact ih hr1 hr2

theorem StepsN_extend {p : Prog} {c c' c'' : Cfg} {n : Nat}
    (h1 : StepsN p c c' n) (h2 : Step p c' c'') : StepsN p c c'' (n + 1) := by
  induction n generalizing c with
  | zero => change c = c' at h1; subst h1; exact ⟨c'', h2, rfl⟩
  | succ n ih => obtain ⟨cm, hs, hr⟩ := h1; exact ⟨cm, hs, ih hr⟩

theorem StepsN_split_last {p : Prog} {c c' : Cfg} {n : Nat}
    (h : StepsN p c c' (n + 1)) : ∃ c'', StepsN p c c'' n ∧ Step p c'' c' := by
  induction n generalizing c with
  | zero => obtain ⟨c'', hs, hr⟩ := h; exact ⟨c, rfl, hr ▸ hs⟩
  | succ n ih =>
    obtain ⟨c1, hs, hr⟩ := h; obtain ⟨c2, h2, hlast⟩ := ih hr
    exact ⟨c2, ⟨c1, hs, h2⟩, hlast⟩

theorem StepsN_trans {p : Prog} {c c' c'' : Cfg} {n m : Nat}
    (h1 : StepsN p c c' n) (h2 : StepsN p c' c'' m) : StepsN p c c'' (n + m) := by
  induction n generalizing c with
  | zero => change c = c' at h1; subst h1; rw [Nat.zero_add]; exact h2
  | succ n ih =>
    obtain ⟨cm, hs, hr⟩ := h1; rw [show n + 1 + m = (n + m) + 1 from by omega]
    exact ⟨cm, hs, ih hr⟩

theorem Steps_to_StepsN {p : Prog} {c c' : Cfg}
    (h : Steps p c c') : ∃ n, StepsN p c c' n := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | step s _ ih => obtain ⟨n, hn⟩ := ih; exact ⟨n + 1, ⟨_, s, hn⟩⟩

theorem StepsN_prefix {p : Prog} {c c' : Cfg} {n k : Nat}
    (h : StepsN p c c' (n + k)) : ∃ c'', StepsN p c c'' n := by
  induction k generalizing c' with
  | zero => exact ⟨c', h⟩
  | succ k ih =>
    rw [show n + (k + 1) = (n + k) + 1 from by omega] at h
    obtain ⟨cmid, hmid, _⟩ := StepsN_split_last h; exact ih hmid

theorem step_from_run {p : Prog} {c c' : Cfg}
    (h : Step p c c') : ∃ pc σ am, c = Cfg.run pc σ am := by
  cases h <;> exact ⟨_, _, _, rfl⟩

theorem inf_exec_is_run {p : Prog} {f : Nat → Cfg} (hinf : IsInfiniteExec p f) :
    ∀ n, ∃ pc σ am, f n = Cfg.run pc σ am := by
  intro n; cases hfn : f n with
  | run pc σ am => exact ⟨pc, σ, am, rfl⟩
  | halt σ am => exfalso; exact Step.no_step_from_halt (hfn ▸ hinf.2 n)
  | errorDiv σ am => exfalso; exact Step.no_step_from_errorDiv (hfn ▸ hinf.2 n)
  | errorBounds σ am => exfalso; exact Step.no_step_from_errorBounds (hfn ▸ hinf.2 n)
  | typeError σ am => exfalso; exact Step.no_step_from_typeError (hfn ▸ hinf.2 n)

theorem StepsN_run_predecessor {p : Prog} {c : Cfg} {pc : Label} {σ : Store} {am : ArrayMem} {n : Nat}
    (h : StepsN p c (Cfg.run pc σ am) (n + 1)) :
    ∃ pc' σ' am' c'', StepsN p c (Cfg.run pc' σ' am') n ∧ Step p (Cfg.run pc' σ' am') c'' := by
  obtain ⟨c'', h'', hlast⟩ := StepsN_split_last h
  obtain ⟨pc', σ', am', hc''⟩ := step_from_run hlast
  exact ⟨pc', σ', am', _, hc'' ▸ h'', hc'' ▸ hlast⟩

theorem StepsN_split {p : Prog} {c c' : Cfg} {n k : Nat}
    (h : StepsN p c c' (n + k)) : ∃ c'', StepsN p c c'' n ∧ StepsN p c'' c' k := by
  induction n generalizing c with
  | zero => exact ⟨c, rfl, (Nat.zero_add k) ▸ h⟩
  | succ n ih =>
    rw [show n + 1 + k = (n + k) + 1 from by omega] at h
    obtain ⟨cm, hs, hr⟩ := h; obtain ⟨c'', hp, hs'⟩ := ih hr
    exact ⟨c'', ⟨cm, hs, hp⟩, hs'⟩

theorem StepsN_intermediate_run {p : Prog} {pc₀ : Label} {σ₀ : Store} {am₀ : ArrayMem}
    {pc' : Label} {σ' : Store} {am' : ArrayMem} {total : Nat}
    (h : StepsN p (Cfg.run pc₀ σ₀ am₀) (Cfg.run pc' σ' am') total)
    {N : Nat} (hle : N ≤ total) :
    ∃ pc'' σ'' am'', StepsN p (Cfg.run pc₀ σ₀ am₀) (Cfg.run pc'' σ'' am'') N := by
  by_cases heq : N = total
  · subst heq; exact ⟨pc', σ', am', h⟩
  · obtain ⟨c'', h1, h2⟩ := StepsN_split (show StepsN p _ _ (N + (total - N)) by rwa [Nat.add_sub_cancel' (by omega : N ≤ total)])
    rw [show total - N = (total - N - 1) + 1 from by omega] at h2
    obtain ⟨c''', hs, _⟩ := h2
    obtain ⟨pc'', σ'', am'', hc⟩ := step_from_run hs; subst hc
    exact ⟨pc'', σ'', am'', h1⟩

-- ============================================================
-- § Soundness for divergence
-- ============================================================

theorem soundness_diverge (cert : PCertificate) (hvalid : PCertificateValid cert)
    (f : Nat → Cfg) (σ₀ : Store) (hts₀ : TypedStore cert.tyCtx σ₀)
    (hinf : IsInfiniteExec cert.trans f) (hf0 : f 0 = Cfg.run 0 σ₀ ArrayMem.init) :
    ∃ g : Nat → Cfg, IsInfiniteExec cert.orig g ∧ g 0 = Cfg.run 0 σ₀ ArrayMem.init := by
  suffices h_arb : ∀ N : Nat, ∃ pc σ am,
      StepsN cert.orig (Cfg.run 0 σ₀ ArrayMem.init) (Cfg.run pc σ am) N by
    have g_spec : ∀ n, ∃ c, StepsN cert.orig (Cfg.run 0 σ₀ ArrayMem.init) c n ∧
        ∃ pc σ am, c = Cfg.run pc σ am := by
      intro n; obtain ⟨pc, σ, am, h⟩ := h_arb n; exact ⟨_, h, pc, σ, am, rfl⟩
    let g : Nat → Cfg := fun n => (g_spec n).choose
    have g_stepsN : ∀ n, StepsN cert.orig (Cfg.run 0 σ₀ ArrayMem.init) (g n) n :=
      fun n => (g_spec n).choose_spec.1
    refine ⟨g, ⟨⟨σ₀, ArrayMem.init, ?_⟩, fun n => ?_⟩, ?_⟩
    · exact (g_stepsN 0).symm
    · obtain ⟨c'', h_prefix, h_last⟩ := StepsN_split_last (g_stepsN (n + 1))
      exact StepsN_det (g_stepsN n) h_prefix ▸ h_last
    · exact (g_stepsN 0).symm
  have hf_run := inf_exec_is_run hinf
  have advance : ∀ (m n : Nat) (pc_o : Label) (σ_o : Store) (am_o : ArrayMem) (total : Nat),
      (∀ pc_t σ_t am_t, f n = Cfg.run pc_t σ_t am_t → cert.measure pc_t σ_t ≤ m) →
      (∀ pc_t σ_t am_t, f n = Cfg.run pc_t σ_t am_t → PSimRel cert pc_t σ_t am_t pc_o σ_o am_o) →
      StepsN cert.orig (Cfg.run 0 σ₀ ArrayMem.init) (Cfg.run pc_o σ_o am_o) total →
      ∃ (n' : Nat) (pc_o' : Label) (σ_o' : Store) (am_o' : ArrayMem) (total' : Nat),
        (∀ pc_t σ_t am_t, f n' = Cfg.run pc_t σ_t am_t → PSimRel cert pc_t σ_t am_t pc_o' σ_o' am_o') ∧
        StepsN cert.orig (Cfg.run 0 σ₀ ArrayMem.init) (Cfg.run pc_o' σ_o' am_o') total' ∧
        total' ≥ total + 1 := by
    intro m; induction m with
    | zero =>
      intro n pc_o σ_o am_o total hmu hsim_fn hsteps
      obtain ⟨pc_t, σ_t, am_t, hfn⟩ := hf_run n
      obtain ⟨pc_t', σ_t', am_t', hfn1⟩ := hf_run (n + 1)
      have hsim := hsim_fn pc_t σ_t am_t hfn
      have hstep : cert.trans ⊩ Cfg.run pc_t σ_t am_t ⟶ Cfg.run pc_t' σ_t' am_t' := by
        have := hinf.2 n; rw [hfn, hfn1] at this; exact this
      obtain ⟨pc_o', σ_o', amo2, horig, hsim'⟩ := step_sim hvalid am_o hsim hstep
      obtain ⟨k, hk⟩ := Steps_to_StepsN horig
      cases k with
      | zero =>
        change Cfg.run pc_o σ_o am_o = Cfg.run pc_o' σ_o' amo2 at hk; cases hk
        have hnt := hvalid.nonterm pc_t pc_t' σ_t σ_t' σ_o am_t am_o
          hsim.2.2.2.1 (hsim.1 ▸ hsim.2.2.2.2.1) hsim.2.1 ⟨_, hstep, _, rfl⟩ (hsim.1.trans hsim'.1.symm)
        have := hmu pc_t σ_t am_t hfn; omega
      | succ k' =>
        exact ⟨n + 1, pc_o', σ_o', amo2, total + (k' + 1),
          fun pc σ am hf => by rw [hfn1] at hf; cases hf; exact hsim',
          StepsN_trans hsteps hk, by omega⟩
    | succ m ih =>
      intro n pc_o σ_o am_o total hmu hsim_fn hsteps
      obtain ⟨pc_t, σ_t, am_t, hfn⟩ := hf_run n
      obtain ⟨pc_t', σ_t', am_t', hfn1⟩ := hf_run (n + 1)
      have hsim := hsim_fn pc_t σ_t am_t hfn
      have hstep : cert.trans ⊩ Cfg.run pc_t σ_t am_t ⟶ Cfg.run pc_t' σ_t' am_t' := by
        have := hinf.2 n; rw [hfn, hfn1] at this; exact this
      obtain ⟨pc_o', σ_o', amo2, horig, hsim'⟩ := step_sim hvalid am_o hsim hstep
      obtain ⟨k, hk⟩ := Steps_to_StepsN horig
      cases k with
      | zero =>
        change Cfg.run pc_o σ_o am_o = Cfg.run pc_o' σ_o' amo2 at hk; cases hk
        have hmu' : ∀ pc σ am, f (n + 1) = Cfg.run pc σ am → cert.measure pc σ ≤ m := by
          intro pc σ am hf; rw [hfn1] at hf; cases hf
          have := hvalid.nonterm pc_t pc_t' σ_t σ_t' σ_o am_t am_o
            hsim.2.2.2.1 (hsim.1 ▸ hsim.2.2.2.2.1) hsim.2.1
            ⟨_, hstep, _, rfl⟩ (hsim.1.trans hsim'.1.symm)
          have := hmu pc_t σ_t am_t hfn; omega
        have hsim_fn' : ∀ pc σ am, f (n + 1) = Cfg.run pc σ am → PSimRel cert pc σ am pc_o σ_o am_o := by
          intro pc σ am hf; rw [hfn1] at hf; cases hf; exact hsim'
        exact ih (n + 1) pc_o σ_o am_o total hmu' hsim_fn' hsteps
      | succ k' =>
        exact ⟨n + 1, pc_o', σ_o', amo2, total + (k' + 1),
          fun pc σ am hf => by rw [hfn1] at hf; cases hf; exact hsim',
          StepsN_trans hsteps hk, by omega⟩
  suffices ∀ N, ∃ (n : Nat) (pc_o : Label) (σ_o : Store) (am_o : ArrayMem) (total : Nat),
      (∀ pc_t σ_t am_t, f n = Cfg.run pc_t σ_t am_t → PSimRel cert pc_t σ_t am_t pc_o σ_o am_o) ∧
      StepsN cert.orig (Cfg.run 0 σ₀ ArrayMem.init) (Cfg.run pc_o σ_o am_o) total ∧ total ≥ N by
    intro N; obtain ⟨_, _, _, am_o, total, _, hsteps, hge⟩ := this N
    exact StepsN_intermediate_run hsteps hge
  intro N; induction N with
  | zero =>
    refine ⟨0, 0, σ₀, ArrayMem.init, 0, ?_, rfl, Nat.zero_le _⟩
    intro pc_t σ_t am_t hfn; rw [hf0] at hfn; cases hfn
    exact ⟨hvalid.start_corr.1, hvalid.start_corr.2 σ₀ ArrayMem.init, rfl,
           hvalid.start_inv.1 σ₀ ArrayMem.init, hvalid.start_inv.2 σ₀ ArrayMem.init, hts₀⟩
  | succ N ih =>
    obtain ⟨n, pc_o, σ_o, am_o, total, hsim_fn, hsteps, hge⟩ := ih
    obtain ⟨pc_t, σ_t, am_t, hfn⟩ := hf_run n
    obtain ⟨n', pc_o', σ_o', am_o', total', hsim', hsteps', hge'⟩ :=
      advance (cert.measure pc_t σ_t) n pc_o σ_o am_o total
        (fun pc σ am hf => by rw [hfn] at hf; cases hf; omega)
        hsim_fn hsteps
    exact ⟨n', pc_o', σ_o', am_o', total', hsim', hsteps', by omega⟩

-- ============================================================
-- § Behaviors
-- ============================================================

inductive Behavior where
  | halts       : Store → Behavior
  | errorDiv    : Store → Behavior
  | errorBounds : Store → Behavior
  | typeErrors  : Store → Behavior
  | diverges    : Behavior

def program_behavior (p : Prog) (σ₀ : Store) (b : Behavior) : Prop :=
  match b with
  | .halts σ'       => ∃ am am', haltsWithResult p 0 σ₀ σ' am am'
  | .errorDiv σ'    => ∃ am am', p ⊩ Cfg.run 0 σ₀ am ⟶* Cfg.errorDiv σ' am'
  | .errorBounds σ' => ∃ am am', p ⊩ Cfg.run 0 σ₀ am ⟶* Cfg.errorBounds σ' am'
  | .typeErrors σ'  => ∃ am am', p ⊩ Cfg.run 0 σ₀ am ⟶* Cfg.typeError σ' am'
  | .diverges       => ∃ f : Nat → Cfg, IsInfiniteExec p f ∧ f 0 = Cfg.run 0 σ₀ ArrayMem.init

private theorem StepsN_to_Steps' {p : Prog} {c c' : Cfg} {n : Nat}
    (h : StepsN p c c' n) : p ⊩ c ⟶* c' := by
  induction n generalizing c with
  | zero => exact h ▸ .refl
  | succ n ih => obtain ⟨c'', hs, hn⟩ := h; exact .step hs (ih hn)

theorem has_behavior (p : Prog) (σ₀ : Store) (hclosed : StepClosedInBounds p) :
    ∃ b, program_behavior p σ₀ b := by
  by_cases h : ∃ n σ' am', StepsN p (Cfg.run 0 σ₀ ArrayMem.init) (Cfg.halt σ' am') n
  · obtain ⟨n, σ', am', hn⟩ := h
    exact ⟨.halts σ', ArrayMem.init, am', StepsN_to_Steps' hn⟩
  · by_cases hed : ∃ n σ' am', StepsN p (Cfg.run 0 σ₀ ArrayMem.init) (Cfg.errorDiv σ' am') n
    · obtain ⟨_, σ', am', hn⟩ := hed
      exact ⟨.errorDiv σ', ArrayMem.init, am', StepsN_to_Steps' hn⟩
    · by_cases heb : ∃ n σ' am', StepsN p (Cfg.run 0 σ₀ ArrayMem.init) (Cfg.errorBounds σ' am') n
      · obtain ⟨_, σ', am', hn⟩ := heb
        exact ⟨.errorBounds σ', ArrayMem.init, am', StepsN_to_Steps' hn⟩
      · by_cases hte : ∃ n σ' am', StepsN p (Cfg.run 0 σ₀ ArrayMem.init) (Cfg.typeError σ' am') n
        · obtain ⟨_, σ', am', hn⟩ := hte
          exact ⟨.typeErrors σ', ArrayMem.init, am', StepsN_to_Steps' hn⟩
        · have h_run : ∀ n, ∃ pc σ am, StepsN p (Cfg.run 0 σ₀ ArrayMem.init) (Cfg.run pc σ am) n ∧ pc < p.size := by
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

-- ============================================================
-- § Simulation trace
-- ============================================================

private theorem simulation_trace_stepsN {cert : PCertificate} (hvalid : PCertificateValid cert)
    {pc_t pc_t' : Label} {σ_t σ_t' : Store} {am_t am_t' : ArrayMem} {n : Nat}
    (hsteps : StepsN cert.trans (Cfg.run pc_t σ_t am_t) (Cfg.run pc_t' σ_t' am_t') n)
    {pc_o : Label} {σ_o : Store} (am_o : ArrayMem)
    (hsim : PSimRel cert pc_t σ_t am_t pc_o σ_o am_o) :
    ∃ pc_o' σ_o' am_o',
      (cert.orig ⊩ Cfg.run pc_o σ_o am_o ⟶* Cfg.run pc_o' σ_o' am_o') ∧
      PSimRel cert pc_t' σ_t' am_t' pc_o' σ_o' am_o' := by
  induction n generalizing pc_t σ_t am_t pc_o σ_o am_o with
  | zero =>
    change Cfg.run pc_t σ_t am_t = Cfg.run pc_t' σ_t' am_t' at hsteps; cases hsteps
    exact ⟨pc_o, σ_o, am_o, .refl, hsim⟩
  | succ n ih =>
    obtain ⟨c_mid, hfirst, hrest⟩ := hsteps
    -- c_mid must be a run config (halt/error/typeError can't continue)
    match c_mid, hfirst with
    | .run pc_mid σ_mid am_mid, hstep =>
      obtain ⟨pc_o_mid, σ_o_mid, am_o_mid, horig_seg, hsim_mid⟩ :=
        step_sim hvalid am_o hsim hstep
      obtain ⟨pc_o', σ_o', am_o', horig_rest, hsim'⟩ :=
        ih hrest am_o_mid hsim_mid
      exact ⟨pc_o', σ_o', am_o', Steps.trans horig_seg horig_rest, hsim'⟩
    | .halt _ _, hstep =>
      exfalso; cases n with
      | zero => exact Cfg.noConfusion (hrest : Cfg.halt _ _ = Cfg.run _ _ _)
      | succ => obtain ⟨_, hs, _⟩ := hrest; exact Step.no_step_from_halt hs
    | .errorDiv _ _, hstep =>
      exfalso; cases n with
      | zero => exact Cfg.noConfusion (hrest : Cfg.errorDiv _ _ = Cfg.run _ _ _)
      | succ => obtain ⟨_, hs, _⟩ := hrest; exact Step.no_step_from_errorDiv hs
    | .errorBounds _ _, hstep =>
      exfalso; cases n with
      | zero => exact Cfg.noConfusion (hrest : Cfg.errorBounds _ _ = Cfg.run _ _ _)
      | succ => obtain ⟨_, hs, _⟩ := hrest; exact Step.no_step_from_errorBounds hs
    | .typeError _ _, hstep =>
      exfalso; cases n with
      | zero => exact Cfg.noConfusion (hrest : Cfg.typeError _ _ = Cfg.run _ _ _)
      | succ => obtain ⟨_, hs, _⟩ := hrest; exact Step.no_step_from_typeError hs

theorem simulation_trace {cert : PCertificate} (hvalid : PCertificateValid cert)
    {σ₀ : Store} (hts₀ : TypedStore cert.tyCtx σ₀)
    {pc_t : Label} {σ_t : Store} {am₀ am_t : ArrayMem}
    (hreach : cert.trans ⊩ Cfg.run 0 σ₀ am₀ ⟶* Cfg.run pc_t σ_t am_t) :
    ∃ pc_o σ_o am_o', (cert.orig ⊩ Cfg.run 0 σ₀ am₀ ⟶* Cfg.run pc_o σ_o am_o') ∧
      PSimRel cert pc_t σ_t am_t pc_o σ_o am_o' := by
  have hsim₀ : PSimRel cert 0 σ₀ am₀ 0 σ₀ am₀ :=
    ⟨hvalid.start_corr.1, hvalid.start_corr.2 σ₀ am₀, rfl,
     hvalid.start_inv.1 σ₀ am₀, hvalid.start_inv.2 σ₀ am₀, hts₀⟩
  obtain ⟨n, hn⟩ := Steps_to_StepsN hreach
  obtain ⟨pc_o, σ_o, am_o_end, hpath, hsim⟩ :=
    simulation_trace_stepsN hvalid hn am₀ hsim₀
  exact ⟨pc_o, σ_o, am_o_end, hpath, hsim⟩

theorem soundness_halt (cert : PCertificate) (hvalid : PCertificateValid cert)
    (σ₀ σ_t' : Store) (hts₀ : TypedStore cert.tyCtx σ₀)
    {am₀ : ArrayMem} (hexec : ∃ am', haltsWithResult cert.trans 0 σ₀ σ_t' am₀ am') :
    ∃ σ_o' am_f, haltsWithResult cert.orig 0 σ₀ σ_o' am₀ am_f ∧
      haltsWithResult cert.trans 0 σ₀ σ_t' am₀ am_f ∧
      ∀ v ∈ cert.observable, σ_t' v = σ_o' v := by
  obtain ⟨am', hhalt⟩ := hexec
  -- Decompose the halt execution into a run-to-run prefix + halt step
  obtain ⟨pc_t, σ_t, am_t, hrun, hhalt_instr, rfl, rfl⟩ := steps_to_halt_decompose hhalt
  -- Use simulation_trace on the run-to-run prefix
  obtain ⟨pc_o, σ_o, am_o', horig, hpc_eq, hrel, ham_eq, _hinv_t, _hinv_o, _hts⟩ :=
    simulation_trace hvalid hts₀ hrun
  -- The original program must also halt at pc_o
  have horig_halt : cert.orig[pc_o]? = some TAC.halt := by
    rw [← hpc_eq]; exact hvalid.halt_corr pc_t hhalt_instr
  -- Both programs halt with the same final array memory, same initial AM
  exact ⟨σ_o, am_o', Steps.trans horig (Steps.step (Step.halt horig_halt) .refl),
    ham_eq ▸ hhalt,
    fun v hv => hvalid.halt_obs pc_t σ_t σ_o am_t am_o' hhalt_instr hrel v hv⟩

-- ============================================================
-- § Observation helpers
-- ============================================================

private theorem obs_map_eq {obs : List Var} {σ_t σ_o : Store}
    (h : ∀ v ∈ obs, σ_t v = σ_o v) :
    obs.map (fun v => (v, σ_t v)) = obs.map (fun v => (v, σ_o v)) := by
  induction obs with
  | nil => rfl
  | cons v rest ih =>
    simp only [List.map_cons, List.cons.injEq]
    exact ⟨congrArg (Prod.mk v) (h v (.head _)), ih (fun w hw => h w (.tail _ hw))⟩

private theorem steps_run_in_bounds {p : Prog} (hclosed : StepClosedInBounds p)
    {pc₀ : Label} {σ₀ : Store} {am₀ : ArrayMem} (hpc₀ : pc₀ < p.size)
    {pc : Label} {σ : Store} {am : ArrayMem}
    (hreach : p ⊩ Cfg.run pc₀ σ₀ am₀ ⟶* Cfg.run pc σ am) : pc < p.size := by
  suffices h : ∀ c c', Steps p c c' →
      ∀ (pc : Label) (σ : Store) (am : ArrayMem), c = Cfg.run pc σ am → pc < p.size →
      ∀ (pc' : Label) (σ' : Store) (am' : ArrayMem), c' = Cfg.run pc' σ' am' → pc' < p.size from
    h _ _ hreach pc₀ σ₀ am₀ rfl hpc₀ pc σ am rfl
  intro c c' hsteps
  induction hsteps with
  | refl => intro pc σ am hc hpc pc' σ' am' hc'; rw [hc] at hc'; cases hc'; exact hpc
  | step hstep rest ih =>
    intro pc σ am hc hpc pc' σ' am' hc'; subst hc
    cases hstep with
    | halt h => cases rest with
      | refl => exact absurd hc' Cfg.noConfusion
      | step s _ => exact absurd s Step.no_step_from_halt
    | binop_divByZero h _ _ _ => cases rest with
      | refl => exact absurd hc' Cfg.noConfusion
      | step s _ => exact absurd s Step.no_step_from_errorDiv
    | binop_typeError h _ | arrLoad_typeError h _ | arrStore_typeError h _
    | fbinop_typeError h _ | intToFloat_typeError h _ | floatToInt_typeError h _
    | floatUnary_typeError h _ | fternop_typeError h _ => cases rest with
      | refl => exact absurd hc' Cfg.noConfusion
      | step s _ => exact absurd s Step.no_step_from_typeError
    | const h =>
      exact ih _ _ _ rfl (hclosed.2 _ _ _ _ _ _ hpc (Step.const (σ := σ) (am := am) h)) _ _ _ hc'
    | copy h =>
      exact ih _ _ _ rfl (hclosed.2 _ _ _ _ _ _ hpc (Step.copy (σ := σ) (am := am) h)) _ _ _ hc'
    | binop h hy hz hs =>
      exact ih _ _ _ rfl (hclosed.2 _ _ _ _ _ _ hpc (Step.binop (am := am) h hy hz hs)) _ _ _ hc'
    | boolop h =>
      exact ih _ _ _ rfl (hclosed.2 _ _ _ _ _ _ hpc (Step.boolop (σ := σ) (am := am) h)) _ _ _ hc'
    | goto h =>
      exact ih _ _ _ rfl (hclosed.2 _ _ _ _ _ _ hpc (Step.goto (σ := σ) (am := am) h)) _ _ _ hc'
    | iftrue h hne =>
      exact ih _ _ _ rfl (hclosed.2 _ _ _ _ _ _ hpc (Step.iftrue (am := am) h hne)) _ _ _ hc'
    | iffall h heq =>
      exact ih _ _ _ rfl (hclosed.2 _ _ _ _ _ _ hpc (Step.iffall (am := am) h heq)) _ _ _ hc'
    | arrLoad h hidx hb =>
      exact ih _ _ _ rfl (hclosed.2 _ _ _ _ _ _ hpc (Step.arrLoad (am := am) h hidx hb)) _ _ _ hc'
    | arrStore h hidx hv hb =>
      exact ih _ _ _ rfl (hclosed.2 _ _ _ _ _ _ hpc (Step.arrStore (am := am) h hidx hv hb)) _ _ _ hc'
    | fbinop h hy hz =>
      exact ih _ _ _ rfl (hclosed.2 _ _ _ _ _ _ hpc (Step.fbinop (am := am) h hy hz)) _ _ _ hc'
    | intToFloat h hy =>
      exact ih _ _ _ rfl (hclosed.2 _ _ _ _ _ _ hpc (Step.intToFloat (am := am) h hy)) _ _ _ hc'
    | floatToInt h hy =>
      exact ih _ _ _ rfl (hclosed.2 _ _ _ _ _ _ hpc (Step.floatToInt (am := am) h hy)) _ _ _ hc'
    | floatUnary h hy =>
      exact ih _ _ _ rfl (hclosed.2 _ _ _ _ _ _ hpc (Step.floatUnary (am := am) h hy)) _ _ _ hc'
    | fternop h ha hb hc =>
      exact ih _ _ _ rfl (hclosed.2 _ _ _ _ _ _ hpc (Step.fternop (am := am) h ha hb hc)) _ _ _ hc'
    | print h =>
      exact ih _ _ _ rfl (hclosed.2 _ _ _ _ _ _ hpc (Step.print (σ := σ) (am := am) h)) _ _ _ hc'
    | printInt h =>
      exact ih _ _ _ rfl (hclosed.2 _ _ _ _ _ _ hpc (Step.printInt (σ := σ) (am := am) h)) _ _ _ hc'
    | printBool h =>
      exact ih _ _ _ rfl (hclosed.2 _ _ _ _ _ _ hpc (Step.printBool (σ := σ) (am := am) h)) _ _ _ hc'
    | printFloat h =>
      exact ih _ _ _ rfl (hclosed.2 _ _ _ _ _ _ hpc (Step.printFloat (σ := σ) (am := am) h)) _ _ _ hc'
    | printString h =>
      exact ih _ _ _ rfl (hclosed.2 _ _ _ _ _ _ hpc (Step.printString (σ := σ) (am := am) h)) _ _ _ hc'
    | arrLoad_boundsError h _ _ => cases rest with
      | refl => exact absurd hc' Cfg.noConfusion
      | step s _ => exact absurd s Step.no_step_from_errorBounds
    | arrStore_boundsError h _ _ _ => cases rest with
      | refl => exact absurd hc' Cfg.noConfusion
      | step s _ => exact absurd s Step.no_step_from_errorBounds

-- ============================================================
-- § Halt preservation
-- ============================================================

theorem halt_preservation (cert : PCertificate) (hvalid : PCertificateValid cert)
    (σ₀ : Store) (hts₀ : TypedStore cert.tyCtx σ₀) (c_t : Cfg)
    (hreach : ∃ am₀, cert.trans ⊩ Cfg.run 0 σ₀ am₀ ⟶* c_t)
    (pairs : List (Var × Value))
    (hobs : observe cert.trans cert.observable c_t = Observation.halt pairs) :
    ∃ c_o, (∃ am₀, cert.orig ⊩ Cfg.run 0 σ₀ am₀ ⟶* c_o) ∧
      observe cert.orig cert.observable c_o = Observation.halt pairs := by
  obtain ⟨am₀, hreach⟩ := hreach
  cases c_t with
  | halt σ_t am_h =>
    obtain ⟨σ_o, am_f, horig', _, hobs_eq⟩ := soundness_halt cert hvalid σ₀ σ_t hts₀ (am₀ := am₀) ⟨am_h, hreach⟩
    simp only [observe] at hobs; rw [Observation.halt.injEq] at hobs; subst hobs
    exact ⟨Cfg.halt σ_o am_f, ⟨am₀, horig'⟩,
      congrArg Observation.halt (obs_map_eq (fun v hv => (hobs_eq v hv).symm))⟩
  | run pc_t σ_t am_t =>
    have hpc := steps_run_in_bounds hvalid.step_closed hvalid.step_closed.1 hreach
    obtain ⟨instr, hinstr⟩ : ∃ instr, cert.trans[pc_t]? = some instr :=
      ⟨cert.trans[pc_t], getElem?_eq_some_iff.mpr ⟨hpc, rfl⟩⟩
    cases instr with
    | halt =>
      obtain ⟨pc_o, σ_o, a2, ho, hpc_eq, hrel, _, _, _⟩ := simulation_trace hvalid hts₀ hreach
      have horig_halt : cert.orig[pc_o]? = some TAC.halt := by rw [← hpc_eq]; exact hvalid.halt_corr pc_t hinstr
      have htobs : observe cert.trans cert.observable (Cfg.run pc_t σ_t am_t) =
          Observation.halt (cert.observable.map fun v => (v, σ_t v)) := by simp only [observe, hinstr]
      have hoobs : observe cert.orig cert.observable (Cfg.run pc_o σ_o a2) =
          Observation.halt (cert.observable.map fun v => (v, σ_o v)) := by simp only [observe, horig_halt]
      rw [htobs] at hobs; rw [Observation.halt.injEq] at hobs; subst hobs
      exact ⟨Cfg.run pc_o σ_o a2, ⟨am₀, ho⟩, hoobs ▸
        congrArg Observation.halt (obs_map_eq (fun v hv => (hvalid.halt_obs pc_t σ_t σ_o am_t a2 hinstr hrel v hv).symm))⟩
    | _ => simp only [observe, hinstr] at hobs; exact Observation.noConfusion hobs
  | errorDiv σ_t am_t => simp [observe] at hobs
  | errorBounds σ_t am_t => simp [observe] at hobs
  | typeError σ_t am_t => simp [observe] at hobs

-- ============================================================
-- § Error decomposition and preservation
-- ============================================================

private theorem steps_to_errorDiv_decompose {p : Prog} {pc₀ : Nat} {σ₀ σ_e : Store} {am₀ am_e : ArrayMem}
    (hsteps : p ⊩ Cfg.run pc₀ σ₀ am₀ ⟶* Cfg.errorDiv σ_e am_e) :
    ∃ pc σ am, (p ⊩ Cfg.run pc₀ σ₀ am₀ ⟶* Cfg.run pc σ am) ∧
      (p ⊩ Cfg.run pc σ am ⟶ Cfg.errorDiv σ am) ∧ σ = σ_e := by
  suffices h : ∀ c c', Steps p c c' →
      ∀ (pc₀ : Nat) (σ₀ : Store) (am₀ : ArrayMem), c = Cfg.run pc₀ σ₀ am₀ →
      ∀ (σ_e : Store) (am_e : ArrayMem), c' = Cfg.errorDiv σ_e am_e →
      ∃ pc σ am, (p ⊩ Cfg.run pc₀ σ₀ am₀ ⟶* Cfg.run pc σ am) ∧
        (p ⊩ Cfg.run pc σ am ⟶ Cfg.errorDiv σ am) ∧ σ = σ_e from
    h _ _ hsteps pc₀ σ₀ am₀ rfl σ_e am_e rfl
  intro c c' hsteps
  induction hsteps with
  | refl => intro pc₀ σ₀ am₀ hc σ_e am_e hc'; rw [hc] at hc'; exact absurd hc' Cfg.noConfusion
  | step hstep rest ih =>
    intro pc₀ σ₀ am₀ hc σ_e am_e hc'; subst hc
    cases hstep with
    | halt h => cases rest with
      | refl => exact absurd hc' Cfg.noConfusion
      | step s _ => exact absurd s Step.no_step_from_halt
    | binop_divByZero h hy hz hs =>
      cases rest with
      | refl => cases hc'; exact ⟨pc₀, σ₀, am₀, Steps.refl, Step.binop_divByZero h hy hz hs, rfl⟩
      | step s _ => exact absurd s Step.no_step_from_errorDiv
    | binop_typeError h _ | arrLoad_typeError h _ | arrStore_typeError h _
    | fbinop_typeError h _ | intToFloat_typeError h _ | floatToInt_typeError h _
    | floatUnary_typeError h _ | fternop_typeError h _ => cases rest with
      | refl => exact absurd hc' Cfg.noConfusion
      | step s _ => exact absurd s Step.no_step_from_typeError
    | const h =>
      obtain ⟨pc, σ, am, hpre, herr, heq⟩ := ih _ _ _ rfl _ _ hc'
      exact ⟨pc, σ, am, Steps.step (Step.const (σ := σ₀) (am := am₀) h) hpre, herr, heq⟩
    | copy h =>
      obtain ⟨pc, σ, am, hpre, herr, heq⟩ := ih _ _ _ rfl _ _ hc'
      exact ⟨pc, σ, am, Steps.step (Step.copy (σ := σ₀) (am := am₀) h) hpre, herr, heq⟩
    | binop h hy hz hs =>
      obtain ⟨pc, σ, am, hpre, herr, heq⟩ := ih _ _ _ rfl _ _ hc'
      exact ⟨pc, σ, am, Steps.step (Step.binop (am := am₀) h hy hz hs) hpre, herr, heq⟩
    | boolop h =>
      obtain ⟨pc, σ, am, hpre, herr, heq⟩ := ih _ _ _ rfl _ _ hc'
      exact ⟨pc, σ, am, Steps.step (Step.boolop (σ := σ₀) (am := am₀) h) hpre, herr, heq⟩
    | goto h =>
      obtain ⟨pc, σ, am, hpre, herr, heq⟩ := ih _ _ _ rfl _ _ hc'
      exact ⟨pc, σ, am, Steps.step (Step.goto (σ := σ₀) (am := am₀) h) hpre, herr, heq⟩
    | iftrue h hne =>
      obtain ⟨pc, σ, am, hpre, herr, heq⟩ := ih _ _ _ rfl _ _ hc'
      exact ⟨pc, σ, am, Steps.step (Step.iftrue (am := am₀) h hne) hpre, herr, heq⟩
    | iffall h heq' =>
      obtain ⟨pc, σ, am, hpre, herr, heq⟩ := ih _ _ _ rfl _ _ hc'
      exact ⟨pc, σ, am, Steps.step (Step.iffall (am := am₀) h heq') hpre, herr, heq⟩
    | arrLoad h hidx hb =>
      obtain ⟨pc, σ, am, hpre, herr, heq⟩ := ih _ _ _ rfl _ _ hc'
      exact ⟨pc, σ, am, Steps.step (Step.arrLoad (am := am₀) h hidx hb) hpre, herr, heq⟩
    | arrStore h hidx hv hb =>
      obtain ⟨pc, σ, am, hpre, herr, heq⟩ := ih _ _ _ rfl _ _ hc'
      exact ⟨pc, σ, am, Steps.step (Step.arrStore (am := am₀) h hidx hv hb) hpre, herr, heq⟩
    | fbinop h hy hz =>
      obtain ⟨pc, σ, am, hpre, herr, heq⟩ := ih _ _ _ rfl _ _ hc'
      exact ⟨pc, σ, am, Steps.step (Step.fbinop (am := am₀) h hy hz) hpre, herr, heq⟩
    | intToFloat h hy =>
      obtain ⟨pc, σ, am, hpre, herr, heq⟩ := ih _ _ _ rfl _ _ hc'
      exact ⟨pc, σ, am, Steps.step (Step.intToFloat (am := am₀) h hy) hpre, herr, heq⟩
    | floatToInt h hy =>
      obtain ⟨pc, σ, am, hpre, herr, heq⟩ := ih _ _ _ rfl _ _ hc'
      exact ⟨pc, σ, am, Steps.step (Step.floatToInt (am := am₀) h hy) hpre, herr, heq⟩
    | floatUnary h hy =>
      obtain ⟨pc, σ, am, hpre, herr, heq⟩ := ih _ _ _ rfl _ _ hc'
      exact ⟨pc, σ, am, Steps.step (Step.floatUnary (am := am₀) h hy) hpre, herr, heq⟩
    | fternop h ha hb hc =>
      obtain ⟨pc, σ, am, hpre, herr, heq⟩ := ih _ _ _ rfl _ _ hc'
      exact ⟨pc, σ, am, Steps.step (Step.fternop (am := am₀) h ha hb hc) hpre, herr, heq⟩
    | print h =>
      obtain ⟨pc, σ, am, hpre, herr, heq⟩ := ih _ _ _ rfl _ _ hc'
      exact ⟨pc, σ, am, Steps.step (Step.print (am := am₀) h) hpre, herr, heq⟩
    | printInt h =>
      obtain ⟨pc, σ, am, hpre, herr, heq⟩ := ih _ _ _ rfl _ _ hc'
      exact ⟨pc, σ, am, Steps.step (Step.printInt (am := am₀) h) hpre, herr, heq⟩
    | printBool h =>
      obtain ⟨pc, σ, am, hpre, herr, heq⟩ := ih _ _ _ rfl _ _ hc'
      exact ⟨pc, σ, am, Steps.step (Step.printBool (am := am₀) h) hpre, herr, heq⟩
    | printFloat h =>
      obtain ⟨pc, σ, am, hpre, herr, heq⟩ := ih _ _ _ rfl _ _ hc'
      exact ⟨pc, σ, am, Steps.step (Step.printFloat (am := am₀) h) hpre, herr, heq⟩
    | printString h =>
      obtain ⟨pc, σ, am, hpre, herr, heq⟩ := ih _ _ _ rfl _ _ hc'
      exact ⟨pc, σ, am, Steps.step (Step.printString (am := am₀) h) hpre, herr, heq⟩
    | arrLoad_boundsError h hidx hob =>
      cases rest with
      | refl => exact absurd hc' Cfg.noConfusion
      | step s _ => exact absurd s Step.no_step_from_errorBounds
    | arrStore_boundsError h hidx hv hob =>
      cases rest with
      | refl => exact absurd hc' Cfg.noConfusion
      | step s _ => exact absurd s Step.no_step_from_errorBounds

private theorem steps_to_errorBounds_decompose {p : Prog} {pc₀ : Nat} {σ₀ σ_e : Store} {am₀ am_e : ArrayMem}
    (hsteps : p ⊩ Cfg.run pc₀ σ₀ am₀ ⟶* Cfg.errorBounds σ_e am_e) :
    ∃ pc σ am, (p ⊩ Cfg.run pc₀ σ₀ am₀ ⟶* Cfg.run pc σ am) ∧
      (p ⊩ Cfg.run pc σ am ⟶ Cfg.errorBounds σ am) ∧ σ = σ_e := by
  suffices h : ∀ c c', Steps p c c' →
      ∀ (pc₀ : Nat) (σ₀ : Store) (am₀ : ArrayMem), c = Cfg.run pc₀ σ₀ am₀ →
      ∀ (σ_e : Store) (am_e : ArrayMem), c' = Cfg.errorBounds σ_e am_e →
      ∃ pc σ am, (p ⊩ Cfg.run pc₀ σ₀ am₀ ⟶* Cfg.run pc σ am) ∧
        (p ⊩ Cfg.run pc σ am ⟶ Cfg.errorBounds σ am) ∧ σ = σ_e from
    h _ _ hsteps pc₀ σ₀ am₀ rfl σ_e am_e rfl
  intro c c' hsteps
  induction hsteps with
  | refl => intro pc₀ σ₀ am₀ hc σ_e am_e hc'; rw [hc] at hc'; exact absurd hc' Cfg.noConfusion
  | step hstep rest ih =>
    intro pc₀ σ₀ am₀ hc σ_e am_e hc'; subst hc
    cases hstep with
    | halt h => cases rest with
      | refl => exact absurd hc' Cfg.noConfusion
      | step s _ => exact absurd s Step.no_step_from_halt
    | binop_divByZero h hy hz hs =>
      cases rest with
      | refl => exact absurd hc' Cfg.noConfusion
      | step s _ => exact absurd s Step.no_step_from_errorDiv
    | binop_typeError h _ | arrLoad_typeError h _ | arrStore_typeError h _
    | fbinop_typeError h _ | intToFloat_typeError h _ | floatToInt_typeError h _
    | floatUnary_typeError h _ | fternop_typeError h _ => cases rest with
      | refl => exact absurd hc' Cfg.noConfusion
      | step s _ => exact absurd s Step.no_step_from_typeError
    | const h =>
      obtain ⟨pc, σ, am, hpre, herr, heq⟩ := ih _ _ _ rfl _ _ hc'
      exact ⟨pc, σ, am, Steps.step (Step.const (σ := σ₀) (am := am₀) h) hpre, herr, heq⟩
    | copy h =>
      obtain ⟨pc, σ, am, hpre, herr, heq⟩ := ih _ _ _ rfl _ _ hc'
      exact ⟨pc, σ, am, Steps.step (Step.copy (σ := σ₀) (am := am₀) h) hpre, herr, heq⟩
    | binop h hy hz hs =>
      obtain ⟨pc, σ, am, hpre, herr, heq⟩ := ih _ _ _ rfl _ _ hc'
      exact ⟨pc, σ, am, Steps.step (Step.binop (am := am₀) h hy hz hs) hpre, herr, heq⟩
    | boolop h =>
      obtain ⟨pc, σ, am, hpre, herr, heq⟩ := ih _ _ _ rfl _ _ hc'
      exact ⟨pc, σ, am, Steps.step (Step.boolop (σ := σ₀) (am := am₀) h) hpre, herr, heq⟩
    | goto h =>
      obtain ⟨pc, σ, am, hpre, herr, heq⟩ := ih _ _ _ rfl _ _ hc'
      exact ⟨pc, σ, am, Steps.step (Step.goto (σ := σ₀) (am := am₀) h) hpre, herr, heq⟩
    | iftrue h hne =>
      obtain ⟨pc, σ, am, hpre, herr, heq⟩ := ih _ _ _ rfl _ _ hc'
      exact ⟨pc, σ, am, Steps.step (Step.iftrue (am := am₀) h hne) hpre, herr, heq⟩
    | iffall h heq' =>
      obtain ⟨pc, σ, am, hpre, herr, heq⟩ := ih _ _ _ rfl _ _ hc'
      exact ⟨pc, σ, am, Steps.step (Step.iffall (am := am₀) h heq') hpre, herr, heq⟩
    | arrLoad h hidx hb =>
      obtain ⟨pc, σ, am, hpre, herr, heq⟩ := ih _ _ _ rfl _ _ hc'
      exact ⟨pc, σ, am, Steps.step (Step.arrLoad (am := am₀) h hidx hb) hpre, herr, heq⟩
    | arrStore h hidx hv hb =>
      obtain ⟨pc, σ, am, hpre, herr, heq⟩ := ih _ _ _ rfl _ _ hc'
      exact ⟨pc, σ, am, Steps.step (Step.arrStore (am := am₀) h hidx hv hb) hpre, herr, heq⟩
    | fbinop h hy hz =>
      obtain ⟨pc, σ, am, hpre, herr, heq⟩ := ih _ _ _ rfl _ _ hc'
      exact ⟨pc, σ, am, Steps.step (Step.fbinop (am := am₀) h hy hz) hpre, herr, heq⟩
    | intToFloat h hy =>
      obtain ⟨pc, σ, am, hpre, herr, heq⟩ := ih _ _ _ rfl _ _ hc'
      exact ⟨pc, σ, am, Steps.step (Step.intToFloat (am := am₀) h hy) hpre, herr, heq⟩
    | floatToInt h hy =>
      obtain ⟨pc, σ, am, hpre, herr, heq⟩ := ih _ _ _ rfl _ _ hc'
      exact ⟨pc, σ, am, Steps.step (Step.floatToInt (am := am₀) h hy) hpre, herr, heq⟩
    | floatUnary h hy =>
      obtain ⟨pc, σ, am, hpre, herr, heq⟩ := ih _ _ _ rfl _ _ hc'
      exact ⟨pc, σ, am, Steps.step (Step.floatUnary (am := am₀) h hy) hpre, herr, heq⟩
    | fternop h ha hb hc =>
      obtain ⟨pc, σ, am, hpre, herr, heq⟩ := ih _ _ _ rfl _ _ hc'
      exact ⟨pc, σ, am, Steps.step (Step.fternop (am := am₀) h ha hb hc) hpre, herr, heq⟩
    | print h =>
      obtain ⟨pc, σ, am, hpre, herr, heq⟩ := ih _ _ _ rfl _ _ hc'
      exact ⟨pc, σ, am, Steps.step (Step.print (am := am₀) h) hpre, herr, heq⟩
    | printInt h =>
      obtain ⟨pc, σ, am, hpre, herr, heq⟩ := ih _ _ _ rfl _ _ hc'
      exact ⟨pc, σ, am, Steps.step (Step.printInt (am := am₀) h) hpre, herr, heq⟩
    | printBool h =>
      obtain ⟨pc, σ, am, hpre, herr, heq⟩ := ih _ _ _ rfl _ _ hc'
      exact ⟨pc, σ, am, Steps.step (Step.printBool (am := am₀) h) hpre, herr, heq⟩
    | printFloat h =>
      obtain ⟨pc, σ, am, hpre, herr, heq⟩ := ih _ _ _ rfl _ _ hc'
      exact ⟨pc, σ, am, Steps.step (Step.printFloat (am := am₀) h) hpre, herr, heq⟩
    | printString h =>
      obtain ⟨pc, σ, am, hpre, herr, heq⟩ := ih _ _ _ rfl _ _ hc'
      exact ⟨pc, σ, am, Steps.step (Step.printString (am := am₀) h) hpre, herr, heq⟩
    | arrLoad_boundsError h hidx hob =>
      cases rest with
      | refl => cases hc'; exact ⟨pc₀, σ₀, am₀, Steps.refl, Step.arrLoad_boundsError h hidx hob, rfl⟩
      | step s _ => exact absurd s Step.no_step_from_errorBounds
    | arrStore_boundsError h hidx hv hob =>
      cases rest with
      | refl => cases hc'; exact ⟨pc₀, σ₀, am₀, Steps.refl, Step.arrStore_boundsError h hidx hv hob, rfl⟩
      | step s _ => exact absurd s Step.no_step_from_errorBounds

theorem errorDiv_preservation (cert : PCertificate) (hvalid : PCertificateValid cert)
    (σ₀ : Store) (hts₀ : TypedStore cert.tyCtx σ₀) {σ_e : Store} {am₀ am_e : ArrayMem}
    (hreach : cert.trans ⊩ Cfg.run 0 σ₀ am₀ ⟶* Cfg.errorDiv σ_e am_e) :
    ∃ σ_o am_o', cert.orig ⊩ Cfg.run 0 σ₀ am₀ ⟶* Cfg.errorDiv σ_o am_o' := by
  obtain ⟨pc_t, σ_t, am_t, hrun, herr, rfl⟩ := steps_to_errorDiv_decompose hreach
  obtain ⟨pc_o, σ_o, a2, horig_prefix, hpc_eq, hrel, _, hinv_t, hinv_o, hts_o⟩ := simulation_trace hvalid hts₀ hrun
  have hpc := steps_run_in_bounds hvalid.step_closed hvalid.step_closed.1 hrun
  rw [← hpc_eq] at horig_prefix
  obtain ⟨σ_o', am_o', horig_err⟩ :=
    (hvalid.error_pres pc_t σ_t σ_o am_t a2 hpc hrel hinv_t (hpc_eq ▸ hinv_o) hts_o).1 herr
  exact ⟨σ_o', am_o', Steps.trans horig_prefix horig_err⟩

theorem errorBounds_preservation (cert : PCertificate) (hvalid : PCertificateValid cert)
    (σ₀ : Store) (hts₀ : TypedStore cert.tyCtx σ₀) {σ_e : Store} {am₀ am_e : ArrayMem}
    (hreach : cert.trans ⊩ Cfg.run 0 σ₀ am₀ ⟶* Cfg.errorBounds σ_e am_e) :
    ∃ σ_o am_o', cert.orig ⊩ Cfg.run 0 σ₀ am₀ ⟶* Cfg.errorBounds σ_o am_o' := by
  obtain ⟨pc_t, σ_t, am_t, hrun, herr, rfl⟩ := steps_to_errorBounds_decompose hreach
  obtain ⟨pc_o, σ_o, a2, horig_prefix, hpc_eq, hrel, _, hinv_t, hinv_o, hts_o⟩ := simulation_trace hvalid hts₀ hrun
  have hpc := steps_run_in_bounds hvalid.step_closed hvalid.step_closed.1 hrun
  rw [← hpc_eq] at horig_prefix
  obtain ⟨σ_o', am_o', horig_err⟩ :=
    (hvalid.error_pres pc_t σ_t σ_o am_t a2 hpc hrel hinv_t (hpc_eq ▸ hinv_o) hts_o).2 herr
  exact ⟨σ_o', am_o', Steps.trans horig_prefix horig_err⟩

/-- Cause-agnostic wrapper: an error reached in trans (either kind) is
    reached in orig with the same cause. -/
theorem error_preservation (cert : PCertificate) (hvalid : PCertificateValid cert)
    (σ₀ : Store) (hts₀ : TypedStore cert.tyCtx σ₀) {σ_e : Store} {am₀ am_e : ArrayMem}
    (hreach : (cert.trans ⊩ Cfg.run 0 σ₀ am₀ ⟶* Cfg.errorDiv σ_e am_e) ∨
              (cert.trans ⊩ Cfg.run 0 σ₀ am₀ ⟶* Cfg.errorBounds σ_e am_e)) :
    ∃ σ_o am_o', (cert.orig ⊩ Cfg.run 0 σ₀ am₀ ⟶* Cfg.errorDiv σ_o am_o') ∨
                 (cert.orig ⊩ Cfg.run 0 σ₀ am₀ ⟶* Cfg.errorBounds σ_o am_o') := by
  rcases hreach with hd | hb
  · obtain ⟨σ_o, am_o', hs⟩ := errorDiv_preservation cert hvalid σ₀ hts₀ hd
    exact ⟨σ_o, am_o', .inl hs⟩
  · obtain ⟨σ_o, am_o', hs⟩ := errorBounds_preservation cert hvalid σ₀ hts₀ hb
    exact ⟨σ_o, am_o', .inr hs⟩

-- ============================================================
-- § Divergence preservation
-- ============================================================

theorem diverge_preservation (cert : PCertificate) (hvalid : PCertificateValid cert)
    (f : Nat → Cfg) (σ₀ : Store) (hts₀ : TypedStore cert.tyCtx σ₀)
    (hinf : IsInfiniteExec cert.trans f) (hf0 : f 0 = Cfg.run 0 σ₀ ArrayMem.init) :
    ∃ g : Nat → Cfg, IsInfiniteExec cert.orig g ∧ g 0 = Cfg.run 0 σ₀ ArrayMem.init :=
  soundness_diverge cert hvalid f σ₀ hts₀ hinf hf0

-- ============================================================
-- § Main soundness
-- ============================================================

theorem credible_compilation_soundness (cert : PCertificate) (hvalid : PCertificateValid cert)
    (σ₀ : Store) (hts₀ : TypedStore cert.tyCtx σ₀) (b : Behavior)
    (htrans : program_behavior cert.trans σ₀ b) :
    match b with
    | .halts σ_t => ∃ σ_o am_o am_f, haltsWithResult cert.orig 0 σ₀ σ_o am_o am_f ∧
        ∀ v ∈ cert.observable, σ_t v = σ_o v
    | .errorDiv _ => ∃ σ_o am_o am_o',
        cert.orig ⊩ Cfg.run 0 σ₀ am_o ⟶* Cfg.errorDiv σ_o am_o'
    | .errorBounds _ => ∃ σ_o am_o am_o',
        cert.orig ⊩ Cfg.run 0 σ₀ am_o ⟶* Cfg.errorBounds σ_o am_o'
    | .typeErrors _ => False
    | .diverges => ∃ f, IsInfiniteExec cert.orig f ∧ f 0 = Cfg.run 0 σ₀ ArrayMem.init := by
  cases b with
  | halts σ_t' =>
    obtain ⟨am, am', h⟩ := htrans
    obtain ⟨σ_o, am_f, hhalt, _, hobs⟩ := soundness_halt cert hvalid σ₀ σ_t' hts₀ (am₀ := am) ⟨am', h⟩
    exact ⟨σ_o, am, am_f, hhalt, hobs⟩
  | errorDiv σ_e =>
    obtain ⟨am, am', h⟩ := htrans
    obtain ⟨σ_o, am_o', ho⟩ := errorDiv_preservation cert hvalid σ₀ hts₀ h
    exact ⟨σ_o, am, am_o', ho⟩
  | errorBounds σ_e =>
    obtain ⟨am, am', h⟩ := htrans
    obtain ⟨σ_o, am_o', ho⟩ := errorBounds_preservation cert hvalid σ₀ hts₀ h
    exact ⟨σ_o, am, am_o', ho⟩
  | typeErrors σ_e =>
    obtain ⟨am, am', h⟩ := htrans
    have hwt : WellTypedProg cert.tyCtx cert.trans := by
      exact hvalid.well_typed_trans
    exact absurd h (type_safety hwt hts₀ hvalid.step_closed)
  | diverges => obtain ⟨f, hinf, hf0⟩ := htrans; exact soundness_diverge cert hvalid f σ₀ hts₀ hinf hf0

theorem credible_compilation_total (cert : PCertificate) (hvalid : PCertificateValid cert)
    (σ₀ : Store) (hts₀ : TypedStore cert.tyCtx σ₀) :
    ∃ b, program_behavior cert.trans σ₀ b ∧
      match b with
      | .halts σ_t => ∃ σ_o am_o am_f, haltsWithResult cert.orig 0 σ₀ σ_o am_o am_f ∧
          ∀ v ∈ cert.observable, σ_t v = σ_o v
      | .errorDiv _ => ∃ σ_o am_o am_o',
          cert.orig ⊩ Cfg.run 0 σ₀ am_o ⟶* Cfg.errorDiv σ_o am_o'
      | .errorBounds _ => ∃ σ_o am_o am_o',
          cert.orig ⊩ Cfg.run 0 σ₀ am_o ⟶* Cfg.errorBounds σ_o am_o'
      | .typeErrors _ => False
      | .diverges => ∃ f, IsInfiniteExec cert.orig f ∧ f 0 = Cfg.run 0 σ₀ ArrayMem.init := by
  obtain ⟨b, hb⟩ := has_behavior cert.trans σ₀ hvalid.step_closed
  refine ⟨b, hb, ?_⟩
  cases b with
  | halts σ_t =>
    obtain ⟨am, am', h⟩ := hb
    obtain ⟨σ_o, am_f, hhalt, _, hobs⟩ := soundness_halt cert hvalid σ₀ σ_t hts₀ (am₀ := am) ⟨am', h⟩
    exact ⟨σ_o, am, am_f, hhalt, hobs⟩
  | errorDiv σ_e =>
    obtain ⟨am, am', h⟩ := hb
    obtain ⟨σ_o, am_o', ho⟩ := errorDiv_preservation cert hvalid σ₀ hts₀ h
    exact ⟨σ_o, am, am_o', ho⟩
  | errorBounds σ_e =>
    obtain ⟨am, am', h⟩ := hb
    obtain ⟨σ_o, am_o', ho⟩ := errorBounds_preservation cert hvalid σ₀ hts₀ h
    exact ⟨σ_o, am, am_o', ho⟩
  | typeErrors σ_e =>
    obtain ⟨am, am', h⟩ := hb
    have hwt : WellTypedProg cert.tyCtx cert.trans := by
      exact hvalid.well_typed_trans
    exact absurd h (type_safety hwt hts₀ hvalid.step_closed)
  | diverges =>
    obtain ⟨f, hinf, hf0⟩ := hb
    exact soundness_diverge cert hvalid f σ₀ hts₀ hinf hf0
