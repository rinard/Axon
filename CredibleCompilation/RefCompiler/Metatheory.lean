-- Copyright (c) 2026 Martin Rinard
import CredibleCompilation.RefCompiler.ErrorHandling

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

-- Helper: Prop-level safe implies Bool-level isSafe
theorem SExpr.isSafe_of_safe (e : SExpr) (σ : Store) (am : ArrayMem)
    (decls : List (ArrayName × Nat × VarTy))
    (h : e.safe σ am decls) : e.isSafe σ am decls = true := by
  induction e with
  | lit _ => simp [SExpr.isSafe]
  | var _ => simp [SExpr.isSafe]
  | bin op a b iha ihb =>
    cases op <;> simp_all [SExpr.safe, SExpr.isSafe, decide_eq_true_eq]
  | arrRead arr idx ih =>
    simp [SExpr.safe] at h; simp [SExpr.isSafe, ih h.1, decide_eq_true_eq, h.2]
  | flit _ => simp [SExpr.isSafe]
  | fbin _ a b iha ihb =>
    simp [SExpr.safe] at h; simp [SExpr.isSafe, iha h.1, ihb h.2]
  | intToFloat e ih =>
    simp [SExpr.safe] at h; simp [SExpr.isSafe, ih h]
  | floatToInt e ih =>
    simp [SExpr.safe] at h; simp [SExpr.isSafe, ih h]
  | floatUnary op e ih =>
    simp [SExpr.safe] at h; simp [SExpr.isSafe, ih h]
  | farrRead arr idx ih =>
    simp [SExpr.safe] at h; simp [SExpr.isSafe, ih h.1, decide_eq_true_eq, h.2]

theorem SBool.isSafe_of_safe (sb : SBool) (σ : Store) (am : ArrayMem)
    (decls : List (ArrayName × Nat × VarTy))
    (h : sb.safe σ am decls) : sb.isSafe σ am decls = true := by
  induction sb with
  | lit _ => simp [SBool.isSafe]
  | bvar _ => simp [SBool.isSafe]
  | cmp _ a b =>
    simp [SBool.safe] at h; simp [SBool.isSafe, SExpr.isSafe_of_safe a σ am decls h.1, SExpr.isSafe_of_safe b σ am decls h.2]
  | not e ih =>
    simp [SBool.safe] at h; simp [SBool.isSafe, ih h]
  | and a b iha ihb =>
    simp [SBool.safe] at h
    simp only [SBool.isSafe, iha h.1, Bool.true_and]
    split <;> simp_all
  | or a b iha ihb =>
    simp [SBool.safe] at h
    simp only [SBool.isSafe, iha h.1, Bool.true_and]
    split <;> simp_all
  | barrRead arr idx =>
    simp [SBool.safe] at h
    have hih := SExpr.isSafe_of_safe idx σ am decls h.1
    simp [SBool.isSafe, hih, decide_eq_true_eq, h.2]
  | fcmp _ a b =>
    simp [SBool.safe] at h
    simp [SBool.isSafe, SExpr.isSafe_of_safe a σ am decls h.1, SExpr.isSafe_of_safe b σ am decls h.2]

private theorem Stmt.interp_ne_none_of_safe_assign (x : Var) (e : SExpr) (σ : Store) (am : ArrayMem)
    (decls : List (ArrayName × Nat × VarTy))
    (hsafe : (Stmt.assign x e).safe 0 σ am decls) :
    (Stmt.assign x e).interp 0 σ am decls ≠ none := by
  simp only [Stmt.safe] at hsafe
  simp [Stmt.interp, SExpr.isSafe_of_safe e σ am decls hsafe]

private theorem Stmt.interp_ne_none_of_safe_bassign (x : Var) (b : SBool) (σ : Store) (am : ArrayMem)
    (decls : List (ArrayName × Nat × VarTy))
    (hsafe : (Stmt.bassign x b).safe 0 σ am decls) :
    (Stmt.bassign x b).interp 0 σ am decls ≠ none := by
  simp only [Stmt.safe] at hsafe
  simp [Stmt.interp, SBool.isSafe_of_safe b σ am decls hsafe]

private theorem Stmt.interp_ne_none_of_safe_arrWrite (arr : ArrayName) (idx val : SExpr) (σ : Store) (am : ArrayMem)
    (decls : List (ArrayName × Nat × VarTy))
    (hsafe : (Stmt.arrWrite arr idx val).safe 0 σ am decls) :
    (Stmt.arrWrite arr idx val).interp 0 σ am decls ≠ none := by
  simp only [Stmt.safe] at hsafe
  simp [Stmt.interp, SExpr.isSafe_of_safe idx σ am decls hsafe.1,
        SExpr.isSafe_of_safe val σ am decls hsafe.2.1, decide_eq_true_eq, hsafe.2.2]

private theorem Stmt.interp_ne_none_of_safe_barrWrite (arr : ArrayName) (idx : SExpr) (bval : SBool) (σ : Store) (am : ArrayMem)
    (decls : List (ArrayName × Nat × VarTy))
    (hsafe : (Stmt.barrWrite arr idx bval).safe 0 σ am decls) :
    (Stmt.barrWrite arr idx bval).interp 0 σ am decls ≠ none := by
  simp only [Stmt.safe] at hsafe
  simp [Stmt.interp, SExpr.isSafe_of_safe idx σ am decls hsafe.1,
        SBool.isSafe_of_safe bval σ am decls hsafe.2.1, decide_eq_true_eq, hsafe.2.2]

private theorem Stmt.interp_ne_none_of_safe_fassign (x : Var) (e : SExpr) (σ : Store) (am : ArrayMem)
    (decls : List (ArrayName × Nat × VarTy))
    (hsafe : (Stmt.fassign x e).safe 0 σ am decls) :
    (Stmt.fassign x e).interp 0 σ am decls ≠ none := by
  simp only [Stmt.safe] at hsafe
  simp [Stmt.interp, SExpr.isSafe_of_safe e σ am decls hsafe]

private theorem Stmt.interp_ne_none_of_safe_farrWrite (arr : ArrayName) (idx val : SExpr) (σ : Store) (am : ArrayMem)
    (decls : List (ArrayName × Nat × VarTy))
    (hsafe : (Stmt.farrWrite arr idx val).safe 0 σ am decls) :
    (Stmt.farrWrite arr idx val).interp 0 σ am decls ≠ none := by
  simp only [Stmt.safe] at hsafe
  simp [Stmt.interp, SExpr.isSafe_of_safe idx σ am decls hsafe.1,
        SExpr.isSafe_of_safe val σ am decls hsafe.2.1, decide_eq_true_eq, hsafe.2.2]

/-!
# Reference Compiler: Metatheory

Step-indexed execution (RefStepsN), fuel monotonicity,
safe/typedVars anti-monotonicity, and divergence theorems.
-/

-- ============================================================
-- § 17. Step-indexed execution (RefStepsN)
-- ============================================================

/-- Step-indexed multi-step relation: exactly `n` steps. -/
inductive RefStepsN (p : Prog) : Nat → Cfg → Cfg → Prop where
  | refl : RefStepsN p 0 c c
  | step : Step p c c' → RefStepsN p n c' c'' → RefStepsN p (n + 1) c c''

theorem RefStepsN.to_Steps {p : Prog} {n : Nat} {c c' : Cfg}
    (h : RefStepsN p n c c') : p ⊩ c ⟶* c' := by
  induction h with
  | refl => exact Steps.refl
  | step s _ ih => exact Steps.step s ih
theorem Steps.to_RefStepsN {p : Prog} {c c' : Cfg}
    (h : p ⊩ c ⟶* c') : ∃ n, RefStepsN p n c c' := by
  induction h with
  | refl => exact ⟨0, .refl⟩
  | step s _ ih => obtain ⟨n, hn⟩ := ih; exact ⟨n + 1, .step s hn⟩
private theorem refStepsN_cast {p : Prog} {n n' : Nat} {c c' : Cfg}
    (h : RefStepsN p n c c') (heq : n = n') : RefStepsN p n' c c' := heq ▸ h

theorem RefStepsN.trans {p : Prog} {n m : Nat} {c c' c'' : Cfg}
    (h₁ : RefStepsN p n c c') (h₂ : RefStepsN p m c' c'') :
    RefStepsN p (n + m) c c'' := by
  induction h₁ with
  | refl => simpa using h₂
  | step s _ ih => exact refStepsN_cast (.step s (ih h₂)) (by omega)
theorem RefStepsN.det_prefix {p : Prog} {n m : Nat} {c c₁ c₂ : Cfg}
    (h₁ : RefStepsN p n c c₁) (h₂ : RefStepsN p m c c₂) (hle : n ≤ m) :
    RefStepsN p (m - n) c₁ c₂ := by
  induction h₁ generalizing m c₂ with
  | refl => simpa using h₂
  | step s _ ih =>
    cases h₂ with
    | refl => omega
    | step s' rest =>
      have := Step.deterministic s s'; subst this
      exact refStepsN_cast (ih rest (by omega)) (by omega)
/-- A halted config cannot take a step in RefStepsN. -/
theorem RefStepsN.no_step_halt {p : Prog} {n : Nat} {σ : Store} {c : Cfg}
    (h : RefStepsN p (n + 1) (Cfg.halt σ _xam) c) : False := by
  cases h with
  | step s _ => exact Step.no_step_from_halt s
/-- If execution takes unbounded steps through `run` configs, it cannot halt. -/
theorem no_halt_of_unbounded {p : Prog} {pc : Nat} {σ : Store} {am : ArrayMem}
    (hunbounded : ∀ N, ∃ n, n ≥ N ∧ ∃ pc' σ',
      RefStepsN p n (Cfg.run pc σ am) (Cfg.run pc' σ' am)) :
    ∀ σ' am', ¬ haltsWithResult p pc σ σ' am am' := by
  intro σ' am' hhalt
  obtain ⟨n, hn⟩ := hhalt.to_RefStepsN
  obtain ⟨m, hm, pc', σ'', hrun⟩ := hunbounded (n + 1)
  have hsuffix := RefStepsN.det_prefix hn hrun (by omega : n ≤ m)
  exact RefStepsN.no_step_halt (refStepsN_cast hsuffix (by omega : m - n = (m - n - 1) + 1))
/-- Variant of `no_halt_of_unbounded` where the array memory can change at each step. -/
theorem no_halt_of_unbounded_am {p : Prog} {pc : Nat} {σ : Store} {am : ArrayMem}
    (hunbounded : ∀ N, ∃ n, n ≥ N ∧ ∃ pc' σ' am',
      RefStepsN p n (Cfg.run pc σ am) (Cfg.run pc' σ' am')) :
    ∀ σ' am', ¬ haltsWithResult p pc σ σ' am am' := by
  intro σ' am' hhalt
  obtain ⟨n, hn⟩ := hhalt.to_RefStepsN
  obtain ⟨m, hm, pc', σ'', am'', hrun⟩ := hunbounded (n + 1)
  have hsuffix := RefStepsN.det_prefix hn hrun (by omega : n ≤ m)
  exact RefStepsN.no_step_halt (refStepsN_cast hsuffix (by omega : m - n = (m - n - 1) + 1))
-- ============================================================
-- § 18. Fuel monotonicity
-- ============================================================

/-- If the interpreter terminates at some fuel, it terminates with the same
    result at one more fuel. -/
theorem Stmt.interp_fuel_succ (s : Stmt) :
    ∀ fuel σ am decls r, s.interp fuel σ am decls = some r → s.interp (fuel + 1) σ am decls = some r := by
  induction s with
  | skip | assign _ _ | bassign _ _ | arrWrite _ _ _ | barrWrite _ _ _ | fassign _ _ | farrWrite _ _ _ | label _ | goto _ | ifgoto _ _ | print _ _ | printInt _ | printBool _ | printFloat _ | printString _ =>
    intro fuel σ am decls r h; simp only [Stmt.interp] at h ⊢; exact h
  | seq s1 s2 ih1 ih2 =>
    intro fuel σ am decls r h
    simp only [Stmt.interp] at h ⊢
    cases h1 : s1.interp fuel σ am decls with
    | none => simp [h1] at h
    | some p =>
      obtain ⟨σ₁, am₁⟩ := p
      simp [h1] at h
      simp [ih1 fuel σ am decls _ h1]
      exact ih2 fuel σ₁ am₁ decls r h
  | ite b s1 s2 ih1 ih2 =>
    intro fuel σ am decls r h
    simp only [Stmt.interp] at h ⊢
    cases hs : b.isSafe σ am decls <;> simp [hs] at h ⊢
    cases heval : b.eval σ am <;> simp [heval] at h ⊢
    · exact ih2 fuel σ am decls r h
    · exact ih1 fuel σ am decls r h
  | loop b body ihb =>
    intro fuel
    induction fuel with
    | zero => intro σ am decls r h; simp [Stmt.interp.eq_8] at h
    | succ fuel' ih_fuel =>
      intro σ am decls r h
      rw [Stmt.interp.eq_9] at h
      rw [Stmt.interp.eq_9]
      cases hs : b.isSafe σ am decls <;> simp [hs] at h ⊢
      cases heval : b.eval σ am <;> simp [heval] at h ⊢
      · exact h
      · cases hb : body.interp fuel' σ am decls with
        | none => simp [hb] at h
        | some p =>
          obtain ⟨σ₁, am₁⟩ := p
          simp [hb] at h
          simp [ihb fuel' σ am decls _ hb]
          exact ih_fuel σ₁ am₁ decls r h
/-- Fuel monotonicity: success at `fuel` implies success at `fuel + k`. -/
theorem Stmt.interp_fuel_mono (s : Stmt) (fuel k : Nat) (σ : Store) (am : ArrayMem)
    (decls : List (ArrayName × Nat × VarTy)) (r : Store × ArrayMem)
    (h : s.interp fuel σ am decls = some r) : s.interp (fuel + k) σ am decls = some r := by
  induction k with
  | zero => simpa using h
  | succ k ih => rw [show fuel + (k + 1) = (fuel + k) + 1 from by omega]; exact s.interp_fuel_succ _ _ _ _ _ ih
/-- Contrapositive of fuel monotonicity: `none` at higher fuel implies `none`
    at lower fuel. -/
theorem Stmt.interp_none_of_le (s : Stmt) (fuel fuel' : Nat) (σ : Store) (am : ArrayMem)
    (decls : List (ArrayName × Nat × VarTy))
    (h : s.interp fuel' σ am decls = none) (hle : fuel ≤ fuel') : s.interp fuel σ am decls = none := by
  by_contra hc; push_neg at hc
  obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.mp hc
  have := s.interp_fuel_mono fuel (fuel' - fuel) σ am decls r hr
  rw [show fuel + (fuel' - fuel) = fuel' from by omega] at this
  simp [this] at h
-- ============================================================
-- § 19. safe anti-monotonicity
-- ============================================================

/-- `safe` at higher fuel implies `safe` at lower fuel. -/
theorem Stmt.safe_fuel_succ (s : Stmt) :
    ∀ fuel σ am decls, s.safe (fuel + 1) σ am decls → s.safe fuel σ am decls := by
  induction s with
  | skip | assign _ _ | bassign _ _ | arrWrite _ _ _ | barrWrite _ _ _ | fassign _ _ | farrWrite _ _ _ | label _ | goto _ | ifgoto _ _ | print _ _ | printInt _ | printBool _ | printFloat _ | printString _ =>
    intro fuel σ am decls h; simp only [Stmt.safe] at h ⊢; try exact h
  | seq s1 s2 ih1 ih2 =>
    intro fuel σ am decls h
    simp only [Stmt.safe] at h ⊢
    obtain ⟨h1, h2⟩ := h
    refine ⟨ih1 fuel σ am decls h1, ?_⟩
    cases h_interp : s1.interp fuel σ am decls with
    | none => trivial
    | some p =>
      obtain ⟨σ₁, am₁⟩ := p
      have h_interp' := s1.interp_fuel_succ fuel σ am decls _ h_interp
      simp [h_interp'] at h2
      exact ih2 fuel σ₁ am₁ decls h2
  | ite b s1 s2 ih1 ih2 =>
    intro fuel σ am decls h
    simp only [Stmt.safe] at h ⊢
    obtain ⟨hb, h_branch⟩ := h
    refine ⟨hb, ?_⟩
    cases heval : b.eval σ am <;> simp [heval] at h_branch ⊢
    · exact ih2 fuel σ am decls h_branch
    · exact ih1 fuel σ am decls h_branch
  | loop b body ihb =>
    intro fuel
    induction fuel with
    | zero => intro σ am decls _; simp [Stmt.safe.eq_8]
    | succ fuel' ih_fuel =>
      intro σ am decls h
      rw [Stmt.safe.eq_9] at h
      rw [Stmt.safe.eq_9]
      obtain ⟨hbs, h_cond⟩ := h
      refine ⟨hbs, ?_⟩
      cases heval : b.eval σ am
      · simp [heval] at h_cond ⊢
      · simp [heval] at h_cond ⊢
        obtain ⟨h_body_safe, h_rest⟩ := h_cond
        refine ⟨ihb fuel' σ am decls h_body_safe, ?_⟩
        cases h_interp : body.interp fuel' σ am decls with
        | none => trivial
        | some p =>
          obtain ⟨σ₁, am₁⟩ := p
          have h_interp' := body.interp_fuel_succ fuel' σ am decls _ h_interp
          simp [h_interp'] at h_rest
          exact ih_fuel σ₁ am₁ decls h_rest
theorem Stmt.safe_of_le (s : Stmt) (fuel fuel' : Nat) (σ : Store) (am : ArrayMem)
    (decls : List (ArrayName × Nat × VarTy))
    (h : s.safe fuel' σ am decls) (hle : fuel ≤ fuel') : s.safe fuel σ am decls := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
  induction k with
  | zero => exact h
  | succ k ih =>
    apply ih
    · exact s.safe_fuel_succ (fuel + k) σ am decls (by rwa [show fuel + (k + 1) = (fuel + k) + 1 from by omega] at h)
    · omega
-- ============================================================
-- § 19c. typedVars anti-monotonicity
-- ============================================================

/-- `typedVars` at higher fuel implies `typedVars` at lower fuel. -/
theorem Stmt.typedVars_fuel_succ (s : Stmt) :
    ∀ fuel σ am decls, s.typedVars (fuel + 1) σ am decls → s.typedVars fuel σ am decls := by
  induction s with
  | skip | assign _ _ | bassign _ _ | arrWrite _ _ _ | barrWrite _ _ _ | fassign _ _ | farrWrite _ _ _ | label _ | goto _ | ifgoto _ _ | print _ _ | printInt _ | printBool _ | printFloat _ | printString _ =>
    intro fuel σ am decls h; simp only [Stmt.typedVars] at h ⊢; try exact h
  | seq s1 s2 ih1 ih2 =>
    intro fuel σ am decls h
    simp only [Stmt.typedVars] at h ⊢
    obtain ⟨h1, h2⟩ := h
    refine ⟨ih1 fuel σ am decls h1, ?_⟩
    cases h_interp : s1.interp fuel σ am decls with
    | none => trivial
    | some p =>
      obtain ⟨σ₁, am₁⟩ := p
      have h_interp' := s1.interp_fuel_succ fuel σ am decls _ h_interp
      simp [h_interp'] at h2
      exact ih2 fuel σ₁ am₁ decls h2
  | ite b s1 s2 ih1 ih2 =>
    intro fuel σ am decls h
    simp only [Stmt.typedVars] at h ⊢
    obtain ⟨hb, h_branch⟩ := h
    refine ⟨hb, ?_⟩
    cases heval : b.eval σ am <;> simp [heval] at h_branch ⊢
    · exact ih2 fuel σ am decls h_branch
    · exact ih1 fuel σ am decls h_branch
  | loop b body ihb =>
    intro fuel
    induction fuel with
    | zero => intro σ am decls _; simp [Stmt.typedVars.eq_8]
    | succ fuel' ih_fuel =>
      intro σ am decls h
      rw [Stmt.typedVars.eq_9] at h
      rw [Stmt.typedVars.eq_9]
      obtain ⟨hbs, h_cond⟩ := h
      refine ⟨hbs, ?_⟩
      cases heval : b.eval σ am
      · simp [heval] at h_cond ⊢
      · simp [heval] at h_cond ⊢
        obtain ⟨h_body_tv, h_rest⟩ := h_cond
        refine ⟨ihb fuel' σ am decls h_body_tv, ?_⟩
        cases h_interp : body.interp fuel' σ am decls with
        | none => trivial
        | some p =>
          obtain ⟨σ₁, am₁⟩ := p
          have h_interp' := body.interp_fuel_succ fuel' σ am decls _ h_interp
          simp [h_interp'] at h_rest
          exact ih_fuel σ₁ am₁ decls h_rest

theorem Stmt.typedVars_of_le (s : Stmt) (fuel fuel' : Nat) (σ : Store) (am : ArrayMem)
    (decls : List (ArrayName × Nat × VarTy))
    (h : s.typedVars fuel' σ am decls) (hle : fuel ≤ fuel') : s.typedVars fuel σ am decls := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
  induction k with
  | zero => exact h
  | succ k ih =>
    apply ih
    · exact s.typedVars_fuel_succ (fuel + k) σ am decls (by rwa [show fuel + (k + 1) = (fuel + k) + 1 from by omega] at h)
    · omega

-- ============================================================
-- § 20. Divergence theorems
-- ============================================================

set_option maxHeartbeats 1600000

/-- One iteration of a divergent loop: execute bool, ifgoto (fall through),
    body, goto back to condLabel. Returns RefStepsN and updated state. -/
private theorem loop_one_iter
    (b : SBool) (body : Stmt) (fuel₀ : Nat) (σ σ₁ : Store) (am am₁ : ArrayMem)
    (offset nextTmp : Nat) (p : Prog) (σ_tac : Store)
    (htmpfree : (Stmt.loop b body).tmpFree)
    (hftmpfree : (Stmt.loop b body).ftmpFree)
    (hbtmpfree : (Stmt.loop b body).btmpFree)
    (hb : b.eval σ am = true)
    (hbds : SBool.safe σ am p.arrayDecls b)
    (htypedv_b : b.typedVars σ am)
    (hbody_res : body.interp fuel₀ σ am p.arrayDecls = some (σ₁, am₁))
    (hds_body : body.safe fuel₀ σ am p.arrayDecls)
    (htypedv_body : body.typedVars fuel₀ σ am p.arrayDecls)
    (hNoGoto : body.noGoto)
    (hagree : ∀ v, v.isTmp = false → v.isFTmp = false → v.isBTmp = false → σ_tac v = σ v)
    (labels : List (String × Nat) := [])
    (hcode : RC.CodeAt (compileStmt (.loop b body) offset nextTmp labels).1 p offset) :
    ∃ σ₁_tac k,
      RefStepsN p k (Cfg.run offset σ_tac am) (Cfg.run offset σ₁_tac am₁) ∧
      (∀ v, v.isTmp = false → v.isFTmp = false → v.isBTmp = false → σ₁_tac v = σ₁ v) ∧ 1 ≤ k := by
  -- Destructure the compiled code for the loop
  dsimp only [compileStmt] at hcode
  generalize hrcb : compileBool b offset nextTmp = rcb at hcode
  obtain ⟨codeBool, be, tmpB⟩ := rcb
  generalize hrcbody : compileStmt body (offset + codeBool.length + 1) tmpB labels = rcbody at hcode
  obtain ⟨codeBody, tmpBody⟩ := rcbody
  simp only [] at hcode
  -- Extract sub-proofs
  have htf_b : ∀ v ∈ b.freeVars, v.isTmp = false :=
    fun v hv => htmpfree v (List.mem_append_left _ hv)
  have hftf_b : ∀ v ∈ b.freeVars, v.isFTmp = false :=
    fun v hv => hftmpfree v (List.mem_append_left _ hv)
  have htbf_b : ∀ v ∈ b.freeVars, v.isBTmp = false :=
    fun v hv => hbtmpfree v (List.mem_append_left _ hv)
  have htf_body : body.tmpFree :=
    fun v hv => htmpfree v (List.mem_append_right _ hv)
  have hftf_body : body.ftmpFree :=
    fun v hv => hftmpfree v (List.mem_append_right _ hv)
  have hbtf_body : body.btmpFree :=
    fun v hv => hbtmpfree v (List.mem_append_right _ hv)
  have hcb : RC.CodeAt (compileBool b offset nextTmp).1 p offset := by
    rw [hrcb]; exact hcode.left.left.left
  -- Step 1: Execute bool
  obtain ⟨σ_bool, hexec_bool, heval_bool, hntmp_bool, _⟩ :=
    compileBool_correct b offset nextTmp σ σ_tac am p htf_b hftf_b htbf_b htypedv_b hbds hagree hcb
  rw [hrcb] at hexec_bool heval_bool; simp at hexec_bool heval_bool
  have hagree_bool : ∀ v, v.isTmp = false → v.isFTmp = false → v.isBTmp = false → σ_bool v = σ v := by
    intro v hv hfv hbv; rw [hntmp_bool v hv hfv hbv]; exact hagree v hv hfv hbv
  -- Step 2: ifgoto (.not be) falls through (condition is true)
  have hifg : p[offset + codeBool.length]? =
      some (.ifgoto (.not be) (offset + codeBool.length + 1 + codeBody.length + 1)) := by
    have := hcode.left.left.right.head
    simp only [List.length_append, List.length_cons, List.length_nil] at this; exact this
  have hnotbe : (BoolExpr.not be).eval σ_bool am = false := by
    simp [BoolExpr.eval, heval_bool, hb]
  have hexec_if := FragExec.single_iffalse (am := am) hifg hnotbe
  -- Step 3: Execute body
  have hcbody : RC.CodeAt (compileStmt body (offset + codeBool.length + 1) tmpB labels).1 p
      (offset + codeBool.length + 1) := by
    rw [hrcbody]; have := hcode.left.right
    simp only [List.length_append, List.length_cons, List.length_nil] at this
    rwa [show offset + (codeBool.length + 1) = offset + codeBool.length + 1 from by omega] at this
  obtain ⟨σ_body, hexec_body, hagree_body⟩ :=
    compileStmt_correct body fuel₀ σ σ₁ am am₁ (offset + codeBool.length + 1) tmpB p
      σ_bool hbody_res htf_body hftf_body hbtf_body hNoGoto hds_body htypedv_body hagree_bool (labels := labels) hcbody
  rw [hrcbody] at hexec_body; simp at hexec_body
  -- Step 4: goto back to condLabel
  have hgoto_back : p[offset + codeBool.length + 1 + codeBody.length]? =
      some (.goto offset) := by
    have := hcode.right.head
    simp only [List.length_append, List.length_cons, List.length_nil] at this
    rwa [show offset + (codeBool.length + 1 + codeBody.length) =
        offset + codeBool.length + 1 + codeBody.length from by omega] at this
  have hexec_goto := FragExec.single_goto (am := am₁) hgoto_back (σ := σ_body)
  -- Compose all steps: use the goto step explicitly to guarantee k ≥ 1
  have hexec_pre := FragExec.trans'
    (FragExec.trans' hexec_bool hexec_if) hexec_body
  obtain ⟨k_pre, hk_pre⟩ := hexec_pre.to_RefStepsN
  -- The goto is exactly 1 step
  have hgoto_step : Step p (Cfg.run (offset + codeBool.length + 1 + codeBody.length) σ_body am₁)
      (Cfg.run offset σ_body am₁) := Step.goto hgoto_back
  have hk : RefStepsN p (k_pre + 1) (Cfg.run offset σ_tac am) (Cfg.run offset σ_body am₁) :=
    RefStepsN.trans hk_pre (.step hgoto_step .refl)
  exact ⟨σ_body, k_pre + 1, hk, hagree_body, by omega⟩
/-- Main divergence: a divergent, safe statement produces unbounded steps. -/
theorem compileStmt_diverges (s : Stmt) (σ : Store) (am : ArrayMem)
    (offset nextTmp : Nat) (p : Prog) (σ_tac : Store)
    (htmpfree : s.tmpFree)
    (hftmpfree : s.ftmpFree)
    (hbtmpfree : s.btmpFree)
    (hNoGoto : s.noGoto)
    (hdiv : ∀ fuel, s.interp fuel σ am p.arrayDecls = none)
    (hsafe : ∀ fuel, s.safe fuel σ am p.arrayDecls)
    (htypedv : ∀ fuel, s.typedVars fuel σ am p.arrayDecls)
    (hagree : ∀ v, v.isTmp = false → v.isFTmp = false → v.isBTmp = false → σ_tac v = σ v)
    (labels : List (String × Nat) := [])
    (hcode : RC.CodeAt (compileStmt s offset nextTmp labels).1 p offset) :
    ∀ N, ∃ n, n ≥ N ∧ ∃ pc' σ' am', RefStepsN p n (Cfg.run offset σ_tac am) (Cfg.run pc' σ' am') := by
  induction s generalizing σ am offset nextTmp σ_tac with
  | skip => exact absurd (hdiv 0) (by simp [Stmt.interp])
  | label _ => exact absurd (hdiv 0) (by simp [Stmt.interp])
  | assign x e =>
    have := SExpr.isSafe_of_safe e σ am p.arrayDecls (by simpa [Stmt.safe] using hsafe 0)
    exact absurd (hdiv 0) (by simp [Stmt.interp, this])
  | bassign x b =>
    have := SBool.isSafe_of_safe b σ am p.arrayDecls (by simpa [Stmt.safe] using hsafe 0)
    exact absurd (hdiv 0) (by simp [Stmt.interp, this])
  | fassign x e =>
    have := SExpr.isSafe_of_safe e σ am p.arrayDecls (by simpa [Stmt.safe] using hsafe 0)
    exact absurd (hdiv 0) (by simp [Stmt.interp, this])
  | arrWrite arr idx val =>
    simp only [Stmt.safe] at hsafe; obtain ⟨hi, hv, hb⟩ := hsafe 0
    have h1 := SExpr.isSafe_of_safe idx σ am _ hi
    have h2 := SExpr.isSafe_of_safe val σ am _ hv
    exact absurd (hdiv 0) (by simp [Stmt.interp, h1, h2, decide_eq_true_eq.mpr hb])
  | barrWrite arr idx bval =>
    simp only [Stmt.safe] at hsafe; obtain ⟨hi, hv, hb⟩ := hsafe 0
    have h1 := SExpr.isSafe_of_safe idx σ am _ hi
    have h2 := SBool.isSafe_of_safe bval σ am _ hv
    exact absurd (hdiv 0) (by simp [Stmt.interp, h1, h2, decide_eq_true_eq.mpr hb])
  | farrWrite arr idx val =>
    simp only [Stmt.safe] at hsafe; obtain ⟨hi, hv, hb⟩ := hsafe 0
    have h1 := SExpr.isSafe_of_safe idx σ am _ hi
    have h2 := SExpr.isSafe_of_safe val σ am _ hv
    exact absurd (hdiv 0) (by simp [Stmt.interp, h1, h2, decide_eq_true_eq.mpr hb])
  | goto _ => exact absurd (hdiv 0) (by simp [Stmt.interp])
  | print _ args =>
    simp only [Stmt.safe] at hsafe
    have hall : (args.all fun e => e.isSafe σ am p.arrayDecls) = true := by
      rw [List.all_eq_true]; intro e he
      exact SExpr.isSafe_of_safe e σ am _ (hsafe 0 e he)
    exact absurd (hdiv 0) (by simp [Stmt.interp, hall])
  | printInt e =>
    have := SExpr.isSafe_of_safe e σ am p.arrayDecls (by simpa [Stmt.safe] using hsafe 0)
    exact absurd (hdiv 0) (by simp [Stmt.interp, this])
  | printBool b =>
    have := SBool.isSafe_of_safe b σ am p.arrayDecls (by simpa [Stmt.safe] using hsafe 0)
    exact absurd (hdiv 0) (by simp [Stmt.interp, this])
  | printFloat e =>
    have := SExpr.isSafe_of_safe e σ am p.arrayDecls (by simpa [Stmt.safe] using hsafe 0)
    exact absurd (hdiv 0) (by simp [Stmt.interp, this])
  | printString _ =>
    exact absurd (hdiv 0) (by simp [Stmt.interp])
  | ifgoto b _ =>
    have hbs := SBool.isSafe_of_safe b σ am p.arrayDecls (by simpa [Stmt.safe] using hsafe 0)
    exact absurd (hdiv 0) (by simp [Stmt.interp, hbs])
  | seq s1 s2 ih1 ih2 =>
    have htf1 : s1.tmpFree := fun v hv => htmpfree v (List.mem_append_left _ hv)
    have htf2 : s2.tmpFree := fun v hv => htmpfree v (List.mem_append_right _ hv)
    have hftf1 : s1.ftmpFree := fun v hv => hftmpfree v (List.mem_append_left _ hv)
    have hftf2 : s2.ftmpFree := fun v hv => hftmpfree v (List.mem_append_right _ hv)
    have hbtf1 : s1.btmpFree := fun v hv => hbtmpfree v (List.mem_append_left _ hv)
    have hbtf2 : s2.btmpFree := fun v hv => hbtmpfree v (List.mem_append_right _ hv)
    have hng1 : s1.noGoto := (hNoGoto : s1.noGoto ∧ s2.noGoto).1
    have hng2 : s2.noGoto := (hNoGoto : s1.noGoto ∧ s2.noGoto).2
    dsimp only [compileStmt] at hcode ⊢
    generalize hrc1 : compileStmt s1 offset nextTmp labels = rc1 at hcode ⊢
    obtain ⟨code1, tmp1⟩ := rc1
    generalize hrc2 : compileStmt s2 (offset + code1.length) tmp1 labels = rc2 at hcode ⊢
    obtain ⟨code2, tmp2⟩ := rc2; simp only [] at hcode ⊢
    by_cases hs1_div : ∀ fuel, s1.interp fuel σ am p.arrayDecls = none
    · -- s1 diverges
      have hs1_safe : ∀ fuel, s1.safe fuel σ am p.arrayDecls := by
        intro fuel; have h := hsafe fuel; simp only [Stmt.safe] at h; exact h.1
      have hs1_tv : ∀ fuel, s1.typedVars fuel σ am p.arrayDecls := by
        intro fuel; have h := htypedv fuel; simp only [Stmt.typedVars] at h; exact h.1
      intro N
      obtain ⟨n, hn, pc', σ', am', hsteps⟩ :=
        ih1 σ am offset nextTmp σ_tac htf1 hftf1 hbtf1 hng1 hs1_div hs1_safe hs1_tv hagree
          (by rw [hrc1]; exact hcode.left) N
      exact ⟨n, hn, pc', σ', am', hsteps⟩
    · -- s1 terminates for some fuel
      push_neg at hs1_div; obtain ⟨f₀, hf₀_ne⟩ := hs1_div
      obtain ⟨r, hf₀⟩ := Option.ne_none_iff_exists'.mp hf₀_ne
      obtain ⟨σ₁, am₁⟩ := r
      have hs1_safe : s1.safe f₀ σ am p.arrayDecls := by
        have h := hsafe f₀; simp only [Stmt.safe] at h; exact h.1
      have hs1_tv : s1.typedVars f₀ σ am p.arrayDecls := by
        have h := htypedv f₀; simp only [Stmt.typedVars] at h; exact h.1
      -- Execute s1
      obtain ⟨σ_1, hexec_1, hagree_1⟩ :=
        compileStmt_correct s1 f₀ σ σ₁ am am₁ offset nextTmp p σ_tac hf₀ htf1 hftf1 hbtf1 hng1
          hs1_safe hs1_tv hagree (labels := labels) (by rw [hrc1]; exact hcode.left)
      rw [hrc1] at hexec_1; simp at hexec_1
      obtain ⟨k₁, hk₁⟩ := hexec_1.to_RefStepsN
      -- s2 diverges
      have hs2_div : ∀ fuel, s2.interp fuel σ₁ am₁ p.arrayDecls = none := by
        intro fuel
        have h := hdiv (max f₀ fuel)
        simp only [Stmt.interp, bind, Option.bind] at h
        have := Stmt.interp_fuel_mono s1 f₀ (max f₀ fuel - f₀) σ am p.arrayDecls _ hf₀
        rw [show f₀ + (max f₀ fuel - f₀) = max f₀ fuel from by omega] at this
        simp [this] at h
        exact Stmt.interp_none_of_le s2 fuel (max f₀ fuel) σ₁ am₁ p.arrayDecls h (by omega)
      have hs2_safe : ∀ fuel, s2.safe fuel σ₁ am₁ p.arrayDecls := by
        intro fuel
        have hsafe_big := hsafe (max f₀ fuel); simp only [Stmt.safe] at hsafe_big
        obtain ⟨_, h2⟩ := hsafe_big
        have hm := Stmt.interp_fuel_mono s1 f₀ (max f₀ fuel - f₀) σ am p.arrayDecls _ hf₀
        rw [show f₀ + (max f₀ fuel - f₀) = max f₀ fuel from by omega] at hm
        rw [hm] at h2
        exact Stmt.safe_of_le s2 fuel (max f₀ fuel) σ₁ am₁ _ h2 (by omega)
      have hs2_tv : ∀ fuel, s2.typedVars fuel σ₁ am₁ p.arrayDecls := by
        intro fuel
        have htv_big := htypedv (max f₀ fuel); simp only [Stmt.typedVars] at htv_big
        obtain ⟨_, h2⟩ := htv_big
        have hm := Stmt.interp_fuel_mono s1 f₀ (max f₀ fuel - f₀) σ am p.arrayDecls _ hf₀
        rw [show f₀ + (max f₀ fuel - f₀) = max f₀ fuel from by omega] at hm
        rw [hm] at h2
        exact Stmt.typedVars_of_le s2 fuel (max f₀ fuel) σ₁ am₁ _ h2 (by omega)
      intro N
      obtain ⟨n₂, hn₂, pc', σ', am', hsteps₂⟩ :=
        ih2 σ₁ am₁ (offset + code1.length) tmp1 σ_1 htf2 hftf2 hbtf2 hng2 hs2_div hs2_safe hs2_tv
          hagree_1 (by rw [hrc2]; exact hcode.right) N
      exact ⟨k₁ + n₂, by omega, pc', σ', am', RefStepsN.trans hk₁ hsteps₂⟩
  | ite b s1 s2 ih1 ih2 =>
    have hb_safe : b.safe σ am p.arrayDecls := by
      have := hsafe 0; simp only [Stmt.safe] at this; exact this.1
    have htv_b : b.typedVars σ am := by
      have := htypedv 0; simp only [Stmt.typedVars] at this; exact this.1
    have hb_isSafe := SBool.isSafe_of_safe b σ am p.arrayDecls hb_safe
    have htf_b : ∀ v ∈ b.freeVars, v.isTmp = false := fun v hv =>
      htmpfree v (List.mem_append_left _ (List.mem_append_left _ hv))
    have hftf_b : ∀ v ∈ b.freeVars, v.isFTmp = false := fun v hv =>
      hftmpfree v (List.mem_append_left _ (List.mem_append_left _ hv))
    have htbf_b : ∀ v ∈ b.freeVars, v.isBTmp = false := fun v hv =>
      hbtmpfree v (List.mem_append_left _ (List.mem_append_left _ hv))
    dsimp only [compileStmt] at hcode ⊢
    generalize hrcb : compileBool b offset nextTmp = rcb at hcode ⊢
    obtain ⟨codeBool, be, tmpB⟩ := rcb
    generalize hrce : compileStmt s2 (offset + codeBool.length + 1) tmpB labels = rce at hcode ⊢
    obtain ⟨codeElse, tmpElse⟩ := rce
    generalize hrct : compileStmt s1 (offset + codeBool.length + 1 + codeElse.length + 1)
        tmpElse labels = rct at hcode ⊢
    obtain ⟨codeThen, tmpThen⟩ := rct; simp only [] at hcode ⊢
    obtain ⟨σ_bool, hexec_bool, heval_bool, hntmp_bool, _, _, _⟩ :=
      compileBool_correct b offset nextTmp σ σ_tac am p htf_b hftf_b htbf_b htv_b hb_safe hagree
        (by rw [hrcb]; exact hcode.left.left.left.left)
    rw [hrcb] at hexec_bool heval_bool; simp at hexec_bool heval_bool
    have hagree_bool : ∀ v, v.isTmp = false → v.isFTmp = false → v.isBTmp = false → σ_bool v = σ v :=
      fun v hv1 hv2 hv3 => by rw [hntmp_bool v hv1 hv2 hv3]; exact hagree v hv1 hv2 hv3
    obtain ⟨k_bool, hk_bool⟩ := hexec_bool.to_RefStepsN
    have hifgoto_instr : p[offset + codeBool.length]? =
        some (.ifgoto be (offset + codeBool.length + 1 + codeElse.length + 1)) := by
      have := hcode.left.left.left.right.head; simpa using this
    cases heval : b.eval σ am
    · -- false → else branch diverges
      have htf2 : s2.tmpFree := fun v hv => htmpfree v (List.mem_append_right _ hv)
      have hftf2 : s2.ftmpFree := fun v hv => hftmpfree v (List.mem_append_right _ hv)
      have hbtf2 : s2.btmpFree := fun v hv => hbtmpfree v (List.mem_append_right _ hv)
      have hs2_div : ∀ fuel, s2.interp fuel σ am p.arrayDecls = none := by
        intro fuel; have := hdiv fuel; simp [Stmt.interp, hb_isSafe, heval] at this; exact this
      have hs2_safe : ∀ fuel, s2.safe fuel σ am p.arrayDecls := by
        intro fuel; have := hsafe fuel; simp [Stmt.safe, heval] at this; exact this.2
      have hs2_tv : ∀ fuel, s2.typedVars fuel σ am p.arrayDecls := by
        intro fuel; have := htypedv fuel; simp [Stmt.typedVars, heval] at this; exact this.2
      have hexec_if := FragExec.single_iffalse (am := am) hifgoto_instr (by rw [heval_bool, heval])
      obtain ⟨k_if, hk_if⟩ := hexec_if.to_RefStepsN
      have hcode_else : RC.CodeAt (compileStmt s2 (offset + codeBool.length + 1) tmpB labels).1 p
          (offset + codeBool.length + 1) := by
        rw [hrce]; have := hcode.left.left.right
        simp only [List.length_append, List.length_cons, List.length_nil] at this
        rwa [show offset + (codeBool.length + 1) =
            offset + codeBool.length + 1 from by omega] at this
      intro N
      obtain ⟨n₂, hn₂, pc', σ', am', hsteps₂⟩ :=
        ih2 σ am (offset + codeBool.length + 1) tmpB σ_bool htf2 hftf2 hbtf2
          (hNoGoto : s1.noGoto ∧ s2.noGoto).2 hs2_div hs2_safe
          hs2_tv hagree_bool hcode_else N
      obtain ⟨k_pre, hk_pre⟩ := (FragExec.trans' hexec_bool hexec_if).to_RefStepsN
      exact ⟨k_pre + n₂, by omega, pc', σ', am', RefStepsN.trans hk_pre hsteps₂⟩
    · -- true → then branch diverges
      have htf1 : s1.tmpFree := fun v hv =>
        htmpfree v (List.mem_append_left _ (List.mem_append_right _ hv))
      have hftf1 : s1.ftmpFree := fun v hv =>
        hftmpfree v (List.mem_append_left _ (List.mem_append_right _ hv))
      have hbtf1 : s1.btmpFree := fun v hv =>
        hbtmpfree v (List.mem_append_left _ (List.mem_append_right _ hv))
      have hs1_div : ∀ fuel, s1.interp fuel σ am p.arrayDecls = none := by
        intro fuel; have := hdiv fuel; simp [Stmt.interp, hb_isSafe, heval] at this; exact this
      have hs1_safe : ∀ fuel, s1.safe fuel σ am p.arrayDecls := by
        intro fuel; have := hsafe fuel; simp [Stmt.safe, heval] at this; exact this.2
      have hs1_tv : ∀ fuel, s1.typedVars fuel σ am p.arrayDecls := by
        intro fuel; have := htypedv fuel; simp [Stmt.typedVars, heval] at this; exact this.2
      have hexec_if := FragExec.single_iftrue (am := am) hifgoto_instr (by rw [heval_bool, heval])
      obtain ⟨k_if, hk_if⟩ := hexec_if.to_RefStepsN
      have hcode_then : RC.CodeAt (compileStmt s1
          (offset + codeBool.length + 1 + codeElse.length + 1) tmpElse labels).1 p
          (offset + codeBool.length + 1 + codeElse.length + 1) := by
        rw [hrct]; have := hcode.right
        simp only [List.length_append, List.length_cons, List.length_nil] at this
        rwa [show offset + (codeBool.length + 1 + codeElse.length + 1) =
            offset + codeBool.length + 1 + codeElse.length + 1 from by omega] at this
      intro N
      obtain ⟨n₁, hn₁, pc', σ', am', hsteps₁⟩ :=
        ih1 σ am (offset + codeBool.length + 1 + codeElse.length + 1) tmpElse σ_bool
          htf1 hftf1 hbtf1 (hNoGoto : s1.noGoto ∧ s2.noGoto).1 hs1_div hs1_safe hs1_tv hagree_bool hcode_then N
      obtain ⟨k_pre, hk_pre⟩ := (FragExec.trans' hexec_bool hexec_if).to_RefStepsN
      exact ⟨k_pre + n₁, by omega, pc', σ', am', RefStepsN.trans hk_pre hsteps₁⟩
  | loop b body ihb =>
    have htf_body : body.tmpFree := fun v hv => htmpfree v (List.mem_append_right _ hv)
    have hftf_body : body.ftmpFree := fun v hv => hftmpfree v (List.mem_append_right _ hv)
    have hbtf_body : body.btmpFree := fun v hv => hbtmpfree v (List.mem_append_right _ hv)
    have hng_body : body.noGoto := hNoGoto
    -- Helper: derive b.eval = true from divergence + safety at any state
    have b_eval_true : ∀ σ' am',
        (∀ fuel, (Stmt.loop b body).interp fuel σ' am' p.arrayDecls = none) →
        (∀ fuel, (Stmt.loop b body).safe fuel σ' am' p.arrayDecls) →
        b.eval σ' am' = true := by
      intro σ' am' hdiv' hsafe'
      by_contra h; cases hh : b.eval σ' am'
      · have hsafe1 := hsafe' 1; rw [Stmt.safe.eq_9] at hsafe1
        have := hdiv' 1; rw [Stmt.interp.eq_9] at this
        simp [SBool.isSafe_of_safe b σ' am' _ hsafe1.1, hh] at this
      · exact h hh
    -- Helper: derive next-state properties after one iteration
    have next_state_props : ∀ σ' am' f₀ σ₁' am₁',
        (∀ fuel, (Stmt.loop b body).interp fuel σ' am' p.arrayDecls = none) →
        (∀ fuel, (Stmt.loop b body).safe fuel σ' am' p.arrayDecls) →
        (∀ fuel, (Stmt.loop b body).typedVars fuel σ' am' p.arrayDecls) →
        body.interp f₀ σ' am' p.arrayDecls = some (σ₁', am₁') →
        (∀ fuel, (Stmt.loop b body).interp fuel σ₁' am₁' p.arrayDecls = none) ∧
        (∀ fuel, (Stmt.loop b body).safe fuel σ₁' am₁' p.arrayDecls) ∧
        (∀ fuel, (Stmt.loop b body).typedVars fuel σ₁' am₁' p.arrayDecls) := by
      intro σ' am' f₀ σ₁' am₁' hdiv' hsafe' htypedv' hbody
      have hbe := b_eval_true σ' am' hdiv' hsafe'
      have hsafe1 := hsafe' 1; rw [Stmt.safe.eq_9] at hsafe1
      have hbisSafe := SBool.isSafe_of_safe b σ' am' _ hsafe1.1
      refine ⟨?_, ?_, ?_⟩
      · intro fuel
        have h := hdiv' (max f₀ fuel + 1); rw [Stmt.interp.eq_9] at h; simp [hbisSafe, hbe] at h
        have := Stmt.interp_fuel_mono body f₀ (max f₀ fuel - f₀) σ' am' p.arrayDecls _ hbody
        rw [show f₀ + (max f₀ fuel - f₀) = max f₀ fuel from by omega] at this
        simp [this] at h; exact Stmt.interp_none_of_le _ fuel _ σ₁' am₁' _ h (by omega)
      · intro fuel
        have h := hsafe' (max f₀ fuel + 1); rw [Stmt.safe.eq_9] at h
        obtain ⟨_, h2⟩ := h; simp [hbe] at h2
        have := Stmt.interp_fuel_mono body f₀ (max f₀ fuel - f₀) σ' am' p.arrayDecls _ hbody
        rw [show f₀ + (max f₀ fuel - f₀) = max f₀ fuel from by omega] at this
        rw [this] at h2; exact Stmt.safe_of_le _ fuel _ σ₁' am₁' _ h2.2 (by omega)
      · intro fuel
        have h := htypedv' (max f₀ fuel + 1); rw [Stmt.typedVars.eq_9] at h
        obtain ⟨_, h2⟩ := h; simp [hbe] at h2
        have := Stmt.interp_fuel_mono body f₀ (max f₀ fuel - f₀) σ' am' p.arrayDecls _ hbody
        rw [show f₀ + (max f₀ fuel - f₀) = max f₀ fuel from by omega] at this
        rw [this] at h2; exact Stmt.typedVars_of_le _ fuel _ σ₁' am₁' _ h2.2 (by omega)
    -- Main proof: suffices with N-induction generalized over state
    suffices ∀ N σ' am' σ_tac',
        (∀ fuel, (Stmt.loop b body).interp fuel σ' am' p.arrayDecls = none) →
        (∀ fuel, (Stmt.loop b body).safe fuel σ' am' p.arrayDecls) →
        (∀ fuel, (Stmt.loop b body).typedVars fuel σ' am' p.arrayDecls) →
        (∀ v, v.isTmp = false → v.isFTmp = false → v.isBTmp = false → σ_tac' v = σ' v) →
        ∃ n, n ≥ N ∧ ∃ pc' σ'' am'',
          RefStepsN p n (Cfg.run offset σ_tac' am') (Cfg.run pc' σ'' am'') by
      exact fun N => this N σ am σ_tac hdiv hsafe htypedv hagree
    intro N; induction N with
    | zero => intro σ' am' σ_tac' _ _ _ _; exact ⟨0, le_refl 0, offset, σ_tac', am', .refl⟩
    | succ N ih_N =>
      intro σ' am' σ_tac' hdiv' hsafe' htypedv' hagree'
      have hbe := b_eval_true σ' am' hdiv' hsafe'
      have hsafe1' := hsafe' 1; rw [Stmt.safe.eq_9] at hsafe1'
      have hbs := hsafe1'.1
      have htypedv1' := htypedv' 1; rw [Stmt.typedVars.eq_9] at htypedv1'
      have htv_b' := htypedv1'.1
      by_cases hbody_div : ∀ fuel, body.interp fuel σ' am' p.arrayDecls = none
      · -- Body diverges: prefix with bool + ifgoto, use structural IH on body
        have hbody_safe : ∀ fuel, body.safe fuel σ' am' p.arrayDecls := by
          intro fuel; have := hsafe' (fuel + 1); rw [Stmt.safe.eq_9] at this
          obtain ⟨_, h2⟩ := this; simp [hbe] at h2; exact h2.1
        have hbody_tv : ∀ fuel, body.typedVars fuel σ' am' p.arrayDecls := by
          intro fuel; have := htypedv' (fuel + 1); rw [Stmt.typedVars.eq_9] at this
          obtain ⟨_, h2⟩ := this; simp [hbe] at h2; exact h2.1
        have htf_b : ∀ v ∈ b.freeVars, v.isTmp = false :=
          fun v hv => htmpfree v (List.mem_append_left _ hv)
        have hftf_b : ∀ v ∈ b.freeVars, v.isFTmp = false :=
          fun v hv => hftmpfree v (List.mem_append_left _ hv)
        have htbf_b : ∀ v ∈ b.freeVars, v.isBTmp = false :=
          fun v hv => hbtmpfree v (List.mem_append_left _ hv)
        dsimp only [compileStmt] at hcode
        generalize hrcb : compileBool b offset nextTmp = rcb at hcode
        obtain ⟨codeBool, be, tmpB⟩ := rcb
        generalize hrcbody : compileStmt body (offset + codeBool.length + 1) tmpB labels = rcbody
            at hcode
        obtain ⟨codeBody, tmpBody⟩ := rcbody; simp only [] at hcode
        obtain ⟨σ_bool, hexec_bool, heval_bool, hntmp_bool, _, _, _⟩ :=
          compileBool_correct b offset nextTmp σ' σ_tac' am' p htf_b hftf_b htbf_b htv_b' hbs hagree'
            (by rw [hrcb]; exact hcode.left.left.left)
        rw [hrcb] at hexec_bool heval_bool; simp at hexec_bool heval_bool
        have hagree_bool : ∀ v, v.isTmp = false → v.isFTmp = false → v.isBTmp = false → σ_bool v = σ' v :=
          fun v hv1 hv2 hv3 => by rw [hntmp_bool v hv1 hv2 hv3]; exact hagree' v hv1 hv2 hv3
        have hifg : p[offset + codeBool.length]? =
            some (.ifgoto (.not be) (offset + codeBool.length + 1 + codeBody.length + 1)) := by
          have := hcode.left.left.right.head
          simp only [List.length_append, List.length_cons, List.length_nil] at this; exact this
        have hexec_if := FragExec.single_iffalse (am := am') (σ := σ_bool) hifg
          (by simp [BoolExpr.eval, heval_bool, hbe])
        obtain ⟨k_pre, hk_pre⟩ := (FragExec.trans' hexec_bool hexec_if).to_RefStepsN
        have hcode_body : RC.CodeAt (compileStmt body (offset + codeBool.length + 1) tmpB labels).1 p
            (offset + codeBool.length + 1) := by
          rw [hrcbody]; have := hcode.left.right
          simp only [List.length_append, List.length_cons, List.length_nil] at this
          rwa [show offset + (codeBool.length + 1) =
              offset + codeBool.length + 1 from by omega] at this
        obtain ⟨n_body, hn_body, pc', σ'', am'', hsteps_body⟩ :=
          ihb σ' am' (offset + codeBool.length + 1) tmpB σ_bool htf_body hftf_body hbtf_body hng_body
            hbody_div hbody_safe hbody_tv hagree_bool hcode_body (N + 1)
        exact ⟨k_pre + n_body, by omega, pc', σ'', am'', RefStepsN.trans hk_pre hsteps_body⟩
      · -- Body terminates for some fuel
        push_neg at hbody_div; obtain ⟨f₀, hf₀_ne⟩ := hbody_div
        obtain ⟨r, hf₀⟩ := Option.ne_none_iff_exists'.mp hf₀_ne
        obtain ⟨σ₁, am₁⟩ := r
        have hbody_safe : body.safe f₀ σ' am' p.arrayDecls := by
          have := hsafe' (f₀ + 1); rw [Stmt.safe.eq_9] at this
          obtain ⟨_, h2⟩ := this; simp [hbe] at h2; exact h2.1
        have hbody_tv : body.typedVars f₀ σ' am' p.arrayDecls := by
          have := htypedv' (f₀ + 1); rw [Stmt.typedVars.eq_9] at this
          obtain ⟨_, h2⟩ := this; simp [hbe] at h2; exact h2.1
        obtain ⟨σ₁_tac, k₁, hiter₁, hagree₁, hk₁_ge⟩ :=
          loop_one_iter b body f₀ σ' σ₁ am' am₁ offset nextTmp p σ_tac' htmpfree hftmpfree hbtmpfree
            hbe hbs htv_b' hf₀ hbody_safe hbody_tv hNoGoto hagree' (labels := labels) hcode
        obtain ⟨hdiv₁, hsafe₁, htypedv₁⟩ := next_state_props σ' am' f₀ σ₁ am₁ hdiv' hsafe' htypedv' hf₀
        obtain ⟨n_rest, hn_rest, pc', σ'', am'', hsteps_rest⟩ :=
          ih_N σ₁ am₁ σ₁_tac hdiv₁ hsafe₁ htypedv₁ hagree₁
        exact ⟨k₁ + n_rest, by omega, pc', σ'', am'', RefStepsN.trans hiter₁ hsteps_rest⟩
/-- Top-level divergence: if the source diverges with safety,
    the compiled program does not halt. -/
theorem compileStmtToProg_diverge (s : Stmt) (σ : Store)
    (htmpfree : s.tmpFree)
    (hftmpfree : s.ftmpFree)
    (hbtmpfree : s.btmpFree)
    (hNoGoto : s.noGoto)
    (hdiv : ∀ fuel, s.interp fuel σ ArrayMem.init (compileStmtToProg s).arrayDecls = none)
    (hsafe : ∀ fuel, s.safe fuel σ ArrayMem.init (compileStmtToProg s).arrayDecls)
    (htypedv : ∀ fuel, s.typedVars fuel σ ArrayMem.init (compileStmtToProg s).arrayDecls) :
    ∀ σ_tac am', ¬ haltsWithResult (compileStmtToProg s) 0 σ σ_tac ArrayMem.init am' := by
  have hcode : RC.CodeAt (compileStmt s 0 0).1 (compileStmtToProg s) 0 := by
    intro i hi; unfold compileStmtToProg; simp only [Prog.ofCode, Prog.getElem?_code, List.getElem?_toArray, Nat.zero_add]
    exact List.getElem?_append_left hi
  have hunbounded := compileStmt_diverges s σ ArrayMem.init 0 0 (compileStmtToProg s) σ
    htmpfree hftmpfree hbtmpfree hNoGoto hdiv hsafe htypedv (fun _ _ _ _ => rfl) (labels := []) hcode
  exact no_halt_of_unbounded_am hunbounded
