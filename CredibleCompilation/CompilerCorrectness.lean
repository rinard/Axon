-- Copyright (c) 2026 Martin Rinard
import CredibleCompilation.WhileLang
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Push

set_option linter.unusedSimpArgs false

/-!
# Compiler Infrastructure: Variable Classification, Congruence, and Division Safety

Shared infrastructure for reasoning about the While→TAC compiler:
- Variable classification (`isTmp`, `freeVars`, `allVars`, `tmpFree`)
- Expression/boolean evaluation congruence under store agreement
- Interpreter congruence on tmp-free programs
- Division safety predicates

These definitions and lemmas are used by `RefCompiler.lean` for the
verified compiler correctness proof.
-/

-- ============================================================
-- § 1. Variable classification
-- ============================================================

def SExpr.freeVars : SExpr → List Var
  | .lit _ => []
  | .var x => [x]
  | .bin _ a b => a.freeVars ++ b.freeVars
  | .arrRead _ idx => idx.freeVars
  | .flit _ => []
  | .fbin _ a b => a.freeVars ++ b.freeVars
  | .intToFloat e => e.freeVars
  | .floatToInt e => e.freeVars
  | .floatUnary _ e => e.freeVars
  | .farrRead _ idx => idx.freeVars

def SBool.freeVars : SBool → List Var
  | .lit _ => []
  | .bvar x => [x]
  | .cmp _ a b => a.freeVars ++ b.freeVars
  | .not e => e.freeVars
  | .and a b => a.freeVars ++ b.freeVars
  | .or a b => a.freeVars ++ b.freeVars
  | .barrRead _ idx => idx.freeVars
  | .fcmp _ a b => a.freeVars ++ b.freeVars

def Stmt.allVars : Stmt → List Var
  | .skip => []
  | .assign x e => x :: e.freeVars
  | .bassign x b => x :: b.freeVars
  | .arrWrite _ idx val => idx.freeVars ++ val.freeVars
  | .barrWrite _ idx bval => idx.freeVars ++ bval.freeVars
  | .seq s₁ s₂ => s₁.allVars ++ s₂.allVars
  | .ite b s₁ s₂ => b.freeVars ++ s₁.allVars ++ s₂.allVars
  | .loop b body => b.freeVars ++ body.allVars
  | .fassign x e => x :: e.freeVars
  | .farrWrite _ idx val => idx.freeVars ++ val.freeVars
  | .label _ => []
  | .goto _ => []
  | .ifgoto b _ => b.freeVars
  | .print _ args => args.flatMap SExpr.freeVars
  | .printInt e => e.freeVars
  | .printBool b => b.freeVars
  | .printFloat e => e.freeVars
  | .printString _ => []

def Stmt.tmpFree (s : Stmt) : Prop := ∀ v ∈ s.allVars, v.isTmp = false
def Stmt.ftmpFree (s : Stmt) : Prop := ∀ v ∈ s.allVars, v.isFTmp = false
def Stmt.btmpFree (s : Stmt) : Prop := ∀ v ∈ s.allVars, v.isBTmp = false

/-- A statement contains no goto/ifgoto. -/
def Stmt.noGoto : Stmt → Prop
  | .skip | .assign .. | .bassign .. | .arrWrite .. | .barrWrite ..
  | .fassign .. | .farrWrite .. | .label .. | .print ..
  | .printInt .. | .printBool .. | .printFloat .. | .printString .. => True
  | .goto .. => False
  | .ifgoto .. => False
  | .seq s₁ s₂ => s₁.noGoto ∧ s₂.noGoto
  | .ite _ s₁ s₂ => s₁.noGoto ∧ s₂.noGoto
  | .loop _ body => body.noGoto


-- ============================================================
-- § 2. Expression evaluation congruence
-- ============================================================

theorem SExpr.eval_agree (e : SExpr) (σ τ : Store) (am : ArrayMem)
    (h : ∀ v ∈ e.freeVars, σ v = τ v) : e.eval σ am = e.eval τ am := by
  induction e with
  | lit _ => rfl
  | var x =>
    simp only [SExpr.eval, SExpr.freeVars, List.mem_singleton] at *
    rw [h x rfl]
  | bin op a b iha ihb =>
    simp only [SExpr.eval]
    rw [iha (fun v hv => h v (List.mem_append_left _ hv)),
        ihb (fun v hv => h v (List.mem_append_right _ hv))]
  | arrRead _ idx ih =>
    simp only [SExpr.eval]
    rw [ih h]
  | flit _ => rfl
  | fbin _ a b iha ihb =>
    simp only [SExpr.eval]
    rw [iha (fun v hv => h v (List.mem_append_left _ hv)),
        ihb (fun v hv => h v (List.mem_append_right _ hv))]
  | intToFloat e ih => simp only [SExpr.eval]; rw [ih h]
  | floatToInt e ih => simp only [SExpr.eval]; rw [ih h]
  | floatUnary op e ih => simp only [SExpr.eval]; rw [ih h]
  | farrRead _ idx ih => simp only [SExpr.eval]; rw [ih h]

theorem SBool.eval_agree (sb : SBool) (σ τ : Store) (am : ArrayMem)
    (h : ∀ v ∈ sb.freeVars, σ v = τ v) : sb.eval σ am = sb.eval τ am := by
  induction sb with
  | lit _ => rfl
  | bvar x =>
    simp only [SBool.eval, SBool.freeVars, List.mem_singleton] at *
    rw [h x rfl]
  | cmp op a b =>
    simp only [SBool.eval, SBool.freeVars] at *
    rw [SExpr.eval_agree a σ τ am (fun v hv => h v (List.mem_append_left _ hv)),
        SExpr.eval_agree b σ τ am (fun v hv => h v (List.mem_append_right _ hv))]
  | not e ih => simp only [SBool.eval]; rw [ih h]
  | and a b iha ihb =>
    simp only [SBool.eval, SBool.freeVars] at *
    rw [iha (fun v hv => h v (List.mem_append_left _ hv)),
        ihb (fun v hv => h v (List.mem_append_right _ hv))]
  | or a b iha ihb =>
    simp only [SBool.eval, SBool.freeVars] at *
    rw [iha (fun v hv => h v (List.mem_append_left _ hv)),
        ihb (fun v hv => h v (List.mem_append_right _ hv))]
  | barrRead arr idx =>
    simp only [SBool.eval]
    rw [SExpr.eval_agree idx σ τ am h]
  | fcmp _ a b =>
    simp only [SBool.eval]
    rw [SExpr.eval_agree a σ τ am (fun v hv => h v (List.mem_append_left _ hv)),
        SExpr.eval_agree b σ τ am (fun v hv => h v (List.mem_append_right _ hv))]

theorem SExpr.eval_tmpAgree (e : SExpr) (σ τ : Store) (am : ArrayMem)
    (hagree : ∀ v, v.isTmp = false → σ v = τ v)
    (htf : ∀ v ∈ e.freeVars, v.isTmp = false) :
    e.eval σ am = e.eval τ am :=
  SExpr.eval_agree e σ τ am (fun v hv => hagree v (htf v hv))

theorem SBool.eval_tmpAgree (sb : SBool) (σ τ : Store) (am : ArrayMem)
    (hagree : ∀ v, v.isTmp = false → σ v = τ v)
    (htf : ∀ v ∈ sb.freeVars, v.isTmp = false) :
    sb.eval σ am = sb.eval τ am :=
  SBool.eval_agree sb σ τ am (fun v hv => hagree v (htf v hv))

-- ============================================================
-- § 2b. isSafe congruence
-- ============================================================

theorem SExpr.isSafe_agree (e : SExpr) (σ τ : Store) (am : ArrayMem) (decls)
    (h : ∀ v ∈ e.freeVars, σ v = τ v) :
    e.isSafe σ am decls = e.isSafe τ am decls := by
  induction e with
  | lit _ | var _ => rfl
  | bin op a b iha ihb =>
    have ha := iha (fun v hv => h v (List.mem_append_left _ hv))
    have hb := ihb (fun v hv => h v (List.mem_append_right _ hv))
    have hbe := SExpr.eval_agree b σ τ am (fun v hv => h v (List.mem_append_right _ hv))
    cases op <;> simp only [SExpr.isSafe, ha, hb, hbe]
  | arrRead arr idx ih =>
    simp only [SExpr.isSafe]
    rw [ih h, SExpr.eval_agree idx σ τ am h]
  | flit _ => rfl
  | fbin _ a b iha ihb =>
    simp only [SExpr.isSafe]
    rw [iha (fun v hv => h v (List.mem_append_left _ hv)),
        ihb (fun v hv => h v (List.mem_append_right _ hv))]
  | intToFloat e ih => simp only [SExpr.isSafe]; rw [ih h]
  | floatToInt e ih => simp only [SExpr.isSafe]; rw [ih h]
  | floatUnary op e ih => simp only [SExpr.isSafe]; rw [ih h]
  | farrRead arr idx ih =>
    simp only [SExpr.isSafe]
    rw [ih h, SExpr.eval_agree idx σ τ am h]

theorem SBool.isSafe_agree (sb : SBool) (σ τ : Store) (am : ArrayMem) (decls)
    (h : ∀ v ∈ sb.freeVars, σ v = τ v) :
    sb.isSafe σ am decls = sb.isSafe τ am decls := by
  induction sb with
  | lit _ | bvar _ => rfl
  | cmp _ a b =>
    simp only [SBool.isSafe]
    rw [SExpr.isSafe_agree a σ τ am decls (fun v hv => h v (List.mem_append_left _ hv)),
        SExpr.isSafe_agree b σ τ am decls (fun v hv => h v (List.mem_append_right _ hv))]
  | not e ih => simp only [SBool.isSafe]; rw [ih h]
  | and a b iha ihb =>
    simp only [SBool.isSafe]
    rw [iha (fun v hv => h v (List.mem_append_left _ hv)),
        SBool.eval_agree a σ τ am (fun v hv => h v (List.mem_append_left _ hv)),
        ihb (fun v hv => h v (List.mem_append_right _ hv))]
  | or a b iha ihb =>
    simp only [SBool.isSafe]
    rw [iha (fun v hv => h v (List.mem_append_left _ hv)),
        SBool.eval_agree a σ τ am (fun v hv => h v (List.mem_append_left _ hv)),
        ihb (fun v hv => h v (List.mem_append_right _ hv))]
  | barrRead arr idx =>
    simp only [SBool.isSafe]
    rw [SExpr.isSafe_agree idx σ τ am decls h,
        SExpr.eval_agree idx σ τ am h]
  | fcmp _ a b =>
    simp only [SBool.isSafe]
    rw [SExpr.isSafe_agree a σ τ am decls (fun v hv => h v (List.mem_append_left _ hv)),
        SExpr.isSafe_agree b σ τ am decls (fun v hv => h v (List.mem_append_right _ hv))]

theorem SExpr.isSafe_tmpAgree (e : SExpr) (σ τ : Store) (am : ArrayMem) (decls)
    (hagree : ∀ v, v.isTmp = false → σ v = τ v)
    (htf : ∀ v ∈ e.freeVars, v.isTmp = false) :
    e.isSafe σ am decls = e.isSafe τ am decls :=
  SExpr.isSafe_agree e σ τ am decls (fun v hv => hagree v (htf v hv))

theorem SBool.isSafe_tmpAgree (sb : SBool) (σ τ : Store) (am : ArrayMem) (decls)
    (hagree : ∀ v, v.isTmp = false → σ v = τ v)
    (htf : ∀ v ∈ sb.freeVars, v.isTmp = false) :
    sb.isSafe σ am decls = sb.isSafe τ am decls :=
  SBool.isSafe_agree sb σ τ am decls (fun v hv => hagree v (htf v hv))

-- ============================================================
-- § 3. Interpreter congruence on tmp-free programs
-- ============================================================

theorem Stmt.interp_tmpAgree (s : Stmt) (fuel : Nat) (σ τ : Store) (am : ArrayMem)
    (decls : List (ArrayName × Nat × VarTy))
    (hagree : ∀ v, v.isTmp = false → σ v = τ v)
    (htf : s.tmpFree)
    (σ' : Store) (am' : ArrayMem) (h : s.interp fuel σ am decls = some (σ', am')) :
    ∃ τ' am'', s.interp fuel τ am decls = some (τ', am'') ∧
      (∀ v, v.isTmp = false → σ' v = τ' v) ∧ am'' = am' := by
  induction s generalizing fuel σ τ σ' am am' with
  | skip =>
    simp only [Stmt.interp] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨τ, am, by simp [Stmt.interp], hagree, rfl⟩
  | assign x e =>
    unfold Stmt.tmpFree Stmt.allVars at htf
    have htf_e : ∀ v ∈ e.freeVars, v.isTmp = false :=
      fun v hv => htf v (List.mem_cons_of_mem x hv)
    have heval : e.eval σ am = e.eval τ am := SExpr.eval_tmpAgree e σ τ am hagree htf_e
    have hsafe : e.isSafe σ am decls = e.isSafe τ am decls :=
      SExpr.isSafe_tmpAgree e σ τ am decls hagree htf_e
    simp only [Stmt.interp] at h
    split at h
    · rename_i hs
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨τ[x ↦ .int (e.eval τ am)], am, ?_, ?_, rfl⟩
      · simp only [Stmt.interp]; rw [← hsafe]; simp [hs]
      · intro v hv; simp only [Store.update]; split
        · rw [heval]
        · exact hagree v hv
    · simp at h
  | bassign x b =>
    unfold Stmt.tmpFree Stmt.allVars at htf
    have htf_b : ∀ v ∈ b.freeVars, v.isTmp = false :=
      fun v hv => htf v (List.mem_cons_of_mem x hv)
    have heval : b.eval σ am = b.eval τ am := SBool.eval_tmpAgree b σ τ am hagree htf_b
    have hsafe : b.isSafe σ am decls = b.isSafe τ am decls :=
      SBool.isSafe_tmpAgree b σ τ am decls hagree htf_b
    simp only [Stmt.interp] at h
    split at h
    · rename_i hs
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨τ[x ↦ .bool (b.eval τ am)], am, ?_, ?_, rfl⟩
      · simp only [Stmt.interp]; rw [← hsafe]; simp [hs]
      · intro v hv; simp only [Store.update]; split
        · rw [heval]
        · exact hagree v hv
    · simp at h
  | arrWrite arr idx val =>
    unfold Stmt.tmpFree Stmt.allVars at htf
    have htf_idx : ∀ v ∈ idx.freeVars, v.isTmp = false :=
      fun v hv => htf v (List.mem_append_left _ hv)
    have htf_val : ∀ v ∈ val.freeVars, v.isTmp = false :=
      fun v hv => htf v (List.mem_append_right _ hv)
    have heval_idx : idx.eval σ am = idx.eval τ am := SExpr.eval_tmpAgree idx σ τ am hagree htf_idx
    have heval_val : val.eval σ am = val.eval τ am := SExpr.eval_tmpAgree val σ τ am hagree htf_val
    have hsafe_idx : idx.isSafe σ am decls = idx.isSafe τ am decls :=
      SExpr.isSafe_tmpAgree idx σ τ am decls hagree htf_idx
    have hsafe_val : val.isSafe σ am decls = val.isSafe τ am decls :=
      SExpr.isSafe_tmpAgree val σ τ am decls hagree htf_val
    simp only [Stmt.interp] at h
    split at h
    · rename_i hs
      obtain ⟨rfl, rfl⟩ := h
      simp [Bool.and_eq_true, decide_eq_true_eq] at hs
      refine ⟨τ, am.write arr (idx.eval τ am) (val.eval τ am), ?_, hagree, ?_⟩
      · simp only [Stmt.interp]
        rw [← hsafe_idx, ← hsafe_val, ← heval_idx]
        simp [hs.1.1, hs.1.2, hs.2]
      · rw [heval_idx, heval_val]
    · simp at h
  | barrWrite arr idx bval =>
    unfold Stmt.tmpFree Stmt.allVars at htf
    have htf_idx : ∀ v ∈ (idx : SExpr).freeVars, v.isTmp = false :=
      fun v hv => htf v (List.mem_append_left _ hv)
    have htf_bval : ∀ v ∈ bval.freeVars, v.isTmp = false :=
      fun v hv => htf v (List.mem_append_right _ hv)
    have heval_idx : (idx : SExpr).eval σ am = (idx : SExpr).eval τ am :=
      SExpr.eval_tmpAgree idx σ τ am hagree htf_idx
    have heval_bval : bval.eval σ am = bval.eval τ am := SBool.eval_tmpAgree bval σ τ am hagree htf_bval
    have hsafe_idx : (idx : SExpr).isSafe σ am decls = (idx : SExpr).isSafe τ am decls :=
      SExpr.isSafe_tmpAgree idx σ τ am decls hagree htf_idx
    have hsafe_bval : bval.isSafe σ am decls = bval.isSafe τ am decls :=
      SBool.isSafe_tmpAgree bval σ τ am decls hagree htf_bval
    simp only [Stmt.interp] at h
    split at h
    · rename_i hs
      simp [Bool.and_eq_true, decide_eq_true_eq] at hs
      simp at h; obtain ⟨rfl, rfl⟩ := h
      refine ⟨τ, am.write arr (idx.eval τ am) (if bval.eval τ am then 1 else 0), ?_, hagree, ?_⟩
      · simp only [Stmt.interp]
        rw [← hsafe_idx, ← hsafe_bval, ← heval_idx]
        simp [hs.1.1, hs.1.2, hs.2]
      · simp [heval_idx, heval_bval]
    · simp at h
  | seq s1 s2 ih1 ih2 =>
    have htf1 : s1.tmpFree := fun v hv => htf v (List.mem_append_left _ hv)
    have htf2 : s2.tmpFree := fun v hv => htf v (List.mem_append_right _ hv)
    simp only [Stmt.interp, bind, Option.bind] at h
    cases h1 : s1.interp fuel σ am decls with
    | none => simp [h1] at h
    | some p =>
      obtain ⟨σ₁, am₁⟩ := p
      simp [h1] at h
      obtain ⟨τ₁, am₁', h1', hagree', rfl⟩ := ih1 (htf := htf1) (hagree := hagree) (h := h1)
      obtain ⟨τ₂, am₂', h2', hagree'', rfl⟩ := ih2 (htf := htf2) (hagree := hagree') (h := h)
      exact ⟨τ₂, am₂', by simp only [Stmt.interp, bind, Option.bind]; simp [h1', h2'], hagree'', rfl⟩
  | ite b s1 s2 ih1 ih2 =>
    unfold Stmt.tmpFree Stmt.allVars at htf
    have htf_b : ∀ v ∈ b.freeVars, v.isTmp = false :=
      fun v hv => htf v (List.mem_append_left _ (List.mem_append_left _ hv))
    have htf1 : s1.tmpFree :=
      fun v hv => htf v (List.mem_append_left _ (List.mem_append_right _ hv))
    have htf2 : s2.tmpFree := fun v hv => htf v (List.mem_append_right _ hv)
    have heval : b.eval σ am = b.eval τ am := SBool.eval_tmpAgree b σ τ am hagree htf_b
    have hsafe : b.isSafe σ am decls = b.isSafe τ am decls :=
      SBool.isSafe_tmpAgree b σ τ am decls hagree htf_b
    simp only [Stmt.interp] at h
    split at h
    · rename_i hbs
      cases heval' : b.eval σ am
      · simp [heval'] at h
        obtain ⟨τ', am'', h', hagree', rfl⟩ := ih2 (htf := htf2) (hagree := hagree) (h := h)
        refine ⟨τ', am'', ?_, hagree', rfl⟩
        simp only [Stmt.interp]; rw [← hsafe]; simp [hbs, ← heval, heval', h']
      · simp [heval'] at h
        obtain ⟨τ', am'', h', hagree', rfl⟩ := ih1 (htf := htf1) (hagree := hagree) (h := h)
        refine ⟨τ', am'', ?_, hagree', rfl⟩
        simp only [Stmt.interp]; rw [← hsafe]; simp [hbs, ← heval, heval', h']
    · simp at h
  | loop b body ihb =>
    unfold Stmt.tmpFree Stmt.allVars at htf
    have htf_b : ∀ v ∈ b.freeVars, v.isTmp = false :=
      fun v hv => htf v (List.mem_append_left _ hv)
    have htf_body : body.tmpFree := fun v hv => htf v (List.mem_append_right _ hv)
    induction fuel generalizing σ τ σ' am am' with
    | zero => simp only [Stmt.interp] at h; simp at h
    | succ fuel' ih_fuel =>
      have heval : b.eval σ am = b.eval τ am := SBool.eval_tmpAgree b σ τ am hagree htf_b
      have hsafe : b.isSafe σ am decls = b.isSafe τ am decls :=
        SBool.isSafe_tmpAgree b σ τ am decls hagree htf_b
      simp only [Stmt.interp] at h
      split at h
      · rename_i hbs
        cases heval' : b.eval σ am
        · simp [heval'] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨τ, am, ?_, hagree, rfl⟩
          simp only [Stmt.interp]; rw [← hsafe]; simp [hbs, ← heval, heval']
        · simp [heval'] at h
          cases h_body : body.interp fuel' σ am decls with
          | none => simp [h_body] at h
          | some p =>
            obtain ⟨σ₁, am₁⟩ := p
            simp [h_body] at h
            obtain ⟨τ₁, am₁', h_body', hagree', rfl⟩ :=
              ihb (htf := htf_body) (hagree := hagree) (h := h_body)
            obtain ⟨τ₂, am₂', h_loop', hagree'', rfl⟩ :=
              ih_fuel (hagree := hagree') (h := h)
            refine ⟨τ₂, am₂', ?_, hagree'', rfl⟩
            simp only [Stmt.interp]; rw [← hsafe]; simp [hbs, ← heval, heval', h_body', h_loop']
      · simp at h
  | fassign x e =>
    unfold Stmt.tmpFree Stmt.allVars at htf
    have htf_e : ∀ v ∈ e.freeVars, v.isTmp = false :=
      fun v hv => htf v (List.mem_cons_of_mem x hv)
    have heval : e.eval σ am = e.eval τ am := SExpr.eval_tmpAgree e σ τ am hagree htf_e
    have hsafe : e.isSafe σ am decls = e.isSafe τ am decls :=
      SExpr.isSafe_tmpAgree e σ τ am decls hagree htf_e
    simp only [Stmt.interp] at h
    split at h
    · rename_i hs
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨τ[x ↦ .float (e.eval τ am)], am, ?_, ?_, rfl⟩
      · simp only [Stmt.interp]; rw [← hsafe]; simp [hs, heval]
      · intro v hv; simp only [Store.update]; split
        · rw [heval]
        · exact hagree v hv
    · simp at h
  | farrWrite arr idx val =>
    unfold Stmt.tmpFree Stmt.allVars at htf
    have htf_idx : ∀ v ∈ idx.freeVars, v.isTmp = false :=
      fun v hv => htf v (List.mem_append_left _ hv)
    have htf_val : ∀ v ∈ val.freeVars, v.isTmp = false :=
      fun v hv => htf v (List.mem_append_right _ hv)
    have heval_idx : idx.eval σ am = idx.eval τ am := SExpr.eval_tmpAgree idx σ τ am hagree htf_idx
    have heval_val : val.eval σ am = val.eval τ am := SExpr.eval_tmpAgree val σ τ am hagree htf_val
    have hsafe_idx : idx.isSafe σ am decls = idx.isSafe τ am decls :=
      SExpr.isSafe_tmpAgree idx σ τ am decls hagree htf_idx
    have hsafe_val : val.isSafe σ am decls = val.isSafe τ am decls :=
      SExpr.isSafe_tmpAgree val σ τ am decls hagree htf_val
    simp only [Stmt.interp] at h
    split at h
    · rename_i hs
      simp at h; obtain ⟨rfl, rfl⟩ := h
      simp [Bool.and_eq_true, decide_eq_true_eq] at hs
      refine ⟨τ, am.write arr (idx.eval τ am) (val.eval τ am), ?_, hagree, ?_⟩
      · simp only [Stmt.interp]
        rw [← hsafe_idx, ← hsafe_val, ← heval_idx]
        simp [hs.1.1, hs.1.2, hs.2]
      · rw [heval_idx, heval_val]
    · simp at h
  | label _ =>
    simp only [Stmt.interp] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨τ, am, by simp [Stmt.interp], hagree, rfl⟩
  | goto _ =>
    simp only [Stmt.interp] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨τ, am, by simp [Stmt.interp], hagree, rfl⟩
  | ifgoto b _ =>
    simp only [Stmt.interp] at h
    split at h
    · obtain ⟨rfl, rfl⟩ := h
      have hsafe : b.isSafe σ am decls = b.isSafe τ am decls :=
        SBool.isSafe_tmpAgree b σ τ am decls hagree (fun v hv => htf v hv)
      refine ⟨τ, am, ?_, hagree, rfl⟩
      simp only [Stmt.interp]; rw [← hsafe]; simp [‹_ = true›]
    · simp at h
  | print fmt args =>
    simp only [Stmt.interp] at h
    split at h
    · obtain ⟨rfl, rfl⟩ := h
      unfold Stmt.tmpFree Stmt.allVars at htf
      refine ⟨τ, am, ?_, hagree, rfl⟩
      simp only [Stmt.interp]
      have : (args.all fun e => e.isSafe τ am decls) = true := by
        rw [List.all_eq_true]
        intro e he
        have := (List.all_eq_true.mp ‹_ = true›) e he
        rwa [SExpr.isSafe_tmpAgree e σ τ am decls hagree
          (fun v hv => htf v (List.mem_flatMap.mpr ⟨e, he, hv⟩))] at this
      simp [this]
    · simp at h
  | printInt e =>
    simp only [Stmt.interp] at h
    split at h
    · obtain ⟨rfl, rfl⟩ := h
      unfold Stmt.tmpFree Stmt.allVars at htf
      refine ⟨τ, am, ?_, hagree, rfl⟩
      simp only [Stmt.interp]
      rw [← SExpr.isSafe_tmpAgree e σ τ am decls hagree (fun v hv => htf v hv)]
      simp [‹_ = true›]
    · simp at h
  | printBool b =>
    simp only [Stmt.interp] at h
    split at h
    · obtain ⟨rfl, rfl⟩ := h
      unfold Stmt.tmpFree Stmt.allVars at htf
      refine ⟨τ, am, ?_, hagree, rfl⟩
      simp only [Stmt.interp]
      rw [← SBool.isSafe_tmpAgree b σ τ am decls hagree (fun v hv => htf v hv)]
      simp [‹_ = true›]
    · simp at h
  | printFloat e =>
    simp only [Stmt.interp] at h
    split at h
    · obtain ⟨rfl, rfl⟩ := h
      unfold Stmt.tmpFree Stmt.allVars at htf
      refine ⟨τ, am, ?_, hagree, rfl⟩
      simp only [Stmt.interp]
      rw [← SExpr.isSafe_tmpAgree e σ τ am decls hagree (fun v hv => htf v hv)]
      simp [‹_ = true›]
    · simp at h
  | printString lit =>
    simp only [Stmt.interp] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨τ, am, by simp [Stmt.interp], hagree, rfl⟩

-- ============================================================
-- § 4. Safety (division + bounds)
-- ============================================================

def SExpr.safe (σ : Store) (am : ArrayMem) (decls : List (ArrayName × Nat × VarTy)) : SExpr → Prop
  | .lit _ => True
  | .var _ => True
  | .bin .div a b => a.safe σ am decls ∧ b.safe σ am decls ∧ b.eval σ am ≠ 0
  | .bin .mod a b => a.safe σ am decls ∧ b.safe σ am decls ∧ b.eval σ am ≠ 0
  | .bin _ a b => a.safe σ am decls ∧ b.safe σ am decls
  | .arrRead arr idx => idx.safe σ am decls ∧ (idx.eval σ am) < arraySizeBv decls arr
  | .flit _ => True
  | .fbin _ a b => a.safe σ am decls ∧ b.safe σ am decls
  | .intToFloat e => e.safe σ am decls
  | .floatToInt e => e.safe σ am decls
  | .floatUnary _ e => e.safe σ am decls
  | .farrRead arr idx => idx.safe σ am decls ∧ (idx.eval σ am) < arraySizeBv decls arr

def SBool.safe (σ : Store) (am : ArrayMem) (decls : List (ArrayName × Nat × VarTy)) : SBool → Prop
  | .lit _ => True
  | .bvar _ => True
  | .cmp _ a b => a.safe σ am decls ∧ b.safe σ am decls
  | .not e => e.safe σ am decls
  | .and a b => a.safe σ am decls ∧ (a.eval σ am = true → b.safe σ am decls)
  | .or a b => a.safe σ am decls ∧ (a.eval σ am = false → b.safe σ am decls)
  | .barrRead arr idx => idx.safe σ am decls ∧ (idx.eval σ am) < arraySizeBv decls arr
  | .fcmp _ a b => a.safe σ am decls ∧ b.safe σ am decls

def Stmt.safe (fuel : Nat) (σ : Store) (am : ArrayMem)
    (decls : List (ArrayName × Nat × VarTy)) : Stmt → Prop
  | .skip => True
  | .assign _ e => e.safe σ am decls
  | .bassign _ b => b.safe σ am decls
  | .arrWrite arr idx val =>
    idx.safe σ am decls ∧ val.safe σ am decls ∧ (idx.eval σ am) < arraySizeBv decls arr
  | .barrWrite arr idx bval =>
    (idx : SExpr).safe σ am decls ∧ bval.safe σ am decls ∧ (idx.eval σ am) < arraySizeBv decls arr
  | .seq s₁ s₂ =>
    s₁.safe fuel σ am decls ∧
    match s₁.interp fuel σ am decls with
    | some (σ', am') => s₂.safe fuel σ' am' decls
    | none => True
  | .ite b s₁ s₂ =>
    b.safe σ am decls ∧ (if b.eval σ am then s₁.safe fuel σ am decls else s₂.safe fuel σ am decls)
  | .loop b body =>
    match fuel with
    | 0 => True
    | fuel' + 1 =>
      b.safe σ am decls ∧
      if b.eval σ am then
        body.safe fuel' σ am decls ∧
        match body.interp fuel' σ am decls with
        | some (σ', am') => (Stmt.loop b body).safe fuel' σ' am' decls
        | none => True
      else True
  | .fassign _ e => e.safe σ am decls
  | .farrWrite arr idx val =>
    idx.safe σ am decls ∧ val.safe σ am decls ∧ (idx.eval σ am) < arraySizeBv decls arr
  | .label _ => True
  | .goto _ => True
  | .ifgoto b _ => b.safe σ am decls
  | .print _ args => ∀ e ∈ args, e.safe σ am decls
  | .printInt e => e.safe σ am decls
  | .printBool b => b.safe σ am decls
  | .printFloat e => e.safe σ am decls
  | .printString _ => True

-- ============================================================
-- § 4a. isSafe → safe bridge
-- ============================================================

theorem SExpr.isSafe_implies_safe (e : SExpr) (σ : Store) (am : ArrayMem) (decls) :
    e.isSafe σ am decls = true → e.safe σ am decls := by
  induction e with
  | lit _ => intro; trivial
  | var _ => intro; trivial
  | bin op a b iha ihb =>
    intro h
    cases op <;> (simp only [SExpr.isSafe, Bool.and_eq_true, decide_eq_true_eq] at h;
                   simp only [SExpr.safe]) <;>
      first
      | exact ⟨iha h.1, ihb h.2⟩
      | exact ⟨iha h.1.1, ihb h.1.2, h.2⟩
  | arrRead arr idx ih =>
    simp only [SExpr.isSafe, SExpr.safe, Bool.and_eq_true, decide_eq_true_eq]
    intro ⟨hs, hb⟩; exact ⟨ih hs, hb⟩
  | flit _ => intro; trivial
  | fbin _ a b iha ihb =>
    simp only [SExpr.isSafe, SExpr.safe, Bool.and_eq_true]
    intro ⟨ha, hb⟩; exact ⟨iha ha, ihb hb⟩
  | intToFloat e ih => simp only [SExpr.isSafe, SExpr.safe]; exact ih
  | floatToInt e ih => simp only [SExpr.isSafe, SExpr.safe]; exact ih
  | floatUnary op e ih => simp only [SExpr.isSafe, SExpr.safe]; exact ih
  | farrRead arr idx ih =>
    simp only [SExpr.isSafe, SExpr.safe, Bool.and_eq_true, decide_eq_true_eq]
    intro ⟨hs, hb⟩; exact ⟨ih hs, hb⟩

theorem SBool.isSafe_implies_safe (sb : SBool) (σ : Store) (am : ArrayMem) (decls) :
    sb.isSafe σ am decls = true → sb.safe σ am decls := by
  induction sb with
  | lit _ => intro; trivial
  | bvar _ => intro; trivial
  | cmp _ a b =>
    simp only [SBool.isSafe, SBool.safe, Bool.and_eq_true]
    intro ⟨ha, hb⟩; exact ⟨SExpr.isSafe_implies_safe a σ am decls ha,
                           SExpr.isSafe_implies_safe b σ am decls hb⟩
  | not e ih =>
    simp only [SBool.isSafe, SBool.safe]; exact ih
  | and a b iha ihb =>
    simp only [SBool.isSafe, SBool.safe, Bool.and_eq_true]
    intro ⟨ha, hb⟩
    refine ⟨iha ha, fun heval => ?_⟩
    simp [heval] at hb; exact ihb hb
  | or a b iha ihb =>
    simp only [SBool.isSafe, SBool.safe, Bool.and_eq_true]
    intro ⟨ha, hb⟩
    refine ⟨iha ha, fun heval => ?_⟩
    simp [heval] at hb; exact ihb hb
  | barrRead arr idx =>
    simp only [SBool.isSafe, SBool.safe, Bool.and_eq_true, decide_eq_true_eq]
    intro ⟨hs, hb⟩; exact ⟨SExpr.isSafe_implies_safe idx σ am decls hs, hb⟩
  | fcmp _ a b =>
    simp only [SBool.isSafe, SBool.safe, Bool.and_eq_true]
    intro ⟨ha, hb⟩; exact ⟨SExpr.isSafe_implies_safe a σ am decls ha,
                           SExpr.isSafe_implies_safe b σ am decls hb⟩

theorem Stmt.interp_some_implies_safe (s : Stmt) (fuel : Nat)
    (σ σ' : Store) (am am' : ArrayMem) (decls) :
    s.interp fuel σ am decls = some (σ', am') → s.safe fuel σ am decls := by
  induction s generalizing fuel σ am σ' am' with
  | skip => intro; simp only [Stmt.safe]
  | assign x e =>
    intro h; simp only [Stmt.interp] at h
    split at h <;> simp at h
    rename_i hs
    simp only [Stmt.safe]
    exact SExpr.isSafe_implies_safe e σ am decls hs
  | bassign x b =>
    intro h; simp only [Stmt.interp] at h
    split at h <;> simp at h
    rename_i hs
    simp only [Stmt.safe]
    exact SBool.isSafe_implies_safe b σ am decls hs
  | arrWrite arr idx val =>
    intro h; simp only [Stmt.interp] at h
    split at h <;> simp at h
    rename_i hs
    simp [Bool.and_eq_true, decide_eq_true_eq] at hs
    simp only [Stmt.safe]
    exact ⟨SExpr.isSafe_implies_safe idx σ am decls hs.1.1,
           SExpr.isSafe_implies_safe val σ am decls hs.1.2, hs.2⟩
  | barrWrite arr idx bval =>
    intro h; simp only [Stmt.interp] at h
    split at h <;> simp at h
    rename_i hs
    simp [Bool.and_eq_true, decide_eq_true_eq] at hs
    simp only [Stmt.safe]
    exact ⟨SExpr.isSafe_implies_safe idx σ am decls hs.1.1,
           SBool.isSafe_implies_safe bval σ am decls hs.1.2, hs.2⟩
  | seq s1 s2 ih1 ih2 =>
    intro h; simp only [Stmt.interp, bind, Option.bind] at h
    cases h1 : s1.interp fuel σ am decls with
    | none => simp [h1] at h
    | some p =>
      obtain ⟨σ₁, am₁⟩ := p
      simp [h1] at h
      simp only [Stmt.safe]
      refine ⟨ih1 fuel σ σ₁ am am₁ h1, ?_⟩
      rw [h1]; exact ih2 fuel σ₁ σ' am₁ am' h
  | ite b s1 s2 ih1 ih2 =>
    intro h; simp only [Stmt.interp] at h
    split at h <;> rename_i hbs
    · simp only [Stmt.safe]
      refine ⟨SBool.isSafe_implies_safe b σ am decls hbs, ?_⟩
      cases heval : b.eval σ am <;> simp [heval] at h ⊢
      · exact ih2 fuel σ σ' am am' h
      · exact ih1 fuel σ σ' am am' h
    · simp at h
  | loop b body ihb =>
    induction fuel generalizing σ am σ' am' with
    | zero => intro h; simp only [Stmt.interp] at h; simp at h
    | succ fuel' ih_fuel =>
      intro h
      simp only [Stmt.interp] at h
      split at h <;> rename_i hbs
      · rw [Stmt.safe.eq_9]
        refine ⟨SBool.isSafe_implies_safe b σ am decls hbs, ?_⟩
        cases heval : b.eval σ am <;> simp [heval] at h ⊢
        cases h_body : body.interp fuel' σ am decls with
        | none => simp [h_body] at h
        | some p =>
          obtain ⟨σ₁, am₁⟩ := p
          simp [h_body] at h
          refine ⟨ihb fuel' σ σ₁ am am₁ h_body, ?_⟩
          simp [h_body]
          exact ih_fuel σ₁ σ' am₁ am' h
      · simp at h
  | fassign x e =>
    intro h; simp only [Stmt.interp] at h
    split at h <;> simp at h
    rename_i hs
    simp only [Stmt.safe]
    exact SExpr.isSafe_implies_safe e σ am decls hs
  | farrWrite arr idx val =>
    intro h; simp only [Stmt.interp] at h
    split at h <;> simp at h
    rename_i hs
    simp [Bool.and_eq_true, decide_eq_true_eq] at hs
    simp only [Stmt.safe]
    exact ⟨SExpr.isSafe_implies_safe idx σ am decls hs.1.1,
           SExpr.isSafe_implies_safe val σ am decls hs.1.2, hs.2⟩
  | label _ => intro; simp only [Stmt.safe]
  | goto _ => intro; simp only [Stmt.safe]
  | ifgoto b _ =>
    intro h; simp only [Stmt.interp] at h
    split at h
    · simp only [Stmt.safe]; exact SBool.isSafe_implies_safe b σ am decls ‹_›
    · simp at h
  | print fmt args =>
    intro h; simp only [Stmt.interp] at h
    split at h <;> simp at h
    rename_i hs
    simp only [Stmt.safe]
    intro e he
    exact SExpr.isSafe_implies_safe e σ am decls
      (List.all_eq_true.mp hs e he)
  | printInt e =>
    intro h; simp only [Stmt.interp] at h
    split at h <;> simp at h
    rename_i hs
    simp only [Stmt.safe]
    exact SExpr.isSafe_implies_safe e σ am decls hs
  | printBool b =>
    intro h; simp only [Stmt.interp] at h
    split at h <;> simp at h
    rename_i hs
    simp only [Stmt.safe]
    exact SBool.isSafe_implies_safe b σ am decls hs
  | printFloat e =>
    intro h; simp only [Stmt.interp] at h
    split at h <;> simp at h
    rename_i hs
    simp only [Stmt.safe]
    exact SExpr.isSafe_implies_safe e σ am decls hs
  | printString lit => intro _; simp only [Stmt.safe]

-- ============================================================
-- § 4a′. Unsafe classification: div vs bounds
-- ============================================================

/-! Dual predicates to `.safe`: classify *why* an unsafe expression/statement
    fails, as either a division error (`unsafeDiv`) or an array-bounds error
    (`unsafeBounds`). Ordering matches TAC's left-to-right evaluation: in
    `and`/`or` short-circuits and `seq`, whichever sub-expression is
    evaluated first wins the error classification. These predicates are
    dormant infrastructure for the backward correctness theorems. -/

def SExpr.unsafeDiv (σ : Store) (am : ArrayMem)
    (decls : List (ArrayName × Nat × VarTy)) : SExpr → Prop
  | .lit _ => False
  | .var _ => False
  | .bin .div a b =>
      a.unsafeDiv σ am decls ∨
      (a.safe σ am decls ∧ b.unsafeDiv σ am decls) ∨
      (a.safe σ am decls ∧ b.safe σ am decls ∧ b.eval σ am = 0)
  | .bin .mod a b =>
      a.unsafeDiv σ am decls ∨
      (a.safe σ am decls ∧ b.unsafeDiv σ am decls) ∨
      (a.safe σ am decls ∧ b.safe σ am decls ∧ b.eval σ am = 0)
  | .bin _ a b =>
      a.unsafeDiv σ am decls ∨ (a.safe σ am decls ∧ b.unsafeDiv σ am decls)
  | .arrRead _ idx => idx.unsafeDiv σ am decls
  | .flit _ => False
  | .fbin _ a b =>
      a.unsafeDiv σ am decls ∨ (a.safe σ am decls ∧ b.unsafeDiv σ am decls)
  | .intToFloat e => e.unsafeDiv σ am decls
  | .floatToInt e => e.unsafeDiv σ am decls
  | .floatUnary _ e => e.unsafeDiv σ am decls
  | .farrRead _ idx => idx.unsafeDiv σ am decls

def SExpr.unsafeBounds (σ : Store) (am : ArrayMem)
    (decls : List (ArrayName × Nat × VarTy)) : SExpr → Prop
  | .lit _ => False
  | .var _ => False
  | .bin _ a b =>
      a.unsafeBounds σ am decls ∨ (a.safe σ am decls ∧ b.unsafeBounds σ am decls)
  | .arrRead arr idx =>
      idx.unsafeBounds σ am decls ∨
      (idx.safe σ am decls ∧ ¬ (idx.eval σ am < arraySizeBv decls arr))
  | .flit _ => False
  | .fbin _ a b =>
      a.unsafeBounds σ am decls ∨ (a.safe σ am decls ∧ b.unsafeBounds σ am decls)
  | .intToFloat e => e.unsafeBounds σ am decls
  | .floatToInt e => e.unsafeBounds σ am decls
  | .floatUnary _ e => e.unsafeBounds σ am decls
  | .farrRead arr idx =>
      idx.unsafeBounds σ am decls ∨
      (idx.safe σ am decls ∧ ¬ (idx.eval σ am < arraySizeBv decls arr))

def SBool.unsafeDiv (σ : Store) (am : ArrayMem)
    (decls : List (ArrayName × Nat × VarTy)) : SBool → Prop
  | .lit _ => False
  | .bvar _ => False
  | .cmp _ a b =>
      a.unsafeDiv σ am decls ∨ (a.safe σ am decls ∧ b.unsafeDiv σ am decls)
  | .not e => e.unsafeDiv σ am decls
  | .and a b =>
      a.unsafeDiv σ am decls ∨
      (a.safe σ am decls ∧ a.eval σ am = true ∧ b.unsafeDiv σ am decls)
  | .or a b =>
      a.unsafeDiv σ am decls ∨
      (a.safe σ am decls ∧ a.eval σ am = false ∧ b.unsafeDiv σ am decls)
  | .barrRead _ idx => idx.unsafeDiv σ am decls
  | .fcmp _ a b =>
      a.unsafeDiv σ am decls ∨ (a.safe σ am decls ∧ b.unsafeDiv σ am decls)

def SBool.unsafeBounds (σ : Store) (am : ArrayMem)
    (decls : List (ArrayName × Nat × VarTy)) : SBool → Prop
  | .lit _ => False
  | .bvar _ => False
  | .cmp _ a b =>
      a.unsafeBounds σ am decls ∨ (a.safe σ am decls ∧ b.unsafeBounds σ am decls)
  | .not e => e.unsafeBounds σ am decls
  | .and a b =>
      a.unsafeBounds σ am decls ∨
      (a.safe σ am decls ∧ a.eval σ am = true ∧ b.unsafeBounds σ am decls)
  | .or a b =>
      a.unsafeBounds σ am decls ∨
      (a.safe σ am decls ∧ a.eval σ am = false ∧ b.unsafeBounds σ am decls)
  | .barrRead arr idx =>
      idx.unsafeBounds σ am decls ∨
      (idx.safe σ am decls ∧ ¬ (idx.eval σ am < arraySizeBv decls arr))
  | .fcmp _ a b =>
      a.unsafeBounds σ am decls ∨ (a.safe σ am decls ∧ b.unsafeBounds σ am decls)

/-- First-error-wins lifts of the `SExpr` unsafe predicates to `List SExpr`.
    Used by the `Stmt.print` case (variadic print evaluates args left-to-right). -/
def SExpr.listUnsafeDiv (σ : Store) (am : ArrayMem)
    (decls : List (ArrayName × Nat × VarTy)) : List SExpr → Prop
  | [] => False
  | e :: rest =>
      e.unsafeDiv σ am decls ∨
      (e.safe σ am decls ∧ SExpr.listUnsafeDiv σ am decls rest)

def SExpr.listUnsafeBounds (σ : Store) (am : ArrayMem)
    (decls : List (ArrayName × Nat × VarTy)) : List SExpr → Prop
  | [] => False
  | e :: rest =>
      e.unsafeBounds σ am decls ∨
      (e.safe σ am decls ∧ SExpr.listUnsafeBounds σ am decls rest)

def Stmt.unsafeDiv (fuel : Nat) (σ : Store) (am : ArrayMem)
    (decls : List (ArrayName × Nat × VarTy)) : Stmt → Prop
  | .skip => False
  | .assign _ e => e.unsafeDiv σ am decls
  | .bassign _ b => b.unsafeDiv σ am decls
  | .arrWrite _ idx val =>
      idx.unsafeDiv σ am decls ∨ (idx.safe σ am decls ∧ val.unsafeDiv σ am decls)
  | .barrWrite _ idx bval =>
      idx.unsafeDiv σ am decls ∨ (idx.safe σ am decls ∧ bval.unsafeDiv σ am decls)
  | .seq s₁ s₂ =>
      s₁.unsafeDiv fuel σ am decls ∨
      (s₁.safe fuel σ am decls ∧
        match s₁.interp fuel σ am decls with
        | some (σ', am') => s₂.unsafeDiv fuel σ' am' decls
        | none => False)
  | .ite b s₁ s₂ =>
      b.unsafeDiv σ am decls ∨
      (b.safe σ am decls ∧
        (if b.eval σ am then s₁.unsafeDiv fuel σ am decls
         else s₂.unsafeDiv fuel σ am decls))
  | .loop b body =>
      match fuel with
      | 0 => False
      | fuel' + 1 =>
        b.unsafeDiv σ am decls ∨
        (b.safe σ am decls ∧ b.eval σ am = true ∧
          (body.unsafeDiv fuel' σ am decls ∨
            (body.safe fuel' σ am decls ∧
              match body.interp fuel' σ am decls with
              | some (σ', am') => (Stmt.loop b body).unsafeDiv fuel' σ' am' decls
              | none => False)))
  | .fassign _ e => e.unsafeDiv σ am decls
  | .farrWrite _ idx val =>
      idx.unsafeDiv σ am decls ∨ (idx.safe σ am decls ∧ val.unsafeDiv σ am decls)
  | .label _ => False
  | .goto _ => False
  | .ifgoto b _ => b.unsafeDiv σ am decls
  | .print _ args => SExpr.listUnsafeDiv σ am decls args
  | .printInt e => e.unsafeDiv σ am decls
  | .printBool b => b.unsafeDiv σ am decls
  | .printFloat e => e.unsafeDiv σ am decls
  | .printString _ => False

def Stmt.unsafeBounds (fuel : Nat) (σ : Store) (am : ArrayMem)
    (decls : List (ArrayName × Nat × VarTy)) : Stmt → Prop
  | .skip => False
  | .assign _ e => e.unsafeBounds σ am decls
  | .bassign _ b => b.unsafeBounds σ am decls
  | .arrWrite arr idx val =>
      idx.unsafeBounds σ am decls ∨
      (idx.safe σ am decls ∧ val.unsafeBounds σ am decls) ∨
      (idx.safe σ am decls ∧ val.safe σ am decls ∧
        ¬ (idx.eval σ am < arraySizeBv decls arr))
  | .barrWrite arr idx bval =>
      idx.unsafeBounds σ am decls ∨
      (idx.safe σ am decls ∧ bval.unsafeBounds σ am decls) ∨
      (idx.safe σ am decls ∧ bval.safe σ am decls ∧
        ¬ (idx.eval σ am < arraySizeBv decls arr))
  | .seq s₁ s₂ =>
      s₁.unsafeBounds fuel σ am decls ∨
      (s₁.safe fuel σ am decls ∧
        match s₁.interp fuel σ am decls with
        | some (σ', am') => s₂.unsafeBounds fuel σ' am' decls
        | none => False)
  | .ite b s₁ s₂ =>
      b.unsafeBounds σ am decls ∨
      (b.safe σ am decls ∧
        (if b.eval σ am then s₁.unsafeBounds fuel σ am decls
         else s₂.unsafeBounds fuel σ am decls))
  | .loop b body =>
      match fuel with
      | 0 => False
      | fuel' + 1 =>
        b.unsafeBounds σ am decls ∨
        (b.safe σ am decls ∧ b.eval σ am = true ∧
          (body.unsafeBounds fuel' σ am decls ∨
            (body.safe fuel' σ am decls ∧
              match body.interp fuel' σ am decls with
              | some (σ', am') => (Stmt.loop b body).unsafeBounds fuel' σ' am' decls
              | none => False)))
  | .fassign _ e => e.unsafeBounds σ am decls
  | .farrWrite arr idx val =>
      idx.unsafeBounds σ am decls ∨
      (idx.safe σ am decls ∧ val.unsafeBounds σ am decls) ∨
      (idx.safe σ am decls ∧ val.safe σ am decls ∧
        ¬ (idx.eval σ am < arraySizeBv decls arr))
  | .label _ => False
  | .goto _ => False
  | .ifgoto b _ => b.unsafeBounds σ am decls
  | .print _ args => SExpr.listUnsafeBounds σ am decls args
  | .printInt e => e.unsafeBounds σ am decls
  | .printBool b => b.unsafeBounds σ am decls
  | .printFloat e => e.unsafeBounds σ am decls
  | .printString _ => False

/-! ### Bridge lemmas: `safe` vs `unsafeDiv`/`unsafeBounds`

Every well-formed subterm is in exactly one of three classes — `safe`,
`unsafeDiv`, or `unsafeBounds`. The main lemmas package this into the
two forms Phase 3+ will consume: the iff
`¬ safe ↔ unsafeDiv ∨ unsafeBounds` and the disjointness
`¬ (unsafeDiv ∧ unsafeBounds)`. -/

section UnsafeSplit
open Classical

theorem SExpr.safe_iff_not_unsafe (e : SExpr) (σ : Store) (am : ArrayMem)
    (decls : List (ArrayName × Nat × VarTy)) :
    e.safe σ am decls ↔ ¬ e.unsafeDiv σ am decls ∧ ¬ e.unsafeBounds σ am decls := by
  induction e with
  | lit _ => simp [SExpr.safe, SExpr.unsafeDiv, SExpr.unsafeBounds]
  | var _ => simp [SExpr.safe, SExpr.unsafeDiv, SExpr.unsafeBounds]
  | bin op a b iha ihb =>
    cases op <;>
      (simp only [SExpr.safe, SExpr.unsafeDiv, SExpr.unsafeBounds, ne_eq]; tauto)
  | arrRead arr idx ih =>
    simp only [SExpr.safe, SExpr.unsafeDiv, SExpr.unsafeBounds]; tauto
  | flit _ => simp [SExpr.safe, SExpr.unsafeDiv, SExpr.unsafeBounds]
  | fbin op a b iha ihb =>
    simp only [SExpr.safe, SExpr.unsafeDiv, SExpr.unsafeBounds]; tauto
  | intToFloat e ih =>
    simp only [SExpr.safe, SExpr.unsafeDiv, SExpr.unsafeBounds]; exact ih
  | floatToInt e ih =>
    simp only [SExpr.safe, SExpr.unsafeDiv, SExpr.unsafeBounds]; exact ih
  | floatUnary op e ih =>
    simp only [SExpr.safe, SExpr.unsafeDiv, SExpr.unsafeBounds]; exact ih
  | farrRead arr idx ih =>
    simp only [SExpr.safe, SExpr.unsafeDiv, SExpr.unsafeBounds]; tauto

theorem SExpr.not_safe_iff_unsafeDiv_or_unsafeBounds (e : SExpr) (σ : Store)
    (am : ArrayMem) (decls : List (ArrayName × Nat × VarTy)) :
    ¬ e.safe σ am decls ↔ e.unsafeDiv σ am decls ∨ e.unsafeBounds σ am decls := by
  rw [SExpr.safe_iff_not_unsafe]; push_neg; tauto

theorem SExpr.unsafeDiv_unsafeBounds_disjoint (e : SExpr) (σ : Store)
    (am : ArrayMem) (decls : List (ArrayName × Nat × VarTy)) :
    ¬ (e.unsafeDiv σ am decls ∧ e.unsafeBounds σ am decls) := by
  induction e with
  | lit _ => simp [SExpr.unsafeDiv, SExpr.unsafeBounds]
  | var _ => simp [SExpr.unsafeDiv, SExpr.unsafeBounds]
  | bin op a b iha ihb =>
    cases op <;>
      (simp only [SExpr.unsafeDiv, SExpr.unsafeBounds,
                  SExpr.safe_iff_not_unsafe a σ am decls,
                  SExpr.safe_iff_not_unsafe b σ am decls,
                  not_and, not_or, Decidable.not_not]
       tauto)
  | arrRead arr idx ih =>
    simp only [SExpr.unsafeDiv, SExpr.unsafeBounds,
               SExpr.safe_iff_not_unsafe idx σ am decls,
               not_and, not_or, Decidable.not_not]
    tauto
  | flit _ => simp [SExpr.unsafeDiv, SExpr.unsafeBounds]
  | fbin op a b iha ihb =>
    simp only [SExpr.unsafeDiv, SExpr.unsafeBounds,
               SExpr.safe_iff_not_unsafe a σ am decls,
               SExpr.safe_iff_not_unsafe b σ am decls,
               not_and, not_or, Decidable.not_not]
    tauto
  | intToFloat e ih => simp only [SExpr.unsafeDiv, SExpr.unsafeBounds]; exact ih
  | floatToInt e ih => simp only [SExpr.unsafeDiv, SExpr.unsafeBounds]; exact ih
  | floatUnary op e ih => simp only [SExpr.unsafeDiv, SExpr.unsafeBounds]; exact ih
  | farrRead arr idx ih =>
    simp only [SExpr.unsafeDiv, SExpr.unsafeBounds,
               SExpr.safe_iff_not_unsafe idx σ am decls,
               not_and, not_or, Decidable.not_not]
    tauto

theorem SBool.safe_iff_not_unsafe (sb : SBool) (σ : Store) (am : ArrayMem)
    (decls : List (ArrayName × Nat × VarTy)) :
    sb.safe σ am decls ↔ ¬ sb.unsafeDiv σ am decls ∧ ¬ sb.unsafeBounds σ am decls := by
  induction sb with
  | lit _ => simp [SBool.safe, SBool.unsafeDiv, SBool.unsafeBounds]
  | bvar _ => simp [SBool.safe, SBool.unsafeDiv, SBool.unsafeBounds]
  | cmp _ a b =>
    simp only [SBool.safe, SBool.unsafeDiv, SBool.unsafeBounds,
               SExpr.safe_iff_not_unsafe a σ am decls,
               SExpr.safe_iff_not_unsafe b σ am decls,
               not_or, not_and, Decidable.not_not]
    tauto
  | not e ih => simp only [SBool.safe, SBool.unsafeDiv, SBool.unsafeBounds]; exact ih
  | and a b iha ihb =>
    simp only [SBool.safe, SBool.unsafeDiv, SBool.unsafeBounds, iha, ihb,
               not_or, not_and, Decidable.not_not]
    tauto
  | or a b iha ihb =>
    simp only [SBool.safe, SBool.unsafeDiv, SBool.unsafeBounds, iha, ihb,
               not_or, not_and, Decidable.not_not]
    tauto
  | barrRead arr idx =>
    simp only [SBool.safe, SBool.unsafeDiv, SBool.unsafeBounds,
               SExpr.safe_iff_not_unsafe idx σ am decls,
               not_or, not_and, Decidable.not_not]
    tauto
  | fcmp _ a b =>
    simp only [SBool.safe, SBool.unsafeDiv, SBool.unsafeBounds,
               SExpr.safe_iff_not_unsafe a σ am decls,
               SExpr.safe_iff_not_unsafe b σ am decls,
               not_or, not_and, Decidable.not_not]
    tauto

theorem SBool.not_safe_iff_unsafeDiv_or_unsafeBounds (sb : SBool) (σ : Store)
    (am : ArrayMem) (decls : List (ArrayName × Nat × VarTy)) :
    ¬ sb.safe σ am decls ↔ sb.unsafeDiv σ am decls ∨ sb.unsafeBounds σ am decls := by
  rw [SBool.safe_iff_not_unsafe]; push_neg; tauto

theorem SBool.unsafeDiv_unsafeBounds_disjoint (sb : SBool) (σ : Store)
    (am : ArrayMem) (decls : List (ArrayName × Nat × VarTy)) :
    ¬ (sb.unsafeDiv σ am decls ∧ sb.unsafeBounds σ am decls) := by
  induction sb with
  | lit _ => simp [SBool.unsafeDiv, SBool.unsafeBounds]
  | bvar _ => simp [SBool.unsafeDiv, SBool.unsafeBounds]
  | cmp _ a b =>
    simp only [SBool.unsafeDiv, SBool.unsafeBounds,
               SExpr.safe_iff_not_unsafe a σ am decls,
               SExpr.safe_iff_not_unsafe b σ am decls,
               not_and, not_or, Decidable.not_not]
    have ha := SExpr.unsafeDiv_unsafeBounds_disjoint a σ am decls
    have hb := SExpr.unsafeDiv_unsafeBounds_disjoint b σ am decls
    tauto
  | not e ih => simp only [SBool.unsafeDiv, SBool.unsafeBounds]; exact ih
  | and a b iha ihb =>
    simp only [SBool.unsafeDiv, SBool.unsafeBounds,
               SBool.safe_iff_not_unsafe a σ am decls,
               not_and, not_or, Decidable.not_not]
    tauto
  | or a b iha ihb =>
    simp only [SBool.unsafeDiv, SBool.unsafeBounds,
               SBool.safe_iff_not_unsafe a σ am decls,
               not_and, not_or, Decidable.not_not]
    tauto
  | barrRead arr idx =>
    simp only [SBool.unsafeDiv, SBool.unsafeBounds,
               SExpr.safe_iff_not_unsafe idx σ am decls,
               not_and, not_or, Decidable.not_not]
    have hidx := SExpr.unsafeDiv_unsafeBounds_disjoint idx σ am decls
    tauto
  | fcmp _ a b =>
    simp only [SBool.unsafeDiv, SBool.unsafeBounds,
               SExpr.safe_iff_not_unsafe a σ am decls,
               SExpr.safe_iff_not_unsafe b σ am decls,
               not_and, not_or, Decidable.not_not]
    have ha := SExpr.unsafeDiv_unsafeBounds_disjoint a σ am decls
    have hb := SExpr.unsafeDiv_unsafeBounds_disjoint b σ am decls
    tauto

theorem SExpr.listSafe_iff_not_unsafe (args : List SExpr) (σ : Store) (am : ArrayMem)
    (decls : List (ArrayName × Nat × VarTy)) :
    (∀ e ∈ args, e.safe σ am decls) ↔
      ¬ SExpr.listUnsafeDiv σ am decls args ∧ ¬ SExpr.listUnsafeBounds σ am decls args := by
  induction args with
  | nil => simp [SExpr.listUnsafeDiv, SExpr.listUnsafeBounds]
  | cons e rest ih =>
    simp only [List.mem_cons, forall_eq_or_imp, SExpr.listUnsafeDiv, SExpr.listUnsafeBounds,
               SExpr.safe_iff_not_unsafe e σ am decls, ih,
               not_or, not_and, Decidable.not_not]
    tauto

theorem SExpr.listUnsafeDiv_listUnsafeBounds_disjoint (args : List SExpr) (σ : Store)
    (am : ArrayMem) (decls : List (ArrayName × Nat × VarTy)) :
    ¬ (SExpr.listUnsafeDiv σ am decls args ∧ SExpr.listUnsafeBounds σ am decls args) := by
  induction args with
  | nil => simp [SExpr.listUnsafeDiv, SExpr.listUnsafeBounds]
  | cons e rest ih =>
    simp only [SExpr.listUnsafeDiv, SExpr.listUnsafeBounds,
               SExpr.safe_iff_not_unsafe e σ am decls,
               not_and, not_or, Decidable.not_not]
    have he := SExpr.unsafeDiv_unsafeBounds_disjoint e σ am decls
    tauto

theorem Stmt.safe_iff_not_unsafe (s : Stmt) (fuel : Nat) (σ : Store) (am : ArrayMem)
    (decls : List (ArrayName × Nat × VarTy)) :
    s.safe fuel σ am decls ↔
      ¬ s.unsafeDiv fuel σ am decls ∧ ¬ s.unsafeBounds fuel σ am decls := by
  induction s generalizing fuel σ am with
  | skip => simp [Stmt.safe, Stmt.unsafeDiv, Stmt.unsafeBounds]
  | assign x e =>
    simp only [Stmt.safe, Stmt.unsafeDiv, Stmt.unsafeBounds]
    exact SExpr.safe_iff_not_unsafe e σ am decls
  | bassign x b =>
    simp only [Stmt.safe, Stmt.unsafeDiv, Stmt.unsafeBounds]
    exact SBool.safe_iff_not_unsafe b σ am decls
  | arrWrite arr idx val =>
    simp only [Stmt.safe, Stmt.unsafeDiv, Stmt.unsafeBounds,
               SExpr.safe_iff_not_unsafe idx σ am decls,
               SExpr.safe_iff_not_unsafe val σ am decls,
               not_or, not_and, Decidable.not_not]
    tauto
  | barrWrite arr idx bval =>
    simp only [Stmt.safe, Stmt.unsafeDiv, Stmt.unsafeBounds,
               SExpr.safe_iff_not_unsafe idx σ am decls,
               SBool.safe_iff_not_unsafe bval σ am decls,
               not_or, not_and, Decidable.not_not]
    tauto
  | seq s₁ s₂ ih1 ih2 =>
    simp only [Stmt.safe, Stmt.unsafeDiv, Stmt.unsafeBounds, ih1,
               not_or, not_and, Decidable.not_not]
    cases h : s₁.interp fuel σ am decls with
    | none => simp [h]
    | some p =>
      obtain ⟨σ', am'⟩ := p
      simp only [h, ih2]
      tauto
  | ite b s1 s2 ih1 ih2 =>
    simp only [Stmt.safe, Stmt.unsafeDiv, Stmt.unsafeBounds,
               SBool.safe_iff_not_unsafe b σ am decls, ih1, ih2,
               not_or, not_and, Decidable.not_not]
    by_cases hb : b.eval σ am
    · simp [hb] <;> tauto
    · simp [hb] <;> tauto
  | loop b body ihbody =>
    induction fuel generalizing σ am with
    | zero => simp [Stmt.safe, Stmt.unsafeDiv, Stmt.unsafeBounds]
    | succ fuel' ih_fuel =>
      simp only [Stmt.safe, Stmt.unsafeDiv, Stmt.unsafeBounds,
                 SBool.safe_iff_not_unsafe b σ am decls,
                 not_or, not_and, Decidable.not_not]
      by_cases hbe : b.eval σ am
      · simp only [hbe, if_true, ihbody fuel' σ am]
        cases h : body.interp fuel' σ am decls with
        | none => simp [h] <;> tauto
        | some p =>
          obtain ⟨σ', am'⟩ := p
          simp only [h, ih_fuel σ' am']
          tauto
      · simp [hbe]
  | fassign x e =>
    simp only [Stmt.safe, Stmt.unsafeDiv, Stmt.unsafeBounds]
    exact SExpr.safe_iff_not_unsafe e σ am decls
  | farrWrite arr idx val =>
    simp only [Stmt.safe, Stmt.unsafeDiv, Stmt.unsafeBounds,
               SExpr.safe_iff_not_unsafe idx σ am decls,
               SExpr.safe_iff_not_unsafe val σ am decls,
               not_or, not_and, Decidable.not_not]
    tauto
  | label _ => simp [Stmt.safe, Stmt.unsafeDiv, Stmt.unsafeBounds]
  | goto _ => simp [Stmt.safe, Stmt.unsafeDiv, Stmt.unsafeBounds]
  | ifgoto b _ =>
    simp only [Stmt.safe, Stmt.unsafeDiv, Stmt.unsafeBounds]
    exact SBool.safe_iff_not_unsafe b σ am decls
  | print _ args =>
    simp only [Stmt.safe, Stmt.unsafeDiv, Stmt.unsafeBounds]
    exact SExpr.listSafe_iff_not_unsafe args σ am decls
  | printInt e =>
    simp only [Stmt.safe, Stmt.unsafeDiv, Stmt.unsafeBounds]
    exact SExpr.safe_iff_not_unsafe e σ am decls
  | printBool b =>
    simp only [Stmt.safe, Stmt.unsafeDiv, Stmt.unsafeBounds]
    exact SBool.safe_iff_not_unsafe b σ am decls
  | printFloat e =>
    simp only [Stmt.safe, Stmt.unsafeDiv, Stmt.unsafeBounds]
    exact SExpr.safe_iff_not_unsafe e σ am decls
  | printString _ => simp [Stmt.safe, Stmt.unsafeDiv, Stmt.unsafeBounds]

/-- Phase 1 target lemma: `¬ safe ↔ unsafeDiv ∨ unsafeBounds`. -/
theorem Stmt.not_safe_iff_unsafeDiv_or_unsafeBounds (s : Stmt) (fuel : Nat) (σ : Store)
    (am : ArrayMem) (decls : List (ArrayName × Nat × VarTy)) :
    ¬ s.safe fuel σ am decls ↔
      s.unsafeDiv fuel σ am decls ∨ s.unsafeBounds fuel σ am decls := by
  rw [Stmt.safe_iff_not_unsafe]; push_neg; tauto

/-- Phase 1 target lemma: `unsafeDiv` and `unsafeBounds` are disjoint. -/
theorem Stmt.unsafeDiv_unsafeBounds_disjoint (s : Stmt) (fuel : Nat) (σ : Store)
    (am : ArrayMem) (decls : List (ArrayName × Nat × VarTy)) :
    ¬ (s.unsafeDiv fuel σ am decls ∧ s.unsafeBounds fuel σ am decls) := by
  induction s generalizing fuel σ am with
  | skip => simp [Stmt.unsafeDiv, Stmt.unsafeBounds]
  | assign x e =>
    simp only [Stmt.unsafeDiv, Stmt.unsafeBounds]
    exact SExpr.unsafeDiv_unsafeBounds_disjoint e σ am decls
  | bassign x b =>
    simp only [Stmt.unsafeDiv, Stmt.unsafeBounds]
    exact SBool.unsafeDiv_unsafeBounds_disjoint b σ am decls
  | arrWrite arr idx val =>
    simp only [Stmt.unsafeDiv, Stmt.unsafeBounds,
               SExpr.safe_iff_not_unsafe idx σ am decls,
               SExpr.safe_iff_not_unsafe val σ am decls,
               not_and, not_or, Decidable.not_not]
    have hidx := SExpr.unsafeDiv_unsafeBounds_disjoint idx σ am decls
    have hval := SExpr.unsafeDiv_unsafeBounds_disjoint val σ am decls
    tauto
  | barrWrite arr idx bval =>
    simp only [Stmt.unsafeDiv, Stmt.unsafeBounds,
               SExpr.safe_iff_not_unsafe idx σ am decls,
               SBool.safe_iff_not_unsafe bval σ am decls,
               not_and, not_or, Decidable.not_not]
    have hidx := SExpr.unsafeDiv_unsafeBounds_disjoint idx σ am decls
    have hval := SBool.unsafeDiv_unsafeBounds_disjoint bval σ am decls
    tauto
  | seq s1 s2 ih1 ih2 =>
    simp only [Stmt.unsafeDiv, Stmt.unsafeBounds,
               Stmt.safe_iff_not_unsafe s1 fuel σ am decls,
               not_and, not_or, Decidable.not_not]
    cases h : s1.interp fuel σ am decls with
    | none => simp [h]; have := ih1 (fuel := fuel) (σ := σ) (am := am); tauto
    | some p =>
      obtain ⟨σ', am'⟩ := p
      simp only [h]
      have h1 := ih1 (fuel := fuel) (σ := σ) (am := am)
      have h2 := ih2 (fuel := fuel) (σ := σ') (am := am')
      tauto
  | ite b s1 s2 ih1 ih2 =>
    simp only [Stmt.unsafeDiv, Stmt.unsafeBounds,
               SBool.safe_iff_not_unsafe b σ am decls,
               not_and, not_or, Decidable.not_not]
    have hb := SBool.unsafeDiv_unsafeBounds_disjoint b σ am decls
    by_cases hbe : b.eval σ am
    · simp only [hbe, if_true]
      have := ih1 (fuel := fuel) (σ := σ) (am := am)
      tauto
    · simp only [hbe, if_false]
      have := ih2 (fuel := fuel) (σ := σ) (am := am)
      tauto
  | loop b body ihbody =>
    induction fuel generalizing σ am with
    | zero => simp [Stmt.unsafeDiv, Stmt.unsafeBounds]
    | succ fuel' ih_fuel =>
      simp only [Stmt.unsafeDiv, Stmt.unsafeBounds,
                 SBool.safe_iff_not_unsafe b σ am decls,
                 not_and, not_or, Decidable.not_not]
      have hb := SBool.unsafeDiv_unsafeBounds_disjoint b σ am decls
      by_cases hbe : b.eval σ am
      · simp only [hbe]
        have hbody_disj := ihbody (fuel := fuel') (σ := σ) (am := am)
        have hbody_iff :=
          Stmt.safe_iff_not_unsafe body fuel' σ am decls
        simp only [hbody_iff, not_and, Decidable.not_not]
        cases h : body.interp fuel' σ am decls with
        | none => simp [h] <;> tauto
        | some p =>
          obtain ⟨σ', am'⟩ := p
          simp only [h]
          have := ih_fuel σ' am'
          tauto
      · simp [hbe] <;> tauto
  | fassign x e =>
    simp only [Stmt.unsafeDiv, Stmt.unsafeBounds]
    exact SExpr.unsafeDiv_unsafeBounds_disjoint e σ am decls
  | farrWrite arr idx val =>
    simp only [Stmt.unsafeDiv, Stmt.unsafeBounds,
               SExpr.safe_iff_not_unsafe idx σ am decls,
               SExpr.safe_iff_not_unsafe val σ am decls,
               not_and, not_or, Decidable.not_not]
    have hidx := SExpr.unsafeDiv_unsafeBounds_disjoint idx σ am decls
    have hval := SExpr.unsafeDiv_unsafeBounds_disjoint val σ am decls
    tauto
  | label _ => simp [Stmt.unsafeDiv, Stmt.unsafeBounds]
  | goto _ => simp [Stmt.unsafeDiv, Stmt.unsafeBounds]
  | ifgoto b _ =>
    simp only [Stmt.unsafeDiv, Stmt.unsafeBounds]
    exact SBool.unsafeDiv_unsafeBounds_disjoint b σ am decls
  | print _ args =>
    simp only [Stmt.unsafeDiv, Stmt.unsafeBounds]
    exact SExpr.listUnsafeDiv_listUnsafeBounds_disjoint args σ am decls
  | printInt e =>
    simp only [Stmt.unsafeDiv, Stmt.unsafeBounds]
    exact SExpr.unsafeDiv_unsafeBounds_disjoint e σ am decls
  | printBool b =>
    simp only [Stmt.unsafeDiv, Stmt.unsafeBounds]
    exact SBool.unsafeDiv_unsafeBounds_disjoint b σ am decls
  | printFloat e =>
    simp only [Stmt.unsafeDiv, Stmt.unsafeBounds]
    exact SExpr.unsafeDiv_unsafeBounds_disjoint e σ am decls
  | printString _ => simp [Stmt.unsafeDiv, Stmt.unsafeBounds]

end UnsafeSplit

-- ============================================================
-- § 4a'. Cause-aware program runner
-- ============================================================

namespace Program

/-- Cause-tagged result of running a `Program` with bounded fuel.
    Distinguishes safe halt, the two runtime errors, and fuel exhaustion. -/
inductive RunResult where
  | halts (σ : Store) (am : ArrayMem) : RunResult
  | divByZero : RunResult
  | outOfBounds : RunResult
  | outOfFuel : RunResult

/-- Cause-aware program run.  Returns:
- `.halts σ am`     if the program terminates safely.
- `.divByZero`      if a div-by-zero error is reached within `fuel` steps.
- `.outOfBounds`    if an out-of-bounds array access is reached within `fuel` steps.
- `.outOfFuel`      if `fuel` is exhausted before any of the above resolve.

Spec-level wrapper around `interp` plus the `unsafeDiv`/`unsafeBounds`
predicates from § 4a.  `noncomputable` because cause classification uses
classical decidability on `Prop`-level predicates; for actual execution
use `prog.interp`. -/
noncomputable def run (prog : Program) (fuel : Nat)
    (inputs : List (Var × Value) := []) : RunResult :=
  open Classical in
  let σ₀ := inputs.foldl (fun σ (x, v) => σ[x ↦ v]) prog.initStore
  if prog.body.unsafeDiv fuel σ₀ ArrayMem.init prog.arrayDecls then .divByZero
  else if prog.body.unsafeBounds fuel σ₀ ArrayMem.init prog.arrayDecls then .outOfBounds
  else match prog.body.interp fuel σ₀ ArrayMem.init prog.arrayDecls with
       | some (σ, am) => .halts σ am
       | none => .outOfFuel

/-- With default (empty) inputs, `prog.run fuel = .divByZero` iff the body's
    `unsafeDiv` predicate fires at this fuel from the declaration-default store. -/
theorem run_divByZero_iff (prog : Program) (fuel : Nat) :
    prog.run fuel = .divByZero ↔
      prog.body.unsafeDiv fuel prog.initStore ArrayMem.init prog.arrayDecls := by
  classical
  constructor
  · intro h
    by_cases hd : prog.body.unsafeDiv fuel prog.initStore ArrayMem.init prog.arrayDecls
    · exact hd
    · exfalso
      unfold run at h
      simp only [List.foldl_nil, hd, if_false] at h
      by_cases hb : prog.body.unsafeBounds fuel prog.initStore ArrayMem.init prog.arrayDecls
      · simp [hb] at h
      · simp only [hb, if_false] at h
        split at h <;> cases h
  · intro hd
    unfold run
    simp [List.foldl_nil, hd]

/-- With default (empty) inputs, `prog.run fuel = .outOfBounds` iff the body's
    `unsafeBounds` predicate fires at this fuel from the declaration-default store.
    Disjointness rules out the cross-cause case. -/
theorem run_outOfBounds_iff (prog : Program) (fuel : Nat) :
    prog.run fuel = .outOfBounds ↔
      prog.body.unsafeBounds fuel prog.initStore ArrayMem.init prog.arrayDecls := by
  classical
  constructor
  · intro h
    unfold run at h
    simp only [List.foldl_nil] at h
    by_cases hd : prog.body.unsafeDiv fuel prog.initStore ArrayMem.init prog.arrayDecls
    · simp [hd] at h
    · simp only [hd, if_false] at h
      by_cases hb : prog.body.unsafeBounds fuel prog.initStore ArrayMem.init prog.arrayDecls
      · exact hb
      · simp only [hb, if_false] at h
        split at h <;> cases h
  · intro hb
    have hd : ¬ prog.body.unsafeDiv fuel prog.initStore ArrayMem.init prog.arrayDecls :=
      fun hd => Stmt.unsafeDiv_unsafeBounds_disjoint prog.body fuel prog.initStore
        ArrayMem.init prog.arrayDecls ⟨hd, hb⟩
    unfold run
    simp [List.foldl_nil, hd, hb]

/-- With default (empty) inputs, `prog.run fuel = .halts σ am` iff `prog.interp fuel`
    returns `some (σ, am)`.  (Backward uses `interp_some_implies_safe` to rule out
    the unsafe branches of `run`.) -/
theorem run_halts_iff (prog : Program) (fuel : Nat) (σ : Store) (am : ArrayMem) :
    prog.run fuel = .halts σ am ↔ prog.interp fuel = some (σ, am) := by
  classical
  constructor
  · intro h
    unfold run at h
    simp only [List.foldl_nil] at h
    by_cases hd : prog.body.unsafeDiv fuel prog.initStore ArrayMem.init prog.arrayDecls
    · simp [hd] at h
    · by_cases hb : prog.body.unsafeBounds fuel prog.initStore ArrayMem.init prog.arrayDecls
      · simp [hd, hb] at h
      · simp only [hd, hb, if_false] at h
        split at h
        · rename_i σ' am' hi
          cases h
          unfold Program.interp; simp [List.foldl_nil, hi]
        · cases h
  · intro hi
    have hi' : prog.body.interp fuel prog.initStore ArrayMem.init prog.arrayDecls = some (σ, am) := by
      unfold Program.interp at hi; simp only [List.foldl_nil] at hi; exact hi
    have hsafe := Stmt.interp_some_implies_safe prog.body fuel _ _ _ _ _ hi'
    have ⟨hnd, hnb⟩ := (Stmt.safe_iff_not_unsafe prog.body fuel
      prog.initStore ArrayMem.init prog.arrayDecls).mp hsafe
    unfold run
    simp [List.foldl_nil, hnd, hnb, hi']

/-- With default (empty) inputs, `prog.run fuel = .outOfFuel` iff source is safe
    at this fuel AND `prog.interp fuel = none`. -/
theorem run_outOfFuel_iff (prog : Program) (fuel : Nat) :
    prog.run fuel = .outOfFuel ↔
      prog.body.safe fuel prog.initStore ArrayMem.init prog.arrayDecls ∧
      prog.interp fuel = none := by
  classical
  constructor
  · intro h
    unfold run at h
    simp only [List.foldl_nil] at h
    by_cases hd : prog.body.unsafeDiv fuel prog.initStore ArrayMem.init prog.arrayDecls
    · simp [hd] at h
    · by_cases hb : prog.body.unsafeBounds fuel prog.initStore ArrayMem.init prog.arrayDecls
      · simp [hd, hb] at h
      · refine ⟨(Stmt.safe_iff_not_unsafe _ _ _ _ _).mpr ⟨hd, hb⟩, ?_⟩
        unfold Program.interp; simp only [List.foldl_nil]
        simp only [hd, hb, if_false] at h
        split at h
        · cases h
        · rename_i hi; exact hi
  · intro ⟨hsafe, hi⟩
    have ⟨hnd, hnb⟩ := (Stmt.safe_iff_not_unsafe prog.body fuel
      prog.initStore ArrayMem.init prog.arrayDecls).mp hsafe
    have hi' : prog.body.interp fuel prog.initStore ArrayMem.init prog.arrayDecls = none := by
      unfold Program.interp at hi; simp only [List.foldl_nil] at hi; exact hi
    unfold run
    simp [List.foldl_nil, hnd, hnb, hi']

end Program

-- ============================================================
-- § 4b. Integer typing (all arithmetic-position variables have int values)
-- ============================================================

/-- Context-sensitive typing for statements. Uses `typedVars` and `wrapEval`
    instead of the broken `intTyped` which assumes all vars are int. -/
def Stmt.typedVars (fuel : Nat) (σ : Store) (am : ArrayMem)
    (decls : List (ArrayName × Nat × VarTy)) : Stmt → Prop
  | .skip => True
  | .assign _ e => e.typedVars σ am ∧ e.wrapEval σ am = .int (e.eval σ am)
  | .bassign _ b => b.typedVars σ am
  | .arrWrite _ idx val =>
    (idx.typedVars σ am ∧ idx.wrapEval σ am = .int (idx.eval σ am)) ∧
    (val.typedVars σ am ∧ val.wrapEval σ am = .int (val.eval σ am))
  | .barrWrite _ idx bval =>
    (idx.typedVars σ am ∧ idx.wrapEval σ am = .int (idx.eval σ am)) ∧ bval.typedVars σ am
  | .seq s₁ s₂ =>
    s₁.typedVars fuel σ am decls ∧
    match s₁.interp fuel σ am decls with
    | some (σ', am') => s₂.typedVars fuel σ' am' decls
    | none => True
  | .ite b s₁ s₂ =>
    b.typedVars σ am ∧ (if b.eval σ am then s₁.typedVars fuel σ am decls else s₂.typedVars fuel σ am decls)
  | .loop b body =>
    match fuel with
    | 0 => True
    | fuel' + 1 =>
      b.typedVars σ am ∧
      if b.eval σ am then
        body.typedVars fuel' σ am decls ∧
        match body.interp fuel' σ am decls with
        | some (σ', am') => (Stmt.loop b body).typedVars fuel' σ' am' decls
        | none => True
      else True
  | .fassign _ e => e.typedVars σ am ∧ e.wrapEval σ am = .float (e.eval σ am)
  | .farrWrite _ idx val =>
    (idx.typedVars σ am ∧ idx.wrapEval σ am = .int (idx.eval σ am)) ∧
    (val.typedVars σ am ∧ val.wrapEval σ am = .float (val.eval σ am))
  | .label _ => True
  | .goto _ => True
  | .ifgoto b _ => b.typedVars σ am
  | .print _ args => ∀ e ∈ args, e.typedVars σ am
  | .printInt e => e.typedVars σ am
  | .printBool b => b.typedVars σ am
  | .printFloat e => e.typedVars σ am
  | .printString _ => True

-- ============================================================
-- § 4c. Bridge: typeCheck → tmpFree
-- ============================================================

/-- If `noTmpDecls decls` holds and `v` is found in `decls`, then `v` is not a tmp. -/
private theorem noTmpDecls_not_tmp {decls : List (Var × VarTy)} {v : Var} {ty : VarTy}
    (hnt : Program.noTmpDecls decls = true) (hlook : decls.lookup v = some ty) :
    v.isTmp = false := by
  -- If v.isTmp were true, lookup would return none, contradicting hlook
  cases hv : v.isTmp with
  | false => rfl
  | true =>
    have := lookup_none_of_isTmp_wt hnt hv
    simp [this] at hlook

private theorem noTmpDecls_not_ftmp {decls : List (Var × VarTy)} {v : Var} {ty : VarTy}
    (hnt : Program.noTmpDecls decls = true) (hlook : decls.lookup v = some ty) :
    v.isFTmp = false := by
  cases hv : v.isFTmp with
  | false => rfl
  | true =>
    have := lookup_none_of_isFTmp_wt hnt hv
    simp [this] at hlook

private theorem noTmpDecls_not_btmp {decls : List (Var × VarTy)} {v : Var} {ty : VarTy}
    (hnt : Program.noTmpDecls decls = true) (hlook : decls.lookup v = some ty) :
    v.isBTmp = false := by
  cases hv : v.isBTmp with
  | false => rfl
  | true =>
    have := lookup_none_of_isBTmp_wt hnt hv
    simp [this] at hlook

/-- All variables in a well-typed arithmetic expression are declared. -/
private theorem checkExpr_declared {lookup : Var → Option VarTy}
    {arrayDecls : List (ArrayName × Nat × VarTy)} {ty : VarTy}
    {e : SExpr} (h : Program.checkExpr lookup arrayDecls ty e = true) :
    ∀ v ∈ e.freeVars, ∃ ty, lookup v = some ty := by
  induction e generalizing ty with
  | lit _ =>
    match ty with
    | .int => intro v hv; simp [SExpr.freeVars] at hv
    | .float => simp [Program.checkExpr] at h
    | .bool => simp [Program.checkExpr] at h
  | var x =>
    match ty with
    | .int =>
      intro v hv; simp [SExpr.freeVars] at hv; subst hv
      simp [Program.checkExpr] at h; exact ⟨.int, h⟩
    | .float =>
      intro v hv; simp [SExpr.freeVars] at hv; subst hv
      simp [Program.checkExpr] at h; exact ⟨.float, h⟩
    | .bool => simp [Program.checkExpr] at h
  | bin _ a b iha ihb =>
    match ty with
    | .int =>
      simp [Program.checkExpr, Bool.and_eq_true] at h
      intro v hv; simp [SExpr.freeVars] at hv
      rcases hv with ha | hb
      · exact iha h.1 v ha
      · exact ihb h.2 v hb
    | .float => simp [Program.checkExpr] at h
    | .bool => simp [Program.checkExpr] at h
  | arrRead _ idx ih =>
    match ty with
    | .int =>
      simp [Program.checkExpr, Bool.and_eq_true] at h
      intro v hv; exact ih h.2 v hv
    | .float => simp [Program.checkExpr] at h
    | .bool => simp [Program.checkExpr] at h
  | flit _ =>
    match ty with
    | .float => intro v hv; simp [SExpr.freeVars] at hv
    | .int => simp [Program.checkExpr] at h
    | .bool => simp [Program.checkExpr] at h
  | fbin _ a b iha ihb =>
    match ty with
    | .float =>
      simp [Program.checkExpr, Bool.and_eq_true] at h
      intro v hv; simp [SExpr.freeVars] at hv
      rcases hv with ha | hb
      · exact iha h.1 v ha
      · exact ihb h.2 v hb
    | .int => simp [Program.checkExpr] at h
    | .bool => simp [Program.checkExpr] at h
  | intToFloat e ih =>
    match ty with
    | .float =>
      simp [Program.checkExpr] at h
      intro v hv; exact ih h v hv
    | .int => simp [Program.checkExpr] at h
    | .bool => simp [Program.checkExpr] at h
  | floatToInt e ih =>
    match ty with
    | .int =>
      simp [Program.checkExpr] at h
      intro v hv; exact ih h v hv
    | .float => simp [Program.checkExpr] at h
    | .bool => simp [Program.checkExpr] at h
  | floatUnary op e ih =>
    match ty with
    | .float =>
      simp [Program.checkExpr] at h
      intro v hv; exact ih h v hv
    | .int => simp [Program.checkExpr] at h
    | .bool => simp [Program.checkExpr] at h
  | farrRead _ idx ih =>
    match ty with
    | .float =>
      simp [Program.checkExpr, Bool.and_eq_true] at h
      intro v hv; exact ih h.2 v hv
    | .int => simp [Program.checkExpr] at h
    | .bool => simp [Program.checkExpr] at h

private theorem checkSExpr_declared {lookup : Var → Option VarTy}
    {arrayDecls : List (ArrayName × Nat × VarTy)}
    {e : SExpr} (h : Program.checkSExpr lookup arrayDecls e = true) :
    ∀ v ∈ e.freeVars, ∃ ty, lookup v = some ty :=
  checkExpr_declared h

private theorem TypedStore.getInt {Γ : TyCtx} {σ : Store} {x : Var}
    (hts : TypedStore Γ σ) (hty : Γ x = .int) : ∃ n, σ x = .int n := by
  have := hts x; rw [hty] at this
  exact Value.int_of_typeOf_int this

private theorem TypedStore.getFloat {Γ : TyCtx} {σ : Store} {x : Var}
    (hts : TypedStore Γ σ) (hty : Γ x = .float) : ∃ f, σ x = .float f := by
  have := hts x; rw [hty] at this
  exact Value.float_of_typeOf_float this

/-- Bridge: `checkExpr ty e = true` + `TypedStore` implies `e.typedVars` and
    that `e.wrapEval` matches the expected type wrapper. -/
theorem checkExpr_typedVars {lookup : Var → Option VarTy}
    {arrayDecls : List (ArrayName × Nat × VarTy)} {Γ : TyCtx} {σ : Store}
    {am : ArrayMem} {ty : VarTy} {e : SExpr}
    (hcompat : ∀ x ty, lookup x = some ty → Γ x = ty)
    (hchk : Program.checkExpr lookup arrayDecls ty e = true)
    (hts : TypedStore Γ σ) :
    e.typedVars σ am ∧
    (ty = .int → e.wrapEval σ am = .int (e.eval σ am)) ∧
    (ty = .float → e.wrapEval σ am = .float (e.eval σ am)) := by
  induction e generalizing ty with
  | lit n =>
    match ty with
    | .int => exact ⟨trivial, fun _ => rfl, fun h => absurd h (by decide)⟩
    | .float => simp [Program.checkExpr] at hchk
    | .bool => simp [Program.checkExpr] at hchk
  | var x =>
    match ty with
    | .int =>
      simp [Program.checkExpr, beq_iff_eq] at hchk
      obtain ⟨n, hn⟩ := TypedStore.getInt hts (hcompat _ .int hchk)
      refine ⟨trivial, fun _ => ?_, fun h => absurd h (by decide)⟩
      simp [SExpr.wrapEval, SExpr.eval, hn]
    | .float =>
      simp [Program.checkExpr, beq_iff_eq] at hchk
      obtain ⟨f, hf⟩ := TypedStore.getFloat hts (hcompat _ .float hchk)
      refine ⟨trivial, fun h => absurd h (by decide), fun _ => ?_⟩
      simp [SExpr.wrapEval, SExpr.eval, hf]
    | .bool => simp [Program.checkExpr] at hchk
  | bin op a b iha ihb =>
    match ty with
    | .int =>
      simp [Program.checkExpr, Bool.and_eq_true] at hchk
      have ⟨htv_a, hwi_a, _⟩ := iha hchk.1
      have ⟨htv_b, hwi_b, _⟩ := ihb hchk.2
      exact ⟨⟨hwi_a rfl, hwi_b rfl, htv_a, htv_b⟩, fun _ => rfl, fun h => absurd h (by decide)⟩
    | .float => simp [Program.checkExpr] at hchk
    | .bool => simp [Program.checkExpr] at hchk
  | arrRead _arr idx ih =>
    match ty with
    | .int =>
      simp [Program.checkExpr, Bool.and_eq_true] at hchk
      have ⟨htv_i, hwi_i, _⟩ := ih hchk.2
      exact ⟨⟨hwi_i rfl, htv_i⟩, fun _ => rfl, fun h => absurd h (by decide)⟩
    | .float => simp [Program.checkExpr] at hchk
    | .bool => simp [Program.checkExpr] at hchk
  | flit f =>
    match ty with
    | .float => exact ⟨trivial, fun h => absurd h (by decide), fun _ => rfl⟩
    | .int => simp [Program.checkExpr] at hchk
    | .bool => simp [Program.checkExpr] at hchk
  | fbin op a b iha ihb =>
    match ty with
    | .float =>
      simp [Program.checkExpr, Bool.and_eq_true] at hchk
      have ⟨htv_a, _, hwf_a⟩ := iha hchk.1
      have ⟨htv_b, _, hwf_b⟩ := ihb hchk.2
      exact ⟨⟨hwf_a rfl, hwf_b rfl, htv_a, htv_b⟩, fun h => absurd h (by decide), fun _ => rfl⟩
    | .int => simp [Program.checkExpr] at hchk
    | .bool => simp [Program.checkExpr] at hchk
  | intToFloat e ih =>
    match ty with
    | .float =>
      simp [Program.checkExpr] at hchk
      have ⟨htv_e, hwi_e, _⟩ := ih hchk
      exact ⟨⟨hwi_e rfl, htv_e⟩, fun h => absurd h (by decide), fun _ => rfl⟩
    | .int => simp [Program.checkExpr] at hchk
    | .bool => simp [Program.checkExpr] at hchk
  | floatToInt e ih =>
    match ty with
    | .int =>
      simp [Program.checkExpr] at hchk
      have ⟨htv_e, _, hwf_e⟩ := ih hchk
      exact ⟨⟨hwf_e rfl, htv_e⟩, fun _ => rfl, fun h => absurd h (by decide)⟩
    | .float => simp [Program.checkExpr] at hchk
    | .bool => simp [Program.checkExpr] at hchk
  | floatUnary op e ih =>
    match ty with
    | .float =>
      simp [Program.checkExpr] at hchk
      have ⟨htv_e, _, hwf_e⟩ := ih hchk
      exact ⟨⟨hwf_e rfl, htv_e⟩, fun h => absurd h (by decide), fun _ => rfl⟩
    | .int => simp [Program.checkExpr] at hchk
    | .bool => simp [Program.checkExpr] at hchk
  | farrRead _arr idx ih =>
    match ty with
    | .float =>
      simp [Program.checkExpr, Bool.and_eq_true] at hchk
      have ⟨htv_i, hwi_i, _⟩ := ih hchk.2
      exact ⟨⟨hwi_i rfl, htv_i⟩, fun h => absurd h (by decide), fun _ => rfl⟩
    | .int => simp [Program.checkExpr] at hchk
    | .bool => simp [Program.checkExpr] at hchk

/-- All variables in a well-typed boolean expression are declared. -/
private theorem checkSBool_declared {lookup : Var → Option VarTy}
    {arrayDecls : List (ArrayName × Nat × VarTy)}
    {b : SBool} (h : Program.checkSBool lookup arrayDecls b = true) :
    ∀ v ∈ b.freeVars, ∃ ty, lookup v = some ty := by
  induction b with
  | lit _ => intro v hv; simp [SBool.freeVars] at hv
  | bvar x =>
    intro v hv; simp [SBool.freeVars] at hv; subst hv
    simp [Program.checkSBool] at h; exact ⟨.bool, h⟩
  | cmp _ a b =>
    simp [Program.checkSBool, Bool.and_eq_true] at h
    intro v hv; simp [SBool.freeVars] at hv
    rcases hv with ha | hb
    · exact checkSExpr_declared h.1 v ha
    · exact checkSExpr_declared h.2 v hb
  | not e ih =>
    simp [Program.checkSBool] at h
    intro v hv; simp [SBool.freeVars] at hv; exact ih h v hv
  | and a b iha ihb =>
    simp [Program.checkSBool, Bool.and_eq_true] at h
    intro v hv; simp [SBool.freeVars] at hv
    rcases hv with ha | hb
    · exact iha h.1 v ha
    · exact ihb h.2 v hb
  | or a b iha ihb =>
    simp [Program.checkSBool, Bool.and_eq_true] at h
    intro v hv; simp [SBool.freeVars] at hv
    rcases hv with ha | hb
    · exact iha h.1 v ha
    · exact ihb h.2 v hb
  | barrRead arr idx =>
    simp [Program.checkSBool, Bool.and_eq_true] at h
    intro v hv; simp [SBool.freeVars] at hv; exact checkSExpr_declared h.2 v hv
  | fcmp _ a b =>
    simp [Program.checkSBool, Bool.and_eq_true] at h
    intro v hv; simp [SBool.freeVars] at hv
    rcases hv with ha | hb
    · exact checkExpr_declared h.1 v ha
    · exact checkExpr_declared h.2 v hb

/-- All variables in a well-typed statement are declared. -/
private theorem checkStmt_declared {lookup : Var → Option VarTy}
    {arrayDecls : List (ArrayName × Nat × VarTy)}
    {s : Stmt} (h : Program.checkStmt lookup arrayDecls s = true) :
    ∀ v ∈ s.allVars, ∃ ty, lookup v = some ty := by
  induction s with
  | skip => intro v hv; simp [Stmt.allVars] at hv
  | assign x e =>
    simp [Program.checkStmt, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hx, he⟩ := h
    intro v hv; simp [Stmt.allVars] at hv
    rcases hv with rfl | hv
    · exact ⟨.int, hx⟩
    · exact checkSExpr_declared he v hv
  | bassign x b =>
    simp [Program.checkStmt, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hx, hb⟩ := h
    intro v hv; simp [Stmt.allVars] at hv
    rcases hv with rfl | hv
    · exact ⟨.bool, hx⟩
    · exact checkSBool_declared hb v hv
  | arrWrite arr idx val =>
    simp [Program.checkStmt, Bool.and_eq_true] at h
    obtain ⟨⟨_, hi⟩, hv⟩ := h
    intro v hv'; simp [Stmt.allVars] at hv'
    rcases hv' with hi' | hv'
    · exact checkSExpr_declared hi v hi'
    · exact checkSExpr_declared hv v hv'
  | barrWrite arr idx bval =>
    simp [Program.checkStmt, Bool.and_eq_true] at h
    obtain ⟨⟨_, hi⟩, hb⟩ := h
    intro v hv; simp [Stmt.allVars] at hv
    rcases hv with hi' | hb'
    · exact checkSExpr_declared hi v hi'
    · exact checkSBool_declared hb v hb'
  | seq s1 s2 ih1 ih2 =>
    simp [Program.checkStmt, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    intro v hv; simp [Stmt.allVars] at hv
    rcases hv with hv1 | hv2
    · exact ih1 h1 v hv1
    · exact ih2 h2 v hv2
  | ite b s1 s2 ih1 ih2 =>
    simp [Program.checkStmt, Bool.and_eq_true] at h
    obtain ⟨⟨hb, h1⟩, h2⟩ := h
    intro v hv; simp [Stmt.allVars] at hv
    rcases hv with hb' | hv1 | hv2
    · exact checkSBool_declared hb v hb'
    · exact ih1 h1 v hv1
    · exact ih2 h2 v hv2
  | loop b body ih =>
    simp [Program.checkStmt, Bool.and_eq_true] at h
    obtain ⟨hb, hbody⟩ := h
    intro v hv; simp [Stmt.allVars] at hv
    rcases hv with hb' | hv'
    · exact checkSBool_declared hb v hb'
    · exact ih hbody v hv'
  | fassign x e =>
    simp [Program.checkStmt, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hx, he⟩ := h
    intro v hv; simp [Stmt.allVars] at hv
    rcases hv with rfl | hv
    · exact ⟨.float, hx⟩
    · exact checkExpr_declared he v hv
  | farrWrite arr idx val =>
    simp [Program.checkStmt, Bool.and_eq_true] at h
    obtain ⟨⟨_, hi⟩, hv⟩ := h
    intro v hv'; simp [Stmt.allVars] at hv'
    rcases hv' with hi' | hv'
    · exact checkSExpr_declared hi v hi'
    · exact checkExpr_declared hv v hv'
  | label _ => intro v hv; simp [Stmt.allVars] at hv
  | goto _ => intro v hv; simp [Stmt.allVars] at hv
  | ifgoto b _ =>
    simp [Program.checkStmt] at h
    intro v hv; simp [Stmt.allVars] at hv
    exact checkSBool_declared h v hv
  | print fmt args =>
    simp [Program.checkStmt, List.all_eq_true, Bool.or_eq_true] at h
    intro v hv; simp [Stmt.allVars] at hv
    obtain ⟨e, he, hv⟩ := hv
    rcases h e he with hc | hc
    · exact checkSExpr_declared hc v hv
    · exact checkExpr_declared hc v hv
  | printInt e =>
    simp [Program.checkStmt] at h
    intro v hv; simp [Stmt.allVars] at hv
    exact checkSExpr_declared h v hv
  | printBool b =>
    simp [Program.checkStmt] at h
    intro v hv; simp [Stmt.allVars] at hv
    exact checkSBool_declared h v hv
  | printFloat e =>
    simp [Program.checkStmt] at h
    intro v hv; simp [Stmt.allVars] at hv
    exact checkExpr_declared h v hv
  | printString lit =>
    intro v hv; simp [Stmt.allVars] at hv

/-- **Bridge lemma**: A type-checked program's body is tmp-free — no variable
    in the source program uses the compiler-reserved `__t` prefix. -/
theorem Program.typeCheck_tmpFree (prog : Program) (h : prog.typeCheck = true) :
    prog.body.tmpFree := by
  unfold Program.typeCheck at h; simp only [Bool.and_eq_true] at h
  have hnt := h.1.2
  have hchk := h.2
  intro v hv
  obtain ⟨ty, hlook⟩ := checkStmt_declared hchk v hv
  exact noTmpDecls_not_tmp hnt hlook

/-- A type-checked program's body has no ftmp-prefixed variables. -/
theorem Program.typeCheck_ftmpFree (prog : Program) (h : prog.typeCheck = true) :
    ∀ v ∈ prog.body.allVars, v.isFTmp = false := by
  unfold Program.typeCheck at h; simp only [Bool.and_eq_true] at h
  have hnt := h.1.2
  have hchk := h.2
  intro v hv
  obtain ⟨ty, hlook⟩ := checkStmt_declared hchk v hv
  exact noTmpDecls_not_ftmp hnt hlook

/-- A type-checked program's body has no btmp-prefixed variables. -/
theorem Program.typeCheck_btmpFree (prog : Program) (h : prog.typeCheck = true) :
    prog.body.btmpFree := by
  unfold Program.typeCheck at h; simp only [Bool.and_eq_true] at h
  have hnt := h.1.2
  have hchk := h.2
  intro v hv
  obtain ⟨ty, hlook⟩ := checkStmt_declared hchk v hv
  exact noTmpDecls_not_btmp hnt hlook

/-- A statement that passes checkNoGoto has no goto/ifgoto. -/
private theorem checkNoGoto_sound {s : Stmt}
    (h : s.checkNoGoto = true) : s.noGoto := by
  induction s with
  | goto _ => simp [Stmt.checkNoGoto] at h
  | ifgoto _ _ => simp [Stmt.checkNoGoto] at h
  | seq s1 s2 ih1 ih2 =>
    simp [Stmt.checkNoGoto, Bool.and_eq_true] at h; exact ⟨ih1 h.1, ih2 h.2⟩
  | ite b s1 s2 ih1 ih2 =>
    simp [Stmt.checkNoGoto, Bool.and_eq_true] at h; exact ⟨ih1 h.1, ih2 h.2⟩
  | loop b body ih =>
    simp [Stmt.checkNoGoto] at h; exact ih h
  | _ => exact trivial

/-- A strictly type-checked program's body has no goto/ifgoto. -/
theorem Program.typeCheck_noGoto (prog : Program) (h : prog.wellFormed = true) :
    prog.body.noGoto := by
  unfold Program.wellFormed at h; simp only [Bool.and_eq_true] at h
  exact checkNoGoto_sound h.1.1.2

-- ============================================================
-- § 4d. Source-level type preservation
-- ============================================================

/-- Helper: checkStmt-declared variables have their declared type in tyCtx. -/
private theorem lookup_tyCtx {lookup : Var → Option VarTy} {Γ : TyCtx}
    (hcompat : ∀ x ty, lookup x = some ty → Γ x = ty) {x : Var} {ty : VarTy}
    (h : lookup x = some ty) : Γ x = ty := hcompat x ty h

/-- Source-level type preservation: interpreting a well-typed statement
    preserves TypedStore. -/
theorem Stmt.interp_preserves_typedStore
    {s : Stmt} {fuel : Nat} {σ σ' : Store} {am am' : ArrayMem} {Γ : TyCtx}
    {lookup : Var → Option VarTy} {arrayDecls : List (ArrayName × Nat × VarTy)}
    (hcompat : ∀ x ty, lookup x = some ty → Γ x = ty)
    (hchk : Program.checkStmt lookup arrayDecls s = true)
    (hts : TypedStore Γ σ)
    (hinterp : s.interp fuel σ am arrayDecls = some (σ', am')) :
    TypedStore Γ σ' := by
  induction s generalizing fuel σ σ' am am' with
  | skip =>
    simp only [Stmt.interp] at hinterp
    obtain ⟨rfl, _⟩ := Option.some.inj hinterp; exact hts
  | assign x e =>
    simp only [Stmt.interp] at hinterp
    split at hinterp <;> simp at hinterp
    obtain ⟨rfl, _⟩ := hinterp
    simp [Program.checkStmt, Bool.and_eq_true, beq_iff_eq] at hchk
    exact TypedStore.update_typed hts (by simp [Value.typeOf, hcompat x .int hchk.1])
  | bassign x b =>
    simp only [Stmt.interp] at hinterp
    split at hinterp <;> simp at hinterp
    obtain ⟨rfl, _⟩ := hinterp
    simp [Program.checkStmt, Bool.and_eq_true, beq_iff_eq] at hchk
    exact TypedStore.update_typed hts (by simp [Value.typeOf, hcompat x .bool hchk.1])
  | arrWrite _ _ _ =>
    simp only [Stmt.interp] at hinterp
    split at hinterp <;> simp at hinterp
    obtain ⟨rfl, _⟩ := hinterp; exact hts
  | barrWrite _ _ _ =>
    simp only [Stmt.interp] at hinterp
    split at hinterp <;> simp at hinterp
    obtain ⟨rfl, _⟩ := hinterp; exact hts
  | seq s1 s2 ih1 ih2 =>
    simp [Program.checkStmt, Bool.and_eq_true] at hchk
    obtain ⟨hc1, hc2⟩ := hchk
    simp only [Stmt.interp, bind, Option.bind] at hinterp
    cases h1 : s1.interp fuel σ am arrayDecls with
    | none => simp [h1] at hinterp
    | some p =>
      obtain ⟨σ₁, am₁⟩ := p
      simp [h1] at hinterp
      exact ih2 (hchk := hc2) (hts := ih1 (hchk := hc1) (hts := hts) h1) hinterp
  | ite b s1 s2 ih1 ih2 =>
    simp [Program.checkStmt, Bool.and_eq_true] at hchk
    obtain ⟨⟨_, hc1⟩, hc2⟩ := hchk
    simp only [Stmt.interp] at hinterp
    split at hinterp
    · cases heval : b.eval σ am
      · simp [heval] at hinterp
        exact ih2 (hchk := hc2) (hts := hts) hinterp
      · simp [heval] at hinterp
        exact ih1 (hchk := hc1) (hts := hts) hinterp
    · simp at hinterp
  | loop b body ihb =>
    simp [Program.checkStmt, Bool.and_eq_true] at hchk
    obtain ⟨_, hcbody⟩ := hchk
    induction fuel generalizing σ σ' am am' with
    | zero => simp only [Stmt.interp] at hinterp; simp at hinterp
    | succ fuel' ih_fuel =>
      simp only [Stmt.interp] at hinterp
      split at hinterp
      · cases heval : b.eval σ am <;> simp [heval] at hinterp
        · obtain ⟨rfl, rfl⟩ := hinterp; exact hts
        · cases h_body : body.interp fuel' σ am arrayDecls with
          | none => simp [h_body] at hinterp
          | some p =>
            obtain ⟨σ₁, am₁⟩ := p
            simp [h_body] at hinterp
            exact ih_fuel (ihb (hchk := hcbody) (hts := hts) h_body) hinterp
      · simp at hinterp
  | fassign x e =>
    simp only [Stmt.interp] at hinterp
    split at hinterp <;> simp at hinterp
    obtain ⟨rfl, _⟩ := hinterp
    simp [Program.checkStmt, Bool.and_eq_true, beq_iff_eq] at hchk
    exact TypedStore.update_typed hts (by simp [Value.typeOf, hcompat x .float hchk.1])
  | farrWrite _ _ _ =>
    simp only [Stmt.interp] at hinterp
    split at hinterp <;> simp at hinterp
    obtain ⟨rfl, _⟩ := hinterp; exact hts
  | label _ =>
    simp only [Stmt.interp] at hinterp
    obtain ⟨rfl, _⟩ := Option.some.inj hinterp; exact hts
  | goto _ =>
    simp only [Stmt.interp] at hinterp
    obtain ⟨rfl, _⟩ := Option.some.inj hinterp; exact hts
  | ifgoto _ _ =>
    simp only [Stmt.interp] at hinterp
    split at hinterp
    · obtain ⟨rfl, _⟩ := Option.some.inj hinterp; exact hts
    · simp at hinterp
  | print fmt args =>
    simp only [Stmt.interp] at hinterp
    split at hinterp
    · obtain ⟨rfl, _⟩ := Option.some.inj hinterp; exact hts
    · simp at hinterp
  | printInt e =>
    simp only [Stmt.interp] at hinterp
    split at hinterp
    · obtain ⟨rfl, _⟩ := Option.some.inj hinterp; exact hts
    · simp at hinterp
  | printBool b =>
    simp only [Stmt.interp] at hinterp
    split at hinterp
    · obtain ⟨rfl, _⟩ := Option.some.inj hinterp; exact hts
    · simp at hinterp
  | printFloat e =>
    simp only [Stmt.interp] at hinterp
    split at hinterp
    · obtain ⟨rfl, _⟩ := Option.some.inj hinterp; exact hts
    · simp at hinterp
  | printString lit =>
    simp only [Stmt.interp] at hinterp
    obtain ⟨rfl, _⟩ := Option.some.inj hinterp; exact hts

-- ============================================================
-- § 4e. Bridge: typeCheck + TypedStore → typedVars
-- ============================================================

/-- Bridge: `checkSBool` + `TypedStore` implies `SBool.typedVars`. -/
theorem checkSBool_typedVars {lookup : Var → Option VarTy}
    {arrayDecls : List (ArrayName × Nat × VarTy)} {Γ : TyCtx} {σ : Store}
    {am : ArrayMem} {b : SBool}
    (hcompat : ∀ x ty, lookup x = some ty → Γ x = ty)
    (hchk : Program.checkSBool lookup arrayDecls b = true)
    (hts : TypedStore Γ σ) :
    b.typedVars σ am := by
  induction b with
  | lit _ => trivial
  | bvar _ => trivial
  | cmp _ a b =>
    simp [Program.checkSBool, Bool.and_eq_true] at hchk
    simp only [SBool.typedVars]
    have ⟨htv_a, hwi_a, _⟩ := checkExpr_typedVars (am := am) hcompat hchk.1 hts
    have ⟨htv_b, hwi_b, _⟩ := checkExpr_typedVars (am := am) hcompat hchk.2 hts
    exact ⟨htv_a, htv_b, hwi_a rfl, hwi_b rfl⟩
  | not e ih => simp [Program.checkSBool] at hchk; exact ih hchk
  | and a b iha ihb =>
    simp [Program.checkSBool, Bool.and_eq_true] at hchk
    exact ⟨iha hchk.1, ihb hchk.2⟩
  | or a b iha ihb =>
    simp [Program.checkSBool, Bool.and_eq_true] at hchk
    exact ⟨iha hchk.1, ihb hchk.2⟩
  | barrRead arr idx =>
    simp [Program.checkSBool, Bool.and_eq_true] at hchk
    simp only [SBool.typedVars]
    have ⟨htv_i, hwi_i, _⟩ := checkExpr_typedVars (am := am) hcompat hchk.2 hts
    exact ⟨htv_i, hwi_i rfl⟩
  | fcmp _ a b =>
    simp [Program.checkSBool, Bool.and_eq_true] at hchk
    simp only [SBool.typedVars]
    have ⟨htv_a, _, hwf_a⟩ := checkExpr_typedVars (am := am) hcompat hchk.1 hts
    have ⟨htv_b, _, hwf_b⟩ := checkExpr_typedVars (am := am) hcompat hchk.2 hts
    exact ⟨htv_a, htv_b, hwf_a rfl, hwf_b rfl⟩

/-- Bridge: `checkStmt` + `TypedStore` implies `Stmt.typedVars`. -/
theorem checkStmt_typedVars
    (lookup : Var → Option VarTy) (arrayDecls : List (ArrayName × Nat × VarTy))
    (Γ : TyCtx) (σ : Store) (am : ArrayMem) (s : Stmt) (fuel : Nat)
    (hcompat : ∀ x ty, lookup x = some ty → Γ x = ty)
    (hchk : Program.checkStmt lookup arrayDecls s = true)
    (hts : TypedStore Γ σ) :
    s.typedVars fuel σ am arrayDecls := by
  induction s generalizing fuel σ am with
  | skip => simp only [Stmt.typedVars]
  | assign x e =>
    simp [Program.checkStmt, Bool.and_eq_true, beq_iff_eq] at hchk
    obtain ⟨_, he⟩ := hchk
    simp only [Stmt.typedVars]
    have ⟨htv, hwi, _⟩ := checkExpr_typedVars (am := am) hcompat he hts
    exact ⟨htv, hwi rfl⟩
  | bassign x b =>
    simp [Program.checkStmt, Bool.and_eq_true] at hchk
    obtain ⟨_, hb⟩ := hchk
    simp only [Stmt.typedVars]
    exact checkSBool_typedVars hcompat hb hts
  | arrWrite arr idx val =>
    simp [Program.checkStmt, Bool.and_eq_true] at hchk
    obtain ⟨⟨_, hi⟩, hv⟩ := hchk
    simp only [Stmt.typedVars]
    have ⟨htv_i, hwi_i, _⟩ := checkExpr_typedVars (am := am) hcompat hi hts
    have ⟨htv_v, hwi_v, _⟩ := checkExpr_typedVars (am := am) hcompat hv hts
    exact ⟨⟨htv_i, hwi_i rfl⟩, ⟨htv_v, hwi_v rfl⟩⟩
  | barrWrite arr idx bval =>
    simp [Program.checkStmt, Bool.and_eq_true] at hchk
    obtain ⟨⟨_, hi⟩, hb⟩ := hchk
    simp only [Stmt.typedVars]
    have ⟨htv_i, hwi_i, _⟩ := checkExpr_typedVars (am := am) hcompat hi hts
    exact ⟨⟨htv_i, hwi_i rfl⟩, checkSBool_typedVars hcompat hb hts⟩
  | seq s1 s2 ih1 ih2 =>
    simp [Program.checkStmt, Bool.and_eq_true] at hchk
    obtain ⟨hc1, hc2⟩ := hchk
    simp only [Stmt.typedVars]
    refine ⟨ih1 σ am fuel hc1 hts, ?_⟩
    cases h1 : s1.interp fuel σ am arrayDecls with
    | none => trivial
    | some p =>
      obtain ⟨σ₁, am₁⟩ := p
      exact ih2 σ₁ am₁ fuel hc2 (Stmt.interp_preserves_typedStore hcompat hc1 hts h1)
  | ite b s1 s2 ih1 ih2 =>
    simp [Program.checkStmt, Bool.and_eq_true] at hchk
    obtain ⟨⟨hb, hc1⟩, hc2⟩ := hchk
    simp only [Stmt.typedVars]
    refine ⟨checkSBool_typedVars hcompat hb hts, ?_⟩
    cases b.eval σ am <;> simp
    · exact ih2 σ am fuel hc2 hts
    · exact ih1 σ am fuel hc1 hts
  | loop b body ih =>
    induction fuel generalizing σ am with
    | zero => simp [Stmt.typedVars.eq_8]
    | succ fuel' ih_fuel =>
      rw [Stmt.typedVars.eq_9]
      simp [Program.checkStmt, Bool.and_eq_true] at hchk
      obtain ⟨hb, hcbody⟩ := hchk
      refine ⟨checkSBool_typedVars hcompat hb hts, ?_⟩
      cases heval : b.eval σ am <;> simp [heval]
      refine ⟨ih σ am fuel' hcbody hts, ?_⟩
      cases h_body : body.interp fuel' σ am arrayDecls with
      | none => trivial
      | some p =>
        obtain ⟨σ₁, am₁⟩ := p
        exact ih_fuel σ₁ am₁ (Stmt.interp_preserves_typedStore hcompat hcbody hts h_body)
  | fassign x e =>
    simp [Program.checkStmt, Bool.and_eq_true, beq_iff_eq] at hchk
    obtain ⟨_, he⟩ := hchk
    simp only [Stmt.typedVars]
    have ⟨htv, _, hwf⟩ := checkExpr_typedVars (am := am) hcompat he hts
    exact ⟨htv, hwf rfl⟩
  | farrWrite arr idx val =>
    simp [Program.checkStmt, Bool.and_eq_true] at hchk
    obtain ⟨⟨_, hi⟩, hv⟩ := hchk
    simp only [Stmt.typedVars]
    have ⟨htv_i, hwi_i, _⟩ := checkExpr_typedVars (am := am) hcompat hi hts
    have ⟨htv_v, _, hwf_v⟩ := checkExpr_typedVars (am := am) hcompat hv hts
    exact ⟨⟨htv_i, hwi_i rfl⟩, ⟨htv_v, hwf_v rfl⟩⟩
  | label _ => simp only [Stmt.typedVars]
  | goto _ => simp only [Stmt.typedVars]
  | ifgoto b _ =>
    simp [Program.checkStmt] at hchk
    simp only [Stmt.typedVars]
    exact checkSBool_typedVars hcompat hchk hts
  | print fmt args =>
    simp [Program.checkStmt, List.all_eq_true, Bool.or_eq_true] at hchk
    simp only [Stmt.typedVars]
    intro e he
    rcases hchk e he with hc | hc
    · exact (checkExpr_typedVars (am := am) hcompat hc hts).1
    · exact (checkExpr_typedVars (am := am) hcompat hc hts).1
  | printInt e =>
    simp [Program.checkStmt] at hchk
    simp only [Stmt.typedVars]
    exact (checkExpr_typedVars (am := am) hcompat hchk hts).1
  | printBool b =>
    simp [Program.checkStmt] at hchk
    simp only [Stmt.typedVars]
    exact checkSBool_typedVars hcompat hchk hts
  | printFloat e =>
    simp [Program.checkStmt] at hchk
    simp only [Stmt.typedVars]
    exact (checkExpr_typedVars (am := am) hcompat hchk hts).1
  | printString lit => simp only [Stmt.typedVars]

/-- **Bridge lemma**: A type-checked program with a well-typed store satisfies typedVars. -/
theorem Program.typeCheck_typedVars (prog : Program) (h : prog.typeCheck = true)
    (σ : Store) (am : ArrayMem) (hts : TypedStore prog.tyCtx σ) (fuel : Nat) :
    prog.body.typedVars fuel σ am prog.arrayDecls := by
  unfold Program.typeCheck at h; simp only [Bool.and_eq_true] at h
  have hchk := h.2
  exact checkStmt_typedVars prog.lookupTy prog.arrayDecls prog.tyCtx σ am prog.body fuel
    (fun x ty hlook => by
      show (prog.lookupTy x).getD (Program.defaultVarTy x) = ty
      rw [hlook]; rfl) hchk hts

-- ============================================================
-- § 5. Fragment execution
-- ============================================================

abbrev FragExec (p : Prog) (pc : Nat) (σ : Store) (pc' : Nat) (σ' : Store) (am am' : ArrayMem) : Prop :=
  p ⊩ Cfg.run pc σ am ⟶* Cfg.run pc' σ' am'

theorem FragExec.rfl' (p : Prog) (pc : Nat) (σ : Store) (am : ArrayMem) :
    FragExec p pc σ pc σ am am := Steps.refl

theorem FragExec.trans' {p : Prog} {pc₁ pc₂ pc₃ : Nat} {σ₁ σ₂ σ₃ : Store} {am₁ am₂ am₃ : ArrayMem}
    (h₁ : FragExec p pc₁ σ₁ pc₂ σ₂ am₁ am₂) (h₂ : FragExec p pc₂ σ₂ pc₃ σ₃ am₂ am₃) :
    FragExec p pc₁ σ₁ pc₃ σ₃ am₁ am₃ := Steps.trans h₁ h₂

theorem FragExec.toHalt {p : Prog} {pc pc' : Nat} {σ σ' : Store} {am am' : ArrayMem}
    (hfrag : FragExec p pc σ pc' σ' am am')
    (hhalt : p[pc']? = some .halt) :
    p ⊩ Cfg.run pc σ am ⟶* Cfg.halt σ' am' :=
  Steps.trans hfrag (Steps.single (.halt hhalt))
