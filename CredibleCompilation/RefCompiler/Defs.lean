-- Copyright (c) 2026 Martin Rinard
import CredibleCompilation.CompilerCorrectness
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.List.Basic

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

/-!
# Compiler Correctness: Definitions and Helpers

Temporary variable helpers, code embedding, single-step execution
helpers, and store update lemmas. Compiler definitions (compileExpr,
compileBool, compileStmt) are in WhileLang.lean.
-/

-- ============================================================
-- § 1. Temporary variable helpers
-- ============================================================

-- -----------------------------------------------
-- Proving tmpName injective
-- -----------------------------------------------

/-- Clean base-10 digit representation. -/
private noncomputable def myDigits (n : Nat) : List Char :=
  if n < 10 then [(n % 10).digitChar]
  else myDigits (n / 10) ++ [(n % 10).digitChar]
termination_by n
decreasing_by omega

private theorem digitChar_injective {m n : Nat} (hm : m < 10) (hn : n < 10)
    (h : m.digitChar = n.digitChar) : m = n := by
  interval_cases m <;> interval_cases n <;> simp_all [Nat.digitChar]

private theorem digitChar_toNat {n : Nat} (hn : n < 10) :
    n.digitChar.toNat - '0'.toNat = n := by
  interval_cases n <;> simp [Nat.digitChar]

private def parseNat (cs : List Char) : Nat :=
  cs.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0

private theorem parseNat_myDigits (n : Nat) : parseNat (myDigits n) = n := by
  rw [myDigits]
  split
  · rename_i hn
    simp only [parseNat, List.foldl]
    rw [digitChar_toNat (by omega : n % 10 < 10)]
    omega
  · rename_i hn
    simp only [parseNat, List.foldl_append, List.foldl]
    show List.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0
        (myDigits (n / 10)) * 10 + ((n % 10).digitChar.toNat - '0'.toNat) = n
    have ih := parseNat_myDigits (n / 10)
    simp only [parseNat] at ih
    rw [ih, digitChar_toNat (by omega : n % 10 < 10)]
    omega
termination_by n
decreasing_by omega

private theorem myDigits_injective : Function.Injective myDigits := by
  intro m n h
  have hm := parseNat_myDigits m
  have hn := parseNat_myDigits n
  rw [h] at hm; omega

private theorem tdc_eq_aux (fuel n : Nat) (ds : List Char) (hfuel : n ≤ fuel) :
    Nat.toDigitsCore 10 (fuel + 1) n ds = myDigits n ++ ds := by
  induction fuel generalizing n ds with
  | zero =>
    have : n = 0 := by omega
    subst this
    simp [Nat.toDigitsCore, myDigits]
  | succ fuel ih =>
    show (let d := (n % 10).digitChar
          let n' := n / 10
          if n' = 0 then d :: ds
          else Nat.toDigitsCore 10 (fuel + 1) n' (d :: ds)) = myDigits n ++ ds
    by_cases hn : n < 10
    · simp [show n / 10 = 0 by omega, myDigits, hn]
    · simp only [show ¬(n / 10 = 0) by omega, ite_false]
      rw [ih (n / 10) _ (by omega)]
      conv_rhs => rw [myDigits, if_neg hn]
      simp [List.append_assoc]

private theorem myDigits_eq_toDigits (n : Nat) : myDigits n = Nat.toDigits 10 n := by
  simp only [Nat.toDigits]
  rw [tdc_eq_aux n n List.nil (by omega)]
  simp

private theorem Nat_toString_injective : Function.Injective (toString : Nat → String) := by
  intro m n h
  have h_toList : (toString m : String).toList = (toString n : String).toList :=
    String.ext_iff.mp h
  show m = n
  simp only [show (toString m : String) = Nat.repr m from rfl,
             show (toString n : String) = Nat.repr n from rfl,
             Nat.repr, String.toList_ofList] at h_toList
  rw [← myDigits_eq_toDigits, ← myDigits_eq_toDigits] at h_toList
  exact myDigits_injective h_toList

private theorem tmpName_injective : Function.Injective tmpName := by
  intro k j h
  have h2 := String.ext_iff.mp h
  simp only [tmpName, String.toList_append] at h2
  have h3 := List.append_cancel_left h2
  exact Nat_toString_injective (String.ext_iff.mpr h3)

-- -----------------------------------------------

theorem tmpName_ne {k j : Nat} (h : k ≠ j) : tmpName k ≠ tmpName j :=
  fun heq => h (tmpName_injective heq)

theorem tmpName_isTmp (k : Nat) : (tmpName k).isTmp = true :=
  tmpName_isTmp_wt k

private theorem ftmpName_injective : Function.Injective ftmpName := by
  intro k j h
  have h2 := String.ext_iff.mp h
  simp only [ftmpName, String.toList_append] at h2
  have h3 := List.append_cancel_left h2
  exact Nat_toString_injective (String.ext_iff.mpr h3)

theorem ftmpName_ne {k j : Nat} (h : k ≠ j) : ftmpName k ≠ ftmpName j :=
  fun heq => h (ftmpName_injective heq)

theorem ftmpName_isFTmp (k : Nat) : (ftmpName k).isFTmp = true :=
  ftmpName_isFTmp_wt k

-- ftmpName_not_isTmp and tmpName_not_isFTmp are imported from WhileLang

/-- tmpName and ftmpName never collide (different prefixes). -/
theorem tmpName_ne_ftmpName {k j : Nat} : tmpName k ≠ ftmpName j := by
  intro h
  have : (tmpName k).isTmp = true := tmpName_isTmp k
  have : (ftmpName j).isTmp = false := ftmpName_not_isTmp j
  rw [h] at *; simp_all

-- ============================================================
-- § 1b. Integer free-variable helpers
-- ============================================================

/-- Free variables that appear in `SExpr` positions within a `SBool`. -/
def SBool.exprFreeVars : SBool → List Var
  | .lit _      => []
  | .bvar _     => []
  | .cmp _ a b  => a.freeVars ++ b.freeVars
  | .not e      => e.exprFreeVars
  | .and a b    => a.exprFreeVars ++ b.exprFreeVars
  | .or a b     => a.exprFreeVars ++ b.exprFreeVars
  | .barrRead _ idx => idx.freeVars
  | .fcmp _ a b => a.freeVars ++ b.freeVars

/-- Integer-safety: all variables used in `SExpr` positions have `.int` values,
    threaded through interpretation just like `Stmt.safe`. -/
def Stmt.intSafe (fuel : Nat) (σ : Store) (am : ArrayMem) (decls : List (ArrayName × Nat × VarTy)) : Stmt → Prop
  | .skip        => True
  | .assign _ e  => ∀ v ∈ e.freeVars, ∃ n, σ v = .int n
  | .bassign _ b => ∀ v ∈ b.exprFreeVars, ∃ n, σ v = .int n
  | .arrWrite _ idx val => (∀ v ∈ idx.freeVars, ∃ n, σ v = .int n) ∧
                           (∀ v ∈ val.freeVars, ∃ n, σ v = .int n)
  | .barrWrite _ idx bval => (∀ v ∈ idx.freeVars, ∃ n, σ v = .int n) ∧
                              (∀ v ∈ bval.exprFreeVars, ∃ n, σ v = .int n)
  | .seq s₁ s₂  =>
    s₁.intSafe fuel σ am decls ∧
    match s₁.interp fuel σ am decls with
    | some (σ', am') => s₂.intSafe fuel σ' am' decls
    | none    => True
  | .ite b s₁ s₂ =>
    (∀ v ∈ b.exprFreeVars, ∃ n, σ v = .int n) ∧
    (if b.eval σ am then s₁.intSafe fuel σ am decls else s₂.intSafe fuel σ am decls)
  | .loop b body =>
    (∀ v ∈ b.exprFreeVars, ∃ n, σ v = .int n) ∧
    match fuel with
    | 0 => True
    | fuel' + 1 =>
      if b.eval σ am then
        body.intSafe fuel' σ am decls ∧
        match body.interp fuel' σ am decls with
        | some (σ', am') => (Stmt.loop b body).intSafe fuel' σ' am' decls
        | none    => True
      else True
  | .fassign _ e => ∀ v ∈ e.freeVars, ∃ n, σ v = .int n
  | .farrWrite _ idx val => (∀ v ∈ idx.freeVars, ∃ n, σ v = .int n) ∧
                            (∀ v ∈ val.freeVars, ∃ n, σ v = .int n)
  | .label _ => True
  | .goto _ => True
  | .ifgoto b _ => ∀ v ∈ b.exprFreeVars, ∃ n, σ v = .int n
  | .print _ args => ∀ e ∈ args, ∀ v ∈ e.freeVars, ∃ n, σ v = .int n
  | .printInt e => ∀ v ∈ e.freeVars, ∃ n, σ v = .int n
  | .printBool b => ∀ v ∈ b.exprFreeVars, ∃ n, σ v = .int n
  | .printFloat e => ∀ v ∈ e.freeVars, ∃ n, σ v = .int n
  | .printString _ => True

-- § 2. Compiler definitions are in WhileLang.lean (compileExpr, compileBool, compileStmt).
-- This module provides proofs and infrastructure about them.

/-- Compile a bare statement to a TAC program (convenience wrapper). -/
def compileStmtToProg (s : Stmt) : Prog :=
  let (code, _) := compileStmt s 0 0
  .ofCode (code ++ [TAC.halt]).toArray

-- ============================================================
-- § 3. Code embedding predicate
-- ============================================================

def RC.CodeAt (code : List TAC) (p : Prog) (offset : Nat) : Prop :=
  ∀ i, i < code.length → p[offset + i]? = code[i]?

@[simp] theorem RC.CodeAt.nil : RC.CodeAt [] p offset :=
  fun _ h => absurd h (Nat.not_lt_zero _)

theorem RC.CodeAt.left {c₁ c₂ : List TAC} {p : Prog} {offset : Nat}
    (h : RC.CodeAt (c₁ ++ c₂) p offset) : RC.CodeAt c₁ p offset := by
  intro i hi
  have := h i (by simp; omega)
  rwa [List.getElem?_append_left (by exact hi)] at this

theorem RC.CodeAt.right {c₁ c₂ : List TAC} {p : Prog} {offset : Nat}
    (h : RC.CodeAt (c₁ ++ c₂) p offset) : RC.CodeAt c₂ p (offset + c₁.length) := by
  intro i hi
  have := h (c₁.length + i) (by simp; omega)
  rw [show offset + (c₁.length + i) = offset + c₁.length + i from by omega] at this
  rwa [List.getElem?_append_right (by omega),
       show c₁.length + i - c₁.length = i from by omega] at this

theorem RC.CodeAt.head {x : TAC} {xs : List TAC} {p : Prog} {offset : Nat}
    (h : RC.CodeAt (x :: xs) p offset) : p[offset]? = some x := by
  have := h 0 (by simp); simpa using this

theorem RC.CodeAt.intro {c₁ c₂ : List TAC} {p : Prog} {offset : Nat}
    (h₁ : RC.CodeAt c₁ p offset) (h₂ : RC.CodeAt c₂ p (offset + c₁.length)) :
    RC.CodeAt (c₁ ++ c₂) p offset := by
  intro i hi
  by_cases hlt : i < c₁.length
  · rw [List.getElem?_append_left hlt]; exact h₁ i hlt
  · rw [List.getElem?_append_right (by omega)]
    have := h₂ (i - c₁.length) (by simp at hi; omega)
    rwa [show offset + c₁.length + (i - c₁.length) = offset + i from by omega] at this

-- ============================================================
-- § 4. FragExec single-step helpers
-- ============================================================

theorem FragExec.single_const {p : Prog} {pc : Nat} {σ : Store} {am : ArrayMem} {x : Var} {v : Value}
    (h : p[pc]? = some (.const x v)) :
    FragExec p pc σ (pc + 1) (σ[x ↦ v]) am am :=
  Steps.single (Step.const h)

theorem FragExec.single_copy {p : Prog} {pc : Nat} {σ : Store} {am : ArrayMem} {x y : Var}
    (h : p[pc]? = some (.copy x y)) :
    FragExec p pc σ (pc + 1) (σ[x ↦ σ y]) am am :=
  Steps.single (Step.copy h)

theorem FragExec.single_binop {p : Prog} {pc : Nat} {σ : Store} {am : ArrayMem}
    {x : Var} {op : BinOp} {y z : Var} {a b : BitVec 64}
    (h : p[pc]? = some (.binop x op y z))
    (hy : σ y = .int a) (hz : σ z = .int b) (hsafe : op.safe a b) :
    FragExec p pc σ (pc + 1) (σ[x ↦ .int (op.eval a b)]) am am :=
  Steps.single (Step.binop h hy hz hsafe)

theorem FragExec.single_goto {p : Prog} {pc : Nat} {σ : Store} {am : ArrayMem} {l : Label}
    (h : p[pc]? = some (.goto l)) :
    FragExec p pc σ l σ am am :=
  Steps.single (Step.goto h)

theorem FragExec.single_iftrue {p : Prog} {pc : Nat} {σ : Store} {am : ArrayMem} {b : BoolExpr} {l : Label}
    (h : p[pc]? = some (.ifgoto b l)) (hb : b.eval σ am = true) :
    FragExec p pc σ l σ am am :=
  Steps.single (Step.iftrue h hb)

theorem FragExec.single_iffalse {p : Prog} {pc : Nat} {σ : Store} {am : ArrayMem} {b : BoolExpr} {l : Label}
    (h : p[pc]? = some (.ifgoto b l)) (hb : b.eval σ am = false) :
    FragExec p pc σ (pc + 1) σ am am :=
  Steps.single (Step.iffall h hb)

theorem FragExec.single_arrLoad {p : Prog} {pc : Nat} {σ : Store} {am : ArrayMem}
    {x : Var} {arr : ArrayName} {idx : Var} {idxVal : BitVec 64}
    (h : p[pc]? = some (.arrLoad x arr idx .int))
    (hidx : σ idx = .int idxVal)
    (hbounds : idxVal < p.arraySizeBv arr) :
    FragExec p pc σ (pc + 1) (σ[x ↦ .int (am.read arr idxVal)]) am am := by
  have := Steps.single (Step.arrLoad (am := am) h hidx hbounds)
  simp [Value.ofBitVec] at this
  exact this

theorem FragExec.single_arrStore {p : Prog} {pc : Nat} {σ : Store} {am : ArrayMem}
    {arr : ArrayName} {idx val : Var} {idxVal v : BitVec 64}
    (h : p[pc]? = some (.arrStore arr idx val .int))
    (hidx : σ idx = .int idxVal) (hval : σ val = .int v)
    (hbounds : idxVal < p.arraySizeBv arr) :
    FragExec p pc σ (pc + 1) σ am (am.write arr idxVal v) := by
  have hty : (σ val).typeOf = .int := by rw [hval]; simp [Value.typeOf]
  have := Steps.single (Step.arrStore (am := am) h hidx hty hbounds)
  simp [hval, Value.toBits] at this
  exact this

theorem FragExec.single_fbinop {p : Prog} {pc : Nat} {σ : Store} {am : ArrayMem}
    {x : Var} {fop : FloatBinOp} {y z : Var} {a b : BitVec 64}
    (h : p[pc]? = some (.fbinop x fop y z))
    (hy : σ y = .float a) (hz : σ z = .float b) :
    FragExec p pc σ (pc + 1) (σ[x ↦ .float (fop.eval a b)]) am am :=
  Steps.single (Step.fbinop h hy hz)

theorem FragExec.single_intToFloat {p : Prog} {pc : Nat} {σ : Store} {am : ArrayMem}
    {x y : Var} {n : BitVec 64}
    (h : p[pc]? = some (.intToFloat x y))
    (hy : σ y = .int n) :
    FragExec p pc σ (pc + 1) (σ[x ↦ .float (intToFloatBv n)]) am am :=
  Steps.single (Step.intToFloat h hy)

theorem FragExec.single_floatToInt {p : Prog} {pc : Nat} {σ : Store} {am : ArrayMem}
    {x y : Var} {f : BitVec 64}
    (h : p[pc]? = some (.floatToInt x y))
    (hy : σ y = .float f) :
    FragExec p pc σ (pc + 1) (σ[x ↦ .int (floatToIntBv f)]) am am :=
  Steps.single (Step.floatToInt h hy)

theorem FragExec.single_floatUnary {p : Prog} {pc : Nat} {σ : Store} {am : ArrayMem}
    {x y : Var} {op : FloatUnaryOp} {f : BitVec 64}
    (h : p[pc]? = some (.floatUnary x op y))
    (hy : σ y = .float f) :
    FragExec p pc σ (pc + 1) (σ[x ↦ .float (op.eval f)]) am am :=
  Steps.single (Step.floatUnary h hy)

theorem FragExec.single_arrStore_float {p : Prog} {pc : Nat} {σ : Store} {am : ArrayMem}
    {arr : ArrayName} {idx val : Var} {idxVal v : BitVec 64}
    (h : p[pc]? = some (.arrStore arr idx val .float))
    (hidx : σ idx = .int idxVal) (hval : σ val = .float v)
    (hbounds : idxVal < p.arraySizeBv arr) :
    FragExec p pc σ (pc + 1) σ am (am.write arr idxVal v) := by
  have hty : (σ val).typeOf = .float := by rw [hval]; simp [Value.typeOf]
  have := Steps.single (Step.arrStore (am := am) h hidx hty hbounds)
  simp [hval, Value.toBits] at this
  exact this

theorem FragExec.single_arrLoad_float {p : Prog} {pc : Nat} {σ : Store} {am : ArrayMem}
    {x : Var} {arr : ArrayName} {idx : Var} {idxVal : BitVec 64}
    (h : p[pc]? = some (.arrLoad x arr idx .float))
    (hidx : σ idx = .int idxVal)
    (hbounds : idxVal < p.arraySizeBv arr) :
    FragExec p pc σ (pc + 1) (σ[x ↦ .float (am.read arr idxVal)]) am am := by
  have := Steps.single (Step.arrLoad (am := am) h hidx hbounds)
  simp [Value.ofBitVec] at this
  exact this

theorem FragExec.single_arrLoad_bool {p : Prog} {pc : Nat} {σ : Store} {am : ArrayMem}
    {x : Var} {arr : ArrayName} {idx : Var} {idxVal : BitVec 64}
    (h : p[pc]? = some (.arrLoad x arr idx .bool))
    (hidx : σ idx = .int idxVal)
    (hbounds : idxVal < p.arraySizeBv arr) :
    FragExec p pc σ (pc + 1) (σ[x ↦ .bool (am.read arr idxVal != 0)]) am am := by
  have := Steps.single (Step.arrLoad (am := am) h hidx hbounds)
  simp [Value.ofBitVec] at this
  exact this

theorem FragExec.single_arrStore_bool {p : Prog} {pc : Nat} {σ : Store} {am : ArrayMem}
    {arr : ArrayName} {idx val : Var} {idxVal : BitVec 64} {b : Bool}
    (h : p[pc]? = some (.arrStore arr idx val .bool))
    (hidx : σ idx = .int idxVal) (hval : σ val = .bool b)
    (hbounds : idxVal < p.arraySizeBv arr) :
    FragExec p pc σ (pc + 1) σ am (am.write arr idxVal (if b then 1 else 0)) := by
  have hty : (σ val).typeOf = .bool := by rw [hval]; simp [Value.typeOf]
  have := Steps.single (Step.arrStore (am := am) h hidx hty hbounds)
  simp [hval, Value.toBits] at this
  exact this

theorem FragExec.single_boolop {p : Prog} {pc : Nat} {σ : Store} {am : ArrayMem}
    {x : Var} {be : BoolExpr}
    (h : p[pc]? = some (.boolop x be)) :
    FragExec p pc σ (pc + 1) (σ[x ↦ .bool (be.eval σ am)]) am am :=
  Steps.single (Step.boolop h)

theorem FragExec.single_print {p : Prog} {pc : Nat} {σ : Store} {am : ArrayMem}
    {fmt : String} {vs : List Var}
    (h : p[pc]? = some (.print fmt vs)) :
    FragExec p pc σ (pc + 1) σ am am :=
  Steps.single (Step.print h)

theorem FragExec.single_printInt {p : Prog} {pc : Nat} {σ : Store} {am : ArrayMem}
    {v : Var} (h : p[pc]? = some (.printInt v)) :
    FragExec p pc σ (pc + 1) σ am am :=
  Steps.single (Step.printInt h)

theorem FragExec.single_printBool {p : Prog} {pc : Nat} {σ : Store} {am : ArrayMem}
    {v : Var} (h : p[pc]? = some (.printBool v)) :
    FragExec p pc σ (pc + 1) σ am am :=
  Steps.single (Step.printBool h)

theorem FragExec.single_printFloat {p : Prog} {pc : Nat} {σ : Store} {am : ArrayMem}
    {v : Var} (h : p[pc]? = some (.printFloat v)) :
    FragExec p pc σ (pc + 1) σ am am :=
  Steps.single (Step.printFloat h)

theorem FragExec.single_printString {p : Prog} {pc : Nat} {σ : Store} {am : ArrayMem}
    {lit : String} (h : p[pc]? = some (.printString lit)) :
    FragExec p pc σ (pc + 1) σ am am :=
  Steps.single (Step.printString h)

-- ============================================================
-- § 6. Division safety helpers
-- ============================================================

theorem SExpr.safe_bin_safe {op : BinOp} {a b : SExpr} {σ : Store} {am : ArrayMem}
    {decls : List (ArrayName × Nat × VarTy)}
    (h : (SExpr.bin op a b).safe σ am decls) : op.safe (a.eval σ am) (b.eval σ am) := by
  cases op <;> simp_all [SExpr.safe, BinOp.safe]

theorem SExpr.safe_bin_left {op : BinOp} {a b : SExpr} {σ : Store} {am : ArrayMem}
    {decls : List (ArrayName × Nat × VarTy)}
    (h : (SExpr.bin op a b).safe σ am decls) : a.safe σ am decls := by
  cases op <;> simp_all [SExpr.safe]

theorem SExpr.safe_bin_right {op : BinOp} {a b : SExpr} {σ : Store} {am : ArrayMem}
    {decls : List (ArrayName × Nat × VarTy)}
    (h : (SExpr.bin op a b).safe σ am decls) : b.safe σ am decls := by
  cases op <;> simp_all [SExpr.safe]

theorem SExpr.safe_fbin_left {fop : FloatBinOp} {a b : SExpr} {σ : Store} {am : ArrayMem}
    {decls : List (ArrayName × Nat × VarTy)}
    (h : (SExpr.fbin fop a b).safe σ am decls) : a.safe σ am decls := by
  simp [SExpr.safe] at h; exact h.1

theorem SExpr.safe_fbin_right {fop : FloatBinOp} {a b : SExpr} {σ : Store} {am : ArrayMem}
    {decls : List (ArrayName × Nat × VarTy)}
    (h : (SExpr.fbin fop a b).safe σ am decls) : b.safe σ am decls := by
  simp [SExpr.safe] at h; exact h.2

-- ============================================================
-- § 7. Store update helpers
-- ============================================================

theorem Store.update_tmpName_ne {σ : Store} {k j : Nat} {v : Value}
    (hne : j ≠ k) : (σ[tmpName k ↦ v]) (tmpName j) = σ (tmpName j) :=
  Store.update_other σ (tmpName k) (tmpName j) v (tmpName_ne hne)

theorem Store.update_isTmp_ne {σ : Store} {t : Var} {v : Value}
    {w : Var} (ht : t.isTmp = true) (hw : w.isTmp = false) :
    (σ[t ↦ v]) w = σ w :=
  Store.update_other σ t w v (fun heq => by rw [heq] at hw; simp [hw] at ht)

theorem Store.update_isFTmp_ne {σ : Store} {t : Var} {v : Value}
    {w : Var} (ht : t.isFTmp = true) (hw : w.isFTmp = false) :
    (σ[t ↦ v]) w = σ w :=
  Store.update_other σ t w v (fun heq => by rw [heq] at hw; simp [hw] at ht)

theorem Store.update_ftmpName_ne {σ : Store} {k j : Nat} {v : Value}
    (hne : j ≠ k) : (σ[ftmpName k ↦ v]) (ftmpName j) = σ (ftmpName j) :=
  Store.update_other σ (ftmpName k) (ftmpName j) v (ftmpName_ne hne)

theorem Store.update_isBTmp_ne {σ : Store} {t : Var} {v : Value}
    {w : Var} (ht : t.isBTmp = true) (hw : w.isBTmp = false) :
    (σ[t ↦ v]) w = σ w :=
  Store.update_other σ t w v (fun heq => by rw [heq] at hw; simp [hw] at ht)

private theorem btmpName_injective : Function.Injective btmpName := by
  intro k j h
  have h2 := String.ext_iff.mp h
  simp only [btmpName, String.toList_append] at h2
  have h3 := List.append_cancel_left h2
  exact Nat_toString_injective (String.ext_iff.mpr h3)

theorem btmpName_ne {k j : Nat} (h : k ≠ j) : btmpName k ≠ btmpName j :=
  fun heq => h (btmpName_injective heq)

theorem btmpName_isBTmp (k : Nat) : (btmpName k).isBTmp = true :=
  btmpName_isBTmp_wt k

/-- `btmpName k` is NOT a regular int temp (different prefix). -/
theorem btmpName_not_isTmp (k : Nat) : (btmpName k).isTmp = false := by
  simp only [String.isTmp, btmpName, String.toList_append]
  show (match '_' :: '_' :: 'b' :: 't' :: (toString k).toList with
    | '_' :: '_' :: 't' :: _ => true | _ => false) = false
  rfl

/-- `btmpName k` is NOT a float temp (different prefix). -/
theorem btmpName_not_isFTmp (k : Nat) : (btmpName k).isFTmp = false := by
  simp only [String.isFTmp, btmpName, String.toList_append]
  show (match '_' :: '_' :: 'b' :: 't' :: (toString k).toList with
    | '_' :: '_' :: 'f' :: 't' :: _ => true | _ => false) = false
  rfl

/-- `tmpName k` is NOT a bool temp. -/
theorem tmpName_not_isBTmp (k : Nat) : (tmpName k).isBTmp = false := by
  simp only [String.isBTmp, tmpName, String.toList_append]
  show (match '_' :: '_' :: 't' :: (toString k).toList with
    | '_' :: '_' :: 'b' :: 't' :: _ => true | _ => false) = false
  rfl

/-- `ftmpName k` is NOT a bool temp. -/
theorem ftmpName_not_isBTmp (k : Nat) : (ftmpName k).isBTmp = false := by
  simp only [String.isBTmp, ftmpName, String.toList_append]
  show (match '_' :: '_' :: 'f' :: 't' :: (toString k).toList with
    | '_' :: '_' :: 'b' :: 't' :: _ => true | _ => false) = false
  rfl

/-- `tmpName` and `btmpName` never collide. -/
theorem tmpName_ne_btmpName {k j : Nat} : tmpName k ≠ btmpName j := by
  intro h
  have ht : (tmpName k).isTmp = true := tmpName_isTmp k
  have hb : (btmpName j).isTmp = false := btmpName_not_isTmp j
  rw [h] at ht; simp_all

/-- `ftmpName` and `btmpName` never collide. -/
theorem ftmpName_ne_btmpName {k j : Nat} : ftmpName k ≠ btmpName j := by
  intro h
  have hf : (ftmpName k).isFTmp = true := ftmpName_isFTmp k
  have hb : (btmpName j).isFTmp = false := btmpName_not_isFTmp j
  rw [h] at hf; simp_all

theorem Store.update_btmpName_ne {σ : Store} {k j : Nat} {v : Value}
    (hne : j ≠ k) : (σ[btmpName k ↦ v]) (btmpName j) = σ (btmpName j) :=
  Store.update_other σ (btmpName k) (btmpName j) v (btmpName_ne hne)
