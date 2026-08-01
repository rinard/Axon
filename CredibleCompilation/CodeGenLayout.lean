-- Copyright (c) 2026 Martin Rinard
/-
  CodeGenLayout: Layout construction and codegen prerequisite checks.

  Extracted from CodeGen.lean so that ExecChecker.lean can import these
  functions (ExecChecker cannot import CodeGen due to dependency order).
-/
import CredibleCompilation.ArmSemantics

-- ============================================================
-- § 1. Variable collection and stack offset map
-- ============================================================

/-- Collect all distinct variables in a program (instruction vars + observables).
    Uses addIfNew pattern to deduplicate. -/
def collectVars (p : Prog) : List Var :=
  let vars := p.code.foldl (init := ([] : List Var)) fun acc instr =>
    (TAC.vars instr).foldl (fun a v => if a.contains v then a else a ++ [v]) acc
  p.observable.foldl (fun acc v => if acc.contains v then acc else acc ++ [v]) vars

/-- Build stack offset map: var i gets offset (i+1)*8. -/
def buildVarMap (vars : List Var) : List (Var × Nat) :=
  (List.range vars.length).zip vars |>.map fun (i, v) => (v, (i + 1) * 8)

/-- Look up a variable's stack offset in the varMap. -/
def lookupVar (varMap : List (Var × Nat)) (v : Var) : Option Nat :=
  varMap.find? (fun (x, _) => x == v) |>.map Prod.snd

-- ============================================================
-- § 2. Register mapping
-- ============================================================

/-- Map a variable name to an ARM integer register.
    `__irN` and `__brN` both map to xN (they share the integer register file). -/
def varToArmReg (v : Var) : Option ArmReg :=
  let n? := if startsWithList v "__ir" then (v.drop 4).toNat?
            else if startsWithList v "__br" then (v.drop 4).toNat?
            else none
  match n? with
  | some 0 => some .x0 | some 1 => some .x1 | some 2 => some .x2
  | some 3 => some .x3 | some 4 => some .x4 | some 5 => some .x5
  | some 6 => some .x6 | some 7 => some .x7 | some 8 => some .x8
  | some 9 => some .x9 | some 10 => some .x10 | some 11 => some .x11
  | some 12 => some .x12 | some 13 => some .x13 | some 14 => some .x14
  | some 15 => some .x15 | some 16 => some .x16 | some 17 => some .x17
  | some 18 => some .x18 | some 19 => some .x19 | some 20 => some .x20
  | some 21 => some .x21 | some 22 => some .x22 | some 23 => some .x23
  | some 24 => some .x24 | some 25 => some .x25 | some 26 => some .x26
  | some 27 => some .x27 | some 28 => some .x28 | _ => none

/-- Map a variable name to an ARM floating-point register.
    `__frN` maps to dN. -/
def varToArmFReg (v : Var) : Option ArmFReg :=
  if startsWithList v "__fr" then
    match (v.drop 4).toNat? with
    | some 0 => some .d0 | some 1 => some .d1 | some 2 => some .d2
    | some 3 => some .d3 | some 4 => some .d4 | some 5 => some .d5
    | some 6 => some .d6 | some 7 => some .d7 | some 8 => some .d8
    | some 9 => some .d9 | some 10 => some .d10 | some 11 => some .d11
    | some 12 => some .d12 | some 13 => some .d13 | some 14 => some .d14
    | some 15 => some .d15 | _ => none
  else none

-- ============================================================
-- § 3. Layout construction
-- ============================================================

/-- Build a VarLayout from the variable list and stack offset map.
    Register-allocated vars (named `__irN`/`__brN`/`__frN`) map to their register;
    all others map to their stack slot. -/
def buildVarLayout (vars : List Var) (varMap : List (Var × Nat)) : VarLayout :=
  { entries := vars.filterMap fun v =>
      match varToArmReg v with
      | some r => some (v, .ireg r)
      | none => match varToArmFReg v with
        | some r => some (v, .freg r)
        | none => match lookupVar varMap v with
          | some off => some (v, .stack off)
          | none => none }

-- ============================================================
-- § 4. Caller-save spec check
-- ============================================================

def listNodupBool [BEq α] : List α → Bool
  | [] => true
  | x :: rest => !rest.any (· == x) && listNodupBool rest

theorem listNodupBool_sound [DecidableEq α] {l : List α}
    (h : listNodupBool l = true) : l.Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons x rest ih =>
    simp only [listNodupBool, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨hNotIn, hRest⟩ := h
    refine List.nodup_cons.mpr ⟨?_, ih hRest⟩
    intro hMem
    simp only [Bool.eq_false_iff] at hNotIn
    exact hNotIn (List.any_eq_true.mpr ⟨x, hMem, by simp⟩)

/-- Check all properties needed by `callerSave_composition` for
    the entries produced by `genCallerSaveAll layout varMap`. -/
def checkCallerSaveSpec (layout : VarLayout) (varMap : List (Var × Nat)) : Bool :=
  let entries := genCallerSaveAll layout varMap
  -- hFresh: no save offset equals a stack layout offset
  entries.all (fun e =>
    layout.entries.all (fun (_, loc) =>
      match loc with | .stack o => !(o == e.off) | _ => true)) &&
  -- hNodup: save offsets pairwise distinct
  listNodupBool (entries.map CallerSaveEntry.off) &&
  -- hCoversIreg: every caller-saved ireg in layout has an entry
  layout.entries.all (fun (_, loc) =>
    match loc with
    | .ireg r => !r.isCallerSaved ||
        entries.any (fun e => match e with | .ireg ir _ => ir == r | _ => false)
    | _ => true) &&
  -- hCoversFreg: every caller-saved freg in layout has an entry
  layout.entries.all (fun (_, loc) =>
    match loc with
    | .freg r => !r.isCallerSaved ||
        entries.any (fun e => match e with | .freg fr _ => fr == r | _ => false)
    | _ => true) &&
  -- hUniqIreg: any two ireg entries with the same register have equal offsets
  entries.all (fun e1 => entries.all (fun e2 =>
    match e1, e2 with
    | .ireg ir1 off1, .ireg ir2 off2 => !(ir1 == ir2) || (off1 == off2)
    | _, _ => true)) &&
  -- hUniqFreg: any two freg entries with the same register have equal offsets
  entries.all (fun e1 => entries.all (fun e2 =>
    match e1, e2 with
    | .freg fr1 off1, .freg fr2 off2 => !(fr1 == fr2) || (off1 == off2)
    | _, _ => true))

-- ============================================================
-- § 5. Well-typed layout check
-- ============================================================

/-- Check that the layout is type-consistent and complete for all instructions.
    Returns `none` on success, `some errMsg` on failure. -/
def checkWellTypedLayout (Γ : TyCtx) (layout : VarLayout) (code : Array TAC) : Option String :=
  let allVars := code.foldl (init := ([] : List Var)) fun acc instr =>
    acc ++ (TAC.vars instr).filter fun v => !acc.contains v
  let typeErr := layout.entries.find? fun (v, loc) =>
    match loc with
    | .freg _ => Γ v != .float
    | .ireg _ => Γ v == .float
    | .stack _ => false
  match typeErr with
  | some (v, loc) =>
    let locStr := match loc with
      | .freg _ => "freg" | .ireg _ => "ireg" | .stack _ => "stack"
    let tyStr := match Γ v with | .int => "int" | .bool => "bool" | .float => "float"
    some s!"layout type mismatch: {v} (type {tyStr}) in {locStr}"
  | none =>
  match allVars.find? fun v => (layout v).isNone with
  | some v => some s!"variable {v} referenced but not in layout"
  | none => none

-- ============================================================
theorem lookup_mem {v : String} {loc : VarLoc}
    {entries : List (String × VarLoc)}
    (h : entries.lookup v = some loc) : (v, loc) ∈ entries := by
  induction entries with
  | nil => simp [List.lookup] at h
  | cons hd tl ih =>
    simp only [List.lookup] at h
    split at h
    · rename_i heq
      have hv : v = hd.fst := by simpa using heq
      have hl : hd.snd = loc := by simpa using h
      subst hv; subst hl; simp
    · exact List.mem_cons_of_mem _ (ih h)

/-- checkWellTypedLayout returning none implies WellTypedLayout (type consistency). -/
theorem checkWellTypedLayout_wellTyped {Γ : TyCtx} {layout : VarLayout}
    {code : Array TAC}
    (h : checkWellTypedLayout Γ layout code = none) : WellTypedLayout Γ layout := by
  simp only [checkWellTypedLayout] at h
  split at h
  · simp at h
  · rename_i hTypeOk
    split at h
    · simp at h
    · constructor
      · intro v fr hNotFloat hContra
        have := (List.find?_eq_none.mp hTypeOk) ⟨v, .freg fr⟩ (lookup_mem hContra)
        simp at this; exact absurd this hNotFloat
      · intro v ir hFloat hContra
        have := (List.find?_eq_none.mp hTypeOk) ⟨v, .ireg ir⟩ (lookup_mem hContra)
        simp at this; exact absurd hFloat this

-- § 6. Codegen prerequisite check
-- ============================================================

/-- Pre-check the codegen-specific properties: layout injectivity, caller-save spec,
    and well-typed layout. All are decidable checks on the constructed layout.
    Added to `checkCertificateExec` so that `generateAsm_total` can derive them. -/
def checkCodegenPrereqs (tyCtx : TyCtx) (p : Prog) : Bool :=
  let vars := collectVars p
  let varMap := buildVarMap vars
  let layout := buildVarLayout vars varMap
  layout.regConventionSafe && layout.isInjective && checkCallerSaveSpec layout varMap &&
  checkWellTypedLayout tyCtx layout p.code == none
