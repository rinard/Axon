-- Copyright (c) 2026 Martin Rinard
import CredibleCompilation.TAC

/-!
# Type System for Three-Address Code

Well-typedness definitions, decidable type checking, type preservation,
and type safety.

Split from `Semantics.lean`.
-/

-- ============================================================
-- § 3a. Type system definitions
-- ============================================================

/-- An expression has a given type under context Γ (leaf forms only). -/
def ExprHasTy (Γ : TyCtx) : Expr → VarTy → Prop
  | .var x, ty => Γ x = ty
  | .lit _, .int => True
  | .flit _, .float => True
  | .blit _, .bool => True
  | _, _ => True

/-- Decidable check that an Expr has the given type. -/
def checkExprTy (Γ : TyCtx) : Expr → VarTy → Bool
  | .var x, ty => decide (Γ x = ty)
  | .lit _, .int => true
  | .flit _, .float => true
  | .blit _, .bool => true
  | _, _ => true

theorem checkExprTy_sound {Γ : TyCtx} {e : Expr} {ty : VarTy}
    (h : checkExprTy Γ e ty = true) : ExprHasTy Γ e ty := by
  cases e <;> cases ty <;> simp_all [checkExprTy, ExprHasTy]

/-- Well-typedness for boolean expressions. -/
inductive WellTypedBoolExpr (Γ : TyCtx) : BoolExpr → Prop where
  | lit    : WellTypedBoolExpr Γ (.lit b)
  | bvar   : Γ x = .bool → WellTypedBoolExpr Γ (.bvar x)
  | cmp    : ExprHasTy Γ a .int → ExprHasTy Γ b .int → WellTypedBoolExpr Γ (.cmp op a b)
  | not    : WellTypedBoolExpr Γ b → WellTypedBoolExpr Γ (.not b)
  | fcmp   : ExprHasTy Γ a .float → ExprHasTy Γ b .float → WellTypedBoolExpr Γ (.fcmp op a b)
  | bexpr  : ExprHasTy Γ e .bool → WellTypedBoolExpr Γ (.bexpr e)

/-- Well-typedness for a single TAC instruction.
    Array instructions additionally require the element type to match the
    declared `arrayElemTy`. -/
inductive WellTypedInstr (Γ : TyCtx) (decls : List (ArrayName × Nat × VarTy)) : TAC → Prop where
  | const  : v.typeOf = Γ x → WellTypedInstr Γ decls (.const x v)
  | copy   : Γ x = Γ y → WellTypedInstr Γ decls (.copy x y)
  | binop  : Γ x = .int → Γ y = .int → Γ z = .int →
      WellTypedInstr Γ decls (.binop x op y z)
  | boolop : Γ x = .bool → WellTypedBoolExpr Γ be →
      WellTypedInstr Γ decls (.boolop x be)
  | goto   : WellTypedInstr Γ decls (.goto l)
  | ifgoto : WellTypedBoolExpr Γ b → WellTypedInstr Γ decls (.ifgoto b l)
  | halt   : WellTypedInstr Γ decls .halt
  | arrLoad  : Γ x = ty → Γ idx = .int → ty = arrayElemTy decls arr →
      WellTypedInstr Γ decls (.arrLoad x arr idx ty)
  | arrStore : Γ idx = .int → Γ val = ty → ty = arrayElemTy decls arr →
      WellTypedInstr Γ decls (.arrStore arr idx val ty)
  | fbinop : Γ x = .float → Γ y = .float → Γ z = .float →
      WellTypedInstr Γ decls (.fbinop x fop y z)
  | intToFloat : Γ x = .float → Γ y = .int → WellTypedInstr Γ decls (.intToFloat x y)
  | floatToInt : Γ x = .int → Γ y = .float → WellTypedInstr Γ decls (.floatToInt x y)
  | floatUnary : Γ x = .float → Γ y = .float → WellTypedInstr Γ decls (.floatUnary x op y)
  | fternop : Γ x = .float → Γ a = .float → Γ b = .float → Γ c = .float →
      WellTypedInstr Γ decls (.fternop x op a b c)
  | print     : WellTypedInstr Γ decls (.print fmt vs)
  | printInt  : Γ v = .int → WellTypedInstr Γ decls (.printInt v)
  | printBool : (Γ v = .bool ∨ Γ v = .int) → WellTypedInstr Γ decls (.printBool v)
  | printFloat : Γ v = .float → WellTypedInstr Γ decls (.printFloat v)
  | printString : WellTypedInstr Γ decls (.printString lit)

/-- A program is well-typed if every instruction is well-typed. -/
def WellTypedProg (Γ : TyCtx) (p : Prog) : Prop :=
  ∀ i, (h : i < p.size) → WellTypedInstr Γ p.arrayDecls p[i]

-- ============================================================
-- § 9. Progress and successor lemmas
-- ============================================================

/-- Helper: extract instruction identity from array lookup. -/
private theorem instr_eq_of_lookup {p : Prog} {pc : Nat} {instr : TAC}
    (hpc : pc < p.size) (h : p[pc]? = some instr) : p[pc] = instr :=
  Option.some.inj ((Prog.getElem?_eq_getElem hpc).symm.trans h)

/-- **Progress**: if the instruction at `pc` exists, the program is
    well-typed, and the store is well-typed, then a step is always possible.
    Unsafe division produces a `Cfg.error` transition rather than getting stuck. -/
theorem Step.progress (p : Prog) (pc : Nat) (σ : Store) (am : ArrayMem) (Γ : TyCtx)
    (hinb : pc < p.size)
    (hwtp : WellTypedProg Γ p) (hts : TypedStore Γ σ) :
    ∃ c', Step p (Cfg.run pc σ am) c' := by
  have hinstr : p[pc]? = some p[pc] := Prog.getElem?_eq_getElem hinb
  have hwti := hwtp pc hinb
  match hp : p[pc] with
  | .const x v     => exact ⟨_, .const (hp ▸ hinstr)⟩
  | .copy x y      => exact ⟨_, .copy (hp ▸ hinstr)⟩
  | .binop x op y z =>
    rw [hp] at hwti; cases hwti with
    | binop _ hy hz =>
      obtain ⟨a, ha⟩ : ∃ n, σ y = .int n := Value.int_of_typeOf_int (by rw [hts y]; exact hy)
      obtain ⟨b, hb⟩ : ∃ n, σ z = .int n := Value.int_of_typeOf_int (by rw [hts z]; exact hz)
      by_cases hs : op.safe a b
      · exact ⟨_, .binop (hp ▸ hinstr) ha hb hs⟩
      · exact ⟨_, .binop_divByZero (hp ▸ hinstr) ha hb hs⟩
  | .boolop x be   => exact ⟨_, .boolop (hp ▸ hinstr)⟩
  | .goto l        => exact ⟨_, .goto (hp ▸ hinstr)⟩
  | .ifgoto b l    =>
    by_cases hb : b.eval σ am = true
    · exact ⟨_, .iftrue (hp ▸ hinstr) hb⟩
    · exact ⟨_, .iffall (hp ▸ hinstr) (Bool.eq_false_iff.mpr hb)⟩
  | .halt          => exact ⟨_, .halt (hp ▸ hinstr)⟩
  | .arrLoad x arr idx ty =>
    rw [hp] at hwti; cases hwti with
    | arrLoad _ hidx _ =>
      obtain ⟨iv, hiv⟩ := Value.int_of_typeOf_int (by rw [hts idx]; exact hidx)
      by_cases hb : iv < p.arraySizeBv arr
      · exact ⟨_, .arrLoad (hp ▸ hinstr) hiv hb⟩
      · exact ⟨_, .arrLoad_boundsError (hp ▸ hinstr) hiv hb⟩
  | .arrStore arr idx val ty =>
    rw [hp] at hwti; cases hwti with
    | arrStore hidx hval _ =>
      obtain ⟨iv, hiv⟩ := Value.int_of_typeOf_int (by rw [hts idx]; exact hidx)
      have hty : (σ val).typeOf = ty := by rw [hts val]; exact hval
      by_cases hb : iv < p.arraySizeBv arr
      · exact ⟨_, .arrStore (hp ▸ hinstr) hiv hty hb⟩
      · exact ⟨_, .arrStore_boundsError (hp ▸ hinstr) hiv hty hb⟩
  | .fbinop x fop y z =>
    rw [hp] at hwti; cases hwti with
    | fbinop _ hy hz =>
      obtain ⟨a, ha⟩ := Value.float_of_typeOf_float (by rw [hts y]; exact hy)
      obtain ⟨b, hb⟩ := Value.float_of_typeOf_float (by rw [hts z]; exact hz)
      exact ⟨_, .fbinop (hp ▸ hinstr) ha hb⟩
  | .intToFloat x y =>
    rw [hp] at hwti; cases hwti with
    | intToFloat _ hy =>
      obtain ⟨n, hn⟩ := Value.int_of_typeOf_int (by rw [hts y]; exact hy)
      exact ⟨_, .intToFloat (hp ▸ hinstr) hn⟩
  | .floatToInt x y =>
    rw [hp] at hwti; cases hwti with
    | floatToInt _ hy =>
      obtain ⟨f, hf⟩ := Value.float_of_typeOf_float (by rw [hts y]; exact hy)
      exact ⟨_, .floatToInt (hp ▸ hinstr) hf⟩
  | .floatUnary x op y =>
    rw [hp] at hwti; cases hwti with
    | floatUnary _ hy =>
      obtain ⟨f, hf⟩ := Value.float_of_typeOf_float (by rw [hts y]; exact hy)
      exact ⟨_, .floatUnary (hp ▸ hinstr) hf⟩
  | .fternop x op a b c =>
    rw [hp] at hwti; cases hwti with
    | fternop _ ha hb hc =>
      obtain ⟨fa, hfa⟩ := Value.float_of_typeOf_float (by rw [hts a]; exact ha)
      obtain ⟨fb, hfb⟩ := Value.float_of_typeOf_float (by rw [hts b]; exact hb)
      obtain ⟨fc, hfc⟩ := Value.float_of_typeOf_float (by rw [hts c]; exact hc)
      exact ⟨_, .fternop (hp ▸ hinstr) hfa hfb hfc⟩
  | .print _ _     => exact ⟨_, .print (hp ▸ hinstr)⟩
  | .printInt _    => exact ⟨_, .printInt (hp ▸ hinstr)⟩
  | .printBool _   => exact ⟨_, .printBool (hp ▸ hinstr)⟩
  | .printFloat _  => exact ⟨_, .printFloat (hp ▸ hinstr)⟩
  | .printString _ => exact ⟨_, .printString (hp ▸ hinstr)⟩

/-- **Type safety (single step)**: a well-typed program with a well-typed store
    never steps to a type-error configuration. -/
theorem Step.no_typeError_of_wellTyped {p : Prog} {pc : Nat} {σ τ : Store} {am am' : ArrayMem} {Γ : TyCtx}
    (hpc : pc < p.size) (hwtp : WellTypedProg Γ p) (hts : TypedStore Γ σ) :
    ¬ (p ⊩ Cfg.run pc σ am ⟶ Cfg.typeError τ am') := by
  intro hstep
  cases hstep with
  | binop_typeError hinstr hne =>
    have hwti := hwtp pc hpc
    have := instr_eq_of_lookup hpc hinstr
    rw [this] at hwti
    cases hwti with
    | binop _ hy hz =>
      cases hne with
      | inl hl => exact hl (by rw [hts]; exact hy)
      | inr hr => exact hr (by rw [hts]; exact hz)
  | arrLoad_typeError hinstr hne =>
    have hwti := hwtp pc hpc
    have := instr_eq_of_lookup hpc hinstr
    rw [this] at hwti
    cases hwti with
    | arrLoad _ hidx _ => exact hne (by rw [hts]; exact hidx)
  | arrStore_typeError hinstr hne =>
    have hwti := hwtp pc hpc
    have := instr_eq_of_lookup hpc hinstr
    rw [this] at hwti
    cases hwti with
    | arrStore hidx hval _ =>
      cases hne with
      | inl hl => exact hl (by rw [hts]; exact hidx)
      | inr hr => exact hr (by rw [hts]; exact hval)
  | fbinop_typeError hinstr hne =>
    have hwti := hwtp pc hpc
    have := instr_eq_of_lookup hpc hinstr
    rw [this] at hwti
    cases hwti with
    | fbinop _ hy hz =>
      cases hne with
      | inl hl => exact hl (by rw [hts]; exact hy)
      | inr hr => exact hr (by rw [hts]; exact hz)
  | intToFloat_typeError hinstr hne =>
    have hwti := hwtp pc hpc
    have := instr_eq_of_lookup hpc hinstr
    rw [this] at hwti
    cases hwti with
    | intToFloat _ hy => exact hne (by rw [hts]; exact hy)
  | floatToInt_typeError hinstr hne =>
    have hwti := hwtp pc hpc
    have := instr_eq_of_lookup hpc hinstr
    rw [this] at hwti
    cases hwti with
    | floatToInt _ hy => exact hne (by rw [hts]; exact hy)
  | floatUnary_typeError hinstr hne =>
    have hwti := hwtp pc hpc
    have := instr_eq_of_lookup hpc hinstr
    rw [this] at hwti
    cases hwti with
    | floatUnary _ hy => exact hne (by rw [hts]; exact hy)
  | fternop_typeError hinstr hne =>
    have hwti := hwtp pc hpc
    have := instr_eq_of_lookup hpc hinstr
    rw [this] at hwti
    cases hwti with
    | fternop _ ha hb hc =>
      rcases hne with hl | hm | hr
      · exact hl (by rw [hts]; exact ha)
      · exact hm (by rw [hts]; exact hb)
      · exact hr (by rw [hts]; exact hc)

/-- **Progress (untyped)**: an in-bounds PC always admits a step,
    regardless of type safety. For ill-typed binop operands, the step
    is `binop_typeError`. -/
theorem Step.progress_untyped (p : Prog) (pc : Nat) (σ : Store) (am : ArrayMem)
    (hinb : pc < p.size) :
    ∃ c', Step p (Cfg.run pc σ am) c' := by
  have hinstr : p[pc]? = some p[pc] := Prog.getElem?_eq_getElem hinb
  match hp : p[pc] with
  | .const x v     => exact ⟨_, .const (hp ▸ hinstr)⟩
  | .copy x y      => exact ⟨_, .copy (hp ▸ hinstr)⟩
  | .binop x op y z =>
    by_cases hy : (σ y).typeOf = .int
    · by_cases hz : (σ z).typeOf = .int
      · obtain ⟨a, ha⟩ := Value.int_of_typeOf_int hy
        obtain ⟨b, hb⟩ := Value.int_of_typeOf_int hz
        by_cases hs : op.safe a b
        · exact ⟨_, .binop (hp ▸ hinstr) ha hb hs⟩
        · exact ⟨_, .binop_divByZero (hp ▸ hinstr) ha hb hs⟩
      · exact ⟨_, .binop_typeError (hp ▸ hinstr) (.inr hz)⟩
    · exact ⟨_, .binop_typeError (hp ▸ hinstr) (.inl hy)⟩
  | .boolop x be   => exact ⟨_, .boolop (hp ▸ hinstr)⟩
  | .goto l        => exact ⟨_, .goto (hp ▸ hinstr)⟩
  | .ifgoto b l    =>
    by_cases hb : b.eval σ am = true
    · exact ⟨_, .iftrue (hp ▸ hinstr) hb⟩
    · exact ⟨_, .iffall (hp ▸ hinstr) (Bool.eq_false_iff.mpr hb)⟩
  | .halt          => exact ⟨_, .halt (hp ▸ hinstr)⟩
  | .arrLoad x arr idx ty =>
    by_cases hidx : (σ idx).typeOf = .int
    · obtain ⟨iv, hiv⟩ := Value.int_of_typeOf_int hidx
      by_cases hb : iv < p.arraySizeBv arr
      · exact ⟨_, .arrLoad (hp ▸ hinstr) hiv hb⟩
      · exact ⟨_, .arrLoad_boundsError (hp ▸ hinstr) hiv hb⟩
    · exact ⟨_, .arrLoad_typeError (hp ▸ hinstr) hidx⟩
  | .arrStore arr idx val ty =>
    by_cases hidx : (σ idx).typeOf = .int
    · by_cases hval : (σ val).typeOf = ty
      · obtain ⟨iv, hiv⟩ := Value.int_of_typeOf_int hidx
        by_cases hb : iv < p.arraySizeBv arr
        · exact ⟨_, .arrStore (hp ▸ hinstr) hiv hval hb⟩
        · exact ⟨_, .arrStore_boundsError (hp ▸ hinstr) hiv hval hb⟩
      · exact ⟨_, .arrStore_typeError (hp ▸ hinstr) (.inr hval)⟩
    · exact ⟨_, .arrStore_typeError (hp ▸ hinstr) (.inl hidx)⟩
  | .fbinop x fop y z =>
    by_cases hy : (σ y).typeOf = .float
    · by_cases hz : (σ z).typeOf = .float
      · obtain ⟨a, ha⟩ := Value.float_of_typeOf_float hy
        obtain ⟨b, hb⟩ := Value.float_of_typeOf_float hz
        exact ⟨_, .fbinop (hp ▸ hinstr) ha hb⟩
      · exact ⟨_, .fbinop_typeError (hp ▸ hinstr) (.inr hz)⟩
    · exact ⟨_, .fbinop_typeError (hp ▸ hinstr) (.inl hy)⟩
  | .intToFloat x y =>
    by_cases hy : (σ y).typeOf = .int
    · obtain ⟨n, hn⟩ := Value.int_of_typeOf_int hy
      exact ⟨_, .intToFloat (hp ▸ hinstr) hn⟩
    · exact ⟨_, .intToFloat_typeError (hp ▸ hinstr) hy⟩
  | .floatToInt x y =>
    by_cases hy : (σ y).typeOf = .float
    · obtain ⟨f, hf⟩ := Value.float_of_typeOf_float hy
      exact ⟨_, .floatToInt (hp ▸ hinstr) hf⟩
    · exact ⟨_, .floatToInt_typeError (hp ▸ hinstr) hy⟩
  | .floatUnary x op y =>
    by_cases hy : (σ y).typeOf = .float
    · obtain ⟨f, hf⟩ := Value.float_of_typeOf_float hy
      exact ⟨_, .floatUnary (hp ▸ hinstr) hf⟩
    · exact ⟨_, .floatUnary_typeError (hp ▸ hinstr) hy⟩
  | .fternop x op a b c =>
    by_cases ha : (σ a).typeOf = .float
    · by_cases hb : (σ b).typeOf = .float
      · by_cases hc : (σ c).typeOf = .float
        · obtain ⟨fa, hfa⟩ := Value.float_of_typeOf_float ha
          obtain ⟨fb, hfb⟩ := Value.float_of_typeOf_float hb
          obtain ⟨fc, hfc⟩ := Value.float_of_typeOf_float hc
          exact ⟨_, .fternop (hp ▸ hinstr) hfa hfb hfc⟩
        · exact ⟨_, .fternop_typeError (hp ▸ hinstr) (.inr (.inr hc))⟩
      · exact ⟨_, .fternop_typeError (hp ▸ hinstr) (.inr (.inl hb))⟩
    · exact ⟨_, .fternop_typeError (hp ▸ hinstr) (.inl ha)⟩
  | .print _ _     => exact ⟨_, .print (hp ▸ hinstr)⟩
  | .printInt _    => exact ⟨_, .printInt (hp ▸ hinstr)⟩
  | .printBool _   => exact ⟨_, .printBool (hp ▸ hinstr)⟩
  | .printFloat _  => exact ⟨_, .printFloat (hp ▸ hinstr)⟩
  | .printString _ => exact ⟨_, .printString (hp ▸ hinstr)⟩

-- ============================================================
-- § 11. Decidable type checking
-- ============================================================

def checkWellTypedBoolExpr (Γ : TyCtx) : BoolExpr → Bool
  | .lit _        => true
  | .bvar x       => decide (Γ x = .bool)
  | .cmp _ a b    => checkExprTy Γ a .int && checkExprTy Γ b .int
  | .not e        => checkWellTypedBoolExpr Γ e
  | .fcmp _ a b   => checkExprTy Γ a .float && checkExprTy Γ b .float
  | .bexpr e      => checkExprTy Γ e .bool

def checkWellTypedInstr (Γ : TyCtx) (decls : List (ArrayName × Nat × VarTy)) : TAC → Bool
  | .const x v     => decide (v.typeOf = Γ x)
  | .copy x y      => decide (Γ x = Γ y)
  | .binop x _ y z => decide (Γ x = .int) && decide (Γ y = .int) && decide (Γ z = .int)
  | .boolop x be   => decide (Γ x = .bool) && checkWellTypedBoolExpr Γ be
  | .goto _        => true
  | .ifgoto b _    => checkWellTypedBoolExpr Γ b
  | .halt          => true
  | .arrLoad x arr idx ty  => decide (Γ x = ty) && decide (Γ idx = .int) && decide (ty = arrayElemTy decls arr)
  | .arrStore arr idx val ty => decide (Γ idx = .int) && decide (Γ val = ty) && decide (ty = arrayElemTy decls arr)
  | .fbinop x _ y z => decide (Γ x = .float) && decide (Γ y = .float) && decide (Γ z = .float)
  | .intToFloat x y => decide (Γ x = .float) && decide (Γ y = .int)
  | .floatToInt x y => decide (Γ x = .int) && decide (Γ y = .float)
  | .floatUnary x _ y => decide (Γ x = .float) && decide (Γ y = .float)
  | .fternop x _ a b c => decide (Γ x = .float) && decide (Γ a = .float) && decide (Γ b = .float) && decide (Γ c = .float)
  | .print _ _    => true
  | .printInt v   => decide (Γ v = .int)
  | .printBool v  => decide (Γ v = .bool) || decide (Γ v = .int)
  | .printFloat v => decide (Γ v = .float)
  | .printString _ => true

theorem checkWellTypedBoolExpr_sound {Γ : TyCtx} {b : BoolExpr}
    (h : checkWellTypedBoolExpr Γ b = true) : WellTypedBoolExpr Γ b := by
  induction b with
  | lit _ => exact .lit
  | bvar x =>
    simp [checkWellTypedBoolExpr, decide_eq_true_eq] at h
    exact .bvar h
  | cmp op a b =>
    simp [checkWellTypedBoolExpr, Bool.and_eq_true] at h
    exact .cmp (checkExprTy_sound h.1) (checkExprTy_sound h.2)
  | not e ih =>
    simp [checkWellTypedBoolExpr] at h; exact .not (ih h)
  | fcmp op a b =>
    simp [checkWellTypedBoolExpr, Bool.and_eq_true] at h
    exact .fcmp (checkExprTy_sound h.1) (checkExprTy_sound h.2)
  | bexpr e =>
    simp [checkWellTypedBoolExpr] at h
    exact .bexpr (checkExprTy_sound h)

theorem checkWellTypedInstr_sound {Γ : TyCtx} {decls : List (ArrayName × Nat × VarTy)} {instr : TAC}
    (h : checkWellTypedInstr Γ decls instr = true) : WellTypedInstr Γ decls instr := by
  cases instr with
  | const x v =>
    simp only [checkWellTypedInstr, decide_eq_true_eq] at h
    exact .const h
  | copy x y =>
    simp [checkWellTypedInstr, decide_eq_true_eq] at h; exact .copy h
  | binop x op y z =>
    simp [checkWellTypedInstr, Bool.and_eq_true, decide_eq_true_eq] at h
    exact .binop h.1.1 h.1.2 h.2
  | boolop x be =>
    simp [checkWellTypedInstr, Bool.and_eq_true, decide_eq_true_eq] at h
    exact .boolop h.1 (checkWellTypedBoolExpr_sound h.2)
  | goto l => exact .goto
  | ifgoto b l =>
    simp [checkWellTypedInstr] at h
    exact .ifgoto (checkWellTypedBoolExpr_sound h)
  | halt => exact .halt
  | arrLoad x arr idx ty =>
    simp [checkWellTypedInstr, Bool.and_eq_true, decide_eq_true_eq] at h
    exact .arrLoad h.1.1 h.1.2 h.2
  | arrStore arr idx val ty =>
    simp [checkWellTypedInstr, Bool.and_eq_true, decide_eq_true_eq] at h
    exact .arrStore h.1.1 h.1.2 h.2
  | fbinop x fop y z =>
    simp [checkWellTypedInstr, Bool.and_eq_true, decide_eq_true_eq] at h
    exact .fbinop h.1.1 h.1.2 h.2
  | intToFloat x y =>
    simp [checkWellTypedInstr, Bool.and_eq_true, decide_eq_true_eq] at h
    exact .intToFloat h.1 h.2
  | floatToInt x y =>
    simp [checkWellTypedInstr, Bool.and_eq_true, decide_eq_true_eq] at h
    exact .floatToInt h.1 h.2
  | floatUnary x _ y =>
    simp [checkWellTypedInstr, Bool.and_eq_true, decide_eq_true_eq] at h
    exact .floatUnary h.1 h.2
  | fternop x _ a b c =>
    simp [checkWellTypedInstr, Bool.and_eq_true, decide_eq_true_eq] at h
    exact .fternop h.1.1.1 h.1.1.2 h.1.2 h.2
  | print _ _ =>
    exact .print
  | printInt v =>
    simp only [checkWellTypedInstr, decide_eq_true_eq] at h
    exact .printInt h
  | printBool v =>
    simp only [checkWellTypedInstr, Bool.or_eq_true, decide_eq_true_eq] at h
    exact .printBool (h.imp id id)
  | printFloat v =>
    simp only [checkWellTypedInstr, decide_eq_true_eq] at h
    exact .printFloat h
  | printString _ =>
    exact .printString

theorem checkExprTy_complete {Γ : TyCtx} {e : Expr} {ty : VarTy}
    (h : ExprHasTy Γ e ty) : checkExprTy Γ e ty = true := by
  cases e <;> cases ty <;> simp_all [checkExprTy, ExprHasTy]

theorem checkWellTypedBoolExpr_complete {Γ : TyCtx} {b : BoolExpr}
    (h : WellTypedBoolExpr Γ b) : checkWellTypedBoolExpr Γ b = true := by
  induction h with
  | lit => rfl
  | bvar h => simp [checkWellTypedBoolExpr, h]
  | cmp ha hb => simp [checkWellTypedBoolExpr, checkExprTy_complete ha, checkExprTy_complete hb]
  | not _ ih => simp [checkWellTypedBoolExpr, ih]
  | fcmp ha hb => simp [checkWellTypedBoolExpr, checkExprTy_complete ha, checkExprTy_complete hb]
  | bexpr he => simp [checkWellTypedBoolExpr, checkExprTy_complete he]

theorem checkWellTypedInstr_complete {Γ : TyCtx} {decls : List (ArrayName × Nat × VarTy)} {instr : TAC}
    (h : WellTypedInstr Γ decls instr) : checkWellTypedInstr Γ decls instr = true := by
  cases h with
  | const h => simp [checkWellTypedInstr, h]
  | copy h => simp [checkWellTypedInstr, h]
  | binop hx hy hz => simp [checkWellTypedInstr, hx, hy, hz]
  | boolop hx hbe => simp [checkWellTypedInstr, hx, checkWellTypedBoolExpr_complete hbe]
  | goto => rfl
  | ifgoto hb => simp [checkWellTypedInstr, checkWellTypedBoolExpr_complete hb]
  | halt => rfl
  | arrLoad hx hi hty => simp [checkWellTypedInstr, hx, hi, hty]
  | arrStore hi hv hty => simp [checkWellTypedInstr, hi, hv, hty]
  | fbinop hx hy hz => simp [checkWellTypedInstr, hx, hy, hz]
  | intToFloat hx hy => simp [checkWellTypedInstr, hx, hy]
  | floatToInt hx hy => simp [checkWellTypedInstr, hx, hy]
  | floatUnary hx hy => simp [checkWellTypedInstr, hx, hy]
  | fternop hx ha hb hc => simp [checkWellTypedInstr, hx, ha, hb, hc]
  | print => rfl
  | printInt h => simp [checkWellTypedInstr, h]
  | printBool h => rcases h with h | h <;> simp [checkWellTypedInstr, h]
  | printFloat h => simp [checkWellTypedInstr, h]
  | printString => rfl

/-- Check that every instruction in a program is well-typed. -/
def checkWellTypedProg (Γ : TyCtx) (p : Prog) : Bool :=
  (List.range p.size).all fun i =>
    match p[i]? with
    | some instr => checkWellTypedInstr Γ p.arrayDecls instr
    | none => true

theorem checkWellTypedProg_sound {Γ : TyCtx} {p : Prog}
    (h : checkWellTypedProg Γ p = true) : WellTypedProg Γ p := by
  intro i hi
  have hmem : i ∈ List.range p.size := List.mem_range.mpr hi
  have hcheck := (List.all_eq_true.mp h) i hmem
  have hsome : p[i]? = some p[i] := Prog.getElem?_eq_getElem hi
  rw [hsome] at hcheck
  exact checkWellTypedInstr_sound hcheck

theorem checkWellTypedProg_complete {Γ : TyCtx} {p : Prog}
    (h : WellTypedProg Γ p) : checkWellTypedProg Γ p = true := by
  show (List.range p.size).all _ = true
  rw [List.all_eq_true]
  intro i hi
  have hpc := List.mem_range.mp hi
  rw [Prog.getElem?_eq_getElem hpc]
  exact checkWellTypedInstr_complete (h i hpc)

-- ============================================================
-- § 11a. Type preservation
-- ============================================================

/-- **Type preservation**: a well-typed program with a well-typed store
    preserves the typed-store invariant after any step to a run config. -/
theorem type_preservation {Γ : TyCtx} {p : Prog} {pc pc' : Nat} {σ σ' : Store} {am am' : ArrayMem}
    (hwtp : WellTypedProg Γ p) (hts : TypedStore Γ σ)
    (hpc : pc < p.size)
    (hstep : p ⊩ Cfg.run pc σ am ⟶ Cfg.run pc' σ' am') :
    TypedStore Γ σ' := by
  have hwti := hwtp pc hpc
  cases hstep with
  | const h =>
    have := instr_eq_of_lookup hpc h
    rw [this] at hwti
    match hwti with
    | .const hv => exact TypedStore.update_typed hts hv
  | copy h =>
    have := instr_eq_of_lookup hpc h
    rw [this] at hwti
    match hwti with
    | .copy hxy => exact TypedStore.update_typed hts (by rw [hts]; exact hxy.symm)
  | binop h _ _ _ =>
    have := instr_eq_of_lookup hpc h
    rw [this] at hwti
    match hwti with
    | .binop hx _ _ => exact TypedStore.update_typed hts (by simp [Value.typeOf]; exact hx.symm)
  | boolop h =>
    have := instr_eq_of_lookup hpc h
    rw [this] at hwti
    match hwti with
    | .boolop hx _ => exact TypedStore.update_typed hts (by simp [Value.typeOf]; exact hx.symm)
  | goto _ => exact hts
  | iftrue _ _ => exact hts
  | iffall _ _ => exact hts
  | arrLoad h _ _ =>
    have := instr_eq_of_lookup hpc h
    rw [this] at hwti
    match hwti with
    | .arrLoad hx _ _ => exact TypedStore.update_typed hts (by simp [Value.typeOf_ofBitVec]; exact hx.symm)
  | arrStore _ _ _ _ => exact hts
  | fbinop h _ _ =>
    have := instr_eq_of_lookup hpc h
    rw [this] at hwti
    match hwti with
    | .fbinop hx _ _ => exact TypedStore.update_typed hts (by simp [Value.typeOf]; exact hx.symm)
  | intToFloat h _ =>
    have := instr_eq_of_lookup hpc h
    rw [this] at hwti
    match hwti with
    | .intToFloat hx _ => exact TypedStore.update_typed hts (by simp [Value.typeOf]; exact hx.symm)
  | floatToInt h _ =>
    have := instr_eq_of_lookup hpc h
    rw [this] at hwti
    match hwti with
    | .floatToInt hx _ => exact TypedStore.update_typed hts (by simp [Value.typeOf]; exact hx.symm)
  | floatUnary h _ =>
    have := instr_eq_of_lookup hpc h
    rw [this] at hwti
    match hwti with
    | .floatUnary hx _ => exact TypedStore.update_typed hts (by simp [Value.typeOf]; exact hx.symm)
  | fternop h _ _ _ =>
    have := instr_eq_of_lookup hpc h
    rw [this] at hwti
    match hwti with
    | .fternop hx _ _ _ => exact TypedStore.update_typed hts (by simp [Value.typeOf]; exact hx.symm)
  | print _ => exact hts
  | printInt _ => exact hts
  | printBool _ => exact hts
  | printFloat _ => exact hts
  | printString _ => exact hts


/-- **Type safety (multi-step)**: a well-typed, step-closed program never
    reaches a type-error configuration from a well-typed initial store. -/
theorem type_safety {p : Prog} {σ₀ σ' : Store} {am₀ am' : ArrayMem} {Γ : TyCtx}
    (hwtp : WellTypedProg Γ p) (hts₀ : TypedStore Γ σ₀)
    (hclosed : StepClosedInBounds p) :
    ¬ (p ⊩ Cfg.run 0 σ₀ am₀ ⟶* Cfg.typeError σ' am') := by
  intro hsteps
  suffices ∀ c c', Steps p c c' →
      ∀ pc σ am, c = Cfg.run pc σ am → c' = Cfg.typeError σ' am' →
      pc < p.size → TypedStore Γ σ → False from
    this _ _ hsteps 0 σ₀ am₀ rfl rfl hclosed.1 hts₀
  intro c c' hss
  induction hss with
  | refl => intro _ _ _ hc hc' _ _; rw [hc] at hc'; exact Cfg.noConfusion hc'
  | step hstep rest ih =>
    intro pc σ am hc hc' hpc hts; subst hc
    cases hstep with
    | halt h => cases rest with
      | refl => exact Cfg.noConfusion hc'
      | step s _ => exact Step.no_step_from_halt s
    | binop_divByZero h _ _ _ => cases rest with
      | refl => exact Cfg.noConfusion hc'
      | step s _ => exact Step.no_step_from_errorDiv s
    | binop_typeError hinstr hne =>
      cases rest with
      | refl => exact Step.no_typeError_of_wellTyped (am := am) (am' := am) hpc hwtp hts
                  (.binop_typeError (am := am) hinstr hne)
      | step s _ => exact Step.no_step_from_typeError s
    | const h =>
      exact ih _ _ am rfl hc'
        (hclosed.2 pc _ σ _ am am hpc (Step.const (am := am) h))
        (type_preservation (am := am) (am' := am) hwtp hts hpc (Step.const (am := am) h))
    | copy h =>
      exact ih _ _ am rfl hc'
        (hclosed.2 pc _ σ _ am am hpc (Step.copy (am := am) h))
        (type_preservation (am := am) (am' := am) hwtp hts hpc (Step.copy (am := am) h))
    | binop h hy hz hs =>
      exact ih _ _ am rfl hc'
        (hclosed.2 pc _ σ _ am am hpc (Step.binop (am := am) h hy hz hs))
        (type_preservation (am := am) (am' := am) hwtp hts hpc (Step.binop (am := am) h hy hz hs))
    | boolop h =>
      exact ih _ _ am rfl hc'
        (hclosed.2 pc _ σ _ am am hpc (Step.boolop (am := am) h))
        (type_preservation (am := am) (am' := am) hwtp hts hpc (Step.boolop (am := am) h))
    | goto h =>
      exact ih _ _ am rfl hc'
        (hclosed.2 pc _ σ _ am am hpc (Step.goto (am := am) h))
        (type_preservation (am := am) (am' := am) hwtp hts hpc (Step.goto (am := am) h))
    | iftrue h hne =>
      exact ih _ _ am rfl hc'
        (hclosed.2 pc _ σ _ am am hpc (Step.iftrue (am := am) h hne))
        (type_preservation (am := am) (am' := am) hwtp hts hpc (Step.iftrue (am := am) h hne))
    | iffall h heq =>
      exact ih _ _ am rfl hc'
        (hclosed.2 pc _ σ _ am am hpc (Step.iffall (am := am) h heq))
        (type_preservation (am := am) (am' := am) hwtp hts hpc (Step.iffall (am := am) h heq))
    | arrLoad h hidx hb =>
      exact ih _ _ am rfl hc'
        (hclosed.2 pc _ σ _ am am hpc (Step.arrLoad (am := am) h hidx hb))
        (type_preservation (am := am) (am' := am) hwtp hts hpc (Step.arrLoad (am := am) h hidx hb))
    | arrStore h hidx hty hb =>
      exact ih _ _ _ rfl hc'
        (hclosed.2 pc _ σ _ am _ hpc (Step.arrStore (am := am) h hidx hty hb))
        (type_preservation (am := am) hwtp hts hpc (Step.arrStore (am := am) h hidx hty hb))
    | arrLoad_boundsError _ _ _ => cases rest with
      | refl => exact Cfg.noConfusion hc'
      | step s _ => exact Step.no_step_from_errorBounds s
    | arrStore_boundsError _ _ _ _ => cases rest with
      | refl => exact Cfg.noConfusion hc'
      | step s _ => exact Step.no_step_from_errorBounds s
    | arrLoad_typeError hinstr hne =>
      cases rest with
      | refl => exact Step.no_typeError_of_wellTyped (am := am) (am' := am) hpc hwtp hts
                  (.arrLoad_typeError (am := am) hinstr hne)
      | step s _ => exact Step.no_step_from_typeError s
    | arrStore_typeError hinstr hne =>
      cases rest with
      | refl => exact Step.no_typeError_of_wellTyped (am := am) (am' := am) hpc hwtp hts
                  (.arrStore_typeError (am := am) hinstr hne)
      | step s _ => exact Step.no_step_from_typeError s
    | fbinop h hy hz =>
      exact ih _ _ am rfl hc'
        (hclosed.2 pc _ σ _ am am hpc (Step.fbinop (am := am) h hy hz))
        (type_preservation (am := am) (am' := am) hwtp hts hpc (Step.fbinop (am := am) h hy hz))
    | fbinop_typeError hinstr hne =>
      cases rest with
      | refl => exact Step.no_typeError_of_wellTyped (am := am) (am' := am) hpc hwtp hts
                  (.fbinop_typeError (am := am) hinstr hne)
      | step s _ => exact Step.no_step_from_typeError s
    | intToFloat h hy =>
      exact ih _ _ am rfl hc'
        (hclosed.2 pc _ σ _ am am hpc (Step.intToFloat (am := am) h hy))
        (type_preservation (am := am) (am' := am) hwtp hts hpc (Step.intToFloat (am := am) h hy))
    | intToFloat_typeError hinstr hne =>
      cases rest with
      | refl => exact Step.no_typeError_of_wellTyped (am := am) (am' := am) hpc hwtp hts
                  (.intToFloat_typeError (am := am) hinstr hne)
      | step s _ => exact Step.no_step_from_typeError s
    | floatToInt h hy =>
      exact ih _ _ am rfl hc'
        (hclosed.2 pc _ σ _ am am hpc (Step.floatToInt (am := am) h hy))
        (type_preservation (am := am) (am' := am) hwtp hts hpc (Step.floatToInt (am := am) h hy))
    | floatToInt_typeError hinstr hne =>
      cases rest with
      | refl => exact Step.no_typeError_of_wellTyped (am := am) (am' := am) hpc hwtp hts
                  (.floatToInt_typeError (am := am) hinstr hne)
      | step s _ => exact Step.no_step_from_typeError s
    | floatUnary h hy =>
      exact ih _ _ am rfl hc'
        (hclosed.2 pc _ σ _ am am hpc (Step.floatUnary (am := am) h hy))
        (type_preservation (am := am) (am' := am) hwtp hts hpc (Step.floatUnary (am := am) h hy))
    | floatUnary_typeError hinstr hne =>
      cases rest with
      | refl => exact Step.no_typeError_of_wellTyped (am := am) (am' := am) hpc hwtp hts
                  (.floatUnary_typeError (am := am) hinstr hne)
      | step s _ => exact Step.no_step_from_typeError s
    | fternop h ha hb hc =>
      exact ih _ _ am rfl hc'
        (hclosed.2 pc _ σ _ am am hpc (Step.fternop (am := am) h ha hb hc))
        (type_preservation (am := am) (am' := am) hwtp hts hpc (Step.fternop (am := am) h ha hb hc))
    | fternop_typeError hinstr hne =>
      cases rest with
      | refl => exact Step.no_typeError_of_wellTyped (am := am) (am' := am) hpc hwtp hts
                  (.fternop_typeError (am := am) hinstr hne)
      | step s _ => exact Step.no_step_from_typeError s
    | print h =>
      exact ih _ _ am rfl hc'
        (hclosed.2 pc _ σ _ am am hpc (Step.print (am := am) h))
        (type_preservation (am := am) (am' := am) hwtp hts hpc (Step.print (am := am) h))
    | printInt h =>
      exact ih _ _ am rfl hc'
        (hclosed.2 pc _ σ _ am am hpc (Step.printInt (am := am) h))
        (type_preservation (am := am) (am' := am) hwtp hts hpc (Step.printInt (am := am) h))
    | printBool h =>
      exact ih _ _ am rfl hc'
        (hclosed.2 pc _ σ _ am am hpc (Step.printBool (am := am) h))
        (type_preservation (am := am) (am' := am) hwtp hts hpc (Step.printBool (am := am) h))
    | printFloat h =>
      exact ih _ _ am rfl hc'
        (hclosed.2 pc _ σ _ am am hpc (Step.printFloat (am := am) h))
        (type_preservation (am := am) (am' := am) hwtp hts hpc (Step.printFloat (am := am) h))
    | printString h =>
      exact ih _ _ am rfl hc'
        (hclosed.2 pc _ σ _ am am hpc (Step.printString (am := am) h))
        (type_preservation (am := am) (am' := am) hwtp hts hpc (Step.printString (am := am) h))
