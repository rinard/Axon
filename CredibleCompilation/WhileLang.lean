-- Copyright (c) 2026 Martin Rinard
import CredibleCompilation.Semantics
import CredibleCompilation.PropChecker

/-!
# While Language — Source Language and Compiler to TAC

A simple structured imperative language with while loops, if/else,
assignment, and sequencing. Variables are typed: integer or boolean.

The compiler translates source programs to TAC (three-address code)
programs suitable for optimization and certificate checking.

## Design note

The compiler is **not verified** — this is intentional. The credible
compilation framework means we don't need to trust the compiler: the
certificate checker verifies that any subsequent optimization preserves
TAC-level semantics. The source language serves as a convenient front-end
for writing programs.

The `RefCompiler/` module provides correctness proofs for the compiler
(refinement, error handling, divergence) with no proof gaps.
-/

-- ============================================================
-- § 1. Source language AST
-- ============================================================

/-- Arithmetic expressions (tree-structured, unlike TAC operands). -/
inductive SExpr where
  | lit     : Int → SExpr
  | var     : Var → SExpr
  | bin     : BinOp → SExpr → SExpr → SExpr
  | arrRead : ArrayName → SExpr → SExpr          -- arr[idx]
  | flit       : Float → SExpr                      -- float literal
  | fbin       : FloatBinOp → SExpr → SExpr → SExpr -- float binary op
  | intToFloat : SExpr → SExpr                      -- int→float cast
  | floatToInt : SExpr → SExpr                      -- float→int cast
  | floatUnary : FloatUnaryOp → SExpr → SExpr        -- exp/sqrt(x) (float)
  | farrRead   : ArrayName → SExpr → SExpr          -- float arr[idx]
  deriving Repr

/-- Boolean expressions over arithmetic sub-expressions. -/
inductive SBool where
  | lit  : Bool → SBool                          -- true / false literal
  | bvar : Var → SBool                           -- read a boolean variable
  | cmp  : CmpOp → SExpr → SExpr → SBool
  | not  : SBool → SBool
  | and      : SBool → SBool → SBool
  | or       : SBool → SBool → SBool
  | barrRead : ArrayName → SExpr → SBool        -- arr[idx] (boolean array read)
  | fcmp : FloatCmpOp → SExpr → SExpr → SBool   -- float comparison
  deriving Repr

/-- Statements. -/
inductive Stmt where
  | skip     : Stmt
  | assign   : Var → SExpr → Stmt               -- integer assignment
  | bassign  : Var → SBool → Stmt               -- boolean assignment
  | arrWrite  : ArrayName → SExpr → SExpr → Stmt  -- arr[idx] := val (int)
  | barrWrite : ArrayName → SExpr → SBool → Stmt  -- arr[idx] := bval (bool)
  | seq      : Stmt → Stmt → Stmt
  | ite      : SBool → Stmt → Stmt → Stmt       -- if-then-else
  | loop     : SBool → Stmt → Stmt
  | fassign   : Var → SExpr → Stmt               -- float assignment
  | farrWrite : ArrayName → SExpr → SExpr → Stmt  -- float arr[idx] := val
  | label    : String → Stmt                      -- label declaration (goto target)
  | goto     : String → Stmt                      -- unconditional jump
  | ifgoto   : SBool → String → Stmt             -- conditional jump
  | print      : String → List SExpr → Stmt        -- print fmt_string [args]
  | printInt    : SExpr → Stmt                     -- printInt(e): bl _printInt with int e in x0
  | printBool   : SBool → Stmt                     -- printBool(b): bl _printBool with bool b in x0
  | printFloat  : SExpr → Stmt                     -- printFloat(e): bl _printFloat with float e in d0
  | printString : String → Stmt                    -- printString("lit"): bl _printString with lit ptr in x0
  deriving Repr

-- Syntactic sugar
infixr:30 " ;; " => Stmt.seq

-- ============================================================
-- § 2. Direct interpretation (for testing / specification)
-- ============================================================

/-- Evaluate an arithmetic expression. Returns BitVec 64; reads integer
    values from the store via `.toInt`. -/
def SExpr.eval (σ : Store) (am : ArrayMem) : SExpr → BitVec 64
  | .lit n      => BitVec.ofInt 64 n
  | .var x      => (σ x).toBits
  | .bin op a b => op.eval (a.eval σ am) (b.eval σ am)
  | .arrRead arr idx => am.read arr (idx.eval σ am)
  | .flit f        => floatToBits f
  | .fbin op a b   => op.eval (a.eval σ am) (b.eval σ am)
  | .intToFloat e  => intToFloatBv (e.eval σ am)
  | .floatToInt e  => floatToIntBv (e.eval σ am)
  | .floatUnary op e => op.eval (e.eval σ am)
  | .farrRead arr idx => am.read arr (idx.eval σ am)

/-- Type-aware expression evaluation: wraps the result in the correct Value constructor.
    For `.var x`, returns `σ x` directly (the actual runtime value). -/
def SExpr.wrapEval (σ : Store) (am : ArrayMem) : SExpr → Value
  | .lit n            => .int (BitVec.ofInt 64 n)
  | .var x            => σ x
  | .bin op a b       => .int (op.eval (a.eval σ am) (b.eval σ am))
  | .arrRead arr idx  => .int (am.read arr (idx.eval σ am))
  | .flit f           => .float (floatToBits f)
  | .fbin op a b      => .float (op.eval (a.eval σ am) (b.eval σ am))
  | .intToFloat e     => .float (intToFloatBv (e.eval σ am))
  | .floatToInt e     => .int (floatToIntBv (e.eval σ am))
  | .floatUnary op e  => .float (op.eval (e.eval σ am))
  | .farrRead arr idx => .float (am.read arr (idx.eval σ am))

/-- Context-sensitive typing: ensures sub-expressions evaluate to the right
    Value type for their parent context. Embeds the `wrapEval = .int/.float (eval)`
    bridge directly so proofs can extract it without a separate lemma. -/
def SExpr.typedVars (σ : Store) (am : ArrayMem) : SExpr → Prop
  | .lit _ | .flit _ => True
  | .var _ => True
  | .bin _ a b =>
    a.wrapEval σ am = .int (a.eval σ am) ∧
    b.wrapEval σ am = .int (b.eval σ am) ∧
    a.typedVars σ am ∧ b.typedVars σ am
  | .arrRead _ idx =>
    idx.wrapEval σ am = .int (idx.eval σ am) ∧ idx.typedVars σ am
  | .fbin _ a b =>
    a.wrapEval σ am = .float (a.eval σ am) ∧
    b.wrapEval σ am = .float (b.eval σ am) ∧
    a.typedVars σ am ∧ b.typedVars σ am
  | .intToFloat e =>
    e.wrapEval σ am = .int (e.eval σ am) ∧ e.typedVars σ am
  | .floatToInt e =>
    e.wrapEval σ am = .float (e.eval σ am) ∧ e.typedVars σ am
  | .floatUnary _ e =>
    e.wrapEval σ am = .float (e.eval σ am) ∧ e.typedVars σ am
  | .farrRead _ idx =>
    idx.wrapEval σ am = .int (idx.eval σ am) ∧ idx.typedVars σ am

/-- Context-sensitive typing for boolean expressions. -/
def SBool.typedVars (σ : Store) (am : ArrayMem) : SBool → Prop
  | .lit _ | .bvar _ => True
  | .cmp _ a b => a.typedVars σ am ∧ b.typedVars σ am ∧
                  a.wrapEval σ am = .int (a.eval σ am) ∧ b.wrapEval σ am = .int (b.eval σ am)
  | .not e => e.typedVars σ am
  | .and a b => a.typedVars σ am ∧ b.typedVars σ am
  | .or a b => a.typedVars σ am ∧ b.typedVars σ am
  | .barrRead _ idx => idx.typedVars σ am ∧ idx.wrapEval σ am = .int (idx.eval σ am)
  | .fcmp _ a b => a.typedVars σ am ∧ b.typedVars σ am ∧
                   a.wrapEval σ am = .float (a.eval σ am) ∧ b.wrapEval σ am = .float (b.eval σ am)

/-- Evaluate a boolean expression. -/
def SBool.eval (σ : Store) (am : ArrayMem) : SBool → Bool
  | .lit b      => b
  | .bvar x     => (σ x).toBool
  | .cmp op a b => op.eval (a.eval σ am) (b.eval σ am)
  | .not e      => !e.eval σ am
  | .and a b    => a.eval σ am && b.eval σ am
  | .or a b        => a.eval σ am || b.eval σ am
  | .barrRead arr idx => (am.read arr (idx.eval σ am)) != 0
  | .fcmp op a b => FloatCmpOp.eval op (a.eval σ am) (b.eval σ am)

/-- Check whether an arithmetic expression is safe to evaluate (no div-by-zero,
    array accesses in bounds). Returns `Bool` for use in `Stmt.interp`. -/
def SExpr.isSafe (σ : Store) (am : ArrayMem) (decls : List (ArrayName × Nat × VarTy)) : SExpr → Bool
  | .lit _ => true
  | .var _ => true
  | .bin .div a b => a.isSafe σ am decls && b.isSafe σ am decls && decide (b.eval σ am ≠ 0)
  | .bin .mod a b => a.isSafe σ am decls && b.isSafe σ am decls && decide (b.eval σ am ≠ 0)
  | .bin _ a b => a.isSafe σ am decls && b.isSafe σ am decls
  | .arrRead arr idx => idx.isSafe σ am decls && decide ((idx.eval σ am) < arraySizeBv decls arr)
  | .flit _ => true
  | .fbin _ a b => a.isSafe σ am decls && b.isSafe σ am decls
  | .intToFloat e => e.isSafe σ am decls
  | .floatToInt e => e.isSafe σ am decls
  | .floatUnary _ e => e.isSafe σ am decls
  | .farrRead arr idx => idx.isSafe σ am decls && decide ((idx.eval σ am) < arraySizeBv decls arr)

/-- Check whether a boolean expression is safe to evaluate. -/
def SBool.isSafe (σ : Store) (am : ArrayMem) (decls : List (ArrayName × Nat × VarTy)) : SBool → Bool
  | .lit _ => true
  | .bvar _ => true
  | .cmp _ a b => a.isSafe σ am decls && b.isSafe σ am decls
  | .not e => e.isSafe σ am decls
  | .and a b => a.isSafe σ am decls && (if a.eval σ am then b.isSafe σ am decls else true)
  | .or a b => a.isSafe σ am decls && (if !(a.eval σ am) then b.isSafe σ am decls else true)
  | .barrRead arr idx => idx.isSafe σ am decls && decide ((idx.eval σ am) < arraySizeBv decls arr)
  | .fcmp _ a b => a.isSafe σ am decls && b.isSafe σ am decls

/-- Interpret a statement directly, with a fuel bound to ensure termination.
    Returns `none` if out of fuel or if a safety check fails (div-by-zero, array out-of-bounds). -/
def Stmt.interp (fuel : Nat) (σ : Store) (am : ArrayMem)
    (decls : List (ArrayName × Nat × VarTy)) : Stmt → Option (Store × ArrayMem)
  | .skip        => some (σ, am)
  | .assign x e  =>
    if e.isSafe σ am decls then some (σ[x ↦ .int (e.eval σ am)], am) else none
  | .bassign x b =>
    if b.isSafe σ am decls then some (σ[x ↦ .bool (b.eval σ am)], am) else none
  | .arrWrite arr idx val =>
    if idx.isSafe σ am decls && val.isSafe σ am decls &&
       decide ((idx.eval σ am) < arraySizeBv decls arr)
    then some (σ, am.write arr (idx.eval σ am) (val.eval σ am))
    else none
  | .barrWrite arr idx bval =>
    if (idx : SExpr).isSafe σ am decls && bval.isSafe σ am decls &&
       decide ((idx.eval σ am) < arraySizeBv decls arr)
    then let b := bval.eval σ am
         let v : BitVec 64 := if b then 1 else 0
         some (σ, am.write arr (idx.eval σ am) v)
    else none
  | .seq s1 s2   => do
    let (σ', am') ← s1.interp fuel σ am decls
    s2.interp fuel σ' am' decls
  | .ite b s1 s2 =>
    if b.isSafe σ am decls then
      if b.eval σ am then s1.interp fuel σ am decls else s2.interp fuel σ am decls
    else none
  | .loop b body =>
    match fuel with
    | 0 => none  -- out of fuel
    | fuel' + 1 =>
      if b.isSafe σ am decls then
        if b.eval σ am then do
          let (σ', am') ← body.interp fuel' σ am decls
          (Stmt.loop b body).interp fuel' σ' am' decls
        else some (σ, am)
      else none
  | .fassign x e =>
    if e.isSafe σ am decls then some (σ[x ↦ .float (e.eval σ am)], am) else none
  | .farrWrite arr idx val =>
    if idx.isSafe σ am decls && val.isSafe σ am decls &&
       decide ((idx.eval σ am) < arraySizeBv decls arr)
    then some (σ, am.write arr (idx.eval σ am) (val.eval σ am))
    else none
  | .label _ => some (σ, am)  -- no-op: label declarations are compilation markers
  | .goto _ => some (σ, am)   -- no-op at statement level; goto resolved at compilation
  | .ifgoto b _ =>
    if b.isSafe σ am decls then some (σ, am) else none
  | .print _ args =>
    if args.all (·.isSafe σ am decls) then some (σ, am) else none
  | .printInt e =>
    if e.isSafe σ am decls then some (σ, am) else none
  | .printBool b =>
    if b.isSafe σ am decls then some (σ, am) else none
  | .printFloat e =>
    if e.isSafe σ am decls then some (σ, am) else none
  | .printString _ => some (σ, am)

-- ============================================================
-- § 3. Compiler: While language → TAC (pure functional)
-- ============================================================

/-- Temporary variable name from index. -/
def tmpName (k : Nat) : Var := s!"__t{k}"

/-- A variable is a temporary iff its name starts with `__t`.
    Defined on `String` so dot notation works (since `Var` is `abbrev String`). -/
def String.isTmp (v : String) : Bool :=
  match v.toList with
  | '_' :: '_' :: 't' :: _ => true
  | _ => false

/-- Float temporary variable name from index. -/
def ftmpName (k : Nat) : Var := s!"__ft{k}"

/-- A variable is a float temporary iff its name starts with `__ft`. -/
def String.isFTmp (v : String) : Bool :=
  match v.toList with
  | '_' :: '_' :: 'f' :: 't' :: _ => true
  | _ => false

/-- Bool temporary variable name from index. -/
def btmpName (k : Nat) : Var := s!"__bt{k}"

/-- A variable is a bool temporary iff its name starts with `__bt`. -/
def String.isBTmp (v : String) : Bool :=
  match v.toList with
  | '_' :: '_' :: 'b' :: 't' :: _ => true
  | _ => false

/-- Compile an arithmetic expression. Returns (code, result variable, next temp index).
    Pre-computes code lengths so no patching is needed. -/
def compileExpr (e : SExpr) (offset nextTmp : Nat) : List TAC × Var × Nat :=
  match e with
  | .lit n =>
    let t := tmpName nextTmp
    ([.const t (.int (BitVec.ofInt 64 n))], t, nextTmp + 1)
  | .var x => ([], x, nextTmp)
  | .bin op a b =>
    let (codeA, va, tmp1) := compileExpr a offset nextTmp
    let (codeB, vb, tmp2) := compileExpr b (offset + codeA.length) tmp1
    let t := tmpName tmp2
    (codeA ++ codeB ++ [.binop t op va vb], t, tmp2 + 1)
  | .arrRead arr idx =>
    let (codeIdx, vIdx, tmp1) := compileExpr idx offset nextTmp
    let t := tmpName tmp1
    (codeIdx ++ [.arrLoad t arr vIdx .int], t, tmp1 + 1)
  | .flit f =>
    let t := ftmpName nextTmp
    ([.const t (.float (floatToBits f))], t, nextTmp + 1)
  | .fbin op a b =>
    let (codeA, va, tmp1) := compileExpr a offset nextTmp
    let (codeB, vb, tmp2) := compileExpr b (offset + codeA.length) tmp1
    let t := ftmpName tmp2
    (codeA ++ codeB ++ [.fbinop t op va vb], t, tmp2 + 1)
  | .intToFloat e =>
    let (codeE, ve, tmp1) := compileExpr e offset nextTmp
    let t := ftmpName tmp1
    (codeE ++ [.intToFloat t ve], t, tmp1 + 1)
  | .floatToInt e =>
    let (codeE, ve, tmp1) := compileExpr e offset nextTmp
    let t := tmpName tmp1
    (codeE ++ [.floatToInt t ve], t, tmp1 + 1)
  | .floatUnary op e =>
    let (codeE, ve, tmp1) := compileExpr e offset nextTmp
    let t := ftmpName tmp1
    (codeE ++ [.floatUnary t op ve], t, tmp1 + 1)
  | .farrRead arr idx =>
    let (codeIdx, vIdx, tmp1) := compileExpr idx offset nextTmp
    let t := ftmpName tmp1
    (codeIdx ++ [.arrLoad t arr vIdx .float], t, tmp1 + 1)

/-- Compile a boolean expression. Returns (code, BoolExpr, next temp index). -/
def compileBool (b : SBool) (offset nextTmp : Nat) : List TAC × BoolExpr × Nat :=
  match b with
  | .lit b => ([], .lit b, nextTmp)
  | .bvar x => ([], .bvar x, nextTmp)
  | .cmp op a b =>
    let (codeA, va, tmp1) := compileExpr a offset nextTmp
    let (codeB, vb, tmp2) := compileExpr b (offset + codeA.length) tmp1
    (codeA ++ codeB, .cmp op (.var va) (.var vb), tmp2)
  | .not e =>
    let (code, be, tmp') := compileBool e offset nextTmp
    (code, .not be, tmp')
  | .and a b =>
    -- Flatten a && b: if !a goto false; if !b goto false; tR := 1; goto end; false: tR := 0; end:
    let (codeA, ba, tmp1) := compileBool a offset nextTmp
    let tR := tmpName tmp1
    let (codeB, bb, tmp2) := compileBool b (offset + codeA.length + 1) (tmp1 + 1)
    -- Layout:
    --   codeA                        -- evaluate a's subexpressions
    --   ifgoto (not ba) falseL       -- if !a goto false
    --   codeB                        -- evaluate b's subexpressions
    --   ifgoto (not bb) falseL       -- if !b goto false
    --   const tR (.int 1)            -- both true → tR = 1
    --   goto endL
    --   falseL: const tR (.int 0)    -- at least one false → tR = 0
    --   endL: ...
    let afterCodeB := offset + codeA.length + 1 + codeB.length
    let falseL := afterCodeB + 3  -- after ifgoto + const + goto
    let endL := falseL + 1
    let code := codeA ++
      [TAC.ifgoto (.not ba) falseL] ++
      codeB ++
      [TAC.ifgoto (.not bb) falseL,
       TAC.const tR (.int (1 : BitVec 64)),
       TAC.goto endL,
       TAC.const tR (.int (0 : BitVec 64))]
    (code, .cmp .ne (.var tR) (.lit 0), tmp2)
  | .or a b =>
    -- Flatten a || b: if a goto true; if b goto true; tR := 0; goto end; true: tR := 1; end:
    let (codeA, ba, tmp1) := compileBool a offset nextTmp
    let tR := tmpName tmp1
    let (codeB, bb, tmp2) := compileBool b (offset + codeA.length + 1) (tmp1 + 1)
    let afterCodeB := offset + codeA.length + 1 + codeB.length
    let trueL := afterCodeB + 3
    let endL := trueL + 1
    let code := codeA ++
      [TAC.ifgoto ba trueL] ++
      codeB ++
      [TAC.ifgoto bb trueL,
       TAC.const tR (.int (0 : BitVec 64)),
       TAC.goto endL,
       TAC.const tR (.int (1 : BitVec 64))]
    (code, .cmp .ne (.var tR) (.lit 0), tmp2)
  | .barrRead arr idx =>
    let (codeIdx, vIdx, tmp1) := compileExpr idx offset nextTmp
    let t := btmpName tmp1
    (codeIdx ++ [.arrLoad t arr vIdx .bool], .bvar t, tmp1 + 1)
  | .fcmp op a b =>
    let (codeA, va, tmp1) := compileExpr a offset nextTmp
    let (codeB, vb, tmp2) := compileExpr b (offset + codeA.length) tmp1
    (codeA ++ codeB, .fcmp op (.var va) (.var vb), tmp2)

/-- The BoolExpr returned by `compileBool` always has simple ops. -/
theorem compileBool_hasSimpleOps (b : SBool) (offset nextTmp : Nat) :
    (compileBool b offset nextTmp).2.1.hasSimpleOps = true := by
  induction b with
  | lit => simp [compileBool, BoolExpr.hasSimpleOps]
  | bvar => simp [compileBool, BoolExpr.hasSimpleOps]
  | cmp => simp [compileBool, BoolExpr.hasSimpleOps]
  | not e ih => simp [compileBool, BoolExpr.hasSimpleOps, ih]
  | and a b iha ihb =>
    simp [compileBool, BoolExpr.hasSimpleOps]
  | or a b iha ihb =>
    simp [compileBool, BoolExpr.hasSimpleOps]
  | barrRead => simp [compileBool, BoolExpr.hasSimpleOps]
  | fcmp => simp [compileBool, BoolExpr.hasSimpleOps]

/-- `compileExpr` never produces `boolop` or `ifgoto` instructions. -/
theorem compileExpr_code_simpleOps (e : SExpr) (offset nextTmp : Nat) :
    (compileExpr e offset nextTmp).1.all (fun instr =>
      match instr with | .boolop _ _ | .ifgoto _ _ => false | _ => true) = true := by
  induction e generalizing offset nextTmp with
  | lit | flit | var => simp [compileExpr]
  | bin _ a b iha ihb =>
    simp only [compileExpr, List.all_append, Bool.and_eq_true, List.all_cons, List.all_nil,
      Bool.true_and, and_true]
    exact ⟨iha _ _, ihb _ _⟩
  | fbin _ a b iha ihb =>
    simp only [compileExpr, List.all_append, Bool.and_eq_true, List.all_cons, List.all_nil,
      Bool.true_and, and_true]
    exact ⟨iha _ _, ihb _ _⟩
  | intToFloat a ih =>
    simp only [compileExpr, List.all_append, Bool.and_eq_true, List.all_cons, List.all_nil,
      Bool.true_and, and_true]
    exact ih _ _
  | floatToInt a ih =>
    simp only [compileExpr, List.all_append, Bool.and_eq_true, List.all_cons, List.all_nil,
      Bool.true_and, and_true]
    exact ih _ _
  | floatUnary _ a ih =>
    simp only [compileExpr, List.all_append, Bool.and_eq_true, List.all_cons, List.all_nil,
      Bool.true_and, and_true]
    exact ih _ _
  | arrRead _ idx ih =>
    simp only [compileExpr, List.all_append, Bool.and_eq_true, List.all_cons, List.all_nil,
      Bool.true_and, and_true]
    exact ih _ _
  | farrRead _ idx ih =>
    simp only [compileExpr, List.all_append, Bool.and_eq_true, List.all_cons, List.all_nil,
      Bool.true_and, and_true]
    exact ih _ _

/-- compileExpr code trivially satisfies instrSimpleOps (no boolop/ifgoto). -/
private theorem compileExpr_simpleOps (e : SExpr) (offset nextTmp : Nat) :
    (compileExpr e offset nextTmp).1.all (fun instr =>
      match instr with | .boolop _ be | .ifgoto be _ => be.hasSimpleOps | _ => true) = true := by
  have h := compileExpr_code_simpleOps e offset nextTmp
  rw [List.all_eq_true] at h ⊢
  intro x hx; have := h x hx; cases x <;> simp_all

/-- All instructions in the code produced by `compileBool` have simple bool ops. -/
theorem compileBool_code_simpleOps (b : SBool) (offset nextTmp : Nat) :
    ∀ instr ∈ (compileBool b offset nextTmp).1,
      match instr with | .boolop _ be | .ifgoto be _ => be.hasSimpleOps = true | _ => True := by
  induction b generalizing offset nextTmp with
  | lit | bvar => simp [compileBool]
  | cmp _ a b =>
    intro instr hmem; unfold compileBool at hmem
    simp only [List.mem_append] at hmem
    rcases hmem with h | h <;>
      (have := List.all_eq_true.mp (compileExpr_simpleOps _ _ _) _ h
       cases instr <;> simp_all)
  | not e ih => intro instr hmem; exact ih _ _ instr (by unfold compileBool at hmem; exact hmem)
  | fcmp _ a b =>
    intro instr hmem; unfold compileBool at hmem
    simp only [List.mem_append] at hmem
    rcases hmem with h | h <;>
      (have := List.all_eq_true.mp (compileExpr_simpleOps _ _ _) _ h
       cases instr <;> simp_all)
  | and a b iha ihb =>
    intro instr hmem; unfold compileBool at hmem
    simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ((h | h) | h) | (h | h | h | h)
    · exact iha _ _ _ h
    · subst h; simp [BoolExpr.hasSimpleOps, compileBool_hasSimpleOps]
    · exact ihb _ _ _ h
    · subst h; simp [BoolExpr.hasSimpleOps, compileBool_hasSimpleOps]
    all_goals (subst h; simp)
  | or a b iha ihb =>
    intro instr hmem; unfold compileBool at hmem
    simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ((h | h) | h) | (h | h | h | h)
    · exact iha _ _ _ h
    · subst h; simp [BoolExpr.hasSimpleOps, compileBool_hasSimpleOps]
    · exact ihb _ _ _ h
    · subst h; simp [BoolExpr.hasSimpleOps, compileBool_hasSimpleOps]
    all_goals (subst h; simp)
  | barrRead _ idx =>
    intro instr hmem; unfold compileBool at hmem
    simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with h | h
    · have := List.all_eq_true.mp (compileExpr_simpleOps idx _ _) _ h
      cases instr <;> simp_all
    · subst h; simp

/-- Compute code length of a compiled expression (offset-independent). -/
def exprCodeLen : SExpr → Nat
  | .lit _ | .flit _ => 1
  | .var _ => 0
  | .bin _ a b | .fbin _ a b => exprCodeLen a + exprCodeLen b + 1
  | .arrRead _ idx | .farrRead _ idx => exprCodeLen idx + 1
  | .intToFloat e | .floatToInt e | .floatUnary _ e => exprCodeLen e + 1

/-- Compute total code length for a list of compiled expressions. -/
def exprsCodeLen : List SExpr → Nat
  | [] => 0
  | e :: rest => exprCodeLen e + exprsCodeLen rest

/-- Compute code length of a compiled boolean expression (offset-independent). -/
def boolCodeLen : SBool → Nat
  | .lit _ | .bvar _ => 0
  | .cmp _ a b => exprCodeLen a + exprCodeLen b
  | .fcmp _ a b => exprCodeLen a + exprCodeLen b
  | .not e => boolCodeLen e
  | .and a b => boolCodeLen a + 1 + boolCodeLen b + 4
  | .or a b => boolCodeLen a + 1 + boolCodeLen b + 4
  | .barrRead _ idx => exprCodeLen idx + 1

/-- Compute code length of a compiled statement (offset- and label-independent). -/
def stmtCodeLen : Stmt → Nat
  | .skip => 0
  | .assign _ e =>
    match e with
    | .lit _ | .var _ => 1
    | .bin _ a b => exprCodeLen a + exprCodeLen b + 1
    | .arrRead _ idx => exprCodeLen idx + 2
    | _ => exprCodeLen e + 1
  | .bassign _ b => boolCodeLen b + 1
  | .arrWrite _ idx val => exprCodeLen idx + exprCodeLen val + 1
  | .barrWrite _ idx bval => exprCodeLen idx + boolCodeLen bval + 2
  | .seq s1 s2 => stmtCodeLen s1 + stmtCodeLen s2
  | .ite b s1 s2 => boolCodeLen b + 1 + stmtCodeLen s2 + 1 + stmtCodeLen s1
  | .loop b body => boolCodeLen b + 1 + stmtCodeLen body + 1
  | .fassign _ e =>
    match e with
    | .flit _ | .var _ => 1
    | .fbin _ a b => exprCodeLen a + exprCodeLen b + 1
    | .intToFloat e | .floatUnary _ e => exprCodeLen e + 1
    | .farrRead _ idx => exprCodeLen idx + 2
    | _ => exprCodeLen e + 1
  | .farrWrite _ idx val => exprCodeLen idx + exprCodeLen val + 1
  | .label _ => 0    -- labels emit no code
  | .goto _ => 1     -- single goto instruction
  | .ifgoto b _ => boolCodeLen b + 1  -- condition code + ifgoto
  | .print _ args => exprsCodeLen args + 1
  | .printInt e => exprCodeLen e + 1
  | .printBool b => boolCodeLen b + 5  -- 4 conv instrs (ifgoto+const+goto+const) + printBool
  | .printFloat e => exprCodeLen e + 1
  | .printString _ => 1

/-- Collect label→PC mappings from a statement, given the starting offset. -/
def collectLabels : Stmt → Nat → List (String × Nat)
  | .label name, offset => [(name, offset)]
  | .seq s1 s2, offset =>
    collectLabels s1 offset ++ collectLabels s2 (offset + stmtCodeLen s1)
  | .ite b s1 s2, offset =>
    let elseStart := offset + boolCodeLen b + 1
    let thenStart := elseStart + stmtCodeLen s2 + 1
    collectLabels s2 elseStart ++ collectLabels s1 thenStart
  | .loop b body, offset =>
    let bodyStart := offset + boolCodeLen b + 1
    collectLabels body bodyStart
  | _, _ => []

/-- Compile a list of expressions (for print arguments).
    Returns (code, vars, next temp index). -/
def compileExprs : List SExpr → Nat → Nat → List TAC × List Var × Nat
  | [], _, nextTmp => ([], [], nextTmp)
  | e :: rest, offset, nextTmp =>
    let (codeE, ve, tmp1) := compileExpr e offset nextTmp
    let (codeRest, vsRest, tmp2) := compileExprs rest (offset + codeE.length) tmp1
    (codeE ++ codeRest, ve :: vsRest, tmp2)

/-- Compile a statement. Returns (code, next temp index).
    Jump targets are pre-computed from code lengths.
    `labels` maps label names to their PCs (for goto/ifgoto). -/
def compileStmt (s : Stmt) (offset nextTmp : Nat)
    (labels : List (String × Nat) := {}) : List TAC × Nat :=
  match s with
  | .skip => ([], nextTmp)
  | .assign x e =>
    match e with
    | .lit n => ([.const x (.int (BitVec.ofInt 64 n))], nextTmp)
    | .var y => ([.copy x y], nextTmp)
    | .bin op a b =>
      let (codeA, va, tmp1) := compileExpr a offset nextTmp
      let (codeB, vb, tmp2) := compileExpr b (offset + codeA.length) tmp1
      (codeA ++ codeB ++ [.binop x op va vb], tmp2)
    | .arrRead arr idx =>
      let (codeIdx, vIdx, tmp1) := compileExpr idx offset nextTmp
      let t := tmpName tmp1
      (codeIdx ++ [.arrLoad t arr vIdx .int, .copy x t], tmp1 + 1)
    | _ =>
      -- Float expressions in int assignment (type error, but handle gracefully)
      let (codeE, ve, tmp1) := compileExpr e offset nextTmp
      (codeE ++ [.copy x ve], tmp1)
  | .bassign x b =>
    let (code, be, tmp') := compileBool b offset nextTmp
    (code ++ [.boolop x be], tmp')
  | .arrWrite arr idx val =>
    let (codeIdx, vIdx, tmp1) := compileExpr idx offset nextTmp
    let (codeVal, vVal, tmp2) := compileExpr val (offset + codeIdx.length) tmp1
    (codeIdx ++ codeVal ++ [.arrStore arr vIdx vVal .int], tmp2)
  | .barrWrite arr idx bval =>
    let (codeIdx, vIdx, tmp1) := compileExpr idx offset nextTmp
    let (codeBool, be, tmp2) := compileBool bval (offset + codeIdx.length) tmp1
    let tBool := btmpName tmp2
    -- Evaluate `be` into bool temp `tBool`, then store directly with .bool element type.
    (codeIdx ++ codeBool ++ [.boolop tBool be, .arrStore arr vIdx tBool .bool], tmp2 + 1)
  | .seq s1 s2 =>
    let (code1, tmp1) := compileStmt s1 offset nextTmp labels
    let (code2, tmp2) := compileStmt s2 (offset + code1.length) tmp1 labels
    (code1 ++ code2, tmp2)
  | .ite b s1 s2 =>
    let (codeB, be, tmpB) := compileBool b offset nextTmp
    -- ifgoto be <then>; <else code>; goto <end>; <then code>
    let elseStart := offset + codeB.length + 1
    let (codeElse, tmpE) := compileStmt s2 elseStart tmpB labels
    let thenStart := elseStart + codeElse.length + 1
    let (codeThen, tmpT) := compileStmt s1 thenStart tmpE labels
    let endLabel := thenStart + codeThen.length
    (codeB ++ [.ifgoto be thenStart] ++ codeElse ++ [.goto endLabel] ++ codeThen, tmpT)
  | .loop b body =>
    let condLabel := offset
    let (codeB, be, tmpB) := compileBool b offset nextTmp
    let bodyStart := offset + codeB.length + 1
    let (codeBody, tmpBody) := compileStmt body bodyStart tmpB labels
    let exitLabel := bodyStart + codeBody.length + 1
    (codeB ++ [.ifgoto (.not be) exitLabel] ++ codeBody ++ [.goto condLabel], tmpBody)
  | .fassign x e =>
    match e with
    | .flit f => ([.const x (.float (floatToBits f))], nextTmp)
    | .var y => ([.copy x y], nextTmp)
    | .fbin op a b =>
      let (codeA, va, tmp1) := compileExpr a offset nextTmp
      let (codeB, vb, tmp2) := compileExpr b (offset + codeA.length) tmp1
      (codeA ++ codeB ++ [.fbinop x op va vb], tmp2)
    | .intToFloat e =>
      let (codeE, ve, tmp1) := compileExpr e offset nextTmp
      (codeE ++ [.intToFloat x ve], tmp1)
    | .floatUnary op e =>
      let (codeE, ve, tmp1) := compileExpr e offset nextTmp
      (codeE ++ [.floatUnary x op ve], tmp1)
    | .farrRead arr idx =>
      let (codeIdx, vIdx, tmp1) := compileExpr idx offset nextTmp
      let t := ftmpName tmp1
      (codeIdx ++ [.arrLoad t arr vIdx .float, .copy x t], tmp1 + 1)
    | _ =>
      -- Fallback: compile expression generically
      let (codeE, ve, tmp1) := compileExpr e offset nextTmp
      (codeE ++ [.copy x ve], tmp1)
  | .farrWrite arr idx val =>
    let (codeIdx, vIdx, tmp1) := compileExpr idx offset nextTmp
    let (codeVal, vVal, tmp2) := compileExpr val (offset + codeIdx.length) tmp1
    (codeIdx ++ codeVal ++ [.arrStore arr vIdx vVal .float], tmp2)
  | .label _ => ([], nextTmp)  -- labels emit no code; PC tracked by collectLabels
  | .goto lbl =>
    let target := (labels.lookup lbl).getD 0
    ([.goto target], nextTmp)
  | .ifgoto b lbl =>
    let (codeB, be, tmpB) := compileBool b offset nextTmp
    let target := (labels.lookup lbl).getD 0
    (codeB ++ [.ifgoto be target], tmpB)
  | .print fmt args =>
    let (allCode, allVars, tmp') := compileExprs args offset nextTmp
    (allCode ++ [.print fmt allVars], tmp')
  | .printInt e =>
    let (codeE, ve, tmp1) := compileExpr e offset nextTmp
    (codeE ++ [.printInt ve], tmp1)
  | .printBool b =>
    -- Materialize the bool expression into an int temp via ifgoto+const sequence,
    -- then call printBool with the int value. Avoids needing a bool temp class.
    -- (printBool's well-typedness now accepts both .bool and .int.)
    let (codeB, be, tmpB) := compileBool b offset nextTmp
    let tInt := tmpName tmpB
    let afterCodeB := offset + codeB.length
    let trueL := afterCodeB + 3  -- ifgoto + const 0 + goto
    let endL := trueL + 1
    let convCode : List TAC :=
      [TAC.ifgoto be trueL,
       TAC.const tInt (.int (0 : BitVec 64)),
       TAC.goto endL,
       TAC.const tInt (.int (1 : BitVec 64))]
    (codeB ++ convCode ++ [.printBool tInt], tmpB + 1)
  | .printFloat e =>
    let (codeE, ve, tmp1) := compileExpr e offset nextTmp
    (codeE ++ [.printFloat ve], tmp1)
  | .printString lit => ([.printString lit], nextTmp)

-- ============================================================
-- § 4. Pretty-printing
-- ============================================================

def SExpr.toString : SExpr → String
  | .lit n => s!"{n}"
  | .var x => x
  | .bin op a b =>
    let opStr := match op with
      | .add => "+" | .sub => "-" | .mul => "*" | .div => "/" | .mod => "%"
      | .band => "&" | .bor => ("|" : String) | .bxor => "^" | .shl => "<<" | .shr => ">>"
    s!"({a.toString} {opStr} {b.toString})"
  | .arrRead arr idx => s!"{arr}[{idx.toString}]"
  | .flit f => s!"{f}"
  | .fbin op a b =>
    match op with
    | .fadd | .fsub | .fmul | .fdiv =>
      let opStr := match op with | .fadd => "+" | .fsub => "-" | .fmul => "*" | .fdiv => "/" | _ => "?"
      s!"({a.toString} {opStr} {b.toString})"
    | .fpow => s!"pow({a.toString}, {b.toString})"
    | .fmin => s!"fmin({a.toString}, {b.toString})"
    | .fmax => s!"fmax({a.toString}, {b.toString})"
  | .intToFloat e => s!"intToFloat({e.toString})"
  | .floatToInt e => s!"floatToInt({e.toString})"
  | .floatUnary op e =>
    let name := match op with
      | .exp => "exp" | .sqrt => "sqrt" | .sin => "sin" | .cos => "cos" | .tan => "tan"
      | .log => "log" | .log2 => "log2" | .log10 => "log10"
      | .abs => "abs" | .neg => "neg" | .round => "round"
    s!"{name}({e.toString})"
  | .farrRead arr idx => s!"{arr}[{idx.toString}]"

def SBool.toString : SBool → String
  | .lit true => "true"
  | .lit false => "false"
  | .bvar x => x
  | .cmp op a b =>
    let opStr := match op with | .eq => "==" | .ne => "!=" | .lt => "<" | .le => "<="
    s!"({a.toString} {opStr} {b.toString})"
  | .not e => s!"!{e.toString}"
  | .and a b => s!"({a.toString} && {b.toString})"
  | .or a b => s!"({a.toString} || {b.toString})"
  | .barrRead arr idx => s!"{arr}[{idx.toString}]"
  | .fcmp op a b =>
    let opStr := match op with | .feq => "==" | .fne => "!=" | .flt => "<" | .fle => "<="
    s!"({a.toString} {opStr} {b.toString})"

/-- Escape a string literal body so the tokenizer's `scanStr` (Parser.lean) reparses it
    identically. `scanStr` recognises `\"`, `\\`, `\n`, `\t`; every other character is
    emitted verbatim. Keeps `print`/`printString` round-tripping when the literal contains
    a quote, backslash, newline or tab. -/
def escapeStringLit (s : String) : String :=
  s.foldl (fun acc c =>
    acc ++ (match c with
      | '"'  => "\\\""
      | '\\' => "\\\\"
      | '\n' => "\\n"
      | '\t' => "\\t"
      | _    => String.singleton c)) ""

def Stmt.toString : Stmt → String
  | .skip => "skip"
  | .assign x e => s!"{x} := {e.toString}"
  | .bassign x b => s!"{x} := {b.toString}"
  | .arrWrite arr idx val => s!"{arr}[{idx.toString}] := {val.toString}"
  | .barrWrite arr idx bval => s!"{arr}[{idx.toString}] := {bval.toString}"
  | .seq s1 s2 => s!"{s1.toString};\n{s2.toString}"
  | .ite b s1 s2 =>
    "if " ++ b.toString ++ " {\n  " ++ s1.toString ++ "\n} else {\n  " ++ s2.toString ++ "\n}"
  | .loop b body =>
    "while " ++ b.toString ++ " {\n  " ++ body.toString ++ "\n}"
  | .fassign x e => s!"{x} := {e.toString}"
  | .farrWrite arr idx val => s!"{arr}[{idx.toString}] := {val.toString}"
  | .label lbl => s!"{lbl}:"
  | .goto lbl => s!"goto {lbl}"
  | .ifgoto b lbl => s!"if {b.toString} goto {lbl}"
  | .print fmt args => s!"print \"{escapeStringLit fmt}\", {", ".intercalate (args.map SExpr.toString)}"
  | .printInt e => s!"printInt({e.toString})"
  | .printBool b => s!"printBool({b.toString})"
  | .printFloat e => s!"printFloat({e.toString})"
  | .printString lit => s!"printString(\"{escapeStringLit lit}\")"

instance : ToString Stmt := ⟨Stmt.toString⟩
instance : ToString SExpr := ⟨SExpr.toString⟩
instance : ToString SBool := ⟨SBool.toString⟩

-- ============================================================
-- § 5. Typed programs with static type checking
-- ============================================================

/-- A typed program: explicit variable declarations followed by a statement body.
    All variables used in the body must be declared with their type.
    This enables static type checking that guarantees no type errors at runtime. -/
structure Program where
  decls      : List (Var × VarTy)
  arrayDecls : List (ArrayName × Nat × VarTy) := []
  body       : Stmt
  deriving Repr

/-- Decidable check that a statement has no goto/ifgoto. -/
def Stmt.checkNoGoto : Stmt → Bool
  | .goto _ | .ifgoto _ _ => false
  | .seq s₁ s₂ => Stmt.checkNoGoto s₁ && Stmt.checkNoGoto s₂
  | .ite _ s₁ s₂ => Stmt.checkNoGoto s₁ && Stmt.checkNoGoto s₂
  | .loop _ body => Stmt.checkNoGoto body
  | _ => true

namespace Program

/-- Look up a variable's declared type. -/
def lookupTy (prog : Program) (x : Var) : Option VarTy :=
  prog.decls.lookup x

/-- Default type for undeclared variables, derived from naming convention:
    `__f`-prefixed → `.float`, `__b`-prefixed → `.bool`, else → `.int`.
    Covers compiler temporaries (`__t`, `__ft`) and register-allocated
    variables (`__ir`, `__br`, `__fr`). -/
def defaultVarTy (x : Var) : VarTy :=
  match x.toList with
  | '_' :: '_' :: 'f' :: _ => .float
  | '_' :: '_' :: 'b' :: _ => .bool
  | _ => .int

theorem defaultVarTy_of_isTmp (x : Var) (h : x.isTmp = true) : defaultVarTy x = .int := by
  unfold defaultVarTy
  split
  · next heq => unfold String.isTmp at h; rw [heq] at h; simp at h
  · next heq => unfold String.isTmp at h; rw [heq] at h; simp at h
  · rfl

theorem defaultVarTy_of_isFTmp (x : Var) (h : x.isFTmp = true) : defaultVarTy x = .float := by
  unfold defaultVarTy
  split
  · rfl
  · next heq => unfold String.isFTmp at h; rw [heq] at h; simp at h
  · next hf _ =>
    unfold String.isFTmp at h
    revert h; split
    · next heq => exfalso; exact hf _ heq
    · simp

theorem defaultVarTy_of_isBTmp (x : Var) (h : x.isBTmp = true) : defaultVarTy x = .bool := by
  unfold defaultVarTy
  split
  · next heq => unfold String.isBTmp at h; rw [heq] at h; simp at h
  · rfl
  · next _ hb =>
    unfold String.isBTmp at h
    revert h; split
    · next heq => exfalso; exact hb _ heq
    · simp

/-- Build a total TyCtx from declarations. Undeclared variables are typed by
    naming convention via `defaultVarTy`. -/
def tyCtx (prog : Program) : TyCtx :=
  fun x => (prog.lookupTy x).getD (defaultVarTy x)

-- ============================================================
-- § 5a. Static type checker
-- ============================================================

/-- No duplicate variable declarations. -/
private def noDups : List Var → Bool
  | [] => true
  | x :: xs => !xs.contains x && noDups xs

/-- No declared variable uses a compiler-reserved temporary name (`__t`- or `__ft`-prefixed).
    Required so that compiler-generated temporaries are always typed correctly
    by `tyCtx` (int temps default to `.int`, float temps to `.float`).
    Not private: used by `CompilerCorrectness.typeCheck_tmpFree`. -/
def noTmpDecls (decls : List (Var × VarTy)) : Bool :=
  decls.all fun (x, _) => !x.isTmp && !x.isFTmp && !x.isBTmp

/-- Check that an array name is declared. -/
private def arrayDeclared (arrayDecls : List (ArrayName × Nat × VarTy)) (arr : ArrayName) : Bool :=
  arrayDecls.any fun (a, _, _) => a == arr

/-- Unified type-checker for expressions parameterized by expected type. -/
def checkExpr (lookup : Var → Option VarTy) (arrayDecls : List (ArrayName × Nat × VarTy))
    : VarTy → SExpr → Bool
  | .int, .lit _ => true
  | .int, .var x => lookup x == some .int
  | .int, .bin _ a b => checkExpr lookup arrayDecls .int a && checkExpr lookup arrayDecls .int b
  | .int, .arrRead arr idx => arrayDeclared arrayDecls arr && (arrayElemTy arrayDecls arr == .int) && checkExpr lookup arrayDecls .int idx
  | .int, .floatToInt e => checkExpr lookup arrayDecls .float e
  | .float, .flit _ => true
  | .float, .var x => lookup x == some .float
  | .float, .fbin _ a b => checkExpr lookup arrayDecls .float a && checkExpr lookup arrayDecls .float b
  | .float, .intToFloat e => checkExpr lookup arrayDecls .int e
  | .float, .floatUnary _ e => checkExpr lookup arrayDecls .float e
  | .float, .farrRead arr idx => arrayDeclared arrayDecls arr && (arrayElemTy arrayDecls arr == .float) && checkExpr lookup arrayDecls .int idx
  | _, _ => false

/-- Check that an expression is well-typed as `int`. -/
abbrev checkSExpr (lookup : Var → Option VarTy) (arrayDecls : List (ArrayName × Nat × VarTy)) :=
  checkExpr lookup arrayDecls .int

/-- Check that an expression is well-typed as `float`. -/
abbrev checkFExpr (lookup : Var → Option VarTy) (arrayDecls : List (ArrayName × Nat × VarTy)) :=
  checkExpr lookup arrayDecls .float

/-- Check that a boolean expression uses properly-typed declared variables. -/
def checkSBool (lookup : Var → Option VarTy) (arrayDecls : List (ArrayName × Nat × VarTy)) : SBool → Bool
  | .lit _ => true
  | .bvar x => lookup x == some .bool
  | .cmp _ a b => checkSExpr lookup arrayDecls a && checkSExpr lookup arrayDecls b
  | .not e => checkSBool lookup arrayDecls e
  | .and a b => checkSBool lookup arrayDecls a && checkSBool lookup arrayDecls b
  | .or a b => checkSBool lookup arrayDecls a && checkSBool lookup arrayDecls b
  | .barrRead arr idx => arrayDeclared arrayDecls arr && (arrayElemTy arrayDecls arr == .bool) && checkSExpr lookup arrayDecls idx
  | .fcmp _ a b => checkFExpr lookup arrayDecls a && checkFExpr lookup arrayDecls b

/-- Check that a statement body is well-typed w.r.t. declarations. -/
def checkStmt (lookup : Var → Option VarTy) (arrayDecls : List (ArrayName × Nat × VarTy)) : Stmt → Bool
  | .skip => true
  | .assign x e => lookup x == some .int && checkSExpr lookup arrayDecls e
  | .bassign x b => lookup x == some .bool && checkSBool lookup arrayDecls b
  | .arrWrite arr idx val =>
    arrayDeclared arrayDecls arr && (arrayElemTy arrayDecls arr == .int) && checkSExpr lookup arrayDecls idx && checkSExpr lookup arrayDecls val
  | .barrWrite arr idx bval =>
    arrayDeclared arrayDecls arr && (arrayElemTy arrayDecls arr == .bool) && checkSExpr lookup arrayDecls idx && checkSBool lookup arrayDecls bval
  | .seq s1 s2 => checkStmt lookup arrayDecls s1 && checkStmt lookup arrayDecls s2
  | .ite b s1 s2 =>
    checkSBool lookup arrayDecls b && checkStmt lookup arrayDecls s1 && checkStmt lookup arrayDecls s2
  | .loop b body => checkSBool lookup arrayDecls b && checkStmt lookup arrayDecls body
  | .fassign x e => lookup x == some .float && checkFExpr lookup arrayDecls e
  | .farrWrite arr idx val =>
    arrayDeclared arrayDecls arr && (arrayElemTy arrayDecls arr == .float) && checkSExpr lookup arrayDecls idx && checkFExpr lookup arrayDecls val
  | .label _ => true
  | .goto _ => true
  | .ifgoto b _ => checkSBool lookup arrayDecls b
  | .print _ args => args.all fun e => checkSExpr lookup arrayDecls e || checkFExpr lookup arrayDecls e
  | .printInt e => checkSExpr lookup arrayDecls e
  | .printBool b => checkSBool lookup arrayDecls b
  | .printFloat e => checkFExpr lookup arrayDecls e
  | .printString _ => true

/-- Full static type check: no duplicate declarations, no compiler-reserved
    temporary names in declarations, and the body is well-typed w.r.t.
    the declared variable types. -/
def typeCheck (prog : Program) : Bool :=
  noDups (prog.decls.map Prod.fst) &&
  noTmpDecls prog.decls &&
  checkStmt prog.lookupTy prog.arrayDecls prog.body

/-- No variable name starts with `__` (reserved for compiler-generated names). -/
def checkNoReservedNames (prog : Program) : Bool :=
  prog.decls.all fun (v, _) => !(startsWithList v "__")

/-- Check that no variable in an expression starts with `__`. -/
def SExpr.noReservedVars : SExpr → Bool
  | .lit _ | .flit _ => true
  | .var x => !(startsWithList x "__")
  | .bin _ a b | .fbin _ a b => SExpr.noReservedVars a && SExpr.noReservedVars b
  | .arrRead _ idx | .farrRead _ idx => SExpr.noReservedVars idx
  | .intToFloat e | .floatToInt e | .floatUnary _ e => SExpr.noReservedVars e

/-- Check that no variable in a boolean expression starts with `__`. -/
def SBool.noReservedVars : SBool → Bool
  | .lit _ => true
  | .bvar x => !(startsWithList x "__")
  | .cmp _ a b | .fcmp _ a b => SExpr.noReservedVars a && SExpr.noReservedVars b
  | .not e => SBool.noReservedVars e
  | .and a b | .or a b => SBool.noReservedVars a && SBool.noReservedVars b
  | .barrRead _ idx => SExpr.noReservedVars idx

/-- Check that no variable in a statement starts with `__`. -/
def Stmt.noReservedVars : Stmt → Bool
  | .skip | .label _ | .goto _ => true
  | .assign x e | .fassign x e => !(startsWithList x "__") && SExpr.noReservedVars e
  | .bassign x b => !(startsWithList x "__") && SBool.noReservedVars b
  | .arrWrite _ idx val | .farrWrite _ idx val =>
      SExpr.noReservedVars idx && SExpr.noReservedVars val
  | .barrWrite _ idx bval => SExpr.noReservedVars idx && SBool.noReservedVars bval
  | .seq s1 s2 => Stmt.noReservedVars s1 && Stmt.noReservedVars s2
  | .ite b s1 s2 =>
      SBool.noReservedVars b && Stmt.noReservedVars s1 && Stmt.noReservedVars s2
  | .loop b body => SBool.noReservedVars b && Stmt.noReservedVars body
  | .ifgoto b _ => SBool.noReservedVars b
  | .print _ args => args.all SExpr.noReservedVars
  | .printInt e => SExpr.noReservedVars e
  | .printBool b => SBool.noReservedVars b
  | .printFloat e => SExpr.noReservedVars e
  | .printString _ => true

/-- Well-formedness check: typeCheck + no goto/ifgoto + no reserved names (in decls and body).
    Used by compiler correctness proofs which require structured control flow
    and guarantee that `__ir`/`__br`/`__fr` register names are compiler-generated. -/
def wellFormed (prog : Program) : Bool :=
  prog.typeCheck && prog.body.checkNoGoto && prog.checkNoReservedNames &&
  Stmt.noReservedVars prog.body

-- ============================================================
-- § 5b. Compilation
-- ============================================================

/-- Emit initialization code for declared variables. -/
def initCode (decls : List (Var × VarTy)) : List TAC :=
  decls.map fun (x, ty) =>
    match ty with
    | .int   => .const x (.int (0 : BitVec 64))
    | .bool  => .const x (.bool false)
    | .float => .const x (.float (0 : BitVec 64))

/-- Infer the type a TAC instruction assigns to its destination variable. -/
private def instrDefType : TAC → Option (Var × VarTy)
  | .const x v        => some (x, v.typeOf)
  | .copy _x _        => none  -- inherits type from source, handled by declared vars
  | .binop x _ _ _    => some (x, .int)
  | .boolop x _       => some (x, .bool)
  | .arrLoad x _ _ ty => some (x, ty)
  | .fbinop x _ _ _   => some (x, .float)
  | .intToFloat x _   => some (x, .float)
  | .floatToInt x _   => some (x, .int)
  | .floatUnary x _ _ => some (x, .float)
  | .fternop x _ _ _ _ => some (x, .float)
  | _                  => none


/-- Compile a typed program: initialize declared variables, then compile body.
    Appends `halt` at the end. -/
def compileToTAC (prog : Program) : Prog :=
  let inits := initCode prog.decls
  let labels := collectLabels prog.body inits.length
  let (body, _) := compileStmt prog.body inits.length 0 labels
  let code := (inits ++ body ++ [TAC.halt]).toArray
  { code := code
    observable := prog.decls.map Prod.fst
    arrayDecls := prog.arrayDecls }


-- ============================================================
-- § 5c. Interpretation
-- ============================================================

-- The fold step for initStore (defined before initStore so it can be reused)
private def initFold (σ : Store) (p : Var × VarTy) : Store :=
  match p.2 with
  | .int   => σ[p.1 ↦ .int (0 : BitVec 64)]
  | .bool  => σ[p.1 ↦ .bool false]
  | .float => σ[p.1 ↦ .float (0 : BitVec 64)]

/-- Base store: defaults match `tyCtx` naming convention via `defaultVarTy`. -/
private def initStoreBase : Store := fun x =>
  match x.toList with
  | '_' :: '_' :: 'f' :: _ => .float (0 : BitVec 64)
  | '_' :: '_' :: 'b' :: _ => .bool false
  | _ => .int (0 : BitVec 64)

/-- Build an initial store from declarations with type-appropriate defaults.
    Int variables get 0, bool variables get false, float variables get 0. -/
def initStore (prog : Program) : Store :=
  prog.decls.foldl initFold initStoreBase

/-- Interpret a typed program. Starts from the declaration-initialized store,
    with optional input overrides. -/
def interp (prog : Program) (fuel : Nat)
    (inputs : List (Var × Value) := []) : Option (Store × ArrayMem) :=
  let σ₀ := inputs.foldl (fun σ (x, v) => σ[x ↦ v]) prog.initStore
  prog.body.interp fuel σ₀ ArrayMem.init prog.arrayDecls

-- ============================================================
-- § 5d. initStore is well-typed
-- ============================================================

-- `contains` false implies not a member (for Var = String with LawfulBEq)
private theorem notMem_of_contains_false {x : Var} {xs : List Var}
    (h : xs.contains x = false) : x ∉ xs := by
  intro hmem
  induction xs with
  | nil => contradiction
  | cons y ys ih =>
    simp only [List.contains_cons, Bool.or_eq_false_iff] at h
    obtain ⟨h1, h2⟩ := h
    cases hmem with
    | head => simp at h1
    | tail _ hmem => exact ih h2 hmem

-- Fold over decls does not change variables not in the domain
private theorem initFold_notMem (ds : List (Var × VarTy)) (σ : Store) (x : Var)
    (h : x ∉ ds.map Prod.fst) :
    ds.foldl initFold σ x = σ x := by
  induction ds generalizing σ with
  | nil => rfl
  | cons hd rest ih =>
    obtain ⟨y, ty⟩ := hd
    simp only [List.map_cons, List.mem_cons, not_or] at h
    obtain ⟨hne, hnot⟩ := h
    simp only [List.foldl, initFold]
    rw [ih _ hnot]
    -- update(y, ...) x = σ x since x ≠ y
    have hbeq : (x == y) = false := by simp [hne]
    cases ty <;> simp [Store.update, hbeq]

-- Core lemma: the fold value type matches lookup default
private theorem initFold_typeOf (ds : List (Var × VarTy)) (σ : Store) (x : Var)
    (hnd : noDups (ds.map Prod.fst) = true) :
    (ds.foldl initFold σ x).typeOf = (ds.lookup x).getD (σ x).typeOf := by
  induction ds generalizing σ with
  | nil => simp [List.lookup]
  | cons hd rest ih =>
    obtain ⟨y, ty⟩ := hd
    simp only [List.map_cons, noDups, Bool.not_eq_true', Bool.and_eq_true] at hnd
    obtain ⟨hny, hnd_rest⟩ := hnd
    have hny_notMem : y ∉ rest.map Prod.fst := notMem_of_contains_false hny
    simp only [List.foldl, List.lookup_cons]
    by_cases hxy : x = y
    · -- x = y: update sets x, rest never touches it (no dup)
      subst hxy
      simp only [beq_self_eq_true]
      rw [initFold_notMem rest _ x hny_notMem]
      cases ty <;> simp [initFold, Store.update_self, Value.typeOf]
    · -- x ≠ y: lookup skips y, initFold(y,..) leaves x unchanged
      have hbeq : (x == y) = false := by simp [hxy]
      simp only [hbeq]
      rw [ih _ hnd_rest]
      -- initFold (σ[y ↦ v]) x = σ x since x ≠ y
      cases ty <;> simp [initFold, Store.update, hbeq]

/-- The initial store from declarations is well-typed w.r.t. the program's TyCtx. -/
theorem initStore_typedStore (prog : Program)
    (hnd : noDups (prog.decls.map Prod.fst) = true) :
    TypedStore prog.tyCtx prog.initStore := by
  intro x
  simp only [initStore, tyCtx, lookupTy]
  show (prog.decls.foldl initFold initStoreBase x).typeOf = _
  rw [initFold_typeOf prog.decls initStoreBase x hnd]
  simp only [initStoreBase, defaultVarTy]
  split <;> simp [Value.typeOf]

/-- wellFormed implies typeCheck. -/
theorem wellFormed_typeCheck (prog : Program) (h : prog.wellFormed = true) :
    prog.typeCheck = true := by
  unfold wellFormed at h; simp only [Bool.and_eq_true] at h; exact h.1.1.1

/-- Extract noDups from typeCheck (public, so other files can use it). -/
theorem typeCheck_noDups (prog : Program) (h : prog.typeCheck = true) :
    noDups (prog.decls.map Prod.fst) = true := by
  unfold typeCheck at h; simp only [Bool.and_eq_true] at h; exact h.1.1

/-- If a program type-checks, its initial store is well-typed. -/
theorem typeCheck_initStore_typedStore (prog : Program) (h : prog.typeCheck = true) :
    TypedStore prog.tyCtx prog.initStore :=
  initStore_typedStore prog (typeCheck_noDups prog h)

-- ============================================================
-- § 5d'. initStore declared-variable values and init code execution
-- ============================================================

/-- For a declared variable in a no-dup list, the fold assigns its default value. -/
private theorem initFold_declared (ds : List (Var × VarTy)) (σ : Store) (x : Var) (ty : VarTy)
    (hmem : (x, ty) ∈ ds) (hnd : noDups (ds.map Prod.fst) = true) :
    ds.foldl initFold σ x = ty.defaultVal := by
  induction ds generalizing σ with
  | nil => contradiction
  | cons hd rest ih =>
    simp only [List.map_cons, noDups, Bool.not_eq_true', Bool.and_eq_true] at hnd
    obtain ⟨hny, hnd_rest⟩ := hnd
    simp only [List.foldl]
    cases hmem with
    | head =>
      rw [initFold_notMem rest _ x (notMem_of_contains_false hny)]
      cases ty <;> simp [initFold, Store.update_self, VarTy.defaultVal]
    | tail _ hmem_rest =>
      exact ih (initFold σ hd) hmem_rest hnd_rest

/-- For each declared variable, `initStore` holds the type-appropriate default. -/
theorem initStore_declared (prog : Program) {x : Var} {ty : VarTy}
    (hmem : (x, ty) ∈ prog.decls) (hnd : noDups (prog.decls.map Prod.fst) = true) :
    prog.initStore x = ty.defaultVal :=
  initFold_declared prog.decls initStoreBase x ty hmem hnd

/-- `initCode` has the same length as the declaration list. -/
private theorem initCode_length (decls : List (Var × VarTy)) :
    (initCode decls).length = decls.length := by
  simp [initCode, List.length_map]

/-- Running init code from `initStore` is idempotent: each `const x v` sets a variable
    that already holds `v`, so the store is unchanged. -/
theorem compileToTAC_initExec (prog : Program)
    (hnd : noDups (prog.decls.map Prod.fst) = true) :
    prog.compileToTAC ⊩ Cfg.run 0 prog.initStore ArrayMem.init ⟶* Cfg.run prog.decls.length prog.initStore ArrayMem.init := by
  suffices h : ∀ (k : Nat), k ≤ prog.decls.length →
      prog.compileToTAC ⊩ Cfg.run 0 prog.initStore ArrayMem.init ⟶* Cfg.run k prog.initStore ArrayMem.init from
    h prog.decls.length (Nat.le_refl _)
  intro k hk
  induction k with
  | zero => exact Steps.refl
  | succ k ih =>
    have ih_steps := ih (by omega)
    have hk_lt : k < prog.decls.length := by omega
    -- The k-th declaration and its init instruction
    have hmem_decl : prog.decls[k] ∈ prog.decls := List.getElem_mem hk_lt
    have hval := initStore_declared prog hmem_decl hnd
    -- The const step is a no-op because the value is already present
    have hstep : Step prog.compileToTAC (.run k prog.initStore ArrayMem.init)
        (.run (k + 1) prog.initStore ArrayMem.init) := by
      -- Normalize get/getElem
      have hget : prog.decls.get ⟨k, hk_lt⟩ = prog.decls[k] := rfl
      rw [hget] at hval
      -- Case split on the type of the k-th declaration
      cases hty : (prog.decls[k]).2 with
      | int =>
        simp only [hty, VarTy.defaultVal] at hval
        have hinst : prog.compileToTAC[k]? =
            some (.const (prog.decls[k]).1 (.int 0)) := by
          simp only [Prog.getElem?_code, Program.compileToTAC, List.getElem?_toArray]
          rw [List.getElem?_append_left (by rw [List.length_append, initCode_length]; omega)]
          rw [List.getElem?_append_left (by rw [initCode_length]; omega)]
          simp only [initCode, List.getElem?_map, List.getElem?_eq_getElem hk_lt,
            Option.map_some, hty]
        have := Step.const hinst (σ := prog.initStore) (am := ArrayMem.init)
        rwa [Store.update_of_eq _ _ _ hval] at this
      | bool =>
        simp only [hty, VarTy.defaultVal] at hval
        have hinst : prog.compileToTAC[k]? =
            some (.const (prog.decls[k]).1 (.bool false)) := by
          simp only [Prog.getElem?_code, Program.compileToTAC, List.getElem?_toArray]
          rw [List.getElem?_append_left (by rw [List.length_append, initCode_length]; omega)]
          rw [List.getElem?_append_left (by rw [initCode_length]; omega)]
          simp only [initCode, List.getElem?_map, List.getElem?_eq_getElem hk_lt,
            Option.map_some, hty]
        have := Step.const hinst (σ := prog.initStore) (am := ArrayMem.init)
        rwa [Store.update_of_eq _ _ _ hval] at this
      | float =>
        simp only [hty, VarTy.defaultVal] at hval
        have hinst : prog.compileToTAC[k]? =
            some (.const (prog.decls[k]).1 (.float 0)) := by
          simp only [Prog.getElem?_code, Program.compileToTAC, List.getElem?_toArray]
          rw [List.getElem?_append_left (by rw [List.length_append, initCode_length]; omega)]
          rw [List.getElem?_append_left (by rw [initCode_length]; omega)]
          simp only [initCode, List.getElem?_map, List.getElem?_eq_getElem hk_lt,
            Option.map_some, hty]
        have := Step.const hinst (σ := prog.initStore) (am := ArrayMem.init)
        rwa [Store.update_of_eq _ _ _ hval] at this
    exact Steps.trans ih_steps (Steps.step hstep Steps.refl)

/-- Index into body code within `prog.compileToTAC`. The body starts at offset `decls.length`. -/
theorem compileToTAC_body_getElem (prog : Program) (i : Nat)
    (hi : i < (compileStmt prog.body prog.decls.length 0
      (collectLabels prog.body prog.decls.length)).1.length) :
    prog.compileToTAC[prog.decls.length + i]? =
      (compileStmt prog.body prog.decls.length 0
        (collectLabels prog.body prog.decls.length)).1[i]? := by
  simp only [Prog.getElem?_code, Program.compileToTAC, List.getElem?_toArray, initCode_length]
  rw [List.getElem?_append_left (by simp [List.length_append, initCode_length]; omega)]
  rw [List.getElem?_append_right (by rw [initCode_length]; omega)]
  simp [initCode_length]

/-- The halt instruction sits right after the body code in `prog.compileToTAC`. -/
theorem compileToTAC_halt_getElem (prog : Program) :
    prog.compileToTAC[prog.decls.length +
      (compileStmt prog.body prog.decls.length 0
        (collectLabels prog.body prog.decls.length)).1.length]? = some .halt := by
  simp [Program.compileToTAC, initCode_length, List.length_append]

-- ============================================================
-- § 5e. Executable well-typedness check for compiled output
-- ============================================================

/-- Check that every instruction in a compiled program is well-typed. -/
def checkWellTypedProg (Γ : TyCtx) (p : Prog) : Bool :=
  (List.range p.size).all fun i =>
    match p[i]? with
    | some instr => checkWellTypedInstr Γ p.arrayDecls instr
    | none => true

/-- Executable verification: if the source type-checks, the compiled TAC
    is well-typed under the program's TyCtx. -/
def verifyWellTyped (prog : Program) : Bool :=
  prog.typeCheck && checkWellTypedProg prog.tyCtx prog.compileToTAC

-- ============================================================
-- § 5f. Soundness: type checking ⟹ compiled TAC is well-typed
-- ============================================================

end Program  -- temporarily close namespace for helper definitions

-- Helper: every element of a list satisfies WellTypedInstr
def AllWTI (Γ : TyCtx) (decls : List (ArrayName × Nat × VarTy)) (l : List TAC) : Prop :=
  ∀ instr, instr ∈ l → WellTypedInstr Γ decls instr

theorem allWTI_nil' (Γ : TyCtx) (decls : List (ArrayName × Nat × VarTy)) : AllWTI Γ decls List.nil := by
  intro _ h; simp at h

theorem allWTI_cons' {Γ : TyCtx} {decls : List (ArrayName × Nat × VarTy)} {x : TAC} {xs : List TAC}
    (hx : WellTypedInstr Γ decls x) (hxs : AllWTI Γ decls xs) :
    AllWTI Γ decls (x :: xs) := by
  intro instr hmem
  simp at hmem
  rcases hmem with rfl | hmem
  · exact hx
  · exact hxs instr hmem

theorem allWTI_one {Γ : TyCtx} {decls : List (ArrayName × Nat × VarTy)} {x : TAC}
    (h : WellTypedInstr Γ decls x) : AllWTI Γ decls (x :: List.nil) :=
  allWTI_cons' h (allWTI_nil' Γ decls)

theorem allWTI_append' {Γ : TyCtx} {decls : List (ArrayName × Nat × VarTy)} {l1 l2 : List TAC}
    (h1 : AllWTI Γ decls l1) (h2 : AllWTI Γ decls l2) :
    AllWTI Γ decls (l1 ++ l2) := by
  intro instr hmem
  simp at hmem
  rcases hmem with h | h
  · exact h1 instr h
  · exact h2 instr h

theorem allWTI_append3 {Γ : TyCtx} {decls : List (ArrayName × Nat × VarTy)} {l1 l2 l3 : List TAC}
    (h1 : AllWTI Γ decls l1) (h2 : AllWTI Γ decls l2) (h3 : AllWTI Γ decls l3) :
    AllWTI Γ decls (l1 ++ l2 ++ l3) :=
  allWTI_append' (allWTI_append' h1 h2) h3

theorem allWTI_toArray' {Γ : TyCtx} {decls : List (ArrayName × Nat × VarTy)} {l : List TAC} {p : Prog}
    (hcode : p.code = l.toArray)
    (hdecls : p.arrayDecls = decls)
    (h : AllWTI Γ decls l) : WellTypedProg Γ p := by
  intro i hi
  have hi' : i < l.length := by rw [Prog.size, hcode] at hi; simp at hi; exact hi
  have hmem : l[i] ∈ l := List.getElem_mem hi'
  show WellTypedInstr Γ p.arrayDecls p[i]
  have : p[i] = l[i] := by simp [Prog.getElem_eq, hcode, List.getElem_toArray]
  rw [this, hdecls]
  exact h _ hmem

-- If (x, ty) ∈ decls and noDups, then lookup x = some ty
theorem lookup_of_mem_noDups_wt {decls : List (Var × VarTy)} {x : Var} {ty : VarTy}
    (hmem : (x, ty) ∈ decls) (hnd : Program.noDups (decls.map Prod.fst) = true) :
    decls.lookup x = some ty := by
  induction decls with
  | nil => simp at hmem
  | cons hd rest ih =>
    obtain ⟨y, ty'⟩ := hd
    simp only [List.map_cons, Program.noDups, Bool.not_eq_true', Bool.and_eq_true] at hnd
    obtain ⟨hny, hnd_rest⟩ := hnd
    simp at hmem
    rcases hmem with ⟨rfl, rfl⟩ | hmem_rest
    · simp [List.lookup]
    · simp only [List.lookup_cons]
      by_cases hxy : x == y
      · simp at hxy; subst hxy
        have : x ∈ rest.map Prod.fst :=
          List.mem_map.mpr ⟨(x, ty), hmem_rest, rfl⟩
        exact absurd this (Program.notMem_of_contains_false hny)
      · simp [hxy]
        exact ih hmem_rest hnd_rest

-- If noTmpDecls and x.isTmp, then lookup returns none
theorem lookup_none_of_isTmp_wt {decls : List (Var × VarTy)}
    (hnt : Program.noTmpDecls decls = true) {x : Var} (hx : x.isTmp = true) :
    decls.lookup x = none := by
  induction decls with
  | nil => rfl
  | cons hd rest ih =>
    obtain ⟨y, ty⟩ := hd
    simp only [Program.noTmpDecls, List.all_cons, Bool.and_eq_true] at hnt
    obtain ⟨⟨⟨hny, _⟩, _⟩, hnt_rest⟩ := hnt
    simp only [List.lookup_cons]
    have hne : (x == y) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]
      intro heq; subst heq
      simp only [Bool.not_eq_true'] at hny
      rw [hx] at hny; exact Bool.noConfusion hny
    simp only [hne]
    exact ih hnt_rest

-- If noTmpDecls and x.isFTmp, then lookup returns none
theorem lookup_none_of_isFTmp_wt {decls : List (Var × VarTy)}
    (hnt : Program.noTmpDecls decls = true) {x : Var} (hx : x.isFTmp = true) :
    decls.lookup x = none := by
  induction decls with
  | nil => rfl
  | cons hd rest ih =>
    obtain ⟨y, ty⟩ := hd
    simp only [Program.noTmpDecls, List.all_cons, Bool.and_eq_true] at hnt
    obtain ⟨⟨⟨_, hny⟩, _⟩, hnt_rest⟩ := hnt
    simp only [List.lookup_cons]
    have hne : (x == y) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]
      intro heq; subst heq
      simp only [Bool.not_eq_true'] at hny
      rw [hx] at hny; exact Bool.noConfusion hny
    simp only [hne]
    exact ih hnt_rest

-- If noTmpDecls and x.isBTmp, then lookup returns none
theorem lookup_none_of_isBTmp_wt {decls : List (Var × VarTy)}
    (hnt : Program.noTmpDecls decls = true) {x : Var} (hx : x.isBTmp = true) :
    decls.lookup x = none := by
  induction decls with
  | nil => rfl
  | cons hd rest ih =>
    obtain ⟨y, ty⟩ := hd
    simp only [Program.noTmpDecls, List.all_cons, Bool.and_eq_true] at hnt
    obtain ⟨⟨_, hny⟩, hnt_rest⟩ := hnt
    simp only [List.lookup_cons]
    have hne : (x == y) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]
      intro heq; subst heq
      simp only [Bool.not_eq_true'] at hny
      rw [hx] at hny; exact Bool.noConfusion hny
    simp only [hne]
    exact ih hnt_rest

-- tmpName k is a temporary variable
theorem tmpName_isTmp_wt (k : Nat) : (tmpName k).isTmp = true := by
  simp only [String.isTmp, tmpName, String.toList_append]
  show (match '_' :: '_' :: 't' :: (toString k).toList with
    | '_' :: '_' :: 't' :: _ => true | _ => false) = true
  rfl

-- tmpName k is NOT a float temporary
theorem tmpName_not_isFTmp (k : Nat) : (tmpName k).isFTmp = false := by
  simp only [String.isFTmp, tmpName, String.toList_append]
  show (match '_' :: '_' :: 't' :: (toString k).toList with
    | '_' :: '_' :: 'f' :: 't' :: _ => false | _ => false) = false
  rfl

-- ftmpName k is a float temporary variable
theorem ftmpName_isFTmp_wt (k : Nat) : (ftmpName k).isFTmp = true := by
  simp only [String.isFTmp, ftmpName, String.toList_append]
  show (match '_' :: '_' :: 'f' :: 't' :: (toString k).toList with
    | '_' :: '_' :: 'f' :: 't' :: _ => true | _ => false) = true
  rfl

-- ftmpName k is NOT a regular temporary
theorem ftmpName_not_isTmp (k : Nat) : (ftmpName k).isTmp = false := by
  simp only [String.isTmp, ftmpName, String.toList_append]
  show (match '_' :: '_' :: 'f' :: 't' :: (toString k).toList with
    | '_' :: '_' :: 't' :: _ => true | _ => false) = false
  rfl

-- btmpName k is a bool temporary variable
theorem btmpName_isBTmp_wt (k : Nat) : (btmpName k).isBTmp = true := by
  simp only [String.isBTmp, btmpName, String.toList_append]
  show (match '_' :: '_' :: 'b' :: 't' :: (toString k).toList with
    | '_' :: '_' :: 'b' :: 't' :: _ => true | _ => false) = true
  rfl

-- tyCtx maps int temporaries to .int
theorem tyCtx_tmp_wt (prog : Program)
    (hnt : Program.noTmpDecls prog.decls = true) (k : Nat) :
    prog.tyCtx (tmpName k) = .int := by
  unfold Program.tyCtx Program.lookupTy
  rw [lookup_none_of_isTmp_wt hnt (tmpName_isTmp_wt k)]
  simp only [Option.getD]
  exact Program.defaultVarTy_of_isTmp _ (tmpName_isTmp_wt k)

-- tyCtx maps float temporaries to .float
theorem tyCtx_ftmp_wt (prog : Program)
    (hnt : Program.noTmpDecls prog.decls = true) (k : Nat) :
    prog.tyCtx (ftmpName k) = .float := by
  unfold Program.tyCtx Program.lookupTy
  rw [lookup_none_of_isFTmp_wt hnt (ftmpName_isFTmp_wt k)]
  simp only [Option.getD]
  exact Program.defaultVarTy_of_isFTmp _ (ftmpName_isFTmp_wt k)

-- tyCtx maps bool temporaries to .bool
theorem tyCtx_btmp_wt (prog : Program)
    (hnt : Program.noTmpDecls prog.decls = true) (k : Nat) :
    prog.tyCtx (btmpName k) = .bool := by
  unfold Program.tyCtx Program.lookupTy
  rw [lookup_none_of_isBTmp_wt hnt (btmpName_isBTmp_wt k)]
  simp only [Option.getD]
  exact Program.defaultVarTy_of_isBTmp _ (btmpName_isBTmp_wt k)

-- If lookupTy x = some ty, then tyCtx x = ty
theorem tyCtx_of_lookup_wt (prog : Program) (x : Var) (ty : VarTy)
    (h : prog.lookupTy x = some ty) : prog.tyCtx x = ty := by
  unfold Program.tyCtx
  rw [h]; rfl

-- compileExpr produces well-typed instructions and the result var has the expected type
theorem compileExpr_typed_wt (prog : Program)
    (hnt : Program.noTmpDecls prog.decls = true)
    (e : SExpr) (ty : VarTy)
    (hchk : Program.checkExpr prog.lookupTy prog.arrayDecls ty e = true)
    (offset nextTmp : Nat) :
    AllWTI prog.tyCtx prog.arrayDecls (compileExpr e offset nextTmp).1
    ∧ prog.tyCtx (compileExpr e offset nextTmp).2.1 = ty := by
  induction e generalizing ty offset nextTmp with
  | lit n =>
    match ty with
    | .int =>
      simp only [compileExpr]
      exact ⟨allWTI_one (.const (by simp [Value.typeOf]; exact (tyCtx_tmp_wt prog hnt _).symm)),
             tyCtx_tmp_wt prog hnt _⟩
    | .float => simp [Program.checkExpr] at hchk
    | .bool => simp [Program.checkExpr] at hchk
  | var x =>
    match ty with
    | .int =>
      simp only [compileExpr]
      constructor
      · exact allWTI_nil' _ _
      · simp [Program.checkExpr, beq_iff_eq] at hchk
        exact tyCtx_of_lookup_wt prog x .int hchk
    | .float =>
      simp only [compileExpr]
      constructor
      · exact allWTI_nil' _ _
      · simp [Program.checkExpr, beq_iff_eq] at hchk
        exact tyCtx_of_lookup_wt prog x .float hchk
    | .bool => simp [Program.checkExpr] at hchk
  | bin op a b iha ihb =>
    match ty with
    | .int =>
      simp [Program.checkExpr, Bool.and_eq_true] at hchk
      obtain ⟨hca, hcb⟩ := hchk
      have ⟨ha_wt, ha_ty⟩ := iha .int hca offset nextTmp
      have ⟨hb_wt, hb_ty⟩ := ihb .int hcb
        (offset + (compileExpr a offset nextTmp).1.length)
        (compileExpr a offset nextTmp).2.2
      simp only [compileExpr]
      constructor
      · exact allWTI_append3 ha_wt hb_wt
          (allWTI_one (.binop (tyCtx_tmp_wt prog hnt _) ha_ty hb_ty))
      · exact tyCtx_tmp_wt prog hnt _
    | .float => simp [Program.checkExpr] at hchk
    | .bool => simp [Program.checkExpr] at hchk
  | arrRead _arr idx ih =>
    match ty with
    | .int =>
      simp [Program.checkExpr, Bool.and_eq_true, beq_iff_eq] at hchk
      have ⟨⟨_, hety⟩, hci⟩ := hchk
      have ⟨hi_wt, hi_ty⟩ := ih .int hci offset nextTmp
      simp only [compileExpr]
      exact ⟨allWTI_append' hi_wt (allWTI_one (.arrLoad (tyCtx_tmp_wt prog hnt _) hi_ty hety.symm)),
             tyCtx_tmp_wt prog hnt _⟩
    | .float => simp [Program.checkExpr] at hchk
    | .bool => simp [Program.checkExpr] at hchk
  | flit f =>
    match ty with
    | .float =>
      simp only [compileExpr]
      exact ⟨allWTI_one (.const (by simp [Value.typeOf]; exact (tyCtx_ftmp_wt prog hnt _).symm)),
             tyCtx_ftmp_wt prog hnt _⟩
    | .int => simp [Program.checkExpr] at hchk
    | .bool => simp [Program.checkExpr] at hchk
  | fbin op a b iha ihb =>
    match ty with
    | .float =>
      simp [Program.checkExpr, Bool.and_eq_true] at hchk
      obtain ⟨hca, hcb⟩ := hchk
      have ⟨ha_wt, ha_ty⟩ := iha .float hca offset nextTmp
      have ⟨hb_wt, hb_ty⟩ := ihb .float hcb
        (offset + (compileExpr a offset nextTmp).1.length)
        (compileExpr a offset nextTmp).2.2
      simp only [compileExpr]
      constructor
      · exact allWTI_append3 ha_wt hb_wt
          (allWTI_one (.fbinop (tyCtx_ftmp_wt prog hnt _) ha_ty hb_ty))
      · exact tyCtx_ftmp_wt prog hnt _
    | .int => simp [Program.checkExpr] at hchk
    | .bool => simp [Program.checkExpr] at hchk
  | intToFloat e ih =>
    match ty with
    | .float =>
      simp [Program.checkExpr] at hchk
      have ⟨he_wt, he_ty⟩ := ih .int hchk offset nextTmp
      simp only [compileExpr]
      constructor
      · exact allWTI_append' he_wt
          (allWTI_one (.intToFloat (tyCtx_ftmp_wt prog hnt _) he_ty))
      · exact tyCtx_ftmp_wt prog hnt _
    | .int => simp [Program.checkExpr] at hchk
    | .bool => simp [Program.checkExpr] at hchk
  | floatToInt e ih =>
    match ty with
    | .int =>
      simp [Program.checkExpr] at hchk
      have ⟨he_wt, he_ty⟩ := ih .float hchk offset nextTmp
      simp only [compileExpr]
      constructor
      · exact allWTI_append' he_wt
          (allWTI_one (.floatToInt (tyCtx_tmp_wt prog hnt _) he_ty))
      · exact tyCtx_tmp_wt prog hnt _
    | .float => simp [Program.checkExpr] at hchk
    | .bool => simp [Program.checkExpr] at hchk
  | floatUnary op e ih =>
    match ty with
    | .float =>
      simp [Program.checkExpr] at hchk
      have ⟨he_wt, he_ty⟩ := ih .float hchk offset nextTmp
      simp only [compileExpr]
      constructor
      · exact allWTI_append' he_wt
          (allWTI_one (.floatUnary (tyCtx_ftmp_wt prog hnt _) he_ty))
      · exact tyCtx_ftmp_wt prog hnt _
    | .int => simp [Program.checkExpr] at hchk
    | .bool => simp [Program.checkExpr] at hchk
  | farrRead _arr idx ih =>
    match ty with
    | .float =>
      simp [Program.checkExpr, Bool.and_eq_true, beq_iff_eq] at hchk
      have ⟨⟨_, hety⟩, hci⟩ := hchk
      have ⟨hi_wt, hi_ty⟩ := ih .int hci offset nextTmp
      simp only [compileExpr]
      exact ⟨allWTI_append' hi_wt (allWTI_one (.arrLoad (tyCtx_ftmp_wt prog hnt _) hi_ty hety.symm)),
             tyCtx_ftmp_wt prog hnt _⟩
    | .int => simp [Program.checkExpr] at hchk
    | .bool => simp [Program.checkExpr] at hchk

-- Backward-compatible wrappers
theorem compileExpr_wt (prog : Program)
    (hnt : Program.noTmpDecls prog.decls = true)
    (e : SExpr) (hchk : Program.checkSExpr prog.lookupTy prog.arrayDecls e = true)
    (offset nextTmp : Nat) :
    AllWTI prog.tyCtx prog.arrayDecls (compileExpr e offset nextTmp).1
    ∧ prog.tyCtx (compileExpr e offset nextTmp).2.1 = .int :=
  compileExpr_typed_wt prog hnt e .int hchk offset nextTmp

theorem compileExpr_float_wt (prog : Program)
    (hnt : Program.noTmpDecls prog.decls = true)
    (e : SExpr) (hchk : Program.checkFExpr prog.lookupTy prog.arrayDecls e = true)
    (offset nextTmp : Nat) :
    AllWTI prog.tyCtx prog.arrayDecls (compileExpr e offset nextTmp).1
    ∧ prog.tyCtx (compileExpr e offset nextTmp).2.1 = .float :=
  compileExpr_typed_wt prog hnt e .float hchk offset nextTmp

theorem compileExprs_wt (prog : Program)
    (hnt : Program.noTmpDecls prog.decls = true)
    (args : List SExpr) (offset nextTmp : Nat)
    (hchk : (args.all fun e =>
      Program.checkSExpr prog.lookupTy prog.arrayDecls e ||
      Program.checkFExpr prog.lookupTy prog.arrayDecls e) = true) :
    AllWTI prog.tyCtx prog.arrayDecls (compileExprs args offset nextTmp).1 := by
  induction args generalizing offset nextTmp with
  | nil => exact allWTI_nil' _ _
  | cons e rest ih =>
    simp only [compileExprs]
    simp only [List.all_cons, Bool.and_eq_true] at hchk
    obtain ⟨he, hrest⟩ := hchk
    simp only [Bool.or_eq_true] at he
    have he_wt : AllWTI prog.tyCtx prog.arrayDecls (compileExpr e offset nextTmp).1 :=
      match he with
      | .inl h => (compileExpr_wt prog hnt e h offset nextTmp).1
      | .inr h => (compileExpr_float_wt prog hnt e h offset nextTmp).1
    exact allWTI_append' he_wt (ih (offset + (compileExpr e offset nextTmp).1.length)
      (compileExpr e offset nextTmp).2.2 hrest)

-- compileBool produces well-typed instructions and a WellTypedBoolExpr
theorem compileBool_wt (prog : Program)
    (hnt : Program.noTmpDecls prog.decls = true)
    (b : SBool) (hchk : Program.checkSBool prog.lookupTy prog.arrayDecls b = true)
    (offset nextTmp : Nat) :
    AllWTI prog.tyCtx prog.arrayDecls (compileBool b offset nextTmp).1
    ∧ WellTypedBoolExpr prog.tyCtx (compileBool b offset nextTmp).2.1 := by
  induction b generalizing offset nextTmp with
  | lit b =>
    simp only [compileBool]
    exact ⟨allWTI_nil' _ _, .lit⟩
  | bvar x =>
    simp only [compileBool]
    constructor
    · exact allWTI_nil' _ _
    · simp [Program.checkSBool, beq_iff_eq] at hchk
      exact .bvar (tyCtx_of_lookup_wt prog x .bool hchk)
  | cmp op a b =>
    simp [Program.checkSBool, Bool.and_eq_true] at hchk
    obtain ⟨hca, hcb⟩ := hchk
    have ⟨ha_wt, ha_ty⟩ := compileExpr_wt prog hnt a hca offset nextTmp
    have ⟨hb_wt, hb_ty⟩ := compileExpr_wt prog hnt b hcb
      (offset + (compileExpr a offset nextTmp).1.length)
      (compileExpr a offset nextTmp).2.2
    simp only [compileBool]
    exact ⟨allWTI_append' ha_wt hb_wt, .cmp ha_ty hb_ty⟩
  | not e ih =>
    simp [Program.checkSBool] at hchk
    have ⟨he_wt, he_ty⟩ := ih hchk offset nextTmp
    simp only [compileBool]
    exact ⟨he_wt, .not he_ty⟩
  | and a b iha ihb =>
    simp [Program.checkSBool, Bool.and_eq_true] at hchk
    obtain ⟨hca, hcb⟩ := hchk
    have ⟨ha_wt, ha_ty⟩ := iha hca offset nextTmp
    have ⟨hb_wt, hb_ty⟩ := ihb hcb
      (offset + (compileBool a offset nextTmp).1.length + 1)
      ((compileBool a offset nextTmp).2.2 + 1)
    simp only [compileBool]
    refine ⟨?_, .cmp (by simp [ExprHasTy]; exact tyCtx_tmp_wt prog hnt _) (by simp [ExprHasTy])⟩
    let tmp1 := (compileBool a offset nextTmp).2.2
    have htR : (Value.int 1).typeOf = prog.tyCtx (tmpName tmp1) := by
      simp [Value.typeOf]; exact (tyCtx_tmp_wt prog hnt tmp1).symm
    have htR0 : (Value.int 0).typeOf = prog.tyCtx (tmpName tmp1) := by
      simp [Value.typeOf]; exact (tyCtx_tmp_wt prog hnt tmp1).symm
    exact allWTI_append' (allWTI_append' (allWTI_append' ha_wt
      (allWTI_one (.ifgoto (.not ha_ty))))
      hb_wt)
      (allWTI_cons' (.ifgoto (.not hb_ty))
        (allWTI_cons' (.const htR)
          (allWTI_cons' .goto
            (allWTI_one (.const htR0)))))
  | or a b iha ihb =>

    simp [Program.checkSBool, Bool.and_eq_true] at hchk
    obtain ⟨hca, hcb⟩ := hchk
    have ⟨ha_wt, ha_ty⟩ := iha hca offset nextTmp
    have ⟨hb_wt, hb_ty⟩ := ihb hcb
      (offset + (compileBool a offset nextTmp).1.length + 1)
      ((compileBool a offset nextTmp).2.2 + 1)
    simp only [compileBool]
    refine ⟨?_, .cmp (by simp [ExprHasTy]; exact tyCtx_tmp_wt prog hnt _) (by simp [ExprHasTy])⟩
    let tmp1 := (compileBool a offset nextTmp).2.2
    have htR : (Value.int 0).typeOf = prog.tyCtx (tmpName tmp1) := by
      simp [Value.typeOf]; exact (tyCtx_tmp_wt prog hnt tmp1).symm
    have htR1 : (Value.int 1).typeOf = prog.tyCtx (tmpName tmp1) := by
      simp [Value.typeOf]; exact (tyCtx_tmp_wt prog hnt tmp1).symm
    exact allWTI_append' (allWTI_append' (allWTI_append' ha_wt
      (allWTI_one (.ifgoto ha_ty)))
      hb_wt)
      (allWTI_cons' (.ifgoto hb_ty)
        (allWTI_cons' (.const htR)
          (allWTI_cons' .goto
            (allWTI_one (.const htR1)))))
  | barrRead _arr idx =>
    simp [Program.checkSBool, Bool.and_eq_true, beq_iff_eq] at hchk
    have ⟨⟨_, hety⟩, hci⟩ := hchk
    have ⟨hi_wt, hi_ty⟩ := compileExpr_wt prog hnt idx hci offset nextTmp
    simp only [compileBool]
    exact ⟨allWTI_append' hi_wt (allWTI_one (.arrLoad (tyCtx_btmp_wt prog hnt _) hi_ty hety.symm)),
           .bvar (tyCtx_btmp_wt prog hnt _)⟩
  | fcmp op a b =>
    simp [Program.checkSBool, Bool.and_eq_true] at hchk
    obtain ⟨hca, hcb⟩ := hchk
    have ⟨ha_wt, ha_ty⟩ := compileExpr_float_wt prog hnt a hca offset nextTmp
    have ⟨hb_wt, hb_ty⟩ := compileExpr_float_wt prog hnt b hcb
      (offset + (compileExpr a offset nextTmp).1.length)
      (compileExpr a offset nextTmp).2.2
    simp only [compileBool]
    exact ⟨allWTI_append' ha_wt hb_wt, .fcmp ha_ty hb_ty⟩

-- compileStmt produces well-typed instructions
theorem compileStmt_wt (prog : Program)
    (hnt : Program.noTmpDecls prog.decls = true)
    (s : Stmt) (hchk : Program.checkStmt prog.lookupTy prog.arrayDecls s = true)
    (offset nextTmp : Nat)
    (labels : List (String × Nat) := []) :
    AllWTI prog.tyCtx prog.arrayDecls (compileStmt s offset nextTmp labels).1 := by
  induction s generalizing offset nextTmp labels with
  | skip => simp [compileStmt]; exact allWTI_nil' _ _
  | assign x e =>
    simp [Program.checkStmt, Bool.and_eq_true] at hchk
    obtain ⟨hx, he⟩ := hchk
    have hxty : prog.tyCtx x = .int := tyCtx_of_lookup_wt prog x .int hx
    cases e with
    | lit n =>
      simp only [compileStmt]
      exact allWTI_one (.const (by simp [Value.typeOf]; exact hxty.symm))
    | var y =>
      simp only [compileStmt]
      simp [Program.checkExpr] at he
      have hyty : prog.tyCtx y = .int := tyCtx_of_lookup_wt prog y .int he
      exact allWTI_one (.copy (by rw [hxty, hyty]))
    | bin op a b =>
      simp [Program.checkExpr, Bool.and_eq_true] at he
      obtain ⟨ha, hb⟩ := he
      have ⟨ha_wt, ha_ty⟩ := compileExpr_wt prog hnt a ha offset nextTmp
      have ⟨hb_wt, hb_ty⟩ := compileExpr_wt prog hnt b hb
        (offset + (compileExpr a offset nextTmp).1.length)
        (compileExpr a offset nextTmp).2.2
      simp only [compileStmt]
      exact allWTI_append3 ha_wt hb_wt
        (allWTI_one (.binop hxty ha_ty hb_ty))
    | arrRead _arr idx =>
      simp [Program.checkExpr, Bool.and_eq_true, beq_iff_eq] at he
      have ⟨⟨_, hety⟩, hci⟩ := he
      have ⟨hi_wt, hi_ty⟩ := compileExpr_wt prog hnt idx hci offset nextTmp
      simp only [compileStmt]
      have htmp_ty := tyCtx_tmp_wt prog hnt (compileExpr idx offset nextTmp).2.2
      exact allWTI_append' hi_wt
        (allWTI_cons' (.arrLoad htmp_ty hi_ty hety.symm)
          (allWTI_one (.copy (by rw [hxty, htmp_ty]))))
    | flit _ | fbin _ _ _ | intToFloat _ | floatUnary _ _ | farrRead _ _ =>
      simp [Program.checkExpr] at he
    | floatToInt e =>
      have ⟨he_wt, he_ty⟩ := compileExpr_wt prog hnt (.floatToInt e) he offset nextTmp
      simp only [compileStmt]
      exact allWTI_append' he_wt (allWTI_one (.copy (by rw [hxty, he_ty])))
  | bassign x b =>
    simp [Program.checkStmt, Bool.and_eq_true] at hchk
    obtain ⟨hx, hb⟩ := hchk
    have hxty : prog.tyCtx x = .bool := tyCtx_of_lookup_wt prog x .bool hx
    have ⟨hb_wt, hb_ty⟩ := compileBool_wt prog hnt b hb offset nextTmp
    simp only [compileStmt]
    exact allWTI_append' hb_wt (allWTI_one (.boolop hxty hb_ty))
  | arrWrite _arr idx val =>
    simp [Program.checkStmt, Bool.and_eq_true, beq_iff_eq] at hchk
    obtain ⟨⟨⟨_, hety⟩, hi⟩, hv⟩ := hchk
    have ⟨hi_wt, hi_ty⟩ := compileExpr_wt prog hnt idx hi offset nextTmp
    have ⟨hv_wt, hv_ty⟩ := compileExpr_wt prog hnt val hv
      (offset + (compileExpr idx offset nextTmp).1.length)
      (compileExpr idx offset nextTmp).2.2
    simp only [compileStmt]
    exact allWTI_append3 hi_wt hv_wt (allWTI_one (.arrStore hi_ty hv_ty hety.symm))
  | barrWrite arr idx bval =>
    simp [Program.checkStmt, Bool.and_eq_true, beq_iff_eq] at hchk
    obtain ⟨⟨⟨_, hety⟩, hi⟩, hb⟩ := hchk
    have ⟨hi_wt, hi_ty⟩ := compileExpr_wt prog hnt idx hi offset nextTmp
    have ⟨hb_wt, hb_ty⟩ := compileBool_wt prog hnt bval hb
      (offset + (compileExpr idx offset nextTmp).1.length)
      (compileExpr idx offset nextTmp).2.2
    simp only [compileStmt]
    exact allWTI_append' (allWTI_append' hi_wt hb_wt)
      (allWTI_cons' (.boolop (tyCtx_btmp_wt prog hnt _) hb_ty)
        (allWTI_one (.arrStore hi_ty (tyCtx_btmp_wt prog hnt _) hety.symm)))
  | seq s1 s2 ih1 ih2 =>
    simp [Program.checkStmt, Bool.and_eq_true] at hchk
    obtain ⟨hc1, hc2⟩ := hchk
    simp only [compileStmt]
    exact allWTI_append' (ih1 hc1 offset nextTmp labels)
      (ih2 hc2 (offset + (compileStmt s1 offset nextTmp labels).1.length)
                (compileStmt s1 offset nextTmp labels).2 labels)
  | ite b s1 s2 ih1 ih2 =>
    simp [Program.checkStmt, Bool.and_eq_true] at hchk
    obtain ⟨⟨hcb, hc1⟩, hc2⟩ := hchk
    have ⟨hb_wt, hb_ty⟩ := compileBool_wt prog hnt b hcb offset nextTmp
    simp only [compileStmt]
    -- The compiled code is left-associated:
    -- ((((codeB ++ [ifgoto]) ++ codeElse) ++ [goto]) ++ codeThen)
    have h_else := ih2 hc2
      (offset + (compileBool b offset nextTmp).1.length + 1)
      (compileBool b offset nextTmp).2.2 labels
    have h_then := ih1 hc1
      (offset + (compileBool b offset nextTmp).1.length + 1 +
        (compileStmt s2 (offset + (compileBool b offset nextTmp).1.length + 1)
          (compileBool b offset nextTmp).2.2 labels).1.length + 1)
      (compileStmt s2 (offset + (compileBool b offset nextTmp).1.length + 1)
        (compileBool b offset nextTmp).2.2 labels).2 labels
    exact allWTI_append'
      (allWTI_append'
        (allWTI_append'
          (allWTI_append' hb_wt (allWTI_one (.ifgoto hb_ty)))
          h_else)
        (allWTI_one .goto))
      h_then
  | loop b body ih =>
    simp [Program.checkStmt, Bool.and_eq_true] at hchk
    obtain ⟨hcb, hcbody⟩ := hchk
    have ⟨hb_wt, hb_ty⟩ := compileBool_wt prog hnt b hcb offset nextTmp
    simp only [compileStmt]
    have h_body := ih hcbody
      (offset + (compileBool b offset nextTmp).1.length + 1)
      (compileBool b offset nextTmp).2.2 labels
    exact allWTI_append'
      (allWTI_append'
        (allWTI_append' hb_wt (allWTI_one (.ifgoto (.not hb_ty))))
        h_body)
      (allWTI_one .goto)
  | fassign x e =>
    simp [Program.checkStmt, Bool.and_eq_true] at hchk
    obtain ⟨hx, he⟩ := hchk
    have hxty : prog.tyCtx x = .float := tyCtx_of_lookup_wt prog x .float hx
    cases e with
    | flit f =>
      simp only [compileStmt]
      exact allWTI_one (.const (by simp [Value.typeOf]; exact hxty.symm))
    | var y =>
      simp only [compileStmt]
      simp [Program.checkExpr] at he
      have hyty : prog.tyCtx y = .float := tyCtx_of_lookup_wt prog y .float he
      exact allWTI_one (.copy (by rw [hxty, hyty]))
    | fbin op a b =>
      simp [Program.checkExpr, Bool.and_eq_true] at he
      obtain ⟨ha, hb⟩ := he
      have ⟨ha_wt, ha_ty⟩ := compileExpr_float_wt prog hnt a ha offset nextTmp
      have ⟨hb_wt, hb_ty⟩ := compileExpr_float_wt prog hnt b hb
        (offset + (compileExpr a offset nextTmp).1.length)
        (compileExpr a offset nextTmp).2.2
      simp only [compileStmt]
      exact allWTI_append3 ha_wt hb_wt
        (allWTI_one (.fbinop hxty ha_ty hb_ty))
    | intToFloat e =>
      simp [Program.checkExpr] at he
      have ⟨he_wt, he_ty⟩ := compileExpr_wt prog hnt e he offset nextTmp
      simp only [compileStmt]
      exact allWTI_append' he_wt
        (allWTI_one (.intToFloat hxty he_ty))
    | floatUnary op e =>
      simp [Program.checkExpr] at he
      have ⟨he_wt, he_ty⟩ := compileExpr_float_wt prog hnt e he offset nextTmp
      simp only [compileStmt]
      exact allWTI_append' he_wt
        (allWTI_one (.floatUnary hxty he_ty))
    | farrRead arr idx =>
      simp [Program.checkExpr, Bool.and_eq_true, beq_iff_eq] at he
      have ⟨⟨_, hety⟩, hci⟩ := he
      have ⟨hi_wt, hi_ty⟩ := compileExpr_wt prog hnt idx hci offset nextTmp
      simp only [compileStmt]
      have htmp_ty := tyCtx_ftmp_wt prog hnt (compileExpr idx offset nextTmp).2.2
      exact allWTI_append' hi_wt
        (allWTI_cons' (.arrLoad htmp_ty hi_ty hety.symm)
          (allWTI_one (.copy (by rw [hxty, htmp_ty]))))
    | floatToInt _ | lit _ | bin _ _ _ | arrRead _ _ =>
      simp [Program.checkExpr] at he
  | farrWrite arr idx val =>
    simp [Program.checkStmt, Bool.and_eq_true, beq_iff_eq] at hchk
    obtain ⟨⟨⟨_, hety⟩, hi⟩, hv⟩ := hchk
    have ⟨hi_wt, hi_ty⟩ := compileExpr_wt prog hnt idx hi offset nextTmp
    have ⟨hv_wt, hv_ty⟩ := compileExpr_float_wt prog hnt val hv
      (offset + (compileExpr idx offset nextTmp).1.length)
      (compileExpr idx offset nextTmp).2.2
    simp only [compileStmt]
    exact allWTI_append3 hi_wt hv_wt (allWTI_one (.arrStore hi_ty hv_ty hety.symm))
  | label _ =>
    simp [compileStmt]; exact allWTI_nil' _ _
  | goto lbl =>
    simp [compileStmt]; exact allWTI_one .goto
  | ifgoto b lbl =>
    simp only [Program.checkStmt] at hchk
    simp only [compileStmt]
    have ⟨hb_wt, hb_ty⟩ := compileBool_wt prog hnt b hchk offset nextTmp
    exact allWTI_append' hb_wt (allWTI_one (.ifgoto hb_ty))
  | print fmt args =>
    simp only [Program.checkStmt] at hchk
    simp only [compileStmt]
    exact allWTI_append' (compileExprs_wt prog hnt args offset nextTmp hchk) (allWTI_one .print)
  | printInt e =>
    simp only [Program.checkStmt] at hchk
    simp only [compileStmt]
    have ⟨he_wt, he_ty⟩ := compileExpr_wt prog hnt e hchk offset nextTmp
    exact allWTI_append' he_wt (allWTI_one (.printInt he_ty))
  | printBool b =>
    simp only [Program.checkStmt] at hchk
    simp only [compileStmt]
    have ⟨hb_wt, hb_ty⟩ := compileBool_wt prog hnt b hchk offset nextTmp
    have htInt := tyCtx_tmp_wt prog hnt (compileBool b offset nextTmp).2.2
    -- Output: (codeB ++ [4 conv instrs]) ++ [printBool tmp]
    refine allWTI_append' (allWTI_append' hb_wt ?_) (allWTI_one (.printBool (Or.inr htInt)))
    intro instr hmem
    simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl
    · exact .ifgoto hb_ty
    · exact .const (by simp [Value.typeOf, htInt])
    · exact .goto
    · exact .const (by simp [Value.typeOf, htInt])
  | printFloat e =>
    simp only [Program.checkStmt] at hchk
    simp only [compileStmt]
    have ⟨he_wt, he_ty⟩ := compileExpr_float_wt prog hnt e hchk offset nextTmp
    exact allWTI_append' he_wt (allWTI_one (.printFloat he_ty))
  | printString lit =>
    simp only [compileStmt]
    exact allWTI_one .printString

-- initCode produces well-typed instructions
theorem initCode_wt (prog : Program)
    (hnd : Program.noDups (prog.decls.map Prod.fst) = true) :
    AllWTI prog.tyCtx prog.arrayDecls (Program.initCode prog.decls) := by
  intro instr hmem
  simp only [Program.initCode, List.mem_map] at hmem
  obtain ⟨⟨x, ty⟩, hmem_decl, hgen⟩ := hmem
  have hlookup : prog.decls.lookup x = some ty :=
    lookup_of_mem_noDups_wt hmem_decl hnd
  have hty : prog.tyCtx x = ty := tyCtx_of_lookup_wt prog x ty hlookup
  cases ty with
  | int =>
    simp at hgen; subst hgen
    exact .const (by simp [Value.typeOf]; exact hty.symm)
  | bool =>
    simp at hgen; subst hgen
    exact .const (by simp [Value.typeOf]; exact hty.symm)
  | float =>
    simp at hgen; subst hgen
    exact .const (by simp [Value.typeOf]; exact hty.symm)

namespace Program  -- reopen namespace

/-- **Key theorem**: A program that passes the static type checker compiles to
    a well-typed TAC program. Combined with the progress theorem from Semantics,
    this guarantees that no type errors can occur at runtime — only division by
    zero can cause the program to get stuck.

    Note: `prog.tyCtx` maps declared variables to their declared type,
    int temporaries (`__tN`) to `.int`, and float temporaries (`__ftN`) to `.float`.
    All other undeclared variables default to `.int`. -/
theorem compileToTAC_wellTyped (prog : Program) (h : prog.typeCheck = true) :
    WellTypedProg prog.tyCtx prog.compileToTAC := by
  unfold typeCheck at h; simp only [Bool.and_eq_true] at h
  have hnd := h.1.1
  have hnt := h.1.2
  have hchk := h.2
  have : prog.compileToTAC.code = (initCode prog.decls ++
      (compileStmt prog.body (initCode prog.decls).length 0
        (collectLabels prog.body (initCode prog.decls).length)).1 ++ [TAC.halt]).toArray :=
    by simp [Program.compileToTAC]
  exact allWTI_toArray' this rfl (allWTI_append3 (initCode_wt prog hnd)
    (compileStmt_wt prog hnt prog.body hchk _ _
      (collectLabels prog.body (initCode prog.decls).length)) (allWTI_one .halt))


/-- `Value.ofBitVec ty 0 = ty.defaultVal` -/
private theorem ofBitVec_zero_eq_defaultVal (ty : VarTy) :
    Value.ofBitVec ty 0 = ty.defaultVal := by
  cases ty <;> simp [Value.ofBitVec, VarTy.defaultVal]

/-- For well-typed programs, `Store.typedInit prog.tyCtx = prog.initStore`.
    Both zero-initialize each variable by type: declared variables get their
    type-appropriate default, and undeclared variables get int zero (or float
    zero for float temporaries). -/
theorem typedInit_eq_initStore (prog : Program) (htc : prog.typeCheck = true) :
    Store.typedInit prog.tyCtx = prog.initStore := by
  have hnd := typeCheck_noDups prog htc
  funext v
  simp only [Store.typedInit, initStore, Program.tyCtx, Program.lookupTy]
  cases hlook : prog.decls.lookup v with
  | none =>
    -- v not found in decls: both sides give initStoreBase v
    simp only [Option.getD]
    have hmem : v ∉ prog.decls.map Prod.fst := by
      intro hmem; obtain ⟨⟨w, ty⟩, hp, hw⟩ := List.exists_of_mem_map hmem
      simp only at hw; subst hw
      -- w ∈ decls so lookup w ≠ none, contradicting hlook
      have : prog.decls.lookup w ≠ none := by
        intro habs
        rw [List.lookup_eq_none_iff] at habs
        have := habs ⟨w, ty⟩ hp
        simp [bne] at this
      exact this hlook
    rw [initFold_notMem prog.decls initStoreBase v hmem]
    simp only [initStoreBase, defaultVarTy]; split <;> simp [Value.ofBitVec]
  | some ty =>
    -- v found with type ty: both sides give ty.defaultVal
    simp only [Option.getD]
    have hmem : (v, ty) ∈ prog.decls := by
      rw [List.lookup_eq_some_iff] at hlook
      obtain ⟨l₁, l₂, heq, _⟩ := hlook
      rw [heq]; exact List.mem_append_right _ (.head _)
    rw [initFold_declared prog.decls initStoreBase v ty hmem hnd,
        ofBitVec_zero_eq_defaultVal]

/-- **Corollary**: A type-checked program with a well-typed initial store
    always makes progress. The next configuration may be `run`, `halt`, or
    `error` (for div-by-zero). This follows directly from `compileToTAC_wellTyped`
    and the progress theorem (`Step.progress`). -/
theorem no_type_stuck (prog : Program)
    (htc : prog.typeCheck = true)
    (σ : Store) (hts : TypedStore prog.tyCtx σ)
    (pc : Nat) (hpc : pc < prog.compileToTAC.size) :
    ∀ am, ∃ c', Step prog.compileToTAC (Cfg.run pc σ am) c' :=
  fun am => Step.progress prog.compileToTAC pc σ am prog.tyCtx hpc
    (prog.compileToTAC_wellTyped htc) hts

-- ============================================================
-- § 5g. Compiled programs are step-closed in bounds
-- ============================================================

/-- All goto/ifgoto targets in `code` are ≤ `bound`. -/
def AllJumpsLe (bound : Nat) (code : List TAC) : Prop :=
  ∀ instr, instr ∈ code →
    match instr with
    | .goto l => l ≤ bound
    | .ifgoto _ l => l ≤ bound
    | _ => True

@[simp] theorem AllJumpsLe_nil : AllJumpsLe bound ([] : List TAC) := by
  intro _ h; simp at h

theorem AllJumpsLe_append (h1 : AllJumpsLe b l1) (h2 : AllJumpsLe b l2) :
    AllJumpsLe b (l1 ++ l2) :=
  fun instr hmem => (List.mem_append.mp hmem).elim (h1 instr) (h2 instr)

theorem AllJumpsLe_mono (h : AllJumpsLe b1 code) (hle : b1 ≤ b2) :
    AllJumpsLe b2 code := by
  intro instr hmem
  have hi := h instr hmem
  cases instr with
  | goto l => exact Nat.le_trans hi hle
  | ifgoto _ l => exact Nat.le_trans hi hle
  | _ => trivial

theorem AllJumpsLe_single_goto (hle : l ≤ bound) :
    AllJumpsLe bound ([TAC.goto l] : List TAC) := by
  intro instr hmem; simp at hmem; subst hmem; exact hle

theorem AllJumpsLe_single_ifgoto {be : BoolExpr} (hle : l ≤ bound) :
    AllJumpsLe bound ([TAC.ifgoto be l] : List TAC) := by
  intro instr hmem; simp at hmem; subst hmem; exact hle

/-- Code with no goto/ifgoto/halt satisfies AllJumpsLe for any bound. -/
def IsSeqInstr (instr : TAC) : Prop :=
  match instr with
  | .const _ _ | .copy _ _ | .binop _ _ _ _ | .boolop _ _
  | .arrLoad _ _ _ _ | .arrStore _ _ _ _
  | .fbinop _ _ _ _ | .intToFloat _ _ | .floatToInt _ _ | .floatUnary _ _ _
  | .print _ _ | .printInt _ | .printBool _ | .printFloat _ | .printString _ => True
  | _ => False

theorem AllJumpsLe_of_allSeq {code : List TAC}
    (h : ∀ instr, instr ∈ code → IsSeqInstr instr) : AllJumpsLe bound code := by
  intro instr hmem; have := h instr hmem; cases instr <;> simp_all [IsSeqInstr]

theorem compileExpr_allSeq (e : SExpr) (offset nextTmp : Nat) :
    ∀ instr, instr ∈ (compileExpr e offset nextTmp).1 → IsSeqInstr instr := by
  induction e generalizing offset nextTmp with
  | lit _ => intro instr hmem; simp [compileExpr] at hmem; subst hmem; trivial
  | var _ => intro _ hmem; simp [compileExpr] at hmem
  | bin _ a b iha ihb =>
    intro instr hmem; simp [compileExpr, List.mem_append] at hmem
    rcases hmem with ha | hb | rfl
    · exact iha _ _ instr ha
    · exact ihb _ _ instr hb
    · trivial
  | arrRead _ idx ih =>
    intro instr hmem; simp [compileExpr, List.mem_append] at hmem
    rcases hmem with hi | rfl
    · exact ih _ _ instr hi
    · trivial
  | flit _ => intro instr hmem; simp [compileExpr] at hmem; subst hmem; trivial
  | fbin _ a b iha ihb =>
    intro instr hmem; simp [compileExpr, List.mem_append] at hmem
    rcases hmem with ha | hb | rfl
    · exact iha _ _ instr ha
    · exact ihb _ _ instr hb
    · trivial
  | intToFloat e ih =>
    intro instr hmem; simp [compileExpr, List.mem_append] at hmem
    rcases hmem with he | rfl
    · exact ih _ _ instr he
    · trivial
  | floatToInt e ih =>
    intro instr hmem; simp [compileExpr, List.mem_append] at hmem
    rcases hmem with he | rfl
    · exact ih _ _ instr he
    · trivial
  | floatUnary op e ih =>
    intro instr hmem; simp [compileExpr, List.mem_append] at hmem
    rcases hmem with he | rfl
    · exact ih _ _ instr he
    · trivial
  | farrRead _ idx ih =>
    intro instr hmem; simp [compileExpr, List.mem_append] at hmem
    rcases hmem with hi | rfl
    · exact ih _ _ instr hi
    · trivial

theorem compileBool_allJumpsLe (b : SBool) (offset nextTmp bound : Nat)
    (hbound : offset + (compileBool b offset nextTmp).1.length ≤ bound) :
    AllJumpsLe bound (compileBool b offset nextTmp).1 := by
  induction b generalizing offset nextTmp bound with
  | lit _ => exact AllJumpsLe_nil
  | bvar _ => exact AllJumpsLe_nil
  | cmp _ a b =>
    exact AllJumpsLe_of_allSeq (fun instr hmem => by
      simp [compileBool, List.mem_append] at hmem
      rcases hmem with ha | hb
      · exact compileExpr_allSeq a _ _ instr ha
      · exact compileExpr_allSeq b _ _ instr hb)
  | not _ ih =>
    simp only [compileBool] at hbound ⊢
    exact ih offset nextTmp bound hbound
  | and _ _ iha ihb =>
    simp only [compileBool, List.length_append, List.length_cons, List.length_nil] at hbound ⊢
    apply AllJumpsLe_append
    · apply AllJumpsLe_append
      · apply AllJumpsLe_append
        · exact AllJumpsLe_mono (iha offset nextTmp _ (Nat.le_refl _)) (by omega)
        · exact AllJumpsLe_single_ifgoto (by omega)
      · exact AllJumpsLe_mono (ihb _ _ _ (Nat.le_refl _)) (by omega)
    · intro instr hmem
      simp [List.mem_cons] at hmem
      rcases hmem with rfl | rfl | rfl | rfl
      · exact Nat.le_trans (by omega) hbound  -- ifgoto: falseL ≤ bound
      · trivial  -- const
      · exact Nat.le_trans (by omega) hbound  -- goto: endL ≤ bound
      · trivial  -- const
  | or _ _ iha ihb =>
    simp only [compileBool, List.length_append, List.length_cons, List.length_nil] at hbound ⊢
    apply AllJumpsLe_append
    · apply AllJumpsLe_append
      · apply AllJumpsLe_append
        · exact AllJumpsLe_mono (iha offset nextTmp _ (Nat.le_refl _)) (by omega)
        · exact AllJumpsLe_single_ifgoto (by omega)
      · exact AllJumpsLe_mono (ihb _ _ _ (Nat.le_refl _)) (by omega)
    · intro instr hmem
      simp [List.mem_cons] at hmem
      rcases hmem with rfl | rfl | rfl | rfl
      · exact Nat.le_trans (by omega) hbound
      · trivial
      · exact Nat.le_trans (by omega) hbound
      · trivial
  | barrRead arr idx =>
    simp only [compileBool, List.length_append, List.length_cons, List.length_nil] at hbound ⊢
    exact AllJumpsLe_of_allSeq (fun instr hmem => by
      simp [List.mem_append] at hmem
      rcases hmem with hi | rfl
      · exact compileExpr_allSeq idx _ _ instr hi
      · trivial)
  | fcmp _ a b =>
    exact AllJumpsLe_of_allSeq (fun instr hmem => by
      simp [compileBool, List.mem_append] at hmem
      rcases hmem with ha | hb
      · exact compileExpr_allSeq a _ _ instr ha
      · exact compileExpr_allSeq b _ _ instr hb)

theorem initCode_allSeq (decls : List (Var × VarTy)) :
    ∀ instr, instr ∈ initCode decls → IsSeqInstr instr := by
  intro instr hmem; simp only [initCode, List.mem_map] at hmem
  obtain ⟨⟨_, ty⟩, _, rfl⟩ := hmem; cases ty <;> trivial

theorem compileExprs_allSeq (args : List SExpr) (offset nextTmp : Nat) :
    ∀ instr, instr ∈ (compileExprs args offset nextTmp).1 → IsSeqInstr instr := by
  induction args generalizing offset nextTmp with
  | nil => intro _ hmem; simp [compileExprs] at hmem
  | cons e rest ih =>
    intro instr hmem
    simp only [compileExprs, List.mem_append] at hmem
    rcases hmem with he | hrest
    · exact compileExpr_allSeq e _ _ instr he
    · exact ih _ _ instr hrest

/-- compileExpr output has simple ops (it never emits boolop/ifgoto). -/
private theorem compileExpr_hasSimpleOps_mem (e : SExpr) (offset nextTmp : Nat) :
    ∀ instr ∈ (compileExpr e offset nextTmp).1, instr.hasSimpleOps = true := by
  intro instr hmem
  exact List.all_eq_true.mp (compileExpr_simpleOps e offset nextTmp) instr hmem

/-- compileExprs output has simple ops. -/
private theorem compileExprs_hasSimpleOps_mem (args : List SExpr) (offset nextTmp : Nat) :
    ∀ instr ∈ (compileExprs args offset nextTmp).1, instr.hasSimpleOps = true := by
  induction args generalizing offset nextTmp with
  | nil => intro _ hmem; simp [compileExprs] at hmem
  | cons e rest ih =>
    intro instr hmem
    simp only [compileExprs, List.mem_append] at hmem
    rcases hmem with he | hrest
    · exact compileExpr_hasSimpleOps_mem e _ _ instr he
    · exact ih _ _ instr hrest

/-- compileBool output has simple ops (bridge from Prop form to Bool). -/
private theorem compileBool_hasSimpleOps_mem (b : SBool) (offset nextTmp : Nat) :
    ∀ instr ∈ (compileBool b offset nextTmp).1, instr.hasSimpleOps = true := by
  intro instr hmem
  have := compileBool_code_simpleOps b offset nextTmp instr hmem
  cases instr <;> simp_all [TAC.hasSimpleOps]

/-- All instructions in compiled statement code have simple boolean ops. -/
theorem compileStmt_code_simpleOps (s : Stmt) (offset nextTmp : Nat)
    (labels : List (String × Nat)) :
    ∀ instr ∈ (compileStmt s offset nextTmp labels).1, instr.hasSimpleOps = true := by
  induction s generalizing offset nextTmp labels with
  | skip => intro _ hmem; simp [compileStmt] at hmem
  | assign x e =>
    cases e with
    | lit _ => intro _ hmem; simp [compileStmt] at hmem; subst hmem; rfl
    | var _ => intro _ hmem; simp [compileStmt] at hmem; subst hmem; rfl
    | bin _ a b =>
      intro instr hmem; simp [compileStmt, List.mem_append] at hmem
      rcases hmem with ha | hb | rfl
      · exact compileExpr_hasSimpleOps_mem a _ _ instr ha
      · exact compileExpr_hasSimpleOps_mem b _ _ instr hb
      · rfl
    | arrRead _ idx =>
      intro instr hmem; simp [compileStmt, List.mem_append] at hmem
      rcases hmem with hi | rfl | rfl
      · exact compileExpr_hasSimpleOps_mem idx _ _ instr hi
      · rfl
      · rfl
    | _ =>
      intro instr hmem; simp [compileStmt, List.mem_append] at hmem
      rcases hmem with he | rfl
      · exact compileExpr_hasSimpleOps_mem _ _ _ instr he
      · rfl
  | bassign _ b =>
    simp only [compileStmt]
    intro instr hmem
    simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with hcode | rfl
    · exact compileBool_hasSimpleOps_mem b _ _ instr hcode
    · simp [TAC.hasSimpleOps, compileBool_hasSimpleOps]
  | arrWrite _ idx val =>
    intro instr hmem; simp [compileStmt, List.mem_append] at hmem
    rcases hmem with hi | hv | rfl
    · exact compileExpr_hasSimpleOps_mem idx _ _ instr hi
    · exact compileExpr_hasSimpleOps_mem val _ _ instr hv
    · rfl
  | barrWrite arr idx bval =>
    match hci : compileExpr idx offset nextTmp with
    | (codeIdx, vIdx, tmp1) =>
    match hcb : compileBool bval (offset + codeIdx.length) tmp1 with
    | (codeBool, be, tmp2) =>
    have hbe : be.hasSimpleOps = true := by
      have : be = (compileBool bval (offset + codeIdx.length) tmp1).2.1 := by simp [hcb]
      rw [this]; exact compileBool_hasSimpleOps bval _ _
    simp only [compileStmt, hci, hcb]
    intro instr hmem
    simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with (hi | hb) | rfl | rfl
    · have := compileExpr_hasSimpleOps_mem idx offset nextTmp instr
      simp [hci] at this; exact this hi
    · have := compileBool_hasSimpleOps_mem bval (offset + codeIdx.length) tmp1 instr
      simp [hcb] at this; exact this hb
    · simp [TAC.hasSimpleOps, hbe]
    · rfl
  | seq s1 s2 ih1 ih2 =>
    intro instr hmem
    simp only [compileStmt, List.mem_append] at hmem
    rcases hmem with h1 | h2
    · exact ih1 _ _ labels instr h1
    · exact ih2 _ _ labels instr h2
  | ite b s1 s2 ih1 ih2 =>
    match hcb : compileBool b offset nextTmp with
    | (codeB, be, tmpB) =>
    match hs2 : compileStmt s2 (offset + codeB.length + 1) tmpB labels with
    | (codeElse, tmpE) =>
    match hs1 : compileStmt s1 (offset + codeB.length + 1 + codeElse.length + 1) tmpE labels with
    | (codeThen, _) =>
    have hbe : be.hasSimpleOps = true := by
      have : be = (compileBool b offset nextTmp).2.1 := by simp [hcb]
      rw [this]; exact compileBool_hasSimpleOps b _ _
    simp only [compileStmt, hcb, hs2, hs1]
    intro instr hmem
    simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    -- structure: ((((∈ codeB ∨ = ifgoto) ∨ ∈ codeElse) ∨ = goto) ∨ ∈ codeThen)
    rcases hmem with (((hb | rfl) | h2) | rfl) | h1
    · have := compileBool_hasSimpleOps_mem b offset nextTmp instr
      simp [hcb] at this; exact this hb
    · simp [TAC.hasSimpleOps, hbe]
    · have h2' := ih2 (offset + codeB.length + 1) tmpB labels instr
      simp only [hs2] at h2'; exact h2' h2
    · rfl
    · have h1' := ih1 (offset + codeB.length + 1 + codeElse.length + 1) tmpE labels instr
      simp only [hs1] at h1'; exact h1' h1
  | loop b body ih =>
    match hcb : compileBool b offset nextTmp with
    | (codeB, be, tmpB) =>
    match hsbody : compileStmt body (offset + codeB.length + 1) tmpB labels with
    | (codeBody, _) =>
    have hbe : be.hasSimpleOps = true := by
      have : be = (compileBool b offset nextTmp).2.1 := by simp [hcb]
      rw [this]; exact compileBool_hasSimpleOps b _ _
    simp only [compileStmt, hcb, hsbody]
    intro instr hmem
    simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    -- structure: (((∈ codeB ∨ = ifgoto) ∨ ∈ codeBody) ∨ = goto)
    rcases hmem with ((hb | rfl) | hbody) | rfl
    · have := compileBool_hasSimpleOps_mem b offset nextTmp instr
      simp [hcb] at this; exact this hb
    · simp [TAC.hasSimpleOps, BoolExpr.hasSimpleOps, hbe]
    · have hih := ih (offset + codeB.length + 1) tmpB labels instr
      simp only [hsbody] at hih; exact hih hbody
    · rfl
  | fassign x e =>
    cases e with
    | flit _ => intro _ hmem; simp [compileStmt] at hmem; subst hmem; rfl
    | var _ => intro _ hmem; simp [compileStmt] at hmem; subst hmem; rfl
    | fbin _ a b =>
      intro instr hmem; simp [compileStmt, List.mem_append] at hmem
      rcases hmem with ha | hb | rfl
      · exact compileExpr_hasSimpleOps_mem a _ _ instr ha
      · exact compileExpr_hasSimpleOps_mem b _ _ instr hb
      · rfl
    | intToFloat e =>
      intro instr hmem; simp [compileStmt, List.mem_append] at hmem
      rcases hmem with he | rfl
      · exact compileExpr_hasSimpleOps_mem e _ _ instr he
      · rfl
    | floatUnary _ e =>
      intro instr hmem; simp [compileStmt, List.mem_append] at hmem
      rcases hmem with he | rfl
      · exact compileExpr_hasSimpleOps_mem e _ _ instr he
      · rfl
    | farrRead _ idx =>
      intro instr hmem; simp [compileStmt, List.mem_append] at hmem
      rcases hmem with hi | rfl | rfl
      · exact compileExpr_hasSimpleOps_mem idx _ _ instr hi
      · rfl
      · rfl
    | _ =>
      intro instr hmem; simp [compileStmt, List.mem_append] at hmem
      rcases hmem with he | rfl
      · exact compileExpr_hasSimpleOps_mem _ _ _ instr he
      · rfl
  | farrWrite _ idx val =>
    intro instr hmem; simp [compileStmt, List.mem_append] at hmem
    rcases hmem with hi | hv | rfl
    · exact compileExpr_hasSimpleOps_mem idx _ _ instr hi
    · exact compileExpr_hasSimpleOps_mem val _ _ instr hv
    · rfl
  | label _ => intro _ hmem; simp [compileStmt] at hmem
  | goto _ => intro _ hmem; simp [compileStmt] at hmem; subst hmem; rfl
  | ifgoto b _ =>
    match hcb : compileBool b offset nextTmp with
    | (codeB, be, tmpB) =>
    have hbe : be.hasSimpleOps = true := by
      have : be = (compileBool b offset nextTmp).2.1 := by simp [hcb]
      rw [this]; exact compileBool_hasSimpleOps b _ _
    simp only [compileStmt, hcb]
    intro instr hmem
    simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with hb | rfl
    · have := compileBool_hasSimpleOps_mem b offset nextTmp instr
      simp [hcb] at this; exact this hb
    · simp [TAC.hasSimpleOps, hbe]
  | print _ args =>
    intro instr hmem; simp [compileStmt, List.mem_append] at hmem
    rcases hmem with he | rfl
    · exact compileExprs_hasSimpleOps_mem args _ _ instr he
    · rfl
  | printInt e =>
    intro instr hmem; simp [compileStmt, List.mem_append] at hmem
    rcases hmem with he | rfl
    · exact compileExpr_hasSimpleOps_mem e _ _ instr he
    · rfl
  | printBool b =>
    intro instr hmem; simp only [compileStmt] at hmem
    simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with (hb | hconv) | rfl
    · exact compileBool_hasSimpleOps_mem b offset nextTmp instr hb
    · -- 4 conv instrs (ifgoto + 3 simple ones)
      rcases hconv with rfl | rfl | rfl | rfl
      · simp [TAC.hasSimpleOps, compileBool_hasSimpleOps]
      · rfl
      · rfl
      · rfl
    · rfl
  | printFloat e =>
    intro instr hmem; simp [compileStmt, List.mem_append] at hmem
    rcases hmem with he | rfl
    · exact compileExpr_hasSimpleOps_mem e _ _ instr he
    · rfl
  | printString lit =>
    intro instr hmem; simp [compileStmt] at hmem; subst hmem; rfl

/-- All values in a label map are ≤ bound. -/
def AllLabelsLe (bound : Nat) (labels : List (String × Nat)) : Prop :=
  ∀ k v, (k, v) ∈ labels → v ≤ bound

theorem AllLabelsLe_lookup {labels : List (String × Nat)} {bound : Nat}
    (h : AllLabelsLe bound labels) (lbl : String) :
    (labels.lookup lbl).getD 0 ≤ bound := by
  induction labels with
  | nil => simp [List.lookup, Option.getD]
  | cons p ps ih =>
    obtain ⟨k, v⟩ := p
    simp only [List.lookup]
    split
    · -- lbl = k, lookup returns some v
      simp [Option.getD]
      exact h k v (by simp)
    · -- lbl ≠ k, recurse
      exact ih (fun k' v' hmem => h k' v' (by simp [hmem]))

-- Code length lemmas: static code length functions match compiled output length

theorem compileExpr_length (e : SExpr) (offset nextTmp : Nat) :
    (compileExpr e offset nextTmp).1.length = exprCodeLen e := by
  induction e generalizing offset nextTmp with
  | lit _ | var _ => simp [compileExpr, exprCodeLen]
  | bin _ a b iha ihb =>
    simp [compileExpr, exprCodeLen, List.length_append, iha, ihb]; omega
  | flit _ => simp [compileExpr, exprCodeLen]
  | fbin _ a b iha ihb =>
    simp [compileExpr, exprCodeLen, List.length_append, iha, ihb]; omega
  | arrRead _ idx ih =>
    simp [compileExpr, exprCodeLen, List.length_append, ih]
  | farrRead _ idx ih =>
    simp [compileExpr, exprCodeLen, List.length_append, ih]
  | intToFloat e ih =>
    simp [compileExpr, exprCodeLen, List.length_append, ih]
  | floatToInt e ih =>
    simp [compileExpr, exprCodeLen, List.length_append, ih]
  | floatUnary op e ih =>
    simp [compileExpr, exprCodeLen, List.length_append, ih]

theorem compileExprs_length (args : List SExpr) (offset nextTmp : Nat) :
    (compileExprs args offset nextTmp).1.length = exprsCodeLen args := by
  induction args generalizing offset nextTmp with
  | nil => simp [compileExprs, exprsCodeLen]
  | cons e rest ih =>
    simp only [compileExprs, exprsCodeLen, List.length_append]
    rw [compileExpr_length, ih]

theorem compileBool_length (b : SBool) (offset nextTmp : Nat) :
    (compileBool b offset nextTmp).1.length = boolCodeLen b := by
  induction b generalizing offset nextTmp with
  | lit _ | bvar _ => simp [compileBool, boolCodeLen]
  | cmp _ a b =>
    simp [compileBool, boolCodeLen, List.length_append, compileExpr_length]
  | not b ih =>
    simp [compileBool, boolCodeLen, ih]
  | and a b iha ihb =>
    simp [compileBool, boolCodeLen, List.length_append, iha, ihb]; omega
  | or a b iha ihb =>
    simp [compileBool, boolCodeLen, List.length_append, iha, ihb]; omega
  | barrRead _ idx =>
    simp [compileBool, boolCodeLen, List.length_append, compileExpr_length]
  | fcmp _ a b =>
    simp [compileBool, boolCodeLen, List.length_append, compileExpr_length]

theorem compileStmt_length (s : Stmt) (offset nextTmp : Nat)
    (labels : List (String × Nat)) :
    (compileStmt s offset nextTmp labels).1.length = stmtCodeLen s := by
  induction s generalizing offset nextTmp labels with
  | skip => simp [compileStmt, stmtCodeLen]
  | assign x e =>
    cases e with
    | lit _ => simp [compileStmt, stmtCodeLen]
    | var _ => simp [compileStmt, stmtCodeLen]
    | bin _ a b =>
      simp [compileStmt, stmtCodeLen, List.length_append, compileExpr_length]; omega
    | arrRead _ idx =>
      simp [compileStmt, stmtCodeLen, List.length_append, compileExpr_length]
    | flit _ | fbin _ _ _ | intToFloat _ | floatUnary _ _ | farrRead _ _ | floatToInt _ =>
      simp [compileStmt, stmtCodeLen, List.length_append, compileExpr_length]; try omega
  | bassign _ b =>
    simp [compileStmt, stmtCodeLen, List.length_append, compileBool_length]
  | arrWrite _ idx val =>
    simp [compileStmt, stmtCodeLen, List.length_append, compileExpr_length]; omega
  | barrWrite _ idx bval =>
    simp [compileStmt, stmtCodeLen, List.length_append, compileExpr_length, compileBool_length]; omega
  | seq s1 s2 ih1 ih2 =>
    simp [compileStmt, stmtCodeLen, List.length_append, ih1, ih2]
  | ite b s1 s2 ih1 ih2 =>
    simp [compileStmt, stmtCodeLen, List.length_append, compileBool_length, ih1, ih2]
    omega
  | loop b body ih =>
    simp [compileStmt, stmtCodeLen, List.length_append, compileBool_length, ih]
    omega
  | fassign x e =>
    cases e with
    | flit _ => simp [compileStmt, stmtCodeLen]
    | var _ => simp [compileStmt, stmtCodeLen]
    | fbin _ a b =>
      simp [compileStmt, stmtCodeLen, List.length_append, compileExpr_length]; omega
    | intToFloat e =>
      simp [compileStmt, stmtCodeLen, List.length_append, compileExpr_length]
    | floatUnary op e =>
      simp [compileStmt, stmtCodeLen, List.length_append, compileExpr_length]
    | farrRead _ idx =>
      simp [compileStmt, stmtCodeLen, List.length_append, compileExpr_length]
    | _ =>
      simp [compileStmt, stmtCodeLen, List.length_append, compileExpr_length]
  | farrWrite _ idx val =>
    simp [compileStmt, stmtCodeLen, List.length_append, compileExpr_length]; omega
  | label _ => simp [compileStmt, stmtCodeLen]
  | goto _ => simp [compileStmt, stmtCodeLen]
  | ifgoto b _ =>
    simp [compileStmt, stmtCodeLen, List.length_append, compileBool_length]
  | print fmt args =>
    simp only [compileStmt, stmtCodeLen, List.length_append, List.length_cons, List.length_nil]
    rw [compileExprs_length]
  | printInt e =>
    simp [compileStmt, stmtCodeLen, List.length_append, compileExpr_length]
  | printBool b =>
    simp [compileStmt, stmtCodeLen, List.length_append, compileBool_length]
  | printFloat e =>
    simp [compileStmt, stmtCodeLen, List.length_append, compileExpr_length]
  | printString lit =>
    simp [compileStmt, stmtCodeLen]

-- collectLabels produces label values ≤ offset + stmtCodeLen s
theorem collectLabels_allLabelsLe (s : Stmt) (offset : Nat) :
    AllLabelsLe (offset + stmtCodeLen s) (collectLabels s offset) := by
  induction s generalizing offset with
  | label name =>
    intro k v hmem
    simp [collectLabels] at hmem
    obtain ⟨rfl, rfl⟩ := hmem
    omega
  | seq s1 s2 ih1 ih2 =>
    intro k v hmem
    simp [collectLabels] at hmem
    simp only [stmtCodeLen]
    rcases hmem with h1 | h2
    · have := ih1 offset k v h1; omega
    · have := ih2 (offset + stmtCodeLen s1) k v h2; omega
  | ite b s1 s2 ih1 ih2 =>
    intro k v hmem
    simp [collectLabels] at hmem
    simp only [stmtCodeLen]
    rcases hmem with h2 | h1
    · have := ih2 (offset + boolCodeLen b + 1) k v h2; omega
    · have := ih1 (offset + boolCodeLen b + 1 + stmtCodeLen s2 + 1) k v h1; omega
  | loop b body ih =>
    intro k v hmem
    simp [collectLabels] at hmem
    simp only [stmtCodeLen]
    have := ih (offset + boolCodeLen b + 1) k v hmem; omega
  | skip | assign _ _ | bassign _ _ | arrWrite _ _ _ | barrWrite _ _ _
  | fassign _ _ | farrWrite _ _ _ | goto _ | ifgoto _ _ | print _ _
  | printInt _ | printBool _ | printFloat _ | printString _ =>
    intro k v hmem; simp [collectLabels] at hmem

/-- All jump targets in compiled statement code are ≤ bound,
    given that all label targets are also ≤ bound. -/
theorem compileStmt_allJumpsLe (s : Stmt) (offset nextTmp : Nat)
    (labels : List (String × Nat))
    (bound : Nat)
    (hbound : offset + (compileStmt s offset nextTmp labels).1.length ≤ bound)
    (hlabels : AllLabelsLe bound labels) :
    AllJumpsLe bound
      (compileStmt s offset nextTmp labels).1 := by
  induction s generalizing offset nextTmp labels bound with
  | skip => exact AllJumpsLe_nil
  | assign x e =>
    cases e with
    | lit _ => intro _ hmem; simp [compileStmt] at hmem; subst hmem; trivial
    | var _ => intro _ hmem; simp [compileStmt] at hmem; subst hmem; trivial
    | bin _ a b =>
      exact AllJumpsLe_of_allSeq (by
        intro instr hmem; simp [compileStmt, List.mem_append] at hmem
        rcases hmem with ha | hb | rfl
        · exact compileExpr_allSeq a _ _ instr ha
        · exact compileExpr_allSeq b _ _ instr hb
        · trivial)
    | arrRead _ idx =>
      exact AllJumpsLe_of_allSeq (by
        intro instr hmem; simp [compileStmt, List.mem_append] at hmem
        rcases hmem with hi | rfl | rfl
        · exact compileExpr_allSeq idx _ _ instr hi
        · trivial
        · trivial)
    | flit _ | fbin _ _ _ | intToFloat _ | floatToInt _ | floatUnary _ _ | farrRead _ _ =>
      exact AllJumpsLe_of_allSeq (by
        intro instr hmem; simp [compileStmt, List.mem_append] at hmem
        rcases hmem with he | rfl
        · exact compileExpr_allSeq _ _ _ instr he
        · trivial)
  | bassign _ b =>
    simp only [compileStmt, List.length_append, List.length_singleton] at hbound ⊢
    exact AllJumpsLe_append
      (AllJumpsLe_mono (compileBool_allJumpsLe b offset nextTmp _ (Nat.le_refl _)) (by omega))
      (AllJumpsLe_of_allSeq (fun instr hmem => by simp at hmem; subst hmem; trivial))
  | arrWrite _ idx val =>
    exact AllJumpsLe_of_allSeq (by
      intro instr hmem; simp [compileStmt, List.mem_append] at hmem
      rcases hmem with hi | hv | rfl
      · exact compileExpr_allSeq idx _ _ instr hi
      · exact compileExpr_allSeq val _ _ instr hv
      · trivial)
  | barrWrite arr idx bval =>
    match hci : compileExpr idx offset nextTmp with
    | (codeIdx, vIdx, tmp1) =>
    match hcb : compileBool bval (offset + codeIdx.length) tmp1 with
    | (codeBool, be, tmp2) =>
    simp only [compileStmt, hci, hcb]
    have hi : AllJumpsLe (offset + codeIdx.length) codeIdx :=
      AllJumpsLe_of_allSeq (fun instr hmem => by
        have := compileExpr_allSeq idx offset nextTmp instr; simp [hci] at this; exact this hmem)
    have hb : AllJumpsLe (offset + codeIdx.length + codeBool.length) codeBool := by
      have := compileBool_allJumpsLe bval (offset + codeIdx.length) tmp1
        (offset + codeIdx.length + codeBool.length) (by simp [hcb])
      simp [hcb] at this; exact this
    simp only [compileStmt, hci, hcb, List.length_append, List.length_cons, List.length_nil] at hbound
    apply AllJumpsLe_append
    · apply AllJumpsLe_append
      · exact AllJumpsLe_mono hi (by omega)
      · exact AllJumpsLe_mono hb (by omega)
    · -- [boolop, arrStore] — both are seq instructions, no jumps to bound.
      exact AllJumpsLe_of_allSeq (fun instr hmem => by
        simp at hmem; rcases hmem with rfl | rfl <;> trivial)
  | seq s1 s2 ih1 ih2 =>
    simp only [compileStmt, List.length_append] at hbound ⊢
    exact AllJumpsLe_append
      (ih1 offset nextTmp labels bound (by omega) hlabels)
      (ih2 _ _ labels bound (by omega) hlabels)
  | ite b s1 s2 ih1 ih2 =>
    match hcb : compileBool b offset nextTmp with
    | (codeB, be, tmpB) =>
    match hs2 : compileStmt s2 (offset + codeB.length + 1) tmpB labels with
    | (codeElse, tmpE) =>
    match hs1 : compileStmt s1 (offset + codeB.length + 1 + codeElse.length + 1) tmpE labels with
    | (codeThen, _) =>
    simp only [compileStmt, hcb, hs2, hs1, List.length_append, List.length_singleton] at hbound ⊢
    have hb : AllJumpsLe (offset + codeB.length) codeB := by
      have := compileBool_allJumpsLe b offset nextTmp (offset + codeB.length) (by simp [hcb])
      simp [hcb] at this; exact this
    have h2 := ih2 (offset + codeB.length + 1) tmpB labels bound
      (by simp only [hs2]; omega) hlabels
    simp only [hs2] at h2
    have h1 := ih1 (offset + codeB.length + 1 + codeElse.length + 1) tmpE labels bound
      (by simp only [hs1]; omega) hlabels
    simp only [hs1] at h1
    -- ++ is left-associative: ((((codeB ++ [ifgoto]) ++ codeElse) ++ [goto]) ++ codeThen)
    exact AllJumpsLe_append
      (AllJumpsLe_append
        (AllJumpsLe_append
          (AllJumpsLe_append (AllJumpsLe_mono hb (by omega))
            (AllJumpsLe_single_ifgoto (by omega)))
          h2)
        (AllJumpsLe_single_goto (by omega)))
      h1
  | loop b body ih =>
    match hcb : compileBool b offset nextTmp with
    | (codeB, be, tmpB) =>
    match hsbody : compileStmt body (offset + codeB.length + 1) tmpB labels with
    | (codeBody, _) =>
    simp only [compileStmt, hcb, hsbody, List.length_append, List.length_singleton] at hbound ⊢
    have hb : AllJumpsLe (offset + codeB.length) codeB := by
      have := compileBool_allJumpsLe b offset nextTmp (offset + codeB.length) (by simp [hcb])
      simp [hcb] at this; exact this
    have hih := ih (offset + codeB.length + 1) tmpB labels bound
      (by simp only [hsbody]; omega) hlabels
    simp only [hsbody] at hih
    -- ++ is left-associative: (((codeB ++ [ifgoto]) ++ codeBody) ++ [goto])
    exact AllJumpsLe_append
      (AllJumpsLe_append
        (AllJumpsLe_append (AllJumpsLe_mono hb (by omega))
          (AllJumpsLe_single_ifgoto (by omega)))
        hih)
      (AllJumpsLe_single_goto (by omega))
  | fassign x e =>
    cases e with
    | flit _ => intro _ hmem; simp [compileStmt] at hmem; subst hmem; trivial
    | var _ => intro _ hmem; simp [compileStmt] at hmem; subst hmem; trivial
    | fbin _ a b =>
      exact AllJumpsLe_of_allSeq (by
        intro instr hmem; simp [compileStmt, List.mem_append] at hmem
        rcases hmem with ha | hb | rfl
        · exact compileExpr_allSeq a _ _ instr ha
        · exact compileExpr_allSeq b _ _ instr hb
        · trivial)
    | intToFloat e =>
      exact AllJumpsLe_of_allSeq (by
        intro instr hmem; simp [compileStmt, List.mem_append] at hmem
        rcases hmem with he | rfl
        · exact compileExpr_allSeq e _ _ instr he
        · trivial)
    | floatUnary op e =>
      exact AllJumpsLe_of_allSeq (by
        intro instr hmem; simp [compileStmt, List.mem_append] at hmem
        rcases hmem with he | rfl
        · exact compileExpr_allSeq e _ _ instr he
        · trivial)
    | farrRead arr idx =>
      exact AllJumpsLe_of_allSeq (by
        intro instr hmem; simp [compileStmt, List.mem_append] at hmem
        rcases hmem with hi | rfl | rfl
        · exact compileExpr_allSeq idx _ _ instr hi
        · trivial
        · trivial)
    | _ =>
      exact AllJumpsLe_of_allSeq (by
        intro instr hmem; simp [compileStmt, List.mem_append] at hmem
        rcases hmem with he | rfl
        · exact compileExpr_allSeq _ _ _ instr he
        · trivial)
  | farrWrite arr idx val =>
    exact AllJumpsLe_of_allSeq (by
      intro instr hmem; simp [compileStmt, List.mem_append] at hmem
      rcases hmem with hi | hv | rfl
      · exact compileExpr_allSeq idx _ _ instr hi
      · exact compileExpr_allSeq val _ _ instr hv
      · trivial)
  | label _ =>
    simp [compileStmt]
  | goto lbl =>
    simp only [compileStmt]
    exact AllJumpsLe_single_goto (Nat.le_trans (AllLabelsLe_lookup hlabels lbl) (by omega))
  | ifgoto b lbl =>
    simp only [compileStmt, List.length_append, List.length_singleton] at hbound ⊢
    exact AllJumpsLe_append
      (AllJumpsLe_mono (compileBool_allJumpsLe b offset nextTmp _ (Nat.le_refl _)) (by omega))
      (AllJumpsLe_single_ifgoto (Nat.le_trans (AllLabelsLe_lookup hlabels lbl) (by omega)))
  | print fmt args =>
    exact AllJumpsLe_of_allSeq (by
      intro instr hmem; simp [compileStmt, List.mem_append] at hmem
      rcases hmem with he | rfl
      · exact compileExprs_allSeq args _ _ instr he
      · trivial)
  | printInt e =>
    exact AllJumpsLe_of_allSeq (by
      intro instr hmem; simp [compileStmt, List.mem_append] at hmem
      rcases hmem with he | rfl
      · exact compileExpr_allSeq e _ _ instr he
      · trivial)
  | printBool b =>
    match hcb : compileBool b offset nextTmp with
    | (codeB, be, tmpB) =>
    simp only [compileStmt, hcb]
    have hb : AllJumpsLe (offset + codeB.length) codeB := by
      have := compileBool_allJumpsLe b offset nextTmp (offset + codeB.length) (by simp [hcb])
      simp [hcb] at this; exact this
    simp only [compileStmt, hcb, List.length_append, List.length_cons, List.length_nil] at hbound
    apply AllJumpsLe_append
    · apply AllJumpsLe_append
      · exact AllJumpsLe_mono hb (by omega)
      · have h_ifgt : offset + codeB.length + 3 ≤ bound := by omega
        have h_goto : offset + codeB.length + 3 + 1 ≤ bound := by omega
        intro instr hmem; simp at hmem
        rcases hmem with rfl | rfl | rfl | rfl
        · exact h_ifgt
        · exact trivial
        · exact h_goto
        · exact trivial
    · exact AllJumpsLe_of_allSeq (fun instr hmem => by simp at hmem; subst hmem; trivial)
  | printFloat e =>
    exact AllJumpsLe_of_allSeq (by
      intro instr hmem; simp [compileStmt, List.mem_append] at hmem
      rcases hmem with he | rfl
      · exact compileExpr_allSeq e _ _ instr he
      · trivial)
  | printString lit =>
    exact AllJumpsLe_of_allSeq (by
      intro instr hmem; simp [compileStmt] at hmem; subst hmem; trivial)

/-- Bridge: if all jump targets in `code` are ≤ `code.length`, then
    `(code ++ [halt]).toArray` is step-closed in bounds. -/
private theorem stepClosed_of_allJumpsLe {code : List TAC} {p : Prog}
    (hcode : p.code = (code ++ [TAC.halt]).toArray)
    (hjumps : AllJumpsLe code.length code) :
    StepClosedInBounds p := by
  have hlen : p.size = code.length + 1 := by simp [Prog.size, hcode]
  constructor
  · omega
  · intro pc pc' σ σ' am am' hpc hstep
    obtain ⟨instr, hinstr, hmem⟩ := Step.mem_successors hstep
    rw [hlen] at hpc ⊢
    rw [show p[pc]? = (code ++ [TAC.halt])[pc]? from by
      simp [Prog.getElem?_code, hcode, List.getElem?_toArray]] at hinstr
    by_cases hlt : pc < code.length
    · -- Instruction is from `code`
      rw [List.getElem?_append_left hlt] at hinstr
      have hmem_code := List.mem_of_getElem? hinstr
      have hj := hjumps instr hmem_code
      cases instr with
      | const _ _ | copy _ _ | binop _ _ _ _ | boolop _ _ =>
        simp [TAC.successors] at hmem; omega
      | arrLoad _ _ _ _ | arrStore _ _ _ _ =>
        simp [TAC.successors] at hmem; omega
      | fbinop _ _ _ _ | intToFloat _ _ | floatToInt _ _ | floatUnary _ _ _
      | fternop _ _ _ _ _ | print _ _ | printInt _ | printBool _ | printFloat _ | printString _ =>
        simp [TAC.successors] at hmem; omega
      | goto l => simp [TAC.successors] at hmem; subst hmem; exact Nat.lt_of_le_of_lt hj (by omega)
      | ifgoto _ l =>
        simp [TAC.successors, List.mem_cons] at hmem
        rcases hmem with rfl | rfl
        · exact Nat.lt_of_le_of_lt hj (by omega)
        · omega
      | halt => simp [TAC.successors] at hmem
    · -- Instruction is halt (at position code.length)
      have hpc_eq : pc = code.length := by omega
      subst hpc_eq
      rw [List.getElem?_append_right (by omega)] at hinstr
      simp at hinstr; subst hinstr
      simp [TAC.successors] at hmem

/-- **Step-closedness**: A type-checked program's compiled output has all
    jump targets within bounds — no instruction can jump outside the program. -/
theorem compileToTAC_stepClosed (prog : Program) (_h : prog.typeCheck = true) :
    StepClosedInBounds prog.compileToTAC := by
  apply stepClosed_of_allJumpsLe (code := initCode prog.decls ++
    (compileStmt prog.body (initCode prog.decls).length 0
      (collectLabels prog.body (initCode prog.decls).length)).1)
  · simp [Program.compileToTAC, List.append_assoc]
  · simp only [List.length_append]
    apply AllJumpsLe_append
    · exact AllJumpsLe_of_allSeq (initCode_allSeq prog.decls)
    · exact compileStmt_allJumpsLe prog.body (initCode prog.decls).length 0
        (collectLabels prog.body (initCode prog.decls).length)
        ((initCode prog.decls).length +
          (compileStmt prog.body (initCode prog.decls).length 0
            (collectLabels prog.body (initCode prog.decls).length)).1.length)
        (by omega)
        (by intro k v hmem
            have := collectLabels_allLabelsLe prog.body (initCode prog.decls).length k v hmem
            rw [compileStmt_length]; exact this)

/-- initCode instructions have simple ops (they are all `const`, never boolop/ifgoto). -/
theorem initCode_hasSimpleOps (decls : List (Var × VarTy)) :
    ∀ instr ∈ initCode decls, instr.hasSimpleOps = true := by
  intro instr hmem; simp only [initCode, List.mem_map] at hmem
  obtain ⟨⟨_, ty⟩, _, rfl⟩ := hmem; cases ty <;> rfl

/-- All instructions in `compileToTAC` output have simple boolean ops. -/
theorem compileToTAC_allSimpleOps (prog : Program) :
    ∀ instr, instr ∈ prog.compileToTAC.code.toList → instr.hasSimpleOps = true := by
  intro instr hmem
  have : prog.compileToTAC.code.toList =
      initCode prog.decls ++ (compileStmt prog.body (initCode prog.decls).length 0
        (collectLabels prog.body (initCode prog.decls).length)).1 ++ [TAC.halt] := by
    simp [Program.compileToTAC, List.append_assoc]
  rw [this] at hmem
  simp only [List.mem_append] at hmem
  rcases hmem with (hinit | hbody) | hhalt
  · exact initCode_hasSimpleOps prog.decls _ hinit
  · exact compileStmt_code_simpleOps prog.body _ _ _ _ hbody
  · simp [List.mem_cons] at hhalt; subst hhalt; rfl

/-- All goto/ifgoto targets in `compileToTAC` output are strictly less than the
    program size. Stated without `match` to avoid dependent type issues. -/
theorem compileToTAC_jumpTargetsBound (prog : Program) :
    prog.compileToTAC.size > 0 ∧
    (∀ l, .goto l ∈ prog.compileToTAC.code.toList → l < prog.compileToTAC.size) ∧
    (∀ be l, .ifgoto be l ∈ prog.compileToTAC.code.toList → l < prog.compileToTAC.size) := by
  -- Decompose the compiled code
  have hcode : prog.compileToTAC.code =
      (initCode prog.decls ++ (compileStmt prog.body (initCode prog.decls).length 0
        (collectLabels prog.body (initCode prog.decls).length)).1 ++ [TAC.halt]).toArray := by
    simp [Program.compileToTAC, List.append_assoc]
  -- Size fact
  have hsize : prog.compileToTAC.size =
      (initCode prog.decls).length +
      (compileStmt prog.body (initCode prog.decls).length 0
        (collectLabels prog.body (initCode prog.decls).length)).1.length + 1 := by
    simp [Prog.size, hcode]; omega
  -- AllJumpsLe for the code body
  have hjumps : AllJumpsLe
      ((initCode prog.decls).length +
        (compileStmt prog.body (initCode prog.decls).length 0
          (collectLabels prog.body (initCode prog.decls).length)).1.length)
      (initCode prog.decls ++ (compileStmt prog.body (initCode prog.decls).length 0
        (collectLabels prog.body (initCode prog.decls).length)).1) := by
    apply AllJumpsLe_append
    · exact AllJumpsLe_of_allSeq (initCode_allSeq prog.decls)
    · exact compileStmt_allJumpsLe prog.body (initCode prog.decls).length 0
        (collectLabels prog.body (initCode prog.decls).length) _ (by omega)
        (by intro k v hmem
            have := collectLabels_allLabelsLe prog.body (initCode prog.decls).length k v hmem
            rw [compileStmt_length]; exact this)
  -- Helper: convert toList membership to the list form
  have hmem_conv : ∀ instr, instr ∈ prog.compileToTAC.code.toList →
      instr ∈ initCode prog.decls ++
        (compileStmt prog.body (initCode prog.decls).length 0
          (collectLabels prog.body (initCode prog.decls).length)).1 ∨
      instr = TAC.halt := by
    intro instr hmem
    rwa [show prog.compileToTAC.code.toList =
        (initCode prog.decls ++ (compileStmt prog.body (initCode prog.decls).length 0
          (collectLabels prog.body (initCode prog.decls).length)).1 ++ [TAC.halt]) from by
      simp [hcode],
      List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  refine ⟨by omega, ?_, ?_⟩
  · intro l hmem
    rcases hmem_conv _ hmem with hcode_mem | habs
    · have h := hjumps (.goto l) hcode_mem
      change l ≤ _ at h; omega
    · simp at habs
  · intro be l hmem
    rcases hmem_conv _ hmem with hcode_mem | habs
    · have h := hjumps (.ifgoto be l) hcode_mem
      change l ≤ _ at h; omega
    · simp at habs

/-- **No-stuck guarantee**: A type-checked program always has a behavior —
    it either halts, errors (div-by-zero), or diverges. No execution can
    get stuck. Combines `compileToTAC_wellTyped`, `compileToTAC_stepClosed`, and
    `has_behavior`. -/
theorem compileToTAC_has_behavior (prog : Program) (htc : prog.typeCheck = true)
    (σ₀ : Store) :
    ∃ b, program_behavior prog.compileToTAC σ₀ b :=
  has_behavior prog.compileToTAC σ₀ (prog.compileToTAC_stepClosed htc)

-- ============================================================
-- § 5h. Pretty-printing
-- ============================================================

private def tyToString : VarTy → String
  | .int   => "int"
  | .bool  => "bool"
  | .float => "float"

def toString (prog : Program) : String :=
  -- ONE comma-separated `var` block + an `array` block, matching the parser's concrete syntax.
  let varBlock := if prog.decls.isEmpty then "" else
    "var " ++ String.intercalate ", " (prog.decls.map fun (x, ty) => s!"{x} : {tyToString ty}") ++ ";\n"
  let arrBlock := if prog.arrayDecls.isEmpty then "" else
    "array " ++ String.intercalate ", "
      (prog.arrayDecls.map fun (a, sz, ty) => s!"{a}[{sz}] : {tyToString ty}") ++ ";\n"
  s!"{varBlock}{arrBlock}{prog.body}"

instance : ToString Program := ⟨Program.toString⟩

end Program
