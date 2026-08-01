-- Copyright (c) 2026 Martin Rinard
import CredibleCompilation.PropChecker
import CredibleCompilation.CodeGenLayout
import Std.Data.HashMap

/-!
# Executable Certificate Checker

An executable certificate checker that returns `Bool`.
Use `#eval! checkCertificateExec cert` or run `lake exe checker` from the terminal.

The checker uses **symbolic execution** and **expression simplification** to verify
that the transformed program's behavior matches the original. Invariants are
represented as lists of `(var, expr)` atoms. An explicit **expression relation**
(per transformed PC) relates expressions over original variables to expressions
over transformed variables via pairs `(e_orig, e_trans)` asserting equality.

## Two-level architecture: list-based vs HashMap-backed

Several check functions and helpers exist in **two parallel forms**:

1. **List-based originals** — take `inv : EInv` (a `List (Var × Expr)`) and
   look up vars via `inv.find?` / `lookupExpr`. Examples: `Expr.simplify`,
   `Expr.simplifyDeep`, `BoolExpr.normalize`, `BoolExpr.symEval`,
   `computeNextPC`, `checkInstrAliasOk`, `checkOrigPath`, `checkInvAtom`,
   `checkInvariantsPreservedExec`, `checkAllTransitionsExec`,
   `checkRelConsistency`, `checkDivPreservationExec`,
   `checkBoundsPreservationExec`. These are the form the **soundness
   theorems in `SoundnessBridge.lean` reason about** (~30 proofs unfold
   their bodies and pattern-match on `inv.find?` results).

2. **HashMap-backed Fast/Early/FromMaps variants** — take
   `FastVarMap = Std.HashMap String Expr` (precomputed once) and look up
   vars in O(1). Examples: `Expr.simplifyFast`, `Expr.simplifyDeepFast`,
   `Expr.simplifyDeepFastEarly`, `BoolExpr.normalizeFast`,
   `BoolExpr.symEvalFast`, `computeNextPCFast`, `checkInstrAliasOkFast`,
   `checkOrigPathFast`, `checkInvAtomFast`,
   `checkInvariantsPreservedFromMaps`, `checkAllTransitionsFromMaps`,
   `checkRelConsistencyFromMap`, `checkDivPreservationFromMaps`,
   `checkBoundsPreservationFromMaps`. **`checkCertificateExec` calls only
   these on the live runtime path**, sharing a single per-PC `FastVarMap`
   cache built by `buildInvMaps`.

3. **Equivalence lemmas** form the bridge:
   `simplifyDeepFastEarly_eq_simplifyDeep`,
   `checkInvAtomFast_eq_checkInvAtom`,
   `BoolExpr.normalizeFast_eq_normalize`, `BoolExpr.symEvalFast_eq_symEval`,
   `computeNextPCFast_eq_computeNextPC`,
   `checkInstrAliasOkFast_eq_checkInstrAliasOk`,
   `checkOrigPathFast_eq_checkOrigPath`,
   `checkInvariantsPreservedFromMaps_eq`,
   `checkAllTransitionsFromMaps_eq`, `checkRelConsistencyFromMap_eq`,
   `checkDivPreservationFromMaps_eq`, `checkBoundsPreservationFromMaps_eq`.
   Each says "Fast/FromMaps form at the canonical call shape (built from
   the cert's invariants) equals the list-based original".
   `checkCertificateExec_sound` uses these as `rw`s to convert the
   conjuncts of `unfold checkCertificateExec at h` from FromMaps form
   back to original form, after which the existing per-conjunct
   soundness theorems apply.

**Convention**: when adding a new check function, write the list-based
original (proof-friendly) and the FromMaps variant (cache-friendly),
plus the equivalence lemma. Wire only the FromMaps variant into
`checkCertificateExec`; soundness flows through the equivalence lemma.

The list-based originals cannot be deleted without rewriting the
~30 proofs in `SoundnessBridge.lean` to reason about Fast forms
directly — a substantial refactor that hasn't been undertaken.
-/

-- ============================================================
-- § 1. Executable invariants and helpers
-- ============================================================

/-- Executable invariant: conjunction of `var = expr` atoms.
    Each `(x, e)` asserts `σ x = e.eval σ` at runtime. -/
abbrev EInv := List (Var × Expr)

/-- Executable expression relation: pairs of expressions asserting equality
    across stores.  Each `(e_o, e_t)` asserts `e_o.eval(σ_orig) = e_t.eval(σ_trans)`.
    Generalizes the old variable map: `(v, e)` in the old map becomes `(e, .var v)`. -/
abbrev EExprRel := List (Expr × Expr)

def lookupExpr (inv : EInv) (v : Var) : Option Expr :=
  (inv.find? (fun p => p.1 == v)).map (·.2)

-- ============================================================
-- § 2. Symbolic expression simplification
-- ============================================================

/-- Reassociate sub-expressions involving literals after simplification.
    Normalizes patterns like `(n - x) - m → (n - m) - x` and
    `n - (x + m) → (n - m) - x` so that the checker can verify
    induction variable elimination (countdown vs recomputation).
    Also normalizes `(n - x) + m → (n + m) - x` and `n - (x - m) → (n + m) - x`
    for additive induction variable elimination. -/
def Expr.reassoc : BinOp → Expr → Expr → Expr
  | .add, .bin .sub (.lit na) x, .lit nb => .bin .sub (.lit (na + nb)) x
  | .sub, .bin .sub (.lit na) x, .lit nb => .bin .sub (.lit (na - nb)) x
  | .sub, .lit na, .bin .add x (.lit nb) => .bin .sub (.lit (na - nb)) x
  | .sub, .lit na, .bin .add (.lit nb) x => .bin .sub (.lit (na - nb)) x
  | .sub, .lit na, .bin .sub x (.lit nb) => .bin .sub (.lit (na + nb)) x
  | op, a, b => .bin op a b

/-- Simplify an `Expr` by substituting known variable expressions and constant-folding.
    After folding, applies `reassoc` to normalize sub/add patterns involving literals. -/
def Expr.simplify (inv : EInv) : Expr → Expr
  | .lit n => .lit n
  | .blit b => .blit b
  | .var v => match lookupExpr inv v with
    | some e => e
    | none   => .var v
  | .bin op a b =>
    match a.simplify inv, b.simplify inv with
    | .lit na, .lit nb => .lit (op.eval na nb)
    | a', b'           => Expr.reassoc op a' b'
  -- Recurse into the boolean-expr-as-Expr constructors so that invariant
  -- substitution reaches variables *inside* comparisons. Without this, a
  -- variable holding a comparison result (e.g. `done := x == y`) cannot have
  -- its operands resolved via the invariant, while `substSymFast` (used on the
  -- transformed side) does recurse — the asymmetry causes spurious
  -- `checkRelConsistency` rejections (e.g. LICM hoisting around a bool flag).
  | .tobool e       => .tobool (e.simplify inv)
  | .cmpE op a b    => .cmpE op (a.simplify inv) (b.simplify inv)
  | .cmpLitE op a n => .cmpLitE op (a.simplify inv) n
  | .notE e         => .notE (e.simplify inv)
  | .andE a b       => .andE (a.simplify inv) (b.simplify inv)
  | .orE a b        => .orE (a.simplify inv) (b.simplify inv)
  | .arrRead arr idx => .arrRead arr (idx.simplify inv)
  | .flit n         => .flit n
  | .fbin op a b    =>
    let a' := a.simplify inv; let b' := b.simplify inv
    match op, a', b' with
    -- normalize a lone `fmul` operand onto the right (helps FMA matching).
    -- When BOTH operands are `fmul`, do NOT swap: swapping would put an `fmul`
    -- back on the left and re-fire on the next iteration, so the normal form
    -- would oscillate by iteration parity and break confluence (equal
    -- expressions reached via different var-unfold depths would not compare
    -- equal). Keeping both-fmul in original order is an immediate fixed point.
    | .fadd, .fbin .fmul _ _, .fbin .fmul _ _ => .fbin .fadd a' b'
    | .fadd, .fbin .fmul _ _, _ => .fbin .fadd b' a'
    | _, _, _ => .fbin op a' b'
  | .fcmpE op a b   => .fcmpE op (a.simplify inv) (b.simplify inv)
  | .intToFloat e   => .intToFloat (e.simplify inv)
  | .floatToInt e   => .floatToInt (e.simplify inv)
  | .floatUnary op e => .floatUnary op (e.simplify inv)
  | .ftern op a b c => match op with
    | .fmadd => .fbin .fadd (a.simplify inv) (.fbin .fmul (b.simplify inv) (c.simplify inv))
    | .fmsub => .fbin .fsub (a.simplify inv) (.fbin .fmul (b.simplify inv) (c.simplify inv))
  | .farrRead arr idx => .farrRead arr (idx.simplify inv)

/-- Like `Expr.simplify` but iterates to resolve chained `.var` lookups.
    Applies `simplify` once, then re-applies up to `n` more times so that
    var-chain references through the invariant are fully resolved.
    Fuel `n` controls the number of extra iterations. -/
def Expr.simplifyDeep : Nat → EInv → Expr → Expr
  | 0, inv, e => e.simplify inv
  | n + 1, inv, e => (e.simplify inv).simplifyDeep n inv

/-- Fuel for `simplifyDeep`: one pass per invariant entry plus one.
    Defined as a separate `def` so that the type-checker cannot pattern-match
    the result as `Nat.succ _`, which would cause `simplifyDeep` to unfold
    one step and break `split`-based proof strategies. -/
def sdFuel (inv : EInv) : Nat := inv.length + 1

-- ============================================================
-- § 3. Symbolic execution
-- ============================================================

/-- Symbolic store: maps modified variables to expressions over initial variables.
    Unmapped variables are implicitly `.var v` (identity). -/
abbrev SymStore := List (Var × Expr)

def ssGet (ss : SymStore) (v : Var) : Expr :=
  match ss.find? (fun p => p.1 == v) with
  | some (_, e) => e
  | none        => .var v

def ssSet (ss : SymStore) (x : Var) (e : Expr) : SymStore :=
  (x, e) :: ss.filter (fun p => !(p.1 == x))

/-- Substitute variables in an Expr using a SymStore. -/
def Expr.substSym' (ss : SymStore) : Expr → Expr
  | .lit n      => .lit n
  | .blit b     => .blit b
  | .var v      => ssGet ss v
  | .bin op a b => .bin op (a.substSym' ss) (b.substSym' ss)
  | .tobool e       => .tobool (e.substSym' ss)
  | .cmpE op a b    => .cmpE op (a.substSym' ss) (b.substSym' ss)
  | .cmpLitE op a n => .cmpLitE op (a.substSym' ss) n
  | .notE e         => .notE (e.substSym' ss)
  | .andE a b       => .andE (a.substSym' ss) (b.substSym' ss)
  | .orE a b        => .orE (a.substSym' ss) (b.substSym' ss)
  | .arrRead arr idx => .arrRead arr (idx.substSym' ss)
  | .flit n          => .flit n
  | .fbin op a b     => .fbin op (a.substSym' ss) (b.substSym' ss)
  | .fcmpE op a b    => .fcmpE op (a.substSym' ss) (b.substSym' ss)
  | .intToFloat e    => .intToFloat (e.substSym' ss)
  | .floatToInt e    => .floatToInt (e.substSym' ss)
  | .floatUnary op e  => .floatUnary op (e.substSym' ss)
  | .ftern op a b c   => .ftern op (a.substSym' ss) (b.substSym' ss) (c.substSym' ss)
  | .farrRead arr idx => .farrRead arr (idx.substSym' ss)

/-- Convert a BoolExpr to a symbolic Expr by replacing each variable reference
    with its symbolic expression from the store. -/
def BoolExpr.toSymExpr (ss : SymStore) : BoolExpr → Expr
  | .lit b       => .blit b
  | .bvar x      => .tobool (ssGet ss x)
  | .cmp op a b  => .cmpE op (a.substSym' ss) (b.substSym' ss)
  | .not e       => .notE (e.toSymExpr ss)
  | .fcmp op a b => .fcmpE op (a.substSym' ss) (b.substSym' ss)
  | .bexpr e     => .tobool (e.substSym' ss)

/-- Symbolic array memory: tracks array writes as a list of (array, index, value) triples.
    Most recent writes are at the head. -/
abbrev SymArrayMem := List (ArrayName × Expr × Expr)

/-- Look up an array read in the symbolic array memory.
    Returns the written value if the array and index match, otherwise `.arrRead`. -/
def samGet (sam : SymArrayMem) (arr : ArrayName) (idx : Expr) (ty : VarTy := .int) : Expr :=
  match sam.find? (fun (a, i, _) => a == arr && i == idx) with
  | some (_, _, v) => v
  | none => match ty with
    | .int   => .arrRead arr idx
    | .float => .farrRead arr idx
    | .bool  => .cmpLitE .ne (.arrRead arr idx) 0

/-- Symbolically execute one TAC instruction.
    Expressions in the resulting store reference the *initial* variable values.
    Returns updated (SymStore, SymArrayMem). -/
def execSymbolic (ss : SymStore) (sam : SymArrayMem) (instr : TAC) : SymStore × SymArrayMem :=
  match instr with
  | .const x (.int n)  => (ssSet ss x (.lit n), sam)
  | .const x (.bool b) => (ssSet ss x (.blit b), sam)
  | .const x (.float f) => (ssSet ss x (.flit f), sam)
  | .boolop x be    => (ssSet ss x (be.toSymExpr ss), sam)
  | .copy x y       => (ssSet ss x (ssGet ss y), sam)
  | .binop x op y z => (ssSet ss x (.bin op (ssGet ss y) (ssGet ss z)), sam)
  | .fbinop x op y z => (ssSet ss x (.fbin op (ssGet ss y) (ssGet ss z)), sam)
  | .intToFloat x y => (ssSet ss x (.intToFloat (ssGet ss y)), sam)
  | .floatToInt x y => (ssSet ss x (.floatToInt (ssGet ss y)), sam)
  | .floatUnary x op y => (ssSet ss x (.floatUnary op (ssGet ss y)), sam)
  | .fternop x op a b c => (ssSet ss x (.ftern op (ssGet ss a) (ssGet ss b) (ssGet ss c)), sam)
  | .arrLoad x arr idx ty => (ssSet ss x (samGet sam arr (ssGet ss idx) ty), sam)
  | .arrStore arr idx val _ => (ss, (arr, ssGet ss idx, ssGet ss val) :: sam)
  | _               => (ss, sam)

/-- Symbolically execute along a path of labels in the original program.
    At each label, look up the instruction and execute it symbolically. -/
def execPath (orig : Prog) (ss : SymStore) (sam : SymArrayMem) (pc : Label) :
    List Label → SymStore × SymArrayMem
  | []             => (ss, sam)
  | nextPC :: rest =>
    match orig[pc]? with
    | some instr =>
      let (ss', sam') := execSymbolic ss sam instr
      execPath orig ss' sam' nextPC rest
    | none       => (ss, sam)

-- ============================================================
-- § 4. Instruction helpers
-- ============================================================

/-- Check whether an expression is a non-zero literal. -/
def Expr.isNonZeroLit : Expr → Bool
  | .lit 0 => false
  | .lit _ => true
  | .blit true => true
  | .blit false | .var _ | .bin _ _ _ => false
  | .tobool _ | .cmpE _ _ _ | .cmpLitE _ _ _ | .notE _ | .andE _ _ | .orE _ _ | .arrRead _ _ => false
  | .flit _ | .fbin _ _ _ | .fcmpE _ _ _ | .intToFloat _ | .floatToInt _ | .floatUnary _ _ | .ftern _ _ _ _ | .farrRead _ _ => false

/-- Normalize a BoolExpr under a symbolic store and invariant: replace variables
    with known literal values, folding constant comparisons when possible. -/
def BoolExpr.normalize (ss : SymStore) (inv : EInv) : BoolExpr → BoolExpr
  | .lit b => .lit b
  | .bvar x =>
    match (ssGet ss x).simplifyDeep (sdFuel inv) inv with
    | .blit b => .lit b
    | e'      => .bexpr e'
  | .cmp op a b =>
    match (a.substSym' ss).simplifyDeep (sdFuel inv) inv, (b.substSym' ss).simplifyDeep (sdFuel inv) inv with
    | .lit va, .lit vb => .lit (op.eval va vb)
    | a', b' => .cmp op a' b'
  | .not e => match e.normalize ss inv with
    | .lit b => .lit (!b)
    | .not inner => inner  -- double negation elimination
    | e' => .not e'
  | .fcmp op a b =>
    match (a.substSym' ss).simplifyDeep (sdFuel inv) inv, (b.substSym' ss).simplifyDeep (sdFuel inv) inv with
    | .flit va, .flit vb => .lit (FloatCmpOp.eval op va vb)
    | a', b' => .fcmp op a' b'
  | .bexpr e =>
    match (e.substSym' ss).simplifyDeep (sdFuel inv) inv with
    | .blit b => .lit b
    | e'      => .bexpr e'

/-- Symbolically evaluate a BoolExpr under a symbolic store and invariant.
    Returns `some true`/`some false` if the result can be determined, `none` otherwise. -/
def BoolExpr.symEval (ss : SymStore) (inv : EInv) : BoolExpr → Option Bool
  | .lit b => some b
  | .bvar x =>
    match (ssGet ss x).simplifyDeep (sdFuel inv) inv with
    | .blit b => some b
    | _ => none
  | .cmp op a b =>
    match (a.substSym' ss).simplifyDeep (sdFuel inv) inv, (b.substSym' ss).simplifyDeep (sdFuel inv) inv with
    | .lit va, .lit vb => some (op.eval va vb)
    | _, _ => none
  | .not e => e.symEval ss inv |>.map (!·)
  | .fcmp _op _a _b => none  -- symbolic fcmp operands don't reduce to literals here; fall back to branchInfo
  | .bexpr e =>
    match (e.substSym' ss).simplifyDeep (sdFuel inv) inv with
    | .blit b => some b
    | _ => none

/-- Collect all variable names from both programs. -/
def collectAllVars (p1 p2 : Prog) : List Var :=
  let extract (instr : TAC) : List Var :=
    match instr with
    | .const x _     => [x]
    | .copy x y      => [x, y]
    | .binop x _ y z => [x, y, z]
    | .boolop x _    => [x]
    | .fbinop x _ y z => [x, y, z]
    | .intToFloat x y => [x, y]
    | .floatToInt x y => [x, y]
    | .floatUnary x _ y => [x, y]
    | .fternop x _ a b c => [x, a, b, c]
    | .arrLoad x _ idx _ => [x, idx]
    | .arrStore _ idx val _ => [idx, val]
    | .print _ vs => vs
    | .ifgoto b _    => b.vars
    | _              => []
  let go (code : Array TAC) := code.toList.foldl (fun acc i => acc ++ extract i) ([] : List Var)
  go p1.code ++ go p2.code

-- ============================================================
-- § 5. Executable certificate types
-- ============================================================

/-- A single transition correspondence with labels of the original path. -/
structure ETransCorr where
  /-- Labels of original PCs visited (successors of pc_orig, ending at pc_orig'). -/
  origLabels : List Label
  /-- Expression relation at the source of this transition (should equal the
      enclosing `EInstrCert.rel`). -/
  rel        : EExprRel := []
  /-- Expression relation at the target of this transition (should equal
      the successor `EInstrCert.rel`). -/
  rel_next   : EExprRel := []
  deriving Repr, Inhabited

/-- Per-instruction certificate entry. -/
structure EInstrCert where
  pc_orig     : Label
  /-- Expression relation at this label: pairs `(e_o, e_t)` asserting
      `e_o.eval(σ_orig) = e_t.eval(σ_trans)`.  Empty list = no constraints. -/
  rel         : EExprRel := []
  transitions : List ETransCorr
  deriving Repr, Inhabited

/-- Per-halt certificate entry. -/
structure EHaltCert where
  pc_orig : Label
  /-- Expression relation at this halt label. -/
  rel     : EExprRel := []
  deriving Repr, Inhabited

/-- Shorthand: ETransCorr with empty (no constraints) relation. -/
abbrev ETransCorr.id (labels : List Label) : ETransCorr := { origLabels := labels }

/-- Shorthand: EInstrCert with empty relation. -/
abbrev EInstrCert.id (pc : Label) (trans : List ETransCorr) : EInstrCert :=
  { pc_orig := pc, transitions := trans }

/-- Shorthand: EHaltCert with empty relation. -/
abbrev EHaltCert.id (pc : Label) : EHaltCert := { pc_orig := pc }

/-- Look up the original-side expression for a transformed variable in a relation.
    Searches for a pair `(e_o, .var v)` and returns `e_o`.
    Defaults to `.var v` (identity) if not found. -/
def relGetOrigExpr (rel : EExprRel) (v : Var) : Expr :=
  match rel.find? (fun p => p.2 == .var v) with
  | some (e_o, _) => e_o
  | none => .var v

/-- Find the original variable name for a transformed variable in the relation.
    Returns `some v'` if there is a pair `(.var v', .var v)` in `rel`. -/
def relFindOrigVar (rel : EExprRel) (v : Var) : Option Var :=
  match rel.find? (fun p => p.2 == .var v) with
  | some (.var v', _) => some v'
  | _ => none

/-- Find the original-side expression for a transformed variable.
    For `(.var v', .var x)` returns `.var v'`; for `(lit c, .var x)` returns `lit c`. -/
def relFindOrigExpr (rel : EExprRel) (v : Var) : Option Expr :=
  match rel.find? (fun p => p.2 == .var v) with
  | some (e_o, _) => some e_o
  | _ => none

/-- Build a substitution map from pre-relation pairs of the form `(e_o, .var v)`.
    Maps transformed variable `v` to original expression `e_o`. -/
def buildSubstMap (rel : EExprRel) : SymStore :=
  rel.filterMap fun (e_o, e_t) =>
    match e_t with
    | .var v => some (v, e_o)
    | _ => none

/-- Map variables in a BoolExpr through the expression relation.
    With Expr operands, just substitute vars in each operand via the relation.
    No flip logic needed — literals on either side are just Expr.lit/Expr.flit. -/
def BoolExpr.mapVarsRel (rel : EExprRel) : BoolExpr → Option BoolExpr
  | .lit b => some (.lit b)
  | .bvar x => do
    let e ← relFindOrigExpr rel x
    match e with | .var v => return .bvar v | _ => none
  | .cmp op a b =>
    let ss := buildSubstMap rel
    some (.cmp op (a.substSym' ss) (b.substSym' ss))
  | .not e => e.mapVarsRel rel |>.map fun
    | .not inner => inner  -- double negation elimination: ¬¬p = p
    | e' => .not e'
  | .fcmp op a b =>
    let ss := buildSubstMap rel
    some (.fcmp op (a.substSym' ss) (b.substSym' ss))
  | .bexpr e =>
    let ss := buildSubstMap rel
    some (.bexpr (e.substSym' ss))

/-- An executable certificate: all data needed to verify the transformation.
    The type context is carried explicitly (not derived from orig/trans programs). -/
structure ECertificate where
  orig       : Prog
  trans      : Prog
  tyCtx      : TyCtx
  inv_orig   : Array EInv
  inv_trans  : Array EInv
  instrCerts : Array EInstrCert
  haltCerts  : Array EHaltCert
  /-- Well-founded measure for non-termination (per transformed label). -/
  measure    : Array Nat

instance : Inhabited ECertificate where
  default := { orig := ⟨#[], [], []⟩, trans := ⟨#[], [], []⟩,
               tyCtx := fun _ => .int,
               inv_orig := #[], inv_trans := #[], instrCerts := #[], haltCerts := #[], measure := #[] }

/-- The observable variables for the certificate, derived from the original program. -/
abbrev ECertificate.observable (cert : ECertificate) : List Var := cert.orig.observable

-- ============================================================
-- § 5b. Shared certificate-building utilities
-- ============================================================

/-- Build instrCerts for a 1:1 PC mapping (orig PC = trans PC).
    Used by optimizers that preserve program size (ConstProp, CSE, LICM).
    Identity pairs `(.var v, .var v)` are included for all variables in `allVars`
    so that the membership-based store relation covers all program variables. -/
def buildInstrCerts1to1 (trans : Prog) (allVars : List Var) : Array EInstrCert :=
  let idRel : EExprRel := allVars.map fun v => (.var v, .var v)
  let arr := (List.range trans.size).map fun i =>
    match trans[i]? with
    | some .halt => { pc_orig := i, transitions := ([] : List ETransCorr), rel := idRel }
    | some (.const _ _) | some (.copy _ _) | some (.binop _ _ _ _) | some (.boolop _ _)
    | some (.fbinop _ _ _ _) | some (.intToFloat _ _) | some (.floatToInt _ _) | some (.floatUnary _ _ _)
    | some (.fternop _ _ _ _ _)
    | some (.arrLoad _ _ _ _) | some (.arrStore _ _ _ _)
    | some (.print _ _) | some (.printInt _) | some (.printBool _) | some (.printFloat _) | some (.printString _) =>
      { pc_orig := i, rel := idRel,
        transitions := [{ origLabels := [i + 1], rel := idRel, rel_next := idRel }] }
    | some (.goto l) =>
      { pc_orig := i, rel := idRel,
        transitions := [{ origLabels := [l], rel := idRel, rel_next := idRel }] }
    | some (.ifgoto _ l) =>
      { pc_orig := i, rel := idRel,
        transitions := [{ origLabels := [l], rel := idRel, rel_next := idRel },
                        { origLabels := [i + 1], rel := idRel, rel_next := idRel }] }
    | none => default
  arr.toArray

/-- Build haltCerts from instrCerts.  Shared by all optimizers.
    Inherits the `rel` from instrCerts so observable variable checks can use identity pairs. -/
def buildHaltCerts (instrCerts : Array EInstrCert) (trans : Prog)
    : Array EHaltCert :=
  let arr := (List.range trans.size).map fun i =>
    let ic := instrCerts.getD i default
    { pc_orig := ic.pc_orig, rel := ic.rel : EHaltCert }
  arr.toArray

/-- Sorted list of kept orig PCs, indexed by trans PC.
    `kept[i] = true` means orig PC `i` is retained.
    Used by compacting optimizers (DCE, Peephole). -/
def buildOrigMap (kept : Array Bool) : Array Nat :=
  ((List.range kept.size).filterMap fun i =>
    if kept.getD i false then some i else none).toArray

/-- Reverse mapping: orig PC → trans PC (0 for removed PCs).
    Used by compacting optimizers (DCE, Peephole). -/
def buildRevMap (origMap : Array Nat) (origSize : Nat) : Array Nat :=
  (List.range origMap.size).foldl (fun arr i =>
    match origMap[i]? with
    | some pc => if pc < arr.size then arr.set! pc i else arr
    | none => arr
  ) (Array.replicate origSize 0)

-- ============================================================
-- § 6. Individual check functions
-- ============================================================

/-- **Condition 1**: Start labels correspond, initial variable map is identity. -/
def checkStartCorrespondenceExec (cert : ECertificate) : Bool :=
  match cert.instrCerts[0]? with
  | some ic => ic.pc_orig == 0
  | none    => false

/-- **Condition 2a**: Invariants are trivially true at label 0. -/
def checkInvariantsAtStartExec (cert : ECertificate) : Bool :=
  (cert.inv_orig.getD 0 ([] : EInv)).isEmpty &&
  (cert.inv_trans.getD 0 ([] : EInv)).isEmpty

/-- **Condition 2c**: Expression relation at label 0 consists only of identity pairs
    (both programs start from the same initial state). -/
def checkRelAtStartExec (cert : ECertificate) : Bool :=
  (cert.instrCerts.getD 0 default).rel.all fun (e_o, e_t) => e_o == e_t

-- ============================================================
-- § 2d. Fast HashMap-based lookups for checker performance
-- ============================================================

abbrev FastVarMap := Std.HashMap String Expr

def FastVarMap.ofList (ss : List (Var × Expr)) : FastVarMap :=
  ss.reverse.foldl (fun m (v, e) => m.insert v e) {}

/-- Per-PC cache: build a `(FastVarMap, fuel)` for every invariant in `invs`.
    Used by `checkCertificateExec` to share invariant maps across the three
    check functions (`checkInvariantsPreserved`, `checkAllTransitions`,
    `checkRelConsistency`) instead of letting each rebuild its own. -/
def buildInvMaps (invs : Array EInv) : Array (FastVarMap × Nat) :=
  invs.map fun inv => (FastVarMap.ofList inv, sdFuel inv)

/-- Lookup helper: extracts `(FastVarMap, fuel)` for a PC, with the same
    "empty invariant" default that the inline-build call sites use. -/
@[inline] def invMapAt (invMaps : Array (FastVarMap × Nat)) (pc : Nat) :
    FastVarMap × Nat :=
  invMaps.getD pc (FastVarMap.ofList [], sdFuel [])

/-- Looking up the cache built by `buildInvMaps` agrees with what the
    inline-build call sites compute: `(FastVarMap.ofList inv_pre, sdFuel inv_pre)`
    where `inv_pre = invs.getD pc []`. The default-value cases align because
    `f [] = (FastVarMap.ofList [], sdFuel [])` matches `invMapAt`'s default. -/
theorem invMapAt_buildInvMaps (invs : Array EInv) (pc : Nat) :
    invMapAt (buildInvMaps invs) pc =
      (FastVarMap.ofList (invs.getD pc ([] : EInv)),
       sdFuel (invs.getD pc ([] : EInv))) := by
  unfold invMapAt buildInvMaps
  by_cases hpc : pc < invs.size
  · simp [Array.getD, hpc, Array.size_map, Array.getElem_map]
  · simp [Array.getD, hpc, Array.size_map]


def Expr.substSymFast (m : FastVarMap) : Expr → Expr
  | .lit n      => .lit n
  | .blit b     => .blit b
  | .var v      => m.getD v (.var v)
  | .bin op a b => .bin op (a.substSymFast m) (b.substSymFast m)
  | .tobool e       => .tobool (e.substSymFast m)
  | .cmpE op a b    => .cmpE op (a.substSymFast m) (b.substSymFast m)
  | .cmpLitE op a n => .cmpLitE op (a.substSymFast m) n
  | .notE e         => .notE (e.substSymFast m)
  | .andE a b       => .andE (a.substSymFast m) (b.substSymFast m)
  | .orE a b        => .orE (a.substSymFast m) (b.substSymFast m)
  | .arrRead arr idx => .arrRead arr (idx.substSymFast m)
  | .flit n          => .flit n
  | .fbin op a b     => .fbin op (a.substSymFast m) (b.substSymFast m)
  | .fcmpE op a b    => .fcmpE op (a.substSymFast m) (b.substSymFast m)
  | .intToFloat e    => .intToFloat (e.substSymFast m)
  | .floatToInt e    => .floatToInt (e.substSymFast m)
  | .floatUnary op e  => .floatUnary op (e.substSymFast m)
  | .ftern op a b c   => .ftern op (a.substSymFast m) (b.substSymFast m) (c.substSymFast m)
  | .farrRead arr idx => .farrRead arr (idx.substSymFast m)

def Expr.simplifyFast (m : FastVarMap) : Expr → Expr
  | .lit n => .lit n
  | .blit b => .blit b
  | .var v => m.getD v (.var v)
  | .bin op a b =>
    match a.simplifyFast m, b.simplifyFast m with
    | .lit na, .lit nb => .lit (op.eval na nb)
    | a', b'           => Expr.reassoc op a' b'
  -- See `Expr.simplify`: recurse so invariant substitution reaches inside comparisons.
  | .tobool e       => .tobool (e.simplifyFast m)
  | .cmpE op a b    => .cmpE op (a.simplifyFast m) (b.simplifyFast m)
  | .cmpLitE op a n => .cmpLitE op (a.simplifyFast m) n
  | .notE e         => .notE (e.simplifyFast m)
  | .andE a b       => .andE (a.simplifyFast m) (b.simplifyFast m)
  | .orE a b        => .orE (a.simplifyFast m) (b.simplifyFast m)
  | .arrRead arr idx => .arrRead arr (idx.simplifyFast m)
  | .flit n         => .flit n
  | .fbin op a b    =>
    let a' := a.simplifyFast m; let b' := b.simplifyFast m
    match op, a', b' with
    -- See `Expr.simplify`: both-fmul must NOT swap, to keep the normal form
    -- confluent (no parity oscillation).
    | .fadd, .fbin .fmul _ _, .fbin .fmul _ _ => .fbin .fadd a' b'
    | .fadd, .fbin .fmul _ _, _ => .fbin .fadd b' a'
    | _, _, _ => .fbin op a' b'
  | .fcmpE op a b   => .fcmpE op (a.simplifyFast m) (b.simplifyFast m)
  | .intToFloat e   => .intToFloat (e.simplifyFast m)
  | .floatToInt e   => .floatToInt (e.simplifyFast m)
  | .floatUnary op e => .floatUnary op (e.simplifyFast m)
  | .ftern op a b c => match op with
    | .fmadd => .fbin .fadd (a.simplifyFast m) (.fbin .fmul (b.simplifyFast m) (c.simplifyFast m))
    | .fmsub => .fbin .fsub (a.simplifyFast m) (.fbin .fmul (b.simplifyFast m) (c.simplifyFast m))
  | .farrRead arr idx => .farrRead arr (idx.simplifyFast m)

-- ============================================================
-- § 4a. FastVarMap ↔ list-based lookup equivalence
-- ============================================================

/-- Core lemma: `foldl insert` with last-wins semantics relates to `find?` on the
    reversed list (which finds the last matching entry, i.e. same as foldl's winner). -/
private theorem foldl_insert_getD
    (l : List (Var × Expr)) (m : FastVarMap) (v : Var) (d : Expr) :
    (l.foldl (fun m (p : Var × Expr) => m.insert p.1 p.2) m).getD v d =
    match l.reverse.find? (fun p => p.1 == v) with
    | some (_, e) => e
    | none => m.getD v d := by
  induction l generalizing m with
  | nil => simp
  | cons p rest ih =>
    simp only [List.foldl]; rw [ih]
    simp only [List.reverse_cons, List.find?_append]
    cases hfind : rest.reverse.find? (fun p => p.1 == v) with
    | some val => simp [Option.or]
    | none =>
      simp only [Option.or, List.find?_cons, List.find?_nil, Std.HashMap.getD_insert]
      cases hbeq : (p.1 == v) <;> simp

/-- `FastVarMap.ofList` lookup agrees with `List.find?` (first-match semantics). -/
theorem FastVarMap.ofList_getD (ss : List (Var × Expr)) (v : Var) (d : Expr) :
    (FastVarMap.ofList ss).getD v d =
    match ss.find? (fun p => p.1 == v) with
    | some (_, e) => e
    | none => d := by
  unfold FastVarMap.ofList
  rw [foldl_insert_getD]
  simp only [Std.HashMap.getD_empty, List.reverse_reverse]

/-- `FastVarMap.ofList` lookup agrees with `ssGet`. -/
theorem FastVarMap.ofList_getD_eq_ssGet (ss : List (Var × Expr)) (v : Var) :
    (FastVarMap.ofList ss).getD v (.var v) = ssGet ss v := by
  rw [FastVarMap.ofList_getD]; unfold ssGet; rfl

/-- `FastVarMap.ofList` lookup agrees with `lookupExpr` (used by `simplify`). -/
theorem FastVarMap.ofList_getD_eq_lookupExpr (inv : EInv) (v : Var) :
    (FastVarMap.ofList inv).getD v (.var v) =
    match lookupExpr inv v with
    | some e => e
    | none   => .var v := by
  rw [FastVarMap.ofList_getD]; unfold lookupExpr
  cases hf : inv.find? (fun p => p.1 == v) with
  | none => rfl
  | some p => simp [Option.map]

/-- Generic pattern lemma: looking up an `inv : EInv` for a literal-valued
    binding gives the same Bool whether you walk the list and pattern-match
    on the `Option (Var × Expr)` result, or look up the `FastVarMap` and
    pattern-match on the resulting `Expr`. Used by `checkDivPreservationExec`-
    and `checkBoundsPreservationExec`-style "is this var a known non-zero
    constant" lookups. -/
theorem invFindLit_eq_invMapGetD (inv : EInv) (k : Var) (P : BitVec 64 → Bool) :
    (match (FastVarMap.ofList inv).getD k (.var k) with
     | .lit c => P c | _ => false)
    = (match inv.find? (fun (v, _) => v == k) with
       | some (_, .lit c) => P c | _ => false) := by
  rw [FastVarMap.ofList_getD]
  cases h : inv.find? (fun p => p.1 == k) with
  | none => rfl
  | some pair =>
    obtain ⟨_, e⟩ := pair
    cases e <;> rfl

/-- Substitute each variable in an expression with its symbolic post-value. -/
def Expr.substSym (ss : SymStore) : Expr → Expr
  | .lit n      => .lit n
  | .blit b     => .blit b
  | .var v      => ssGet ss v
  | .bin op a b => .bin op (a.substSym ss) (b.substSym ss)
  | .tobool e       => .tobool (e.substSym ss)
  | .cmpE op a b    => .cmpE op (a.substSym ss) (b.substSym ss)
  | .cmpLitE op a n => .cmpLitE op (a.substSym ss) n
  | .notE e         => .notE (e.substSym ss)
  | .andE a b       => .andE (a.substSym ss) (b.substSym ss)
  | .orE a b        => .orE (a.substSym ss) (b.substSym ss)
  | .arrRead arr idx => .arrRead arr (idx.substSym ss)
  | .flit n          => .flit n
  | .fbin op a b     => .fbin op (a.substSym ss) (b.substSym ss)
  | .fcmpE op a b    => .fcmpE op (a.substSym ss) (b.substSym ss)
  | .intToFloat e    => .intToFloat (e.substSym ss)
  | .floatToInt e    => .floatToInt (e.substSym ss)
  | .floatUnary op e  => .floatUnary op (e.substSym ss)
  | .ftern op a b c   => .ftern op (a.substSym ss) (b.substSym ss) (c.substSym ss)
  | .farrRead arr idx => .farrRead arr (idx.substSym ss)

@[simp] theorem Expr.substSym'_eq_substSym (e : Expr) (ss : SymStore) :
    e.substSym' ss = e.substSym ss := by
  induction e with
  | lit _ | blit _ | flit _ | var _ => simp [substSym', substSym]
  | bin _ a b iha ihb => simp [substSym', substSym, iha, ihb]
  | tobool e ih => simp [substSym', substSym, ih]
  | cmpE _ a b iha ihb => simp [substSym', substSym, iha, ihb]
  | cmpLitE _ a _ ih => simp [substSym', substSym, ih]
  | notE e ih => simp [substSym', substSym, ih]
  | andE a b iha ihb => simp [substSym', substSym, iha, ihb]
  | orE a b iha ihb => simp [substSym', substSym, iha, ihb]
  | arrRead _ idx ih => simp [substSym', substSym, ih]
  | fbin _ a b iha ihb => simp [substSym', substSym, iha, ihb]
  | fcmpE _ a b iha ihb => simp [substSym', substSym, iha, ihb]
  | intToFloat e ih => simp [substSym', substSym, ih]
  | floatToInt e ih => simp [substSym', substSym, ih]
  | floatUnary _ e ih => simp [substSym', substSym, ih]
  | ftern _ a b c iha ihb ihc => simp [substSym', substSym, iha, ihb, ihc]
  | farrRead _ idx ih => simp [substSym', substSym, ih]

/-- `substSymFast` with `FastVarMap.ofList` equals `substSym`. -/
theorem Expr.substSymFast_eq_substSym (e : Expr) (ss : SymStore) :
    e.substSymFast (FastVarMap.ofList ss) = e.substSym ss := by
  induction e with
  | lit _ | blit _ | flit _ => rfl
  | var v => exact FastVarMap.ofList_getD_eq_ssGet ss v
  | bin op a b iha ihb => simp only [substSymFast, substSym, iha, ihb]
  | tobool e ih => simp only [substSymFast, substSym, ih]
  | cmpE op a b iha ihb => simp only [substSymFast, substSym, iha, ihb]
  | cmpLitE op a n ih => simp only [substSymFast, substSym, ih]
  | notE e ih => simp only [substSymFast, substSym, ih]
  | andE a b iha ihb => simp only [substSymFast, substSym, iha, ihb]
  | orE a b iha ihb => simp only [substSymFast, substSym, iha, ihb]
  | arrRead arr idx ih => simp only [substSymFast, substSym, ih]
  | fbin op a b iha ihb => simp only [substSymFast, substSym, iha, ihb]
  | fcmpE op a b iha ihb => simp only [substSymFast, substSym, iha, ihb]
  | intToFloat e ih => simp only [substSymFast, substSym, ih]
  | floatToInt e ih => simp only [substSymFast, substSym, ih]
  | floatUnary op e ih => simp only [substSymFast, substSym, ih]
  | ftern op a b c iha ihb ihc => simp only [substSymFast, substSym, iha, ihb, ihc]
  | farrRead arr idx ih => simp only [substSymFast, substSym, ih]

/-- `simplifyFast` with `FastVarMap.ofList` equals `simplify`. -/
theorem Expr.simplifyFast_eq_simplify (e : Expr) (inv : EInv) :
    e.simplifyFast (FastVarMap.ofList inv) = e.simplify inv := by
  induction e with
  | lit _ | blit _ | flit _ => rfl
  | var v => exact FastVarMap.ofList_getD_eq_lookupExpr inv v
  | bin op a b iha ihb => simp only [simplifyFast, simplify, iha, ihb]
  | tobool _ ih => simp only [simplifyFast, simplify, ih]
  | cmpE op a b iha ihb => simp only [simplifyFast, simplify, iha, ihb]
  | cmpLitE op a n ih => simp only [simplifyFast, simplify, ih]
  | notE _ ih => simp only [simplifyFast, simplify, ih]
  | andE a b iha ihb => simp only [simplifyFast, simplify, iha, ihb]
  | orE a b iha ihb => simp only [simplifyFast, simplify, iha, ihb]
  | arrRead arr idx ih => simp only [simplifyFast, simplify, ih]
  | fbin op a b iha ihb => simp only [simplifyFast, simplify, iha, ihb]
  | fcmpE op a b iha ihb => simp only [simplifyFast, simplify, iha, ihb]
  | intToFloat e ih => simp only [simplifyFast, simplify, ih]
  | floatToInt e ih => simp only [simplifyFast, simplify, ih]
  | floatUnary op e ih => simp only [simplifyFast, simplify, ih]
  | ftern op a b c iha ihb ihc => cases op <;> simp only [simplifyFast, simplify, iha, ihb, ihc]
  | farrRead arr idx ih => simp only [simplifyFast, simplify, ih]

/-- HashMap version of `simplifyDeep`: iterates `simplifyFast`. -/
def Expr.simplifyDeepFast : Nat → FastVarMap → Expr → Expr
  | 0, m, e => e.simplifyFast m
  | n + 1, m, e => (e.simplifyFast m).simplifyDeepFast n m

/-- Like `simplifyDeepFast` but stops as soon as a `simplifyFast` pass produces
    no change. Returns the same value as `simplifyDeepFast` once `simplify` has
    reached its fixed point — which it always does in ≤ `n` steps for the fuel
    we use — but typically in 1-3 iterations instead of full `fuel`. -/
def Expr.simplifyDeepFastEarly : Nat → FastVarMap → Expr → Expr
  | 0, m, e => e.simplifyFast m
  | n + 1, m, e =>
    let e' := e.simplifyFast m
    if e' == e then e' else e'.simplifyDeepFastEarly n m

/-- `simplifyDeepFast` with `FastVarMap.ofList` equals `simplifyDeep`. -/
theorem Expr.simplifyDeepFast_eq_simplifyDeep (n : Nat) (e : Expr) (inv : EInv) :
    e.simplifyDeepFast n (FastVarMap.ofList inv) = e.simplifyDeep n inv := by
  induction n generalizing e with
  | zero =>
    show e.simplifyFast _ = e.simplify _
    exact Expr.simplifyFast_eq_simplify e inv
  | succ n ih =>
    show (e.simplifyFast _).simplifyDeepFast n _ = (e.simplify inv).simplifyDeep n inv
    rw [Expr.simplifyFast_eq_simplify]; exact ih _

/-- Applying `simplifyFast` to a fixpoint stays at the fixpoint, so
    `simplifyDeepFast n m e = e` for any `n`. -/
theorem Expr.simplifyDeepFast_idempotent_at_fp
    (m : FastVarMap) (e : Expr) (hfp : e.simplifyFast m = e) :
    ∀ n, e.simplifyDeepFast n m = e := by
  intro n
  induction n with
  | zero => exact hfp
  | succ n ih =>
    show (e.simplifyFast m).simplifyDeepFast n m = e
    rw [hfp]; exact ih

/-- `simplifyDeepFastEarly` and `simplifyDeepFast` agree at every fuel. -/
theorem Expr.simplifyDeepFastEarly_eq_simplifyDeepFast
    (n : Nat) (m : FastVarMap) (e : Expr) :
    e.simplifyDeepFastEarly n m = e.simplifyDeepFast n m := by
  induction n generalizing e with
  | zero => rfl
  | succ n ih =>
    show (let e' := e.simplifyFast m
          if e' == e then e' else e'.simplifyDeepFastEarly n m)
         = (e.simplifyFast m).simplifyDeepFast n m
    by_cases hb : e.simplifyFast m == e
    · have hfp : e.simplifyFast m = e := (beq_iff_eq).mp hb
      simp only [hb, ↓reduceIte]
      rw [hfp]
      exact (Expr.simplifyDeepFast_idempotent_at_fp m e hfp n).symm
    · simp only [hb, Bool.false_eq_true, ↓reduceIte]
      exact ih (e.simplifyFast m)

/-- Equivalence specialised to the actual call shape used in the live
    checker (`FastVarMap.ofList inv` and `sdFuel inv`). This is the
    rewrite the soundness proofs need. -/
theorem Expr.simplifyDeepFastEarly_eq_simplifyDeep
    (inv : EInv) (e : Expr) :
    e.simplifyDeepFastEarly (sdFuel inv) (FastVarMap.ofList inv)
      = e.simplifyDeep (sdFuel inv) inv := by
  rw [Expr.simplifyDeepFastEarly_eq_simplifyDeepFast]
  exact Expr.simplifyDeepFast_eq_simplifyDeep _ e inv

/-- The HashMap-based variable set lookup used in `checkRelConsistency` is equivalent
    to the list-based `any` check used in the spec theorems. -/
theorem relVarSet_contains_eq_any (rel_pre : EExprRel) (w : Var) :
    (Std.HashMap.ofList (rel_pre.filterMap fun (_, e_t') =>
      match e_t' with | .var v => some (v, ()) | _ => none)).contains w =
    (rel_pre.any fun (_, e_t') => e_t' == .var w) := by
  rw [Std.HashMap.contains_ofList]
  induction rel_pre with
  | nil => simp
  | cons p rest ih =>
    obtain ⟨e_o, e_t'⟩ := p
    simp only [List.filterMap_cons, List.any_cons]
    cases e_t' with
    | var v =>
      simp only [List.map_cons, List.contains_cons, BEq.beq, Expr.var.injEq, ih]
      congr 1; exact decide_eq_decide.mpr ⟨Eq.symm, Eq.symm⟩
    | _ => simpa [BEq.beq] using ih

/-- Check that a single invariant atom `(x, e)` is preserved by an instruction.
    Uses symbolic execution: the post-value of `x` and the post-value of `e`
    (with each variable replaced by its symbolic post-value) must be equal
    when simplified under the pre-invariant. -/
def checkInvAtom (inv_pre : EInv) (instr : TAC) (atom : Var × Expr) : Bool :=
  let (ss, _) := execSymbolic ([] : SymStore) ([] : SymArrayMem) instr
  let fuel := sdFuel inv_pre
  let lhs := (ssGet ss atom.1).simplifyDeep fuel inv_pre
  let rhs := (atom.2.substSym ss).simplifyDeep fuel inv_pre
  lhs == rhs

/-- HashMap-backed variant of `checkInvAtom` taking a precomputed `FastVarMap`
    plus the fuel. Equivalent to `checkInvAtom inv_pre instr atom` when
    `invMap = FastVarMap.ofList inv_pre` and `fuel = sdFuel inv_pre`, but
    avoids re-building the map per atom. -/
def checkInvAtomFast (invMap : FastVarMap) (fuel : Nat) (instr : TAC)
    (atom : Var × Expr) : Bool :=
  let (ss, _) := execSymbolic ([] : SymStore) ([] : SymArrayMem) instr
  let lhs := (ssGet ss atom.1).simplifyDeepFastEarly fuel invMap
  let rhs := (atom.2.substSym ss).simplifyDeepFastEarly fuel invMap
  lhs == rhs

/-- Compute reachable PCs from PC 0 via successor edges. -/
partial def reachable (prog : Prog) : Array Bool :=
  let rec go (visited : Array Bool) (worklist : List Nat) : Array Bool :=
    match worklist with
    | [] => visited
    | pc :: rest =>
      if pc < prog.size && !(visited.getD pc false) then
        let visited' := visited.set! pc true
        let succs := match prog[pc]? with
          | some instr => instr.successors pc
          | none => []
        go visited' (succs ++ rest)
      else go visited rest
  go (Array.replicate prog.size false) (0 :: [])

/-- Compact a program: remove unreachable PCs and remap labels.
    Returns `(compacted, origMap, revMap)`. -/
def compactProg (prog : Prog) (reached : Array Bool) : Prog × Array Nat × Array Nat :=
  let origMap := buildOrigMap reached
  let revMap := buildRevMap origMap prog.size
  let arr := (List.range origMap.size).map fun i =>
    match origMap[i]? with
    | some pc =>
      match prog[pc]? with
      | some (.goto l)    => .goto (revMap.getD l 0)
      | some (.ifgoto b l) => .ifgoto b (revMap.getD l 0)
      | some instr        => instr
      | none              => .halt
    | none => .halt
  ({ code := arr.toArray,
     observable := prog.observable, arrayDecls := prog.arrayDecls },
   origMap, revMap)

/-- **Condition 2b**: Invariants are preserved by both programs.

    The pre-invariant `inv[pc]` is shared across all atoms of all successors,
    so we materialize a `FastVarMap` once per pc and reuse it for every
    `checkInvAtomFast` call. This collapses the per-atom O(|inv|²) cost of
    list-based `simplifyDeep` to O(|inv|). -/
def checkInvariantsPreservedExec (cert : ECertificate) : Bool :=
  let checkProg (prog : Prog) (inv : Array EInv) : Bool :=
    (List.range prog.size).all fun pc =>
      match prog[pc]? with
      | some instr =>
        let inv_pre := inv.getD pc ([] : EInv)
        let invMap := FastVarMap.ofList inv_pre
        let fuel := sdFuel inv_pre
        (instr.successors pc).all fun pc' =>
          (inv.getD pc' ([] : EInv)).all (checkInvAtomFast invMap fuel instr)
      | none => true
  checkProg cert.orig cert.inv_orig &&
  checkProg cert.trans cert.inv_trans

/-- Cached variant of `checkInvariantsPreservedExec`: takes precomputed
    per-PC `(FastVarMap, fuel)` arrays instead of building them inline. The
    caller (`checkCertificateExec`) builds these once and shares them with
    `checkAllTransitionsFromMaps` so invariant maps are not rebuilt. -/
def checkInvariantsPreservedFromMaps (cert : ECertificate)
    (invMaps_orig invMaps_trans : Array (FastVarMap × Nat)) : Bool :=
  let checkProg (prog : Prog) (inv : Array EInv)
      (invMaps : Array (FastVarMap × Nat)) : Bool :=
    (List.range prog.size).all fun pc =>
      match prog[pc]? with
      | some instr =>
        let (invMap, fuel) := invMapAt invMaps pc
        (instr.successors pc).all fun pc' =>
          (inv.getD pc' ([] : EInv)).all (checkInvAtomFast invMap fuel instr)
      | none => true
  checkProg cert.orig cert.inv_orig invMaps_orig &&
  checkProg cert.trans cert.inv_trans invMaps_trans

/-- `checkInvariantsPreservedFromMaps` agrees with `checkInvariantsPreservedExec`
    when called with maps built from the cert's invariants — i.e., the cache
    is just the per-PC pre-computation that the original does inline. -/
theorem checkInvariantsPreservedFromMaps_eq (cert : ECertificate) :
    checkInvariantsPreservedFromMaps cert
      (buildInvMaps cert.inv_orig) (buildInvMaps cert.inv_trans)
      = checkInvariantsPreservedExec cert := by
  unfold checkInvariantsPreservedFromMaps checkInvariantsPreservedExec
  simp only [invMapAt_buildInvMaps]

/-- **Condition 4a**: Each halt in trans corresponds to a halt in orig.
    Uses `instrCerts` (not `haltCerts`) for consistency with the simulation. -/
def checkHaltCorrespondenceExec (cert : ECertificate) : Bool :=
  (List.range cert.trans.size).all fun pc =>
    match cert.trans[pc]? with
    | some .halt =>
      match cert.orig[(cert.instrCerts.getD pc default).pc_orig]? with
      | some .halt => true
      | _          => false
    | _ => true

/-- **Condition 4b**: Observable equivalence at halt.
    For each halt in trans, every observable variable must map to itself
    via `buildSubstMap` of the expression relation (i.e., `ssGet (buildSubstMap rel) v = .var v`).
    This ensures the transformed program produces the same observable values
    as the original at halt. -/
def checkHaltObservableExec (cert : ECertificate) : Bool :=
  (List.range cert.trans.size).all fun pc =>
    match cert.trans[pc]? with
    | some .halt =>
      let ic := cert.instrCerts.getD pc default
      cert.observable.all fun v =>
        ic.rel.any fun (e_o, e_t) => e_t == .var v && e_o == .var v
    | _ => true

/-- Compute the next PC from an instruction, using symbolic evaluation for ifgoto. -/
def computeNextPC (instr : TAC) (pc : Label) (ss : SymStore) (inv : EInv) : Option Label :=
  match instr with
  | .const _ _ | .copy _ _ | .binop _ _ _ _ | .boolop _ _ => some (pc + 1)
  | .fbinop _ _ _ _ | .intToFloat _ _ | .floatToInt _ _ | .floatUnary _ _ _ | .fternop _ _ _ _ _ => some (pc + 1)
  | .arrLoad _ _ _ _ | .arrStore _ _ _ _ => some (pc + 1)
  | .print _ _ | .printInt _ | .printBool _ | .printFloat _ | .printString _ => some (pc + 1)
  | .goto l => some l
  | .ifgoto b l =>
    match b.symEval ss inv with
    | some true  => some l
    | some false => some (pc + 1)
    | none       => none
  | .halt => none

/-- HashMap-backed variants of `BoolExpr.normalize` / `BoolExpr.symEval` and
    the call sites that thread the same `inv` through a recursive walk.
    Each takes a precomputed `FastVarMap` and `fuel` instead of an `EInv`. -/
def BoolExpr.normalizeFast (ss : SymStore) (invMap : FastVarMap) (fuel : Nat) :
    BoolExpr → BoolExpr
  | .lit b => .lit b
  | .bvar x =>
    match (ssGet ss x).simplifyDeepFastEarly fuel invMap with
    | .blit b => .lit b
    | e'      => .bexpr e'
  | .cmp op a b =>
    match (a.substSym' ss).simplifyDeepFastEarly fuel invMap,
          (b.substSym' ss).simplifyDeepFastEarly fuel invMap with
    | .lit va, .lit vb => .lit (op.eval va vb)
    | a', b' => .cmp op a' b'
  | .not e => match e.normalizeFast ss invMap fuel with
    | .lit b => .lit (!b)
    | .not inner => inner
    | e' => .not e'
  | .fcmp op a b =>
    match (a.substSym' ss).simplifyDeepFastEarly fuel invMap,
          (b.substSym' ss).simplifyDeepFastEarly fuel invMap with
    | .flit va, .flit vb => .lit (FloatCmpOp.eval op va vb)
    | a', b' => .fcmp op a' b'
  | .bexpr e =>
    match (e.substSym' ss).simplifyDeepFastEarly fuel invMap with
    | .blit b => .lit b
    | e'      => .bexpr e'

def BoolExpr.symEvalFast (ss : SymStore) (invMap : FastVarMap) (fuel : Nat) :
    BoolExpr → Option Bool
  | .lit b => some b
  | .bvar x =>
    match (ssGet ss x).simplifyDeepFastEarly fuel invMap with
    | .blit b => some b
    | _ => none
  | .cmp op a b =>
    match (a.substSym' ss).simplifyDeepFastEarly fuel invMap,
          (b.substSym' ss).simplifyDeepFastEarly fuel invMap with
    | .lit va, .lit vb => some (op.eval va vb)
    | _, _ => none
  | .not e => e.symEvalFast ss invMap fuel |>.map (!·)
  | .fcmp _op _a _b => none
  | .bexpr e =>
    match (e.substSym' ss).simplifyDeepFastEarly fuel invMap with
    | .blit b => some b
    | _ => none

def computeNextPCFast (instr : TAC) (pc : Label) (ss : SymStore)
    (invMap : FastVarMap) (fuel : Nat) : Option Label :=
  match instr with
  | .const _ _ | .copy _ _ | .binop _ _ _ _ | .boolop _ _ => some (pc + 1)
  | .fbinop _ _ _ _ | .intToFloat _ _ | .floatToInt _ _ | .floatUnary _ _ _ | .fternop _ _ _ _ _ => some (pc + 1)
  | .arrLoad _ _ _ _ | .arrStore _ _ _ _ => some (pc + 1)
  | .print _ _ | .printInt _ | .printBool _ | .printFloat _ | .printString _ => some (pc + 1)
  | .goto l => some l
  | .ifgoto b l =>
    match b.symEvalFast ss invMap fuel with
    | some true  => some l
    | some false => some (pc + 1)
    | none       => none
  | .halt => none

/-- Check that an arrLoad/arrStore instruction's index doesn't alias any existing SAM entry
    for the same array.  Uses simplification under the invariant to compare indices. -/
def checkInstrAliasOk (instr : TAC) (ss : SymStore) (sam : SymArrayMem) (inv : EInv) : Bool :=
  match instr with
  | .arrLoad _ arr idx _ | .arrStore arr idx _ _ =>
    let idx_sym := ssGet ss idx
    sam.all fun (a, i, _) =>
      !(a == arr) || (i == idx_sym) ||
      match i.simplifyDeep (sdFuel inv) inv, idx_sym.simplifyDeep (sdFuel inv) inv with
      | .lit n, .lit m => !(n == m)
      | _, _ => false
  | _ => true

def checkInstrAliasOkFast (instr : TAC) (ss : SymStore) (sam : SymArrayMem)
    (invMap : FastVarMap) (fuel : Nat) : Bool :=
  match instr with
  | .arrLoad _ arr idx _ | .arrStore arr idx _ _ =>
    let idx_sym := ssGet ss idx
    sam.all fun (a, i, _) =>
      !(a == arr) || (i == idx_sym) ||
      match i.simplifyDeepFastEarly fuel invMap, idx_sym.simplifyDeepFastEarly fuel invMap with
      | .lit n, .lit m => !(n == m)
      | _, _ => false
  | _ => true

/-- Verify that the original path is structurally valid:
    at each PC, the instruction's successor matches the next label. -/
def checkOrigPath (orig : Prog) (ss : SymStore) (sam : SymArrayMem) (inv : EInv)
    (pc : Label) (labels : List Label) (pc_next : Label)
    (branchInfo : Option (BoolExpr × Bool) := none) : Bool :=
  match labels with
  | [] => pc == pc_next
  | nextPC :: rest =>
    match orig[pc]? with
    | some instr =>
      let pcOk := match computeNextPC instr pc ss inv with
        | some pc' => pc' == nextPC
        | none =>
          match branchInfo, instr with
          | some (origCond, true),  .ifgoto b l =>
            b.normalize ss inv == origCond.normalize ss inv && nextPC == l
          | some (origCond, false), .ifgoto b _ =>
            b.normalize ss inv == origCond.normalize ss inv && nextPC == pc + 1
          | _, _ => false
      let aliasOk := checkInstrAliasOk instr ss sam inv
      let (ss', sam') := execSymbolic ss sam instr
      pcOk && aliasOk &&
      checkOrigPath orig ss' sam' inv nextPC rest pc_next none
    | none => false

/-- HashMap-backed mirror of `checkOrigPath`. The caller materializes
    `invMap = FastVarMap.ofList inv` and `fuel = sdFuel inv` once and threads
    them through the recursion, so we never rebuild the map per orig step. -/
def checkOrigPathFast (orig : Prog) (ss : SymStore) (sam : SymArrayMem)
    (invMap : FastVarMap) (fuel : Nat)
    (pc : Label) (labels : List Label) (pc_next : Label)
    (branchInfo : Option (BoolExpr × Bool) := none) : Bool :=
  match labels with
  | [] => pc == pc_next
  | nextPC :: rest =>
    match orig[pc]? with
    | some instr =>
      let pcOk := match computeNextPCFast instr pc ss invMap fuel with
        | some pc' => pc' == nextPC
        | none =>
          match branchInfo, instr with
          | some (origCond, true),  .ifgoto b l =>
            b.normalizeFast ss invMap fuel == origCond.normalizeFast ss invMap fuel
              && nextPC == l
          | some (origCond, false), .ifgoto b _ =>
            b.normalizeFast ss invMap fuel == origCond.normalizeFast ss invMap fuel
              && nextPC == pc + 1
          | _, _ => false
      let aliasOk := checkInstrAliasOkFast instr ss sam invMap fuel
      let (ss', sam') := execSymbolic ss sam instr
      pcOk && aliasOk &&
      checkOrigPathFast orig ss' sam' invMap fuel nextPC rest pc_next none
    | none => false

-- ============================================================
-- § 6a. Wrapper-equivalence lemmas
--
-- Each Fast wrapper is point-wise equal to the original wrapper when called
-- with `FastVarMap.ofList inv` and `sdFuel inv`. Soundness proofs for the
-- runtime checker bodies (`checkInvariantsPreservedExec`,
-- `checkAllTransitionsExec`, `checkRelConsistency`) rewrite Fast → original
-- via these equalities and reuse the existing reasoning about the originals.
-- The originals are kept around solely as proof intermediates and are not
-- called from any live path.
-- ============================================================

/-- `checkInvAtomFast` with the canonical map/fuel equals `checkInvAtom`. -/
theorem checkInvAtomFast_eq_checkInvAtom
    (inv_pre : EInv) (instr : TAC) (atom : Var × Expr) :
    checkInvAtomFast (FastVarMap.ofList inv_pre) (sdFuel inv_pre) instr atom
      = checkInvAtom inv_pre instr atom := by
  unfold checkInvAtomFast checkInvAtom
  simp only [Expr.simplifyDeepFastEarly_eq_simplifyDeep]

/-- Function-extensionality form of `checkInvAtomFast_eq_checkInvAtom`,
    needed when the function is partially applied (e.g., as the predicate
    of a `List.all`). -/
theorem checkInvAtomFast_eq_checkInvAtom_fn (inv_pre : EInv) (instr : TAC) :
    checkInvAtomFast (FastVarMap.ofList inv_pre) (sdFuel inv_pre) instr
      = checkInvAtom inv_pre instr := by
  funext atom; exact checkInvAtomFast_eq_checkInvAtom inv_pre instr atom

/-- `BoolExpr.normalizeFast` with the canonical map/fuel equals
    `BoolExpr.normalize`. -/
theorem BoolExpr.normalizeFast_eq_normalize
    (b : BoolExpr) (ss : SymStore) (inv : EInv) :
    b.normalizeFast ss (FastVarMap.ofList inv) (sdFuel inv)
      = b.normalize ss inv := by
  induction b with
  | lit _ => rfl
  | bvar x =>
    simp only [BoolExpr.normalizeFast, BoolExpr.normalize,
      Expr.simplifyDeepFastEarly_eq_simplifyDeep]
  | cmp op a b =>
    simp only [BoolExpr.normalizeFast, BoolExpr.normalize,
      Expr.simplifyDeepFastEarly_eq_simplifyDeep]
  | fcmp op a b =>
    simp only [BoolExpr.normalizeFast, BoolExpr.normalize,
      Expr.simplifyDeepFastEarly_eq_simplifyDeep]
  | not e ih =>
    simp only [BoolExpr.normalizeFast, BoolExpr.normalize, ih]
  | bexpr e =>
    simp only [BoolExpr.normalizeFast, BoolExpr.normalize,
      Expr.simplifyDeepFastEarly_eq_simplifyDeep]

/-- `BoolExpr.symEvalFast` with the canonical map/fuel equals
    `BoolExpr.symEval`. -/
theorem BoolExpr.symEvalFast_eq_symEval
    (b : BoolExpr) (ss : SymStore) (inv : EInv) :
    b.symEvalFast ss (FastVarMap.ofList inv) (sdFuel inv)
      = b.symEval ss inv := by
  induction b with
  | lit _ => rfl
  | bvar x =>
    simp only [BoolExpr.symEvalFast, BoolExpr.symEval,
      Expr.simplifyDeepFastEarly_eq_simplifyDeep]
  | cmp op a b =>
    simp only [BoolExpr.symEvalFast, BoolExpr.symEval,
      Expr.simplifyDeepFastEarly_eq_simplifyDeep]
  | fcmp op a b => rfl
  | not e ih =>
    simp only [BoolExpr.symEvalFast, BoolExpr.symEval, ih]
  | bexpr e =>
    simp only [BoolExpr.symEvalFast, BoolExpr.symEval,
      Expr.simplifyDeepFastEarly_eq_simplifyDeep]

/-- `computeNextPCFast` with the canonical map/fuel equals `computeNextPC`. -/
theorem computeNextPCFast_eq_computeNextPC
    (instr : TAC) (pc : Label) (ss : SymStore) (inv : EInv) :
    computeNextPCFast instr pc ss (FastVarMap.ofList inv) (sdFuel inv)
      = computeNextPC instr pc ss inv := by
  cases instr <;>
    simp only [computeNextPCFast, computeNextPC,
      BoolExpr.symEvalFast_eq_symEval]

/-- `checkInstrAliasOkFast` with the canonical map/fuel equals
    `checkInstrAliasOk`. -/
theorem checkInstrAliasOkFast_eq_checkInstrAliasOk
    (instr : TAC) (ss : SymStore) (sam : SymArrayMem) (inv : EInv) :
    checkInstrAliasOkFast instr ss sam (FastVarMap.ofList inv) (sdFuel inv)
      = checkInstrAliasOk instr ss sam inv := by
  cases instr <;>
    simp only [checkInstrAliasOkFast, checkInstrAliasOk,
      Expr.simplifyDeepFastEarly_eq_simplifyDeep]

/-- `checkOrigPathFast` with the canonical map/fuel equals `checkOrigPath`. -/
theorem checkOrigPathFast_eq_checkOrigPath
    (orig : Prog) (inv : EInv) :
    ∀ (ss : SymStore) (sam : SymArrayMem) (pc : Label) (labels : List Label)
      (pc_next : Label) (branchInfo : Option (BoolExpr × Bool)),
    checkOrigPathFast orig ss sam (FastVarMap.ofList inv) (sdFuel inv)
        pc labels pc_next branchInfo
      = checkOrigPath orig ss sam inv pc labels pc_next branchInfo := by
  intro ss sam pc labels
  induction labels generalizing ss sam pc with
  | nil =>
    intro pc_next branchInfo
    rfl
  | cons nextPC rest ih =>
    intro pc_next branchInfo
    unfold checkOrigPathFast checkOrigPath
    cases horig : orig[pc]? with
    | none => rfl
    | some instr =>
      simp only [computeNextPCFast_eq_computeNextPC,
        BoolExpr.normalizeFast_eq_normalize,
        checkInstrAliasOkFast_eq_checkInstrAliasOk]
      have hrec := ih (execSymbolic ss sam instr).1 (execSymbolic ss sam instr).2
                     nextPC pc_next none
      rw [hrec]

/-- Check expression relation consistency via symbolic execution.
    For every `(e_o, e_t)` pair in `rel_post`, the original-side expression
    after symbolic execution must agree with the transformed symbolic execution
    value after substituting the pre-relation map, both simplified under `inv_orig`.
    Only iterates over pairs claimed by the certificate — no all-variables sweep. -/
def checkRelConsistency
    (orig : Prog) (pc_orig : Label) (origLabels : List Label) (transInstr : TAC)
    (inv_orig : EInv) (rel_pre rel_post : EExprRel) : Bool :=
  let (origSS, origSAM) := execPath orig ([] : SymStore) ([] : SymArrayMem) pc_orig origLabels
  let (transSS, transSAM) := execSymbolic ([] : SymStore) ([] : SymArrayMem) transInstr
  let preSubst := buildSubstMap rel_pre
  -- Build HashMap versions for O(1) lookups in the hot inner loop
  let origSSMap := FastVarMap.ofList origSS
  let transSSMap := FastVarMap.ofList transSS
  let preSubstMap := FastVarMap.ofList preSubst
  let invMap := FastVarMap.ofList inv_orig
  let fuel := sdFuel inv_orig
  let pairCheck := rel_post.all fun (e_o, e_t) =>
    let origVal := e_o.substSymFast origSSMap |>.simplifyDeepFastEarly fuel invMap
    let transVal := (e_t.substSymFast transSSMap).substSymFast preSubstMap |>.simplifyDeepFastEarly fuel invMap
    origVal == transVal
  -- Free-variable coverage: for each (_, e_t) in rel_post, all free variables of
  -- (e_t.substSym transSS) must have a pair in rel_pre.
  -- Also covers array memory expression variables (i_t, v_t from transSAM).
  let relVarSet := Std.HashMap.ofList (rel_pre.filterMap fun (_, e_t') =>
    match e_t' with | .var w => some (w, ()) | _ => none)
  let relHasVar (w : Var) := relVarSet.contains w
  let fvCheck := rel_post.all fun (_, e_t) =>
    (e_t.substSymFast transSSMap).freeVars.all fun w => relHasVar w
  let amFvCheck := transSAM.all fun (_, i_t, v_t) =>
    i_t.freeVars.all (fun w => relHasVar w) &&
    v_t.freeVars.all (fun w => relHasVar w)
  let amCheck := origSAM.length == transSAM.length &&
    (origSAM.zip transSAM).all fun ((a_o, i_o, v_o), (a_t, i_t, v_t)) =>
      a_o == a_t &&
      i_o.simplifyDeepFastEarly fuel invMap == (i_t.substSymFast preSubstMap).simplifyDeepFastEarly fuel invMap &&
      v_o.simplifyDeepFastEarly fuel invMap == (v_t.substSymFast preSubstMap).simplifyDeepFastEarly fuel invMap
  pairCheck && fvCheck && amFvCheck && amCheck

/-- Cached variant of `checkRelConsistency`: takes a precomputed
    `(invMap, fuel)` for `inv_orig` instead of building it inline.
    The body is otherwise identical, so the call sites can share the
    map built once at the surrounding pc_t. -/
def checkRelConsistencyFromMap
    (orig : Prog) (pc_orig : Label) (origLabels : List Label) (transInstr : TAC)
    (invMap : FastVarMap) (fuel : Nat)
    (rel_pre rel_post : EExprRel) : Bool :=
  let (origSS, origSAM) := execPath orig ([] : SymStore) ([] : SymArrayMem) pc_orig origLabels
  let (transSS, transSAM) := execSymbolic ([] : SymStore) ([] : SymArrayMem) transInstr
  let preSubst := buildSubstMap rel_pre
  let origSSMap := FastVarMap.ofList origSS
  let transSSMap := FastVarMap.ofList transSS
  let preSubstMap := FastVarMap.ofList preSubst
  let pairCheck := rel_post.all fun (e_o, e_t) =>
    let origVal := e_o.substSymFast origSSMap |>.simplifyDeepFastEarly fuel invMap
    let transVal := (e_t.substSymFast transSSMap).substSymFast preSubstMap |>.simplifyDeepFastEarly fuel invMap
    origVal == transVal
  let relVarSet := Std.HashMap.ofList (rel_pre.filterMap fun (_, e_t') =>
    match e_t' with | .var w => some (w, ()) | _ => none)
  let relHasVar (w : Var) := relVarSet.contains w
  let fvCheck := rel_post.all fun (_, e_t) =>
    (e_t.substSymFast transSSMap).freeVars.all fun w => relHasVar w
  let amFvCheck := transSAM.all fun (_, i_t, v_t) =>
    i_t.freeVars.all (fun w => relHasVar w) &&
    v_t.freeVars.all (fun w => relHasVar w)
  let amCheck := origSAM.length == transSAM.length &&
    (origSAM.zip transSAM).all fun ((a_o, i_o, v_o), (a_t, i_t, v_t)) =>
      a_o == a_t &&
      i_o.simplifyDeepFastEarly fuel invMap == (i_t.substSymFast preSubstMap).simplifyDeepFastEarly fuel invMap &&
      v_o.simplifyDeepFastEarly fuel invMap == (v_t.substSymFast preSubstMap).simplifyDeepFastEarly fuel invMap
  pairCheck && fvCheck && amFvCheck && amCheck

/-- `checkRelConsistencyFromMap` agrees with `checkRelConsistency` when the
    map is built from `inv_orig`. The bodies differ only in whether
    `(invMap, fuel)` are passed in or computed inline; otherwise identical. -/
theorem checkRelConsistencyFromMap_eq
    (orig : Prog) (pc_orig : Label) (origLabels : List Label) (transInstr : TAC)
    (inv_orig : EInv) (rel_pre rel_post : EExprRel) :
    checkRelConsistencyFromMap orig pc_orig origLabels transInstr
        (FastVarMap.ofList inv_orig) (sdFuel inv_orig) rel_pre rel_post
      = checkRelConsistency orig pc_orig origLabels transInstr inv_orig rel_pre rel_post := by
  rfl

/-- A physical successor `pc_t'` of `instr` (at `pc_t`) is *statically dead* when the
    trans-side invariant determines control to flow to a different successor
    `pc_det ≠ pc_t'`. `computeNextPCFast` returns `some pc_det` exactly when the
    branch condition is constant under the invariant; an `ifgoto` whose condition the
    invariant fixes has one live edge and one dead edge. No execution from a state
    satisfying `inv_trans` takes a dead edge, so its transition need not be certified.
    For non-branch instructions and undetermined branches this is always `false`. -/
def isDeadSuccExec (instr : TAC) (pc_t pc_t' : Label)
    (invMapT : FastVarMap) (fuelT : Nat) : Bool :=
  match computeNextPCFast instr pc_t ([] : SymStore) invMapT fuelT with
  | some pc_det => pc_det != pc_t'
  | none        => false

/-- **Condition 3**: Every transition in the transformed program has a
    corresponding original-program path with consistent variable effects.

    Materializes the `inv_orig[ic.pc_orig]` `FastVarMap` once per pc_t and
    threads it through `checkOrigPathFast`. `checkRelConsistency` already
    builds its own internal map, so it stays as-is.

    Statically-dead successor edges are skipped via `isDeadSuccExec`: when the
    trans-side invariant `inv_trans` determines an `ifgoto`'s guard, the other
    successor is never executed from a state satisfying `inv_trans`, so demanding a
    valid original path for it (which cannot exist — the original never takes that
    branch) would reject correct transforms that hand the checker an UNFOLDED
    determined `ifgoto`. This is sound because `checkAllTransitionsProp` assumes
    `σ_t ⊨ inv_trans` and `computeNextPC` soundness shows no such run takes the dead
    edge. (Previously a known completeness gap; surfaced at RegAlloc, the last pass,
    which correctly does not fold branches.) -/
def checkAllTransitionsExec (cert : ECertificate) : Bool :=
  (List.range cert.trans.size).all fun pc_t =>
    match cert.trans[pc_t]? with
    | some .halt => true
    | some instr =>
      match cert.instrCerts[pc_t]? with
      | some ic =>
        let inv_orig := cert.inv_orig.getD ic.pc_orig ([] : EInv)
        let invMap := FastVarMap.ofList inv_orig
        let fuel := sdFuel inv_orig
        -- Trans-side invariant at this PC: if it determines a branch, the other
        -- physical successor is statically dead and its transition need not be
        -- certified (no actual run from a state satisfying `inv_trans` takes it).
        let inv_trans := cert.inv_trans.getD pc_t ([] : EInv)
        let invMapT := FastVarMap.ofList inv_trans
        let fuelT := sdFuel inv_trans
        (instr.successors pc_t).all fun pc_t' =>
          isDeadSuccExec instr pc_t pc_t' invMapT fuelT ||
          let ic' := cert.instrCerts.getD pc_t' default
          let branchInfo := match instr with
            | .ifgoto b l =>
              match b.mapVarsRel ic.rel with
              | some origCond =>
                if !(l == pc_t + 1) then some (origCond, pc_t' == l) else none
              | none => none
            | _ => none
          ic.transitions.any fun tc =>
            tc.rel == ic.rel &&
            tc.rel_next == ic'.rel &&
            checkOrigPathFast cert.orig ([] : SymStore) ([] : SymArrayMem) invMap fuel
              ic.pc_orig tc.origLabels ic'.pc_orig branchInfo &&
            checkRelConsistency cert.orig ic.pc_orig tc.origLabels instr
              inv_orig
              tc.rel tc.rel_next
      | none => false
    | none => true

/-- Cached variant of `checkAllTransitionsExec`: takes the precomputed
    `invMaps_orig` array built once by `checkCertificateExec`. Looks up
    `(invMap, fuel)` per `ic.pc_orig` instead of building inline, and
    threads them to `checkRelConsistencyFromMap` so the inner call also
    skips its own map build. -/
def checkAllTransitionsFromMaps (cert : ECertificate)
    (invMaps_orig : Array (FastVarMap × Nat)) : Bool :=
  (List.range cert.trans.size).all fun pc_t =>
    match cert.trans[pc_t]? with
    | some .halt => true
    | some instr =>
      match cert.instrCerts[pc_t]? with
      | some ic =>
        let (invMap, fuel) := invMapAt invMaps_orig ic.pc_orig
        let inv_trans := cert.inv_trans.getD pc_t ([] : EInv)
        let invMapT := FastVarMap.ofList inv_trans
        let fuelT := sdFuel inv_trans
        (instr.successors pc_t).all fun pc_t' =>
          isDeadSuccExec instr pc_t pc_t' invMapT fuelT ||
          let ic' := cert.instrCerts.getD pc_t' default
          let branchInfo := match instr with
            | .ifgoto b l =>
              match b.mapVarsRel ic.rel with
              | some origCond =>
                if !(l == pc_t + 1) then some (origCond, pc_t' == l) else none
              | none => none
            | _ => none
          ic.transitions.any fun tc =>
            tc.rel == ic.rel &&
            tc.rel_next == ic'.rel &&
            checkOrigPathFast cert.orig ([] : SymStore) ([] : SymArrayMem) invMap fuel
              ic.pc_orig tc.origLabels ic'.pc_orig branchInfo &&
            checkRelConsistencyFromMap cert.orig ic.pc_orig tc.origLabels instr
              invMap fuel
              tc.rel tc.rel_next
      | none => false
    | none => true

/-- `checkAllTransitionsFromMaps` agrees with `checkAllTransitionsExec` when
    the map array is built from `cert.inv_orig`. Same logic, just lookups
    instead of inline builds, and via `checkRelConsistencyFromMap` for the
    inner call (which also agrees by `checkRelConsistencyFromMap_eq`). -/
theorem checkAllTransitionsFromMaps_eq (cert : ECertificate) :
    checkAllTransitionsFromMaps cert (buildInvMaps cert.inv_orig)
      = checkAllTransitionsExec cert := by
  unfold checkAllTransitionsFromMaps checkAllTransitionsExec
  simp only [invMapAt_buildInvMaps, checkRelConsistencyFromMap_eq]

/-- **Condition 5**: Zero-step original transitions decrease the measure. -/
def checkNonterminationExec (cert : ECertificate) : Bool :=
  (List.range cert.trans.size).all fun pc_t =>
    match cert.trans[pc_t]? with
    | some .halt => true
    | some instr =>
      match cert.instrCerts[pc_t]? with
      | some ic =>
        (instr.successors pc_t).all fun pc_t' =>
          let ic' := cert.instrCerts.getD pc_t' default
          if ic.pc_orig == ic'.pc_orig then
            cert.measure.getD pc_t' 0 < cert.measure.getD pc_t 0
          else true
      | none => false
    | none => true

/-- **Condition 6**: The transformed program is non-empty and every successor
    PC is in bounds.  This ensures the transformed program never reaches an
    error state from an out-of-bounds PC.  Thin wrapper over `TAC.checkStepClosed`. -/
def checkSuccessorsInBounds (cert : ECertificate) : Bool :=
  checkStepClosed cert.trans

-- ============================================================
-- § 7. Main checker
-- ============================================================

/-- Condition 9 (error preservation for binop): for every `binop` in the
    transformed program, the original at the mapped PC also has a `binop`
    with the same operator, and both operands are related through the
    expression relation. This ensures div-by-zero errors on the
    transformed side also occur on the original side. -/
def checkDivPreservationExec (cert : ECertificate) : Bool :=
  (List.range cert.trans.size).all fun pc_t =>
    match cert.trans[pc_t]? with
    | some (.binop _ op y z) =>
      let ic := cert.instrCerts.getD pc_t default
      match cert.orig[ic.pc_orig]? with
      | some (.binop _ op' y' z') =>
        op == op' &&
        -- Only div/mod need operand correspondence via relFindOrigVar;
        -- add/sub/mul are always safe so operand mapping is not required.
        match op with
        | .div | .mod =>
          -- Dividend correspondence. Like the divisor it has a hoisted-constant
          -- fallback: the dividend never causes a div-by-zero trap, so all we need
          -- is that the trans dividend and the orig dividend hold the SAME value —
          -- either both the same renamed variable, or both the same literal (the
          -- relation maps trans `y` to a literal `c` and the orig invariant proves
          -- the orig dividend `y'` equals that same `c`).
          (relFindOrigVar ic.rel y == some y' ||
           (match (cert.inv_orig.getD ic.pc_orig ([] : EInv)).find? (fun (v, _) => v == y') with
            | some (_, .lit c) =>
              match relFindOrigExpr ic.rel y with
              | some (.lit c') => c == c'
              | _ => false
            | _ => false)) &&
          (relFindOrigVar ic.rel z == some z' ||
           -- Fallback for hoisted constants: the relation maps the trans divisor
           -- to a non-zero literal (preventing trans errors), AND the orig invariant
           -- proves the orig divisor is non-zero (ensuring orig path walkability).
           ((match relFindOrigExpr ic.rel z with
             | some (.lit c) => c != 0 | _ => false) &&
            (match (cert.inv_orig.getD ic.pc_orig ([] : EInv)).find?
               (fun (v, _) => v == z') with
             | some (_, .lit c) => c != 0 | _ => false)))
        | _ => true
      | _ => false
    | _ =>
      -- When the trans instruction is not a binop, verify the mapped orig
      -- instruction is not div/mod (otherwise we cannot transfer div-safety).
      -- Exception: if the orig invariant proves the divisor is a non-zero
      -- constant, the division is provably safe and needs no trans counterpart.
      let ic := cert.instrCerts.getD pc_t default
      match cert.orig[ic.pc_orig]? with
      | some (.binop _ .div _ z) | some (.binop _ .mod _ z) =>
        let inv := cert.inv_orig.getD ic.pc_orig ([] : EInv)
        match inv.find? (fun (v, _) => v == z) with
        | some (_, .lit c) => c != 0
        | _ => false
      | _ => true

/-- Cached variant of `checkDivPreservationExec`: looks up the divisor's
    constant value via the per-PC `FastVarMap` cache instead of `inv.find?`.
    Functionally equivalent to the original; used by `checkCertificateExec`
    so all per-PC invariant lookups go through the shared cache. -/
def checkDivPreservationFromMaps (cert : ECertificate)
    (invMaps_orig : Array (FastVarMap × Nat)) : Bool :=
  (List.range cert.trans.size).all fun pc_t =>
    match cert.trans[pc_t]? with
    | some (.binop _ op y z) =>
      let ic := cert.instrCerts.getD pc_t default
      match cert.orig[ic.pc_orig]? with
      | some (.binop _ op' y' z') =>
        op == op' &&
        match op with
        | .div | .mod =>
          (relFindOrigVar ic.rel y == some y' ||
           (match (invMapAt invMaps_orig ic.pc_orig).1.getD y' (.var y') with
            | .lit c =>
              match relFindOrigExpr ic.rel y with
              | some (.lit c') => c == c'
              | _ => false
            | _ => false)) &&
          (relFindOrigVar ic.rel z == some z' ||
           ((match relFindOrigExpr ic.rel z with
             | some (.lit c) => c != 0 | _ => false) &&
            (match (invMapAt invMaps_orig ic.pc_orig).1.getD z' (.var z') with
             | .lit c => c != 0 | _ => false)))
        | _ => true
      | _ => false
    | _ =>
      let ic := cert.instrCerts.getD pc_t default
      match cert.orig[ic.pc_orig]? with
      | some (.binop _ .div _ z) | some (.binop _ .mod _ z) =>
        let invMap := (invMapAt invMaps_orig ic.pc_orig).1
        match invMap.getD z (.var z) with
        | .lit c => c != 0
        | _ => false
      | _ => true

/-- `checkDivPreservationFromMaps` agrees with `checkDivPreservationExec`
    when the maps are built from `cert.inv_orig`. Both lookup strategies
    return the same Bool by `invFindLit_eq_invMapGetD`. -/
theorem checkDivPreservationFromMaps_eq (cert : ECertificate) :
    checkDivPreservationFromMaps cert (buildInvMaps cert.inv_orig)
      = checkDivPreservationExec cert := by
  unfold checkDivPreservationFromMaps checkDivPreservationExec
  simp only [invMapAt_buildInvMaps, invFindLit_eq_invMapGetD]

/-- **Condition 10 (error preservation for array bounds)**: for every
    `arrLoad`/`arrStore` in the transformed program, the original at the
    mapped PC has a matching array instruction on the same array with the
    same index (via the expression relation).  Combined with equal array
    sizes, this ensures OOB errors on the transformed side also occur on
    the original side. -/
def checkBoundsPreservationExec (cert : ECertificate) : Bool :=
  (List.range cert.trans.size).all fun pc_t =>
    let ic := cert.instrCerts.getD pc_t default
    let inv := cert.inv_orig.getD ic.pc_orig ([] : EInv)
    -- Check index mapping: either via relFindOrigVar or both indices are
    -- the same known constant from the original invariant (hoisted by LICM).
    let idxOk (idx idx' : Var) :=
      relFindOrigVar ic.rel idx == some idx' ||
      (match inv.find? (fun (v, _) => v == idx') with
       | some (_, .lit c) =>
         match relFindOrigExpr ic.rel idx with
         | some (.lit c') => c == c'
         | _ => false
       | _ => false)
    match cert.trans[pc_t]? with
    | some (.arrLoad _ arr idx _) =>
      match cert.orig[ic.pc_orig]? with
      | some (.arrLoad _ arr' idx' _) =>
        arr == arr' && idxOk idx idx'
      | _ => false
    | some (.arrStore arr idx _ _) =>
      match cert.orig[ic.pc_orig]? with
      | some (.arrStore arr' idx' _ _) =>
        arr == arr' && idxOk idx idx'
      | _ => false
    | _ => true

/-- Cached variant of `checkBoundsPreservationExec`: looks up the index's
    constant value via the per-PC `FastVarMap` cache instead of `inv.find?`.
    Functionally equivalent to the original. -/
def checkBoundsPreservationFromMaps (cert : ECertificate)
    (invMaps_orig : Array (FastVarMap × Nat)) : Bool :=
  (List.range cert.trans.size).all fun pc_t =>
    let ic := cert.instrCerts.getD pc_t default
    let invMap := (invMapAt invMaps_orig ic.pc_orig).1
    let idxOk (idx idx' : Var) :=
      relFindOrigVar ic.rel idx == some idx' ||
      (match invMap.getD idx' (.var idx') with
       | .lit c =>
         match relFindOrigExpr ic.rel idx with
         | some (.lit c') => c == c'
         | _ => false
       | _ => false)
    match cert.trans[pc_t]? with
    | some (.arrLoad _ arr idx _) =>
      match cert.orig[ic.pc_orig]? with
      | some (.arrLoad _ arr' idx' _) =>
        arr == arr' && idxOk idx idx'
      | _ => false
    | some (.arrStore arr idx _ _) =>
      match cert.orig[ic.pc_orig]? with
      | some (.arrStore arr' idx' _ _) =>
        arr == arr' && idxOk idx idx'
      | _ => false
    | _ => true

/-- `checkBoundsPreservationFromMaps` agrees with `checkBoundsPreservationExec`
    when the maps are built from `cert.inv_orig`. The `idxOk` lookup is the
    only difference, and `invFindLit_eq_invMapGetD` covers it. -/
theorem checkBoundsPreservationFromMaps_eq (cert : ECertificate) :
    checkBoundsPreservationFromMaps cert (buildInvMaps cert.inv_orig)
      = checkBoundsPreservationExec cert := by
  unfold checkBoundsPreservationFromMaps checkBoundsPreservationExec
  simp only [invMapAt_buildInvMaps, invFindLit_eq_invMapGetD]

/-- **Condition 12**: On each orig path, all instructions after the first are scalar,
    AND if the first orig instruction is an array op, the trans instruction at pc_t must
    also be an array op (so bounds transfer from the trans step).
    This ensures array bounds can always be established on the orig path. -/
def checkOrigPathBoundsOk (cert : ECertificate) : Bool :=
  (List.range cert.trans.size).all fun pc_t =>
    match cert.trans[pc_t]? with
    | some .halt => true
    | some _ =>
      match cert.instrCerts[pc_t]? with
      | some ic =>
        -- If orig at ic.pc_orig is an array op, trans must also be an array op
        (match cert.orig[ic.pc_orig]? with
         | some (.arrLoad ..) | some (.arrStore ..) =>
           match cert.trans[pc_t]? with
           | some (.arrLoad ..) | some (.arrStore ..) => true
           | _ => false
         | _ => true) &&
        -- All intermediate orig path labels have scalar, non-div/mod instructions
        ic.transitions.all fun tc =>
          tc.origLabels.dropLast.all fun l =>
            match cert.orig[l]? with
            | some (.binop _ .div _ _) => false
            | some (.binop _ .mod _ _) => false
            | some instr => instr.isScalar
            | none => true
      | none => false
    | none => true

/-- **Condition 11**: Both programs declare the same array sizes. -/
def checkArraySizesExec (cert : ECertificate) : Bool :=
  cert.orig.arrayDecls == cert.trans.arrayDecls

/-- Check that all invariant expressions are arrRead-free. -/
def checkNoArrReadInInvs (invs : Array EInv) : Bool :=
  invs.all fun inv => inv.all fun (_, e) => !e.hasArrRead

/-- Check that all original-side expressions in relations are arrRead-free.
    buildSubstMap extracts the first element of (e_o, .var v) pairs, so we check e_o. -/
def checkNoArrReadInRels (certs : Array EInstrCert) : Bool :=
  certs.all fun ic =>
    ic.rel.all (fun (e, _) => !e.hasArrRead) &&
    ic.transitions.all fun tc =>
      tc.rel.all (fun (e, _) => !e.hasArrRead) &&
      tc.rel_next.all (fun (e, _) => !e.hasArrRead)

/-- Collect free variables from the Expr operands of a BoolExpr.
    For `.bvar x`, includes `x` (needed for the store-relation bridge). -/
def BoolExpr.exprFreeVars : BoolExpr → List Var
  | .lit _       => []
  | .bvar x      => [x]
  | .cmp _ a b   => a.freeVars ++ b.freeVars
  | .not e       => e.exprFreeVars
  | .fcmp _ a b  => a.freeVars ++ b.freeVars
  | .bexpr e     => e.freeVars

/-- Check that all free variables in BoolExpr operands of ifgoto instructions
    in the transformed program are covered by the instruction's expression relation.
    This guarantees the `substSym` bridge in `branchInfo_of_step_with_rel`. -/
def checkBoolVarsCoveredExec (cert : ECertificate) : Bool :=
  (List.range cert.trans.size).all fun pc =>
    match cert.trans.code[pc]?, cert.instrCerts[pc]? with
    | some (.ifgoto b _), some ic =>
      b.exprFreeVars.all fun v => ic.rel.any fun (_, e_t) => e_t == .var v
    | some (.ifgoto _ _), none => false
    | _, _ => true

/-- Check that all BoolExpr operands in a program's boolop/ifgoto instructions
    are arrRead-free (no `.arrRead`/`.farrRead` sub-expressions). -/
def checkBoolExprNoArrRead (p : Prog) : Bool :=
  p.code.all fun instr =>
    match instr with
    | .boolop _ be | .ifgoto be _ => !be.hasArrRead
    | _ => true

/-- Soundness: `checkBoolExprNoArrRead` implies every BoolExpr in the program is arrRead-free. -/
theorem checkBoolExprNoArrRead_sound (p : Prog)
    (h : checkBoolExprNoArrRead p = true) :
    ∀ (pc : Nat) (instr : TAC), p[pc]? = some instr →
      (∀ x be, instr = TAC.boolop x be → be.hasArrRead = false) ∧
      (∀ b l, instr = TAC.ifgoto b l → b.hasArrRead = false) := by
  intro pc instr hinstr
  unfold checkBoolExprNoArrRead at h
  have hbound := bound_of_getElem? hinstr
  have hget : p.code[pc] = instr :=
    Option.some.inj ((Array.getElem?_eq_getElem hbound).symm.trans hinstr)
  have hall := (Array.all_eq_true.mp h) pc hbound
  rw [hget] at hall
  constructor
  · intro x be heq; subst heq; simp at hall; exact hall
  · intro b l heq; subst heq; simp at hall; exact hall

/-- Check that all BoolExpr operands in boolop/ifgoto instructions have simple
    operands (variables and literals only, no `.bexpr`).
    Ensures the verified code generator can handle all boolean conditions. -/
def checkBoolExprSimpleOps (p : Prog) : Bool :=
  p.code.all fun instr =>
    match instr with
    | .boolop _ be | .ifgoto be _ => be.hasSimpleOps
    | _ => true

/-- Check that no variable in the program would map to a restricted register.
    Scratch registers: x0-x2 (__ir0-2/__br0-2), d0-d2 (__fr0-2).
    Reserved/platform registers: x16-x18 (__ir16-18/__br16-18). -/
def violatesRegConvention (v : Var) : Bool :=
  -- Use parse-based check so this agrees with varToArmReg / varToArmFReg
  -- (exact string matching would miss aliases like "__ir00" → x0)
  let irN := if startsWithList v "__ir" then (v.drop 4).toNat?
             else if startsWithList v "__br" then (v.drop 4).toNat?
             else none
  let frN := if startsWithList v "__fr" then (v.drop 4).toNat? else none
  match irN with
  | some 0 | some 1 | some 2 | some 16 | some 17 | some 18 => true
  | _ => match frN with
    | some 0 | some 1 | some 2 => true
    | _ => false

def checkNoRegConventionViolations (p : Prog) : Bool :=
  p.code.all fun instr =>
    instr.vars.all fun v => !violatesRegConvention v

/-- Check that no two distinct variable names would map to the same ARM register.
    The collision case is `__irN` and `__brN` for the same N — both map to register xN
    via `varToArmReg`, making the layout non-injective. -/
def checkNoRegisterCollisions (p : Prog) : Bool :=
  let vars := (p.code.toList.flatMap TAC.vars).eraseDups
  vars.all fun v =>
    if v.startsWith "__ir" then
      let n := v.drop 4
      !(vars.any fun w => w == ("__br" ++ n))
    else true

/-- Check all certificate conditions. Returns `true` iff the certificate is valid. -/
def checkCertificateExec (cert : ECertificate) : Bool :=
  -- Build the per-PC FastVarMap caches once and share across the three
  -- check functions that would otherwise rebuild them. The
  -- `*FromMaps`/`*FromMap` variants are equivalent to the originals at this
  -- call shape (see `checkInvariantsPreservedFromMaps_eq`,
  -- `checkAllTransitionsFromMaps_eq`).
  let invMaps_orig := buildInvMaps cert.inv_orig
  let invMaps_trans := buildInvMaps cert.inv_trans
  checkWellTypedProg cert.tyCtx cert.orig &&
  checkWellTypedProg cert.tyCtx cert.trans &&
  (cert.orig.observable == cert.trans.observable) &&
  checkStartCorrespondenceExec cert &&
  checkInvariantsAtStartExec cert &&
  checkRelAtStartExec cert &&
  checkInvariantsPreservedFromMaps cert invMaps_orig invMaps_trans &&
  checkNoArrReadInInvs cert.inv_orig &&
  checkNoArrReadInInvs cert.inv_trans &&
  checkNoArrReadInRels cert.instrCerts &&
  checkAllTransitionsFromMaps cert invMaps_orig &&
  checkHaltCorrespondenceExec cert &&
  checkHaltObservableExec cert &&
  checkNonterminationExec cert &&
  checkDivPreservationFromMaps cert invMaps_orig &&
  checkBoundsPreservationFromMaps cert invMaps_orig &&
  checkArraySizesExec cert &&
  checkOrigPathBoundsOk cert &&
  checkSuccessorsInBounds cert &&
  checkBoolExprNoArrRead cert.orig &&
  checkBoolExprNoArrRead cert.trans &&
  checkBoolExprSimpleOps cert.orig &&
  checkBoolExprSimpleOps cert.trans &&
  checkNoRegConventionViolations cert.orig &&
  checkNoRegConventionViolations cert.trans &&
  checkNoRegisterCollisions cert.orig &&
  checkNoRegisterCollisions cert.trans &&
  checkBoolVarsCoveredExec cert &&
  checkCodegenPrereqs cert.tyCtx cert.orig &&
  checkCodegenPrereqs cert.tyCtx cert.trans

/-- Verbose check: returns the result of each individual condition. -/
def checkCertificateVerboseExec (cert : ECertificate) : List (String × Bool) :=
  [ ("well_typed_orig",       checkWellTypedProg cert.tyCtx cert.orig),
    ("well_typed_trans",      checkWellTypedProg cert.tyCtx cert.trans),
    ("same_observable",       cert.orig.observable == cert.trans.observable),
    ("start_correspondence",  checkStartCorrespondenceExec cert),
    ("invariants_at_start",   checkInvariantsAtStartExec cert),
    ("rel_at_start",          checkRelAtStartExec cert),
    ("invariants_preserved",  checkInvariantsPreservedExec cert),
    ("no_arrread_inv_orig",   checkNoArrReadInInvs cert.inv_orig),
    ("no_arrread_inv_trans",  checkNoArrReadInInvs cert.inv_trans),
    ("no_arrread_rels",       checkNoArrReadInRels cert.instrCerts),
    ("all_transitions",       checkAllTransitionsExec cert),
    ("halt_correspondence",   checkHaltCorrespondenceExec cert),
    ("halt_observable",       checkHaltObservableExec cert),
    ("nontermination",        checkNonterminationExec cert),
    ("div_preservation",      checkDivPreservationExec cert),
    ("bounds_preservation",   checkBoundsPreservationExec cert),
    ("array_sizes_equal",     checkArraySizesExec cert),
    ("orig_path_bounds_ok",   checkOrigPathBoundsOk cert),
    ("successors_in_bounds",  checkSuccessorsInBounds cert),
    ("bool_expr_no_arr_read_orig", checkBoolExprNoArrRead cert.orig),
    ("bool_expr_no_arr_read_trans", checkBoolExprNoArrRead cert.trans),
    ("bool_expr_simple_ops_orig", checkBoolExprSimpleOps cert.orig),
    ("bool_expr_simple_ops_trans", checkBoolExprSimpleOps cert.trans),
    ("reg_convention_orig", checkNoRegConventionViolations cert.orig),
    ("reg_convention_trans", checkNoRegConventionViolations cert.trans),
    ("reg_collision_orig", checkNoRegisterCollisions cert.orig),
    ("reg_collision_trans", checkNoRegisterCollisions cert.trans),
    ("bool_vars_covered",     checkBoolVarsCoveredExec cert),
    ("codegen_prereqs_orig",  checkCodegenPrereqs cert.tyCtx cert.orig),
    ("codegen_prereqs_trans", checkCodegenPrereqs cert.tyCtx cert.trans) ]

