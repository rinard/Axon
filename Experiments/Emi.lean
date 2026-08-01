-- Copyright (c) 2026 Martin Rinard
import CredibleCompilation.CodeGen

/-! # EMI (Equivalence Modulo Inputs) mutator — Orion / Athena

    Le, Afshari, Su, "Compiler Validation via Equivalence Modulo Inputs", PLDI 2014
    (Orion = prune unexecuted code); Le, Sun, Su, OOPSLA 2015 (Athena = insert into
    unexecuted regions).

    While programs are deterministic (no inputs), so the single execution profile
    IS the "modulo inputs" profile. We:
      1. parse a `.w` program,
      2. run a coverage interpreter that records which `if` arms and `while`
         bodies actually execute,
      3. mutate the UNEXECUTED (dead) regions — Orion replaces a dead arm with
         `skip`; Athena injects junk (writes to live vars + a sentinel print)
         into a dead arm,
      4. pretty-print each mutant back to `.w` source.

    Every mutant is equivalent to the seed (dead code never runs), so the seed
    and every mutant must produce identical output. A divergence — in particular
    the sentinel string `[EMILEAK]` ever appearing — is a compiler bug. -/

namespace Emi

-- ============================================================
-- § 1. Pretty-printer: AST → .w source (fully parenthesized)
-- ============================================================

/-- Re-escape a string literal's contents for `.w` source. -/
def escStr (s : String) : String :=
  s.foldl (fun acc c =>
    acc ++ (match c with
      | '\n' => "\\n" | '\t' => "\\t" | '"' => "\\\"" | '\\' => "\\\\"
      | _ => String.singleton c)) ""

def ppBinOp : BinOp → String
  | .add => "+" | .sub => "-" | .mul => "*" | .div => "/" | .mod => "%"
  | .band => "&" | .bor => "|" | .bxor => "^" | .shl => "<<" | .shr => ">>"

def ppCmpOp : CmpOp → String
  | .eq => "==" | .ne => "!=" | .lt => "<" | .le => "<="

def ppFCmpOp : FloatCmpOp → String
  | .feq => "==" | .fne => "!=" | .flt => "<" | .fle => "<="

def ppFUnary : FloatUnaryOp → String
  | .exp => "exp" | .sqrt => "sqrt" | .sin => "sin" | .cos => "cos" | .tan => "tan"
  | .log => "log" | .log2 => "log2" | .log10 => "log10"
  | .abs => "abs" | .neg => "neg" | .round => "round"

partial def ppSExpr : SExpr → String
  | .lit n => if n < 0 then s!"(0 - {-n})" else toString n
  | .var x => x
  | .bin op a b => s!"({ppSExpr a} {ppBinOp op} {ppSExpr b})"
  | .arrRead arr i => s!"{arr}[{ppSExpr i}]"
  | .flit f => toString f
  | .fbin op a b =>
    match op with
    | .fadd => s!"({ppSExpr a} + {ppSExpr b})"
    | .fsub => s!"({ppSExpr a} - {ppSExpr b})"
    | .fmul => s!"({ppSExpr a} * {ppSExpr b})"
    | .fdiv => s!"({ppSExpr a} / {ppSExpr b})"
    | .fpow => s!"pow({ppSExpr a}, {ppSExpr b})"
    | .fmin => s!"fmin({ppSExpr a}, {ppSExpr b})"
    | .fmax => s!"fmax({ppSExpr a}, {ppSExpr b})"
  | .intToFloat e => s!"intToFloat({ppSExpr e})"
  | .floatToInt e => s!"floatToInt({ppSExpr e})"
  | .floatUnary op e => s!"{ppFUnary op}({ppSExpr e})"
  | .farrRead arr i => s!"{arr}[{ppSExpr i}]"

partial def ppSBool : SBool → String
  | .lit true => "(0 == 0)"
  | .lit false => "(0 != 0)"
  | .bvar x => x
  | .cmp op a b => s!"({ppSExpr a} {ppCmpOp op} {ppSExpr b})"
  | .not b => s!"(!{ppSBool b})"
  | .and a b => s!"({ppSBool a} && {ppSBool b})"
  | .or a b => s!"({ppSBool a} || {ppSBool b})"
  | .barrRead arr i => s!"{arr}[{ppSExpr i}]"
  | .fcmp op a b => s!"({ppSExpr a} {ppFCmpOp op} {ppSExpr b})"

/-- Pretty-print a statement. Returns a list of lines (already indented by `ind`). -/
partial def ppStmt (ind : String) : Stmt → List String
  | .skip => [ind ++ "skip"]
  | .assign x e => [s!"{ind}{x} := {ppSExpr e}"]
  | .fassign x e => [s!"{ind}{x} := {ppSExpr e}"]
  | .bassign x b => [s!"{ind}{x} := {ppSBool b}"]
  | .arrWrite a i v => [s!"{ind}{a}[{ppSExpr i}] := {ppSExpr v}"]
  | .farrWrite a i v => [s!"{ind}{a}[{ppSExpr i}] := {ppSExpr v}"]
  | .barrWrite a i v => [s!"{ind}{a}[{ppSExpr i}] := {ppSBool v}"]
  | .seq s1 s2 =>
    -- join the two with a trailing `;` on the last line of s1
    let l1 := ppStmt ind s1
    let l2 := ppStmt ind s2
    match l1.reverse with
    | last :: rest => (rest.reverse ++ [last ++ ";"]) ++ l2
    | [] => l2
  | .ite c t e =>
    [ind ++ "if (" ++ ppSBool c ++ ") {"] ++ ppStmt (ind ++ "  ") t ++
    [ind ++ "} else {"] ++ ppStmt (ind ++ "  ") e ++ [ind ++ "}"]
  | .loop c body =>
    [ind ++ "while (" ++ ppSBool c ++ ") {"] ++ ppStmt (ind ++ "  ") body ++ [ind ++ "}"]
  | .print fmt args =>
    [ind ++ "print \"" ++ escStr fmt ++ "\"" ++ (if args.isEmpty then "" else ", " ++ String.intercalate ", " (args.map ppSExpr))]
  | .printInt e => [s!"{ind}printInt({ppSExpr e})"]
  | .printFloat e => [s!"{ind}printFloat({ppSExpr e})"]
  | .printBool b => [s!"{ind}printBool({ppSBool b})"]
  | .printString s => [ind ++ "printString(\"" ++ escStr s ++ "\")"]
  | .label l => [s!"{ind}{l}:"]
  | .goto l => [s!"{ind}goto {l}"]
  | .ifgoto c l => [s!"{ind}if ({ppSBool c}) goto {l}"]

def ppTy : VarTy → String
  | .int => "int" | .bool => "bool" | .float => "float"

def ppProgram (p : Program) : String :=
  let decls := String.intercalate ", " (p.decls.map fun (v, t) => s!"{v} : {ppTy t}")
  let arrs := p.arrayDecls.map fun (n, sz, t) => s!"{n}[{sz}] : {ppTy t}"
  let header := s!"var {decls};\n" ++
    (if arrs.isEmpty then "" else "array " ++ String.intercalate ", " arrs ++ ";\n")
  header ++ String.intercalate "\n" (ppStmt "" p.body) ++ "\n"

-- ============================================================
-- § 2. Coverage interpreter
-- ============================================================

/-- Count every Stmt node (pre-order), so child node-ids are stable across
    loop iterations. -/
partial def countNodes : Stmt → Nat
  | .seq a b => 1 + countNodes a + countNodes b
  | .ite _ a b => 1 + countNodes a + countNodes b
  | .loop _ b => 1 + countNodes b
  | _ => 1

abbrev Cov := Std.HashSet String

/-- Coverage-tracking interpreter. `id` is the pre-order id of this node.
    Records `ite{id}then` / `ite{id}else` / `loop{id}body` when those regions run. -/
partial def coverInterp (fuel : Nat) (σ : Store) (am : ArrayMem)
    (decls : List (ArrayName × Nat × VarTy)) (id : Nat) (cov : Cov) :
    Stmt → Option (Store × ArrayMem × Cov)
  | .skip => some (σ, am, cov)
  | .assign x e => if e.isSafe σ am decls then some (σ[x ↦ .int (e.eval σ am)], am, cov) else none
  | .fassign x e => if e.isSafe σ am decls then some (σ[x ↦ .float (e.eval σ am)], am, cov) else none
  | .bassign x b => if b.isSafe σ am decls then some (σ[x ↦ .bool (b.eval σ am)], am, cov) else none
  | .arrWrite arr idx val =>
    if idx.isSafe σ am decls && val.isSafe σ am decls && decide ((idx.eval σ am) < arraySizeBv decls arr)
    then some (σ, am.write arr (idx.eval σ am) (val.eval σ am), cov) else none
  | .farrWrite arr idx val =>
    if idx.isSafe σ am decls && val.isSafe σ am decls && decide ((idx.eval σ am) < arraySizeBv decls arr)
    then some (σ, am.write arr (idx.eval σ am) (val.eval σ am), cov) else none
  | .barrWrite arr idx bval =>
    if (idx : SExpr).isSafe σ am decls && bval.isSafe σ am decls && decide ((idx.eval σ am) < arraySizeBv decls arr)
    then let b := bval.eval σ am
         some (σ, am.write arr (idx.eval σ am) (if b then 1 else 0), cov) else none
  | .seq s1 s2 => do
    let (σ', am', cov') ← coverInterp fuel σ am decls (id+1) cov s1
    coverInterp fuel σ' am' decls (id+1+countNodes s1) cov' s2
  | .ite b s1 s2 =>
    if b.isSafe σ am decls then
      if b.eval σ am then coverInterp fuel σ am decls (id+1) (cov.insert s!"ite{id}then") s1
      else coverInterp fuel σ am decls (id+1+countNodes s1) (cov.insert s!"ite{id}else") s2
    else none
  | .loop b body =>
    match fuel with
    | 0 => none
    | fuel'+1 =>
      if b.isSafe σ am decls then
        if b.eval σ am then do
          let (σ', am', cov') ← coverInterp fuel' σ am decls (id+1) (cov.insert s!"loop{id}body") body
          coverInterp fuel' σ' am' decls id cov' (.loop b body)
        else some (σ, am, cov)
      else none
  | .label _ => some (σ, am, cov)
  | .goto _ => some (σ, am, cov)
  | .ifgoto b _ => if b.isSafe σ am decls then some (σ, am, cov) else none
  | .print _ args => if args.all (·.isSafe σ am decls) then some (σ, am, cov) else none
  | .printInt e => if e.isSafe σ am decls then some (σ, am, cov) else none
  | .printBool b => if b.isSafe σ am decls then some (σ, am, cov) else none
  | .printFloat e => if e.isSafe σ am decls then some (σ, am, cov) else none
  | .printString _ => some (σ, am, cov)

-- ============================================================
-- § 3. Mutators (Orion = delete dead arm, Athena = inject junk)
-- ============================================================

/-- Junk to inject into a dead region: a sentinel print plus writes to live int
    vars. Never executes if the region is truly dead; if it ever runs, the
    sentinel `[EMILEAK]` and/or corrupted values surface in the output. -/
def junk (intVars : List Var) : Stmt :=
  let writes := (intVars.take 3).map fun v => Stmt.assign v (.bin .add (.var v) (.lit 987654321))
  let base : Stmt := .printString "[EMILEAK]"
  writes.foldl (fun acc w => .seq acc w) base

/-- Walk the AST with the same pre-order numbering as `coverInterp` and rewrite
    each DEAD arm (an `ite` arm or `loop` body whose coverage key is absent)
    using `rewrite deadStmt`. -/
partial def mutate (cov : Cov) (intVars : List Var) (rewrite : Stmt → Stmt)
    (id : Nat) : Stmt → Stmt
  | .seq s1 s2 => .seq (mutate cov intVars rewrite (id+1) s1)
                       (mutate cov intVars rewrite (id+1+countNodes s1) s2)
  | .ite b s1 s2 =>
    let s1' := if cov.contains s!"ite{id}then"
               then mutate cov intVars rewrite (id+1) s1 else rewrite s1
    let s2' := if cov.contains s!"ite{id}else"
               then mutate cov intVars rewrite (id+1+countNodes s1) s2 else rewrite s2
    .ite b s1' s2'
  | .loop b body =>
    let body' := if cov.contains s!"loop{id}body"
                 then mutate cov intVars rewrite (id+1) body else rewrite body
    .loop b body'
  | s => s

/-- Count dead arms (number of injection sites). -/
partial def countDead (cov : Cov) (id : Nat) : Stmt → Nat
  | .seq s1 s2 => countDead cov (id+1) s1 + countDead cov (id+1+countNodes s1) s2
  | .ite _ s1 s2 =>
    (if cov.contains s!"ite{id}then" then countDead cov (id+1) s1 else 1) +
    (if cov.contains s!"ite{id}else" then countDead cov (id+1+countNodes s1) s2 else 1)
  | .loop _ body =>
    if cov.contains s!"loop{id}body" then countDead cov (id+1) body else 1
  | _ => 0

-- ============================================================
-- § 3b. Metamorphic transforms (semantics-preserving rewrites)
-- ============================================================
-- Each transform preserves the program's meaning, so the mutant MUST produce
-- the same output as the seed. They create operand orders / control-flow shapes
-- the While front end never emits, stressing the optimizer + certificate checker
-- (this is how the LICM/CSE/Peephole bugs were originally surfaced).

mutual
/-- `comm`: swap operands of `+`/`*` (wrapping add/mul are commutative).
    `strength`: rewrite `x*2` ⇒ `x+x`. `negate` is identity on expressions. -/
partial def metaSExpr (mode : String) : SExpr → SExpr
  | .bin op a b =>
    let a' := metaSExpr mode a; let b' := metaSExpr mode b
    match mode, op with
    | "comm", .add => .bin .add b' a'
    | "comm", .mul => .bin .mul b' a'
    | "strength", .mul =>
      match b' with
      | .lit 2 => .bin .add a' a'
      | _ => match a' with | .lit 2 => .bin .add b' b' | _ => .bin op a' b'
    | _, _ => .bin op a' b'
  | .arrRead arr i => .arrRead arr (metaSExpr mode i)
  | .fbin op a b => .fbin op (metaSExpr mode a) (metaSExpr mode b)
  | .intToFloat e => .intToFloat (metaSExpr mode e)
  | .floatToInt e => .floatToInt (metaSExpr mode e)
  | .floatUnary op e => .floatUnary op (metaSExpr mode e)
  | .farrRead arr i => .farrRead arr (metaSExpr mode i)
  | e => e

partial def metaSBool (mode : String) : SBool → SBool
  | .cmp op a b => .cmp op (metaSExpr mode a) (metaSExpr mode b)
  | .not b => .not (metaSBool mode b)
  | .and a b => .and (metaSBool mode a) (metaSBool mode b)
  | .or a b => .or (metaSBool mode a) (metaSBool mode b)
  | .barrRead arr i => .barrRead arr (metaSExpr mode i)
  | .fcmp op a b => .fcmp op (metaSExpr mode a) (metaSExpr mode b)
  | b => b
end

/-- `negate`: rewrite `if (c) {A} else {B}` ⇒ `if (!c) {B} else {A}`. -/
partial def metaStmt (mode : String) : Stmt → Stmt
  | .assign x e => .assign x (metaSExpr mode e)
  | .fassign x e => .fassign x (metaSExpr mode e)
  | .bassign x b => .bassign x (metaSBool mode b)
  | .arrWrite a i v => .arrWrite a (metaSExpr mode i) (metaSExpr mode v)
  | .farrWrite a i v => .farrWrite a (metaSExpr mode i) (metaSExpr mode v)
  | .barrWrite a i v => .barrWrite a (metaSExpr mode i) (metaSBool mode v)
  | .seq s1 s2 => .seq (metaStmt mode s1) (metaStmt mode s2)
  | .ite c t e =>
    let c' := metaSBool mode c
    let t' := metaStmt mode t; let e' := metaStmt mode e
    if mode == "negate" then .ite (.not c') e' t' else .ite c' t' e'
  | .loop c body => .loop (metaSBool mode c) (metaStmt mode body)
  | .printInt e => .printInt (metaSExpr mode e)
  | .printFloat e => .printFloat (metaSExpr mode e)
  | .printBool b => .printBool (metaSBool mode b)
  | .print fmt args => .print fmt (args.map (metaSExpr mode))
  | s => s

-- ============================================================
-- § 3c. Hermes-style insertion into LIVE regions
-- ============================================================
-- Hermes (Le, Sun, Su) inserts code into EXECUTED regions, made inert so output
-- is unchanged. Here: after each statement we splice a dead-variable assignment
-- `hg{k} := <expr over live vars>`. It runs on live paths (stressing the
-- optimizer's liveness/DCE/CSE on real computation) but `hg*` are never printed,
-- so the output must be identical to the seed's.

/-- A dead assignment `hg{k%4} := <expr>` built from up to two live int vars. -/
def deadAssign (lives : List Var) (k : Nat) : Stmt :=
  let hv := s!"hg{k % 4}"
  let e : SExpr := match lives with
    | a :: b :: _ =>
      match k % 3 with
      | 0 => .bin .add (.var a) (.var b)
      | 1 => .bin .mul (.var a) (.var b)
      | _ => .bin .sub (.var a) (.var b)
    | a :: _ => .bin .add (.var a) (.lit (Int.ofNat k))
    | [] => .lit (Int.ofNat k)
  .assign hv e

/-- Splice a dead assignment after every statement; recurse into branches/loops.
    Threads a counter for variety. -/
partial def hermes (lives : List Var) : Nat → Stmt → Stmt × Nat
  | k, .seq a b =>
    let (a', k1) := hermes lives k a
    let (b', k2) := hermes lives k1 b
    (.seq a' b', k2)
  | k, .ite c t e =>
    let (t', k1) := hermes lives k t
    let (e', k2) := hermes lives k1 e
    (.seq (.ite c t' e') (deadAssign lives k2), k2 + 1)
  | k, .loop c body =>
    let (b', k1) := hermes lives k body
    (.seq (.loop c b') (deadAssign lives k1), k1 + 1)
  | k, s => (.seq s (deadAssign lives k), k + 1)

-- ============================================================
-- § 4. Driver
-- ============================================================

partial def hasFloat : Stmt → Bool
  | .fassign .. | .farrWrite .. | .printFloat .. => true
  | .seq a b | .ite _ a b => hasFloat a || hasFloat b
  | .loop _ b => hasFloat b
  | _ => false

def main (args : List String) : IO UInt32 := do
  match args with
  | [mode, inputFile, outDir] =>
    let src ← IO.FS.readFile ⟨inputFile⟩
    match parseProgram src with
    | .error e => IO.eprintln s!"parse error: {e}"; return 1
    | .ok prog =>
      if !prog.wellFormed then IO.eprintln "not well-formed"; return 1
      if hasFloat prog.body || (prog.decls.any fun (_, t) => t == .float) then
        IO.println "skip: float program (parser float round-trip unreliable)"; return 0
      let base := (inputFile.splitOn "/").getLast!.replace ".w" ""
      -- Metamorphic modes: semantics-preserving whole-program rewrites (no
      -- coverage needed). Output must equal the seed's.
      if mode == "comm" || mode == "strength" || mode == "negate" then
        let m := { prog with body := metaStmt mode prog.body }
        IO.FS.writeFile ⟨s!"{outDir}/{base}_{mode}.w"⟩ (ppProgram m)
        IO.println s!"wrote {outDir}/{base}_{mode}.w"
        return 0
      if mode == "hermes" then
        let lives := prog.decls.filterMap fun (v, t) => if t == .int then some v else none
        if lives.isEmpty then IO.println "skip: no int vars"; return 0
        -- add 4 fresh dead vars hg0..hg3
        let newDecls := prog.decls ++ (List.range 4).map fun i => (s!"hg{i}", VarTy.int)
        let (body', _) := hermes lives 0 prog.body
        let m := { prog with decls := newDecls, body := body' }
        IO.FS.writeFile ⟨s!"{outDir}/{base}_hermes.w"⟩ (ppProgram m)
        IO.println s!"wrote {outDir}/{base}_hermes.w"
        return 0
      let intVars := (prog.decls.filterMap fun (v, t) => if t == .int then some v else none)
      match coverInterp 1000000 prog.initStore ArrayMem.init prog.arrayDecls 0 (∅) prog.body with
      | none => IO.println "skip: interp failed (out of fuel / unsafe)"; return 0
      | some (_, _, cov) =>
        let nDead := countDead cov 0 prog.body
        IO.println s!"dead arms: {nDead}"
        if nDead == 0 then return 0
        let base := (inputFile.splitOn "/").getLast!.replace ".w" ""
        let rewrite : Stmt → Stmt := match mode with
          | "orion"  => fun _ => .skip
          | "athena" => fun _ => junk intVars
          | _ => fun s => s
        -- Mutant A: rewrite ALL dead arms at once.
        let mAll := { prog with body := mutate cov intVars rewrite 0 prog.body }
        IO.FS.writeFile ⟨s!"{outDir}/{base}_{mode}_all.w"⟩ (ppProgram mAll)
        IO.println s!"wrote {outDir}/{base}_{mode}_all.w"
        return 0
  | _ => IO.eprintln "usage: emi <orion|athena> <file.w> <outdir>"; return 1

end Emi

def main (args : List String) : IO UInt32 := Emi.main args
