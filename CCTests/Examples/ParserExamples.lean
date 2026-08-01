-- Copyright (c) 2026 Martin Rinard
import CredibleCompilation.Parser
import CredibleCompilation.CSEOpt

/-!
# Parser Examples and Tests

Tests the parser on a variety of programs covering all language constructs,
then runs parsed programs through the full pipeline:
parse → compile → optimize → certificate check.
-/

open SExpr SBool Stmt

-- ============================================================
-- § 1. Expression parsing
-- ============================================================

-- Arithmetic: precedence and associativity
#eval! parseProgram "var x : int; x := 1 + 2 * 3"
-- expect: x := 1 + (2 * 3) = bin .add (lit 1) (bin .mul (lit 2) (lit 3))

#eval! parseProgram "var x : int; x := (1 + 2) * 3"
-- expect: x := (1 + 2) * 3

#eval! parseProgram "var x : int, y : int; x := y / 2 - 1"
-- expect: x := (y / 2) - 1

-- Nested parentheses
#eval! parseProgram "var x : int, a : int, b : int, c : int; x := (a + b) * (c - 1)"

-- ============================================================
-- § 2. Boolean expression parsing
-- ============================================================

-- Simple comparisons
#eval! parseProgram "var x : int, flag : bool; flag := x < 10"
#eval! parseProgram "var x : int, flag : bool; flag := x == 0"
#eval! parseProgram "var a : int, b : int, flag : bool; flag := a != b"

-- Logical operators
#eval! parseProgram "var a : int, b : int, flag : bool; flag := a < 10 && b < 20"
#eval! parseProgram "var a : int, b : int, flag : bool; flag := a == 0 || b == 0"

-- Negation
#eval! parseProgram "var x : int, flag : bool; flag := !(x < 5)"

-- Boolean variable
#eval! parseProgram "var done : bool, result : bool; result := !done"

-- Complex boolean: (a < b) && !(c == 0) || (d <= 10)
#eval! parseProgram "
  var a : int, b : int, c : int, d : int, r : bool;
  r := (a < b) && !(c == 0) || (d <= 10)
"

-- ============================================================
-- § 3. Control flow
-- ============================================================

-- If-then-else
#eval! parseProgram "
  var x : int, y : int;
  if (x < y) { x := y } else { skip }
"

-- Nested if
#eval! parseProgram "
  var a : int, b : int, c : int, m : int;
  if (a < b) {
    if (a < c) { m := a } else { m := c }
  } else {
    if (b < c) { m := b } else { m := c }
  }
"

-- While loop
#eval! parseProgram "
  var n : int, s : int;
  s := 0;
  while (n != 0) {
    s := s + n;
    n := n - 1
  }
"

-- Nested loops
#eval! parseProgram "
  var i : int, j : int, s : int, n : int;
  s := 0;
  i := 0;
  while (i < n) {
    j := 0;
    while (j < n) {
      s := s + 1;
      j := j + 1
    };
    i := i + 1
  }
"

-- ============================================================
-- § 4. Trailing semicolons and sequencing
-- ============================================================

-- Trailing semicolon before closing brace
#eval! parseProgram "
  var x : int;
  while (x < 10) {
    x := x + 1;
  }
"

-- Multiple statements
#eval! parseProgram "
  var a : int, b : int, c : int, t : int;
  t := a;
  a := b;
  b := c;
  c := t
"

-- ============================================================
-- § 5. End-to-end: parse → compile → interpret
-- ============================================================

section RunTests
-- Temporarily disable the store update notation to allow list literals
set_option hygiene false in
local notation:max "[" "]" => (List.nil : List _)
-- Use a helper to build input lists without clashing with σ[x ↦ v]

private def run (input : String) (fuel : Nat)
    (inputs : List (String × Int)) (observe : List String)
    : Except String (Option (List (String × Value))) := do
  let prog ← parseProgram input
  let σ₀ := inputs.foldl (fun σ (x, n) => Store.update σ x (.int n)) prog.initStore
  return (prog.body.interp fuel σ₀ ArrayMem.init prog.arrayDecls).map (fun (σ, _) => observe.map (fun v => (v, σ v)))

-- Sum 1..10
#eval! run "
  var n : int, s : int, i : int;
  s := 0; i := 1;
  while (i <= n) { s := s + i; i := i + 1 }
" 1000 (("n", 10) :: List.nil) ("s" :: List.nil)
-- expect: some [("s", int 55)]

-- Factorial 5
#eval! run "
  var n : int, r : int;
  r := 1;
  while (n != 0) { r := r * n; n := n - 1 }
" 1000 (("n", 5) :: List.nil) ("r" :: List.nil)
-- expect: some [("r", int 120)]

-- Max of two numbers
#eval! run "
  var a : int, b : int, m : int;
  if (a < b) { m := b } else { m := a }
" 100 (("a", 3) :: ("b", 7) :: List.nil) ("m" :: List.nil)
-- expect: some [("m", int 7)]

-- Division
#eval! run "
  var a : int, b : int, q : int;
  q := a / b
" 100 (("a", 42) :: ("b", 6) :: List.nil) ("q" :: List.nil)
-- expect: some [("q", int 7)]

end RunTests

-- ============================================================
-- § 6. End-to-end: parse → compile → optimize → check
-- ============================================================

-- Sum: constant propagation
#eval! do
  let prog ← parseProgram "
    var n : int, s : int, i : int;
    s := 0;
    i := 1;
    while (i <= n) {
      s := s + i;
      i := i + 1
    }
  "
  return checkCertificateVerboseExec (ConstPropOpt.optimize prog.tyCtx prog.compileToTAC)

-- Factorial: constant propagation
#eval! do
  let prog ← parseProgram "
    var n : int, r : int;
    r := 1;
    while (n != 0) {
      r := r * n;
      n := n - 1
    }
  "
  return checkCertificateVerboseExec (ConstPropOpt.optimize prog.tyCtx prog.compileToTAC)

-- Max: constant propagation
#eval! do
  let prog ← parseProgram "
    var a : int, b : int, m : int;
    if (a < b) { m := b } else { m := a }
  "
  return checkCertificateVerboseExec (ConstPropOpt.optimize prog.tyCtx prog.compileToTAC)

-- Nested loops: constant propagation
#eval! do
  let prog ← parseProgram "
    var i : int, j : int, s : int, n : int;
    s := 0;
    i := 0;
    while (i < n) {
      j := 0;
      while (j < n) {
        s := s + 1;
        j := j + 1
      };
      i := i + 1
    }
  "
  return checkCertificateVerboseExec (ConstPropOpt.optimize prog.tyCtx prog.compileToTAC)

-- Swap: CSE optimization
#eval! do
  let prog ← parseProgram "
    var a : int, b : int, t : int;
    t := a;
    a := b;
    b := t
  "
  return checkCertificateVerboseExec (CSEOpt.optimize prog.tyCtx prog.compileToTAC)

-- ============================================================
-- § 7. Parse error tests
-- ============================================================

-- Missing semicolon after declarations
#eval! parseProgram "var x : int x := 0"
-- expect: error

-- Unknown type
#eval! parseProgram "var x : float; x := 0"
-- expect: error

-- Missing else branch
#eval! parseProgram "var x : int; if (x < 0) { x := 0 }"
-- expect: error

-- Unmatched parenthesis
#eval! parseProgram "var x : int; x := (1 + 2"
-- expect: error

-- Empty program body
#eval! parseProgram "var x : int;"
-- expect: error
