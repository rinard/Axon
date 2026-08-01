-- Copyright (c) 2026 Martin Rinard
import CredibleCompilation.ExecChecker

/-!
# Bounds Check Elision — Interval Analysis

Forward dataflow interval analysis tracking `[lo, hi)` per integer variable
at each PC. Worklist algorithm with widening at back edges. Produces
`Array (Option IMap)` that CodeGen consumes to decide whether `arrLoad`/`arrStore`
bounds checks can be safely omitted.

CodeGen independently verifies the invariant claims — it never trusts them
blindly. If the analysis is buggy, CodeGen simply emits bounds checks.
-/

namespace BoundsOpt

-- ============================================================
-- § 1. Interval domain
-- ============================================================

private def iBot : Int := -1000000000000
private def iTop : Int := 1000000000000

structure IRange where
  lo : Int
  hi : Int  -- exclusive upper bound: value < hi

def irTop : IRange := ⟨iBot, iTop⟩

def IRange.join (a b : IRange) : IRange :=
  ⟨min a.lo b.lo, max a.hi b.hi⟩

def IRange.widen (old new_ : IRange) : IRange :=
  ⟨if new_.lo < old.lo then iBot else old.lo,
   if new_.hi > old.hi then iTop else old.hi⟩

def IRange.beq (a b : IRange) : Bool :=
  a.lo == b.lo && a.hi == b.hi

/-- Does this range prove 0 ≤ x < size? -/
def IRange.inBounds (r : IRange) (size : Nat) : Bool :=
  r.lo >= 0 && r.hi <= size

-- ============================================================
-- § 2. Interval map
-- ============================================================

abbrev IMap := List (Var × IRange)

def imLookup (m : IMap) (v : Var) : IRange :=
  match m.find? (fun p => p.1 == v) with
  | some (_, r) => r
  | none => irTop

def imSet (m : IMap) (v : Var) (r : IRange) : IMap :=
  (v, r) :: m.filter (fun p => !(p.1 == v))

def imJoin (a b : IMap) : IMap :=
  let vars := (a.map Prod.fst ++ b.map Prod.fst).eraseDups
  vars.map fun v => (v, (imLookup a v).join (imLookup b v))

def imWiden (old merged : IMap) : IMap :=
  let vars := (old.map Prod.fst ++ merged.map Prod.fst).eraseDups
  vars.map fun v =>
    let oldR := imLookup old v
    let newR := imLookup merged v
    if oldR.lo == iBot && oldR.hi == iTop then (v, newR)
    else (v, oldR.widen newR)

def imBeq (a b : IMap) : Bool :=
  let norm (m : IMap) := m.filter (fun (_, r) => !(r.lo == iBot && r.hi == iTop))
  let an := norm a; let bn := norm b
  an.length == bn.length && an.all fun (v, r) => (imLookup b v).beq r

-- ============================================================
-- § 3. Transfer function
-- ============================================================

/-- Transfer function: update intervals for scalar assignments. -/
def transferInterval (m : IMap) (instr : TAC) : IMap :=
  match instr with
  | .const x (.int n)  => imSet m x ⟨n.toInt, n.toInt + 1⟩
  | .const x (.bool b) => imSet m x ⟨if b then 1 else 0, if b then 2 else 1⟩
  | .copy x y          => imSet m x (imLookup m y)
  | .binop x .add y z  =>
    let iy := imLookup m y; let iz := imLookup m z
    imSet m x ⟨iy.lo + iz.lo, iy.hi + iz.hi - 1⟩
  | .binop x .sub y z  =>
    let iy := imLookup m y; let iz := imLookup m z
    imSet m x ⟨iy.lo - iz.hi + 1, iy.hi - iz.lo⟩
  | .binop x .mul y z  =>
    let iy := imLookup m y; let iz := imLookup m z
    -- Multiply closed ranges [lo, hi-1] × [lo, hi-1], take min/max of all 4 corners
    let a := iy.lo; let b := iy.hi - 1; let c := iz.lo; let d := iz.hi - 1
    let p1 := a * c; let p2 := a * d; let p3 := b * c; let p4 := b * d
    let lo := min (min p1 p2) (min p3 p4)
    let hi := max (max p1 p2) (max p3 p4) + 1
    imSet m x ⟨lo, hi⟩
  | .binop x _ _ _     => imSet m x irTop
  | .boolop x _        => imSet m x ⟨0, 2⟩
  | .arrLoad x _ _ _   => imSet m x irTop
  | .floatToInt x _    => imSet m x irTop
  | _                  => m

-- ============================================================
-- § 4. Condition refinement
-- ============================================================

/-- Refine intervals when a boolean condition is known true or false. -/
partial def refineCondition (m : IMap) (be : BoolExpr) (isTrue : Bool) : IMap :=
  match be with
  | .not inner => refineCondition m inner (!isTrue)
  | .cmp .lt (.var x) (.lit n) =>
    let iv := imLookup m x
    if isTrue then imSet m x ⟨iv.lo, min iv.hi n.toInt⟩
    else imSet m x ⟨max iv.lo n.toInt, iv.hi⟩
  | .cmp .lt (.var x) (.var bound) =>
    let biv := imLookup m bound; let iv := imLookup m x
    if biv.lo + 1 == biv.hi then
      if isTrue then imSet m x ⟨iv.lo, min iv.hi biv.lo⟩
      else imSet m x ⟨max iv.lo biv.lo, iv.hi⟩
    else m
  | .cmp .le (.var x) (.lit n) =>
    let iv := imLookup m x
    if isTrue then imSet m x ⟨iv.lo, min iv.hi (n.toInt + 1)⟩
    else imSet m x ⟨max iv.lo (n.toInt + 1), iv.hi⟩
  | .cmp .le (.var x) (.var bound) =>
    let biv := imLookup m bound; let iv := imLookup m x
    if biv.lo + 1 == biv.hi then
      if isTrue then imSet m x ⟨iv.lo, min iv.hi (biv.lo + 1)⟩
      else imSet m x ⟨max iv.lo (biv.lo + 1), iv.hi⟩
    else m
  | _ => m

/-- Compute the interval map at a successor PC. -/
def successorIMap (m : IMap) (instr : TAC) (succPC : Nat) : IMap :=
  match instr with
  | .ifgoto be l =>
    if succPC == l then refineCondition m be true
    else refineCondition m be false
  | _ => transferInterval m instr

-- ============================================================
-- § 5. Worklist solver
-- ============================================================

/-- Forward interval analysis with worklist and widening at back edges. -/
partial def analyzeIntervalsLoop (prog : Prog)
    (ivals : Array (Option IMap)) (worklist : List Nat) : Array (Option IMap) :=
  match worklist with
  | [] => ivals
  | pc :: rest =>
    match ivals[pc]?, prog[pc]? with
    | some (some m), some instr =>
      let succs := instr.successors pc
      let (ivals', newWork) := succs.foldl (fun (ivs, work) pc' =>
        if pc' >= prog.size then (ivs, work)
        else
          let outM := successorIMap m instr pc'
          match ivs[pc']? with
          | some (some old) =>
            let merged := imJoin old outM
            let final := if pc' <= pc then imWiden old merged else merged
            if imBeq final old then (ivs, work)
            else (ivs.set! pc' (some final), work ++ [pc'])
          | _ => (ivs.set! pc' (some outM), work ++ [pc'])
      ) (ivals, rest)
      analyzeIntervalsLoop prog ivals' newWork
    | _, _ => analyzeIntervalsLoop prog ivals rest

-- ============================================================
-- § 6. Entry point
-- ============================================================

/-- Run forward interval analysis on a program.
    Returns `Option IMap` per PC (`none` = unreachable). -/
def analyzeIntervals (prog : Prog) : Array (Option IMap) :=
  if prog.size == 0 then #[]
  else
    let init := (Array.replicate prog.size (none : Option IMap)).set! 0 (some [])
    analyzeIntervalsLoop prog init (0 :: [])

end BoundsOpt
