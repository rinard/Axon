-- Copyright (c) 2026 Martin Rinard
import CredibleCompilation.WhileLang
import CredibleCompilation.Parser

/- Round-trip the AST→text printer against the 24 Livermore benchmarks: parse each `.w`, print the
   AST (`toString`), re-parse the printed form, re-print, and require the print∘parse fixpoint
   (`print = print∘parse∘print`). A PRINT-NOPARSE or ROUNDTRIP-DIFF is a printer bug. -/

def main : IO Unit := do
  let dir : System.FilePath := "benchmarks/livermore"
  let entries ← (try dir.readDir catch _ => pure #[])
  let paths := (entries.toList.filterMap (fun e =>
    if e.fileName.endsWith ".w" then some (e.fileName, e.path) else none)).toArray.qsort
      (fun a b => a.1 < b.1) |>.toList
  let mut total := 0; let mut fails := 0
  for (name, p) in paths do
    total := total + 1
    let text ← IO.FS.readFile p
    match parseProgram text with
    | .error e => IO.println s!"SEED-PARSE-FAIL {name}: {e}"; fails := fails + 1
    | .ok ast1 =>
      let printed1 := s!"{ast1}"
      match parseProgram printed1 with
      | .error e =>
        fails := fails + 1
        IO.println s!"PRINT-NOPARSE {name}: {e}"
      | .ok ast2 =>
        let printed2 := s!"{ast2}"
        if printed1 != printed2 then
          fails := fails + 1
          IO.println s!"ROUNDTRIP-DIFF {name}"
  IO.println s!"=== T2bench: {total} benchmarks, {fails} printer failures ==="
