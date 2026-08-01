-- Copyright (c) 2026 Martin Rinard
import CredibleCompilation.WhileLang
import CredibleCompilation.ExecChecker
import CredibleCompilation.ConstPropOpt

/-!
# Parser for the While Language

Parses a string into a `Program`. No verification on the translation.

## Concrete syntax

```
var x : int, y : int, flag : bool;
x := 0;
y := 1;
while (x < 10) {
  y := y * x;
  x := x + 1
};
if (flag) { skip } else { y := 0 }
```
-/

-- ============================================================
-- § 1. Tokenizer
-- ============================================================

inductive Token where
  | ident  : String → Token
  | num    : Int → Token
  | fnum   : Float → Token
  | str    : String → Token
  | kw     : String → Token
  | op     : String → Token
  | lparen | rparen | lbrace | rbrace | lbracket | rbracket | comma | semi | colon : Token
  deriving Repr

private def keywords : List String :=
  ["var", "array", "int", "bool", "float", "if", "else", "while", "skip", "true", "false",
   "intToFloat", "floatToInt", "exp", "sqrt", "sin", "cos", "tan",
   "log", "log2", "log10", "abs", "neg", "round", "pow", "fmin", "fmax", "goto",
   "print", "printInt", "printBool", "printFloat", "printString"]

private def spanDigits : List Char → List Char × List Char
  | c :: rest => if c.isDigit then let (d, r) := spanDigits rest; (c :: d, r) else ([], c :: rest)
  | [] => ([], [])

private def spanAlphaNum : List Char → List Char × List Char
  | c :: rest =>
    if c.isAlphanum || c == '_' then let (d, r) := spanAlphaNum rest; (c :: d, r)
    else ([], c :: rest)
  | [] => ([], [])

/-- Scan a string literal body (after opening `"`), handling escape sequences. -/
private def scanStr : List Char → List Char → Except String (List Char × List Char)
  | [], _ => .error "unterminated string literal"
  | '"' :: rest, acc => .ok (acc.reverse, rest)
  | '\\' :: 'n' :: rest, acc => scanStr rest ('\n' :: acc)
  | '\\' :: 't' :: rest, acc => scanStr rest ('\t' :: acc)
  | '\\' :: '\\' :: rest, acc => scanStr rest ('\\' :: acc)
  | '\\' :: '"' :: rest, acc => scanStr rest ('"' :: acc)
  | ch :: rest, acc => scanStr rest (ch :: acc)

partial def tokenize (s : String) : Except String (List Token) :=
  go s.toList ([] : List Token)
where
  go : List Char → List Token → Except String (List Token)
    | [], acc => .ok acc.reverse
    | c :: rest, acc =>
      if c == ' ' || c == '\n' || c == '\r' || c == '\t' then go rest acc
      else if c == '(' then go rest (.lparen :: acc)
      else if c == ')' then go rest (.rparen :: acc)
      else if c == '{' then go rest (.lbrace :: acc)
      else if c == '}' then go rest (.rbrace :: acc)
      else if c == '[' then go rest (.lbracket :: acc)
      else if c == ']' then go rest (.rbracket :: acc)
      else if c == ',' then go rest (.comma :: acc)
      else if c == ';' then go rest (.semi :: acc)
      else if c == '+' then go rest (.op "+" :: acc)
      else if c == '*' then go rest (.op "*" :: acc)
      else if c == '/' then go rest (.op "/" :: acc)
      else if c == '%' then go rest (.op "%" :: acc)
      else if c == '-' then go rest (.op "-" :: acc)
      else if c == ':' then
        match rest with
        | '=' :: rest' => go rest' (.op ":=" :: acc)
        | _ => go rest (.colon :: acc)
      else if c == '<' then
        match rest with
        | '<' :: rest' => go rest' (.op "<<" :: acc)
        | '=' :: rest' => go rest' (.op "<=" :: acc)
        | _ => go rest (.op "<" :: acc)
      else if c == '>' then
        match rest with
        | '>' :: rest' => go rest' (.op ">>" :: acc)
        | '=' :: rest' => go rest' (.op ">=" :: acc)
        | _ => go rest (.op ">" :: acc)
      else if c == '=' then
        match rest with
        | '=' :: rest' => go rest' (.op "==" :: acc)
        | _ => .error "unexpected '=', did you mean ':=' or '=='?"
      else if c == '!' then
        match rest with
        | '=' :: rest' => go rest' (.op "!=" :: acc)
        | _ => go rest (.op "!" :: acc)
      else if c == '&' then
        match rest with
        | '&' :: rest' => go rest' (.op "&&" :: acc)
        | _ => go rest (.op "&" :: acc)
      else if c == '|' then
        match rest with
        | '|' :: rest' => go rest' (.op "||" :: acc)
        | _ => go rest (.op "|" :: acc)
      else if c == '^' then go rest (.op "^" :: acc)
      else if c == '~' then go rest (.op "~" :: acc)
      else if c.isDigit then
        let (digits, rest') := spanDigits (c :: rest)
        -- Check if this is a float literal (digits followed by '.')
        match rest' with
        | '.' :: rest'' =>
          let (frac, rest''') := spanDigits rest''
          let intPart : Float := Float.ofNat (digits.foldl (fun a d => a * 10 + d.toNat - '0'.toNat) 0)
          let fracPart : Float :=
            if frac.isEmpty then 0.0
            else
              let fracVal := Float.ofNat (frac.foldl (fun a d => a * 10 + d.toNat - '0'.toNat) 0)
              let fracDiv := Float.ofNat (10 ^ frac.length)
              fracVal / fracDiv
          go rest''' (.fnum (intPart + fracPart) :: acc)
        | _ =>
          let n := digits.foldl (fun acc d => acc * 10 + d.toNat - '0'.toNat) 0
          go rest' (.num (Int.ofNat n) :: acc)
      else if c == '"' then
        match scanStr rest ([] : List Char) with
        | .error e => .error e
        | .ok (chars, rest') => go rest' (.str (String.ofList chars) :: acc)
      else if c.isAlpha || c == '_' then
        let (chars, rest') := spanAlphaNum (c :: rest)
        let word := String.ofList chars
        if keywords.contains word then go rest' (.kw word :: acc)
        else go rest' (.ident word :: acc)
      else .error s!"unexpected character '{c}'"

-- ============================================================
-- § 2. Parser (mutual recursive)
-- ============================================================

mutual

partial def parseAtom (toks : List Token) : Except String (SExpr × List Token) :=
  match toks with
  | Token.num n :: rest => .ok (.lit n, rest)
  | Token.fnum f :: rest => .ok (.flit f, rest)
  | Token.kw "intToFloat" :: Token.lparen :: rest => do
    let (e, rest') ← parseExpr rest
    match rest' with
    | Token.rparen :: rest'' => .ok (.intToFloat e, rest'')
    | _ => .error "expected ')' after intToFloat argument"
  | Token.kw "floatToInt" :: Token.lparen :: rest => do
    let (e, rest') ← parseExpr rest
    match rest' with
    | Token.rparen :: rest'' => .ok (.floatToInt e, rest'')
    | _ => .error "expected ')' after floatToInt argument"
  | Token.kw "exp" :: Token.lparen :: rest => do
    let (e, rest') ← parseExpr rest
    match rest' with
    | Token.rparen :: rest'' => .ok (.floatUnary .exp e, rest'')
    | _ => .error "expected ')' after exp argument"
  | Token.kw "sqrt" :: Token.lparen :: rest => do
    let (e, rest') ← parseExpr rest
    match rest' with
    | Token.rparen :: rest'' => .ok (.floatUnary .sqrt e, rest'')
    | _ => .error "expected ')' after sqrt argument"
  | Token.kw "sin" :: Token.lparen :: rest => do
    let (e, rest') ← parseExpr rest
    match rest' with
    | Token.rparen :: rest'' => .ok (.floatUnary .sin e, rest'')
    | _ => .error "expected ')' after sin argument"
  | Token.kw "cos" :: Token.lparen :: rest => do
    let (e, rest') ← parseExpr rest
    match rest' with
    | Token.rparen :: rest'' => .ok (.floatUnary .cos e, rest'')
    | _ => .error "expected ')' after cos argument"
  | Token.kw "tan" :: Token.lparen :: rest => do
    let (e, rest') ← parseExpr rest
    match rest' with
    | Token.rparen :: rest'' => .ok (.floatUnary .tan e, rest'')
    | _ => .error "expected ')' after tan argument"
  | Token.kw "log" :: Token.lparen :: rest => do
    let (e, rest') ← parseExpr rest
    match rest' with
    | Token.rparen :: rest'' => .ok (.floatUnary .log e, rest'')
    | _ => .error "expected ')' after log argument"
  | Token.kw "log2" :: Token.lparen :: rest => do
    let (e, rest') ← parseExpr rest
    match rest' with
    | Token.rparen :: rest'' => .ok (.floatUnary .log2 e, rest'')
    | _ => .error "expected ')' after log2 argument"
  | Token.kw "log10" :: Token.lparen :: rest => do
    let (e, rest') ← parseExpr rest
    match rest' with
    | Token.rparen :: rest'' => .ok (.floatUnary .log10 e, rest'')
    | _ => .error "expected ')' after log10 argument"
  | Token.kw "abs" :: Token.lparen :: rest => do
    let (e, rest') ← parseExpr rest
    match rest' with
    | Token.rparen :: rest'' => .ok (.floatUnary .abs e, rest'')
    | _ => .error "expected ')' after abs argument"
  | Token.kw "neg" :: Token.lparen :: rest => do
    let (e, rest') ← parseExpr rest
    match rest' with
    | Token.rparen :: rest'' => .ok (.floatUnary .neg e, rest'')
    | _ => .error "expected ')' after neg argument"
  | Token.kw "round" :: Token.lparen :: rest => do
    let (e, rest') ← parseExpr rest
    match rest' with
    | Token.rparen :: rest'' => .ok (.floatUnary .round e, rest'')
    | _ => .error "expected ')' after round argument"
  | Token.kw "pow" :: Token.lparen :: rest => do
    let (a, rest') ← parseExpr rest
    match rest' with
    | Token.comma :: rest'' => do
      let (b, rest''') ← parseExpr rest''
      match rest''' with
      | Token.rparen :: rest'''' => .ok (.fbin .fpow a b, rest'''')
      | _ => .error "expected ')' after pow arguments"
    | _ => .error "expected ',' after first pow argument"
  | Token.kw "fmin" :: Token.lparen :: rest => do
    let (a, rest') ← parseExpr rest
    match rest' with
    | Token.comma :: rest'' => do
      let (b, rest''') ← parseExpr rest''
      match rest''' with
      | Token.rparen :: rest'''' => .ok (.fbin .fmin a b, rest'''')
      | _ => .error "expected ')' after fmin arguments"
    | _ => .error "expected ',' after first fmin argument"
  | Token.kw "fmax" :: Token.lparen :: rest => do
    let (a, rest') ← parseExpr rest
    match rest' with
    | Token.comma :: rest'' => do
      let (b, rest''') ← parseExpr rest''
      match rest''' with
      | Token.rparen :: rest'''' => .ok (.fbin .fmax a b, rest'''')
      | _ => .error "expected ')' after fmax arguments"
    | _ => .error "expected ',' after first fmax argument"
  | Token.ident x :: Token.lbracket :: rest => do
    let (idx, rest') ← parseExpr rest
    match rest' with
    | Token.rbracket :: rest'' => .ok (.arrRead x idx, rest'')
    | _ => .error "expected ']' after array index"
  | Token.ident x :: rest => .ok (.var x, rest)
  | Token.lparen :: rest => do
    let (e, rest') ← parseExpr rest
    match rest' with
    | Token.rparen :: rest'' => .ok (e, rest'')
    | _ => .error "expected ')'"
  | Token.op "~" :: rest => do
    let (e, rest') ← parseAtom rest
    .ok (.bin .bxor e (.lit (-1)), rest')
  | Token.op "-" :: Token.num n :: rest => .ok (.lit (-n), rest)
  | Token.op "-" :: Token.fnum f :: rest => .ok (.flit (-f), rest)
  | Token.op "-" :: rest => do
    let (e, rest') ← parseAtom rest
    .ok (.bin .sub (.lit 0) e, rest')
  | tok :: _ => .error s!"expected expression, got {repr tok}"
  | [] => .error "expected expression, got end of input"

partial def parseTerm (toks : List Token) : Except String (SExpr × List Token) := do
  let (e, rest) ← parseAtom toks
  parseTerm' e rest

partial def parseTerm' (lhs : SExpr) (toks : List Token) : Except String (SExpr × List Token) :=
  match toks with
  | Token.op "*" :: rest => do let (rhs, rest') ← parseAtom rest; parseTerm' (.bin .mul lhs rhs) rest'
  | Token.op "/" :: rest => do let (rhs, rest') ← parseAtom rest; parseTerm' (.bin .div lhs rhs) rest'
  | Token.op "%" :: rest => do let (rhs, rest') ← parseAtom rest; parseTerm' (.bin .mod lhs rhs) rest'
  | _ => .ok (lhs, toks)

partial def parseAddSub (toks : List Token) : Except String (SExpr × List Token) := do
  let (e, rest) ← parseTerm toks
  parseAddSub' e rest

partial def parseAddSub' (lhs : SExpr) (toks : List Token) : Except String (SExpr × List Token) :=
  match toks with
  | Token.op "+" :: rest => do let (rhs, rest') ← parseTerm rest; parseAddSub' (.bin .add lhs rhs) rest'
  | Token.op "-" :: rest => do let (rhs, rest') ← parseTerm rest; parseAddSub' (.bin .sub lhs rhs) rest'
  | _ => .ok (lhs, toks)

partial def parseShift (toks : List Token) : Except String (SExpr × List Token) := do
  let (e, rest) ← parseAddSub toks
  parseShift' e rest

partial def parseShift' (lhs : SExpr) (toks : List Token) : Except String (SExpr × List Token) :=
  match toks with
  | Token.op "<<" :: rest => do let (rhs, rest') ← parseAddSub rest; parseShift' (.bin .shl lhs rhs) rest'
  | Token.op ">>" :: rest => do let (rhs, rest') ← parseAddSub rest; parseShift' (.bin .shr lhs rhs) rest'
  | _ => .ok (lhs, toks)

partial def parseBitAnd (toks : List Token) : Except String (SExpr × List Token) := do
  let (e, rest) ← parseShift toks
  parseBitAnd' e rest

partial def parseBitAnd' (lhs : SExpr) (toks : List Token) : Except String (SExpr × List Token) :=
  match toks with
  | Token.op "&" :: rest => do let (rhs, rest') ← parseShift rest; parseBitAnd' (.bin .band lhs rhs) rest'
  | _ => .ok (lhs, toks)

partial def parseBitXor (toks : List Token) : Except String (SExpr × List Token) := do
  let (e, rest) ← parseBitAnd toks
  parseBitXor' e rest

partial def parseBitXor' (lhs : SExpr) (toks : List Token) : Except String (SExpr × List Token) :=
  match toks with
  | Token.op "^" :: rest => do let (rhs, rest') ← parseBitAnd rest; parseBitXor' (.bin .bxor lhs rhs) rest'
  | _ => .ok (lhs, toks)

partial def parseExpr (toks : List Token) : Except String (SExpr × List Token) := do
  let (e, rest) ← parseBitXor toks
  parseExpr' e rest

partial def parseExpr' (lhs : SExpr) (toks : List Token) : Except String (SExpr × List Token) :=
  match toks with
  | Token.op "|" :: rest => do let (rhs, rest') ← parseBitXor rest; parseExpr' (.bin .bor lhs rhs) rest'
  | _ => .ok (lhs, toks)

partial def parseBAtom (toks : List Token) : Except String (SBool × List Token) :=
  match toks with
  | Token.kw "true" :: rest => .ok (.lit true, rest)
  | Token.kw "false" :: rest => .ok (.lit false, rest)
  | Token.lparen :: rest => do
    -- Try as boolean expression first
    match parseBOr rest with
    | .ok (b, Token.rparen :: rest'') => .ok (b, rest'')
    | _ =>
      -- Fall back: parenthesized int expr, then comparison op
      let (e1, rest') ← parseExpr (Token.lparen :: rest)
      match rest' with
      | Token.op "<" :: rest'' =>  do let (e2, r) ← parseExpr rest''; .ok (.cmp .lt e1 e2, r)
      | Token.op "<=" :: rest'' => do let (e2, r) ← parseExpr rest''; .ok (.cmp .le e1 e2, r)
      | Token.op "==" :: rest'' => do let (e2, r) ← parseExpr rest''; .ok (.cmp .eq e1 e2, r)
      | Token.op "!=" :: rest'' => do let (e2, r) ← parseExpr rest''; .ok (.cmp .ne e1 e2, r)
      | Token.op ">" :: rest'' =>  do let (e2, r) ← parseExpr rest''; .ok (.cmp .lt e2 e1, r)
      | Token.op ">=" :: rest'' => do let (e2, r) ← parseExpr rest''; .ok (.cmp .le e2 e1, r)
      | _ => .error "expected ')' after boolean expression"
  | Token.op "!" :: rest => do
    let (b, rest') ← parseBAtom rest
    .ok (.not b, rest')
  | _ => do
    let (e1, rest) ← parseExpr toks
    match rest with
    | Token.op "<" :: rest' =>  do let (e2, r) ← parseExpr rest'; .ok (.cmp .lt e1 e2, r)
    | Token.op "<=" :: rest' => do let (e2, r) ← parseExpr rest'; .ok (.cmp .le e1 e2, r)
    | Token.op "==" :: rest' => do let (e2, r) ← parseExpr rest'; .ok (.cmp .eq e1 e2, r)
    | Token.op "!=" :: rest' => do let (e2, r) ← parseExpr rest'; .ok (.cmp .ne e1 e2, r)
    | Token.op ">" :: rest' =>  do let (e2, r) ← parseExpr rest'; .ok (.cmp .lt e2 e1, r)
    | Token.op ">=" :: rest' => do let (e2, r) ← parseExpr rest'; .ok (.cmp .le e2 e1, r)
    | _ =>
      match e1 with
      | .var x => .ok (.bvar x, rest)
      | .arrRead arr idx => .ok (.barrRead arr idx, rest)
      | _ => .error "expected comparison operator after expression"

partial def parseBNot (toks : List Token) : Except String (SBool × List Token) :=
  match toks with
  | Token.op "!" :: rest => do let (b, rest') ← parseBNot rest; .ok (.not b, rest')
  | _ => parseBAtom toks

partial def parseBand (toks : List Token) : Except String (SBool × List Token) := do
  let (b, rest) ← parseBNot toks
  parseBand' b rest

partial def parseBand' (lhs : SBool) (toks : List Token) : Except String (SBool × List Token) :=
  match toks with
  | Token.op "&&" :: rest => do let (rhs, rest') ← parseBNot rest; parseBand' (.and lhs rhs) rest'
  | _ => .ok (lhs, toks)

partial def parseBOr (toks : List Token) : Except String (SBool × List Token) := do
  let (b, rest) ← parseBand toks
  parseBOr' b rest

partial def parseBOr' (lhs : SBool) (toks : List Token) : Except String (SBool × List Token) :=
  match toks with
  | Token.op "||" :: rest => do let (rhs, rest') ← parseBand rest; parseBOr' (.or lhs rhs) rest'
  | _ => .ok (lhs, toks)

partial def parseBExprParen (toks : List Token) : Except String (SBool × List Token) :=
  match toks with
  | Token.lparen :: rest => do
    let (b, rest') ← parseBOr rest
    match rest' with
    | Token.rparen :: rest'' => .ok (b, rest'')
    | _ => .error "expected ')' after condition"
  | _ => parseBOr toks

partial def parseStmtAtom (toks : List Token) : Except String (Stmt × List Token) :=
  match toks with
  | Token.kw "skip" :: rest => .ok (.skip, rest)
  | Token.ident x :: Token.lbracket :: rest => do
    let (idx, rest') ← parseExpr rest
    match rest' with
    | Token.rbracket :: Token.op ":=" :: rest'' =>
      match rest'' with
      | Token.kw "true" :: _ | Token.kw "false" :: _ | Token.op "!" :: _ => do
        let (b, rest''') ← parseBOr rest''
        .ok (.barrWrite x idx b, rest''')
      | Token.lparen :: _ =>
        match parseBOr rest'' with
        | .ok (b, rest''') => .ok (.barrWrite x idx b, rest''')
        | .error _ => do
          let (val, rest''') ← parseExpr rest''
          .ok (.arrWrite x idx val, rest''')
      | _ => do
        let (val, rest''') ← parseExpr rest''
        match rest''' with
        | Token.op "<" :: _ | Token.op "<=" :: _ | Token.op ">" :: _ | Token.op ">=" :: _
        | Token.op "==" :: _ | Token.op "!=" :: _
        | Token.op "&&" :: _ | Token.op "||" :: _ => do
          let (b, rest4) ← parseBOr rest''
          .ok (.barrWrite x idx b, rest4)
        | _ => .ok (.arrWrite x idx val, rest''')
    | _ => .error "expected '] :=' for array write"
  | Token.ident x :: Token.op ":=" :: rest =>
    match rest with
    | Token.kw "true" :: _ | Token.kw "false" :: _ | Token.op "!" :: _ => do
      let (b, rest') ← parseBOr rest
      .ok (.bassign x b, rest')
    | Token.lparen :: _ => do
      -- Ambiguous: could be parenthesized int expr or parenthesized bool expr.
      -- Try boolean first (it handles both since comparison falls through to expr).
      match parseBOr rest with
      | .ok (b, rest') => .ok (.bassign x b, rest')
      | .error _ => do
        let (e, rest') ← parseExpr rest
        .ok (.assign x e, rest')
    | _ => do
      let (e, rest') ← parseExpr rest
      match rest' with
      | Token.op "<" :: _ | Token.op "<=" :: _ | Token.op ">" :: _ | Token.op ">=" :: _
      | Token.op "==" :: _ | Token.op "!=" :: _
      | Token.op "&&" :: _ | Token.op "||" :: _ => do
        let (b, rest'') ← parseBOr rest
        .ok (.bassign x b, rest'')
      | _ => .ok (.assign x e, rest')
  | Token.kw "goto" :: Token.ident lbl :: rest => .ok (.goto lbl, rest)
  | Token.kw "if" :: rest => do
    let (cond, rest') ← parseBExprParen rest
    match rest' with
    | Token.kw "goto" :: Token.ident lbl :: rest'' => .ok (.ifgoto cond lbl, rest'')
    | Token.lbrace :: rest'' => do
      let (s1, rest''') ← parseStmt rest''
      match rest''' with
      | Token.rbrace :: Token.kw "else" :: Token.lbrace :: rest4 => do
        let (s2, rest5) ← parseStmt rest4
        match rest5 with
        | Token.rbrace :: rest6 => .ok (.ite cond s1 s2, rest6)
        | _ => .error "expected '}' after else branch"
      | _ => .error "expected '} else {'"
    | _ => .error "expected '{' or 'goto' after if condition"
  | Token.kw "while" :: rest => do
    let (cond, rest') ← parseBExprParen rest
    match rest' with
    | Token.lbrace :: rest'' => do
      let (body, rest''') ← parseStmt rest''
      match rest''' with
      | Token.rbrace :: rest4 => .ok (.loop cond body, rest4)
      | _ => .error "expected '}' after while body"
    | _ => .error "expected '{' after while condition"
  | Token.ident lbl :: Token.colon :: rest => .ok (.label lbl, rest)
  | Token.kw "print" :: Token.str fmt :: rest => do
    let (args, rest') ← parsePrintArgs rest ([] : List SExpr)
    .ok (.print fmt args, rest')
  | Token.kw "print" :: _ => .error "expected string literal after 'print'"
  | Token.kw "printInt" :: Token.lparen :: rest => do
    let (e, rest') ← parseExpr rest
    match rest' with
    | Token.rparen :: rest'' => .ok (.printInt e, rest'')
    | _ => .error "expected ')' after printInt argument"
  | Token.kw "printInt" :: _ => .error "expected '(' after 'printInt'"
  | Token.kw "printBool" :: Token.lparen :: rest => do
    let (b, rest') ← parseBOr rest
    match rest' with
    | Token.rparen :: rest'' => .ok (.printBool b, rest'')
    | _ => .error "expected ')' after printBool argument"
  | Token.kw "printBool" :: _ => .error "expected '(' after 'printBool'"
  | Token.kw "printFloat" :: Token.lparen :: rest => do
    let (e, rest') ← parseExpr rest
    match rest' with
    | Token.rparen :: rest'' => .ok (.printFloat e, rest'')
    | _ => .error "expected ')' after printFloat argument"
  | Token.kw "printFloat" :: _ => .error "expected '(' after 'printFloat'"
  | Token.kw "printString" :: Token.lparen :: Token.str lit :: Token.rparen :: rest =>
    .ok (.printString lit, rest)
  | Token.kw "printString" :: _ => .error "expected '(\"<literal>\")' after 'printString'"
  | tok :: _ => .error s!"expected statement, got {repr tok}"
  | [] => .error "expected statement, got end of input"

partial def parseStmt (toks : List Token) : Except String (Stmt × List Token) := do
  let (s, rest) ← parseStmtAtom toks
  parseStmt' s rest

partial def parseStmt' (lhs : Stmt) (toks : List Token) : Except String (Stmt × List Token) :=
  match toks with
  | Token.semi :: Token.rbrace :: rest => .ok (lhs, Token.rbrace :: rest)
  | Token.semi :: rest => do
    let (rhs, rest') ← parseStmtAtom rest
    parseStmt' (.seq lhs rhs) rest'
  | _ => .ok (lhs, toks)

/-- Parse comma-separated expressions for print arguments. -/
partial def parsePrintArgs (toks : List Token) (acc : List SExpr) : Except String (List SExpr × List Token) :=
  match toks with
  | Token.comma :: rest => do
    let (e, rest') ← parseExpr rest
    parsePrintArgs rest' (acc ++ [e])
  | _ => .ok (acc, toks)

end

-- ============================================================
-- § 3. Declaration and program parser
-- ============================================================

private def parseDecl (toks : List Token) : Except String ((Var × VarTy) × List Token) :=
  match toks with
  | Token.ident x :: Token.colon :: Token.kw "int" :: rest => .ok ((x, .int), rest)
  | Token.ident x :: Token.colon :: Token.kw "bool" :: rest => .ok ((x, .bool), rest)
  | Token.ident x :: Token.colon :: Token.kw "float" :: rest => .ok ((x, .float), rest)
  | Token.ident _ :: Token.colon :: tok :: _ => .error s!"expected 'int', 'bool', or 'float', got {repr tok}"
  | Token.ident _ :: tok :: _ => .error s!"expected ':', got {repr tok}"
  | tok :: _ => .error s!"expected variable name, got {repr tok}"
  | [] => .error "expected declaration"

private partial def parseDecls' (acc : List (Var × VarTy)) (toks : List Token)
    : Except String (List (Var × VarTy) × List Token) :=
  match toks with
  | Token.comma :: rest => do let (d, rest') ← parseDecl rest; parseDecls' (acc ++ [d]) rest'
  | Token.semi :: rest => .ok (acc, rest)
  | tok :: _ => .error s!"expected ',' or ';' after declaration, got {repr tok}"
  | [] => .error "expected ';' after declarations"

private partial def parseDecls (toks : List Token) : Except String (List (Var × VarTy) × List Token) :=
  match toks with
  | Token.kw "var" :: rest => do
    let (d, rest') ← parseDecl rest
    parseDecls' [d] rest'
  | tok :: _ => .error s!"expected 'var', got {repr tok}"
  | [] => .error "expected 'var'"

/-- Parse a single array declaration: `name[size] : type`. -/
private def parseArrayDecl (toks : List Token)
    : Except String ((ArrayName × Nat × VarTy) × List Token) :=
  match toks with
  | Token.ident name :: Token.lbracket :: Token.num n :: Token.rbracket
      :: Token.colon :: Token.kw "int" :: rest =>
    if n ≥ 0 then .ok ((name, n.toNat, .int), rest)
    else .error s!"array size must be non-negative, got {n}"
  | Token.ident name :: Token.lbracket :: Token.num n :: Token.rbracket
      :: Token.colon :: Token.kw "bool" :: rest =>
    if n ≥ 0 then .ok ((name, n.toNat, .bool), rest)
    else .error s!"array size must be non-negative, got {n}"
  | Token.ident name :: Token.lbracket :: Token.num n :: Token.rbracket
      :: Token.colon :: Token.kw "float" :: rest =>
    if n ≥ 0 then .ok ((name, n.toNat, .float), rest)
    else .error s!"array size must be non-negative, got {n}"
  | Token.ident _ :: Token.lbracket :: Token.num _ :: Token.rbracket
      :: Token.colon :: tok :: _ =>
    .error s!"expected 'int', 'bool', or 'float' after ':', got {repr tok}"
  | Token.ident _ :: Token.lbracket :: Token.num _ :: Token.rbracket
      :: tok :: _ =>
    .error s!"expected ':' after ']', got {repr tok}"
  | Token.ident _ :: Token.lbracket :: Token.num _ :: tok :: _ =>
    .error s!"expected ']' after array size, got {repr tok}"
  | Token.ident _ :: Token.lbracket :: tok :: _ =>
    .error s!"expected array size (integer), got {repr tok}"
  | Token.ident _ :: tok :: _ => .error s!"expected '[' after array name, got {repr tok}"
  | tok :: _ => .error s!"expected array name, got {repr tok}"
  | [] => .error "expected array declaration"

private partial def parseArrayDecls' (acc : List (ArrayName × Nat × VarTy)) (toks : List Token)
    : Except String (List (ArrayName × Nat × VarTy) × List Token) :=
  match toks with
  | Token.comma :: rest => do let (d, rest') ← parseArrayDecl rest; parseArrayDecls' (acc ++ [d]) rest'
  | Token.semi :: rest => .ok (acc, rest)
  | tok :: _ => .error s!"expected ',' or ';' after array declaration, got {repr tok}"
  | [] => .error "expected ';' after array declarations"

private partial def parseArrayDecls (toks : List Token)
    : Except String (List (ArrayName × Nat × VarTy) × List Token) :=
  match toks with
  | Token.kw "array" :: rest => do
    let (d, rest') ← parseArrayDecl rest
    parseArrayDecls' [d] rest'
  | _ => .ok ([], toks)  -- array declarations are optional

-- ============================================================
-- § 3a. Type resolution (convert int ops to float where appropriate)
-- ============================================================

/-- Infer whether an SExpr is a float expression based on variable/literal types. -/
private def isFloatExpr (lookupVar : Var → Option VarTy)
    (lookupArr : ArrayName → Option VarTy) : SExpr → Bool
  | .flit _ | .fbin _ _ _ | .intToFloat _ | .floatUnary _ _ | .farrRead _ _ => true
  | .var x => lookupVar x == some .float
  | .arrRead arr _ => lookupArr arr == some .float
  | _ => false

/-- Resolve types in an SExpr: convert `.bin` to `.fbin` when operands are float. -/
private partial def resolveSExpr (lookupVar : Var → Option VarTy)
    (lookupArr : ArrayName → Option VarTy) : SExpr → SExpr
  | .lit n => .lit n
  | .flit f => .flit f
  | .var x => .var x
  | .bin op a b =>
    let a' := resolveSExpr lookupVar lookupArr a
    let b' := resolveSExpr lookupVar lookupArr b
    if isFloatExpr lookupVar lookupArr a' || isFloatExpr lookupVar lookupArr b' then
      match op.toFloat? with
      | some fop => .fbin fop a' b'
      | none => .bin op a' b'  -- mod on floats: leave as-is (type error)
    else .bin op a' b'
  | .arrRead arr idx =>
    let idx' := resolveSExpr lookupVar lookupArr idx
    if lookupArr arr == some .float then .farrRead arr idx'
    else .arrRead arr idx'
  | .fbin op a b => .fbin op (resolveSExpr lookupVar lookupArr a) (resolveSExpr lookupVar lookupArr b)
  | .intToFloat e => .intToFloat (resolveSExpr lookupVar lookupArr e)
  | .floatToInt e => .floatToInt (resolveSExpr lookupVar lookupArr e)
  | .floatUnary op e => .floatUnary op (resolveSExpr lookupVar lookupArr e)
  | .farrRead arr idx => .farrRead arr (resolveSExpr lookupVar lookupArr idx)

/-- Resolve types in an SBool: convert `.cmp` to `.fcmp` when operands are float. -/
private partial def resolveSBool (lookupVar : Var → Option VarTy)
    (lookupArr : ArrayName → Option VarTy) : SBool → SBool
  | .lit b => .lit b
  | .bvar x => .bvar x
  | .cmp op a b =>
    let a' := resolveSExpr lookupVar lookupArr a
    let b' := resolveSExpr lookupVar lookupArr b
    if isFloatExpr lookupVar lookupArr a' || isFloatExpr lookupVar lookupArr b' then
      .fcmp op.toFloat a' b'
    else .cmp op a' b'
  | .not e => .not (resolveSBool lookupVar lookupArr e)
  | .and a b => .and (resolveSBool lookupVar lookupArr a) (resolveSBool lookupVar lookupArr b)
  | .or a b => .or (resolveSBool lookupVar lookupArr a) (resolveSBool lookupVar lookupArr b)
  | .barrRead arr idx => .barrRead arr (resolveSExpr lookupVar lookupArr idx)
  | .fcmp op a b => .fcmp op (resolveSExpr lookupVar lookupArr a) (resolveSExpr lookupVar lookupArr b)

/-- Try to view a (resolved) SExpr as a SBool when the destination is bool-typed.
    Handles only the syntactic forms that the statement parser produces for
    `t := flags[i]` / `flags[0] := flags[3]`-style writes (the parser commits
    to SExpr before the type is known). Other forms are left to the
    well-formedness check to reject. -/
private def sExprToSBool (lookupVar : Var → Option VarTy)
    (lookupArr : ArrayName → Option VarTy) : SExpr → Option SBool
  | .var x => if lookupVar x == some .bool then some (.bvar x) else none
  | .arrRead arr idx => if lookupArr arr == some .bool then some (.barrRead arr idx) else none
  | _ => none

/-- Resolve types in a Stmt: convert `.assign` to `.fassign`, `.arrWrite` to `.farrWrite`.
    Also reroute bool-typed `.assign`/`.arrWrite` to `.bassign`/`.barrWrite` when the
    parser-emitted SExpr value can be re-viewed as a SBool (a `.bvar` or `.barrRead`). -/
private partial def resolveStmt (lookupVar : Var → Option VarTy)
    (lookupArr : ArrayName → Option VarTy) : Stmt → Stmt
  | .skip => .skip
  | .assign x e =>
    let e' := resolveSExpr lookupVar lookupArr e
    if lookupVar x == some .float then .fassign x e'
    else if lookupVar x == some .bool then
      match sExprToSBool lookupVar lookupArr e' with
      | some b => .bassign x b
      | none => .assign x e'
    else .assign x e'
  | .bassign x b => .bassign x (resolveSBool lookupVar lookupArr b)
  | .arrWrite arr idx val =>
    let idx' := resolveSExpr lookupVar lookupArr idx
    let val' := resolveSExpr lookupVar lookupArr val
    if lookupArr arr == some .float then .farrWrite arr idx' val'
    else if lookupArr arr == some .bool then
      match sExprToSBool lookupVar lookupArr val' with
      | some bval => .barrWrite arr idx' bval
      | none => .arrWrite arr idx' val'
    else .arrWrite arr idx' val'
  | .barrWrite arr idx bval =>
    .barrWrite arr (resolveSExpr lookupVar lookupArr idx) (resolveSBool lookupVar lookupArr bval)
  | .seq s1 s2 => .seq (resolveStmt lookupVar lookupArr s1) (resolveStmt lookupVar lookupArr s2)
  | .ite b s1 s2 =>
    .ite (resolveSBool lookupVar lookupArr b) (resolveStmt lookupVar lookupArr s1) (resolveStmt lookupVar lookupArr s2)
  | .loop b body => .loop (resolveSBool lookupVar lookupArr b) (resolveStmt lookupVar lookupArr body)
  | .fassign x e => .fassign x (resolveSExpr lookupVar lookupArr e)
  | .farrWrite arr idx val =>
    .farrWrite arr (resolveSExpr lookupVar lookupArr idx) (resolveSExpr lookupVar lookupArr val)
  | .label lbl => .label lbl
  | .goto lbl => .goto lbl
  | .ifgoto b lbl => .ifgoto (resolveSBool lookupVar lookupArr b) lbl
  | .print fmt args => .print fmt (args.map (resolveSExpr lookupVar lookupArr))
  | .printInt e => .printInt (resolveSExpr lookupVar lookupArr e)
  | .printBool b => .printBool (resolveSBool lookupVar lookupArr b)
  | .printFloat e => .printFloat (resolveSExpr lookupVar lookupArr e)
  | .printString lit => .printString lit

/-- Parse a string into a `Program`. -/
def parseProgram (input : String) : Except String Program := do
  let toks ← tokenize input
  let (decls, rest) ← parseDecls toks
  let (arrayDecls, rest'') ← parseArrayDecls rest
  let (body, rest') ← parseStmt rest''
  if rest'.isEmpty then
    -- Type resolution: convert int ops to float where declared types indicate
    let lookupVar : Var → Option VarTy := fun x => decls.lookup x
    let lookupArr : ArrayName → Option VarTy := fun arr =>
      (arrayDecls.find? (fun (a, _, _) => a == arr)).map (fun (_, _, ty) => ty)
    let body' := resolveStmt lookupVar lookupArr body
    .ok { decls, arrayDecls, body := body' }
  else .error s!"unexpected tokens after program"

-- ============================================================
-- § 4. Tests
-- ============================================================

#eval! parseProgram "var x : int, y : int; x := 0; y := x + 1"

#eval! parseProgram "
  var n : int, s : int, i : int;
  s := 0;
  i := 1;
  while (i <= n) {
    s := s + i;
    i := i + 1
  }
"

#eval! parseProgram "
  var r : int, n : int;
  r := 1;
  while (n != 0) {
    r := r * n;
    n := n - 1
  }
"

#eval! parseProgram "
  var a : int, b : int, m : int;
  if (a < b) { m := b } else { m := a }
"

#eval! parseProgram "
  var x : int, flag : bool;
  x := 5;
  flag := x < 10
"

-- Float program test
#eval! parseProgram "
  var x : float, y : float, n : int;
  x := 3.14;
  y := x + 2.0;
  n := floatToInt(y)
"

-- Float array test
#eval! parseProgram "
  var x : float, i : int;
  array A[10] : float;
  x := 1.5;
  A[0] := x;
  x := A[0] + 2.5
"

-- End-to-end: parse → compile → optimize → check
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
  return (prog.compileToTAC.code.toList, checkCertificateVerboseExec (ConstPropOpt.optimize prog.tyCtx prog.compileToTAC))
