/-
# Lang.Pretty — a package or a term printed with glyphs, for a person to read

A printer, not a second surface. `pretty x` prints the tree `Read.parse` made of a text: the member's
own surface text or a core text. Nothing here reads types or lowers anything. Install, the core text,
the wire and every refusal are unchanged; the raw text stays the source of truth.

The printer has three parts.

* The GLYPH TABLE (`table`): a form `(HEAD child…)` of a known shape prints as a template of glyphs and
  its children (`(<= a b)` as `a ≤ b`, `(record (k 0))` as `⟨k ≔ 0⟩`, `(hole u e)` as `◯u[e]`). Two atoms
  print as glyphs wherever they stand (`nat` as `ℕ`, `ok` as `⊤`). A form of no known shape prints as
  itself, in parentheses.
* A LAYOUT pass (`render`): declarations one per line with the keyword in a fixed column, a law's arms
  aligned on `↦`, a hole's candidates one per line with their facts in a fixed column, long terms broken
  at a width. Layout only places whitespace and decorations (a candidate's index, a view's marks).
* A POSITION MAP: each printed token that came from an atom, a string or a form carries that node's
  source offset, so a refusal at an offset can be shown on the printed token.

`unglyph` reads a printed text back: it drops whitespace and decorations, reads each glyph as the atom
or form it stands for, and returns the tree. `Lang.Proofs.Pretty.unglyph_pretty` proves that it gives
back the printed tree up to offsets, for every tree the reader can make. That theorem rests on one
decidable property of the table (`tableOk`, proved by `decide`): each template is told apart from the
others by one token, and nothing that may follow a form can be read as part of it.

An atom whose text would read as something else (a keyword such as `then`, an operator such as `+`, or
text holding a glyph character) prints escaped, `‹then›` or `‹"a,b"›`. A string prints as `“text”`, or as
`"text"` when it holds a `”`.
-/
import Lang.Read

namespace Nanodregg.Lang.Pretty

open Read (SExp)

/-! ## Tokens -/

/-- A printed token: a word (an atom's own text, or a keyword), one glyph character, or a string. -/
inductive Lx
  | w (s : String)
  | g (c : Char)
  | q (s : String)
  deriving DecidableEq, Repr, Inhabited

def Lx.isQuote : Lx → Bool
  | .q _ => true
  | _ => false

/-- The characters that are a token of their own wherever they stand. -/
def symChars : List Char :=
  ['(', ')', '[', ']', '{', '}', ',', ':', '?', '‹', '›', '⟨', '⟩', '≔', '↦', 'λ', 'ℕ', '⊤', '⊥', '∧', '∨',
   '¬', '⧺', '≡', '→', '≤', '∈', '‥', '·', '←', '⊕', '⊖', '◯', '◇', '∅', 'Σ', '⊢', '⊣', '−', '×', '÷']

/-- Characters the reader of a printed text skips, like whitespace: a candidate's index and a view's marks. -/
def decoChars : List Char := ['₀', '₁', '₂', '₃', '₄', '₅', '₆', '₇', '₈', '₉', '✓', '✗', '◉']

def isSym (c : Char) : Bool := symChars.contains c
def isDeco (c : Char) : Bool := decoChars.contains c

/-- A character that may stand inside a word. -/
def wordChar (c : Char) : Bool :=
  !c.isWhitespace && !isSym c && !isDeco c && c != '"' && c != '“' && c != '”'

def wordSafe (s : String) : Bool := !s.toList.isEmpty && s.toList.all wordChar

/-- The text of a token. A string holding `”` is written with ASCII quotes (a string never holds `"`). -/
def Lx.chars : Lx → List Char
  | .w s => s.toList
  | .g c => [c]
  | .q s => if s.toList.contains '”' then '"' :: (s.toList ++ ['"']) else '“' :: (s.toList ++ ['”'])

/-! ## The glyph table: atoms -/

/-- The atoms that print as a glyph wherever they stand. -/
def atomGlyphs : List (String × Lx) := [("nat", .g 'ℕ'), ("ok", .g '⊤')]

/-- How an atom prints, before escaping: its glyph, else its text as a word, else its text quoted. -/
def atomLex (a : String) : Lx :=
  match atomGlyphs.find? (·.1 = a) with
  | some (_, l) => l
  | none => if wordSafe a && !(atomGlyphs.any (·.2 = .w a)) then .w a else .q a

/-- The atom a token names: the inverse of `atomLex`. -/
def unlex : Lx → String
  | l@(.w s) => match atomGlyphs.find? (·.2 = l) with
    | some (a, _) => a
    | none => s
  | l@(.g c) => match atomGlyphs.find? (·.2 = l) with
    | some (a, _) => a
    | none => String.singleton c
  | .q s => s

/-! ## The glyph table: forms -/

/-- The kinds of position a form may stand in. Each kind has its own templates. -/
inductive Cls
  | top | expr | prim | decl | clause | arm | occ | field | vfield | cArm | cond | ctx | ctxE | hcl | pin
  | item | relCl | coreRel | effRow | claimRow
  deriving DecidableEq, Repr, Inhabited

def allCls : List Cls :=
  [.top, .expr, .prim, .decl, .clause, .arm, .occ, .field, .vfield, .cArm, .cond, .ctx, .ctxE, .hcl, .pin,
   .item, .relCl, .coreRel, .effRow, .claimRow]

/-- A pattern for one element of a form. -/
inductive Src
  /-- exactly this atom (it prints through the template's own glyphs) -/
  | atom (s : String)
  /-- one of these atoms, bound like `one` -/
  | atomIn (ss : List String)
  /-- one element, bound -/
  | one
  /-- every element left over at this level, bound as a list -/
  | rest
  /-- a list, element by element -/
  | list (ps : List Src)
  deriving DecidableEq, Repr, Inhabited

/-- Whitespace and decoration a template asks for; none of it is a token. -/
inductive Lay
  /-- a line break at the current indentation -/
  | nl
  /-- indent what follows by `n` more -/
  | ind (n : Nat)
  /-- undo the last `ind` -/
  | ded
  /-- pad to column `n` past the current indentation (one space if already past it) -/
  | col (n : Nat)
  /-- where a column of aligned items is padded (`Many.align`) -/
  | tab
  /-- the item's index among its many's items, as subscript digits -/
  | idx
  /-- no space before the next token -/
  | glue
  deriving DecidableEq, Repr, Inhabited

/-- How a list of elements bound by one `rest` prints: its items' kind, the token between items, and
the tokens around them, written only when there is at least one item. -/
structure Many where
  sep : Option Lx := none
  lead : Option Lx := none
  close : Option Lx := none
  /-- each item on its own line -/
  vert : Bool := false
  /-- pad each item at its `tab` so the tabs line up -/
  align : Bool := false
  /-- the last item on its own line -/
  lastNl : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- One piece of a printed template. -/
inductive Pc
  | lit (l : Lx)
  /-- bound element `i` (counting `one`s and `atomIn`s in order) printed as kind `c` -/
  | slot (c : Cls) (i : Nat)
  /-- bound list `j` (counting `rest`s in order), each item printed as kind `c` -/
  | many (c : Cls) (j : Nat) (m : Many)
  | lay (x : Lay)
  deriving DecidableEq, Repr, Inhabited

/-- A form's shape and how it prints. -/
structure Tmpl where
  src : List Src
  out : List Pc
  deriving DecidableEq, Repr, Inhabited

/-- How a kind of position reads: its own templates, whether it also takes the expression templates,
whether an atom may start an item unescaped (`bare`), and whether its one template is the only shape
it takes (`strict`: no item of any other shape). -/
structure Spec where
  own : List Tmpl
  inherit : Bool := false
  bare : Bool := true
  strict : Bool := false
  deriving Repr, Inhabited

section table
open Pc Lay

private def w (s : String) : Pc := .lit (.w s)
private def g (c : Char) : Pc := .lit (.g c)
private def comma : Option Lx := some (.g ',')

/-- `(op a b)` as `a op b`. -/
private def infix2 (head : String) (op : Lx) : Tmpl :=
  ⟨[.atom head, .one, .one], [slot .prim 0, lit op, slot .prim 1]⟩

/-- Fields `(f x)…` between two glyphs, as `f : x` or `f ≔ x`. -/
private def fields (c : Cls) (j : Nat) : Pc := many c j { sep := comma }

/-- The expression templates: terms and types, in a surface or a core text. -/
def exprT : List Tmpl :=
  [ ⟨[.atom "if", .one, .one, .one], [w "if", slot .expr 0, w "then", slot .expr 1, w "else", slot .expr 2]⟩
  , ⟨[.atom "lam", .one, .one, .one], [g 'λ', lay .glue, slot .prim 0, g ':', slot .expr 1, g '↦', slot .expr 2]⟩
  , ⟨[.atom "let", .one, .one, .one, .one],
      [w "let", slot .prim 0, g ':', slot .expr 1, g '≔', slot .expr 2, w "in", slot .expr 3]⟩
  , ⟨[.atom "case", .one, .rest],
      [w "case", slot .expr 0, g '{', lay (ind 2), many .cArm 0 { sep := comma, vert := true, align := true }, lay ded,
       lay nl, g '}']⟩
  , ⟨[.atom "done", .one, .rest],
      [w "done", slot .expr 0, lay (ind 2), many .item 0 { sep := comma, lead := some (.g '['), close := some (.g ']'), vert := true },
       lay ded]⟩
  , ⟨[.atom "check", .rest, .one],
      [w "check", lay (ind 2), many .cond 0 { sep := comma, vert := true }, lay ded, lay nl, w "then", slot .expr 0]⟩
  , ⟨[.atom "all", .rest], [w "all", g '[', lay (ind 2), many .cond 0 { sep := comma, vert := true }, lay ded, g ']']⟩
  , ⟨[.atom "not", .one], [g '¬', lay .glue, slot .prim 0]⟩
  , ⟨[.atom "refuse", .one], [g '⊥', slot .prim 0]⟩
  , ⟨[.atom "none", .one], [g '∅', slot .prim 0]⟩
  , ⟨[.atom "record", .rest], [g '⟨', lay .glue, fields .vfield 0, lay .glue, g '⟩']⟩
  , ⟨[.atom "rec", .rest], [g '{', lay .glue, fields .field 0, lay .glue, g '}']⟩
  , ⟨[.atom "sum", .rest], [g 'Σ', lay .glue, g '{', lay .glue, fields .field 0, lay .glue, g '}']⟩
  , ⟨[.atom "hole", .one, .rest],
      [g '◯', lay .glue, slot .prim 0, lay .glue, g '[', lay .glue, many .expr 0 { sep := comma }, lay .glue, g ']']⟩
  , ⟨[.atom "and", .one, .one], [slot .prim 0, g '∧', slot .prim 1]⟩
  , ⟨[.atom "any", .one, .one, .rest],
      [slot .prim 0, g '∨', slot .prim 1, many .prim 0 { sep := some (.g '∨'), lead := some (.g '∨') }]⟩
  , infix2 "+" (.w "+"), infix2 "-" (.g '−'), infix2 "*" (.g '×'), infix2 "/" (.g '÷'), infix2 "%" (.w "%")
  , infix2 "<" (.w "<"), infix2 "<=" (.g '≤'), infix2 "==" (.w "="), infix2 "cat" (.g '⧺'), infix2 "deq" (.g '≡')
  , infix2 "->" (.g '→')
  , ⟨[.atom ".", .one, .one], [slot .prim 0, lay .glue, g '·', lay .glue, slot .prim 1]⟩
  , ⟨[.atom "option", .one], [slot .prim 0, lay .glue, g '?']⟩
  , ⟨[.atomIn ["nat", "bytes"], .one, .one], [slot .prim 0, g '∈', slot .prim 1, lay .glue, g '‥', lay .glue, slot .prim 2]⟩
  , ⟨[.atom "with", .one, .rest], [slot .prim 0, w "with", g '⟨', lay .glue, fields .vfield 0, lay .glue, g '⟩']⟩ ]

/-- The kinds of a method's effects (`Surface.callKinds`). -/
def callKinds : List String := ["account", "credit", "grant", "install", "transfer", "invoke"]

def spec : Cls → Spec
  | .top => { own := [⟨[.atom "package", .rest], [w "package", lay (ind 2), many .decl 0 { vert := true }, lay ded]⟩],
              inherit := true }
  | .expr => { own := exprT }
  | .prim => { own := [] }
  | .decl => { bare := false, own :=
      [ ⟨[.atom "doc", .one], [w "doc", lay (col 8), slot .prim 0]⟩
      , ⟨[.atom "state", .one], [w "state", lay (col 8), slot .expr 0]⟩
      , ⟨[.atom "type", .one, .one], [w "type", lay (col 8), slot .prim 0, g '≔', slot .expr 1]⟩
      , ⟨[.atom "import", .one, .one], [w "import", lay (col 8), slot .prim 0, slot .prim 1]⟩
      , ⟨[.atom "layer", .one], [w "layer", lay (col 8), slot .prim 0]⟩
      , ⟨[.atom "rel", .one, .list [.atom "key", .rest], .list [.atom "val", .one], .rest],
          [w "rel", lay (col 8), slot .prim 0, g ':', g '{', lay .glue, fields .field 0, lay .glue, g '}', g '↦',
           slot .expr 1, many .relCl 1 {}]⟩
      , ⟨[.atom "method", .one, .rest], [w "method", lay (col 8), slot .prim 0, lay (ind 2), many .clause 0 { lastNl := true }, lay ded]⟩
      , ⟨[.atom "law", .one, .rest],
          [w "law", lay (col 8), slot .prim 0, lay (ind 2), many .arm 0 { vert := true, align := true }, lay ded]⟩
      , ⟨[.atom "guard", .one, .one], [w "guard", lay (col 8), slot .prim 0, g '≔', slot .expr 1]⟩
      , ⟨[.atom "activity", .one, .one, .rest],
          [w "activity", lay (col 8), slot .prim 0, slot .prim 1, lay (ind 2), many .clause 0 { vert := true }, lay ded]⟩
      , ⟨[.atom "claim", .atom "keeps", .one, .one], [w "claim", lay (col 8), slot .prim 0, w "kept", w "by", slot .prim 1]⟩
      , ⟨[.atom "hole", .one, .one, .rest],
          [w "hole", lay (col 8), slot .prim 0, g ':', slot .ctx 1, lay (ind 2), many .hcl 0 { vert := true }, lay ded]⟩
      , ⟨[.atom "imports", .rest], [w "imports", lay (col 8), many .prim 0 { sep := comma, lead := some (.g '['), close := some (.g ']') }]⟩
      , ⟨[.atom "iface", .one], [w "iface", lay (col 8), slot .expr 0]⟩
      , ⟨[.atom "methods", .rest], [w "methods", lay (col 8), many .prim 0 { sep := comma, lead := some (.g '['), close := some (.g ']') }]⟩
      , ⟨[.atom "laws", .rest], [w "laws", lay (col 8), many .prim 0 { sep := comma, lead := some (.g '['), close := some (.g ']') }]⟩
      , ⟨[.atom "rels", .rest],
          [w "rels", lay (col 8), lay (ind 2), many .coreRel 0 { sep := some (.g ','), lead := some (.g '['), close := some (.g ']'), vert := true },
           lay ded]⟩
      , ⟨[.atom "body", .one], [w "body", lay (col 8), slot .expr 0]⟩
      , ⟨[.atom "effects", .rest], [w "effects", lay (col 8), many .effRow 0 { sep := comma, lead := some (.g '['), close := some (.g ']') }]⟩
      , ⟨[.atom "claims", .rest], [w "claims", lay (col 8), many .claimRow 0 { sep := comma, lead := some (.g '['), close := some (.g ']') }]⟩
      , ⟨[.atom "holes", .rest], [w "holes", lay (col 8), lay (ind 2), many .prim 0 { lead := some (.g '['), close := some (.g ']'), vert := true }, lay ded]⟩ ] }
  | .clause => { bare := false, inherit := true, own :=
      [ ⟨[.atom "arg", .one], [g ':', slot .expr 0]⟩
      , ⟨[.atom "edits", .one], [w "edits", slot .prim 0]⟩
      , ⟨[.atom "calls", .list [.one]], [w "calls", slot .prim 0]⟩
      , ⟨[.atom "effect", .list [.atom "moves", .one]], [w "moves", g '≤', slot .prim 0]⟩
      , ⟨[.atom "resumer", .one], [lay nl, w "resumer", slot .expr 0]⟩ ] }
  | .arm => { bare := false, own :=
      [ ⟨[.atom "on", .one, .rest, .one], [w "on", slot .occ 0, many .prim 0 {}, lay tab, g '↦', slot .expr 1]⟩
      , ⟨[.atom "else", .one], [w "else", lay tab, g '↦', slot .expr 0]⟩ ] }
  | .occ => { own := [⟨[.one, .one, .rest], [slot .prim 0, g '∨', slot .prim 1, many .prim 0 { sep := some (.g '∨'), lead := some (.g '∨') }]⟩] }
  | .field => { strict := true, own := [⟨[.one, .one], [slot .prim 0, g ':', slot .expr 1]⟩] }
  | .vfield => { strict := true, own := [⟨[.one, .one], [slot .prim 0, g '≔', slot .expr 1]⟩] }
  | .cArm => { strict := true, own := [⟨[.one, .one, .one], [slot .prim 0, slot .prim 1, lay tab, g '↦', slot .expr 2]⟩] }
  | .cond => { strict := true, own := [⟨[.one, .one], [slot .expr 0, w "else", slot .prim 1]⟩] }
  | .ctx => { own := [⟨[.rest, .atom "⊢", .one], [g '[', lay .glue, many .ctxE 0 { sep := comma }, g '⊢', slot .expr 0, lay .glue, g ']']⟩] }
  | .ctxE => { strict := true, own :=
      [⟨[.one, .one, .rest], [slot .prim 0, g ':', slot .expr 1, many .pin 0 { sep := some (.g '∧'), lead := some (.g '⊣') }]⟩] }
  | .hcl => { bare := false, own :=
      [ ⟨[.atom "select", .one, .one], [w "selected", w "by", slot .prim 0, lay .glue, slot .prim 1]⟩
      , ⟨[.atom "candidate", .one, .rest],
          [g '◇', lay idx, slot .expr 0, lay (col 40), many .pin 0 { sep := some (.g '∧'), lead := some (.g '⊣') }]⟩ ] }
  | .pin => { own :=
      [ ⟨[.atom "cell", .one], [w "live", slot .prim 0]⟩
      , ⟨[.atom "cell", .one, .list [.atom "law", .one]], [slot .prim 0, w "under", slot .prim 1]⟩
      , ⟨[.atom "cell", .one, .list [.atom "runs", .one]], [slot .prim 0, w "runs", slot .prim 1]⟩
      , ⟨[.atom "row", .one, .one, .one], [w "row", slot .prim 0, slot .prim 1, slot .prim 2]⟩ ] }
  | .item => { own :=
      [ ⟨[.atom "upsert", .one, .one, .one], [slot .prim 0, g '←', slot .expr 1, g '↦', slot .expr 2]⟩
      , ⟨[.atom "insert", .one, .one, .one], [slot .prim 0, g '⊕', slot .expr 1, g '↦', slot .expr 2]⟩
      , ⟨[.atom "retract", .one, .one], [slot .prim 0, g '⊖', slot .expr 1]⟩
      , ⟨[.atomIn callKinds, .rest], [slot .prim 0, lay .glue, g '(', lay .glue, fields .vfield 0, lay .glue, g ')']⟩ ] }
  | .relCl => { bare := false, own :=
      [ ⟨[.atom "limit", .one], [w "limit", slot .prim 0]⟩, ⟨[.atom "sum", .one], [w "sum", slot .prim 0]⟩
      , ⟨[.atom "cap", .one], [w "cap", slot .prim 0]⟩, ⟨[.atom "guard", .one], [w "guard", slot .prim 0]⟩
      , ⟨[.atom "holds", .one], [w "holds", slot .prim 0]⟩ ] }
  | .coreRel => { own :=
      [⟨[.one, .list [.atom "key", .rest], .list [.atom "val", .one], .list [.atom "limit", .one], .list [.atom "sum", .rest],
          .list [.atom "cap", .one], .list [.atom "retract", .one], .list [.atom "guard", .rest], .list [.atom "holds", .rest]],
        [slot .prim 0, g ':', g '{', lay .glue, fields .field 0, lay .glue, g '}', g '↦', slot .expr 1, w "limit", slot .prim 2,
         many .prim 1 { sep := comma, lead := some (.w "sum") }, w "cap", slot .prim 3, w "retract", slot .prim 4,
         many .prim 2 { sep := comma, lead := some (.w "guard") }, many .prim 3 { sep := comma, lead := some (.w "holds") }]⟩] }
  | .effRow => { own :=
      [⟨[.one, .one, .rest], [slot .prim 0, w "moves", g '≤', slot .prim 1, many .expr 0 { lead := some (.w "produces") }]⟩] }
  | .claimRow => { own := [⟨[.atom "keeps", .one, .one], [slot .prim 0, w "kept", w "by", slot .prim 1]⟩] }

end table

/-- The templates of a kind: its own, then the expression templates if it takes them. -/
def tmpls (c : Cls) : List Tmpl := (spec c).own ++ (if (spec c).inherit then (spec .expr).own else [])

/-! ## Matching a form against a template -/

/-- What a match binds: the `one`s (and `atomIn`s) and the `rest`s, in order. -/
structure Env where
  ones : List SExp := []
  rests : List (List SExp) := []
  deriving Inhabited

mutual
def matchS : Src → SExp → Env → Option Env
  | .atom s, .atom _ a, e => if a = s then some e else none
  | .atomIn ss, x@(.atom _ a), e => if ss.contains a then some { e with ones := e.ones ++ [x] } else none
  | .one, x, e => some { e with ones := e.ones ++ [x] }
  | .list ps, .list _ xs, e => matchL ps xs e
  | _, _, _ => none

/-- A `rest` takes every element but those the patterns after it need, one each. -/
def matchL : List Src → List SExp → Env → Option Env
  | [], [], e => some e
  | .rest :: ps, xs, e =>
    if ps.length ≤ xs.length then
      matchL ps (xs.drop (xs.length - ps.length)) { e with rests := e.rests ++ [xs.take (xs.length - ps.length)] }
    else none
  | p :: ps, x :: xs, e => (matchS p x e).bind (matchL ps xs)
  | _, _, _ => none
end

/-- A form rebuilt from a template's pattern and what it bound (offsets 0). -/
mutual
def buildS : Src → List SExp → List (List SExp) → Option (SExp × List SExp × List (List SExp))
  | .atom s, os, rs => some (.atom 0 s, os, rs)
  | .atomIn _, o :: os, rs => some (o, os, rs)
  | .one, o :: os, rs => some (o, os, rs)
  | .list ps, os, rs => (buildL ps os rs).map fun (xs, os, rs) => (.list 0 xs, os, rs)
  | _, _, _ => none

def buildL : List Src → List SExp → List (List SExp) → Option (List SExp × List SExp × List (List SExp))
  | [], os, rs => some ([], os, rs)
  | .rest :: ps, os, r :: rs => (buildL ps os rs).map fun (xs, os, rs) => (r ++ xs, os, rs)
  | p :: ps, os, rs => do
    let (x, os, rs) ← buildS p os rs
    let (xs, os, rs) ← buildL ps os rs
    pure (x :: xs, os, rs)
end

/-- The first non-layout pieces. -/
def stripLay : List Pc → List Pc
  | .lay _ :: ps => stripLay ps
  | ps => ps

/-- A template's first token, if it starts with one. -/
def Tmpl.lead (t : Tmpl) : Option Lx :=
  match stripLay t.out with
  | .lit l :: _ => some l
  | _ => none

/-- An infix template's operator: the token after its first element. -/
def Tmpl.op (t : Tmpl) : Option Lx :=
  match stripLay t.out with
  | .slot .prim _ :: rest => match stripLay rest with
    | .lit l :: _ => some l
    | _ => none
  | _ => none

/-- A template that ends with a token or an atom-like element: nothing after it can be read as its own. -/
def Tmpl.closed (t : Tmpl) : Bool :=
  t.lead.isSome &&
    match (stripLay t.out.reverse) with
    | .lit _ :: _ | .slot .prim _ :: _ => true
    | _ => false

/-- Expression templates that may stand where an atom stands, unparenthesised. -/
def closedT : List Tmpl := (spec .expr).own.filter Tmpl.closed

def leadOf (c : Cls) (l : Lx) : Option Tmpl := (tmpls c).find? (·.lead = some l)
def opOf (c : Cls) (l : Lx) : Option Tmpl := (tmpls c).find? (·.op = some l)
def closedLead (l : Lx) : Option Tmpl := closedT.find? (·.lead = some l)

/-- The single template of a strict kind. -/
def strictT (c : Cls) : Option Tmpl := (spec c).own.head?

/-! ## Escaping -/

def structural : List Lx := [.g '(', .g ')', .g '‹', .g '›']

/-- Words that must never stand as an unescaped atom, besides the leads and operators: a word that
follows a list a parser decides on (`check c else "r", … then e`). -/
def reserved : List Lx := [.w "then", .w "else", .g '↦', .g '⊢', .g ':', .g '≔', .g ',', .g ']', .g '}', .g '⟩']

/-- The tokens an atom never prints as unescaped: what a parser reads as structure at a place an atom
may stand. -/
def esc : List Lx :=
  structural ++ reserved ++
    (allCls.filter fun c => (spec c).bare && !(spec c).strict).flatMap (fun c => (tmpls c).filterMap (·.lead)) ++
    (allCls.filter fun c => !(spec c).strict).flatMap (fun c => (tmpls c).filterMap (·.op))

/-- An atom that may print as its own token at the start of an item of a `bare` kind. -/
def plainLx (l : Lx) : Bool := !l.isQuote && !esc.contains l

/-! ## Printing: forms to tokens -/

/-- A printed token, or layout. `pos` is the source offset of the atom, string or form it came from. -/
inductive Tk
  | lx (l : Lx) (pos : Nat)
  | lay (x : Lay)
  | deco (s : String)
  deriving Repr, Inhabited

def subscript (n : Nat) : String :=
  String.ofList ((Nat.toDigits 10 n).map fun d => Char.ofNat ('₀'.toNat + (d.toNat - '0'.toNat)))

def printAtom (bare : Bool) (a : String) (p : Nat) : List Tk :=
  let l := atomLex a
  if bare && plainLx l then [.lx l p] else [.lx (.g '‹') p, .lay .glue, .lx l p, .lay .glue, .lx (.g '›') p]

mutual
/-- Is `x` a form of this template, with every element a strict kind needs of that kind's shape? -/
def fitsT : Nat → Tmpl → SExp → Option Env
  | 0, _, _ => none
  | F + 1, t, .list _ xs =>
    (matchL t.src xs {}).bind fun e => if fitsPieces F t.out e then some e else none
  | _ + 1, _, _ => none

def fitsPieces : Nat → List Pc → Env → Bool
  | 0, _, _ => false
  | F + 1, ps, e => ps.all fun
    | .slot c i => !(spec c).strict || (match strictT c, e.ones[i]? with
      | some t, some x => (fitsT F t x).isSome
      | _, _ => false)
    | .many c j _ => !(spec c).strict || (match strictT c, e.rests[j]? with
      | some t, some xs => xs.all fun x => (fitsT F t x).isSome
      | _, _ => false)
    | _ => true
end

def firstMatch (F : Nat) (ts : List Tmpl) (x : SExp) : Option (Tmpl × Env) :=
  ts.findSome? fun t => (fitsT F t x).map (t, ·)

mutual
/-- `x` printed as kind `c`; `ord` numbers it among its many's items (a candidate's index). -/
def printC : Nat → Cls → Nat → SExp → List Tk
  | 0, _, _, _ => []
  | F + 1, c, ord, x =>
    if c = .prim then printP F true x else
    match firstMatch F (tmpls c) x with
    | some (t, e) => printPieces F (spec c).bare ord x.pos t.out e
    | none => printP F (spec c).bare x

/-- `x` where an atom may stand: an atom, a string, a closed template, a parenthesised template, or
the form itself in parentheses. `bare`: an atom may print unescaped. -/
def printP : Nat → Bool → SExp → List Tk
  | 0, _, _ => []
  | _ + 1, bare, .atom p a => printAtom bare a p
  | _ + 1, _, .str p s => [.lx (.q s) p]
  | F + 1, bare, x@(.list p xs) =>
    match firstMatch F (spec .expr).own x with
    | some (t, e) =>
      if t.closed then printPieces F bare 0 p t.out e
      else [.lx (.g '(') p, .lay .glue] ++ printPieces F true 0 p t.out e ++ [.lay .glue, .lx (.g ')') p]
    | none => [.lx (.g '(') p, .lay .glue] ++ printItems F xs ++ [.lay .glue, .lx (.g ')') p]

def printItems : Nat → List SExp → List Tk
  | 0, _ => []
  | F + 1, xs => xs.flatMap (printP F true)

/-- A template's pieces. The first element prints with the kind's `bare`; the rest bare. -/
def printPieces : Nat → Bool → Nat → Nat → List Pc → Env → List Tk
  | 0, _, _, _, _, _ => []
  | F + 1, bare, ord, p, ps, e =>
    let firstSlot := (stripLay ps).head?
    ps.flatMap fun pc => match pc with
      | .lit l => [.lx l p]
      | .slot c i =>
        let x := e.ones.getD i default
        if c = .prim then printP F (bare || firstSlot != some pc) x else printC F c 0 x
      | .many c j m => printMany F c m p (e.rests.getD j [])
      | .lay .idx => [.deco (subscript ord)]
      | .lay x => [.lay x]

def printMany : Nat → Cls → Many → Nat → List SExp → List Tk
  | 0, _, _, _, _ => []
  | F + 1, c, m, p, xs =>
    if xs.isEmpty then [] else
    let n := xs.length
    let items := xs.zipIdx.map fun (x, k) =>
      (if m.vert || (m.lastNl && k + 1 = n) then [.lay .nl] else []) ++
        printC F c k x ++
        (if k + 1 < n then (match m.sep with | some s => [.lay .glue, .lx s p] | none => []) else [])
    (match m.lead with | some l => [.lx l p] ++ (if m.vert then [] else [.lay .glue]) | none => []) ++
      items.flatten ++
      (match m.close with | some l => [.lay .glue, .lx l p] | none => [])
end

/-- The tokens of a printing, without layout. -/
def lexemes (ts : List Tk) : List Lx := ts.filterMap fun | .lx l _ => some l | _ => none

/-! ## Layout: tokens to text, with a position map -/

/-- One printed token with what precedes it (whitespace and decorations only) and where it came from. -/
structure Cell where
  pre : List Char
  lx : Lx
  pos : Nat
  deriving Inhabited

/-- The width terms are broken at. -/
def width : Nat := 100

structure LState where
  col : Nat := 0
  ind : List Nat := [0]
  /-- what separates the next token: `none` nothing, `some s` that text -/
  pend : Option (List Char) := none
  deco : List Char := []
  /-- after a `glue`: no space before the next token -/
  glued : Bool := true
  nl : Bool := false
  colTo : Option Nat := none
  lastWord : Bool := false
  cells : List Cell := []
  deriving Inhabited

def LState.cur (s : LState) : Nat := s.ind.headD 0

def spaces (n : Nat) : List Char := List.replicate n ' '

/-- What goes before a token at this state: a line break, padding to a column, a space, or nothing;
then the decorations. A word after a word always gets a space. -/
def sepFor (s : LState) (l : Lx) : List Char :=
  let base :=
    if s.nl then '\n' :: spaces s.cur
    else match s.colTo with
      | some n => if s.col < s.cur + n then spaces (s.cur + n - s.col) else [' ']
      | none => if s.glued || s.cells.isEmpty then [] else [' ']
  let wrap :=
    if !s.nl && s.colTo.isNone && !s.glued && !s.cells.isEmpty && s.col + 1 + l.chars.length > width && s.col > s.cur + 4
    then '\n' :: spaces (s.cur + 4) else base
  let pre := wrap ++ s.deco
  match l with
  | .w _ => if s.lastWord && pre.isEmpty then [' '] else pre
  | _ => pre

def colAfter (col : Nat) : List Char → Nat
  | [] => col
  | c :: cs => if c = '\n' then colAfter 0 cs else colAfter (col + 1) cs

def layStep (s : LState) : Tk → LState
  | .lx l p =>
    let pre := sepFor s l
    let col := colAfter s.col (pre ++ l.chars)
    { s with col, pend := none, deco := [], glued := false, nl := false, colTo := none,
             lastWord := (match l with | .w _ => true | _ => false), cells := ⟨pre, l, p⟩ :: s.cells }
  | .deco d => { s with deco := s.deco ++ d.toList }
  | .lay .nl => { s with nl := true }
  | .lay .glue => { s with glued := true }
  | .lay (.ind n) => { s with ind := (s.cur + n) :: s.ind }
  | .lay .ded => { s with ind := s.ind.tail }
  | .lay (.col n) => { s with colTo := some n }
  | .lay .tab => s
  | .lay .idx => s

/-- Tokens laid out as cells, in order. -/
def layout (ts : List Tk) : List Cell := (ts.foldl layStep {}).cells.reverse

def cellsText (cs : List Cell) : List Char := cs.flatMap fun c => c.pre ++ c.lx.chars

/-- The position map: each cell's character range in the text and its source offset. -/
def posMap (cs : List Cell) : List (Nat × Nat × Nat) :=
  (cs.foldl (fun (acc : Nat × List (Nat × Nat × Nat)) c =>
    let start := acc.1 + c.pre.length
    let stop := start + c.lx.chars.length
    (stop, (start, stop, c.pos) :: acc.2)) (0, [])).2.reverse

/-! ## Reading a printed text back -/

/-- Text to tokens: whitespace and decorations are skipped; `"…"` and `“…”` are strings; a symbol is a
token; anything else runs to the end of a word. -/
def lexAux : Nat → List Char → List Lx
  | 0, _ => []
  | _ + 1, [] => []
  | n + 1, c :: cs =>
    if c.isWhitespace || isDeco c then lexAux n cs
    else if c = '"' then .q (String.ofList (cs.takeWhile (· ≠ '"'))) :: lexAux n ((cs.dropWhile (· ≠ '"')).drop 1)
    else if c = '“' then .q (String.ofList (cs.takeWhile (· ≠ '”'))) :: lexAux n ((cs.dropWhile (· ≠ '”')).drop 1)
    else if isSym c then .g c :: lexAux n cs
    else .w (String.ofList (c :: cs.takeWhile wordChar)) :: lexAux n (cs.dropWhile wordChar)

def lex (cs : List Char) : List Lx := lexAux (cs.length + 1) cs

/-- A parse in progress: what each `one` and `rest` of a template has been read as. -/
structure PEnv where
  ones : List (Option SExp)
  rests : List (Option (List SExp))
  deriving Inhabited

mutual
def countOnes : List Src → Nat
  | [] => 0
  | .one :: ps | .atomIn _ :: ps => countOnes ps + 1
  | .list qs :: ps => countOnes qs + countOnes ps
  | _ :: ps => countOnes ps
end

mutual
def countRests : List Src → Nat
  | [] => 0
  | .rest :: ps => countRests ps + 1
  | .list qs :: ps => countRests qs + countRests ps
  | _ :: ps => countRests ps
end

def PEnv.init (t : Tmpl) : PEnv := ⟨List.replicate (countOnes t.src) none, List.replicate (countRests t.src) none⟩

/-- The form a finished parse of `t` makes. -/
def finish (t : Tmpl) (e : PEnv) : Option SExp := do
  let os ← e.ones.mapM id
  let rs ← e.rests.mapM id
  let (xs, _, _) ← buildL t.src os rs
  pure (.list 0 xs)

/-- Can `l` start an item of kind `c`? -/
def firstC (c : Cls) (l : Lx) : Bool :=
  if c = .prim then l = .g '(' || l = .g '‹' || l.isQuote || (closedLead l).isSome || plainLx l
  else if (spec c).strict then
    match strictT c with
    | some t => match stripLay t.out with
      | .lit l' :: _ => l = l'
      | .slot c' _ :: _ =>
        -- a strict kind starts like the kind of its first element
        if c' = .prim then l = .g '(' || l = .g '‹' || l.isQuote || (closedLead l).isSome || plainLx l
        else (leadOf c' l).isSome || l = .g '(' || l = .g '‹' || l.isQuote || (closedLead l).isSome ||
          ((spec c').bare && plainLx l)
      | _ => false
    | none => false
  else (leadOf c l).isSome || l = .g '(' || l = .g '‹' || l.isQuote || (closedLead l).isSome || ((spec c).bare && plainLx l)

mutual
def parseC : Nat → Cls → List Lx → Option (SExp × List Lx)
  | 0, _, _ => none
  | F + 1, c, ls =>
    if c = .prim then parseP F ls
    else if (spec c).strict then
      match strictT c with
      | some t => (parsePieces F t.out (.init t) ls).bind fun (e, r) => (finish t e).map (·, r)
      | none => none
    else match ls with
      | l :: _ => match leadOf c l with
        | some t => (parsePieces F t.out (.init t) ls).bind fun (e, r) => (finish t e).map (·, r)
        | none => (parseP F ls).bind fun (x, r) => parseInfix F c x r
      | [] => none

/-- After an item's first element `x`: an operator of kind `c` continues it, anything else ends it. -/
def parseInfix : Nat → Cls → SExp → List Lx → Option (SExp × List Lx)
  | 0, _, _, _ => none
  | F + 1, c, x, r =>
    match r with
    | o :: _ => match opOf c o with
      | some t => match stripLay t.out with
        | .slot .prim i :: rest =>
          let e := PEnv.init t
          (parsePieces F rest { e with ones := e.ones.set i (some x) } r).bind fun (e, r) => (finish t e).map (·, r)
        | _ => none
      | none => some (x, r)
    | [] => some (x, [])

def parseP : Nat → List Lx → Option (SExp × List Lx)
  | 0, _ => none
  | F + 1, ls =>
    match ls with
    | .g '(' :: r => parseParen F r
    | .g '‹' :: l :: .g '›' :: r => some (.atom 0 (unlex l), r)
    | .q s :: r => some (.str 0 s, r)
    | l :: r => match closedLead l with
      | some t => (parsePieces F t.out (.init t) ls).bind fun (e, r) => (finish t e).map (·, r)
      | none => some (.atom 0 (unlex l), r)
    | [] => none

/-- After `(`: a parenthesised template, or a form's elements up to `)`. -/
def parseParen : Nat → List Lx → Option (SExp × List Lx)
  | 0, _ => none
  | F + 1, ls =>
    match ls with
    | .g ')' :: r => some (.list 0 [], r)
    | l :: _ =>
      if (leadOf .expr l).isSome && (closedLead l).isNone then
        (parseC F .expr ls).bind fun (x, r) => match r with
          | .g ')' :: r => some (x, r)
          | _ => none
      else (parseP F ls).bind fun (x, r) => match r with
        | o :: _ =>
          if (opOf .expr o).isSome then
            (parseInfix F .expr x r).bind fun (y, r) => match r with
              | .g ')' :: r => some (y, r)
              | _ => none
          else parseItems F [x] r
        | [] => none
    | [] => none

def parseItems : Nat → List SExp → List Lx → Option (SExp × List Lx)
  | 0, _, _ => none
  | F + 1, acc, ls =>
    match ls with
    | .g ')' :: r => some (.list 0 acc.reverse, r)
    | _ => (parseP F ls).bind fun (x, r) => parseItems F (x :: acc) r

def parsePieces : Nat → List Pc → PEnv → List Lx → Option (PEnv × List Lx)
  | 0, _, _, _ => none
  | _ + 1, [], e, ls => some (e, ls)
  | F + 1, .lay _ :: ps, e, ls => parsePieces F ps e ls
  | F + 1, .lit l :: ps, e, ls => match ls with
    | l' :: r => if l' = l then parsePieces F ps e r else none
    | [] => none
  | F + 1, .slot c i :: ps, e, ls =>
    (parseC F c ls).bind fun (x, r) => parsePieces F ps { e with ones := e.ones.set i (some x) } r
  | F + 1, .many c j m :: ps, e, ls =>
    (parseMany F c m ls).bind fun (xs, r) => parsePieces F ps { e with rests := e.rests.set j (some xs) } r

def parseMany : Nat → Cls → Many → List Lx → Option (List SExp × List Lx)
  | 0, _, _, _ => none
  | F + 1, c, m, ls =>
    let closeBy (r : List Lx) (xs : List SExp) : Option (List SExp × List Lx) :=
      match m.close with
      | some cl => match r with
        | l :: r => if l = cl then some (xs, r) else none
        | [] => none
      | none => some (xs, r)
    match m.lead, ls with
    | some ld, l :: r => if l = ld then (parseSome F c m.sep r).bind fun (xs, r) => closeBy r xs else some ([], ls)
    | some _, [] => some ([], [])
    | none, l :: _ => if firstC c l then (parseSome F c m.sep ls).bind fun (xs, r) => closeBy r xs else some ([], ls)
    | none, [] => some ([], [])

def parseSome : Nat → Cls → Option Lx → List Lx → Option (List SExp × List Lx)
  | 0, _, _, _ => none
  | F + 1, c, sep, ls =>
    (parseC F c ls).bind fun (x, r) =>
      match sep, r with
      | some s, l :: r' => if l = s then (parseSome F c sep r').map fun (xs, r'') => (x :: xs, r'') else some ([x], r)
      | none, l :: _ => if firstC c l then (parseSome F c sep r).map fun (xs, r') => (x :: xs, r') else some ([x], r)
      | _, [] => some ([x], [])
end

/-! ## The entry points -/

/-- The nodes of a form: a bound on the tokens and the fuel it needs. -/
mutual
def size : SExp → Nat
  | .atom _ _ | .str _ _ => 1
  | .list _ xs => 1 + sizes xs

def sizes : List SExp → Nat
  | [] => 0
  | x :: xs => size x + sizes xs
end

structure Printed where
  text : String
  /-- (start, end, source offset) of each printed token, in characters -/
  map : List (Nat × Nat × Nat)

def fuelOf (x : SExp) : Nat := 8 * size x + 8

/-- A text's tree, printed with glyphs. -/
def pretty (x : SExp) : Printed :=
  let cs := layout (printC (fuelOf x) .top 0 x)
  ⟨String.ofList (cellsText cs), posMap cs⟩

/-- A printed text read back to its tree: tokens, then the templates. -/
def unglyph (s : String) : Option SExp :=
  let ls := lex s.toList
  match parseC (8 * ls.length + 8) .top ls with
  | some (x, []) => some x
  | _ => none


end Nanodregg.Lang.Pretty
