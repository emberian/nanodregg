/-
# Lang.Read — the core in s-expressions, with names: what a Hermes resident writes

Not admission: a resident (or its client) reads text into a `Package`, checks it with the same
`Package.checkWith` the receiver runs, and installs the bytes. The surface is the core with names
(resolved to de Bruijn indices here) and three conveniences: application of many arguments
`(f a b)`, `(let x T e body)` = `((lam x T body) e)`, and `(fn (x T) (y U) body)` = nested `lam`.

    type  ::= nat | bool | bytes | (-> T U) | (rec (l T)…) | (sum (l T)…)
    term  ::= x | 123 | true | false | "text" | (lam x T e) | (fn (x T)… e) | (let x T e e)
            | (fix e) | (OP e e) with OP ∈ + - * / % == < <= beq cat
            | (record (l e)…) | (. e l) | (extend e (l e)…) | (inj T l e)
            | (case e (l x e)…) | (if e e e) | (ref i) | (e e…)
    package ::= (package (imports "hex"…) (state T) (iface T) (methods l…) (laws l…) (body e))

Fields and arms may be written in any order: they are sorted into the canonical (ascending) order.
Every recursion is bounded by `depthMax`. A refusal is a `ReadRefusal`: a named constructor with
the character offset of the form it is about (law 7), never prose.
-/
import Lang.Package
import Lang.Data

namespace Nanodregg.Lang.Read

/-- An s-expression; every node carries the character offset where it starts. -/
inductive SExp
  | atom (pos : Nat) (s : String)
  | str (pos : Nat) (s : String)
  | list (pos : Nat) (xs : List SExp)
  deriving Inhabited

def SExp.pos : SExp → Nat
  | .atom p _ | .str p _ | .list p _ => p

def depthMax : Nat := 512

/-- Why the reader refuses, by name, at a character offset. -/
inductive ReadRefusal
  /-- forms nested (or a list longer) than `depthMax` -/
  | tooDeep (pos : Nat)
  /-- the text ended where a form was expected -/
  | unexpectedEnd (pos : Nat)
  /-- a `)` with no `(` -/
  | stray (pos : Nat)
  | unterminatedString (pos : Nat)
  /-- a `(` never closed -/
  | unclosed (pos : Nat)
  /-- text after the one form -/
  | trailing (pos : Nat)
  | notAType (pos : Nat)
  /-- a row entry is `(label type)`, a field `(label term)`, an arm `(label name term)` -/
  | badEntry (pos : Nat)
  | unbound (pos : Nat) (name : String)
  /-- `(ref i)` with `i` not a numeral -/
  | badRef (pos : Nat)
  | emptyApplication (pos : Nat)
  /-- `fn` takes `(name type)…` and a body -/
  | badBinder (pos : Nat)
  /-- an import is a hex digest string -/
  | badImport (pos : Nat)
  /-- `methods` and `laws` list labels -/
  | badLabel (pos : Nat)
  /-- not `(package (imports …) (state T) (iface T) (methods …) (laws …) (body e))` -/
  | notPackage (pos : Nat)
  /-- a data literal that is not a value of the type it is read at (or out of the data bounds) -/
  | notOfType (pos : Nat)
  deriving DecidableEq, Repr

/-- The refusal's name on the wire (law 7). -/
def ReadRefusal.name : ReadRefusal → String
  | .tooDeep _ => "tooDeep" | .unexpectedEnd _ => "unexpectedEnd" | .stray _ => "stray"
  | .unterminatedString _ => "unterminatedString" | .unclosed _ => "unclosed"
  | .trailing _ => "trailing" | .notAType _ => "notAType" | .badEntry _ => "badEntry"
  | .unbound _ _ => "unbound" | .badRef _ => "badRef" | .emptyApplication _ => "emptyApplication"
  | .badBinder _ => "badBinder" | .badImport _ => "badImport" | .badLabel _ => "badLabel"
  | .notPackage _ => "notPackage" | .notOfType _ => "notOfType"

def ReadRefusal.pos : ReadRefusal → Nat
  | .tooDeep p | .unexpectedEnd p | .stray p | .unterminatedString p | .unclosed p | .trailing p
  | .notAType p | .badEntry p | .unbound p _ | .badRef p | .emptyApplication p | .badBinder p
  | .badImport p | .badLabel p | .notPackage p | .notOfType p => p

/-- `name @offset`, plus the unbound name: what a resident reads. -/
def ReadRefusal.text (e : ReadRefusal) : String :=
  match e with
  | .unbound p x => s!"unbound @{p} {x}"
  | e => s!"{e.name} @{e.pos}"

abbrev P (α : Type) := Except ReadRefusal α

/-! ## Reading text (the offset of the head of the remaining characters is carried) -/

def isDelim (c : Char) : Bool := c = '(' || c = ')' || c = '"' || c.isWhitespace || c = ';'

mutual
/-- Skip whitespace and `;` comments to end of line. -/
def skip : Nat → List Char → Nat × List Char
  | p, [] => (p, [])
  | p, c :: cs => if c.isWhitespace then skip (p + 1) cs else if c = ';' then skipLine (p + 1) cs else (p, c :: cs)

def skipLine : Nat → List Char → Nat × List Char
  | p, [] => (p, [])
  | p, c :: cs => if c = '\n' then skip (p + 1) cs else skipLine (p + 1) cs
end

mutual
def sexp : Nat → Nat → List Char → P (SExp × Nat × List Char)
  | 0, p, _ => .error (.tooDeep p)
  | d + 1, p, cs =>
    match skip p cs with
    | (p, []) => .error (.unexpectedEnd p)
    | (p, '(' :: rest) =>
      let (q, rest) := skip (p + 1) rest
      (sexps d p q rest []).map fun (xs, r) => (.list p xs, r)
    | (p, ')' :: _) => .error (.stray p)
    | (p, '"' :: rest) =>
      let body := rest.takeWhile (· ≠ '"')
      match rest.dropWhile (· ≠ '"') with
      | '"' :: r => .ok (.str p (String.ofList body), p + body.length + 2, r)
      | _ => .error (.unterminatedString p)
    | (p, cs') =>
      let a := cs'.takeWhile (fun c => !isDelim c)
      .ok (.atom p (String.ofList a), p + a.length, cs'.dropWhile (fun c => !isDelim c))

/-- The rest of a list opened at `open`, from offset `p`. -/
def sexps : Nat → Nat → Nat → List Char → List SExp → P (List SExp × Nat × List Char)
  | 0, _, p, _, _ => .error (.tooDeep p)
  | d + 1, o, p, cs, acc =>
    match skip p cs with
    | (p, ')' :: rest) => .ok (acc.reverse, p + 1, rest)
    | (_, []) => .error (.unclosed o)
    | (p, cs') =>
      match sexp d p cs' with
      | .ok (x, q, r) => sexps d o q r (x :: acc)
      | .error e => .error e
end

def parse (text : String) : P SExp :=
  match sexp depthMax 0 text.toList with
  | .ok (x, p, rest) =>
    match skip p rest with
    | (_, []) => .ok x
    | (q, _) => .error (.trailing q)
  | .error e => .error e

/-! ## Elaboration to the core -/

def sortRow {α : Type} (r : List (Label × α)) : List (Label × α) :=
  r.mergeSort fun a b => decide (a.1 ≤ b.1)

def primOf : String → Option Prim
  | "+" => some .add | "-" => some .sub | "*" => some .mul | "/" => some .div | "%" => some .mod
  | "==" => some .eq | "<" => some .lt | "<=" => some .le | "beq" => some .beq | "cat" => some .cat
  | _ => none

mutual
def ty : Nat → SExp → P Ty
  | 0, x => .error (.tooDeep x.pos)
  | _ + 1, .atom _ "nat" => .ok .nat
  | _ + 1, .atom _ "bool" => .ok .bool
  | _ + 1, .atom _ "bytes" => .ok .bytes
  | d + 1, .list _ [.atom _ "->", a, b] => do pure (.fn (← ty d a) (← ty d b))
  | d + 1, .list _ (.atom _ "rec" :: fs) => do pure (.record (sortRow (← tyRow d fs)))
  | d + 1, .list _ (.atom _ "sum" :: fs) => do pure (.sum (sortRow (← tyRow d fs)))
  | _ + 1, x => .error (.notAType x.pos)

def tyRow : Nat → List SExp → P (List (Label × Ty))
  | _, [] => .ok []
  | 0, x :: _ => .error (.tooDeep x.pos)
  | d + 1, .list _ [.atom _ ℓ, t] :: rest => do pure ((ℓ, ← ty d t) :: (← tyRow d rest))
  | _ + 1, x :: _ => .error (.badEntry x.pos)
end

def indexOf (x : String) : List String → Option Nat
  | [] => none
  | y :: ys => if x = y then some 0 else (indexOf x ys).map (· + 1)

def appAll (f : Term) : List Term → Term
  | [] => f
  | a :: as => appAll (.app f a) as

mutual
def term : Nat → List String → SExp → P Term
  | 0, _, x => .error (.tooDeep x.pos)
  | _ + 1, _, .atom _ "true" => .ok (.bool true)
  | _ + 1, _, .atom _ "false" => .ok (.bool false)
  | _ + 1, sc, .atom p a =>
    match a.toNat? with
    | some n => .ok (.nat n)
    | none =>
      match indexOf a sc with
      | some i => .ok (.var i)
      | none => .error (.unbound p a)
  | _ + 1, _, .str _ s => .ok (.bytes s.toUTF8)
  | d + 1, sc, .list _ [.atom _ "lam", .atom _ x, t, b] => do
    pure (.lam (← ty d t) (← term d (x :: sc) b))
  | d + 1, sc, .list _ (.atom _ "fn" :: rest) => fnBinders d sc rest
  | d + 1, sc, .list _ [.atom _ "let", .atom _ x, t, e, b] => do
    pure (.app (.lam (← ty d t) (← term d (x :: sc) b)) (← term d sc e))
  | d + 1, sc, .list _ [.atom _ "fix", e] => do pure (.fix (← term d sc e))
  | d + 1, sc, .list _ [.atom _ ".", e, .atom _ ℓ] => do pure (.get (← term d sc e) ℓ)
  | d + 1, sc, .list _ (.atom _ "record" :: fs) => do pure (.record (sortRow (← fields d sc fs)))
  | d + 1, sc, .list _ (.atom _ "extend" :: e :: fs) => do
    pure (.extend (← term d sc e) (sortRow (← fields d sc fs)))
  | d + 1, sc, .list _ [.atom _ "inj", t, .atom _ ℓ, e] => do pure (.inj (← ty d t) ℓ (← term d sc e))
  | d + 1, sc, .list _ (.atom _ "case" :: e :: arms) => do
    pure (.case (← term d sc e) (sortRow (← armsOf d sc arms)))
  | d + 1, sc, .list _ [.atom _ "if", c, a, b] => do
    pure (.ite (← term d sc c) (← term d sc a) (← term d sc b))
  | _ + 1, _, .list p [.atom _ "ref", .atom _ i] =>
    match i.toNat? with
    | some n => .ok (.ref n)
    | none => .error (.badRef p)
  | d + 1, sc, .list _ [.atom q op, a, b] =>
    match primOf op with
    | some p => do pure (.prim p (← term d sc a) (← term d sc b))
    | none => do pure (appAll (← term d sc (.atom q op)) [← term d sc a, ← term d sc b])
  | d + 1, sc, .list _ (f :: args) => do pure (appAll (← term d sc f) (← termList d sc args))
  | _ + 1, _, .list p [] => .error (.emptyApplication p)

def termList : Nat → List String → List SExp → P (List Term)
  | _, _, [] => .ok []
  | 0, _, x :: _ => .error (.tooDeep x.pos)
  | d + 1, sc, e :: es => do pure ((← term d sc e) :: (← termList d sc es))

def fields : Nat → List String → List SExp → P (List (Label × Term))
  | _, _, [] => .ok []
  | 0, _, x :: _ => .error (.tooDeep x.pos)
  | d + 1, sc, .list _ [.atom _ ℓ, e] :: rest => do pure ((ℓ, ← term d sc e) :: (← fields d sc rest))
  | _ + 1, _, x :: _ => .error (.badEntry x.pos)

def armsOf : Nat → List String → List SExp → P (List (Label × Term))
  | _, _, [] => .ok []
  | 0, _, x :: _ => .error (.tooDeep x.pos)
  | d + 1, sc, .list _ [.atom _ ℓ, .atom _ x, e] :: rest => do
    pure ((ℓ, ← term d (x :: sc) e) :: (← armsOf d sc rest))
  | _ + 1, _, x :: _ => .error (.badEntry x.pos)

def fnBinders : Nat → List String → List SExp → P Term
  | 0, _, _ => .error (.tooDeep 0)
  | d + 1, sc, [b] => term d sc b
  | d + 1, sc, .list _ [.atom _ x, t] :: rest => do pure (.lam (← ty d t) (← fnBinders d (x :: sc) rest))
  | _ + 1, _, x :: _ => .error (.badBinder x.pos)
  | _ + 1, _, [] => .error (.badBinder 0)
end

def hexVal (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10) else none

def unhex (acc : ByteArray) : List Char → Option ByteArray
  | [] => some acc
  | a :: b :: rest => do unhex (acc.push (UInt8.ofNat ((← hexVal a) * 16 + (← hexVal b)))) rest
  | _ => none

def labels : List SExp → P (List Label)
  | [] => .ok []
  | .atom _ ℓ :: rest => do pure (ℓ :: (← labels rest))
  | x :: _ => .error (.badLabel x.pos)

def package (x : SExp) : P Package :=
  match x with
  | .list _ [.atom _ "package", .list _ (.atom _ "imports" :: is), .list _ [.atom _ "state", s],
      .list _ [.atom _ "iface", i], .list _ (.atom _ "methods" :: ms), .list _ (.atom _ "laws" :: ls),
      .list _ [.atom _ "body", b]] => do
    let imports ← is.mapM fun
      | .str p h => match unhex ByteArray.empty h.toList with
        | some bs => .ok bs
        | none => .error (.badImport p)
      | y => .error (.badImport y.pos)
    pure { imports, state := ← ty depthMax s, iface := ← ty depthMax i, body := ← term depthMax [] b,
           methods := ← labels ms, laws := ← labels ls }
  | y => .error (.notPackage y.pos)

/-! ## Data literals at a known type

What a resident writes for an object's seed state or a method's arguments: `123`, `true`/`false`,
`"text"`, `(record (l v)…)` (fields in any order, exactly the type's), and for a sum `(l v)` or a
bare `l` for an arm whose payload is the empty record. The type directs the reading, so a literal
needs no annotation, and only a value of the type is accepted (`Lang.Proofs.Read.dataAt_conforms`):
a natural below `Bounds.natLimit`, a byte string of at most `Bounds.bytesMax`. -/

/-- A scalar literal at a scalar type. -/
def scalarAt : Ty → SExp → P Data
  | .nat, x@(.atom p a) =>
    match a.toNat? with
    | some n => if n < Bounds.natLimit then .ok (.nat n) else .error (.notOfType p)
    | none => .error (.notOfType x.pos)
  | .bool, x@(.atom _ a) =>
    if a = "true" then .ok (.bool true) else if a = "false" then .ok (.bool false)
    else .error (.notOfType x.pos)
  | .bytes, .str p s =>
    if s.toUTF8.size ≤ Bounds.bytesMax then .ok (.bytes s.toUTF8) else .error (.notOfType p)
  | _, x => .error (.notOfType x.pos)

/-- The fields of a record literal, unread: `(label value)…`. -/
def dataFields : List SExp → P (List (Label × SExp))
  | [] => .ok []
  | .list _ [.atom _ ℓ, v] :: rest => do pure ((ℓ, v) :: (← dataFields rest))
  | x :: _ => .error (.badEntry x.pos)

mutual
def dataAt : Nat → Ty → SExp → P Data
  | 0, _, x => .error (.tooDeep x.pos)
  | d + 1, T, x =>
    match T, x with
    | .record row, .list p (.atom _ "record" :: fs) => do
      pure (.record (← dataRow d p row (sortRow (← dataFields fs))))
    | .sum row, .list p [.atom _ ℓ, v] =>
      match Row.find? ℓ row with
      | some A => do pure (.inj ℓ (← dataAt d A v))
      | none => .error (.notOfType p)
    | .sum row, .atom p ℓ =>
      match Row.find? ℓ row with
      | some (.record []) => .ok (.inj ℓ (.record []))
      | _ => .error (.notOfType p)
    | .record _, y | .sum _, y | .fn _ _, y => .error (.notOfType y.pos)
    | T, y => scalarAt T y

/-- Read sorted fields at the record row: the same labels in the same order, each at its type. -/
def dataRow : Nat → Nat → List (Label × Ty) → List (Label × SExp) → P (List (Label × Data))
  | _, _, [], [] => .ok []
  | 0, p, _, _ => .error (.tooDeep p)
  | d + 1, p, (ℓ, A) :: row, (k, v) :: fs =>
    if ℓ = k then do pure ((ℓ, ← dataAt d A v) :: (← dataRow d p row fs)) else .error (.notOfType v.pos)
  | _ + 1, p, _, _ => .error (.notOfType p)
end

/-- Text to data at type `T`. -/
def readData (T : Ty) (text : String) : P Data := do dataAt depthMax T (← parse text)

/-! ## Printing types (what a resident pastes into an annotation) -/

mutual
/-- A type as text `ty` reads back (rows are printed in their own order). -/
def showTy : Ty → String
  | .nat => "nat" | .bool => "bool" | .bytes => "bytes"
  | .fn a b => s!"(-> {showTy a} {showTy b})"
  | .record r => s!"(rec{showRow r})"
  | .sum r => s!"(sum{showRow r})"

def showRow : List (Label × Ty) → String
  | [] => ""
  | (ℓ, t) :: r => s!" ({ℓ} {showTy t}){showRow r}"
end

/-- Text to a package. -/
def readPackage (text : String) : P Package := do package (← parse text)

/-- Text to a closed term (no package around it). -/
def readTerm (text : String) : P Term := do term depthMax [] (← parse text)

/-- Text to a type. -/
def readTy (text : String) : P Ty := do ty depthMax (← parse text)

end Nanodregg.Lang.Read
