/-
# Lang.Read — the core in s-expressions, with names: what a Hermes resident writes

Not admission: a resident (or its client) reads text into a `Package`, checks it with the same
`Package.checkWith` the receiver runs, and installs the bytes. The surface is the core with names
(resolved to de Bruijn indices here) and three conveniences: application of many arguments
`(f a b)`, `(let x T e body)` = `((lam x T body) e)`, and `(fn (x T) (y U) body)` = nested `lam`.

    type  ::= nat | bool | bytes | (-> T U) | (rec (l T)…) | (sum (l T)…)
    term  ::= x | 123 | true | false | "text" | #hex | (lam x T e) | (fn (x T)… e) | (let x T e e)
            | (fix e) | (OP e e) with OP ∈ + - * / % == < <= beq cat
            | (record (l e)…) | (. e l) | (extend e (l e)…) | (inj T l e)
            | (case e (l x e)…) | (if e e e) | (ref i) | (e e…)
    package ::= (package (imports "hex"…) (state T) (iface T) (methods l…) (laws l…) (body e))

A binder (`lam`, `let`, `fn`, a `case` arm) may not be named like a literal, a head word or a
primitive (`reservedBinder`).
Fields and arms may be written in any order: they are sorted into the canonical (ascending) order.
Forms nest at most `depthMax` deep and a list holds at most `listMax` elements: the reader's fuel
counts nesting only, so a long chain (`anyOf` over 63 members) costs its depth, not its length.
A refusal is a `ReadRefusal`: a named constructor with
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

/-- The deepest nesting the reader reads: the wire's tree depth plus 2. A printed form nests at most
one level deeper than its tree (`(ref i)` is a list, its tree a leaf), and the package's sections
one more, so every package the wire carries has a text within it (`Lang.Proofs.PrintWire`). -/
def depthMax : Nat := Wire.depthMax + 2

/-- The most elements one list holds: a row of `Wire.rowMax` entries after the head words of
`(case e arm…)` / `(extend e field…)`, so every form the wire carries has a text that fits. -/
def listMax : Nat := Wire.rowMax + 2

/-- Why the reader refuses, by name, at a character offset. -/
inductive ReadRefusal
  /-- forms nested deeper than `depthMax` -/
  | tooDeep (pos : Nat)
  /-- a list (opened at `pos`) of more than `listMax` elements -/
  | tooLong (pos : Nat)
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
  /-- a binder named like a literal (`true`, `false`, a numeral, `#hex`) or a form's head word (`if`,
  `+`, …): a use would read as the literal or the form, so the binder could not be referred to -/
  | reservedBinder (pos : Nat) (name : String)
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
  | .tooDeep _ => "tooDeep" | .tooLong _ => "tooLong" | .unexpectedEnd _ => "unexpectedEnd" | .stray _ => "stray"
  | .unterminatedString _ => "unterminatedString" | .unclosed _ => "unclosed"
  | .trailing _ => "trailing" | .notAType _ => "notAType" | .badEntry _ => "badEntry"
  | .unbound _ _ => "unbound" | .badRef _ => "badRef" | .emptyApplication _ => "emptyApplication"
  | .badBinder _ => "badBinder" | .reservedBinder _ _ => "reservedBinder" | .badImport _ => "badImport" | .badLabel _ => "badLabel"
  | .notPackage _ => "notPackage" | .notOfType _ => "notOfType"

def ReadRefusal.pos : ReadRefusal → Nat
  | .tooDeep p | .tooLong p | .unexpectedEnd p | .stray p | .unterminatedString p | .unclosed p | .trailing p
  | .notAType p | .badEntry p | .unbound p _ | .badRef p | .emptyApplication p | .badBinder p
  | .reservedBinder p _
  | .badImport p | .badLabel p | .notPackage p | .notOfType p => p

/-- `name @offset`, plus the unbound name: what a resident reads. -/
def ReadRefusal.text (e : ReadRefusal) : String :=
  match e with
  | .unbound p x => s!"unbound @{p} {x}"
  | .reservedBinder p x => s!"reservedBinder @{p} {x}"
  | e => s!"{e.name} @{e.pos}"

abbrev P (α : Type) := Except ReadRefusal α

/-! ## Reading text (the offset of the head of the remaining characters is carried) -/


mutual
/-- Skip whitespace and `;` comments to end of line. -/
def skip : Nat → List Char → Nat × List Char
  | p, [] => (p, [])
  | p, c :: cs => if c.isWhitespace then skip (p + 1) cs else if c = ';' then skipLine (p + 1) cs else (p, c :: cs)

def skipLine : Nat → List Char → Nat × List Char
  | p, [] => (p, [])
  | p, c :: cs => if c = '\n' then skip (p + 1) cs else skipLine (p + 1) cs
end

/-- The rest of a list opened at `o`, from offset `p`, each element read by `elem`, at most `n`
more of them (`tooLong` past that). -/
def sexpsWith (elem : Nat → List Char → P (SExp × Nat × List Char)) (o : Nat) :
    Nat → Nat → List Char → List SExp → P (List SExp × Nat × List Char)
  | n, p, cs, acc =>
    match skip p cs with
    | (p, ')' :: rest) => .ok (acc.reverse, p + 1, rest)
    | (_, []) => .error (.unclosed o)
    | (p, cs') =>
      match n with
      | 0 => .error (.tooLong o)
      | n + 1 =>
        match elem p cs' with
        | .ok (x, q, r) => sexpsWith elem o n q r (x :: acc)
        | .error e => .error e

/-- One form within `d` levels of nesting: an atom or a string costs 1, a list 1 more than its
deepest element; a list's length is bounded by `listMax`, not by the fuel. -/
def sexp : Nat → Nat → List Char → P (SExp × Nat × List Char)
  | 0, p, _ => .error (.tooDeep p)
  | d + 1, p, cs =>
    match skip p cs with
    | (p, []) => .error (.unexpectedEnd p)
    | (p, '(' :: rest) =>
      let (q, rest) := skip (p + 1) rest
      (sexpsWith (fun p cs => sexp d p cs) p listMax q rest []).map fun (xs, r) => (.list p xs, r)
    | (p, ')' :: _) => .error (.stray p)
    | (p, '"' :: rest) =>
      let body := rest.takeWhile (· ≠ '"')
      match rest.dropWhile (· ≠ '"') with
      | '"' :: r => .ok (.str p (String.ofList body), p + body.length + 2, r)
      | _ => .error (.unterminatedString p)
    | (p, cs') =>
      let a := cs'.takeWhile (fun c => !isDelim c)
      .ok (.atom p (String.ofList a), p + a.length, cs'.dropWhile (fun c => !isDelim c))

def parse (text : String) : P SExp :=
  match sexp depthMax 0 text.toList with
  | .ok (x, p, rest) =>
    match skip p rest with
    | (_, []) => .ok x
    | (q, _) => .error (.trailing q)
  | .error e => .error e

/-! ## Elaboration to the core -/

def primOf : String → Option Prim
  | "+" => some .add | "-" => some .sub | "*" => some .mul | "/" => some .div | "%" => some .mod
  | "==" => some .eq | "<" => some .lt | "<=" => some .le | "beq" => some .beq | "cat" => some .cat
  | _ => none

/-- The entries `(label x)…` of a row, each `x` read by `f`. -/
def entries {α : Type} (f : SExp → P α) : List SExp → P (List (Label × α))
  | [] => .ok []
  | .list _ [.atom _ ℓ, e] :: rest => do pure ((ℓ, ← f e) :: (← entries f rest))
  | x :: _ => .error (.badEntry x.pos)

def ty : Nat → SExp → P Ty
  | 0, x => .error (.tooDeep x.pos)
  | _ + 1, .atom _ "nat" => .ok .nat
  | _ + 1, .atom _ "bool" => .ok .bool
  | _ + 1, .atom _ "bytes" => .ok .bytes
  | d + 1, .list _ [.atom _ "->", a, b] => do pure (.fn (← ty d a) (← ty d b))
  | d + 1, .list _ (.atom _ "rec" :: fs) => do pure (.record (Row.sort (← entries (fun t => ty d t) fs)))
  | d + 1, .list _ (.atom _ "sum" :: fs) => do pure (.sum (Row.sort (← entries (fun t => ty d t) fs)))
  | _ + 1, x => .error (.notAType x.pos)

def hexVal (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10) else none

def unhex (acc : ByteArray) : List Char → Option ByteArray
  | [] => some acc
  | a :: b :: rest => do unhex (acc.push (UInt8.ofNat ((← hexVal a) * 16 + (← hexVal b)))) rest
  | _ => none

/-- `#HEX`: the bytes of an even count of lowercase hex digits after `#`. -/
def hexBytes? (a : String) : Option ByteArray :=
  match a.toList with
  | '#' :: hs => unhex .empty hs
  | _ => none

/-- An atom that `term` reads as a literal before it looks at the scope. -/
def isLiteral (a : String) : Bool := a = "true" || a = "false" || a.toNat?.isSome || (hexBytes? a).isSome

/-- The head words of the forms `term` reads (besides the primitives, `primOf`). -/
def keywords : List String := ["lam", "fn", "let", "fix", ".", "record", "extend", "inj", "case", "if", "ref"]

/-- A name `term` reads as something other than a variable: a literal, a head word, a primitive. -/
def isReserved (a : String) : Bool := isLiteral a || keywords.contains a || (primOf a).isSome

/-- A binder name is not reserved (`reservedBinder` at its offset). -/
def binder (p : Nat) (x : String) : P Unit := if isReserved x then .error (.reservedBinder p x) else .ok ()

def indexOf (x : String) : List String → Option Nat
  | [] => none
  | y :: ys => if x = y then some 0 else (indexOf x ys).map (· + 1)

def appAll (f : Term) : List Term → Term
  | [] => f
  | a :: as => appAll (.app f a) as

/-- The arms `(label name body)…` of a case, each body read by `f` with `name` bound. -/
def arms (f : String → SExp → P Term) : List SExp → P (List (Label × Term))
  | [] => .ok []
  | .list _ [.atom _ ℓ, .atom q x, e] :: rest => do binder q x; pure ((ℓ, ← f x e) :: (← arms f rest))
  | x :: _ => .error (.badEntry x.pos)

/-- `(fn (x T)… body)` after `fn`: each binder's type read by `tyOf`, the body by `body` in the
scope the binders extend. -/
def fnWith (tyOf : SExp → P Ty) (body : List String → SExp → P Term) : List String → List SExp → P Term
  | sc, [b] => body sc b
  | sc, .list _ [.atom q x, t] :: rest => do
    binder q x; pure (.lam (← tyOf t) (← fnWith tyOf body (x :: sc) rest))
  | _, x :: _ => .error (.badBinder x.pos)
  | _, [] => .error (.badBinder 0)

def term : Nat → List String → SExp → P Term
  | 0, _, x => .error (.tooDeep x.pos)
  | _ + 1, _, .atom _ "true" => .ok (.bool true)
  | _ + 1, _, .atom _ "false" => .ok (.bool false)
  | _ + 1, sc, .atom p a =>
    match a.toNat? with
    | some n => .ok (.nat n)
    | none =>
      match hexBytes? a with
      | some b => .ok (.bytes b)
      | none =>
        match indexOf a sc with
        | some i => .ok (.var i)
        | none => .error (.unbound p a)
  | _ + 1, _, .str _ s => .ok (.bytes s.toUTF8)
  | d + 1, sc, .list _ [.atom _ "lam", .atom q x, t, b] => do
    binder q x; pure (.lam (← ty d t) (← term d (x :: sc) b))
  | d + 1, sc, .list _ (.atom _ "fn" :: rest) => fnWith (fun t => ty d t) (fun sc b => term d sc b) sc rest
  | d + 1, sc, .list _ [.atom _ "let", .atom q x, t, e, b] => do
    binder q x; pure (.app (.lam (← ty d t) (← term d (x :: sc) b)) (← term d sc e))
  | d + 1, sc, .list _ [.atom _ "fix", e] => do pure (.fix (← term d sc e))
  | d + 1, sc, .list _ [.atom _ ".", e, .atom _ ℓ] => do pure (.get (← term d sc e) ℓ)
  | d + 1, sc, .list _ (.atom _ "record" :: fs) => do
    pure (.record (Row.sort (← entries (fun e => term d sc e) fs)))
  | d + 1, sc, .list _ (.atom _ "extend" :: e :: fs) => do
    pure (.extend (← term d sc e) (Row.sort (← entries (fun e => term d sc e) fs)))
  | d + 1, sc, .list _ [.atom _ "inj", t, .atom _ ℓ, e] => do pure (.inj (← ty d t) ℓ (← term d sc e))
  | d + 1, sc, .list _ (.atom _ "case" :: e :: as) => do
    pure (.case (← term d sc e) (Row.sort (← arms (fun x b => term d (x :: sc) b) as)))
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
  | d + 1, sc, .list _ (f :: args) => do pure (appAll (← term d sc f) (← args.mapM fun e => term d sc e))
  | _ + 1, _, .list p [] => .error (.emptyApplication p)

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
`"text"`, `#0a1b` (a byte string as lowercase hex, an even count of digits: bytes that are not
UTF-8, such as a member's id; what `ob` prints such bytes as), `(record (l v)…)` (fields in any order, exactly the type's), and for a sum `(l v)` or a
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
  | .bytes, .atom p a =>
    match hexBytes? a with
    | some b => if b.size ≤ Bounds.bytesMax then .ok (.bytes b) else .error (.notOfType p)
    | none => .error (.notOfType p)
  | _, x => .error (.notOfType x.pos)

/-- The fields of a record literal, unread: `(label value)…`. -/
def dataFields : List SExp → P (List (Label × SExp))
  | [] => .ok []
  | .list _ [.atom _ ℓ, v] :: rest => do pure ((ℓ, v) :: (← dataFields rest))
  | x :: _ => .error (.badEntry x.pos)

/-- Read sorted fields at the record row: the same labels in the same order, each by `f` at its type. -/
def dataRowWith (f : Ty → SExp → P Data) (p : Nat) :
    List (Label × Ty) → List (Label × SExp) → P (List (Label × Data))
  | [], [] => .ok []
  | (ℓ, A) :: row, (k, v) :: fs =>
    if ℓ = k then do pure ((ℓ, ← f A v) :: (← dataRowWith f p row fs)) else .error (.notOfType v.pos)
  | _, _ => .error (.notOfType p)

def dataAt : Nat → Ty → SExp → P Data
  | 0, _, x => .error (.tooDeep x.pos)
  | d + 1, T, x =>
    match T, x with
    | .record row, .list p (.atom _ "record" :: fs) => do
      pure (.record (← dataRowWith (fun A v => dataAt d A v) p row (Row.sort (← dataFields fs))))
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

/-- Text to data at type `T`. -/
def readData (T : Ty) (text : String) : P Data := do dataAt depthMax T (← parse text)

/-- Text to a package. -/
def readPackage (text : String) : P Package := do package (← parse text)

/-- Text to a closed term (no package around it). -/
def readTerm (text : String) : P Term := do term depthMax [] (← parse text)

/-- Text to a type. -/
def readTy (text : String) : P Ty := do ty depthMax (← parse text)

end Nanodregg.Lang.Read
