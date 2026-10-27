/-
# Lang.Read — the core in s-expressions, with names: what a Hermes resident writes

Not admission: a resident (or its client) reads text into a `Package`, checks it with the same
`Package.checkWith` the receiver runs, and installs the bytes. The surface is the core with names
(resolved to de Bruijn indices here) and three conveniences: application of many arguments
`(f a b)`, `(let x T e body)` = `((lam x T body) e)`, and `(fn (x T) (y U) body)` = nested `lam`.

    (the grammar is `grammar`, below: one text, which this comment and the testground both read)

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

/-- The core grammar, as a text a tool shows (the testground's grammar window). -/
def grammar : String :=
  "type  ::= nat | bool | bytes | digest | (-> T U) | (rec (l T)…) | (sum (l T)…)\n" ++
  "term  ::= x | 123 | true | false | \"text\" | #hex | (lam x T e) | (fn (x T)… e) | (let x T e e)\n" ++
  "        | (digest #hex) | (fix e) | (OP e e) with OP ∈ + - * / % == < <= beq cat deq len<= u64be sized dsized\n" ++
  "        | (record (l e)…) | (. e l) | (extend e (l e)…) | (inj T l e)\n" ++
  "        | (case e (l x e)…) | (if e e e) | (ref i) | (refuse T \"why\") | (e e…)\n" ++
  "package ::= (package (imports \"hex\"…) (doc [\"text\"]) (state T) (iface T) (methods l…) (laws l…) (rels rel…)\n" ++
  "            (body e) [(effects (l n)…)])\n" ++
  "rel     ::= (l (key (l T)…) (val T) (limit n) (sum [l]) (cap n) (retract b) (guard [l]) (holds [l]))\n"

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
  /-- `(digest #hex)` with something other than `#hex` -/
  | badDigest (pos : Nat)
  /-- `(refuse T why)` with `why` not a `"text"` or `#hex` literal -/
  | badRefuse (pos : Nat)
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
  /-- not `(package (imports …) (doc …) (state T) (iface T) (methods …) (laws …) (rels …) (body e))` -/
  | notPackage (pos : Nat)
  /-- a doc that is not one `"text"` of `Bounds.docOk` bytes (at most `docMax`, printable, no `"`), or
  is `(doc "")`: the empty doc is written `(doc)` (LANG-60) -/
  | badDoc (pos : Nat)
  /-- a data literal that is not a value of the type it is read at (or out of the data bounds) -/
  | notOfType (pos : Nat)
  deriving DecidableEq, Repr

/-- The refusal's name on the wire (law 7). -/
def ReadRefusal.name : ReadRefusal → String
  | .tooDeep _ => "tooDeep" | .tooLong _ => "tooLong" | .unexpectedEnd _ => "unexpectedEnd" | .stray _ => "stray"
  | .unterminatedString _ => "unterminatedString" | .unclosed _ => "unclosed"
  | .trailing _ => "trailing" | .notAType _ => "notAType" | .badEntry _ => "badEntry"
  | .unbound _ _ => "unbound" | .badRef _ => "badRef" | .badDigest _ => "badDigest" | .badRefuse _ => "badRefuse" | .emptyApplication _ => "emptyApplication"
  | .badBinder _ => "badBinder" | .reservedBinder _ _ => "reservedBinder" | .badImport _ => "badImport" | .badLabel _ => "badLabel"
  | .notPackage _ => "notPackage" | .notOfType _ => "notOfType" | .badDoc _ => "badDoc"

def ReadRefusal.pos : ReadRefusal → Nat
  | .tooDeep p | .tooLong p | .unexpectedEnd p | .stray p | .unterminatedString p | .unclosed p | .trailing p
  | .notAType p | .badEntry p | .unbound p _ | .badRef p | .badDigest p | .badRefuse p | .emptyApplication p | .badBinder p
  | .reservedBinder p _
  | .badImport p | .badLabel p | .notPackage p | .notOfType p | .badDoc p => p

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
  | "deq" => some .deq | "len<=" => some .lenLe
  | "u64be" => some .u64be | "sized" => some .sized | "dsized" => some .dsized
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
  | _ + 1, .atom _ "digest" => .ok .digest
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
def keywords : List String :=
  ["lam", "fn", "let", "fix", ".", "record", "extend", "inj", "case", "if", "ref", "digest", "refuse", "hole"]

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
  | _ + 1, _, .list p [.atom _ "digest", .atom _ h] =>
    match hexBytes? h with
    | some b => .ok (.digest b)
    | none => .error (.badDigest p)
  | d + 1, _, .list p [.atom _ "refuse", t, w] =>
    match w with
    | .str _ s => do pure (.refuse (← ty d t) s.toUTF8)
    | .atom _ a =>
      match hexBytes? a with
      | some b => do pure (.refuse (← ty d t) b)
      | none => .error (.badRefuse p)
    | _ => .error (.badRefuse p)
  | _ + 1, _, .list p [.atom _ "ref", .atom _ i] =>
    match i.toNat? with
    | some n => .ok (.ref n)
    | none => .error (.badRef p)
  | d + 1, sc, .list p [.atom _ "hole", .atom _ i, .list _ (.atom _ "subst" :: ts)] =>
    match i.toNat? with
    | some n => do pure (.hole n (← ts.mapM fun t => term d sc t))
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

/-- A key's fields `(l T)…`, in DECLARED order (a key's bytes follow it; LANG-49). -/
def keyFields : List SExp → P (List (Label × Ty))
  | [] => .ok []
  | .list _ [.atom _ ℓ, t] :: rest => do pure ((ℓ, ← ty depthMax t) :: (← keyFields rest))
  | x :: _ => .error (.badEntry x.pos)

/-- An optional label: `()` or `(l)` after the section word. -/
def optLabel (p : Nat) : List SExp → P (Option Label)
  | [] => .ok none
  | [.atom _ ℓ] => .ok (some ℓ)
  | _ => .error (.badEntry p)

/-- A relation: `(l (key (l T)…) (val T) (limit n) (sum [l]) (cap n) (retract b) (guard [l]))`. -/
def rel : SExp → P (Label × RelDecl)
  | .list p [.atom _ ℓ, .list _ (.atom _ "key" :: ks), .list _ [.atom _ "val", v],
      .list _ [.atom _ "limit", .atom _ l], .list _ (.atom _ "sum" :: su), .list _ [.atom _ "cap", .atom _ c],
      .list _ [.atom _ "retract", .atom _ r], .list _ (.atom _ "guard" :: gu), .list _ (.atom _ "holds" :: ho)] =>
    match l.toNat?, c.toNat?, (if r = "true" then some true else if r = "false" then some false else none) with
    | some limit, some cap, some retract => do
      pure (ℓ, { key := ← keyFields ks, val := ← ty depthMax v, limit, sum := ← optLabel p su, cap, retract,
                 guard := ← optLabel p gu, holds := ← optLabel p ho })
    | _, _, _ => .error (.badEntry p)
  | y => .error (.badEntry y.pos)

/-- A doc section's contents (LANG-60): none is the empty doc; one `"text"` is a doc that is
`Bounds.docOk` and not empty (one spelling per doc). -/
def doc (p : Nat) : List SExp → P ByteArray
  | [] => .ok .empty
  | [.str q t] => if Bounds.docOk t.toUTF8 && !t.toUTF8.isEmpty then .ok t.toUTF8 else .error (.badDoc q)
  | _ => .error (.badDoc p)

/-- The stable binder names used for a contextual candidate's explicit context. -/
def holeScope (n : Nat) : List String :=
  ((List.range n).map (fun i => "x" ++ Nat.repr i)).reverse

def holeNat : SExp → P Nat
  | .atom p a => match a.toNat? with
    | some n => .ok n
    | none => .error (.badEntry p)
  | x => .error (.badEntry x.pos)

def holeBytes : SExp → P ByteArray
  | .atom p a => match hexBytes? a with
    | some b => .ok b
    | none => .error (.badEntry p)
  | x => .error (.badEntry x.pos)

def supportPin : SExp → P SupportPin
  | .list _ [.atom _ "pin", r, k, v] => do pure (.row (← holeNat r) (← holeBytes k) (← holeNat v))
  | .list _ [.atom _ "cell", k] => do pure (.cell (← holeBytes k))
  | .list _ [.atom _ "cell-law", k, l] => do pure (.cellLaw (← holeBytes k) (← holeBytes l))
  | .list _ [.atom _ "cell-package", k, q] => do pure (.cellPackage (← holeBytes k) (← holeBytes q))
  | x => .error (.badEntry x.pos)

def supportOptPin : SExp → P (Option SupportPin)
  | .list _ [.atom _ "structural"] => .ok none
  | x => (supportPin x).map some

def holeCode (ctx : List Ty) : SExp → P HoleCode
  | .list _ [.atom _ "candidate", b, .list _ (.atom _ "supports" :: ps)] => do
    pure ⟨← term depthMax (holeScope ctx.length) b, ← ps.mapM supportPin⟩
  | x => .error (.badEntry x.pos)

def holeROM : SExp → P HoleROM
  | .list _ [.atom _ "hole", n, .list _ (.atom _ "context" :: cs),
      .list _ [.atom _ "result", t], .list _ [.atom _ "selection", r, k],
      .list _ (.atom _ "hypotheses" :: hs), .list _ [.atom _ "guard", p, g],
      .list _ (.atom _ "code" :: ks)] => do
    let ctx ← cs.mapM (ty depthMax)
    let name ← holeNat n
    let result ← ty depthMax t
    let selectionRel ← holeNat r
    let selectionKey ← holeBytes k
    let hypotheses ← hs.mapM supportOptPin
    let guardPin ← supportOptPin p
    let guard ← term depthMax (holeScope 1) g
    let code ← ks.mapM (holeCode ctx)
    pure { name, ctx, ty := result, selectionRel, selectionKey, hypotheses, guardPin, guard, code }
  | x => .error (.badEntry x.pos)

def packageBase (x : SExp) : P Package :=
  match x with
  | .list _ [.atom _ "package", .list _ (.atom _ "imports" :: is), .list q (.atom _ "doc" :: ds),
      .list _ [.atom _ "state", s],
      .list _ [.atom _ "iface", i], .list _ (.atom _ "methods" :: ms), .list _ (.atom _ "laws" :: ls),
      .list _ (.atom _ "rels" :: rs), .list _ [.atom _ "body", b]] => do
    let imports ← is.mapM fun
      | .str p h => match unhex ByteArray.empty h.toList with
        | some bs => .ok bs
        | none => .error (.badImport p)
      | y => .error (.badImport y.pos)
    let doc ← doc q ds
    pure { imports, state := ← ty depthMax s, iface := ← ty depthMax i, body := ← term depthMax [] b,
           methods := ← labels ms, laws := ← labels ls, rels := ← rs.mapM rel, doc }
  | y => .error (.notPackage y.pos)

/-- A method's grades (LANG-89): `(ℓ N)` or `(ℓ N I)` with the interface it produces (LANG-103); `N` is bounded at encode (`effectWire`), as a relation's
`limit` is (`relWire`), not here. -/
def effect : SExp → P (Label × Effect)
  | .list _ [.atom _ ℓ, .atom q n] =>
    match n.toNat? with
    | some m => .ok (ℓ, { moves := m })
    | none => .error (.notOfType q)
  | .list _ [.atom _ ℓ, .atom q n, i] =>
    match n.toNat? with
    | some m => do pure (ℓ, { moves := m, produces := some (← ty depthMax i) })
    | none => .error (.notOfType q)
  | y => .error (.notOfType y.pos)

/-- A claim (LANG-93): `(keeps INV LAW)`. -/
def claim : SExp → P Claim
  | .list _ [.atom _ "keeps", .atom _ inv, .atom _ law] => .ok (.keeps inv law)
  | x => .error (.badEntry x.pos)

/-- The eight sections, then the optional `(effects …)` (LANG-89), `(claims …)` (LANG-93) and
`(holes …)`, in that order; each is absent exactly when empty (`Print.packageText`), so a core text
without one means a package with none of it. -/
def package (x : SExp) : P Package :=
  match x with
  | .list p [.atom q "package", is, ds, s, i, ms, ls, rs, b, .list _ (.atom _ "effects" :: es), .list _ (.atom _ "claims" :: cs), .list _ (.atom _ "holes" :: hs)] => do
    let base ← packageBase (.list p [.atom q "package", is, ds, s, i, ms, ls, rs, b])
    pure { base with effects := ← es.mapM effect, claims := ← cs.mapM claim, holes := ← hs.mapM holeROM }
  | .list p [.atom q "package", is, ds, s, i, ms, ls, rs, b, .list _ (.atom _ "effects" :: es), .list _ (.atom _ "claims" :: cs)] => do
    let base ← packageBase (.list p [.atom q "package", is, ds, s, i, ms, ls, rs, b])
    pure { base with effects := ← es.mapM effect, claims := ← cs.mapM claim }
  | .list p [.atom q "package", is, ds, s, i, ms, ls, rs, b, .list _ (.atom _ "effects" :: es), .list _ (.atom _ "holes" :: hs)] => do
    let base ← packageBase (.list p [.atom q "package", is, ds, s, i, ms, ls, rs, b])
    pure { base with effects := ← es.mapM effect, holes := ← hs.mapM holeROM }
  | .list p [.atom q "package", is, ds, s, i, ms, ls, rs, b, .list _ (.atom _ "effects" :: es)] => do
    let base ← packageBase (.list p [.atom q "package", is, ds, s, i, ms, ls, rs, b])
    pure { base with effects := ← es.mapM effect }
  | .list p [.atom q "package", is, ds, s, i, ms, ls, rs, b, .list _ (.atom _ "claims" :: cs), .list _ (.atom _ "holes" :: hs)] => do
    let base ← packageBase (.list p [.atom q "package", is, ds, s, i, ms, ls, rs, b])
    pure { base with claims := ← cs.mapM claim, holes := ← hs.mapM holeROM }
  | .list p [.atom q "package", is, ds, s, i, ms, ls, rs, b, .list _ (.atom _ "claims" :: cs)] => do
    let base ← packageBase (.list p [.atom q "package", is, ds, s, i, ms, ls, rs, b])
    pure { base with claims := ← cs.mapM claim }
  | .list p [.atom q "package", is, ds, s, i, ms, ls, rs, b, .list _ (.atom _ "holes" :: hs)] => do
    let base ← packageBase (.list p [.atom q "package", is, ds, s, i, ms, ls, rs, b])
    pure { base with holes := ← hs.mapM holeROM }
  | _ => packageBase x

/-! ## Data literals at a known type

What a resident writes for an object's seed state or a method's arguments: `123`, `true`/`false`,
`"text"`, `#0a1b` (a byte string as lowercase hex, an even count of digits: bytes that are not
UTF-8, such as a member's id; what `ob` prints such bytes as), `(record (l v)…)` (fields in any order, exactly the type's), and for a sum `(l v)` or a
bare `l` for an arm whose payload is the empty record. The type directs the reading, so a literal
needs no annotation, and only a value of the type is accepted (`Lang.Proofs.Read.dataAt_conforms`):
a natural below `Bounds.natLimit`, a byte string of at most `Bounds.bytesMax`, a digest (`#hex` at
type `digest`) of at most `Bounds.digestBytesMax`. -/

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
  | .digest, .atom p a =>
    match hexBytes? a with
    | some b => if b.size ≤ Bounds.digestBytesMax then .ok (.digest b) else .error (.notOfType p)
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
