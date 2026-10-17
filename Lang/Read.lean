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
Every recursion is bounded by `depthMax`.
-/
import Lang.Package

namespace Nanodregg.Lang.Read

inductive SExp
  | atom (s : String)
  | str (s : String)
  | list (xs : List SExp)
  deriving Inhabited

def depthMax : Nat := 512

abbrev P (α : Type) := Except String α

/-! ## Reading text -/

def isDelim (c : Char) : Bool := c = '(' || c = ')' || c = '"' || c.isWhitespace || c = ';'

mutual
/-- Skip whitespace and `;` comments to end of line. -/
def skip : List Char → List Char
  | [] => []
  | c :: cs => if c.isWhitespace then skip cs else if c = ';' then skipLine cs else c :: cs

def skipLine : List Char → List Char
  | [] => []
  | c :: cs => if c = '\n' then skip cs else skipLine cs
end

mutual
def sexp : Nat → List Char → P (SExp × List Char)
  | 0, _ => .error "nested too deep"
  | d + 1, cs =>
    match skip cs with
    | [] => .error "unexpected end"
    | '(' :: rest => (sexps d (skip rest) []).map fun (xs, r) => (.list xs, r)
    | ')' :: _ => .error "unexpected )"
    | '"' :: rest =>
      let body := rest.takeWhile (· ≠ '"')
      match rest.dropWhile (· ≠ '"') with
      | '"' :: r => .ok (.str (String.ofList body), r)
      | _ => .error "unterminated string"
    | cs' =>
      let a := cs'.takeWhile (fun c => !isDelim c)
      .ok (.atom (String.ofList a), cs'.dropWhile (fun c => !isDelim c))

def sexps : Nat → List Char → List SExp → P (List SExp × List Char)
  | 0, _, _ => .error "list too long"
  | d + 1, cs, acc =>
    match skip cs with
    | ')' :: rest => .ok (acc.reverse, rest)
    | [] => .error "unclosed ("
    | cs' =>
      match sexp d cs' with
      | .ok (x, r) => sexps d r (x :: acc)
      | .error e => .error e
end

def parse (text : String) : P SExp :=
  match sexp depthMax text.toList with
  | .ok (x, rest) => if (skip rest).isEmpty then .ok x else .error "text after the expression"
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
  | 0, _ => .error "type too deep"
  | _ + 1, .atom "nat" => .ok .nat
  | _ + 1, .atom "bool" => .ok .bool
  | _ + 1, .atom "bytes" => .ok .bytes
  | d + 1, .list [.atom "->", a, b] => do pure (.fn (← ty d a) (← ty d b))
  | d + 1, .list (.atom "rec" :: fs) => do pure (.record (sortRow (← tyRow d fs)))
  | d + 1, .list (.atom "sum" :: fs) => do pure (.sum (sortRow (← tyRow d fs)))
  | _ + 1, _ => .error "not a type"

def tyRow : Nat → List SExp → P (List (Label × Ty))
  | _, [] => .ok []
  | 0, _ => .error "row too deep"
  | d + 1, .list [.atom ℓ, t] :: rest => do pure ((ℓ, ← ty d t) :: (← tyRow d rest))
  | _ + 1, _ => .error "a row entry is (label type)"
end

def indexOf (x : String) : List String → Option Nat
  | [] => none
  | y :: ys => if x = y then some 0 else (indexOf x ys).map (· + 1)

def appAll (f : Term) : List Term → Term
  | [] => f
  | a :: as => appAll (.app f a) as

mutual
def term : Nat → List String → SExp → P Term
  | 0, _, _ => .error "term too deep"
  | _ + 1, _, .atom "true" => .ok (.bool true)
  | _ + 1, _, .atom "false" => .ok (.bool false)
  | _ + 1, sc, .atom a =>
    match a.toNat? with
    | some n => .ok (.nat n)
    | none =>
      match indexOf a sc with
      | some i => .ok (.var i)
      | none => .error s!"unbound {a}"
  | _ + 1, _, .str s => .ok (.bytes s.toUTF8)
  | d + 1, sc, .list [.atom "lam", .atom x, t, b] => do
    pure (.lam (← ty d t) (← term d (x :: sc) b))
  | d + 1, sc, .list (.atom "fn" :: rest) => fnBinders d sc rest
  | d + 1, sc, .list [.atom "let", .atom x, t, e, b] => do
    pure (.app (.lam (← ty d t) (← term d (x :: sc) b)) (← term d sc e))
  | d + 1, sc, .list [.atom "fix", e] => do pure (.fix (← term d sc e))
  | d + 1, sc, .list [.atom ".", e, .atom ℓ] => do pure (.get (← term d sc e) ℓ)
  | d + 1, sc, .list (.atom "record" :: fs) => do pure (.record (sortRow (← fields d sc fs)))
  | d + 1, sc, .list (.atom "extend" :: e :: fs) => do
    pure (.extend (← term d sc e) (sortRow (← fields d sc fs)))
  | d + 1, sc, .list [.atom "inj", t, .atom ℓ, e] => do pure (.inj (← ty d t) ℓ (← term d sc e))
  | d + 1, sc, .list (.atom "case" :: e :: arms) => do
    pure (.case (← term d sc e) (sortRow (← armsOf d sc arms)))
  | d + 1, sc, .list [.atom "if", c, a, b] => do
    pure (.ite (← term d sc c) (← term d sc a) (← term d sc b))
  | _ + 1, _, .list [.atom "ref", .atom i] =>
    match i.toNat? with
    | some n => .ok (.ref n)
    | none => .error "ref takes an index"
  | d + 1, sc, .list [.atom op, a, b] =>
    match primOf op with
    | some p => do pure (.prim p (← term d sc a) (← term d sc b))
    | none => do pure (appAll (← term d sc (.atom op)) [← term d sc a, ← term d sc b])
  | d + 1, sc, .list (f :: args) => do pure (appAll (← term d sc f) (← termList d sc args))
  | _ + 1, _, .list [] => .error "empty application"

def termList : Nat → List String → List SExp → P (List Term)
  | _, _, [] => .ok []
  | 0, _, _ => .error "too many arguments"
  | d + 1, sc, e :: es => do pure ((← term d sc e) :: (← termList d sc es))

def fields : Nat → List String → List SExp → P (List (Label × Term))
  | _, _, [] => .ok []
  | 0, _, _ => .error "too many fields"
  | d + 1, sc, .list [.atom ℓ, e] :: rest => do pure ((ℓ, ← term d sc e) :: (← fields d sc rest))
  | _ + 1, _, _ => .error "a field is (label term)"

def armsOf : Nat → List String → List SExp → P (List (Label × Term))
  | _, _, [] => .ok []
  | 0, _, _ => .error "too many arms"
  | d + 1, sc, .list [.atom ℓ, .atom x, e] :: rest => do
    pure ((ℓ, ← term d (x :: sc) e) :: (← armsOf d sc rest))
  | _ + 1, _, _ => .error "an arm is (label name term)"

def fnBinders : Nat → List String → List SExp → P Term
  | 0, _, _ => .error "too many binders"
  | d + 1, sc, [b] => term d sc b
  | d + 1, sc, .list [.atom x, t] :: rest => do pure (.lam (← ty d t) (← fnBinders d (x :: sc) rest))
  | _ + 1, _, _ => .error "fn takes (name type)… body"
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
  | .atom ℓ :: rest => do pure (ℓ :: (← labels rest))
  | _ => .error "expected labels"

def package (x : SExp) : P Package :=
  match x with
  | .list [.atom "package", .list (.atom "imports" :: is), .list [.atom "state", s],
      .list [.atom "iface", i], .list (.atom "methods" :: ms), .list (.atom "laws" :: ls),
      .list [.atom "body", b]] => do
    let imports ← is.mapM fun
      | .str h => match unhex ByteArray.empty h.toList with
        | some bs => .ok bs
        | none => .error "an import is a hex digest"
      | _ => .error "an import is a hex digest"
    pure { imports, state := ← ty depthMax s, iface := ← ty depthMax i, body := ← term depthMax [] b,
           methods := ← labels ms, laws := ← labels ls }
  | _ => .error "(package (imports …) (state T) (iface T) (methods …) (laws …) (body e))"

/-- Text to a package. -/
def readPackage (text : String) : P Package := do package (← parse text)

end Nanodregg.Lang.Read
