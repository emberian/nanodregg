/-
# Lang.Print — the core as the text `Lang.Read` reads: the one printer

A type, a term, a data value and a package print first as an s-expression (`Read.SExp`, every
offset 0), then as characters (`chars`). `Lang.Proofs.Print` proves the round trip: `Read` gives
back exactly what was printed.

When something has no text, the printer returns `none`. It never guesses. Three things have no text:
a label that is not one atom (empty, or holding a `Read.isDelim` character), a term with a free
variable, and a form needing more than `Read.depthMax` of the reader's fuel (`need`: the reader
spends one per nesting level AND one per list element, so a long chain such as `anyOf` over many
ids costs fuel in proportion to its length; measured 10-17, a 63-member `Std.quorum` law needs 385
and a 63-id `allowlist` 351). The reader would refuse such a text `tooDeep`. A bound variable prints as `x<depth>`, which names the binder that introduced it. Bytes
print as `"text"` when they are UTF-8 with no `"`, and otherwise as `#hex` (lowercase, two digits per
byte). `Read` reads both spellings in a term and in a data literal.

This is the printer the resident (`ob`), the journeys, the rows and the shipped package texts
(`world/grain/Lifecycle`) use. A package is laid out one section per line.
-/
import Lang.Read

namespace Nanodregg.Lang.Print

open Read (SExp isDelim)

/-! ## Characters -/

/-- A label prints as one atom: nonempty, with no delimiter (over `toList`, so the kernel reduces it). -/
def labelOk (s : String) : Bool := !s.toList.isEmpty && s.toList.all (fun c => !isDelim c)

def atom (s : String) : SExp := .atom 0 s
def list (xs : List SExp) : SExp := .list 0 xs

def label (s : String) : Option SExp := if labelOk s then some (atom s) else none

mutual
/-- An s-expression as characters; the elements of a list are separated by one space. -/
def chars : SExp → List Char
  | .atom _ s => s.toList
  | .str _ s => '"' :: (s.toList ++ ['"'])
  | .list _ xs => '(' :: items [' '] xs

/-- The elements of a list separated by `sep`, then `)`. -/
def items (sep : List Char) : List SExp → List Char
  | [] => [')']
  | x :: [] => chars x ++ [')']
  | x :: y :: ys => chars x ++ sep ++ items sep (y :: ys)
end

def text (x : SExp) : String := String.ofList (chars x)

mutual
/-- The reader's fuel for a form: one per nesting level, and one per element of a list, because
`Read.sexps` spends one per element. The printer refuses a form needing more than `Read.depthMax`,
since the reader would refuse it with `tooDeep`. -/
def need : SExp → Nat
  | .atom _ _ | .str _ _ => 1
  | .list _ xs => needs xs + 1

def needs : List SExp → Nat
  | [] => 1
  | x :: xs => max (need x) (needs xs) + 1
end

/-- The text of a form the reader can read: `none` past `Read.depthMax`. -/
def fits (x : SExp) : Option String := if need x ≤ Read.depthMax then some (text x) else none

def hexDigit (n : Nat) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

/-- Lowercase hex, two digits per byte (what `Read.unhex` reads). -/
def hexChars (b : ByteArray) : List Char :=
  b.data.foldr (fun x cs => hexDigit (x.toNat / 16) :: hexDigit (x.toNat % 16) :: cs) []

def hex (b : ByteArray) : String := String.ofList (hexChars b)

/-- Bytes as `"text"` when they are UTF-8 holding no `"`, else as `#hex`. -/
def bytesSx (b : ByteArray) : SExp :=
  match String.fromUTF8? b with
  | some t => if t.toList.contains '"' then atom ("#" ++ hex b) else .str 0 t
  | none => atom ("#" ++ hex b)

def bytesText (b : ByteArray) : String := text (bytesSx b)

/-! ## Types -/

mutual
def tySx : Ty → Option SExp
  | .nat => some (atom "nat")
  | .bool => some (atom "bool")
  | .bytes => some (atom "bytes")
  | .fn a b => do pure (list [atom "->", ← tySx a, ← tySx b])
  | .record r => do pure (list (atom "rec" :: (← rowSx r)))
  | .sum r => do pure (list (atom "sum" :: (← rowSx r)))

def rowSx : List (Label × Ty) → Option (List SExp)
  | [] => some []
  | (ℓ, t) :: r => do pure (list [← label ℓ, ← tySx t] :: (← rowSx r))
end

def ty (T : Ty) : Option String := (tySx T).bind fits

/-- A type that is a constant of the program: that it has a text is decided where it is written. -/
def tyText (T : Ty) (h : (ty T).isSome = true := by decide) : String := (ty T).get h

/-! ## Terms -/

def primWord : Prim → String
  | .add => "+" | .sub => "-" | .mul => "*" | .div => "/" | .mod => "%"
  | .eq => "==" | .lt => "<" | .le => "<=" | .beq => "beq" | .cat => "cat"

/-- The name of the variable bound at depth `d`. -/
def name (d : Nat) : String := "x" ++ Nat.repr d

mutual
/-- Term `t` under `d` binders. -/
def termSx (d : Nat) : Term → Option SExp
  | .var i => if i < d then some (atom (name (d - 1 - i))) else none
  | .lam a b => do pure (list [atom "lam", atom (name d), ← tySx a, ← termSx (d + 1) b])
  | .app f a => do pure (list [← termSx d f, ← termSx d a])
  | .fix t => do pure (list [atom "fix", ← termSx d t])
  | .nat n => some (atom (Nat.repr n))
  | .bool b => some (atom (if b then "true" else "false"))
  | .bytes s => some (bytesSx s)
  | .prim p a b => do pure (list [atom (primWord p), ← termSx d a, ← termSx d b])
  | .record fs => do pure (list (atom "record" :: (← fieldsSx d fs)))
  | .get t ℓ => do pure (list [atom ".", ← termSx d t, ← label ℓ])
  | .extend t fs => do pure (list (atom "extend" :: (← termSx d t) :: (← fieldsSx d fs)))
  | .inj T ℓ t => do pure (list [atom "inj", ← tySx T, ← label ℓ, ← termSx d t])
  | .case t arms => do pure (list (atom "case" :: (← termSx d t) :: (← armsSx d arms)))
  | .ite c a b => do pure (list [atom "if", ← termSx d c, ← termSx d a, ← termSx d b])
  | .ref i => some (list [atom "ref", atom (Nat.repr i)])

def fieldsSx (d : Nat) : List (Label × Term) → Option (List SExp)
  | [] => some []
  | (ℓ, t) :: fs => do pure (list [← label ℓ, ← termSx d t] :: (← fieldsSx d fs))

def armsSx (d : Nat) : List (Label × Term) → Option (List SExp)
  | [] => some []
  | (ℓ, t) :: arms => do pure (list [← label ℓ, atom (name d), ← termSx (d + 1) t] :: (← armsSx d arms))
end

/-- A closed term. -/
def term (t : Term) : Option String := (termSx 0 t).bind fits

/-! ## Data (what `Read.dataAt` reads back at the value's type) -/

mutual
def dataSx : Data → Option SExp
  | .nat n => some (atom (Nat.repr n))
  | .bool b => some (atom (if b then "true" else "false"))
  | .bytes s => some (bytesSx s)
  | .record fs => do pure (list (atom "record" :: (← dataFieldsSx fs)))
  | .inj ℓ v => do pure (list [← label ℓ, ← dataSx v])

def dataFieldsSx : List (Label × Data) → Option (List SExp)
  | [] => some []
  | (ℓ, v) :: fs => do pure (list [← label ℓ, ← dataSx v] :: (← dataFieldsSx fs))
end

def data (v : Data) : Option String := (dataSx v).bind fits

/-! ## Packages -/

/-- The six sections of `(package …)`, in the order `Read.package` requires. -/
def sectionsSx (p : Package) : Option (List SExp) := do
  pure [list (atom "imports" :: p.imports.map fun i => .str 0 (hex i)),
    list [atom "state", ← tySx p.state],
    list [atom "iface", ← tySx p.iface],
    list (atom "methods" :: (← p.methods.mapM label)),
    list (atom "laws" :: (← p.laws.mapM label)),
    list [atom "body", ← termSx 0 p.body]]

/-- The package's text, one section per line. -/
def package (p : Package) : Option String := do
  let xs := atom "package" :: (← sectionsSx p)
  if need (list xs) ≤ Read.depthMax then
    pure (String.ofList ('(' :: items ['\n', ' ', ' '] xs ++ ['\n']))
  else none

end Nanodregg.Lang.Print
