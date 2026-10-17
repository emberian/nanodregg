/-
# Lang.Print — the core as the text `Lang.Read` reads: the one printer

A type, a term, a data value and a package print first as an s-expression (`Read.SExp`, every
offset 0), then as characters (`chars`). `Lang.Proofs.Print` proves the round trip: `Read` gives
back exactly what was printed.

When something has no text, the printer returns `none`. It never guesses. Three things have no text:
a label the wire refuses (`Wire.labelOk`: not one atom, or past 64 bytes), a term with a free
variable, and a form nested deeper than `Read.depthMax` (`need`, one per nesting level: what the
reader's fuel counts) or holding a list of more than `Read.listMax` elements (`width`). The reader
would refuse such a text `tooDeep` / `tooLong`. A bound variable prints as `x<depth>`, which names the binder that introduced it. Bytes
print as `"text"` when they are UTF-8 with no `"`, and otherwise as `#hex` (lowercase, two digits per
byte). `Read` reads both spellings in a term and in a data literal.

This is the printer the resident (`ob`), the journeys, the rows and the shipped package texts
(`world/grain/Lifecycle`) use. A package is laid out one section per line.
-/
import Lang.Read

namespace Nanodregg.Lang.Print

open Read (SExp)
open Wire (labelOk)

/-! ## Characters -/


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
/-- The reader's fuel for a form: its nesting depth (an atom or a string 1, a list one more than its
deepest element). The printer refuses a form needing more than `Read.depthMax`, since the reader
would refuse it with `tooDeep`. -/
def need : SExp → Nat
  | .atom _ _ | .str _ _ => 1
  | .list _ xs => needs xs + 1

/-- The deepest element's need (0 for none). -/
def needs : List SExp → Nat
  | [] => 0
  | x :: xs => max (need x) (needs xs)
end

mutual
/-- The longest list in a form; the reader refuses one longer than `Read.listMax` (`tooLong`). -/
def width : SExp → Nat
  | .atom _ _ | .str _ _ => 0
  | .list _ xs => max xs.length (widths xs)

def widths : List SExp → Nat
  | [] => 0
  | x :: xs => max (width x) (widths xs)
end

/-- The reader reads the form: nested at most `Read.depthMax`, no list past `Read.listMax`. -/
def fitsB (x : SExp) : Bool := need x ≤ Read.depthMax && width x ≤ Read.listMax

/-- The text of a form the reader can read: `none` past `Read.depthMax` or `Read.listMax`. -/
def fits (x : SExp) : Option String := if fitsB x then some (text x) else none

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

/-- A term that is a constant of the program: that it has a text is decided where it is written. -/
def termText (t : Term) (h : (term t).isSome = true := by decide) : String := (term t).get h

/-! ## A method's calls, as a resident pastes them (printed, never restated) -/

/-- The calls row of a method that makes no calls. -/
def noCallsText : String := termText (callsT [])

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
  if fitsB (list xs) then
    pure (String.ofList ('(' :: items ['\n', ' ', ' '] xs ++ ['\n']))
  else none

end Nanodregg.Lang.Print
