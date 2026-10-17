/-
# Hosting.Text — a core package as the text `Lang.Read` reads

The grain package is generated as a Lean `Package` (what the theorems are about) and shipped as
the text a member installs (`install TEXT`, `world/grain/Lifecycle`). This prints the one as the
other; `Hosting.Proofs.Package.lifecycle_text_reads` proves that reading the text gives the same
package bytes, so the reader is checked against the printer on the one package that ships.

A bound variable is printed as `x<depth>`, the binder that introduced it; a term with a free
variable, a byte literal `Lang.Read` cannot spell (not UTF-8, or holding `"`), or a label that is
not an atom has no text (`none`).
-/
import Lang.Package

namespace Nanodregg.Hosting.Text

open Nanodregg.Lang

/-- A label `Lang.Read` reads back as one atom (over `toList`: the kernel reduces it, and
`lifecycle_text_reads` is the kernel evaluating this printer). -/
def atomOk (s : String) : Bool :=
  let cs := s.toList
  !cs.isEmpty && cs.all (fun c => !(c = '(' || c = ')' || c = '"' || c = ';' || c.isWhitespace)) &&
    !cs.all (fun c => c.isDigit || c = '_') && s != "true" && s != "false"

def label (s : String) : Option String := if atomOk s then some s else none

def paren (parts : List String) : String := "(" ++ " ".intercalate parts ++ ")"

mutual
def ty : Ty → Option String
  | .nat => some "nat"
  | .bool => some "bool"
  | .bytes => some "bytes"
  | .fn a b => do pure (paren ["->", ← ty a, ← ty b])
  | .record r => do pure (paren ("rec" :: (← tyRow r)))
  | .sum r => do pure (paren ("sum" :: (← tyRow r)))

def tyRow : List (Label × Ty) → Option (List String)
  | [] => some []
  | (ℓ, t) :: r => do pure (paren [← label ℓ, ← ty t] :: (← tyRow r))
end

def primWord : Prim → String
  | .add => "+" | .sub => "-" | .mul => "*" | .div => "/" | .mod => "%"
  | .eq => "==" | .lt => "<" | .le => "<=" | .beq => "beq" | .cat => "cat"

def name (d : Nat) : String := s!"x{d}"

def bytesLit (b : ByteArray) : Option String := do
  let s ← String.fromUTF8? b
  if s.toList.contains '"' then none else pure ("\"" ++ s ++ "\"")

mutual
/-- Term `t` under `d` binders. -/
def term (d : Nat) : Term → Option String
  | .var i => if i < d then some (name (d - 1 - i)) else none
  | .lam a b => do pure (paren ["lam", name d, ← ty a, ← term (d + 1) b])
  | .app f a => do pure (paren [← term d f, ← term d a])
  | .fix t => do pure (paren ["fix", ← term d t])
  | .nat n => some (toString n)
  | .bool b => some (if b then "true" else "false")
  | .bytes s => bytesLit s
  | .prim p a b => do pure (paren [primWord p, ← term d a, ← term d b])
  | .record fs => do pure (paren ("record" :: (← fields d fs)))
  | .get t ℓ => do pure (paren [".", ← term d t, ← label ℓ])
  | .extend t fs => do pure (paren ("extend" :: (← term d t) :: (← fields d fs)))
  | .inj T ℓ t => do pure (paren ["inj", ← ty T, ← label ℓ, ← term d t])
  | .case t arms => do pure (paren ("case" :: (← term d t) :: (← armsOf d arms)))
  | .ite c a b => do pure (paren ["if", ← term d c, ← term d a, ← term d b])
  | .ref i => some (paren ["ref", toString i])

def fields (d : Nat) : List (Label × Term) → Option (List String)
  | [] => some []
  | (ℓ, t) :: fs => do pure (paren [← label ℓ, ← term d t] :: (← fields d fs))

def armsOf (d : Nat) : List (Label × Term) → Option (List String)
  | [] => some []
  | (ℓ, t) :: arms => do pure (paren [← label ℓ, name d, ← term (d + 1) t] :: (← armsOf d arms))
end

def hex (b : ByteArray) : String :=
  let digit (n : Nat) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)
  String.ofList (b.toList.flatMap fun x => [digit (x.toNat / 16), digit (x.toNat % 16)])

/-- The package's text, one section per line. -/
def package (p : Package) : Option String := do
  let labels (ls : List Label) : Option (List String) := ls.mapM label
  let sections := [
    paren ("imports" :: p.imports.map fun i => "\"" ++ hex i ++ "\""),
    paren ["state", ← ty p.state],
    paren ["iface", ← ty p.iface],
    paren ("methods" :: (← labels p.methods)),
    paren ("laws" :: (← labels p.laws)),
    paren ["body", ← term 0 p.body]]
  pure ("(package\n  " ++ "\n  ".intercalate sections ++ ")\n")

end Nanodregg.Hosting.Text
