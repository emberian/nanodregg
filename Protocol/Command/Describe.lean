/-
# Protocol.Command.Describe — an object describes itself (PROTOCOL-44; DELVETALK-LEARNINGS §4.3)

`read OBJ ?` prints what a member needs in order to call an object it has never seen. That text comes
from the object's package on follow's World, through LANG's own resolution and its one printer, so
the text says exactly what `invoke` will check:

    object HEX
    owner HEX
    package HEX                    (or `data`: an object with no package)
    state TYPE
    method I LABEL ARGTYPE         one per method, I being the index `invoke OBJ I ARGS` names
    call I J TYPE                  method I's declared call slot J (LANG-23)
    law LABEL                      each law of the package
    law HEX LABEL…                 each further law package of the object, with its laws

Each method line is `Lang.resolveMethod`'s answer for that index: the label `invoke` resolves, and
the argument type that `Lang.argsOf` reads ARGS at (`Proofs.Describe.methodLine_resolves`). Each type is
`Lang.Print.ty` of it, which `Lang.Read` reads back. Labels print as they are: install admitted
each method and law label only if `Wire.labelOk` (one atom, at most 64 bytes). If anything has no text, the whole description is
refused `noText`: the printer never guesses, and neither does this.
-/
import Lang.Program
import Lang.Print
import Protocol.Command.Text

namespace Nanodregg.Protocol.Command

open Nanodregg.Kernel Nanodregg.Kernel.Receive

variable {D : Type} [Ord D] [DecidableEq D]

/-- Method `i`'s declared call slots as lines, or `none` if one has no text. -/
def callLines (i : Nat) (ks : List Lang.Ty) : Option (List String) :=
  ks.zipIdx.mapM fun (k, j) => (Lang.Print.ty k).map fun t => s!"call {i} {j} {t}"

/-- Method `i` of `p` as text: its line and its call-slot lines, or `none` if it has no text. -/
def methodLine (p : Lang.Package) (i : Nat) : Option (List String) :=
  match Lang.resolveMethod (D := D) p i with
  | .error _ => none
  | .ok (ℓ, sg) =>
    match Lang.Print.ty sg.arg, callLines i sg.calls with
    | some a, some cs => some (s!"method {i} {ℓ} {a}" :: cs)
    | _, _ => none

/-- A package's description lines: its state, every method in index order, its laws. -/
def packageLines (p : Lang.Package) : Option (List String) := do
  let st ← Lang.Print.ty p.state
  let ms ← (List.range p.methods.length).mapM (methodLine (D := D) p)
  pure ((s!"state {st}" :: ms.flatten) ++ p.laws.map fun ℓ => s!"law {ℓ}")

end Nanodregg.Protocol.Command
