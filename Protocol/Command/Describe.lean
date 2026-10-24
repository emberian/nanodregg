/-
# Protocol.Command.Describe — an object describes itself (PROTOCOL-44; DELVETALK-LEARNINGS §4.3)

`read OBJ ?` prints what a member needs in order to call an object it has never seen. That text comes
from the object's package on follow's World, through LANG's own resolution and its one printer, so
the text says exactly what `invoke` will check:

    object HEX
    owner HEX
    package HEX                    (or `data`: an object with no package)
    core HEX                       the package cell's bytes, the ones `Lang.readPackage` decodes
                                   (`Lang.Print.hex`): a reader can check WHICH program it calls,
                                   not only its interface (HOSTING-45: the resident checks the Bell)
    doc "TEXT"                     what the package says of itself (LANG-60; `Lang.Print.bytesText` of
                                   its doc, one line, which `Lang.Read` reads back); no line when empty
    state TYPE
    method I LABEL ARGTYPE         one per method, I being the index `invoke OBJ I ARGS` names
    call I J TYPE                  method I's declared call slot J (LANG-23)
    law LABEL                      each law of the package
    rel (LABEL (key …) (val T) …)  each relation of the package (`Lang.Print.relSx`): its key's
                                   fields in DECLARED order (a range prefix is the first ones) and
                                   its `limit` (the most `read OBJ REL K` lists, PROTOCOL-51)
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

/-- A line holds no line break: what `describe` requires of every line it prints. -/
def noBreak (s : String) : Bool := !s.toList.contains '\n'

/-- Method `i` of `p` as text: its line and its call-slot lines, or `none` if it has no text. The
label must be one atom (`Lang.labelAtom`: no space, so the line's words are its index, its label and
its type) and the argument type well formed (`Lang.Ty.wf`: what `Lang.Read.readTy` reads back,
`Lang.Print.readTy_ty`), so the line says the method's argument type exactly (HOSTING-43). -/
def methodLine (p : Lang.Package) (i : Nat) : Option (List String) :=
  match Lang.resolveMethod (D := D) p i with
  | .error _ => none
  | .ok (ℓ, sg) =>
    if Lang.labelAtom ℓ && sg.arg.wf then
      match Lang.Print.ty sg.arg, callLines i sg.calls with
      | some a, some cs => some (s!"method {i} {ℓ} {a}" :: cs)
      | _, _ => none
    else none

/-- A relation as text: LANG's own printer's (`Lang.Print.relSx`, the form `Lang.Read` reads). -/
def relLine (r : Lang.Label × Lang.RelDecl) : Option String :=
  ((Lang.Print.relSx r).bind Lang.Print.fits).map fun t => s!"rel {t}"

/-- The package's doc as a line (LANG-60): LANG's printer's text of it; none for the empty doc. -/
def docLines (p : Lang.Package) : List String :=
  if p.doc.isEmpty then [] else [s!"doc {Lang.Print.bytesText p.doc}"]

/-- A package's description lines: its doc, its state, every method in index order, its laws, its
relations. -/
def packageLines (p : Lang.Package) : Option (List String) := do
  let st ← Lang.Print.ty p.state
  let ms ← (List.range p.methods.length).mapM (methodLine (D := D) p)
  let rs ← p.rels.mapM relLine
  pure (docLines p ++ (s!"state {st}" :: ms.flatten) ++ p.laws.map (fun ℓ => s!"law {ℓ}") ++ rs)

end Nanodregg.Protocol.Command
