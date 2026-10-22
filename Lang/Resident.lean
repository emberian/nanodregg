/-
# Lang.Resident — what a resident checks before it installs: `ob FORM`

One s-expression form in, one line out, no admission and no World. Every answer comes from the
functions admission itself runs: `Read` (the one reader), `Package.checkWith` and the id-literal
check (the install check, at the deployed digest),
`Wire.encodePackage` (the bytes `install` carries), KERNEL's `romIdOf` under CODEC's deployed `Env`
(the id the package cell will have), the one evaluator under a tick budget, and `runLaw` (the one
law runner the receiver calls). Refusals are printed by NAME, with the offset or label they are
about.

    (check PACKAGE)              ok BYTES bytes id HEX     | refused NAME … [line N]
    (check PACKAGE (with SUPER…)) a layer, checked against the packages it imports
    (bytes PACKAGE)              hex of the package bytes  | refused NAME …
    (core PACKAGE)               the core text a surface package lowers to
    (source PACKAGE)             id HEX source DIGEST: what this text installs, and the text's own digest
    (type TERM)                  the closed term's type    | refused illTyped
    (eval TICKS TERM)            VALUE : TYPE used N of TICKS | fault NAME after N of TICKS
    (law PACKAGE LABEL OLD NEW REQ)   admitted | refused "REASON" | fault NAME
                                 (OLD/NEW read at the package's state type, REQ at `reqTy`)

PACKAGE is a core text or a surface text (`Lang.Surface`, LANG-50): a surface package is lowered,
printed and read again by the one reader, and a refusal names the line of the text it is about
(`refused illTyped noField @reply.body.body.body.body.target line 5`). A package with imports is
checked only against the packages given after `with` (a layer's super), in order; this tool reads
no World. The id is the deployed one.
-/
import Lang.Print
import Lang.Surface
import Lang.Law
import Kernel.Receive.Call
import Codec.Deployed

namespace Nanodregg.Lang.Resident

open Nanodregg.Kernel Nanodregg.Kernel.Receive Read

/-- The most input one invocation reads, in bytes. -/
def inputMax : Nat := 1048576

open Print (hex)

def faultName : Fault → String
  | .stuck => "stuck" | .overflow => "overflow" | .underflow => "underflow"
  | .divZero => "divZero" | .tooLarge => "tooLarge" | .ticks => "ticks" | .stack => "stack"
  | .refused w => s!"refused {(String.fromUTF8? w).getD (Print.hex w)}"

/-- An answer: the line, and whether it is a refusal (the exit status). -/
structure Answer where
  line : String
  refused : Bool

def ok (line : String) : Answer := ⟨line, false⟩
def no (line : String) : Answer := ⟨s!"refused {line}", true⟩

def readRefused (e : ReadRefusal) : Answer := no e.text

/-- A type or value with no text: a label that is not one atom (`Print`). -/
def unprintable : Answer := no "unprintable (a label that is not one atom)"

/-- The package's bytes and id, or the install check's refusal, against the imports' interfaces. -/
def checkPackageWith (ifaces : List Ty) (p : Package) : Except Answer (ByteArray × String) := do
  unless p.imports.length = ifaces.length do throw (no "imports (a package with imports is checked with its imports: (check P (with Q…)))")
  match p.checkWith ifaces with
  | .error e => throw (no e.wire)
  | .ok () =>
    -- install's id-literal check (`Program.checkLits`) at the deployed digest (LANG-38)
    unless p.body.digestLits.all (fun b => (Codec.Digest.ofBytes? b).isSome) do throw (no "notDigest")
    match Wire.encodePackage p with
    | none => throw (no "packageWire (past the package bounds)")
    | some b =>
      let id := romIdOf Codec.Deployed.env { kind := kindPackage, discipline := .rom, slots := [(0, b)] }
      pure (b, id.toHex)

def checkPackage (p : Package) : Except Answer (ByteArray × String) := checkPackageWith [] p

/-- A refusal of the surface, with the line of `src` it is about. -/
def surfaceRefused (src : String) (e : Surface.Refusal) : Answer := no (e.text src)

def readSub (src : String) (supers : List (ByteArray × Package)) (x : SExp) : Except Answer Surface.Lowered :=
  match Surface.readSExpWith supers x with
  | .ok l => .ok l
  | .error e => .error (surfaceRefused src e)

/-- The interfaces of `p`'s imports, from the packages given. -/
def ifacesOf (sup : List (ByteArray × Package)) (p : Package) : List Ty :=
  p.imports.filterMap fun i => (sup.find? (fun (q : ByteArray × Package) => q.1 = i)).map fun q => q.2.iface

/-- The supers of a layer, each read and checked in turn (each may itself be a layer over the ones
before it); with their ids' bytes, for `(import N "hex")`. -/
def supersOf (src : String) : List SExp → Except Answer (List (ByteArray × Package) × List Ty)
  | [] => .ok ([], [])
  | x :: xs => do
    let (sup, ifs) ← supersOf src xs
    let l ← readSub src sup x
    let (b, _) ← checkPackageWith (ifacesOf sup l.pkg) l.pkg
    let id := romIdOf Codec.Deployed.env { kind := kindPackage, discipline := .rom, slots := [(0, b)] }
    pure ((id.bytes, l.pkg) :: sup, l.pkg.iface :: ifs)

/-- Check a lowered package; an `illTyped` refusal names the line of the text its path points to. -/
def checkLowered (src : String) (ifaces : List Ty) (l : Surface.Lowered) : Except Answer (ByteArray × String) :=
  match checkPackageWith ifaces l.pkg with
  | .ok r => .ok r
  | .error a =>
    match l.pkg.checkWith ifaces with
    | .error (.illTyped why) =>
      match Surface.locateField l why.path with
      | some pos => .error (no s!"illTyped {why.text} line {Surface.lineOf src pos}")
      | none => .error a
    | _ => .error a

def answer (src : String) : SExp → Answer
  | .list _ [.atom _ "check", px] =>
    match readSub src [] px >>= checkLowered src [] with
    | .ok (b, id) => ok s!"ok {b.size} bytes id {id}"
    | .error a => a
  | .list _ [.atom _ "check", px, .list _ (.atom _ "with" :: qs)] =>
    match (do
      let (sup, _) ← supersOf src qs.reverse
      let l ← readSub src sup px
      checkLowered src (ifacesOf sup l.pkg) l) with
    | .ok (b, id) => ok s!"ok {b.size} bytes id {id}"
    | .error a => a
  | .list _ [.atom _ "bytes", px] =>
    match readSub src [] px >>= checkLowered src [] with
    | .ok (b, _) => ok (hex b)
    | .error a => a
  | .list _ [.atom _ "core", px] =>
    match readSub src [] px with
    | .error a => a
    | .ok l => match Print.package l.pkg with
      | some t => ok t
      | none => unprintable
  | .list _ [.atom _ "source", px] =>
    match readSub src [] px >>= checkLowered src [] with
    | .error a => a
    | .ok (_, id) =>
      -- the package's own text: from its `(` to the `)` that closes `(source …)`, excluded
      let rest := (src.toList.drop px.pos).reverse.dropWhile Char.isWhitespace
      let body := String.ofList ((rest.drop 1).dropWhile Char.isWhitespace).reverse
      ok s!"id {id} source {(Codec.Deployed.env.hash Surface.domSource body.toUTF8).toHex}"
  | .list _ [.atom _ "type", tx] =>
    match term depthMax [] tx with
    | .error e => readRefused e
    | .ok t => match inferE [] [] t (Ω := []) with
      | .ok T => match Print.ty T with
        | some s => ok s
        | none => unprintable
      | .error e => no s!"illTyped {e.text}"
  | .list _ [.atom _ "eval", .atom p n, tx] =>
    match n.toNat?, term depthMax [] tx with
    | none, _ => readRefused (.notOfType p)
    | _, .error e => readRefused e
    | some ticks, .ok t =>
      match inferE [] [] t (Ω := []) with
      | .error e => no s!"illTyped {e.text}"
      | .ok T =>
        match eval [] ticks t with
        | .fault f used => no s!"fault {faultName f} after {used} of {ticks}"
        | .value v used =>
          if T.isData then
            match (Machine.mk []).extract T (ticks - used) v with
            | .ok (d, left) => match Print.data d, Print.ty T with
              | some v, some s => ok s!"{v} : {s} used {ticks - left} of {ticks}"
              | _, _ => unprintable
            | .error f => no s!"fault {faultName f} extracting, {ticks} ticks"
          else match Print.ty T with
            | some s => ok s!"<{s}> used {used} of {ticks}"
            | none => unprintable
  | .list _ [.atom _ "law", px, .atom _ ℓ, ox, nx, rx] =>
    match readSub src [] px >>= fun l => (checkLowered src [] l).map fun _ => l.pkg with
    | .error a => a
    | .ok p =>
      if ¬ ℓ ∈ p.laws then no s!"noLaw {ℓ}" else
      match dataAt depthMax p.state ox, dataAt depthMax p.state nx, dataAt depthMax reqTy rx with
      | .error e, _, _ | _, .error e, _ | _, _, .error e => readRefused e
      | .ok o, .ok n, .ok r =>
        match runLaw [p.body] (.get (.ref 0) ℓ) o n r with
        | .ok (.ok ()) => ok "admitted"
        | .ok (.error why) => no s!"\"{(String.fromUTF8? why).getD (hex why)}\""
        | .error f => no s!"fault {faultName f}"
  | x => no s!"usage @{x.pos} (check P [(with Q…)]) (bytes P) (core P) (source P) (type T) (eval TICKS T) (law P LABEL OLD NEW REQ)"

/-- One invocation: the text of one form. -/
def run (text : String) : Answer :=
  if text.utf8ByteSize > inputMax then no s!"tooLarge (over {inputMax} bytes)" else
  match parse text with
  | .error e => readRefused e
  | .ok x => answer text x

end Nanodregg.Lang.Resident
