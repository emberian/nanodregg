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
    (check PACKAGE [(with SUPER…)] (view FACT…))
                                 a package with holes, its holes resolved on the stated view:
                                 ok BYTES bytes id HEX hole N candidate I… | refused HOLE-REFUSAL…
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

A package with holes is checked by install's own admission (`admitContextual`, what `checkInstall`
runs once the imports are loaded): every candidate at its hole's context and type, the body with the
holes' signature in scope. Install reads no hole's facts. `(view FACT…)` states the facts a call would
pin, and resolves every hole on them by the function a run prepares its body with
(`instantiateHoles`): each hole's selected candidate, or each blocked hole's refusal, which is the
text a run that demands that hole is refused with. A fact is

    (select HOLE I)          the hole's selection row names candidate I    (select HOLE none): absent
    (row REL KEY VER)        a row of the object at version VER           (row REL KEY none): absent
    (live #ID [(law #L)…] [(runs #P)])   a live cell, its laws in force, the package it runs
    (dead #ID)               a cell pinned and not live (a tombstone)

HOLE is a hole's name (a surface text) or number; REL a relation's label; KEY its key as a record
literal. A cell or row the view does not state is unpinned, as in a call that does not pin it.
-/
import Lang.Print
import Lang.Surface
import Lang.Law
import Kernel.Receive.Call
import Lang.Program
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

/-- A kernel refusal of install, as `ob` prints it: a program refusal by its text, any other by name. -/
def kernelRefused : Refusal Codec.Digest → Answer
  | .program why => no why
  | r => no r.name

/-- A package with holes, by install's admission: the imports given, in order, as its closure. -/
def admitHoles (sups : List Package) (b : ByteArray) (p : Package) : Except Answer Unit :=
  match admitContextual Codec.Digest.ofBytes? (fun _ => unresolvedBody) b p ⟨[], [], sups⟩
      (List.range sups.length) with
  | .ok _ => .ok ()
  | .error r => .error (kernelRefused r)

/-- The package's bytes and id, or the install check's refusal, against the packages it imports. -/
def checkPackageWith (sups : List Package) (p : Package) : Except Answer (ByteArray × String) := do
  let ifaces := sups.map (·.iface)
  unless p.imports.length = ifaces.length do throw (no "imports (a package with imports is checked with its imports: (check P (with Q…)))")
  if p.holes.isEmpty then
    match p.checkWith ifaces with
    | .error e => throw (no e.wire)
    | .ok () =>
      -- install's id-literal check (`Program.checkLits`) at the deployed digest (LANG-38)
      unless p.body.digestLits.all (fun b => (Codec.Digest.ofBytes? b).isSome) do throw (no "notDigest")
  let some b := Wire.encodePackage p | throw (no "packageWire (past the package bounds)")
  unless p.holes.isEmpty do admitHoles sups b p
  pure (b, (romIdOf Codec.Deployed.env { kind := kindPackage, discipline := .rom, slots := [(0, b)] }).toHex)

def checkPackage (p : Package) : Except Answer (ByteArray × String) := checkPackageWith [] p

/-- A refusal of the surface, with the line of `src` it is about. -/
def surfaceRefused (src : String) (e : Surface.Refusal) : Answer := no (e.text src)

def readSub (src : String) (supers : List (ByteArray × Package)) (x : SExp) : Except Answer Surface.Lowered :=
  match Surface.readSExpWith supers x with
  | .ok l => .ok l
  | .error e => .error (surfaceRefused src e)

/-- `p`'s imports, in order, from the packages given. -/
def importsOf (sup : List (ByteArray × Package)) (p : Package) : List Package :=
  p.imports.filterMap fun i => (sup.find? (fun (q : ByteArray × Package) => q.1 = i)).map (·.2)

/-- The supers of a layer, each read and checked in turn (each may itself be a layer over the ones
before it); with their ids' bytes, for `(import N "hex")`. -/
def supersOf (src : String) : List SExp → Except Answer (List (ByteArray × Package))
  | [] => .ok []
  | x :: xs => do
    let sup ← supersOf src xs
    let l ← readSub src sup x
    let (b, _) ← checkPackageWith (importsOf sup l.pkg) l.pkg
    let id := romIdOf Codec.Deployed.env { kind := kindPackage, discipline := .rom, slots := [(0, b)] }
    pure ((id.bytes, l.pkg) :: sup)

/-- The line of the text a hole's refusal is about: the guard of a hole that is not `bool`, the candidate
whose type is not the hole's. -/
def holeSite (l : Surface.Lowered) : HoleRefusal → Option Nat
  | .guardType n => (l.sites.find? fun s => s.1 = n ∧ s.2.1 = none).map (·.2.2)
  | .candidateType n i => (l.sites.find? fun s => s.1 = n ∧ s.2.1 = some i).map (·.2.2)
  | _ => none

/-- Check a lowered package; an `illTyped` refusal names the line of the text its path points to, and a
hole's ill-typed guard or candidate the line it is written on. -/
def checkLowered (src : String) (sups : List Package) (l : Surface.Lowered) : Except Answer (ByteArray × String) :=
  match checkPackageWith sups l.pkg with
  | .ok r => .ok r
  | .error a =>
    if l.pkg.holes.isEmpty then
      match l.pkg.checkWith (sups.map (·.iface)) with
      | .error (.illTyped why) =>
        match Surface.locateField l why.path with
        | some pos => .error (no s!"illTyped {why.text} line {Surface.lineOf src pos}")
        | none => .error a
      | _ => .error a
    else
      match l.pkg.checkContextual (sups.map (·.iface)) with
      | .error e =>
        match holeSite l e with
        | some pos => .error (no s!"{e.wire} line {Surface.lineOf src pos}")
        | none => .error a
      | .ok () => .error a

/-! ## A stated view (LANG-105) -/

/-- What a stated view holds: pinned cells (live, with their slots, or not live) and the hole
object's rows under each relation number (present, or absent). Everything else is unpinned. -/
structure View where
  cells : List (ByteArray × Option Cell) := []
  rows : List (Nat × ByteArray × Option RowLeaf) := []

/-- The caller's pinned cells, as the view states them; any other cell is unpinned. -/
def View.look (v : View) : Pinned Codec.Digest := fun g =>
  match v.cells.find? (·.1 == g.bytes) with
  | some (_, c) => .ok c
  | none => .error (.unpinned g)

/-- The hole object's row pins, as the view states them (the object is the only parent a hole reads). -/
def View.rowView (v : View) : RowView Codec.Digest where
  points _ rel := (v.rows.filter (·.1 == rel)).map fun (_, k, l) => (k, l)
  ranges _ _ := .ok []

/-- A hole by its surface name or its number. -/
def holeOf (l : Surface.Lowered) : SExp → Option HoleROM
  | .atom _ u =>
    let n := match l.holes.find? (·.1 = u) with
      | some (_, n) => some n
      | none => u.toNat?
    n.bind fun n => l.pkg.holes.find? (·.name = n)
  | _ => none

def hexOfAtom : SExp → Except Answer ByteArray
  | .atom p a => match hexBytes? a with
    | some b => .ok b
    | none => .error (readRefused (.notOfType p))
  | x => .error (readRefused (.notOfType x.pos))

/-- A row's leaf: `none` absent, a version present (its value is the selection's index, or empty). -/
def leafOf (val : ByteArray) : SExp → Except Answer (Option RowLeaf)
  | .atom _ "none" => .ok none
  | .atom p v => match v.toNat? with
    | some n => .ok (some (.row 0 val n))
    | none => .error (readRefused (.notOfType p))
  | x => .error (readRefused (.notOfType x.pos))

/-- One fact of a stated view, added to `v`. -/
def factOf (src : String) (l : Surface.Lowered) (v : View) : SExp → Except Answer View
  | .list _ [.atom _ "select", u, .atom r i] => do
    let some h := holeOf l u | throw (no s!"noHole @{u.pos}")
    let leaf ← if i = "none" then pure none else
      match i.toNat?.bind fun k => Wire.encodeData .nat (.nat k) with
      | some b => pure (some (.row 0 b 1))
      | none => throw (readRefused (.notOfType r))
    pure { v with rows := v.rows ++ [(h.selectionRel, h.selectionKey, leaf)] }
  | .list q [.atom _ "row", .atom _ rel, k, ver] => do
    let some ((_, d), i) := l.pkg.rels.zipIdx.find? (·.1.1 = rel) | throw (no s!"noRel @{q} {rel}")
    let key ← match Surface.keyLit d k with
      | .ok b => pure b
      | .error e => throw (surfaceRefused src e)
    pure { v with rows := v.rows ++ [(i, key, ← leafOf .empty ver)] }
  | .list _ (.atom _ "live" :: x :: more) => do
    let id ← hexOfAtom x
    let mut laws : List ByteArray := []
    let mut pkg : List (Nat × ByteArray) := []
    for m in more do
      match m with
      | .list _ [.atom _ "law", y] => laws := laws ++ [← hexOfAtom y]
      | .list _ [.atom _ "runs", y] => pkg := [(slotPackage, ← hexOfAtom y)]
      | y => throw (no s!"badFact @{y.pos}")
    let c : Cell := { kind := 0, discipline := .ram, slots := pkg ++ laws.zipIdx.map fun (b, j) => (lawBase + j, b) }
    pure { v with cells := v.cells ++ [(id, some c)] }
  | .list _ [.atom _ "dead", x] => do pure { v with cells := v.cells ++ [(← hexOfAtom x, none)] }
  | x => .error (no s!"badFact @{x.pos} (select HOLE I) (row REL KEY VER) (live #ID …) (dead #ID)")

/-- A checked package's holes resolved on a stated view: each hole's candidate, or the blocked holes'
refusals (the texts a run that demands them is refused with). -/
def viewAnswer (src : String) (sups : List Package) (l : Surface.Lowered) (b : ByteArray) (id : String)
    (facts : List SExp) : Answer :=
  match facts.foldlM (factOf src l) {} with
  | .error a => a
  | .ok v =>
    match instantiateHoles Codec.Digest.ofBytes? v.look v.rowView Codec.Digest.zero (sups.map (·.iface)) l.pkg with
    | .error e => no e.wire
    | .ok inst =>
      let blocked := inst.resolutions.filterMap fun
        | .blocked _ _ why => some why.wire
        | .selected _ => none
      if blocked.isEmpty then
        ok (s!"ok {b.size} bytes id {id}" ++ String.join (inst.selections.map fun s => s!" hole {s.name} candidate {s.index}"))
      else no ("; ".intercalate blocked)

def answer (src : String) : SExp → Answer
  | .list _ [.atom _ "check", px] =>
    match readSub src [] px >>= checkLowered src [] with
    | .ok (b, id) => ok s!"ok {b.size} bytes id {id}"
    | .error a => a
  | .list _ [.atom _ "check", px, .list _ (.atom _ "with" :: qs)] =>
    match (do
      let sup ← supersOf src qs.reverse
      let l ← readSub src sup px
      checkLowered src (importsOf sup l.pkg) l) with
    | .ok (b, id) => ok s!"ok {b.size} bytes id {id}"
    | .error a => a
  | .list _ [.atom _ "check", px, .list _ (.atom _ "view" :: fs)] =>
    match (do
      let l ← readSub src [] px
      let (b, id) ← checkLowered src [] l
      pure (l, b, id)) with
    | .ok (l, b, id) => viewAnswer src [] l b id fs
    | .error a => a
  | .list _ [.atom _ "check", px, .list _ (.atom _ "with" :: qs), .list _ (.atom _ "view" :: fs)] =>
    match (do
      let sup ← supersOf src qs.reverse
      let l ← readSub src sup px
      let sups := importsOf sup l.pkg
      let (b, id) ← checkLowered src sups l
      pure (sups, l, b, id)) with
    | .ok (sups, l, b, id) => viewAnswer src sups l b id fs
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
  | x => no s!"usage @{x.pos} (check P [(with Q…)] [(view F…)]) (bytes P) (core P) (source P) (type T) (eval TICKS T) (law P LABEL OLD NEW REQ)"

/-- One invocation: the text of one form. -/
def run (text : String) : Answer :=
  if text.utf8ByteSize > inputMax then no s!"tooLarge (over {inputMax} bytes)" else
  match parse text with
  | .error e => readRefused e
  | .ok x => answer text x

end Nanodregg.Lang.Resident
