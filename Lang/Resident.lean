/-
# Lang.Resident — what a resident checks before it installs: `ob FORM`

One s-expression form in, one line out, no admission and no World. Every answer comes from the
functions admission itself runs: `Read` (the one reader), `Package.checkWith` (the install check),
`Wire.encodePackage` (the bytes `install` carries), KERNEL's `romIdOf` under CODEC's deployed `Env`
(the id the package cell will have), the one evaluator under a tick budget, and `runLaw` (the one
law runner the receiver calls). Refusals are printed by NAME, with the offset or label they are
about.

    (check PACKAGE)              ok BYTES bytes id HEX     | refused NAME …
    (bytes PACKAGE)              hex of the package bytes  | refused NAME …
    (type TERM)                  the closed term's type    | refused illTyped
    (eval TICKS TERM)            VALUE : TYPE used N of TICKS | fault NAME after N of TICKS
    (law PACKAGE LABEL OLD NEW REQ)   admitted | refused "REASON" | fault NAME
                                 (OLD/NEW read at the package's state type, REQ at `reqTy`)

A package with imports cannot be checked here: the imports' interfaces live in the World, and this
tool reads none (`refused imports`). The id is the deployed one only for an import-free package,
which is exactly what it can check.
-/
import Lang.Read
import Lang.Law
import Kernel.Receive.Call
import Codec.Deployed

namespace Nanodregg.Lang.Resident

open Nanodregg.Kernel Nanodregg.Kernel.Receive Read

/-- The most input one invocation reads, in bytes. -/
def inputMax : Nat := 1048576

def hex (b : ByteArray) : String :=
  let digit (n : UInt8) : Char := if n < 10 then Char.ofNat (48 + n.toNat) else Char.ofNat (87 + n.toNat)
  b.foldl (fun s x => (s.push (digit (x >>> 4))).push (digit (x &&& 15))) ""

mutual
/-- Data as the literal `Read.dataAt` reads back (bytes that are not quote-free UTF-8 print as
`#hex`, which the reader reads at type `bytes`). -/
def showData : Data → String
  | .nat n => toString n
  | .bool b => if b then "true" else "false"
  | .bytes s => match String.fromUTF8? s with
    | some t => if t.any (· = '"') then s!"#{hex s}" else s!"\"{t}\""
    | none => s!"#{hex s}"
  | .record fs => s!"(record{showFields fs})"
  | .inj ℓ d => s!"({ℓ} {showData d})"

def showFields : List (Label × Data) → String
  | [] => ""
  | (ℓ, d) :: fs => s!" ({ℓ} {showData d}){showFields fs}"
end

def faultName : Fault → String
  | .stuck => "stuck" | .overflow => "overflow" | .underflow => "underflow"
  | .divZero => "divZero" | .tooLarge => "tooLarge" | .ticks => "ticks" | .stack => "stack"

/-- An answer: the line, and whether it is a refusal (the exit status). -/
structure Answer where
  line : String
  refused : Bool

def ok (line : String) : Answer := ⟨line, false⟩
def no (line : String) : Answer := ⟨s!"refused {line}", true⟩

def readRefused (e : ReadRefusal) : Answer := no e.text

/-- The package's bytes and id, or the install check's refusal. -/
def checkPackage (p : Package) : Except Answer (ByteArray × String) := do
  unless p.imports.isEmpty do throw (no "imports (a package with imports is checked by install)")
  match p.checkWith [] with
  | .error e => throw (no e.wire)
  | .ok () =>
    match Wire.encodePackage p with
    | none => throw (no "packageWire (past the package bounds)")
    | some b =>
      let id := romIdOf Codec.Deployed.env { kind := kindPackage, discipline := .rom, slots := [(0, b)] }
      pure (b, id.toHex)

def readSub (x : SExp) : Except Answer Package :=
  match package x with
  | .ok p => .ok p
  | .error e => .error (readRefused e)

def answer : SExp → Answer
  | .list _ [.atom _ "check", px] =>
    match readSub px >>= checkPackage with
    | .ok (b, id) => ok s!"ok {b.size} bytes id {id}"
    | .error a => a
  | .list _ [.atom _ "bytes", px] =>
    match readSub px >>= checkPackage with
    | .ok (b, _) => ok (hex b)
    | .error a => a
  | .list _ [.atom _ "type", tx] =>
    match term depthMax [] tx with
    | .error e => readRefused e
    | .ok t => match inferE [] [] t with
      | .ok T => ok (showTy T)
      | .error e => no s!"illTyped {e.text}"
  | .list _ [.atom _ "eval", .atom p n, tx] =>
    match n.toNat?, term depthMax [] tx with
    | none, _ => readRefused (.notOfType p)
    | _, .error e => readRefused e
    | some ticks, .ok t =>
      match inferE [] [] t with
      | .error e => no s!"illTyped {e.text}"
      | .ok T =>
        match eval [] ticks t with
        | .fault f used => no s!"fault {faultName f} after {used} of {ticks}"
        | .value v used =>
          if T.isData then
            match (Machine.mk []).extract T (ticks - used) v with
            | .ok (d, left) => ok s!"{showData d} : {showTy T} used {ticks - left} of {ticks}"
            | .error f => no s!"fault {faultName f} extracting, {ticks} ticks"
          else ok s!"<{showTy T}> used {used} of {ticks}"
  | .list _ [.atom _ "law", px, .atom _ ℓ, ox, nx, rx] =>
    match readSub px >>= fun p => (checkPackage p).map fun _ => p with
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
  | x => no s!"usage @{x.pos} (check P) (bytes P) (type T) (eval TICKS T) (law P LABEL OLD NEW REQ)"

/-- One invocation: the text of one form. -/
def run (text : String) : Answer :=
  if text.utf8ByteSize > inputMax then no s!"tooLarge (over {inputMax} bytes)" else
  match parse text with
  | .error e => readRefused e
  | .ok x => answer x

end Nanodregg.Lang.Resident
