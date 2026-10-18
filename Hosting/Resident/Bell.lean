/-
# Hosting.Resident.Bell — what the resident decides, as pure functions (HOSTING-27)

The resident serves ONE bell (`world/resident/Bell.ob`, LANG-52) through its member socket:
- It reads the bell's description once (`read OBJ ?`, PROTOCOL-44). From it come the state type and
  the index of the method labelled `answer`, whose argument must be `(rec (text bytes))`. No index
  or state type is written into the program.
- Each tick it reads the bell's state, the ONE line `read OBJ` prints (PROTOCOL-48), with
  `Lang.Read.readData` at that state type.
- When a ring is pending, it asks keybroker once, with the ring's text as the one user message.
- It answers with `invoke OBJ <answer> ARG`, where ARG is `Lang.Print.data` of `(record (text T))`.

Everything it reads and writes is Lang's one reader and one printer. It holds no copy of either.

**Exactly one ask per ring** (each ask costs the meter). An ask is SPENT once its frame has been sent
in full. From then on the ring's answer text is decided, whatever comes back: the reply's text, or
a short text naming what came instead (a refusal, a status, an unanswered or undecodable answer).
That text is kept in the resident's volume until the bell takes it, so neither a failed invoke nor
a restart asks again (`Proofs.Resident.decide_*`, over `decideTick`).
-/
import Lang.Read
import Lang.Print
import Hosting.BrokerWire

namespace Nanodregg.Hosting.Resident

open Nanodregg.Lang

/-! ## The config: `pkg/resident.conf`, one Lang data value -/

/-- The config's type. The operator writes one value of it beside the program:
`(record (bell #HEX) (grant #HEX) (maxTokens N) (model "NAME") (system "TEXT"))`, where `grant` is
the operator's grant to the resident's member that `invoke` names (`--via`). -/
def confTy : Ty :=
  .record [("bell", .digest), ("grant", .digest), ("maxTokens", .nat), ("model", .bytes), ("system", .bytes)]

/-- The largest config file read. -/
def confBytesMax : Nat := 65536

structure Conf where
  /-- the bell object's id (32 bytes) -/
  bell : ByteArray
  /-- the grant the answer is invoked through (32 bytes) -/
  grant : ByteArray
  maxTokens : Nat
  model : ByteArray
  system : ByteArray

/-- The config from its text; `none` names `confMalformed`. -/
def Conf.read (text : String) : Option Conf :=
  match Read.readData confTy text with
  | .ok (.record [("bell", .digest b), ("grant", .digest g), ("maxTokens", .nat n), ("model", .bytes m),
      ("system", .bytes s)]) =>
    if b.size = 32 ∧ g.size = 32 then some ⟨b, g, n, m, s⟩ else none
  | _ => none

/-! ## The description -/

/-- The argument type of the bell's `answer`. -/
def answerArgTy : Ty := .record [("text", .bytes)]

/-- What the resident needs from the description: the state type and `answer`'s index. -/
structure Shape where
  state : List (Label × Ty)
  answer : Nat

/-- The fields the resident reads, at the types it reads them. -/
def stateNeeds : List (Label × Ty) := [("pending", .bool), ("ring", .bytes), ("ringer", .digest)]

/-- The shape from `read OBJ ?`'s lines, or why not. The `state` line's type and the `method I
answer TYPE` line are read by `Lang.Read.readTy`. -/
def Shape.read (out : String) : Except String Shape := do
  let lines := out.splitOn "\n"
  let some st := lines.findSome? (fun l => (l.dropPrefix? "state ").map (·.toString))
    | throw "noState"
  let .ok (.record row) := Read.readTy st | throw "stateNotRecord"
  unless stateNeeds.all (fun (ℓ, T) => Row.find? ℓ row == some T) do throw "stateFields"
  let methods := lines.filterMap fun l => (l.dropPrefix? "method ").map (·.toString.splitOn " ")
  let some (i, ty) := methods.findSome? (fun
      | i :: "answer" :: ty => some (i, " ".intercalate ty)
      | _ => none)
    | throw "noAnswer"
  let some i := i.toNat? | throw "answerIndex"
  match Read.readTy ty with
  | .ok T => unless T = answerArgTy do throw "answerType"
  | .error _ => throw "answerType"
  pure ⟨row, i⟩

/-! ## A ring -/

/-- A pending ring: who rang, and the text. -/
structure Ring where
  ringer : ByteArray
  text : ByteArray
  deriving DecidableEq

/-- The pending ring in a state value, `none` when nothing is pending, or why the value is not one
the resident can read. -/
def Ring.ofState (v : Data) : Except String (Option Ring) :=
  match v with
  | .record fs =>
    match Row.find? "pending" fs, Row.find? "ring" fs, Row.find? "ringer" fs with
    | some (.bool false), _, _ => .ok none
    | some (.bool true), some (.bytes t), some (.digest r) => .ok (some ⟨r, t⟩)
    | _, _, _ => .error "stateFields"
  | _ => .error "stateNotRecord"

/-- The pending ring in `read OBJ`'s line, read at the described state type. -/
def Ring.read (sh : Shape) (line : String) : Except String (Option Ring) :=
  match Read.readData (.record sh.state) line with
  | .ok v => Ring.ofState v
  | .error e => .error s!"stateUnread {e.name}"

/-! ## Deciding a tick -/

/-- What the resident does this tick. -/
inductive Act
  | idle
  /-- ask keybroker for this ring (a NEW ask: the meter is charged) -/
  | ask (r : Ring)
  /-- answer the pending ring with this text (decided earlier; no ask) -/
  | answer (text : ByteArray)
  deriving DecidableEq

/-- The decision: nothing pending is idle; a ring whose answer is already decided (`kept`, from an
earlier ask) is answered with it; any other ring is asked about. -/
def decideTick (pending : Option Ring) (kept : Option (Ring × ByteArray)) : Act :=
  match pending, kept with
  | none, _ => .idle
  | some r, some (r', t) => if r = r' then .answer t else .ask r
  | some r, none => .ask r

/-! ## The answer -/

/-- The longest answer text: the bell's `answer` takes text of 1..2000 bytes (LANG-52). The
description shows the argument's type, not its bound. So this is the one copy of the bound, and a
text the bell still refuses ends the resident by that refusal's name, never as a second ask. -/
def textMax : Nat := 2000

/-- Whether a byte continues a UTF-8 sequence (`10xxxxxx`). -/
def continues (b : UInt8) : Bool := b &&& 0xC0 == 0x80

/-- `t`'s longest prefix of at most `n` bytes that ends on a UTF-8 boundary. -/
def utf8Prefix (t : ByteArray) (n : Nat) : ByteArray :=
  if t.size ≤ n then t else go n
where
  go : Nat → ByteArray
    | 0 => ByteArray.empty
    | k + 1 => if continues t[k + 1]! then go k else t.extract 0 (k + 1)

/-- What the resident answers when the ask brought no reply text: a short text naming it. -/
def named (what : String) : ByteArray := s!"({what})".toUTF8

/-- A text the bell takes: cut to `textMax` at a UTF-8 boundary; an empty one is named
(`Proofs.Resident.fit_size`: always 1..`textMax` bytes). -/
def fit (t : ByteArray) : ByteArray :=
  let u := utf8Prefix t textMax
  if u.isEmpty then named "empty reply" else u

/-- The answer text for what keybroker answered: the reply, or a short text naming the refusal or
the status, each fitted. -/
def answerText : Broker.Answer → ByteArray
  | .reply t => fit t
  | .refused why => fit (named s!"refused {why.name}")
  | .status c => fit (named s!"status {c}")

/-- The `answer` argument: `(record (text T))` through Lang's one printer. -/
def answerArg (t : ByteArray) : Option String := Print.data (.record [("text", .bytes t)])

/-- The ask for a ring: the ring's text as the one user message. -/
def askOf (c : Conf) (r : Ring) : Broker.Ask :=
  { model := c.model, maxTokens := c.maxTokens, system := c.system, roles := ⟨#[0]⟩, texts := [r.text] }

/-! ## What the volume keeps: a ring and its decided answer -/

def keptTy : Ty := .record [("ring", .bytes), ("ringer", .digest), ("text", .bytes)]

def keptText (r : Ring) (t : ByteArray) : Option String :=
  Print.data (.record [("ring", .bytes r.text), ("ringer", .digest r.ringer), ("text", .bytes t)])

def keptRead (s : String) : Option (Ring × ByteArray) :=
  match Read.readData keptTy s with
  | .ok (.record [("ring", .bytes x), ("ringer", .digest g), ("text", .bytes t)]) => some (⟨g, x⟩, t)
  | _ => none

/-! ## The member commands (`nd --stdio`'s argv) -/

def hexOf (b : ByteArray) : ByteArray := (Print.hex b).toUTF8

def describeArgv (c : Conf) : List ByteArray := ["read".toUTF8, hexOf c.bell, "?".toUTF8]
def readArgv (c : Conf) : List ByteArray := ["read".toUTF8, hexOf c.bell]
def invokeArgv (c : Conf) (sh : Shape) (arg : String) : List ByteArray :=
  ["invoke".toUTF8, hexOf c.bell, (toString sh.answer).toUTF8, arg.toUTF8, "--via".toUTF8, hexOf c.grant]

end Nanodregg.Hosting.Resident
