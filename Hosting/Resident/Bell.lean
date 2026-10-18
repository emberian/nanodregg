/-
# Hosting.Resident.Bell — what the resident decides, as pure functions (HOSTING-27, HOSTING-31)

The resident serves ONE bell (`world/resident/Bell.ob`, LANG-58: a queue of rings) through its
member socket:
- It reads the bell's description once (`read OBJ ?`, PROTOCOL-44). From it come the index of the
  method labelled `answer`, whose argument must be `answerArgTy`, and the relation `pending`, whose
  key must be `(notBefore nat) (ringer digest)` and whose value `(rec (text bytes))`. No index,
  bound or relation layout is written into the program; the read's K is `pending`'s declared limit.
- Each tick it makes ONE read, `read OBJ pending K` (PROTOCOL-51's range read): every unanswered
  ring, one `Lang.Print.data` line per row, read with `Lang.Read.readData` at the relation's row
  type (`Lang.rowTy`). The range read refuses past K and never truncates, so with K the declared
  limit the lines are ALL the pending rings (`Protocol.Proofs.Command.rangeLines_reads`), in
  ascending key order, which is ring order (`Lang.Proofs.KeyOrder.range_keys_ascend_read`).
- It answers the lowest pending ring: `invoke OBJ <answer> ARG`, ARG `Lang.Print.data` of
  `(record (notBefore N) (ringText X) (ringer #H) (text T))`, X the ring's text as the pending row
  holds it. The bell (LANG-59) upserts `rings[k]` to `(answer (some T)) (text X)` and retracts
  `pending[k]`; its `rings` guard refuses the upsert unless the ring is unanswered and X is the
  ring's own text (`rung: answered`, `rung: text`), so exactly-once is a check on the row as it is.

Everything it reads and writes is Lang's one reader and one printer. It holds no copy of either.

**Exactly one ask per ring** (each ask costs the meter). A ring is its key `(notBefore, ringer)`
and its text. An ask is SPENT once its frame has been sent in full. From then on the ring's answer
text is decided, whatever comes back: the reply's text, or a short text naming what came instead.
That text is kept in the resident's volume, with the ring, until the ring leaves `pending`, so
neither a failed invoke nor a restart asks again. A ring that arrives BELOW the kept one (a ringer
may backdate its notBefore by up to the kernel's window) waits until the kept ring is delivered: the
kept ring is answered first wherever it stands, and only then is the lowest asked about
(`Proofs.Resident.decide_*`, over `decideTick`).
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

/-- The argument type of the bell's `answer` (LANG-59): the ring's key, the ring's own text as the
resident read it (`ringText`: the bell's guard refuses the answer unless it equals the ring's), and
the answer text. Labels ascending, as every Lang row (`"ringText" < "ringer"`). -/
def answerArgTy : Ty :=
  .record [("notBefore", .nat), ("ringText", .bytes), ("ringer", .digest), ("text", .bytes)]

/-- The key of the bell's `pending`, in declared order (key bytes follow it, LANG-49/57). -/
def pendingKey : List (Label × Ty) := [("notBefore", .nat), ("ringer", .digest)]

/-- The value of the bell's `pending`: the ring's text, held beside the key so a tick is one read. -/
def pendingVal : Ty := .record [("text", .bytes)]

/-- What the resident needs from the description: `answer`'s index and `pending` as declared,
with the key and value it reads at (so every theorem over a shape has them without a premise). -/
structure Shape where
  answer : Nat
  pending : RelDecl
  key : pending.key = pendingKey
  val : pending.val = pendingVal

/-- The shape from `read OBJ ?`'s lines, or why not. The `method I answer TYPE` line's type is read
by `Lang.Read.readTy`, the `rel (pending …)` line by `Lang.Read.rel`. -/
def Shape.read (out : String) : Except String Shape := do
  let lines := out.splitOn "\n"
  let methods := lines.filterMap fun l => (l.dropPrefix? "method ").map (·.toString.splitOn " ")
  let some (i, ty) := methods.findSome? (fun
      | i :: "answer" :: ty => some (i, " ".intercalate ty)
      | _ => none)
    | throw "noAnswer"
  let some i := i.toNat? | throw "answerIndex"
  match Read.readTy ty with
  | .ok T => unless T = answerArgTy do throw "answerType"
  | .error _ => throw "answerType"
  let rels := lines.filterMap fun l => (l.dropPrefix? "rel ").map (·.toString)
  let some d := rels.findSome? (fun t => match Read.parse t >>= Read.rel with
      | .ok ("pending", d) => some d
      | _ => none)
    | throw "noPending"
  if d.limit = 0 then throw "pendingLimit"
  if hk : d.key = pendingKey then
    if hv : d.val = pendingVal then pure ⟨i, d, hk, hv⟩ else throw "pendingType"
  else throw "pendingType"

/-! ## A ring -/

/-- A pending ring: its key (the signed notBefore it rang at, who rang) and its text. -/
structure Ring where
  notBefore : Nat
  ringer : ByteArray
  text : ByteArray
  deriving DecidableEq

/-- A ring as the range read's row datum: `(record (key (record (notBefore N) (ringer #H))) (val
(record (text T))))`, `Lang.rowTy` of `pending` (`keyTy`'s labels ascending). -/
def Ring.row (r : Ring) : Data :=
  .record [("key", .record [("notBefore", .nat r.notBefore), ("ringer", .digest r.ringer)]),
    ("val", .record [("text", .bytes r.text)])]

/-- The ring in a row datum, or why the datum is not a pending row. -/
def Ring.ofRow : Data → Except String Ring
  | .record [("key", .record [("notBefore", .nat n), ("ringer", .digest g)]),
      ("val", .record [("text", .bytes t)])] => .ok ⟨n, g, t⟩
  | _ => .error "rowFields"

/-- One line of `read OBJ pending K`, read at `pending`'s row type. -/
def Ring.read (sh : Shape) (line : String) : Except String Ring :=
  match Read.readData (rowTy sh.pending) line with
  | .ok v => Ring.ofRow v
  | .error e => .error s!"rowUnread {e.name}"

/-- Every pending ring, in the order the range read lists them (key order: ring order). The
output's lines end in a line feed; a blank line is no row. -/
def Ring.readAll (sh : Shape) (out : String) : Except String (List Ring) :=
  ((out.splitOn "\n").filter (· ≠ "")).mapM (Ring.read sh)

/-! ## Deciding a tick -/

/-- What the resident does this tick. -/
inductive Act
  | idle
  /-- ask keybroker for this ring (a NEW ask: the meter is charged) -/
  | ask (r : Ring)
  /-- answer this pending ring with this text (decided earlier; no ask) -/
  | answer (r : Ring) (text : ByteArray)
  deriving DecidableEq

/-- The decision over every pending ring, lowest first. A kept ring (its answer decided by an
earlier ask) that is still pending is answered with its text, wherever it stands in the queue; with
none, the lowest pending ring is asked about; nothing pending is idle. -/
def decideTick (pending : List Ring) (kept : Option (Ring × ByteArray)) : Act :=
  match kept with
  | some (r, t) => if r ∈ pending then .answer r t else
      match pending with
      | [] => .idle
      | q :: _ => .ask q
  | none =>
      match pending with
      | [] => .idle
      | q :: _ => .ask q

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

/-- The `answer` argument's datum, at `answerArgTy`: the ring's key, the ring's text re-sent, the
answer text. -/
def answerDatum (r : Ring) (t : ByteArray) : Data :=
  .record [("notBefore", .nat r.notBefore), ("ringText", .bytes r.text), ("ringer", .digest r.ringer),
    ("text", .bytes t)]

/-- The `answer` argument for ring `r`, through Lang's one printer. -/
def answerArg (r : Ring) (t : ByteArray) : Option String := Print.data (answerDatum r t)

/-- The ask for a ring: the ring's text as the one user message. -/
def askOf (c : Conf) (r : Ring) : Broker.Ask :=
  { model := c.model, maxTokens := c.maxTokens, system := c.system, roles := ⟨#[0]⟩, texts := [r.text] }

/-! ## What the volume keeps: a ring and its decided answer -/

/-- One kept record: the ring (key and text) and the answer decided for it. -/
def keptTy : Ty :=
  .record [("answer", .bytes), ("notBefore", .nat), ("ringer", .digest), ("text", .bytes)]

def keptDatum (r : Ring) (t : ByteArray) : Data :=
  .record [("answer", .bytes t), ("notBefore", .nat r.notBefore), ("ringer", .digest r.ringer),
    ("text", .bytes r.text)]

def keptText (r : Ring) (t : ByteArray) : Option String := Print.data (keptDatum r t)

def keptRead (s : String) : Option (Ring × ByteArray) :=
  match Read.readData keptTy s with
  | .ok (.record [("answer", .bytes t), ("notBefore", .nat n), ("ringer", .digest g), ("text", .bytes x)]) =>
    some (⟨n, g, x⟩, t)
  | _ => none

/-! ## The member commands (`nd --stdio`'s argv) -/

def hexOf (b : ByteArray) : ByteArray := (Print.hex b).toUTF8

def describeArgv (c : Conf) : List ByteArray := ["read".toUTF8, hexOf c.bell, "?".toUTF8]
/-- `read OBJ pending K`, K = `pending`'s declared limit (the range read refuses past it). -/
def pendingArgv (c : Conf) (sh : Shape) : List ByteArray :=
  ["read".toUTF8, hexOf c.bell, "pending".toUTF8, (toString sh.pending.limit).toUTF8]
def invokeArgv (c : Conf) (sh : Shape) (arg : String) : List ByteArray :=
  ["invoke".toUTF8, hexOf c.bell, (toString sh.answer).toUTF8, arg.toUTF8, "--via".toUTF8, hexOf c.grant]

end Nanodregg.Hosting.Resident
