/-
# Protocol.Table — the one operation table, as data

Two sockets, six operations. Everything a client or a supervisor needs to know about the wire is
on this page, and CODEC generates the Rust copy from it (law 2): op bytes, status bytes, step tags
and the four client bounds.

* `host.sock` (`host serve STORE`, the one writer): `submit`, `lookup`, `read`, `log`.
* `follow.sock` (`host follow STORE`, the member's own fold): `command`, `resume`.

What is NOT an operation, and where it went (minidregg's 186 opcodes, `DELETE-PROTOCOL-20261016.md`):
every family-specific plan/assemble/submit/lookup quadruple is one `submit`/`lookup` whose payload is
a signed call of some KIND (KERNEL's `Receive`; LANG's `install`/`invoke` are kinds, not ops); every
view is a `read` kind; challenge, prepare, assemble, author, inspect and signatures are steps of the
follow machine (Lean), not wire operations; describe/profile are a `read` kind; certify is the Host's
own seal; consent frames are `host follow` (HOST-7).

Each operation names the one function that answers it (`receiver`). The names are data until the
receiving layers commit those declarations; a gate then resolves each name in the environment.
-/
import Codec.Layout

namespace Nanodregg.Protocol

/-- The two sockets of a deployment. -/
inductive Socket
  | host
  | follow
  deriving DecidableEq, Repr

/-- Whether answering an operation may append to the log. -/
inductive Effect
  | read
  | write
  deriving DecidableEq, Repr

/-- Every operation of the protocol. -/
inductive Op
  /-- a signed call: received into a Turn, admitted, appended; replies with the receipt -/
  | submit
  /-- the same signed call bytes: committed (receipt), absent, or never-admissible -/
  | lookup
  /-- a view of the writer's World, by kind; an authorized view carries a signature -/
  | read
  /-- the log's frames from a height: what a follower folds -/
  | log
  /-- a member's argv, parsed by the one command language -/
  | command
  /-- a continuation echoed back with the result of the step it asked for -/
  | resume
  deriving DecidableEq, Repr

namespace Op

def all : List Op := [submit, lookup, read, log, command, resume]

def code : Op → UInt8
  | submit => 1
  | lookup => 2
  | read => 3
  | log => 4
  | command => 5
  | resume => 6

def socket : Op → Socket
  | submit | lookup | read | log => .host
  | command | resume => .follow

def effect : Op → Effect
  | submit => .write
  | lookup | read | log | command | resume => .read

/-- The declaration that answers the operation. -/
def receiver : Op → String
  | submit => "Nanodregg.Kernel.Receive.receive"
  | lookup => "Nanodregg.Kernel.World.lookup"
  | read => "Nanodregg.Kernel.Receive.view"
  | log => "Nanodregg.Host.Log.framesFrom"
  | command => "Nanodregg.Protocol.Command.start"
  | resume => "Nanodregg.Protocol.Command.step"

/-- The operations a `host` step may ask the client to relay. Not `submit`: a call reaches the
writer only through a `submit` step, which the client freezes as an attempt first (CLIENT-3), so
follow cannot make the client send a call outside the attempt store (PROTOCOL-9). -/
def relayable : List Op := [lookup, read, log]

def name : Op → String
  | submit => "submit" | lookup => "lookup" | read => "read" | log => "log"
  | command => "command" | resume => "resume"

/-- A RESERVED operation is in the table but no row may claim it: a declared absence. `read` is
reserved while Ember's thin-consent ruling is open (HOST-7a): under PROTOCOL-3 every member follows
and reads through its own follow, so nothing sends `read`. If thin members are out, `read` is
deleted (6 → 5); if they are in, a thin-member row sends it and it stops being reserved. -/
def reserved : Op → Bool
  | read => true
  | submit | lookup | log | command | resume => false

/-- Decode a request byte; anything else is refused before a payload is read. -/
def ofCode? (b : UInt8) : Option Op := all.find? (·.code == b)

end Op

/-- The status byte of every reply on either socket. -/
inductive Status
  /-- answered; for `lookup`, committed -/
  | ok
  /-- refused by name; the payload is the refusal -/
  | refused
  /-- the writer cannot say whether the call committed (an append that did not read back) -/
  | uncertain
  /-- `lookup` only: the call is not in the log; resending the same bytes is safe -/
  | absent
  deriving DecidableEq, Repr

namespace Status

def all : List Status := [ok, refused, uncertain, absent]

def code : Status → UInt8
  | ok => 0
  | refused => 1
  | uncertain => 2
  | absent => 3

def ofCode? (b : UInt8) : Option Status := all.find? (·.code == b)

end Status

/-- The tag of a step the follow machine asks the client to perform (CLIENT-2). -/
inductive Step
  /-- print, exit; the command is over -/
  | done
  /-- sign exactly these bytes with custody's key -/
  | sign
  /-- send this frame to `host.sock` and resume with its reply -/
  | host
  /-- freeze this call as an attempt, settle it by submit/lookup, resume with the settlement -/
  | submit
  /-- custody: make sure a PENDING key (the one after the next) exists, durably, before any rotate
  call is frozen; idempotent (a retried command never mints a second one). Result:
  `precommitResultLayout` (CLIENT-13) -/
  | precommit
  /-- custody: sign exactly these bytes with the NEXT key. Result: `signResultLayout` with
  `key` = the next key, `next` = the pending key. It arms the rotation: the following `submit`
  step's attempt is the rotation attempt, and custody advances (current := next, next := pending)
  only on ITS OWN settlement of that attempt as committed, never on a follow step (CLIENT-13) -/
  | signNext
  deriving DecidableEq, Repr

namespace Step

def all : List Step := [done, sign, host, submit, precommit, signNext]

def code : Step → UInt8
  | done => 0
  | sign => 1
  | host => 2
  | submit => 3
  | precommit => 4
  | signNext => 5

def ofCode? (b : UInt8) : Option Step := all.find? (·.code == b)

/-- The fields of each step's frame, after its tag byte (CLIENT-10). `k` is the follow machine's
opaque continuation; the client echoes it back in `resume` and never reads it. -/
def layout : Step → Codec.Layout
  | done => [.byte "exit", .bytes "stdout", .bytes "stderr"]
  | sign => [.bytes "message", .bytes "k"]
  | host => [.oneOf "op" (Op.relayable.map fun o => (o.name, o.code)), .bytes "payload", .bytes "k"]
  | submit => [.bytes "call", .bytes "k"]
  | precommit => [.bytes "k"]
  | signNext => [.bytes "message", .bytes "k"]

end Step

/-- The `command` payload: the member's argv. -/
def commandLayout : Codec.Layout := [.list "argv"]

/-- The `resume` payload: the continuation from the step, and that step's result (the signature
for `sign`; the Host's reply, `u8 status ‖ payload`, for `host` and `submit`). -/
def resumeLayout : Codec.Layout := [.bytes "k", .bytes "result"]

/-- What custody answers to a `sign` step (the `result` of the `resume`): its current public key,
its precommitted NEXT public key (so follow can state the digest a sponsor or a rotation commits
to), and the current key's signature over exactly the step's message. -/
def signResultLayout : Codec.Layout := [.bytes "key", .bytes "next", .bytes "signature"]

/-- What custody answers to a `precommit` step: its NEXT public key and its PENDING public key (the
one a rotation to `next` precommits, by digest). -/
def precommitResultLayout : Codec.Layout := [.bytes "next", .bytes "pending"]

/-- The READ ENVELOPE: the payload of `log` (and `read`). A member's request to read the writer's
log from a height, signed by its current key and gated by its follow grant (PROTOCOL-3, HOST-11):
digests are `Env.bytes`, heights are u64le. The signed message is `Envelope.message` (domain tag,
member, grant, from, validUntil); `validUntil` bounds a replay to a window of heights. -/
def envelopeLayout : Codec.Layout :=
  [.bytes "member", .bytes "grant", .bytes "from", .bytes "validUntil", .bytes "key", .bytes "signature"]

/-- The `log` reply's payload: the signed calls (events) logged from the requested height, in log
order, then the writer's World height and log chain after the last of them, then `tip`, the
writer's World height when the page was built. A follower re-derives every Turn from the events
(PROTOCOL-4) and asserts that its own fold reached the same height and chain (a pair assertion,
law 4): an omitted, truncated or reordered event is caught at the page. A page holds at most a
frame of events (HOST-17), so it may end before the tip, even inside a writer batch: follow pages
again from `height` until `height = tip` (at most `Bounds.pagesPerCommandMax` pages a command). -/
def logReplyLayout : Codec.Layout := [.list "events", .bytes "height", .bytes "chain", .bytes "tip"]

/-- The `read` reply's payload: one page of the World bytes of the writer's NEWEST base (HOST-14,
HOST-15), for a thin member (PROTOCOL-14, option A). The request is the read envelope, its `start`
read as a byte offset into those World bytes. `height` and `chain` are the base World's,
`total` its World bytes' length, `digest` = `Hash.digest "nanodregg/host/base/v1"` of them, and
`bytes` = World bytes `[start, start + chunk)`. All numbers are u64le. A seal between two pages
changes `height` and `digest`, and the member starts its download again. The member trusts none of
it: it accepts the assembled bytes only if they hash to a base digest it pinned out of band
(`Protocol.Thin.accept`; a forged byte is `baseMismatch`). -/
def readReplyLayout : Codec.Layout :=
  [.bytes "height", .bytes "total", .bytes "digest", .bytes "chain", .bytes "bytes"]

/-! The bounds the client and the supervisor enforce before allocating. -/
namespace Bounds

/-- One frame body (op or status byte and payload), either socket, either direction. -/
def frameBytesMax : Nat := 262144
/-- A `command` payload: the argv, `4 + Σ (4 + len)`. -/
def argvBytesMax : Nat := 65536
/-- Steps one command may take before follow ends it with a refusal. -/
def stepsPerCommandMax : Nat := 64
/-- Sends of one frozen call: the first submit and the resends after `absent`. -/
def sendsMax : Nat := 8
/-- `log` pages one command may read while it catches up (two steps each: sign the envelope from
the page's start, relay `log`). A follow further behind than this ends the command `behind`,
keeping what it absorbed, and the member runs it again. With the at most four other steps of any
command it fits `stepsPerCommandMax` (`Bounds.pages_fit_steps`). -/
def pagesPerCommandMax : Nat := 28
/-- Connections one `nd-supervise` holds open at once (either socket). It bounds the supervisor's
memory: each connection buffers at most one frame per direction, so the whole mux holds at most
`2 * connectionsMax * frameBytesMax` bytes (32 MiB). A deployment's members are friends, not the
public: past the bound the supervisor stops accepting, and the client sees a refused connect. -/
def connectionsMax : Nat := 64
/-- A remote (ssh-bridged) connection idle this long, with no frame in either direction, is closed
by the supervisor (PROTOCOL-11). Five minutes: longer than any command's step round trip, and a
slow-loris peer holds one of `connectionsMax` slots for at most this long. -/
def idleMsMax : Nat := 300000

end Bounds

end Nanodregg.Protocol
