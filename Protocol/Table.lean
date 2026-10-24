/-
# Protocol.Table — the one operation table, as data

Two sockets, seven operations. Everything a client or a supervisor needs to know about the wire is
on this page, and CODEC generates the Rust copy from it (law 2): op bytes, status bytes, step tags
and the four client bounds.

* `host.sock` (`host serve STORE`, the one writer): `submit`, `lookup`, `read`, `log`, `cancel`.
* `follow.sock` (`host follow STORE`, the member's own fold): `command`, `resume`.

What is NOT an operation, and where it went (minidregg's 186 opcodes, `DELETE-PROTOCOL-20261016.md`):
every family-specific plan/assemble/submit/lookup quadruple is one `submit`/`lookup` whose payload is
a signed call of some KIND (KERNEL's `Receive`; LANG's `install`/`invoke` are kinds, not ops); every
view is answered by the member's own follow (its World, caught up from `log`); `read` serves only
the newest base's World bytes, to a thin member (PROTOCOL-14 A); challenge, prepare, assemble,
author, inspect and signatures are steps of the follow machine (Lean), not wire operations; certify
is the Host's own seal; consent frames are `host follow` (HOST-7).

Each operation names the one function that answers it (`receiver`). The names are data until the
receiving layers commit those declarations; a gate then resolves each name in the environment.
-/
import Codec.Layout
import Host.Bounds

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
  /-- a page of the writer's newest base, for a thin member (PROTOCOL-14 A, `readReplyLayout`) -/
  | read
  /-- the log's frames from a height: what a follower folds -/
  | log
  /-- a member's argv, parsed by the one command language -/
  | command
  /-- a continuation echoed back with the result of the step it asked for -/
  | resume
  /-- a member's cancel of its own call (`cancelEvent`: its signature over `domCancel ‖ txId` and
  the call's bytes): recorded `refused cancelled` inside the call's window, or declined by name
  (KERNEL-60, design C1) -/
  | cancel
  deriving DecidableEq, Repr

namespace Op

def all : List Op := [submit, lookup, read, log, command, resume, cancel]

def code : Op → UInt8
  | submit => 1
  | lookup => 2
  | read => 3
  | log => 4
  | command => 5
  | resume => 6
  | cancel => 7

def socket : Op → Socket
  | submit | lookup | read | log | cancel => .host
  | command | resume => .follow

def effect : Op → Effect
  | submit | cancel => .write
  | lookup | read | log | command | resume => .read

/-- The declaration that answers the operation. -/
def receiver : Op → String
  | submit => "Nanodregg.Kernel.Receive.receive"
  | lookup => "Nanodregg.Kernel.World.lookup"
  | read => "Nanodregg.Host.Page.basePage"
  | log => "Nanodregg.Host.Page.build"
  | command => "Nanodregg.Protocol.Command.start"
  | resume => "Nanodregg.Protocol.Command.step"
  | cancel => "Nanodregg.Kernel.Receive.cancel"

/-- The operations a `host` step may ask the client to relay. Not `submit`: a call reaches the
writer only through a `submit` step, which the client freezes as an attempt first (CLIENT-3), so
follow cannot make the client send a call outside the attempt store (PROTOCOL-9). `cancel` is
relayable: its payload carries a call's bytes, but the writer only ever records that call
`refused cancelled` or declines (`Receive.cancel` admits nothing), and a lost cancel reply needs no
attempt: the member's next `cancel` of the same call catches up and is answered by its own follow
(`refusedFinal` once recorded). -/
def relayable : List Op := [lookup, read, log, cancel]

def name : Op → String
  | submit => "submit" | lookup => "lookup" | read => "read" | log => "log"
  | command => "command" | resume => "resume" | cancel => "cancel"

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
  /-- the supervisor (or `nd-attach`) closed this connection; the payload is the `CloseReason`'s
  name, and nothing follows on the connection. Not a verdict on any request: a request in flight
  is unsettled (for a frozen call, uncertain: its attempt goes on by lookup) -/
  | closed
  /-- `submit` only: refused by name and NOT recorded, so NOT final (PROTOCOL-41, KERNEL-47
  amendment 7). The payload is the name. The call was not authenticated for this World (an
  unauthenticated code), or its window has not opened (an early `outsideWindow`), or its member's
  refusals this window are spent (`refusalBudget`), or the World's are (`refusalsFull`, KERNEL-55 R1). The same bytes may still be admitted later (a
  call signed with the precommitted next key is `unknownKey` until the rotate, and admissible after it),
  so the attempt stays open. A `refused` reply is the final one: the refusal is recorded, or was
  recorded before, or the call's window has passed -/
  | declined
  deriving DecidableEq, Repr

namespace Status

def all : List Status := [ok, refused, uncertain, absent, closed, declined]

def code : Status → UInt8
  | ok => 0
  | refused => 1
  | uncertain => 2
  | absent => 3
  | closed => 4
  | declined => 5

def ofCode? (b : UInt8) : Option Status := all.find? (·.code == b)

end Status

/-- The name a page is refused by when the writer's IO failed while building it (HOST-48): the
writer refuses THAT page and serves on, so it says "not now", never "never". A follower that reads it
ends its command restart-class (`CommandExit.pageIo`) and runs again; it is none of the read gate's
names (`Host.pageIoName_fresh`). -/
def pageIoName : String := "pageIo"

/-- Why a connection was closed (law 7: every close is named to the peer, `Status.closed ‖ name`).
The supervisor's mux decides WHEN, against the `Bounds` below; this is the whole vocabulary. -/
inductive CloseReason
  /-- silent at a frame boundary with no request in flight for `idleMsMax` -/
  | idle
  /-- a started frame was not complete within `frameMsMax` -/
  | frameStalled
  /-- a frame past `frameBytesMax`, or an empty one -/
  | frameRefused
  /-- a reply arrived while the previous one was still unread: the peer is not reading -/
  | replyBacklog
  /-- writing a reply to the peer failed or took longer than `replyWriteMsMax` -/
  | replyWriteFailed
  /-- a request had no reply for `replyMsMax` (a backstop: the Host owes one reply per request) -/
  | replyTimeout
  /-- `connectionsMax` (or, at `nd-attach`, `peerConnectionsMax`) connections are open -/
  | full
  /-- `nd-attach`: a frame for a connection that already ended -/
  | ended
  /-- nothing behind the socket answers: at `nd-attach`, the Store's socket does not accept a
  connection; at `nd-supervise`, its child's stdout closed (the child is gone), so every open peer is
  closed with this name -/
  | unreachable
  /-- the client ended its stream at a frame boundary; named to the CHILD in its hang-up (there is
  no peer left to tell) -/
  | peerLeft
  /-- the connecting peer's credentials (uid, gid) are not the ones the supervisor was started
  for (`nd-supervise --peer`, HOSTING-20): closed before any frame is read -/
  | peerRefused
  deriving DecidableEq, Repr

namespace CloseReason

def all : List CloseReason :=
  [idle, frameStalled, frameRefused, replyBacklog, replyWriteFailed, replyTimeout, full, ended, unreachable,
   peerLeft, peerRefused]

/-- The name on the wire (`CloseReason.name_injective`). -/
def name : CloseReason → String
  | idle => "idle" | frameStalled => "frameStalled" | frameRefused => "frameRefused"
  | replyBacklog => "replyBacklog" | replyWriteFailed => "replyWriteFailed"
  | replyTimeout => "replyTimeout" | full => "full" | ended => "ended" | unreachable => "unreachable"
  | peerLeft => "peerLeft" | peerRefused => "peerRefused"

/-- The reason a hang-up's payload names (its name in UTF-8), if any. -/
def ofBytes? (b : ByteArray) : Option CloseReason := all.find? (·.name.toUTF8 == b)

end CloseReason

/-! ## The child wire's hang-up (PROTOCOL-23)

Toward the child (`host serve`, `nd-attach`) a frame is `u32 conn ‖ byte ‖ payload`. The byte is a
request's `Op.code`, or `hangupCode`: connection `conn` has ended, and the payload is the ended
connection's `CloseReason` name. A hang-up is not an `Op` (it has no receiver in the op table, so
`every_op_has_a_row` stays about operations); `hangup_not_op` keeps the two apart. The child
acknowledges it by name with `ack`: `Status.closed ‖ the same name` (`ackReason?_ack`). -/

/-- What the byte after a child-wire frame's connection id says. -/
inductive ChildKind
  | request
  | hangup
  deriving DecidableEq, Repr

def hangupCode : UInt8 := 255

/-- `none`: a byte that is neither an op nor `hangupCode`, refused by the Host as `unknownOp`. -/
def childKindOf? (b : UInt8) : Option ChildKind :=
  if b = hangupCode then some .hangup
  else if Op.all.any (·.code == b) then some .request else none

/-- The child's acknowledgement of a hang-up for `r`, as a reply's `status ‖ payload`. -/
def ack (r : CloseReason) : ByteArray := ByteArray.mk #[Status.closed.code] ++ r.name.toUTF8

/-- The reason a `closed` reply names, if it names one. -/
def ackReason? (b : ByteArray) : Option CloseReason := CloseReason.all.find? (ack · == b)

/-- The tag of a step the follow machine asks the client to perform (CLIENT-2). -/
inductive Step
  /-- print, exit; the command is over -/
  | done
  /-- sign exactly these bytes with custody's key -/
  | sign
  /-- send this frame to `host.sock` and resume with its reply -/
  | host
  /-- freeze this call as an attempt, drive it by submit/lookup, settle it by the member's own
  follow (`receipt CALL`, PROTOCOL-46), and resume with the attempt's end: `u8 Action.code ‖
  payload` (`Protocol.Attempt`) -/
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
  /-- custody: sign exactly these bytes, a read envelope's message (`ENVELOPE_DOMAIN`, never a
  call), with the ARMED rotation's incoming key (the next key). Result: `signResultLayout` with
  `key` = the incoming key. Follow asks it ONCE per command of a verb that signs no call, after the
  writer refused its envelope `unknownKey`: the rotation landed and custody has not yet settled it
  (PROTOCOL-46, CLIENT-13 amended). Refused `notArmed` with no armed rotation, `envelopeOnly` for
  any other message, `noRotation` by a resident's custody -/
  | signIncoming
  deriving DecidableEq, Repr

namespace Step

def all : List Step := [done, sign, host, submit, precommit, signNext, signIncoming]

def code : Step → UInt8
  | done => 0
  | sign => 1
  | host => 2
  | submit => 3
  | precommit => 4
  | signNext => 5
  | signIncoming => 6

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
  | signIncoming => [.bytes "message", .bytes "k"]

end Step

/-- The `command` payload: the member's argv. -/
def commandLayout : Codec.Layout := [.list "argv"]

/-- The `resume` payload: the continuation from the step, and that step's result. EVERY result is
`u8 status ‖ payload` (`Status`), but `submit`'s, which is `u8 Action.code ‖ payload` (the attempt's end,
`Protocol.Attempt`, PROTOCOL-46): for `host` the Host's reply; for the custody steps
(`sign`, `signNext`, `signIncoming`, `precommit`) `ok ‖ signResultLayout` / `ok ‖ precommitResultLayout`, or
`refused ‖ custodyRefusalLayout` when custody refuses, so follow ends the command with the
refusal's name instead of the client exiting with a code (CLIENT-2's ask). -/
def resumeLayout : Codec.Layout := [.bytes "k", .bytes "result"]

/-- What custody answers to a `sign` step (the `result` of the `resume`): its current public key,
its precommitted NEXT public key (so follow can state the digest a sponsor or a rotation commits
to), and the current key's signature over exactly the step's message. -/
def signResultLayout : Codec.Layout := [.bytes "key", .bytes "next", .bytes "signature"]

/-- What custody answers to a `precommit` step: its NEXT public key and its PENDING public key (the
one a rotation to `next` precommits, by digest). -/
def precommitResultLayout : Codec.Layout := [.bytes "next", .bytes "pending"]

/-- Why custody refuses a step (CLIENT-2's `CustodyError`, as names on the wire). A custody result
that is `refused` carries exactly one of these (`custodyRefusalLayout`); follow renders it by
name. -/
inductive CustodyRefusal
  /-- a custody file or the holding directory failed the custody checks (mode, owner, kind) -/
  | fileRefused
  /-- a key file already exists where a new one was asked for -/
  | exists
  /-- the workspace has both custody shapes, or neither -/
  | shape
  /-- the separate holding of the next key is not named or not present -/
  | holdingAbsent
  /-- `signNext` without a precommitted pending key -/
  | noPending
  /-- a rotation is already armed; it is settled first -/
  | rotationInFlight
  /-- a key file disagrees with the keys the rotation or the workspace names -/
  | mismatch
  /-- the file system failed -/
  | io
  /-- an observer custody (a follower's observe-only key, HOSTING-17 §7) signs only read envelope
  messages: a sign of anything else, a precommit or a signNext is refused -/
  | envelopeOnly
  /-- custody opened by `nd --stdio` (a hosted resident) refuses `precommit` and `signNext`: a
  resident does not rotate its key (PROTOCOL-40) -/
  | noRotation
  /-- `signIncoming` with no armed rotation: there is no incoming key to sign with -/
  | notArmed
  deriving DecidableEq, Repr

namespace CustodyRefusal

def all : List CustodyRefusal :=
  [fileRefused, .exists, shape, holdingAbsent, noPending, rotationInFlight, mismatch, io, envelopeOnly, noRotation,
   notArmed]

def code : CustodyRefusal → UInt8
  | fileRefused => 0 | .exists => 1 | shape => 2 | holdingAbsent => 3 | noPending => 4
  | rotationInFlight => 5 | mismatch => 6 | io => 7 | envelopeOnly => 8 | noRotation => 9
  | notArmed => 10

def name : CustodyRefusal → String
  | fileRefused => "fileRefused" | .exists => "exists" | shape => "shape"
  | holdingAbsent => "holdingAbsent" | noPending => "noPending"
  | rotationInFlight => "rotationInFlight" | mismatch => "mismatch" | io => "io"
  | envelopeOnly => "envelopeOnly" | noRotation => "noRotation" | notArmed => "notArmed"

def ofCode? (b : UInt8) : Option CustodyRefusal := all.find? (·.code == b)

end CustodyRefusal

/-- A refused custody result's payload: the refusal, one byte, refused as `badTag` unless it is
one of `CustodyRefusal`'s codes (by the Lean codec and the emitted Rust reader alike). -/
def custodyRefusalLayout : Codec.Layout :=
  [.oneOf "refusal" (CustodyRefusal.all.map fun r => (r.name, r.code))]

/-- The READ ENVELOPE: the payload of `log` (and `read`). A member's request to read the writer's
log from a height, signed by its current key and gated by its follow grant (PROTOCOL-3, HOST-11):
digests are `Env.bytes`, heights are u64le. The signed message is `Envelope.message` (domain tag,
member, grant, from, notBefore, validUntil); `[notBefore, validUntil]`, at most the kernel's
`windowMax` wide, bounds a replay to one window of heights (PROTOCOL-27). -/
def envelopeLayout : Codec.Layout :=
  [.bytes "world", .bytes "member", .bytes "grant", .bytes "from", .bytes "notBefore", .bytes "validUntil",
   .bytes "key", .bytes "signature"]

/-- The `refused` payload of `log` and `read` when the envelope's `validUntil` is below the writer's
height (PROTOCOL-19): the name `expired` as bytes, then that height, so an authenticated member
more than a window behind re-signs once with `validUntil` = height + window. Every other refusal of
the Host is its name as UTF-8; this payload starts with the name's length (`u32` 7: first byte
0x07, which no name begins with). The Host states it only to the current key of a live member whose
follow grant is live (`Envelope.check` checks expiry last). -/
def expiredRefusalLayout : Codec.Layout := [.bytes "refusal", .u64 "height"]

/-- The `log` reply's payload: the logged STEPS from the requested log position (a step count), in
log order, then the writer's step count and log chain after the last of them, then the writer's tip
when the page was built, as a step count (`tipSteps`) and a World height (`tipHeight`, which follow's
next envelope window is signed from). Each event is a tag byte and a signed call: 0 an admitted Turn,
1 a recorded refusal (KERNEL-44/47, PROTOCOL-41). A follower re-derives every step from its event
(PROTOCOL-4: a Turn by `submit`, a refusal by `judge`, which must record it) and asserts that its own
fold reached the same step count and chain (a pair assertion, law 4; the pair the kernel's
`fold_reaches_host` binds): an omitted, truncated or reordered event is caught at the page. A page
holds at most a frame of events (HOST-17), so it may end before the tip, even inside a writer batch:
follow pages again from `steps` until `steps = tipSteps` (at most `Bounds.pagesPerCommandMax` pages a
command). Last, the writer's newest DURABLE base when it built the page (PROTOCOL-47): its step
count (`baseSteps`, at most `tipSteps`, else the page is refused) and its digest (`baseDigest`, the
`read` header's and `host seal`'s). A seal racing the page leaves them stale; the follower trusts
neither: it records its OWN World's digest where its fold sits at `baseSteps`, and `invite` pins
that only when the stated digest agrees (`baseMismatch` otherwise). -/
def logReplyLayout : Codec.Layout :=
  [.list "events", .bytes "steps", .bytes "chain", .bytes "tipSteps", .bytes "tipHeight",
   .bytes "baseSteps", .bytes "baseDigest"]

/-- The `read` reply's payload: one page of the World bytes of the writer's NEWEST base (HOST-14,
HOST-15), for a thin member (PROTOCOL-14, option A). The request is the read envelope, its `start`
read as a byte offset into those World bytes. `steps` (the base World's step count: its position in
the log, KERNEL-47, PROTOCOL-41) and `chain` are the base World's,
`total` its World bytes' length, `digest` = `Hash.digest "nanodregg/host/base-digest/v1"` of them, and
`bytes` = World bytes `[start, start + chunk)`. All numbers are u64le. A seal between two pages
changes `steps` and `digest`, and the member starts its download again. The member trusts none of
it: it accepts the assembled bytes only if they hash to a base digest it pinned out of band
(`Protocol.Thin.accept`; a forged byte is `baseMismatch`). -/
def readReplyLayout : Codec.Layout :=
  [.bytes "steps", .bytes "total", .bytes "digest", .bytes "chain", .bytes "bytes"]

/-! The bounds the client and the supervisor enforce before allocating. -/
namespace Bounds

/-- One frame body (op or status byte and payload), either socket, either direction. -/
def frameBytesMax : Nat := 262144
/-- A `command` payload: the argv, `4 + Σ (4 + len)`. DERIVED from the kernel's call bound: it holds
`receipt CALL`, the call in hex, for every call the kernel admits (`eventBytesMax` bytes;
`Command.receipt_argv_fits`). At 65536 a call past 32,760 bytes was committed and never confirmed:
follow refused the confirm's argv `argvPastBound`, which the attempt reads as `uncertain` (LANG-76,
the Bell's install at 36,379 call bytes). -/
def argvBytesMax : Nat := 2 * Kernel.Bounds.eventBytesMax + 1024
/-- Steps one command may take: the CLIENT's bound, not follow's. Follow keeps no step counter (a
continuation carries no count); `nd`'s run loop ends a command past this many steps
(`client/src/run.rs`, `StepsExhausted`) and so does the rows' harness (`Rows.Loopback.resume`). A
table constant Rust consumes (law 2); `Bounds.pages_fit_steps` is why an honest catch-up never meets it. -/
def stepsPerCommandMax : Nat := 64
/-- Sends of one frozen call: the first submit and the resends after `absent`. -/
def sendsMax : Nat := 8
/-- `log` pages one command may read while it catches up (two steps each: sign the envelope from
the page's start, relay `log`). A follow further behind than this ends the command `behind`,
keeping what it absorbed, and the member runs it again. With the at most four other steps of any
command it fits `stepsPerCommandMax` (`Bounds.pages_fit_steps`). -/
def pagesPerCommandMax : Nat := 28
/-- Steps one `log` page may carry: one follower record's worth (HOST-41), so a follower appends one
page as one record: it IS HOST's `recordTurnsMax` (the batch codec's count bound), one source.
Follow refuses a longer page `pageTooLong`. -/
def pageStepsMax : Nat := Host.recordTurnsMax
/-- Connections one `nd-supervise` holds open at once (either socket). It bounds the supervisor's
memory: each connection buffers at most one frame per direction, so the whole mux holds at most
`2 * connectionsMax * frameBytesMax` bytes (32 MiB). A deployment's members are friends, not the
public: past the bound the supervisor answers `closed full` and closes. -/
def connectionsMax : Nat := 64
/-- A connection silent AT A FRAME BOUNDARY with NO request in flight this long is closed `idle`
by the supervisor (PROTOCOL-11, corrected by scout T2: the old rule, "no frame in either
direction", closed a client that was waiting on a slow reply). Five minutes: longer than any
command's step round trip; an idle peer holds one of `connectionsMax` slots at most this long. -/
def idleMsMax : Nat := 300000
/-- A frame that has started must be complete within this, or the connection is closed
`frameStalled` (a slow-loris peer cannot hold a slot by trickling one frame). 30 s: a
`frameBytesMax` frame at 10 KB/s. -/
def frameMsMax : Nat := 30000
/-- One reply write to a peer must complete within this, or the connection is closed
`replyWriteFailed` (a peer that stops reading cannot hold the supervisor's writer). -/
def replyWriteMsMax : Nat := 30000
/-- Connections one `nd-attach` process (one friend's ssh session) holds open to the Store's
socket at once; the next is answered `closed full`. Across sessions only sshd bounds a friend
(MaxSessions): the per-friend cap is a declared absence (CLIENT-12). -/
def peerConnectionsMax : Nat := 8
/-- How long a client waits for the reply to ONE request (one frame to `host.sock` or
`follow.sock`) before it stops waiting. Past it the client reports `timeout` by name; a request
that carried a frozen call is then UNCERTAIN (its attempt goes on by lookup: `Attempt.Seen.lost`),
never refused. It bounds one request, not a command (that is `stepsPerCommandMax` of these).
Two minutes: above a writer's worst legitimate wait for one request (a batch that seals inline
before it can append, plus a supervisor restart of the child, whose cold reopen THE BAR bounds
at 60 s), and below `idleMsMax`, so the supervisor never closes a connection a client is still
waiting on (`Bounds.reply_within_idle`). -/
def replyMsMax : Nat := 120000
/-- The bytes of a confirm's `receipt CALL` stderr the attempt store hands follow with an
`uncertain` end (cv 01a150b1): a longer one is handed as none, never cut, so the hint follow prints
is the refusal's whole first line or nothing. 512: past every `refused NAME` line Lean prints. -/
def hintBytesMax : Nat := 512
/-- The widest step event a `log` page carries (`Host.Page.stepEvent`, PROTOCOL-60): the 1-byte tag,
a cancel signature's eight-byte length and the signature at `cancelBytesMax` (tag 2 only), and the
call at `eventBytesMax`. A page budget of this plus the page's 4-byte length serves every event a
record decodes to (`Host.Page.budget_fits_event`). -/
def pageEventBytesMax : Nat := Kernel.Bounds.eventBytesMax + 1 + 8 + Kernel.Bounds.cancelBytesMax

/-! ### The frame as a whole (PROTOCOL-70)

Every byte-string field of a layout is bounded by `frameBytesMax` on its own (`Codec.Layout`); the
transport bounds the frame's BODY, the op or status byte and every field together, by the same number
(`Host.Wire.bodyMax`, `client/src/frame.rs`). A `resume` after a `log` carries two big fields, the
continuation and the Host's page, so the page's room is the frame less the continuation's largest
size and every byte of framing: `pageBytesMax`, the deployed writer's page budget (`Host.Page.budget`).
Before PROTOCOL-70 the budget was `frameBytesMax - 1024`: a full page left 890 bytes for the
continuation, and `receipt CALL` of any call over 337 bytes could not take it back (measured). -/

/-- The deployed custody's public key (`client/src/custody.rs`: Ed25519). -/
def custodyKeyBytes : Nat := 32
/-- The deployed custody's signature (Ed25519). -/
def custodySignatureBytes : Nat := 64
/-- Custody's `sign` answer at the deployed widths (`signResultLayout`: key, next key, signature,
each behind a `u32` length): what a page phase's continuation holds as `signed`. -/
def signedBytes : Nat := (4 + custodyKeyBytes) + (4 + custodyKeyBytes) + (4 + custodySignatureBytes)
/-- What a `resume` frame spends beside its two fields' bytes: the op byte and the two `u32`
lengths (`resumeLayout`). -/
def resumeFramingBytes : Nat := 1 + 4 + 4
/-- What a `log` reply spends beside its events' bytes: the status byte, the events' `u32` count,
the four `u64` positions behind their lengths, and the chain and base digest behind theirs
(`logReplyLayout`). A `read` reply spends less (`readReplyLayout`: two `u64`s and two digests). -/
def logReplyFramingBytes : Nat := 1 + 4 + 4 * (4 + 8) + 2 * (4 + Host.digestBytes)
/-- The largest continuation a page-asking step hands out: phase 2's (`log`), the argv at
`argvBytesMax` (`parse` refuses a longer one), the phase byte, the acc's `u32` count and its five
fields (`start`, `pages`, `upTo`, `tried` as `u64`s, custody's `signed` answer), each behind its
length. Phase 7's (`read`) holds four `u64`s and is smaller. -/
def pageContinuationBytesMax : Nat := argvBytesMax + 1 + 4 + 4 * (4 + 8) + (4 + signedBytes)
/-- **The page budget**: the event bytes (`Σ (4 + |event|)`) one `log` page carries, and the World
bytes one `read` page carries. The frame less the resume's framing, the reply's framing and the
largest continuation, so a page and the continuation that asked for it fit ONE frame
(`Protocol.Proofs.FrameFit.resume_frame_fits`). It still serves every event the kernel admits
(`Host.Page.budget_fits_event`: `pageEventBytesMax + 4 ≤ pageBytesMax`). -/
def pageBytesMax : Nat :=
  frameBytesMax - resumeFramingBytes - logReplyFramingBytes - pageContinuationBytesMax

end Bounds

/-! ## A page's step events (PROTOCOL-8, PROTOCOL-41, PROTOCOL-60)

The one source of the tags: `Host.Page.stepEvent` writes them, `Command.absorbStep` reads them. A
recorded refusal is tag 1 when it carries no cancel signature and tag 2 when it does, the same
discriminator the kernel's audit uses (`Receive.recordedBy`: the FIELD, never the code). -/

/-- `0 ‖ call`: an admitted Turn. -/
def eventTurn : UInt8 := 0
/-- `1 ‖ call`: a recorded refusal with no cancel signature (judged by `Receive.judge`). -/
def eventRefusal : UInt8 := 1
/-- `2 ‖ nat64 n ‖ sig ‖ call`, `sig` the `n` bytes of the member's cancel signature (KERNEL-60,
design C1; `0 < n ≤ cancelBytesMax`): a recorded CANCEL, re-recorded by `Receive.cancel`. -/
def eventCancel : UInt8 := 2

/-- THE tag-2 event: a cancel signature `sig` and the cancelled call's bytes `call`, as
`Host.Page.stepEvent` writes it and `cancelParts` (below) reads it back. -/
def cancelEvent (sig call : ByteArray) : ByteArray :=
  ⟨#[eventCancel]⟩ ++ Codec.Stream.nat64.bytes sig.size ++ sig ++ call

/-- A cancel event's signature and call bytes (`eventCancel`: `2 ‖ nat64 n ‖ sig ‖ call`): the
length read at byte 1, then `n` signature bytes, then the rest. `none` when the length does not
read, is `0`, is past `cancelBytesMax`, or runs past the event (each is one encoding the writer's
`stepEvent` never makes, PROTOCOL-60). Beside `cancelEvent` so the one encoding's writer and
reader sit together: follow's `absorbStep` and the Host's `cancel` op both read with it (HOST-66). -/
def cancelParts (e : ByteArray) : Option (ByteArray × ByteArray) :=
  match Codec.Stream.nat64.get e 1 with
  | .ok (n, j) =>
      if 0 < n ∧ n ≤ Kernel.Bounds.cancelBytesMax ∧ j + n ≤ e.size then
        some (e.extract j (j + n), e.extract (j + n) e.size)
      else none
  | .error _ => none

end Nanodregg.Protocol
