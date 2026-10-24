/-
# Protocol.Attempt — what the attempt store does next with a frozen call (PROTOCOL-17, PROTOCOL-46)

A `submit` step hands the client a signed call. The client FREEZES it (CLIENT-3: the exact bytes,
on disk, written once) and drives it to the writer by `submit` and `lookup` of those same bytes.
Which request comes next, and when the attempt is over, is a decision (law 2), so it is this
function, and the client's attempt store consults it (CLIENT-3 implements it from `Attempt.table`,
which CODEC emits; the client keeps no second copy of the rule).

The Host HINTS; the member's follow SETTLES (PROTOCOL-46). The Host's status drives the loop (when to
look up, when to send the same bytes again), and it never ends an attempt final. A Host reply that
would end it (committed, refused) is followed by `confirm`: nd asks its own follow `receipt CALL`,
which catches up, builds the receipt from the member's own World and answers `Settle.ofReceipt`'s
verdict (`settle_seen` reads its first word). Sends exhausted and still `absent` is followed by
`probe`, the same request. So:

* never sent → `submit`;
* a Host reply saying committed or refused → `confirm`;
* follow saying committed → over, `committed`; refused (recorded, or the window passed) → over,
  `refused`. Only these two are final, and only follow says them (`Proofs.Attempt.next_final`);
* a probe follow answers `open` (absent, the window live: the Host or any relay holding the bytes
  may still land them) → the same bytes again while sends remain; with none left → over, `open`:
  the attempt stays OPEN on disk; running the command again would sign a NEW call that could land
  beside this one (`Proofs.Settle.settle_open_not_final`);
* a confirm follow answers `open` or `forgotten` after the Host said committed or refused → over,
  `contradicted`, named (`hostContradicted HOSTSAID FOLLOWSAID`); the attempt stays open;
* a submit or a lookup answered `declined` (refused by name, NOT recorded: unauthenticated, an early
  window, the member's refusal budget, undecodable bytes, or a frame the writer still held queued
  when it stopped, HOST-74) → over for this run, `declined`, the attempt stays open (PROTOCOL-41);
* a submit whose reply was lost or `uncertain` → `lookup`, never a second submit: the first may
  still be queued at the writer, and only a lookup can say;
* a lookup that says `absent` → `probe` FIRST (KERNEL-54, PROTOCOL-15's condition 3): follow says
  whether the call is dead before any resend. Follow's `refused` (a recorded refusal, the window
  passed, or its own fold's stale BEHIND, `Settle.ofReceipt`) ends it; its `open` → `submit` again
  (the same bytes; the journal makes a duplicate commit impossible) while sends remain, and with
  none left over `open`;
* a lookup whose reply was lost or `uncertain`, a probe past `journalForgets`, a confirm or probe
  follow did not answer → over, `uncertain`: this run stops and the attempt stays frozen and
  unsettled on disk; the next run starts from "sent, outcome lost" and looks up again;
* a reply that cannot answer the request (`absent` to a submit, a settle word to the Host's
  request, a Host status to follow's) → over, `badReply`, by name.

Nothing here signs: an attempt's bytes never change (`Protocol.Proofs.Attempt`).
-/
namespace Nanodregg.Protocol.Attempt

/-- The four requests an attempt sends, each carrying the frozen bytes: two to the writer, two to
the member's own follow (`receipt CALL`). -/
inductive Request
  | submit
  | lookup
  /-- the Host said committed or refused: follow settles it -/
  | confirm
  /-- every send was answered `absent`: follow says whether the call is dead -/
  | probe
  deriving DecidableEq, Repr

/-- What the reply to the last request said. To `submit` / `lookup`, the writer's status byte (the
generated status table): `ok` committed, `refused` refused (final at the writer's word),
`declined` refused and not final, `uncertain` unknown, `absent` absent. To `confirm` / `probe`, the
first word of follow's `settle` line (`settle_seen`): committed, refused (also `expired`), open,
forgotten. `lost` is no reply at all (a dropped connection, a crash, the reply deadline, a follow
that did not answer). -/
inductive Seen
  | committed
  | refused
  | declined
  | unknown
  | absent
  | lost
  | «open»
  | forgotten
  deriving DecidableEq, Repr

def Seen.name : Seen → String
  | .committed => "committed" | .refused => "refused" | .declined => "declined"
  | .unknown => "unknown" | .absent => "absent" | .lost => "lost" | .open => "open"
  | .forgotten => "forgotten"

/-- What the attempt store does next. The last seven end the run. -/
inductive Action
  | submit
  | lookup
  | confirm
  | probe
  /-- follow's own World holds the call's journal entry -/
  | committed
  /-- follow's own World holds the call's recorded refusal, or the call's window has passed -/
  | refused
  /-- refused by name and not final (PROTOCOL-41): the run stops; the attempt stays open (unsettled
  on disk) for the next run, which looks it up -/
  | declined
  /-- every send was answered `absent` and the call's window is still live: the run stops; the
  attempt stays open (the bytes may still land; running the command again is NOT safe) -/
  | «open»
  /-- the Host said committed or refused and follow says otherwise: named, the attempt stays open -/
  | contradicted
  /-- the reply cannot answer the request -/
  | badReply
  /-- nothing settled: the run stops; the attempt stays unsettled for the next run -/
  | uncertain
  deriving DecidableEq, Repr

def Action.name : Action → String
  | .submit => "submit" | .lookup => "lookup" | .confirm => "confirm" | .probe => "probe"
  | .committed => "committed" | .refused => "refused" | .declined => "declined" | .open => "open"
  | .contradicted => "contradicted" | .badReply => "badReply" | .uncertain => "uncertain"

/-- The byte nd hands follow as step 4's result, before the payload (`Command.Machine`). -/
def Action.code : Action → UInt8
  | .submit => 0 | .lookup => 1 | .confirm => 2 | .probe => 3 | .committed => 4 | .refused => 5
  | .declined => 6 | .open => 7 | .contradicted => 8 | .badReply => 9 | .uncertain => 10

/-- THE decision. `sendsLeft` is `sends < Bounds.sendsMax`; `last` is the last request and what
its reply said, `none` if nothing was sent. -/
def next (sendsLeft : Bool) : Option (Request × Seen) → Action
  | none => .submit
  -- the Host's word: never final
  | some (.submit, .committed) | some (.submit, .refused)
  | some (.lookup, .committed) | some (.lookup, .refused) => .confirm
  | some (.submit, .declined) | some (.lookup, .declined) => .declined
  | some (.submit, .unknown) | some (.submit, .lost) => .lookup
  | some (.lookup, .unknown) | some (.lookup, .lost) => .uncertain
  | some (.lookup, .absent) => .probe
  -- follow's word
  | some (.confirm, .committed) | some (.probe, .committed) => .committed
  | some (.confirm, .refused) | some (.probe, .refused) => .refused
  | some (.probe, .open) => if sendsLeft then .submit else .open
  | some (.confirm, .open) | some (.confirm, .forgotten) => .contradicted
  | some (.probe, .forgotten) => .uncertain
  | some (.confirm, .lost) | some (.probe, .lost) => .uncertain
  -- a reply that cannot answer its request
  | some (.submit, .absent) | some (.submit, .open) | some (.submit, .forgotten)
  | some (.lookup, .open) | some (.lookup, .forgotten)
  | some (.confirm, .declined) | some (.confirm, .unknown) | some (.confirm, .absent)
  | some (.probe, .declined) | some (.probe, .unknown) | some (.probe, .absent) => .badReply

/-- Follow's `settle` line, by its first word (`Command.Machine`'s `receipt` arm prints it): what
the attempt store sees for a `confirm` / `probe`. `expired` is a refusal by the call's window. -/
def settleSeen : String → Option Seen
  | "committed" => some .committed
  | "refused" => some .refused
  | "expired" => some .refused
  | "open" => some .open
  | "forgotten" => some .forgotten
  | _ => none

/-- The first words of the three lines follow prints for `receipt CALL` (`Command.Machine.receiptText`),
each followed by one space: the receipt in hex, the head it was built at, the settlement. The client reads
a confirm's answer by them (`client/src/attempt.rs`, emitted `RECEIPT_WORD`, `HEAD_WORD`, `SETTLE_WORD`, CLIENT-40). -/
def receiptWord : String := "receipt"
def headWord : String := "head"
def settleWord : String := "settle"

/-- The words `settleSeen` reads, in the order the emitter prints them. -/
def settleWords : List String := ["committed", "refused", "expired", "open", "forgotten"]

def Request.all : List Request := [.submit, .lookup, .confirm, .probe]
def Seen.all : List Seen := [.committed, .refused, .declined, .unknown, .absent, .lost, .open, .forgotten]
/-- Every action, in constructor order: what CODEC emits as the client's `Action` enum. -/
def Action.all : List Action :=
  [.submit, .lookup, .confirm, .probe, .committed, .refused, .declined, .open, .contradicted, .badReply,
   .uncertain]

/-- Every input the decision distinguishes. -/
def inputs : List (Bool × Option (Request × Seen)) :=
  [false, true].flatMap fun b =>
    (b, none) :: Request.all.flatMap fun r => Seen.all.map fun s => (b, some (r, s))

/-- The decision as data, one row per input: what CODEC emits for the client (law 2). -/
def table : List ((Bool × Option (Request × Seen)) × Action) :=
  inputs.map fun (b, l) => ((b, l), next b l)

end Nanodregg.Protocol.Attempt
