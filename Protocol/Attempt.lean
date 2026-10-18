/-
# Protocol.Attempt — what the attempt store does next with a frozen call (PROTOCOL-17)

A `submit` step hands the client a signed call. The client FREEZES it (CLIENT-3: the exact bytes,
on disk, written once) and settles it against the writer by `submit` and `lookup` of those same
bytes. Which request comes next, and when the attempt is over, is a decision (law 2), so it is this
function, and the client's attempt store consults it (CLIENT-3 implements it from `Attempt.table`,
which CODEC emits; the client keeps no second copy of the rule):

* never sent → `submit`;
* a reply that says committed → over, `committed`; a FINAL named refusal (status `refused`: recorded
  now or before, or past the call's window; `Protocol.Settle`, PROTOCOL-41) → over, `refused`;
* a submit answered `declined` (refused by name, NOT recorded: unauthenticated, an early window, the
  member's refusal budget) → over for this run, `declined`, and the attempt stays OPEN: frozen and
  unsettled on disk like `uncertain`, so the next run looks it up (the same bytes may still be
  admitted: a call signed with the precommitted next key is `unknownKey` until the rotate);
* a submit whose reply was lost or `uncertain` → `lookup`, never a second submit: the first may
  still be queued at the writer, and only a lookup can say;
* a lookup that says `absent` → `submit` again (the same bytes; the journal makes a duplicate
  commit impossible), while sends remain; with none left → over, `absent` (the member may run the
  command again: nothing committed);
* a lookup whose reply was lost or `uncertain` → over, `uncertain`: this run stops and the attempt
  stays frozen and unsettled on disk; the next run starts from "sent, outcome lost" and looks up
  again (CLIENT-2: a lookup loop inside one run would have no deadline);
* a reply that cannot answer the request (`absent` to a submit) → over, `badReply`, by name.

Nothing here signs: an attempt's bytes never change (`Protocol.Proofs.Attempt`). One run makes at
most `2 · Bounds.sendsMax` requests: every lookup follows a submit, and a lookup that settles
nothing ends the run (`Proofs.Attempt.next_after_lookup`).
-/
namespace Nanodregg.Protocol.Attempt

/-- The two requests an attempt sends, each carrying the frozen bytes. -/
inductive Request
  | submit
  | lookup
  deriving DecidableEq, Repr

/-- What the writer's reply to the last request said, classified by its status byte (the
generated status table): `ok` committed, `refused` refused (final), `declined` refused and not final, `uncertain` unknown,
`absent` absent;
`lost` is no reply at all (a dropped connection, a crash, the reply deadline). -/
inductive Seen
  | committed
  | refused
  | declined
  | unknown
  | absent
  | lost
  deriving DecidableEq, Repr

/-- What the attempt store does next. The last six end the run. -/
inductive Action
  | submit
  | lookup
  | committed
  | refused
  /-- refused by name and not final (PROTOCOL-41): the run stops; the attempt stays open (unsettled
  on disk) for the next run, which looks it up -/
  | declined
  /-- every permitted send was answered `absent`: nothing committed; running the command again is safe -/
  | absent
  /-- the reply cannot answer the request -/
  | badReply
  /-- a lookup settled nothing: the run stops; the attempt stays unsettled for the next run -/
  | uncertain
  deriving DecidableEq, Repr

def Action.name : Action → String
  | .submit => "submit" | .lookup => "lookup" | .committed => "committed" | .refused => "refused"
  | .declined => "declined" | .absent => "absent" | .badReply => "badReply" | .uncertain => "uncertain"

/-- THE decision. `sendsLeft` is `sends < Bounds.sendsMax`; `last` is the last request and what
its reply said, `none` if nothing was sent. -/
def next (sendsLeft : Bool) : Option (Request × Seen) → Action
  | none => .submit
  | some (_, .committed) => .committed
  | some (_, .refused) => .refused
  | some (.submit, .declined) => .declined
  | some (.lookup, .declined) => .badReply
  | some (.submit, .unknown) | some (.submit, .lost) => .lookup
  | some (.submit, .absent) => .badReply
  | some (.lookup, .unknown) | some (.lookup, .lost) => .uncertain
  | some (.lookup, .absent) => if sendsLeft then .submit else .absent

def Request.all : List Request := [.submit, .lookup]
def Seen.all : List Seen := [.committed, .refused, .declined, .unknown, .absent, .lost]
/-- Every action, in constructor order: what CODEC emits as the client's `Action` enum. -/
def Action.all : List Action := [.submit, .lookup, .committed, .refused, .declined, .absent, .badReply, .uncertain]

/-- Every input the decision distinguishes. -/
def inputs : List (Bool × Option (Request × Seen)) :=
  [false, true].flatMap fun b =>
    (b, none) :: Request.all.flatMap fun r => Seen.all.map fun s => (b, some (r, s))

/-- The decision as data, one row per input: what CODEC emits for the client (law 2). -/
def table : List ((Bool × Option (Request × Seen)) × Action) :=
  inputs.map fun (b, l) => ((b, l), next b l)

end Nanodregg.Protocol.Attempt
