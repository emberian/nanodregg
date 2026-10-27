/-
# Protocol.Rows — the conformance rows, as data

The spec of the end system is these rows (CHARTER). A row is a fresh deployment, a list of member
commands (argv of `nd`, the one command language), and for each command the outcome it must get,
by name. A row names the operations its commands drive and the receiver kinds they reach, so the
reach table IS this file: `Protocol.Proofs.Rows.every_op_has_a_row` refuses an operation no row
exercises, and the size ratchet counts what is here.

Each row also names its PLANT: a mutation of the system, the line that must catch it and the
outcome that line then gets. A row whose plant does not move that line is blind and is red.

Refusal names are the owners' `name`s (`Kernel.Reject.name`, `Receive.Refusal.name`,
`Protocol.Command.Refusal.name`, `ReadRefusal.name`, `ParseRefusal.name`, `Host.OpenFault`).

Rows come from minidregg's landing rows (`scripts/pipeline/journey-rows`, main 2c27b08b). What a
minidregg row checked that nanodregg does not have (a codec child, a host-image pin, a socket
filter) is gone with the thing; what it checked about the WORLD stays.
-/
import Protocol.Table
import Lang.Print
import Lang.Surface

namespace Nanodregg.Protocol

/-- What one line must end in. `refused` carries the refusal's name (its owner's `name`). -/
inductive Expect
  | ok
  | refused (name : String)
  /-- the Host's lookup answers `absent` (`retry`, `resubmit`: the Host's word, never a settlement) -/
  | absent
  /-- the Host's reply was `uncertain` (a failed append): a real outcome, never a guess -/
  | uncertain
  /-- the Host's reply was `uncertain` and named why (`forgotten`: the journal no longer answers,
  KERNEL-33): not a verdict on the call, and never a refusal -/
  | unsettled (why : String)
  /-- the line ran past its LIVENESS deadline (`withinMs`): the system did not answer in time. A
  non-verdict by name, never a judgement of speed (Ember: no wall-clock verdict until the end, on a
  quiet box; THE BAR's ≤ 5 s is PERF's final spec, `scripts/bar.sh`, not a row criterion) -/
  | hang
  /-- the command's catch-up ended still behind the writer's tip (`CommandExit.behind`): run again -/
  | behind
  /-- the writer refused the call by name and did NOT record it (`Status.declined`, PROTOCOL-41): not
  final, the attempt stays open -/
  | declined (name : String)
  /-- every send was answered `absent` and the member's own follow says the call's window is live
  (`CommandExit.open`, PROTOCOL-46): the attempt stays open, the bytes may still land -/
  | «open»
  /-- the Host said committed or refused and the member's follow says otherwise
  (`CommandExit.hostContradicted`): `HOSTSAID FOLLOWSAID` -/
  | contradicted (said : String)
  /-- the writer refused a page `pageIo` (`CommandExit.pageIo`, HOST-48): not now, never never; the
  member runs the command again -/
  | pageIo
  deriving DecidableEq, Repr

def Expect.text : Expect → String
  | .ok => "ok" | .refused n => s!"refused {n}" | .absent => "absent" | .uncertain => "uncertain"
  | .unsettled n => s!"uncertain {n}" | .hang => "hang" | .behind => "behind"
  | .declined n => s!"declined {n}" | .open => "open" | .contradicted n => s!"hostContradicted {n}"
  | .pageIo => "pageIo"

/-- What a line does. A member command goes through the one command language; the others are the
operator's and the attempt store's acts, which are not member commands. -/
inductive Act
  /-- `nd ARGV`: an argument `@name` is the id a previous line bound to `name`, in hex -/
  | cmd (argv : List String)
  /-- stop the Host loop and reopen the Store from its bytes, cold -/
  | restart
  /-- the attempt store settles the actor's last frozen call by `lookup` -/
  | retry
  /-- open a copy of the Store whose BASE file has the byte at `offset` flipped -/
  | reopenFlipped (offset : Nat)
  /-- the operator seals a base of the writer's World as it stands, then restarts the loop from it
  (the writer's newest base is then at its tip) -/
  | seal
  /-- the actor accepts the invitation bound to `invite` under the sponsor key bound to `key`
  (`Invite.accept`, the decision `host join` makes, PROTOCOL-42): its `Self.world` is the accepted
  World's origin and its follow starts from that World. Every actor not a founder has already
  accepted the rows' founding invitation (the sponsor's, at genesis) when it is first used -/
  | accept (invite key : String)
  /-- the actor catches up (`sync`), then counts, on its own World, the objects made by one member
  and used by another over every call the writer committed (`Protocol.Use.shared`, PROTOCOL-43):
  `ok` when there are at least `atLeast`, else `refused unshared:N` -/
  | used (atLeast : Nat)
  /-- the actor runs `receipt CALL` for OWNER's last call (its frozen bytes) -/
  | receiptOf (owner : String)
  /-- the actor, holding only its own head (its follow World's height and roots), checks the
  receipt bound to `receipt` for OWNER's last call (`Protocol.Receipt.check`); `ok` prints the
  answer, else `refused NAME` -/
  | verify (owner receipt : String)
  /-- the actor, holding only its own head (`Head.headOf` its follow World), checks the HEALTH
  receipt bound to `health` for OWNER's member (`Protocol.Health.check`, DESIGN-OBS §1.5); `ok` prints
  the three counters, else `refused NAME` -/
  | verifyHealth (owner health : String)
  /-- every call the writer committed so far is submitted, byte-identical and in order, to a SECOND
  writer made by a second genesis with the same name, allowance and founders, and the same nonce
  (`sameNonce`: a restore of the same World) or another one (OPS's cross-World replay). The outcome
  is the one every call got; calls that got different outcomes are `refused mixed:I:OUTCOME` -/
  | replayLog (sameNonce : Bool)
  /-- a hostile client: the actor's command ARGV is parsed and planned on its follow World as its
  last command left it (`Command.parse`, `body`, `planUnchecked`), signed and submitted WITHOUT
  follow's own admission; what the writer answers is the outcome. Custody is not advanced (only
  a rotation advances it, and a forged rotation is not a row's business) -/
  | forge (argv : List String)
  /-- the operator stops the writer, exports its World (`Host.Carry.exportFile`) and imports it as
  a NEW World (`Host.Carry.importWorld`: the one decision `host import` makes), under the rows'
  name and another nonce, with the file's digest (`rightDigest`) or a digest with one bit flipped;
  an import that succeeds is the writer from then on (`Writer.genesisStore` of the carried World),
  one that is refused leaves the old writer serving -/
  | carry (rightDigest : Bool)
  /-- the actor is re-invited to the carried World: its `Self.world` is the new origin and its
  follow starts from the carried World (members, grants and accounts are carried cells) -/
  | acceptCarry (wrongOrigin : Bool)
  /-- the actor is re-invited to the carried World (its `Self.world` the new origin) but its follow
  is the lineage's FIRST genesis, height 0: a follower Store from before the import's first step,
  which never adopted the carried base -/
  | rejoinBehind
  /-- the actor signs a `log` read envelope for ITS World (from height 0, one window from 0) and
  sends it to a second writer made as `replayLog` makes one (PROTOCOL-29's cross-World read); the
  outcome is that writer's answer -/
  | readElsewhere (sameNonce : Bool)
  /-- the actor's last call (its frozen bytes) is submitted again, byte-identical: a relay or a
  client that still holds the bytes. The outcome is the writer's answer -/
  | resubmit
  /-- the attempt store's next run of the actor's open attempt (its last frozen call): "sent, outcome
  lost", so it looks up, sends the same bytes again while sends remain, and settles by the member's
  own follow (PROTOCOL-46); the outcome is the command's end, as the follow machine renders it -/
  | rerun
  /-- the actor's client signs every later envelope for `n` heights (its own `Self.window`, a
  client's setting; the writer's read gate bounds it by `Bounds.windowMax`) -/
  | window (n : Nat)
  /-- the actor runs `cancel CALL` for OWNER's last call (its frozen bytes) -/
  | cancelOf (owner : String)
  deriving Repr

/-- A fault the transport or the client injects into one command. -/
inductive Fault
  | none
  /-- the Host commits the submit, the reply is lost; the attempt store settles by `lookup` -/
  | dropReply
  /-- the submit never reaches the Host; the lookup answers `absent` -/
  | neverForward
  /-- between this command's signature and its submit, ACTOR runs ARGV to completion (ok) -/
  | race (actor : String) (argv : List String)
  /-- this command's follow starts from genesis, and the page's event at `index` has its last
  byte flipped -/
  | flipEvent (index : Nat)
  /-- this command's follow starts from genesis, and the page omits its last event -/
  | dropLastEvent
  /-- this command's follow starts from genesis -/
  | cold
  /-- the actor signs as member `victim` with the victim's CURRENT key (stolen), its own custody
  holding every other key -/
  | stolenKey (victim : String)
  /-- the invitation reaches the actor through a relay that changed its nonce (a forged origin: the
  relay's own World); `resign`: the relay also re-signs it with its own key -/
  | forgeInvite (resign : Bool)
  /-- the receipt reaches the checker through a relay that states `absent` over the same paths (a
  host that says "not admitted"); a health receipt, through one that states the member spent no
  ticks this window -/
  | forgeReceipt
  /-- the Host commits the submit, the reply is lost, and its lookup lies: `refused stale` for the
  committed call (PROTOCOL-46: the Host hints, follow settles) -/
  | lieLookup
  /-- every `log` and `read` page this command asks for is refused by the writer's `pageIo` reply
  (`Host.pageIoReply`: its IO failed building that page, and it serves on, HOST-48) -/
  | pageIo
  /-- the actor's command runs on member `other`'s follower (its Self) with the actor's own custody
  under `nd --stdio`, which refuses every rotation step `noRotation` (CLIENT-8's nd-members finding:
  a resident's socket bound to another member's follower) -/
  | wrongFollower (other : String)
  /-- this command's follow starts from genesis, and every cancel event (tag 2) a page carries has
  the first byte of its signature flipped: a Host that serves a cancel the member never signed -/
  | forgeCancel
  /-- the relay keeps this command's `cancel` op from the writer and answers it `refused cancelled`:
  a Host that says it recorded a cancel it never saw (PROTOCOL-71) -/
  | lieCancel
  deriving Repr

/-- One line of a row. -/
structure Line where
  actor : String
  act : Act
  expect : Expect
  fault : Fault := .none
  /-- bind the first `id HEX` / `join HEX` the command prints to this name -/
  bind : Option String := none
  /-- run the act this many times (each must get `expect`); the driver may scale it -/
  times : Nat := 1
  /-- a liveness deadline: a run that has not ended after this many milliseconds of wall time is
  `hang` (a non-verdict), never a speed verdict -/
  withinMs : Option Nat := none
  /-- text the act must print (stdout) when it gets `expect`; missing, the line gets `refused
  unprinted` -/
  prints : Option String := none
  /-- `prints` is the act's WHOLE stdout, not a part of it -/
  exact : Bool := false
  deriving Repr

/-- How a row is driven. -/
inductive Drive
  /-- a Lean executable of this tree that drives the real receive path in-process (toy
  parameters, the real pipeline); it passes when it exits 0 and its last line is `last` -/
  | exe (name : String) (args : List String) (last : String)
  /-- members' commands, each through the one command language -/
  | members (lines : List Line)
  deriving Repr

/-- A mutation of the system a row must catch. Each is a change to the parameters the loopback
runs (the writer's and the followers' contexts, the Host's machine, the attempt store), never a
change to the row. -/
inductive Mutation
  /-- the Host serves `log` without checking the read envelope -/
  | openLog
  /-- every law admits (LANG's judge skipped), for the writer and every follower -/
  | skipJudge
  /-- a follower accepts any signature on a logged event -/
  | followVerifyAll
  /-- the Store reopens to a World with an empty journal -/
  | forgetJournal
  /-- after a lost reply the client signs the command afresh instead of looking up -/
  | resendFresh
  /-- every `withinMs` bound is 0: the liveness check must be live -/
  | zeroDeadline
  /-- custody advances to the next key when it signs a rotation, not on its settlement -/
  | advanceOnSend
  /-- the writer states every log page's own end as its tip, hiding the log after it -/
  | lieTip
  /-- the writer serves its newest base with one World byte flipped, stating the honest digest -/
  | forgeBase
  /-- the writer's certificate of its base carries a flipped signature byte: a forged certification
  (PROTOCOL-77.1) -/
  | forgeCertificate
  /-- the writer refuses an expired envelope by the name alone, stating no height (PROTOCOL-12's
  shape, before PROTOCOL-19) -/
  | unstatedExpiry
  /-- the writer answers `forgotten` as a REFUSAL (`refused forgotten`), the shape KERNEL-33 did not
  take: a client would read a call committed long ago as refused -/
  | forgottenRefused
  /-- a second genesis draws the first one's nonce (HOST's randomness repeats): the origin is only
  as unique as the nonce (KERNEL-24's critique) -/
  | nonceRepeats
  /-- the keyed account id ignores its owner (the shape LEDGER-7 replaced): every owner's account
  of one denomination is one id, for the writer and every follower -/
  | accountByAsset
  /-- the writer admits each Turn against its World with every spent nullifier forgotten, and
  keeps the World that admission reaches (so it forgets them for good, and diverges from its
  followers): a writer that does not keep its spent set -/
  | writerForgetsSpent
  /-- the import is handed the file's OWN digest whatever the operator gave: no out-of-band link
  from the old Store to the bytes imported -/
  | importTrustsFile
  /-- the writer admits a call whose transaction id holds a recorded refusal (judged on its World
  with the refusals forgotten) and still answers it `refused NAME`: a writer that tells the client a
  final no and commits the call anyway (the A→B→A defect, as a lie). Live under KERNEL-54 on the
  unpinned-insert arm: an insert refused `relationFull` is recorded, a retract frees the slot, and
  the same signed bytes would then derive and admit -/
  | admitsRecorded
  /-- the attempt store takes the Host's `declined` as final and settles the attempt `refused`
  (KERNEL-54: the writer declines a stale, never records it; only the member's own fold settles
  it, PROTOCOL-15's condition 1) -/
  | settleDecline
  /-- the joiner takes an invitation's inputs as they arrive, checking neither its signer nor its
  signature: trust on first use, the shape before PROTOCOL-42 -/
  | trustFirstUse
  /-- every actor's client signs as the sponsor (its member, its key): one resident playing every
  part, so every use is self-use -/
  | oneMember
  /-- the resident's client does not read a description: every method it binds from one is
  method 0 (a guess at the first method) -/
  | guessMethod
  /-- the phone believes a receipt's stated answer with its roots matched, never checking the paths -/
  | trustReceipt
  /-- the attempt store ends an attempt on the Host's final REFUSAL (its lookup's `refused NAME`),
  never asking its own follow (the shape before PROTOCOL-46). Only the refusal is trusted, so the
  plant bites where the Host lies about one, not at every honest commit -/
  | trustLookup
  /-- the operator's seal is a restart that seals nothing (the rows' seal without `Host.sealNow`,
  HOST-43's tooth) -/
  | sealIgnored
  /-- the writer states its tip as its newest base, with the sealed base's digest (PROTOCOL-47) -/
  | lieBase
  /-- `read OBJ` of a programmed object prints its raw state slots (`I=BYTES`, the shape before
  PROTOCOL-48), not its state value at the package's state type -/
  | rawSlots
  /-- the follower reads a page refused `pageIo` as a final refusal (exit 1, `refused pageIo`), the
  shape before PROTOCOL-49: "not now" read as "never" -/
  | pageIoFatal
  /-- `read OBJ REL K` prints the rows' lines with the first one dropped: a reader that loses a row
  (PROTOCOL-51) -/
  | dropRow
  /-- `read OBJ REL K` lists whatever K asks, never checking it against the relation's declared
  `limit` (`Command.rowLines` without `rangeLines`' bound, PROTOCOL-51) -/
  | noReadLimit
  /-- `nd`'s output for a method's refusal is the bare `refused program`, its reason dropped (the
  stdio surface before cv 01a15039): the hint line LANG's words travel on is removed -/
  | flatProgram
  /-- the writer pages with 16384 bytes, the guess at the largest event the rows log that the queue
  Bell's install outgrew (PROTOCOL-18): an event past the budget is never served -/
  | guessedBudget
  /-- a custody refusal of the `signIncoming` step ends the command by custody's name: `nd --stdio`'s
  `noRotation` masks the writer's `unknownKey`. The machine before ROOT's rule (a) (PROTOCOL-56) did
  that for every name but `notArmed`; the plant cuts in in the harness, before `step` -/
  | maskIncoming
  /-- the attempt store ends `uncertain` with no payload: the confirm's `receipt CALL` stderr dropped,
  the shape before cv 01a150b1 (nd's `Vec::new()`) -/
  | dropHint
  /-- the writer's reopen is handed the genesis base instead of the newest, so it replays the whole
  log (PROTOCOL-53: THE BAR's `rowbar reopen-bytes-per-byte-past-base` must move) -/
  | staleBase
  /-- the client runs every write command twice (PROTOCOL-53: THE BAR's `rowbar frames-per-write`
  and `steps-per-write` must move) -/
  | twiceEach
  /-- a relay hides the log from an invoke with `--range` (an empty page at follow's own position,
  stated as the tip): follow's own machine, its admission included, plans and signs at the listing it
  held at its LAST command (item 4: only the writer's check is left to refuse the stale range). One
  change: before Q8's split this plant also skipped follow's admission (`forged`) -/
  | staleRange
  /-- the client drops an invoke's `--range REL K [PREFIX]`: the plan signs no range (item 4, the shape
  before it: the receiver's `rangeUnpinned`) -/
  | dropRange
  /-- follow ACTS on the writer's `beforeLog`: it takes the writer's first step as its base (the
  carried World, on the writer's word) and reads again (cv 01a151bc-6ef3: follow reports it, never acts) -/
  | actOnBeforeLog
  /-- `read OBJ ?` prints no `doc` line (cv 01a151bc-6f0b: the description the Bell's doc line rides on) -/
  | dropDoc
  /-- custody signs a cancel's message without its domain (`domCancel` dropped: the bare transaction
  id), a signature that is no cancel (PROTOCOL-63) -/
  | cancelUndomained
  /-- the writer pages with `frameBytesMax - 1024`, the budget that bounds the page as one field of
  the frame and leaves 890 bytes for the continuation beside it (the shape before PROTOCOL-70) -/
  | perFieldBudget
  /-- the client drops `sync`'s `--to STEPS:CHAIN`: a catch-up that compares its fold with nobody's
  position, the shape before PROTOCOL-74 (members never compared heads) -/
  | ignoreAnchor
  /-- `cancel CALL` ends `cancelled TXID` on the writer's `refused cancelled`, never settling it on
  follow's World (follow's phase 10 before PROTOCOL-71) -/
  | trustCancel
  /-- the writer records a judged refusal under ANOTHER code (the next one) while answering the
  honest name: a forged refusal record, the lie in the log and not in the reply. A page carries a judged refusal as `1 ‖ call` only, so nothing on
  the page states the record; the follower re-derives it by its own `judge`, and the page's stated
  chain (over the writer's record) is what refuses the forgery (HOST-75) -/
  | forgesRefusal
  deriving DecidableEq, Repr

/-- A row's plant: the mutation, and the line that must catch it with the outcome it then gets. -/
inductive Plant
  /-- under `mutation`, the lines before `line` keep their outcomes and line `line` gets `got` -/
  | caught (mutation : Mutation) (line : Nat) (got : Expect)
  /-- an `exe` row's executable runs its own plant -/
  | internal (what : String)
  /-- no cheap plant exists (a plant is a vacuity check run when cheap, never a landing gate: CHARTER,
  Ember 10-24): the row was MEASURED red against the code it replaced, as `what` says -/
  | measured (what : String)
  deriving Repr

/-- A row: one fresh deployment, how it is driven, what it reaches, and its plant. -/
structure Row where
  name : String
  /-- the minidregg rows this row replaces -/
  replaces : List String
  /-- the operations the row's commands drive (an `exe` row drives none: it has no wire) -/
  ops : List Op
  /-- the receiver kinds (`Kernel.Receive.Body` constructors) the row reaches -/
  kinds : List String
  drive : Drive
  plant : Plant
  /-- a piece of the system the row needs that does not exist yet, with its owner: the row is
  PENDING by that name, never PASS and never a red that hides the others -/
  blockedOn : Option String := none
  /-- the writer's page budget for this row, when the row drives a misconfigured writer on purpose
  (a fault of the row, never the parameters' setting) -/
  pageBudget : Option Nat := none
  deriving Repr

def Row.lines (r : Row) : List Line :=
  match r.drive with
  | .members ls => ls
  | .exe _ _ _ => []

private def ok (actor : String) (argv : List String) : Line := { actor, act := .cmd argv, expect := .ok }
private def no (actor : String) (argv : List String) (name : String) : Line :=
  { actor, act := .cmd argv, expect := .refused name }
private def okBind (actor : String) (argv : List String) (b : String) : Line :=
  { actor, act := .cmd argv, expect := .ok, bind := some b }

/-! ## Packages the rows install (LANG's text form; `install` reads it) -/

/-- The request and verdict types as a resident pastes them: printed from LANG's own types, never
restated. -/
def reqTy : String := Lang.Print.tyText Lang.reqTy (by decide +kernel)
def verdictTy : String := Lang.Print.tyText Lang.verdictTy

/-- A law package over a data object, with one law `l` whose body is `verdict`. -/
def lawPackage (l verdict : String) : String :=
  s!"(package (imports) (doc) (state (rec)) (iface (rec ({l} (-> (rec) (-> (rec) (-> {reqTy} {verdictTy}))))))
    (methods) (laws {l}) (rels)
    (body (record ({l} (fn (old (rec)) (new (rec)) (r {reqTy}) {verdict})))))"

def permitAll : String := lawPackage "permit" s!"(inj {verdictTy} ok (record))"
/-- Admits a birth and its own adoption (KERNEL-27: a new law judges the state it is adopted over
under `adopt`) and refuses every other act: writes, invokes and its own replacement. A deny-all law
cannot be adopted at all, so this is what "deny the newcomer and the repair" is. -/
def sealedLaw : String :=
  let no := s!"(inj {verdictTy} refused \"sealed\")"
  lawPackage "sealed" s!"(case (. r occasion) (adopt x (inj {verdictTy} ok (record))) (birth x (inj {verdictTy} ok (record))) (invoke x {no}) (relaw x {no}) (write x {no}))"
def hermesLaw : String := lawPackage "hermes" s!"(inj {verdictTy} ok (record))"

/-- THE BAR's programmed object: a counter whose method `add n` adds to its total, judged by one
law `bounded` (total at most 10^6), so every invoke runs a method AND a law. -/
def counter : String :=
  let S := "(rec (total nat))"
  let res := Lang.Print.tyText (Lang.resultTy (.record [("total", .nat)])) (by decide +kernel)
  s!"(package (imports) (doc) (state {S})
    (iface (rec (add (-> (rec) (-> {S} (-> nat (-> {reqTy} {res})))))
                (bounded (-> {S} (-> {S} (-> {reqTy} {verdictTy}))))))
    (methods add) (laws bounded) (rels)
    (body (record
      (add (fn (v (rec)) (s {S}) (n nat) (r {reqTy})
        (record (calls {Lang.Print.noCallsText}) (edits (record)) (state (record (total (+ (. s total) n)))))))
      (bounded (fn (old {S}) (new {S}) (r {reqTy})
        (if (<= (. new total) 1000000)
            (inj {verdictTy} ok (record))
            (inj {verdictTy} refused \"over a million\")))))))"

/-- A queue of rings over a relation (PROTOCOL-51's stand-in for the Bell as a queue, cv
01a14ece-43f1, until LANG re-cuts the Bell): `ring` inserts its text at key `(round, n)`, `n` the
state's `next`, and moves `next` on. Written in LANG's authoring surface, installed as the core text
LANG's one printer gives it. -/
def ringsSource : String := "
(package
  (state (rec (next nat)))
  (rel rings (key (round nat) (n nat)) (val (rec (text bytes))) (limit 64))
  (method ring (arg (rec (round nat) (text bytes))) (edits 1)
    (done (with state (next (+ state.next 1)))
      (insert rings (record (round arg.round) (n state.next)) (record (text arg.text)))))
  (law always (else ok)))
"

/-- `ringsSource` as `install` reads it (empty, and so refused by `install`, if it had no text). -/
def ringsQueue : String :=
  match Lang.Surface.readPackage ringsSource with
  | .ok p => (Lang.Print.package p).getD ""
  | .error _ => ""

/-- A board of posts (KERNEL-54's recorded class for the rows that need one): `post` inserts its
text at key `k` and leaves the state alone, so a post at a TAKEN key derives on any World and is
refused by the kernel, `keyTaken`, authenticated and RECORDED (a stale is never recorded). -/
def boardSource : String := "
(package
  (state (rec))
  (rel posts (key (k nat)) (val (rec (text bytes))) (limit 64))
  (method post (arg (rec (k nat) (text bytes))) (edits 1)
    (done state (insert posts (record (k arg.k)) (record (text arg.text)))))
  (law always (else ok)))
"

/-- `boardSource` as `install` reads it. -/
def board : String :=
  match Lang.Surface.readPackage boardSource with
  | .ok p => (Lang.Print.package p).getD ""
  | .error _ => ""

/-- A board of ONE slot whose rows may be retracted (ROOT's instance for the `admitsRecorded`
tooth under KERNEL-54): `post` inserts (unpinned, judged on the current World: `relationFull` once
the slot is taken, authenticated and RECORDED), `clear` retracts a row (a PINNED row effect: the plan
pins it from follow's World, `Command.derivePins` on `rowUnpinned`). The printed package orders its
methods by name: `clear` is method 0, `post` method 1. -/
def slotSource : String := "
(package
  (state (rec))
  (rel posts (key (k nat)) (val (rec (text bytes))) (limit 1) (retract))
  (method post (arg (rec (k nat) (text bytes))) (edits 1)
    (done state (insert posts (record (k arg.k)) (record (text arg.text)))))
  (method clear (arg (rec (k nat))) (edits 1)
    (done state (retract posts (record (k arg.k)))))
  (law always (else ok)))
"

/-- `slotSource` as `install` reads it. -/
def slot : String :=
  match Lang.Surface.readPackage slotSource with
  | .ok p => (Lang.Print.package p).getD ""
  | .error _ => ""

/-! ## The rows -/

/-- A newcomer joins: `init` (a join token for its sponsor), the sponsor `enroll`s it (spending one
of its World grant's enrolments) and grants it `observe` on the World, attenuated from its own
(following the log, KERNEL-20). Binds `NAME` (the member) and `NAME.grant` (its World grant). -/
def join (sponsor name : String) : List Line :=
  [okBind name ["init", s!"@{sponsor}"] s!"{name}.join",
   okBind sponsor ["enroll", s!"@{name}.join"] name,
   okBind sponsor ["grant", "world", s!"@{name}", "observe", "--via", s!"@{sponsor}.grant"] s!"{name}.grant"]

/-- The welcome every member row starts from: a newcomer, an object `shared` the sponsor owns,
judged by `permit`, and the newcomer's grant `g` to observe and mutate it. -/
def welcome : List Line :=
  join "sponsor" "newcomer" ++
  [okBind "sponsor" ["install", permitAll] "permit",
   okBind "sponsor" ["create", "@permit"] "shared",
   okBind "sponsor" ["grant", "@shared", "@newcomer", "observe,mutate"] "g"]

/-- The sponsor's board `posts` with its first post at key 1, public to `post` (`bpub`), and READER
having read its description (binding `posts.post`): what a recorded `keyTaken` needs. -/
def boardWith (reader : String) : List Line :=
  [okBind "sponsor" ["install", board] "board",
   okBind "sponsor" ["create", "--pkg", "@board", "(record)"] "posts",
   okBind "sponsor" ["grant", "@posts", "anyone", "invoke:0"] "bpub",
   ok "sponsor" ["invoke", "@posts", "0", "(record (k 1) (text \"first\"))"],
   { actor := reader, act := .cmd ["read", "@posts", "?"], expect := .ok, bind := some "posts" }]

/-- Every command reads through the member's own follow, which catches up from the writer's log
(`log`) before it answers; a write is a `submit`. -/
def everyCommand : List Op := [.command, .resume, .log]
def everyWrite : List Op := everyCommand ++ [.submit]
def settled : List Op := everyWrite ++ [.lookup]

/-- J0–J5: a clean start, an independent newcomer, a resource, a grant, a signed read and write; a
stranger refused at the log for both; a write without the grant; a write planned on a World that
moved before it landed. Then a public object: the owner grants `anyone` (KERNEL-26), and a member
enrolled after that grant writes through it (without it, `noGrant`). -/
def journey : Row where
  name := "journey"
  replaces := ["journey/J0", "journey/J1", "journey/J2", "journey/J3", "journey/J4", "journey/J5",
    "welcomecontinuity"]
  ops := everyWrite
  kinds := ["enroll", "install", "create", "grant", "write"]
  drive := .members (welcome ++ [
    ok "newcomer" ["write", "@shared", "2", "1", "--via", "@g"],
    ok "newcomer" ["read", "@shared", "2=1"],
    no "stranger" ["read", "@shared"] "unknownKey",
    no "stranger" ["write", "@shared", "2", "9"] "unknownKey",
    no "newcomer" ["write", "@shared", "2", "3"] "noGrant",
    { actor := "sponsor", act := .cmd ["write", "@shared", "2", "9"], expect := .declined "stale",
      fault := .race "newcomer" ["write", "@shared", "2", "8", "--via", "@g"] },
    ok "newcomer" ["read", "@shared", "2=8"]] ++
    -- a public object (KERNEL-26): a grant to `anyone` lets a member enrolled AFTER it mutate
    [okBind "sponsor" ["grant", "@shared", "anyone", "observe,mutate"] "public"] ++
    join "sponsor" "visitor" ++
    [no "visitor" ["write", "@shared", "4", "1"] "noGrant",
     ok "visitor" ["write", "@shared", "4", "1", "--via", "@public"],
     ok "newcomer" ["read", "@shared", "4=1"]])
  plant := .caught .openLog 8 .ok

/-- J6: stop and reopen; the state and the journal survive; the attempt store's lookup of a
committed call answers its receipt (a retry is the same call: it lands once, KERNEL-7). -/
def reopen : Row where
  name := "reopen"
  replaces := ["journey/J6", "hostupgrade/REOPEN"]
  ops := settled
  kinds := ["enroll", "install", "create", "grant", "write"]
  drive := .members (welcome ++ [
    ok "newcomer" ["write", "@shared", "2", "3", "--via", "@g"],
    { actor := "operator", act := .restart, expect := .ok },
    ok "newcomer" ["read", "@shared", "2=3"],
    { actor := "newcomer", act := .retry, expect := .ok },
    ok "newcomer" ["write", "@shared", "2", "4", "--via", "@g"]])
  plant := .caught .forgetJournal 9 .absent

/-- J7, J8: a law replaced keeps the grant; a sealed law refuses the newcomer and the repair. -/
def laws : Row where
  name := "laws"
  replaces := ["journey/J7", "journey/J8", "journey/J13"]
  ops := everyWrite
  kinds := ["enroll", "install", "create", "grant", "write", "law"]
  drive := .members (welcome ++ [
    okBind "sponsor" ["install", sealedLaw] "deny",
    ok "newcomer" ["write", "@shared", "2", "7", "--via", "@g"],
    ok "sponsor" ["law", "@shared", "@deny"],
    no "newcomer" ["write", "@shared", "2", "8", "--via", "@g"] "lawDenied",
    no "sponsor" ["law", "@shared", "@permit"] "lawDenied",
    ok "newcomer" ["read", "@shared", "2=7"]])
  plant := .caught .skipJudge 9 .ok

/-- JROT, JROTL: pre-rotation; a stolen daily key cannot rotate (the thief's custody does not hold
the precommitted next key); a lost rotation reply is found by lookup; a rotation that never reached
the writer ends `open` (follow's own World says its window is live, PROTOCOL-46) and leaves custody
on the old key, which still signs (custody advances on settlement). The plant is custody advancing
when it signs: the rotation that never landed leaves it on a key the World never installed, so the
probe cannot even read (`unknownKey`, and no rotation is armed) and line 11 is `uncertain`. -/
def rotate : Row where
  name := "rotate"
  replaces := ["journey/JROT", "journey/JROTL"]
  ops := settled
  kinds := ["enroll", "install", "create", "grant", "rotate", "write"]
  drive := .members (welcome ++ [
    { actor := "thief", act := .cmd ["rotate"], expect := .refused "notPrecommitted",
      fault := .stolenKey "newcomer" },
    ok "newcomer" ["rotate"],
    ok "newcomer" ["write", "@shared", "2", "4", "--via", "@g"],
    { actor := "newcomer", act := .cmd ["rotate"], expect := .ok, fault := .dropReply },
    { actor := "newcomer", act := .retry, expect := .ok },
    { actor := "newcomer", act := .cmd ["rotate"], expect := .open, fault := .neverForward },
    ok "newcomer" ["write", "@shared", "2", "5", "--via", "@g"],
    ok "newcomer" ["read", "@shared", "2=5"]])
  plant := .caught .advanceOnSend 11 .uncertain

/-- JAUDIT: a follower re-derives the Store from genesis, every Turn from its event, by the same
receivers. A flipped byte in a copy of the Store's base is refused `baseCorrupt` by the Store's
open (`Host.BaseFault.baseCorrupt`: open trusts one base and its tail, so the base is where a
flipped byte must be caught); a flipped byte in a SERVED event is refused `eventMismatch` at its height
by the re-derivation; an event the writer omits is refused `chainMismatch` at the page. -/
def audit : Row where
  name := "audit"
  replaces := ["journey/JAUDIT", "jstoreaudit"]
  ops := everyWrite
  kinds := ["enroll", "install", "create", "grant", "write"]
  drive := .members (welcome ++ join "sponsor" "auditor" ++ [
    ok "newcomer" ["write", "@shared", "2", "1", "--via", "@g"],
    ok "sponsor" ["write", "@shared", "3", "2"],
    { actor := "auditor", act := .cmd ["read", "@shared", "2=1", "3=2"], expect := .ok, fault := .cold },
    { actor := "operator", act := .reopenFlipped 6, expect := .refused "baseCorrupt" },
    { actor := "auditor", act := .cmd ["read", "@shared"], expect := .refused "eventMismatch",
      fault := .flipEvent 8 },
    { actor := "auditor", act := .cmd ["read", "@shared"], expect := .refused "chainMismatch",
      fault := .dropLastEvent }])
  plant := .caught .followVerifyAll 13 (.refused "chainMismatch")

/-- A log page holds at most a page budget of events (HOST-17), so it can end before the writer's
tip, even inside a batch; a cold follower pages from each page's height until it reaches the tip
the writer states. New in nanodregg (minidregg served the whole log in one frame), so it replaces
no row. A page also ends at `recordTurnsMax` (64) events, and at these writes that is what ends it,
under both parameter sets, before the budget (`Rows.Params.pageBudget`, every event the kernel
admits) does: the row's 108 steps are two pages, so `lieTip` is read at line 11 (re-measured at the
derived budget, PROTOCOL-18). -/
def paging : Row where
  name := "paging"
  replaces := []
  ops := everyWrite
  kinds := ["enroll", "install", "create", "grant", "write"]
  drive := .members (welcome ++ join "sponsor" "auditor" ++ [
    { actor := "newcomer", act := .cmd ["write", "@shared", "2", "1", "--via", "@g"], expect := .ok,
      times := 100 },
    ok "sponsor" ["write", "@shared", "3", "9"],
    { actor := "auditor", act := .cmd ["read", "@shared", "2=1", "3=9"], expect := .ok, fault := .cold }])
  plant := .caught .lieTip 11 (.refused "expect")

/-- A follower that cold-starts more than two windows behind the tip (PROTOCOL-19): its first
envelope, signed for its own height + window, is refused `expired` with the writer's height; follow
re-signs ONCE for that height + window, and every later page's envelope covers the tip the
previous page stated, so it reaches the tip. New in nanodregg (the defect was found by reasoning,
PROTOCOL-19); every rows actor's window is 100, so 210 writes put the tip two windows past genesis.
`sync` (PROTOCOL-38) is the catch-up alone: its cold run re-signs the same way, then the read. -/
def coldCatchUp : Row where
  name := "coldCatchUp"
  replaces := []
  ops := everyWrite
  kinds := ["enroll", "install", "create", "grant", "write"]
  drive := .members (welcome ++ join "sponsor" "auditor" ++ [
    { actor := "newcomer", act := .cmd ["write", "@shared", "2", "1", "--via", "@g"], expect := .ok,
      times := 210 },
    { actor := "auditor", act := .cmd ["sync"], expect := .ok, fault := .cold },
    { actor := "auditor", act := .cmd ["read", "@shared", "2=1"], expect := .ok, fault := .cold }])
  plant := .caught .unstatedExpiry 10 (.refused "expired")

/-- THIN (PROTOCOL-14, option A; minidregg's `journey.d/jthin-consent.sh`, which drove the
deleted thin consent frames 230–232): a member that never folded the log adopts the writer's
newest base, pinned by a full follower's word, then is an ordinary follower from the base on: it
re-derives the suffix and signs a write planned on it. The full follower (`operator`) catches up,
the writer seals at its tip, and the operator states the pin of its own World (`attest`, out of
band until PROTOCOL-42; now an invitation the operator signs, `invite`, and the thin member's
`adopt INVITE KEY` accepts it under the operator's key). A newer seal moves the base off the pin: a
member (`late`) holding the old invitation is refused `baseMoved`. -/
def thin : Row where
  name := "thin"
  replaces := ["journey.d/jthin-consent"]
  ops := everyWrite ++ [.read]
  kinds := ["enroll", "install", "create", "grant", "write"]
  drive := .members (welcome ++ join "sponsor" "thin" ++ join "sponsor" "late" ++ [
    okBind "sponsor" ["grant", "@shared", "@thin", "observe,mutate"] "gt",
    ok "newcomer" ["write", "@shared", "2", "1", "--via", "@g"],
    ok "operator" ["read", "@shared", "2=1"],
    { actor := "operator", act := .seal, expect := .ok },
    okBind "operator" ["invite", "@inputs"] "pin",
    ok "thin" ["adopt", "@pin", "@operator.key"],
    ok "newcomer" ["write", "@shared", "2", "2", "--via", "@g"],
    ok "thin" ["write", "@shared", "3", "7", "--via", "@gt"],
    ok "thin" ["read", "@shared", "2=2", "3=7"],
    { actor := "operator", act := .seal, expect := .ok },
    no "late" ["adopt", "@pin", "@operator.key"] "baseMoved"])
  plant := .caught .forgeBase 17 (.refused "baseMismatch")

/-- A thin member whose pin is more than a window old (PROTOCOL-37; PROTOCOL-4's leftover, adopt's
`reSign` path). The thin member's client signs for a window of 5 heights; the operator seals and
states the pin, then the log runs 12 writes past it, fewer than the rows' seal cadence needs, so the
newest base is still the pinned one (a deployed writer's seal cadence is in bytes, its window in
heights: a pin a window old with the base unmoved is the ordinary case). `adopt`'s first envelope is signed for one window from height 0 (a pin names a step count, PROTOCOL-41). The
writer refuses it `expired` and states its height, and follow re-signs ONCE for that height + window
(`Command.reSign`, the same rule as a cold follower's, `reSign_ok`), then pages the base. Its first
write after that catches up from the base's height, again more than a window behind (held by its
expectation; the plant stops the row at the adopt). Without the stated height (`unstatedExpiry`) the adopt is `refused expired`.
New in nanodregg: no minidregg journey adopted a stale pin. -/
def thinStale : Row where
  name := "thinStale"
  replaces := []
  ops := everyWrite ++ [.read]
  kinds := ["enroll", "install", "create", "grant", "write"]
  drive := .members (welcome ++ join "sponsor" "thin" ++ [
    okBind "sponsor" ["grant", "@shared", "@thin", "observe,mutate"] "gt",
    { actor := "thin", act := .window 5, expect := .ok },
    ok "operator" ["read", "@shared"],
    { actor := "operator", act := .seal, expect := .ok },
    okBind "operator" ["invite", "@inputs"] "pin",
    { actor := "newcomer", act := .cmd ["write", "@shared", "2", "1", "--via", "@g"], expect := .ok,
      times := 12 },
    ok "thin" ["adopt", "@pin", "@operator.key"],
    ok "thin" ["write", "@shared", "3", "7", "--via", "@gt"],
    ok "thin" ["read", "@shared", "2=1", "3=7"]])
  plant := .caught .unstatedExpiry 15 (.refused "expired")

/-- HOST-43 as members meet it (PROTOCOL-47): the operator seals the stopped writer by the deployed
act (`Host.sealNow`, `host seal STORE`'s core), and its `invite` pins the newest base its own follow
verified, its OWN digest of its own World at the base's step count, never the writer's tip. So an
invitation made after the log moved on past the base (twelve writes, fewer than the rows' seal
cadence) still names the base, and a thin member adopts it; before PROTOCOL-47 `invite` pinned the
tip, and this adopt was `baseMoved` (CLIENT-5's finding). A thin member holding the earlier pin of
the same base adopts too. The plant is a seal that seals nothing (`sealIgnored`): the first
invitation then pins the writer's genesis base (the newest base the operator's follow verified),
which a thin member already holds, so its adopt (line 19) is refused `notBehind` by name. That adopt
comes first: what the SECOND invitation pins under the plant depends on whether the writer's own
cadence sealed during the twelve writes, which is a byte count and differs between the toy and the
deployed parameters (PROTOCOL-50); the first invitation's does not. New in nanodregg. -/
def sealRow : Row where
  name := "seal"
  replaces := []
  ops := everyWrite ++ [.read]
  kinds := ["enroll", "install", "create", "grant", "write"]
  drive := .members (welcome ++ join "sponsor" "thin" ++ join "sponsor" "thin2" ++ [
    okBind "sponsor" ["grant", "@shared", "@thin", "observe,mutate"] "gt",
    ok "newcomer" ["write", "@shared", "2", "1", "--via", "@g"],
    ok "operator" ["read", "@shared", "2=1"],
    { actor := "operator", act := .seal, expect := .ok },
    okBind "operator" ["invite", "@inputs"] "pin",
    { actor := "newcomer", act := .cmd ["write", "@shared", "2", "2", "--via", "@g"], expect := .ok,
      times := 12 },
    okBind "operator" ["invite", "@inputs"] "pin2",
    ok "thin2" ["adopt", "@pin", "@operator.key"],
    ok "thin" ["adopt", "@pin2", "@operator.key"],
    ok "thin" ["write", "@shared", "3", "7", "--via", "@gt"],
    ok "thin" ["read", "@shared", "2=2", "3=7"]])
  plant := .caught .sealIgnored 19 (.refused "notBehind")

/-- PROTOCOL-49 (HOST-48's ruling): a page the writer could not build is refused `pageIo` and the
writer serves on, so the member's command ends `pageIo` (restart class), keeps what it absorbed, and
the same command run again succeeds. Once on a write's catch-up (nothing signed: it lands once,
after the re-run) and once on an adoption's base page (`read`). The plant reads `pageIo` as the old
final refusal: line 9 is `refused pageIo`. -/
def pageIoRow : Row where
  name := "pageIo"
  replaces := []
  ops := everyWrite ++ [.read]
  kinds := ["enroll", "install", "create", "grant", "write"]
  drive := .members (welcome ++ join "sponsor" "thin" ++ [
    { actor := "newcomer", act := .cmd ["write", "@shared", "2", "1", "--via", "@g"], expect := .pageIo,
      fault := .pageIo },
    ok "newcomer" ["write", "@shared", "2", "1", "--via", "@g"],
    ok "operator" ["read", "@shared", "2=1"],
    { actor := "operator", act := .seal, expect := .ok },
    okBind "operator" ["invite", "@inputs"] "pin",
    { actor := "thin", act := .cmd ["adopt", "@pin", "@operator.key"], expect := .pageIo, fault := .pageIo },
    ok "thin" ["adopt", "@pin", "@operator.key"],
    ok "thin" ["read", "@shared", "2=1"]])
  plant := .caught .pageIoFatal 9 (.refused "pageIo")

/-- PROTOCOL-47's tooth: a sponsor never signs the Host's word for where its base is. Every log
page states the writer's newest durable base (its step count and digest); follow records its OWN
World's digest where its fold sits at that step count, and `invite` pins it only when the stated
digest is that one. Here the operator seals, invites (its fold sat at the base), the log moves on,
and it invites again (the same base, the same pin). The plant is a writer that states its TIP as
its base with the sealed base's digest: follow's fold sits at the stated "base" at every page's end,
its own digest there is not the stated one once the log has moved past the seal, and the second
invitation is refused `baseMismatch` by name. New in nanodregg. -/
def basePin : Row where
  name := "basePin"
  replaces := []
  ops := everyWrite
  kinds := ["enroll", "install", "create", "grant", "write"]
  drive := .members (welcome ++ [
    ok "newcomer" ["write", "@shared", "2", "1", "--via", "@g"],
    ok "operator" ["read", "@shared", "2=1"],
    { actor := "operator", act := .seal, expect := .ok },
    okBind "operator" ["invite", "@inputs"] "pin",
    ok "newcomer" ["write", "@shared", "2", "2", "--via", "@g"],
    okBind "operator" ["invite", "@inputs"] "pin2"])
  plant := .caught .lieBase 11 (.refused "baseMismatch")

/-- Cross-World replay (OPS, ASSEMBLY-ops D3; reproduced on 87c721e against the `host` exe): two
`host genesis` runs with the same name and founders made two Worlds that admitted each other's
calls. KERNEL-24 binds every call to its World's origin (`Unsigned.world`, checked first;
`Kernel.Receive.admitted_elsewhere_refused`), and the origin commits to the genesis nonce. So the
writer's whole log replayed into a Store whose genesis differs ONLY in its nonce is refused
`wrongWorld`, every call, by that name (`declined`: an unauthenticated refusal, recorded nowhere and
not final, PROTOCOL-41). The same log into a Store of the same nonce is a restore of
the same World and is admitted, every call: the binding is the origin, not the process or the
Store. Without the check, line 7 is `unknownKey` (founder ids are keyed by the origin), so the
expectation by name holds the check; the plant holds the nonce. -/
def wrongWorld : Row where
  name := "wrongWorld"
  replaces := ["ops/replay-20261016"]
  ops := everyWrite
  kinds := ["enroll", "install", "create", "grant", "write"]
  drive := .members (welcome ++ [
    ok "newcomer" ["write", "@shared", "2", "1", "--via", "@g"],
    { actor := "operator", act := .replayLog false, expect := .declined "wrongWorld" },
    { actor := "operator", act := .replayLog true, expect := .ok }])
  plant := .caught .nonceRepeats 7 .ok

/-- The read half of `wrongWorld` (PROTOCOL-29): a member's signed `log` envelope, carried to a
Store whose genesis differs only in its nonce, is refused `wrongWorld` by that name (the envelope
names its World, checked first: never `unknownKey`, though the founder ids differ too); the same
envelope to a Store of the same nonce, a restore of the same World, is served. The plant holds the
nonce: with the second Store's nonce repeated, line 6 is served. -/
def wrongWorldRead : Row where
  name := "wrongWorldRead"
  replaces := ["ops/replay-20261016"]
  ops := everyWrite
  kinds := ["enroll", "install", "create", "grant"]
  drive := .members (welcome ++ [
    { actor := "operator", act := .readElsewhere false, expect := .refused "wrongWorld" },
    { actor := "operator", act := .readElsewhere true, expect := .ok }])
  plant := .caught .nonceRepeats 6 .ok

/-- KERNEL-33's journal prune, as an attempt store meets it. A call the Host never saw (`sponsor`'s,
never forwarded) is, past its window, `refused expired`: true while the journal still answers
(`notBefore + 2·windowMax > height`). A call that COMMITTED (`newcomer`'s, its reply lost and
settled by lookup) is still `ok` there. Past `journalForgets`, and past the prune that drops the
committed entry (entries under `3·windowMax`), both are `uncertain forgotten`: never `refused`, so
a call committed long ago is never reported refused. The counts are heights, so this row is not
for `rows --times` scaling (it would cut them). -/
def forgotten : Row where
  name := "forgotten"
  replaces := []
  ops := settled
  kinds := ["enroll", "install", "create", "grant", "write"]
  drive := .members (welcome ++ [
    { actor := "newcomer", act := .cmd ["write", "@shared", "2", "1", "--via", "@g"], expect := .ok,
      fault := .dropReply },
    { actor := "sponsor", act := .cmd ["write", "@shared", "3", "1"], expect := .open,
      fault := .neverForward },
    okBind "operator" ["create", "@permit"] "own",
    { actor := "operator", act := .cmd ["write", "@own", "2", "1"], expect := .ok, times := 110 },
    { actor := "sponsor", act := .retry, expect := .refused "expired" },
    { actor := "newcomer", act := .retry, expect := .ok },
    { actor := "operator", act := .cmd ["write", "@own", "2", "1"], expect := .ok, times := 3100 },
    { actor := "sponsor", act := .retry, expect := .unsettled "forgotten" },
    { actor := "newcomer", act := .retry, expect := .unsettled "forgotten" }])
  plant := .caught .forgottenRefused 13 (.refused "forgotten")

/-- KERNEL-44's teeth over sockets (PROTOCOL-41), as KERNEL-54 re-cut them: a refusal of a class
that is not structurally final is a recorded system interaction, final for its transaction id within
the window; a STALE is never recorded. A write raced by another member's write is `declined stale`:
the writer neither records it nor ends the attempt. The attempt store's next run looks it up
(`absent`), confirms that with follow before any resend (PROTOCOL-15's condition 3), and follow's
own fold settles it `refused stale` (BEHIND: the member's own call, planned at a height follow has
reached, refused `stale` there, `Command.staleBehind`). The World's pin returns to the value the call
saw (A→B→A): the same bytes sent again are still `declined stale` (the pin reads the entry and its
version, KERNEL-54), the Host's lookup is `absent` (nothing recorded), and the next run settles
`refused stale` again. Another member asking about the call it did not plan settles `open`
(unplaceable: never final from someone else's fold). A member's refusals in one window are bounded:
sixteen recorded `keyTaken` refusals (posts at a taken key of a board), then `declined refusalBudget`, not recorded
and not final (its lookup is `absent`). A thin member then adopts a base whose step count is past its
height and catches up from its steps. Past the window the journal forgets and the first call's
lookup is `uncertain forgotten`, never `refused`. The plant is an attempt store that takes the
Host's decline as final: line 13 ends on that claim, and step 4 checks it on follow's World, where the
decline is no refusal: `hostContradicted refused open`. The counts are heights, so this row is not for
`rows --times` scaling. -/
def refusedRow : Row where
  name := "refused"
  replaces := []
  ops := settled ++ [.read]
  kinds := ["enroll", "install", "create", "grant", "write", "invoke"]
  drive := .members (welcome ++ join "sponsor" "auditor" ++ [
    okBind "sponsor" ["grant", "@shared", "@auditor", "observe,mutate"] "g2",
    ok "sponsor" ["write", "@shared", "2", "1"],
    ok "newcomer" ["read", "@shared", "2=1"],
    ok "auditor" ["read", "@shared", "2=1"],
    -- signed on the World where 2=1, raced by the sponsor's write: the writer declines it stale
    { actor := "newcomer", act := .cmd ["write", "@shared", "3", "7", "--via", "@g"],
      expect := .declined "stale", fault := .race "sponsor" ["write", "@shared", "2", "5"] },
    -- the next run: lookup `absent`, follow's own fold settles it
    { actor := "newcomer", act := .rerun, expect := .refused "stale" },
    -- A→B→A: the content the call saw holds again; its version does not
    ok "sponsor" ["write", "@shared", "2", "1"],
    { actor := "newcomer", act := .resubmit, expect := .declined "stale" },
    { actor := "newcomer", act := .retry, expect := .absent },
    { actor := "newcomer", act := .rerun, expect := .refused "stale" },
    ok "newcomer" ["read", "@shared", "2=1"],
    -- unplaceable: another member's follow did not plan the call, so it never settles it final
    { actor := "auditor", act := .receiptOf "newcomer", expect := .ok, prints := some "settle open" },
    ] ++ boardWith "auditor" ++ [
    -- one member's window budget: sixteen recorded refusals (posts at a taken key), then
    -- `declined refusalBudget`
    ok "sponsor" ["write", "@shared", "2", "9"]] ++
    (List.range Kernel.Bounds.refusalsPerWindow).map (fun i =>
      { actor := "auditor", act := .forge ["invoke", "@posts", "@posts.post",
          s!"(record (k 1) (text \"{i}\"))", "--via", "@bpub"], expect := .refused "keyTaken" }) ++ [
    { actor := "auditor", act := .forge ["invoke", "@posts", "@posts.post",
        "(record (k 1) (text \"over\"))", "--via", "@bpub"], expect := .declined "refusalBudget" },
    { actor := "auditor", act := .retry, expect := .absent }] ++
    -- a thin member adopts a base sealed after seventeen recorded refusals, where the World's step
    -- count is past its height: it pages the log from the base's STEPS (paging from its height
    -- would re-absorb recorded steps and be refused)
    join "sponsor" "thinr" ++ [
    ok "operator" ["read", "@shared", "2=9"],
    { actor := "operator", act := .seal, expect := .ok },
    okBind "operator" ["invite", "@inputs"] "pin",
    ok "thinr" ["adopt", "@pin", "@operator.key"],
    ok "sponsor" ["write", "@shared", "2", "4"],
    ok "thinr" ["read", "@shared", "2=4"],
    -- past the window: the record is pruned, and the answer is `forgotten`, never `refused`
    okBind "operator" ["create", "@permit"] "own",
    { actor := "operator", act := .cmd ["write", "@own", "2", "1"], expect := .ok, times := 3100 },
    { actor := "newcomer", act := .retry, expect := .unsettled "forgotten" }])
  -- the store's `refused` is checked by follow's own World at step 4 (R7): the decline it settled
  -- is no refusal there, so follow says `hostContradicted refused open`, never `refused stale`
  plant := .caught .settleDecline 13 (.contradicted "refused open")

/-- KERNEL-44's admit-after-refusal tooth on the arm KERNEL-54 leaves live (ROOT's ruling on
PROTOCOL-52): an unpinned row birth is judged on the CURRENT World, so its refusal can stop being
derivable. The sponsor's post fills a one-slot board; the auditor forges a post at another key,
refused `relationFull` and RECORDED; the sponsor clears the slot (a retract, a pinned row effect,
which `plan` pins from follow's World); the auditor sends the same signed bytes again, and they are
answered `refused relationFull` from the record, never re-derived and never admitted, so the slot
stays free for the sponsor's next post. The plant is a writer that commits a recorded call while
answering it `refused relationFull` (line 16 reads the same either way: the lie is in the log, not
the reply): the sponsor's next command catches up through the logged Turn, and its own follower
refuses it by the kernel's name, `refusedFinal`, at line 17, as the old tooth was caught on the line
after its resubmit. -/
def refusedFinalRow : Row where
  name := "refusedFinal"
  replaces := []
  ops := everyWrite
  kinds := ["enroll", "install", "create", "grant", "invoke"]
  drive := .members (welcome ++ join "sponsor" "auditor" ++ [
    okBind "sponsor" ["install", slot] "slotPkg",
    okBind "sponsor" ["create", "--pkg", "@slotPkg", "(record)"] "slot",
    okBind "sponsor" ["grant", "@slot", "anyone", "invoke:1"] "spub",
    ok "sponsor" ["invoke", "@slot", "1", "(record (k 1) (text \"first\"))"],
    { actor := "auditor", act := .cmd ["read", "@slot", "?"], expect := .ok, bind := some "slot" },
    -- the slot is taken: the kernel refuses the post `relationFull`, and the writer records it
    { actor := "auditor", act := .forge ["invoke", "@slot", "@slot.post",
        "(record (k 2) (text \"second\"))", "--via", "@spub"], expect := .refused "relationFull" },
    -- a retract: the plan pins the row from follow's World (`derivePins` on `rowUnpinned`)
    ok "sponsor" ["invoke", "@slot", "0", "(record (k 1))"],
    -- the same signed bytes would now derive and admit; the record answers them
    { actor := "auditor", act := .resubmit, expect := .refused "relationFull" },
    ok "sponsor" ["invoke", "@slot", "1", "(record (k 3) (text \"third\"))"]])
  plant := .caught .admitsRecorded 17 (.refused "refusedFinal")

/-- PROTOCOL-42: a joiner derives the World it joins from an invitation its sponsor signed, never
from the first bytes it sees. The sponsor signs one (`invite`, from the World's origin inputs, which
founders hold from `host genesis` and joiners from their own invitation); a joiner accepts it under
the sponsor key it trusts and joins, writes and reads on the World it derived. The same invitation
relayed with its nonce changed (a hostile Host's own World) is refused `pinMismatch`; relayed and
re-signed by the relay, `notSponsor`; a joiner trusting another key refuses the honest one
`notSponsor`, and so does a thin member's `adopt` of it; a sponsor asked to invite to inputs that
are not its World refuses `otherWorld`. The
plant is trust on first use: the joiner takes the forged origin, line 14 `ok`. -/
def inviteRow : Row where
  name := "invite"
  replaces := []
  ops := everyWrite
  kinds := ["enroll", "install", "create", "grant", "write"]
  drive := .members (welcome ++ [
    okBind "sponsor" ["invite", "@inputs"] "inv",
    { actor := "joiner", act := .accept "inv" "sponsor.key", expect := .ok }] ++
    join "sponsor" "joiner" ++ [
    okBind "sponsor" ["grant", "@shared", "@joiner", "observe,mutate"] "gj",
    ok "joiner" ["write", "@shared", "2", "5", "--via", "@gj"],
    ok "joiner" ["read", "@shared", "2=5"],
    { actor := "mallory", act := .accept "inv" "sponsor.key", expect := .refused "pinMismatch",
      fault := .forgeInvite false },
    { actor := "mallory", act := .accept "inv" "sponsor.key", expect := .refused "notSponsor",
      fault := .forgeInvite true },
    { actor := "joiner", act := .accept "inv" "newcomer.key", expect := .refused "notSponsor" },
    no "sponsor" ["invite", "@otherInputs"] "otherWorld",
    no "late" ["adopt", "@inv", "@newcomer.key"] "notSponsor"])
  plant := .caught .trustFirstUse 14 .ok

/-- THE BAR's purpose as a row (PROTOCOL-43; DELVETALK-LEARNINGS §4.7, §7): two friends and a
hosted resident use what the others made. Each friend (the founders) makes two counters on THE BAR's
programmed counter package and grants `anyone` its `add` (a public object, PROTOCOL-26); each adds
to the other's two (a friend's add to its own is not counted). The measure, `Protocol.Use.shared` on
the member's own World over every committed call, is at least 4 (delvetalk's go/no-go); then Hermes
joins, uses a friend's counter and makes one a friend uses: at least 5. The plant is one resident
playing every part (`oneMember`: every client signs as the sponsor): every command still succeeds,
and the count reads 0 at line 14, by name. -/
def useRow : Row where
  name := "use"
  replaces := []
  ops := everyWrite
  kinds := ["install", "create", "grant", "invoke", "enroll"]
  drive := .members ([
    okBind "sponsor" ["install", counter] "counter",
    okBind "sponsor" ["create", "--pkg", "@counter", "(record (total 0))"] "a1",
    okBind "sponsor" ["create", "--pkg", "@counter", "(record (total 0))"] "a2",
    okBind "sponsor" ["grant", "@a1", "anyone", "invoke:0"] "pa1",
    okBind "sponsor" ["grant", "@a2", "anyone", "invoke:0"] "pa2",
    okBind "operator" ["create", "--pkg", "@counter", "(record (total 0))"] "b1",
    okBind "operator" ["create", "--pkg", "@counter", "(record (total 0))"] "b2",
    okBind "operator" ["grant", "@b1", "anyone", "invoke:0"] "pb1",
    okBind "operator" ["grant", "@b2", "anyone", "invoke:0"] "pb2",
    ok "operator" ["invoke", "@a1", "0", "1", "--via", "@pa1"],
    ok "operator" ["invoke", "@a2", "0", "1", "--via", "@pa2"],
    ok "sponsor" ["invoke", "@b1", "0", "1", "--via", "@pb1"],
    ok "sponsor" ["invoke", "@b2", "0", "1", "--via", "@pb2"],
    ok "sponsor" ["invoke", "@a1", "0", "5"],
    { actor := "operator", act := .used 4, expect := .ok }] ++
    join "sponsor" "hermes" ++ [
    ok "hermes" ["invoke", "@a1", "0", "1", "--via", "@pa1"],
    okBind "hermes" ["create", "--pkg", "@counter", "(record (total 0))"] "h1",
    okBind "hermes" ["grant", "@h1", "anyone", "invoke:0"] "ph1",
    ok "sponsor" ["invoke", "@h1", "0", "1", "--via", "@ph1"],
    { actor := "hermes", act := .used 5, expect := .ok }])
  plant := .caught .oneMember 14 (.refused "unshared:0")

/-- PROTOCOL-44 (DELVETALK-LEARNINGS §4.3): an object describes itself. The sponsor makes a grain
on the shipped lifecycle package and grants `anyone` its start (the right names the method by its
index, which the owner knows). A member who has never seen the object reads its description,
`read OBJ ?`, which binds each printed `method I LABEL ARG` as `app.LABEL` = I, and starts it from
that text alone: the method index, through the public grant, with an argument of the printed type
(`(rec)`, written `(record)`). A second start is refused `lawDenied` by the package's law `phase`,
and the refusal says so on stdout (`hint lawDenied …`). The plant is a resident that does not read
the description and guesses method 0: line 7 calls `remove` through a grant to `start`,
`grantRight`. -/
def describeRow : Row where
  name := "describe"
  replaces := []
  ops := everyWrite
  kinds := ["enroll", "grant", "install", "create", "invoke"]
  drive := .members (join "sponsor" "newcomer" ++ [
    okBind "operator" ["install", "<world/grain/Lifecycle"] "lifecycle",
    okBind "sponsor" ["create", "--pkg", "@lifecycle",
      "(record (entry \"app\") (kind app) (phase installed))"] "app",
    okBind "sponsor" ["grant", "@app", "anyone", "invoke:1"] "pub",
    { actor := "newcomer", act := .cmd ["read", "@app", "?"], expect := .ok, bind := some "app",
      prints := some "law phase" },
    ok "newcomer" ["invoke", "@app", "@app.start", "(record)", "--via", "@pub"],
    { actor := "newcomer", act := .cmd ["invoke", "@app", "@app.start", "(record)", "--via", "@pub"],
      expect := .refused "lawDenied", prints := some "hint lawDenied" }])
  plant := .caught .guessMethod 7 (.refused "grantRight")

/-- PROTOCOL-48 (HOSTING-8's resident reads only through `nd --stdio`): `read OBJ` of a programmed
object prints ONE line, its state value at the package's state type (`Lang.Print.data`), the text
`Lang.Read` reads back to that value (`Proofs.Command.readText_reads`). The sponsor creates an app
from a state text; the newcomer's read prints that value, and nothing else (`exact`), as the printer's one canonical text (an
enum's case in full, `(kind (app (record)))`, where the creator wrote the reader's short form
`(kind app)`); after `start` the read prints the moved phase. The plant is a reader that prints the raw state slots (the
shape before PROTOCOL-48): line 6 is `refused unprinted`. -/
def stateRow : Row where
  name := "state"
  replaces := []
  ops := everyWrite
  kinds := ["enroll", "grant", "install", "create", "invoke"]
  drive := .members (join "sponsor" "newcomer" ++ [
    okBind "operator" ["install", "<world/grain/Lifecycle"] "lifecycle",
    okBind "sponsor" ["create", "--pkg", "@lifecycle",
      "(record (entry \"app\") (kind app) (phase installed))"] "app",
    okBind "sponsor" ["grant", "@app", "anyone", "invoke:1"] "pub",
    { actor := "newcomer", act := .cmd ["read", "@app"], expect := .ok,
      prints := some "(record (entry \"app\") (kind (app (record))) (phase (installed (record))))\n",
      exact := true },
    { actor := "newcomer", act := .cmd ["read", "@app", "?"], expect := .ok, bind := some "app" },
    ok "newcomer" ["invoke", "@app", "@app.start", "(record)", "--via", "@pub"],
    { actor := "newcomer", act := .cmd ["read", "@app"], expect := .ok,
      prints := some "(record (entry \"app\") (kind (app (record))) (phase (running (record))))\n",
      exact := true }])
  plant := .caught .rawSlots 6 (.refused "unprinted")

/-- PROTOCOL-45 (cv 01a14ade-0f69; delvetalk's top thirst, "a receipt as proof"): a member proves to
itself what happened to a call from the head it holds alone. The member's follow makes a RECEIPT
(`receipt CALL`: the roots and the trie paths for the call's id) and a phone, which holds only its own head
(height and roots, as `sync` prints them), checks it (`Receipt.check`). A committed write checks
`committed`; the same receipt relayed by a host that says "not admitted" (`absent` over the same
paths) is refused `pathMismatch`; a call the writer refused and RECORDED checks `refused` with its
code (PROTOCOL-41); a call that never reached the writer checks `absent`, inside the window. The
plant is a phone that believes the stated answer: line 10 `ok`. -/
def receiptRow : Row where
  name := "receipt"
  replaces := []
  ops := settled
  kinds := ["enroll", "install", "create", "grant", "write", "invoke"]
  drive := .members (welcome ++ [
    ok "newcomer" ["write", "@shared", "2", "1", "--via", "@g"],
    ok "operator" ["read", "@shared", "2=1"],
    { actor := "newcomer", act := .receiptOf "newcomer", expect := .ok, bind := some "rc1" },
    { actor := "operator", act := .verify "newcomer" "rc1", expect := .ok, prints := some "committed" },
    { actor := "operator", act := .verify "newcomer" "rc1", expect := .refused "pathMismatch",
      fault := .forgeReceipt },
    ok "sponsor" ["write", "@shared", "2", "5"]] ++ boardWith "newcomer" ++ [
    { actor := "newcomer", act := .forge ["invoke", "@posts", "@posts.post",
        "(record (k 1) (text \"again\"))", "--via", "@bpub"], expect := .refused "keyTaken" },
    { actor := "newcomer", act := .receiptOf "newcomer", expect := .ok, bind := some "rc2" },
    ok "operator" ["read", "@shared", "2=5"],
    { actor := "operator", act := .verify "newcomer" "rc2", expect := .ok, prints := some "refused" },
    { actor := "sponsor", act := .cmd ["write", "@shared", "3", "1"], expect := .open,
      fault := .neverForward },
    { actor := "sponsor", act := .receiptOf "sponsor", expect := .ok, bind := some "rc3" },
    { actor := "operator", act := .verify "sponsor" "rc3", expect := .ok, prints := some "absent" }])
  plant := .caught .trustReceipt 10 .ok

/-- DESIGN-OBS §1.5, the HEALTH RECEIPT: a member asks its World what it has spent this window and
hands the answer to another member, who checks it against the head it holds alone. The sponsor's
invoke spent ticks; its own follow prints `receipt --health` (the meter, its refusals and the World's,
each with its window-trie path); the operator, caught up to the same tip, checks it (`Health.check`):
`ok`, with the ticks. The same receipt relayed as "spent nothing" (ticks 0 over the same paths) is
`pathMismatch`; asked about another member, `otherMember`; checked after the World moved, against
the newer head, `headMismatch` — a health receipt is a statement about ONE head, never a standing
one. A fresh receipt at the new head checks. The plant is a phone that believes the stated answer
once the roots match: the relayed "spent nothing" line reads `ok`. -/
def healthRow : Row where
  name := "health"
  replaces := []
  ops := everyWrite
  kinds := ["enroll", "install", "create", "grant", "write", "invoke"]
  drive := .members (welcome ++ boardWith "newcomer" ++ [
    { actor := "sponsor", act := .cmd ["receipt", "--health"], expect := .ok, bind := some "h1",
      prints := some "ticks " },
    ok "operator" ["sync"],
    { actor := "operator", act := .verifyHealth "sponsor" "h1", expect := .ok, prints := some "ticks " },
    { actor := "operator", act := .verifyHealth "sponsor" "h1", expect := .refused "pathMismatch",
      fault := .forgeReceipt },
    { actor := "operator", act := .verifyHealth "newcomer" "h1", expect := .refused "otherMember" },
    ok "sponsor" ["write", "@shared", "2", "5"],
    ok "operator" ["sync"],
    { actor := "operator", act := .verifyHealth "sponsor" "h1", expect := .refused "headMismatch" },
    { actor := "sponsor", act := .cmd ["receipt", "--health"], expect := .ok, bind := some "h2" },
    ok "operator" ["sync"],
    { actor := "operator", act := .verifyHealth "sponsor" "h2", expect := .ok, prints := some "ticks " }])
  plant := .caught .trustReceipt 14 .ok

/-- OPS-P1's carry (KERNEL-29, HOST-28 at 6b89d6f): state crosses to a NEW World by export and
import, never by history. A committed call; an import with a wrong digest is refused
`carryMismatch` and the old writer still serves; the import with the file's digest makes the
carried World the writer. There the last committed call is still answered `ok` by lookup (the
journal is carried, PROTOCOL-30); a NEW call signed for the old origin is `wrongWorld` (`declined`, PROTOCOL-41); a member
re-invited to the new origin through a sponsor-signed carried start writes on the carried cells, and a founder acting for the first time
after the carry does so under the id the lineage's first genesis minted. -/
def carry : Row where
  name := "carry"
  replaces := ["ops/OPS-P1"]
  ops := settled
  kinds := ["enroll", "install", "create", "grant", "write"]
  drive := .members (welcome ++ [
    { actor := "newcomer", act := .cmd ["write", "@shared", "2", "1", "--via", "@g"], expect := .ok,
      fault := .dropReply },
    { actor := "operator", act := .carry false, expect := .refused "carryMismatch" },
    ok "newcomer" ["write", "@shared", "2", "2", "--via", "@g"],
    { actor := "operator", act := .carry true, expect := .ok },
    { actor := "newcomer", act := .retry, expect := .ok },
    { actor := "sponsor", act := .forge ["write", "@shared", "3", "1"], expect := .declined "wrongWorld" },
    { actor := "newcomer", act := .acceptCarry false, expect := .ok },
    ok "newcomer" ["write", "@shared", "2", "3", "--via", "@g"],
    ok "newcomer" ["read", "@shared", "2=3"],
    -- a founder's FIRST act after the carry: its id is the lineage's (minted at the first
    -- genesis), never recomputed from the carried origin (KERNEL-40, opacity)
    { actor := "operator", act := .acceptCarry false, expect := .ok },
    ok "operator" ["create", "@permit"]])
  plant := .caught .importTrustsFile 7 .ok

/-- A valid sponsor signature naming another origin cannot authorize this export. -/
def carriedInviteWrongWorld : Row where
  name := "carriedInviteWrongWorld"
  replaces := []
  ops := everyWrite
  kinds := ["enroll", "install", "create", "grant"]
  drive := .members (welcome ++ [
    { actor := "operator", act := .carry true, expect := .ok },
    { actor := "newcomer", act := .acceptCarry true, expect := .refused "carryMismatch wrongWorld" },
    { actor := "newcomer", act := .acceptCarry false, expect := .ok }])
  plant := .caught .importTrustsFile 7 .ok

/-- cv 01a151bc-6ef3 (HOST-61's `beforeLog`): a member re-invited to the carried World whose follow
Store is from before the import's first step (`rejoinBehind`: the lineage's first genesis, height 0)
asks the writer for a page from step 0; the carried Store's log begins at the carried height, so the
writer refuses `beforeLog` by name. Follow REPORTS it, with the remedy (`hint beforeLog`: an
invitation that pins that base, nd adopt) and never acts on it: adopting a base on the writer's word
is what an invitation's pin exists to refuse. The plant is a follow that acts (takes the writer's
first step as its base and reads again): line 9 is `ok`. -/
def beforeLogRow : Row where
  name := "beforeLog"
  replaces := []
  ops := everyWrite
  kinds := ["enroll", "install", "create", "grant", "write"]
  drive := .members (welcome ++ [
    ok "newcomer" ["write", "@shared", "2", "1", "--via", "@g"],
    { actor := "operator", act := .carry true, expect := .ok },
    { actor := "newcomer", act := .rejoinBehind, expect := .ok },
    { actor := "newcomer", act := .cmd ["read", "@shared", "2=1"], expect := .refused "beforeLog",
      prints := some "hint beforeLog: the writer's log starts at a base; join it with an invitation that pins that base (nd adopt)" }])
  plant := .caught .actOnBeforeLog 9 .ok

/-- JPAY (the payment half): a transfer spends a once-only key of its source (`--once`), and the
same key again is `spent`, whether the client checks it (follow's own admission, line 3) or a
hostile client skips that check and the WRITER refuses it (line 4). Another key pays again. -/
def pay : Row where
  name := "pay"
  replaces := ["jpay/JPAY1", "jpay/JPAY2", "jpay/JPAY3", "jpay/JPAY4", "jpay/JPAY6"]
  ops := everyWrite
  kinds := ["issue", "account", "transfer"]
  drive := .members [
    okBind "sponsor" ["issue", "100"] "w",
    ok "sponsor" ["account", "@w", "--owner", "@operator"],
    ok "sponsor" ["transfer", "well:{@w}", "of:{@operator}:{@w}", "10", "--once", "6b31"],
    no "sponsor" ["transfer", "well:{@w}", "of:{@operator}:{@w}", "10", "--once", "6b31"] "spent",
    { actor := "sponsor", act := .forge ["transfer", "well:{@w}", "of:{@operator}:{@w}", "10", "--once", "6b31"],
      expect := .refused "spent" },
    ok "sponsor" ["transfer", "well:{@w}", "of:{@operator}:{@w}", "10", "--once", "6b32"]]
  plant := .caught .writerForgetsSpent 4 .ok

/-- K-WELL on the ledger receivers (LEDGER-6 (f), LEDGER-7): the issuer bears a denomination
(`issue`, its well), opens accounts by owner (`account … --owner`; one per owner, `idTaken` after),
mints out of the well within the cap and is refused past it (`belowFloor`), extends a credit line
(`credit`); an owner moves its own balance, a non-owner is refused `noGrant`, and a transfer into
the well burns. -/
def well : Row where
  name := "well"
  replaces := ["journey/KW", "seats(well)"]
  ops := everyWrite
  kinds := ["issue", "account", "transfer", "credit"]
  drive := .members [
    okBind "sponsor" ["issue", "100"] "w",
    ok "sponsor" ["account", "@w", "--owner", "@operator"],
    no "operator" ["account", "@w"] "idTaken",
    ok "sponsor" ["account", "@w"],
    ok "sponsor" ["transfer", "well:{@w}", "of:{@operator}:{@w}", "10"],
    no "sponsor" ["transfer", "well:{@w}", "of:{@operator}:{@w}", "1000"] "belowFloor",
    ok "sponsor" ["credit", "@w", "of:{@sponsor}:{@w}", "5"],
    ok "operator" ["transfer", "of:{@operator}:{@w}", "of:{@sponsor}:{@w}", "3"],
    no "sponsor" ["transfer", "of:{@operator}:{@w}", "of:{@sponsor}:{@w}", "1"] "noGrant",
    ok "operator" ["transfer", "of:{@operator}:{@w}", "well:{@w}", "2"]]
  plant := .caught .accountByAsset 3 (.refused "idTaken")

/-- The bounty on LEDGER's escrow (`world/escrow/Escrow`, LEDGER-10 at 7c6c7e1): the poster (the
arbiter) births an escrow over 30 of the sponsor's denomination for the hunter; the escrow's own
account and the hunter's are opened top-level first (the pinned view forbids a birth in the
deposit's tree); the poster grants the depositor `invoke:0`; the depositor lends its account to
the object (a `transfer:30` grant over `of:SPONSOR:W`: exactly the deposit, KERNEL-60). A deposit through a grant that is not
that lend is refused `grantTarget`; the real deposit moves 30 into the escrow; the arbiter's
release pays the hunter; a second release is `lawDenied` (the escrow is settled). Plant: without
the law, the kernel still refuses the second payout by its own name (an empty escrow account),
so the plant changes the refusal, it does not admit it. -/
def bounty : Row where
  name := "bounty"
  replaces := ["bounty", "seats", "activity", "objective", "call", "send"]
  ops := everyWrite
  kinds := ["enroll", "grant", "issue", "account", "transfer", "install", "create", "invoke"]
  drive := .members (join "sponsor" "poster" ++ join "sponsor" "hunter" ++ [
    okBind "sponsor" ["issue", "1000"] "w",
    ok "sponsor" ["account", "@w"],
    ok "sponsor" ["transfer", "well:{@w}", "of:{@sponsor}:{@w}", "100"],
    okBind "poster" ["install", "<world/escrow/Escrow"] "escrow",
    okBind "poster" ["create", "--pkg", "@escrow",
      "(record (amount 30) (arbiter #{@poster}) (asset #{@w}) (beneficiary #{@hunter}) (depositor #{@sponsor}) (nonce \"bounty-1\") (phase open))"]
      "bounty",
    ok "poster" ["account", "@w", "--owner", "@bounty"],
    ok "poster" ["account", "@w", "--owner", "@hunter"],
    okBind "poster" ["grant", "@bounty", "@sponsor", "invoke:0"] "gd",
    okBind "sponsor" ["grant", "of:{@sponsor}:{@w}", "@bounty", "transfer:30"] "gm",
    no "sponsor" ["invoke", "@bounty", "0", "(record (grant #{@gd}))", "--via", "@gd"] "grantTarget",
    ok "sponsor" ["invoke", "@bounty", "0", "(record (grant #{@gm}))", "--via", "@gd"],
    ok "poster" ["invoke", "@bounty", "2", "(record)"],
    no "poster" ["invoke", "@bounty", "2", "(record)"] "lawDenied"])
  plant := .caught .skipJudge 18 (.refused "belowFloor")

/-- m6grain (HOSTING-5, 6095c5b): a grain is an object programmed by the SHIPPED lifecycle package
(`world/grain/Lifecycle`, `Hosting.Text.package` of `Hosting.lifecycle?`, G0 byte for byte), born
`installed` (state entry, kind, phase; its owner is the cell's, KERNEL's: the package names none
since 6577e82). Methods remove 0, start 1, stop 2, each taking the empty record. The owner starts it; a second start has no edge (the package's own phase law); a
member who is not the owner cannot stop it (invoke is owner-gated, KERNEL-25: `noGrant`); the owner's grant of `invoke:1` (start)
does not let the grantee stop it (`grantRight`). Its physical half is the standing cargo row
`cargo:launcher:grain` (launcher/tests/grain.rs, `the_owner_stops_a_grain_and_a_start_only_grantee_cannot`,
HOSTING-22, c2019b9). Under a real Store and the controller's Lean plan, the owner's start runs one
process, the grantee's stop is refused `grantRight` and the process lives, and the owner's stop ends
it (plants: a controller or a launcher that ignores stop is red at that step). The resident's half,
reaching its broker socket and nothing else, is `cargo:launcher:resident` (113537f). -/
def grain : Row where
  name := "grain"
  replaces := ["m6grain", "journey/M6"]
  ops := everyWrite
  kinds := ["enroll", "grant", "install", "create", "invoke"]
  drive := .members (join "sponsor" "newcomer" ++ [
    okBind "operator" ["install", "<world/grain/Lifecycle"] "lifecycle",
    okBind "sponsor" ["create", "--pkg", "@lifecycle",
      "(record (entry \"app\") (kind app) (phase installed))"] "app",
    ok "sponsor" ["invoke", "@app", "1", "(record)"],
    no "sponsor" ["invoke", "@app", "1", "(record)"] "lawDenied",
    no "newcomer" ["invoke", "@app", "2", "(record)"] "noGrant",
    okBind "sponsor" ["grant", "@app", "@newcomer", "invoke:1"] "gs",
    no "newcomer" ["invoke", "@app", "2", "(record)", "--via", "@gs"] "grantRight",
    ok "sponsor" ["invoke", "@app", "2", "(record)"]])
  plant := .caught .skipJudge 6 .ok

/-- hermes: a hosted agent is a member with its own seed; the reply to its install is lost (killed
after the send); the attempt settles by lookup, once, and is never signed afresh (a second install
of the same package would be `idTaken`: content-addressed). Then it writes and reads through its
grant. -/
def hermes : Row where
  name := "hermes"
  replaces := ["hermes", "journey/M5", "journey/J14"]
  ops := settled
  kinds := ["enroll", "install", "create", "grant", "write"]
  drive := .members (welcome ++ join "sponsor" "hermes" ++ [
    okBind "sponsor" ["grant", "@shared", "@hermes", "observe,mutate"] "gh",
    { actor := "hermes", act := .cmd ["install", hermesLaw], expect := .ok, fault := .dropReply },
    { actor := "hermes", act := .retry, expect := .ok },
    ok "hermes" ["write", "@shared", "2", "5", "--via", "@gh"],
    ok "hermes" ["read", "@shared", "2=5"]])
  plant := .caught .resendFresh 10 (.refused "idTaken")

/-- THE BAR's workload, in process: N births by one member; one law installed and N invokes of it
on one programmed object (`add 1`; after them `add 999999` passes the law's bound, so the invokes
really added: refused `lawDenied`); a cold reopen; the state read back. The 5 s and 60 s are
LIVENESS deadlines (a miss is `hang`, a non-verdict), not THE BAR's speed spec, which PERF judges at
the end on a quiet box (`scripts/bar.sh`). The deterministic measures are the `WASTE invoke
ticks-per-call` and `packages-checked-per-call` lines, pinned in gates/waste.tsv; the `BAR` lines
are printed for the record and judged by nothing. (64 per landing; `rows --times 1000 bar` for the nightly number.) -/
def barWithCount (count : Nat) : Row where
  name := "bar"
  replaces := ["births", "perf", "growth", "journey/G"]
  ops := everyWrite
  kinds := ["install", "create", "invoke", "write"]
  drive := .members [
    { actor := "sponsor", act := .cmd ["create"], expect := .ok, bind := some "obj", times := count,
      withinMs := some 5000 },
    okBind "sponsor" ["install", counter] "counter",
    okBind "sponsor" ["create", "--pkg", "@counter", "(record (total 0))"] "tally",
    { actor := "sponsor", act := .cmd ["invoke", "@tally", "0", "1"], expect := .ok, times := count - 20,
      withinMs := some 5000 },
    -- The last 20 invokes leave the measured tail under the 8192-byte seal floor (23 did at 7912
    -- bytes until KERNEL-68 made a Turn record 40 bytes larger, 8832, and the seal fired on the
    -- tip: a reopen with nothing past its base, a ratio over nothing). Keep the total workload;
    -- do not let the wire size choose this boundary.
    { actor := "operator", act := .seal, expect := .ok },
    { actor := "sponsor", act := .cmd ["invoke", "@tally", "0", "1"], expect := .ok, times := min count 20,
      withinMs := some 5000 },
    no "sponsor" ["invoke", "@tally", "0", "999999"] "lawDenied",
    { actor := "operator", act := .restart, expect := .ok, withinMs := some 60000 },
    { actor := "sponsor", act := .cmd ["write", "@obj", "1", "x"], expect := .ok, withinMs := some 5000 },
    ok "sponsor" ["read", "@obj", "1=x"]]
  plant := .caught .zeroDeadline 0 .hang


/-- The standing workload. The runner applies --times to the total before splitting the tail. -/
def bar : Row := barWithCount 64

/-! ## Lean-internal rows

A row whose driver is an executable of this tree: the real receivers and `World.admit` in one process
under the Sim's toy parameters, with no socket. It reaches kinds and refusals but no operation, so
`ops` is empty; the executable runs its own plant and goes red by name if the plant stays green.
The `*-sim` executables are NOT rows: standing's sim stage is their one judge (ROOT, PROTOCOL-10). -/

/-- LANG's first law end to end (L1–L7): install → create → invoke; laws refuse by name. -/
def langJourney : Row where
  name := "lang-journey"
  replaces := ["journey/J7(law)", "objectivebend/install-invoke"]
  ops := []
  kinds := ["install", "create", "invoke", "grant"]
  drive := .exe "lang-journey" [] "lang-journey: GREEN"
  plant := .internal "a program whose judge admits everything: L4 set 101 must be admitted"

/-- PROTOCOL-46: a settlement is the member's word, never the Host's. The attempt store drives a
frozen call by the Host's status and ends it only on its own follow's `receipt CALL`
(`Settle.ofReceipt`). A committed call whose lookup the Host answers `refused stale` settles
committed. A call that never reached the writer ends `open`, not "absent, safe to run again": a
relay holding the bytes lands them. A second such call, signed for a window of 2, is re-run past
its window and settles `refused expired`, final. A rotation whose `ok` is lost confirms through
the ARMED rotation's incoming key (`signIncoming`: the writer refuses the old key `unknownKey`),
and custody advances on that confirmation, so the next write signs with the new key. The plant is
a store that takes the Host's final refusal as final: line 6, the lying lookup's own line, ends on
the Host's `refused stale`, and step 4 checks that claim on follow's World, which never caught the
call up: `hostContradicted refused open`. -/
def settleRow : Row where
  name := "settle"
  replaces := []
  ops := settled
  kinds := ["enroll", "install", "create", "grant", "rotate", "write"]
  drive := .members (welcome ++ [
    { actor := "newcomer", act := .cmd ["write", "@shared", "2", "1", "--via", "@g"], expect := .ok,
      fault := .lieLookup },
    ok "operator" ["read", "@shared", "2=1"],
    { actor := "sponsor", act := .cmd ["write", "@shared", "3", "1"], expect := .open,
      fault := .neverForward },
    { actor := "sponsor", act := .resubmit, expect := .ok },
    ok "operator" ["read", "@shared", "3=1"],
    { actor := "sponsor", act := .window 2, expect := .ok },
    { actor := "sponsor", act := .cmd ["write", "@shared", "3", "2"], expect := .open,
      fault := .neverForward },
    okBind "operator" ["create", "@permit"] "own",
    { actor := "operator", act := .cmd ["write", "@own", "2", "1"], expect := .ok, times := 3 },
    { actor := "sponsor", act := .rerun, expect := .refused "expired" },
    ok "operator" ["read", "@shared", "3=1"],
    { actor := "newcomer", act := .cmd ["rotate"], expect := .ok, fault := .dropReply },
    ok "newcomer" ["write", "@shared", "2", "6", "--via", "@g"],
    ok "operator" ["read", "@shared", "2=6"]])
  -- the store's `refused` on the Host's word is checked by follow's own World at step 4 (R7): with no
  -- confirm, follow has not caught up the committed call, so line 6 says `hostContradicted refused
  -- open`, never `refused stale`; the honest lines before it trust no refusal and keep their outcomes
  plant := .caught .trustLookup 6 (.contradicted "refused open")

/-- A tally of rings by round whose `take` reads a round's rings as ONE signed range (item 4): `ring`
inserts its text at key `(round, ringer)` and leaves the state alone (it writes no cell: two rings
touch disjoint rows, so a ring moves only the range); `take` reads the range over the key's first
field (the round, up to 8 rows) and refuses `empty` on an empty one. -/
def tallySource : String := "
(package
  (state (rec))
  (rel rings (key (round nat) (ringer digest)) (val (rec (text bytes))) (limit 64))
  (method ring (arg (rec (round nat) (text bytes))) (edits 1)
    (done state (insert rings (record (round arg.round) (ringer req.agent)) (record (text arg.text)))))
  (method take (reads (rings (range 1 8)))
    (case rows.rings.range.rows.r0 (none _ (refuse \"empty\")) (some _ (done state))))
  (law always (else ok)))
"

/-- `tallySource` as `install` reads it. -/
def tally : String :=
  match Lang.Surface.readPackage tallySource with
  | .ok p => (Lang.Print.package p).getD ""
  | .error _ => ""

/-- Item 4 (ROOT ruled): a method that reads a relation by range is invoked through nd with
`--range REL K [PREFIX]`, `read OBJ REL K [PREFIX]`'s arguments, and the plan signs that range at
follow's listing (`Command.signedReads`, the read verb's `rangeListing`). The sponsor and the newcomer
ring round 1; without `--range` the sponsor's take is refused `rangeUnpinned` (LANG's structured
refusal, with the hint naming the flag); the newcomer rings round 1 (so the sponsor's follow is one
ring behind); with `--range` the take commits, its range signed at the two-ring listing the
sponsor's follow caught up to. -/
def rangeInvokeLines : List Line :=
  join "sponsor" "newcomer" ++ [
    okBind "operator" ["install", tally] "tallyPkg",
    okBind "sponsor" ["create", "--pkg", "@tallyPkg", "(record)"] "t",
    okBind "sponsor" ["grant", "@t", "anyone", "invoke:0"] "tpub",
    { actor := "sponsor", act := .cmd ["read", "@t", "?"], expect := .ok, bind := some "t" },
    ok "sponsor" ["invoke", "@t", "@t.ring", "(record (round 1) (text \"a\"))"],
    { actor := "sponsor", act := .cmd ["invoke", "@t", "@t.take", "(record)"],
      expect := .refused "rangeUnpinned", prints := some "hint rangeUnpinned: this method reads a relation by range; pass --range REL K [PREFIX]" },
    ok "newcomer" ["invoke", "@t", "@t.ring", "(record (round 1) (text \"b\"))", "--via", "@tpub"],
    ok "sponsor" ["invoke", "@t", "@t.take", "(record)", "--range", "rings", "8", "(record (round 1))"]]

/-- Item 4's plant (i): a relay hides the log from the take, so the sponsor's follow, by its own machine
and admission, signs the range at its stale listing (one ring, before the newcomer's ring); the
writer declines it `stale`, by name, at the last line (KERNEL-54: a stale is declined, never
recorded; only the range moved, as `ring` writes no cell). Follow's admission admits it there (the
stale World is self-consistent): the writer's check is the tooth. -/
def rangeInvokeRow : Row where
  name := "rangeInvoke"
  replaces := []
  ops := everyWrite
  kinds := ["enroll", "grant", "install", "create", "invoke"]
  drive := .members rangeInvokeLines
  plant := .caught .staleRange 10 (.declined "stale")

/-- Item 4's plant (ii): the client that drops `--range` signs no range, and the last line is
refused `rangeUnpinned` by name. -/
def rangeFlagRow : Row where
  name := "rangeFlag"
  replaces := []
  ops := everyWrite
  kinds := ["enroll", "grant", "install", "create", "invoke"]
  drive := .members rangeInvokeLines
  plant := .caught .dropRange 10 (.refused "rangeUnpinned")

/-- The queue every range row starts from: a newcomer, the operator's `rings` package, the sponsor's
queue `q` and its public `ring` grant `pub`. -/
def queue : List Line :=
  join "sponsor" "newcomer" ++ [
    okBind "operator" ["install", ringsQueue] "rings",
    okBind "sponsor" ["create", "--pkg", "@rings", "(record (next 0))"] "q",
    okBind "sponsor" ["grant", "@q", "anyone", "invoke:0"] "pub"]

/-- PROTOCOL-51 (cv 01a14f18-b8c8, the Bell as a queue's unblocker): a resident reads a relation's
rows in key order from the text alone. The newcomer reads the queue's description, which names the
relation, its key's fields in declared order and its limit (`rel …`, LANG's printer), and binds
`ring` from it; three rings land (round 2 first, then two in round 1); `read @q rings 8` prints
exactly the three rows, ONE line each, in key-BYTE order (round 1's two before round 2's, not ring
order), each `Lang.Print.data` text of the row at the relation's row type
(`Proofs.Command.rangeLines_reads`); with the prefix `(record (round 1))` exactly round 1's two;
`rings 2` over three rows is `rangeTooLong` (refused, never truncated: the method path's name), and a
relation the package does not declare is `unknownRelation`. The plant is a reader that drops a row:
line 10 is `refused unprinted`. -/
def rangeRow : Row where
  name := "range"
  replaces := []
  ops := everyWrite
  kinds := ["enroll", "grant", "install", "create", "invoke"]
  drive := .members (queue ++ [
    { actor := "newcomer", act := .cmd ["read", "@q", "?"], expect := .ok, bind := some "q",
      prints := some "rel (rings (key (round nat) (n nat)) (val (rec (text bytes))) (limit 64)" },
    ok "sponsor" ["invoke", "@q", "@q.ring", "(record (round 2) (text \"b\"))"],
    ok "newcomer" ["invoke", "@q", "@q.ring", "(record (round 1) (text \"a\"))", "--via", "@pub"],
    ok "newcomer" ["invoke", "@q", "@q.ring", "(record (round 1) (text \"c\"))", "--via", "@pub"],
    { actor := "newcomer", act := .cmd ["read", "@q", "rings", "8"], expect := .ok, exact := true,
      prints := some ("(record (key (record (n 1) (round 1))) (val (record (text \"a\"))))\n" ++
        "(record (key (record (n 2) (round 1))) (val (record (text \"c\"))))\n" ++
        "(record (key (record (n 0) (round 2))) (val (record (text \"b\"))))\n") },
    { actor := "newcomer", act := .cmd ["read", "@q", "rings", "8", "(record (round 1))"], expect := .ok,
      exact := true,
      prints := some ("(record (key (record (n 1) (round 1))) (val (record (text \"a\"))))\n" ++
        "(record (key (record (n 2) (round 1))) (val (record (text \"c\"))))\n") },
    no "newcomer" ["read", "@q", "rings", "2"] "rangeTooLong",
    no "newcomer" ["read", "@q", "bells", "8"] "unknownRelation"])
  plant := .caught .dropRow 10 (.refused "unprinted")

/-- PROTOCOL-51: K past the relation's declared `limit` (64, printed in the description) is refused
`rangePastLimit` by name before any row is read (`Proofs.Command.rangeLines_pastLimit`); K at the
limit over the empty relation prints nothing. The plant is a reader that never checks K: line 6 is
`ok`. -/
def rangeLimitRow : Row where
  name := "rangeLimit"
  replaces := []
  ops := everyWrite
  kinds := ["enroll", "grant", "install", "create"]
  drive := .members (queue ++ [
    no "newcomer" ["read", "@q", "rings", "65"] "rangePastLimit",
    { actor := "newcomer", act := .cmd ["read", "@q", "rings", "64"], expect := .ok, exact := true,
      prints := some "" }])
  plant := .caught .noReadLimit 6 .ok

/-- The Bell's lines (`bellRow`, `bellDocRow`). The newcomer's description of the Bell carries the
Bell's own `doc` line (LANG-60, cv 01a151bc-6f0b). -/
def bellLines : List Line :=
  welcome ++ [
    okBind "sponsor" ["install", "<world/resident/Bell"] "bellPkg",
    okBind "sponsor" ["create", "--pkg", "@bellPkg", "(record (open true) (resident #{@newcomer}))"] "bell",
    okBind "sponsor" ["grant", "@bell", "@newcomer", "invoke:0"] "ga",
    { actor := "newcomer", act := .cmd ["read", "@bell", "?"], expect := .ok, bind := some "bell",
      prints := some "doc \"A ring is answered once by the resident, its text sent back;" },
    { actor := "sponsor", act := .cmd ["invoke", "@bell", "@bell.answer",
        "(record (notBefore 1) (ringText \"hi\") (ringer #{@sponsor}) (text \"me\") (to none))"],
      expect := .refused "program", prints := some "refused notResident" },
    { actor := "newcomer", act := .cmd ["invoke", "@bell", "@bell.answer",
        "(record (notBefore 1) (ringText \"hi\") (ringer #{@sponsor}) (text \"nobody rang\") (to none))", "--via", "@ga"],
      expect := .refused "lawDenied", prints := some "rung: unrung" },
    ok "sponsor" ["invoke", "@bell", "@bell.ring", "(record (text \"hello\") (to none))"],
    { actor := "newcomer", act := .cmd ["read", "@bell", "pending", "64"], expect := .ok,
      prints := some "hello" }]

/-- cv 01a15039: a member reads WHY a method refused it, in the method's own words (LANG-51's
`refuse`). The sponsor installs the shipped Bell (`world/resident/Bell`, LANG-58's queue of rings,
LANG-59's answers in `rings`) with the newcomer as its resident and grants it `answer`. The sponsor, not
the resident, answers: `refused program`, and its output says `refused notResident` (line 10). The
resident answering a ring nobody rang is refused by the Bell's guard `rung` (`lawDenied`, hint
`rung: unrung`: the guard sees the pinned slot empty). The sponsor rings, and the resident reads the ring in `pending`. The
plant is the flattened output (the reason dropped): line 10 is `refused unprinted`. -/
def bellRow : Row where
  name := "bell"
  replaces := []
  ops := everyWrite
  kinds := ["enroll", "grant", "install", "create", "invoke"]
  drive := .members bellLines
  plant := .caught .flatProgram 10 (.refused "unprinted")

/-- cv 01a151bc-6f0b: the Bell's description pins its doc line (`read @bell ?` prints
`doc "A ring is answered once…"`). The plant is a describe that drops the doc line: line 9 is
`refused unprinted`. -/
def bellDocRow : Row where
  name := "bellDoc"
  replaces := []
  ops := everyWrite
  kinds := ["enroll", "grant", "install", "create", "invoke"]
  drive := .members bellLines
  plant := .caught .dropDoc 9 (.refused "unprinted")

/-- The writer serves every event the kernel admits (PROTOCOL-18): the largest a row logs is the
install of the shipped queue Bell (27.7 KB printed). Its submit commits and its confirm, the
sponsor's own follow reading the log through the writer's pages, settles it. The plant is the
budget guessed at 16384: the event never fits a page, the confirm's receipt is refused
`badResult` (an empty page short of the tip) and the attempt ends `uncertain` (line 6). -/
def bigEventRow : Row where
  name := "bigEvent"
  replaces := []
  ops := everyWrite
  kinds := ["enroll", "grant", "install", "create"]
  drive := .members (welcome ++ [
    okBind "sponsor" ["install", "<world/resident/Bell"] "bellPkg",
    okBind "sponsor" ["create", "--pkg", "@bellPkg", "(record (open true) (resident #{@newcomer}))"] "bell"])
  plant := .caught .guessedBudget 6 .uncertain

/-- A resident whose `nd --stdio` socket is bound to ANOTHER member's follower (CLIENT-8's
nd-members finding, ecb02bf): the envelope names the other member and is signed by the resident's
key, so the writer refuses it `unknownKey`; follow asks custody once for the incoming key, and the
stdio custody refuses that `noRotation`. The command ends by the WRITER's word, `refused unknownKey`
(ROOT's rule (a), PROTOCOL-56): custody's refusal only says why the retry could not happen. The
plant ends a refused `signIncoming` by custody's name, as the machine before the rule did for
`noRotation`: line 6 is `refused noRotation`. -/
def wrongFollowerRow : Row where
  name := "wrongFollower"
  replaces := []
  ops := everyWrite
  kinds := ["enroll", "install", "create", "grant"]
  drive := .members (welcome ++ [
    { actor := "newcomer", act := .cmd ["read", "@shared"], expect := .refused "unknownKey",
      fault := .wrongFollower "sponsor" },
    ok "newcomer" ["read", "@shared"]])
  plant := .caught .maskIncoming 6 (.refused "noRotation")

/-- An attempt that ends `uncertain` because the member's own follow refused the confirm says which
refusal (cv 01a150b1, PROTOCOL-55's finding): the writer pages with the old 16384-byte budget (the
row's fault), so the queue Bell's install never fits a page, its confirm's `receipt CALL` is
refused `badResult`, and line 6 ends `uncertain` printing `hint confirm: refused badResult`. The
plant is the attempt store that drops the receipt's stderr (nd's `Vec::new()` before cv 01a150b1):
line 6 is `refused unprinted`. -/
def uncertainHintRow : Row where
  name := "uncertainHint"
  replaces := []
  ops := everyWrite
  kinds := ["enroll", "grant", "install", "create"]
  pageBudget := some 16384
  drive := .members (welcome ++ [
    { actor := "sponsor", act := .cmd ["install", "<world/resident/Bell"], expect := .uncertain,
      prints := some "hint confirm: refused badResult" }])
  plant := .caught .dropHint 6 (.refused "unprinted")

/-- KERNEL-60's cancel over the wire (PROTOCOL-63; HOST-18's `cancel` op, cv 01a15543-39fd): a member
closes its own LOOSE call (sent, outcome unknown, window live) without waiting out the window. The
sponsor's write never reaches the writer (`open`); the newcomer's cancel of it is refused
`badSignature` (a cancel verifies under the CALL's member's key); the sponsor's own cancel is
recorded and prints `cancelled TXID`; the attempt's next run settles `refused cancelled` by the
member's own fold; the same bytes sent again are answered from the record; a second cancel is
`refusedFinal`. A call whose window has passed (the newcomer signs for one height, the sponsor's
write moves the World past it) is refused `outsideWindow`. The plant is custody signing the cancel
without its domain: line 8 is `refused badSignature`. -/
def cancelRow : Row where
  name := "cancel"
  replaces := []
  ops := settled ++ [.cancel]
  kinds := ["enroll", "install", "create", "grant", "write"]
  drive := .members (welcome ++ [
    { actor := "sponsor", act := .cmd ["write", "@shared", "3", "1"], expect := .open,
      fault := .neverForward },
    { actor := "newcomer", act := .cancelOf "sponsor", expect := .refused "badSignature" },
    { actor := "sponsor", act := .cancelOf "sponsor", expect := .ok, prints := some "cancelled " },
    { actor := "sponsor", act := .rerun, expect := .refused "cancelled" },
    { actor := "sponsor", act := .resubmit, expect := .refused "cancelled" },
    { actor := "sponsor", act := .cancelOf "sponsor", expect := .refused "refusedFinal" },
    { actor := "newcomer", act := .window 1, expect := .ok },
    { actor := "newcomer", act := .cmd ["write", "@shared", "2", "1", "--via", "@g"], expect := .open,
      fault := .neverForward },
    ok "sponsor" ["write", "@shared", "4", "1"],
    { actor := "newcomer", act := .cancelOf "newcomer", expect := .refused "outsideWindow" },
    ok "operator" ["read", "@shared", "4=1"]])
  plant := .caught .cancelUndomained 8 (.refused "badSignature")

/-- A moved pin and a refusing receiver at once (PROTOCOL-73, FIX-KERNEL's finding after KERNEL-66): the
newcomer writes through its grant `g` while the sponsor revokes `g`. The Host compares the call's pins
first, so the moved grant pin makes it `declined stale`, though the write's receiver would also refuse
it now (no grant). The next run's settlement is follow's own fold: `staleBehind` asks what the Host
asks, in its order (`signedBy`, then `checkPins`), so it settles `refused stale`, final. Before
PROTOCOL-73 follow asked `receive` first, read the refusing receiver as "not stale" and left the
settlement `open`, so the attempt sent the call again and the Host declined it again: line 7 `declined
stale`, never settled (MEASURED, both parameter sets). -/
def staleRefusingRow : Row where
  name := "staleRefusing"
  replaces := []
  ops := settled
  kinds := ["enroll", "install", "create", "grant", "write", "revoke"]
  drive := .members (welcome ++ [
    { actor := "newcomer", act := .cmd ["write", "@shared", "2", "1", "--via", "@g"],
      expect := .declined "stale", fault := .race "sponsor" ["revoke", "@g"] },
    { actor := "newcomer", act := .rerun, expect := .refused "stale" }])
  plant := .measured "receive-first staleBehind: line 7 declined stale, the settlement open"

/-- A Host that says it recorded a cancel it never saw (PROTOCOL-71, readers A7): the sponsor's write
never reaches the writer (`open`); its cancel is answered `refused cancelled` by a relay that kept the
cancel from the writer. Follow catches up again, finds the call still open on its own World and ends
`hostContradicted cancelled open`, the attempt left open; the honest cancel after it is recorded and
prints `cancelled TXID`, and the attempt's next run settles it `refused cancelled`. The plant is
follow's old phase 10, `cancelled` on the writer's word: line 7 ends `ok`. -/
def cancelLieRow : Row where
  name := "cancelLie"
  replaces := []
  ops := settled ++ [.cancel]
  kinds := ["enroll", "install", "create", "grant", "write"]
  drive := .members (welcome ++ [
    { actor := "sponsor", act := .cmd ["write", "@shared", "3", "1"], expect := .open,
      fault := .neverForward },
    { actor := "sponsor", act := .cancelOf "sponsor", expect := .contradicted "cancelled open",
      fault := .lieCancel },
    { actor := "sponsor", act := .cancelOf "sponsor", expect := .ok, prints := some "cancelled " },
    { actor := "sponsor", act := .rerun, expect := .refused "cancelled" }])
  plant := .caught .trustCancel 7 .ok

/-- A cancel the member never signed, served by the writer (PROTOCOL-63): the sponsor's loose call
is cancelled; a follower reading the log from genesis through a Host that flipped the cancel's
signature refuses the log `cancelForged`, the re-deriver's name for it (`Receive.rederive`), and the
honest log reads `ok`. The plant is a follower that accepts any signature: line 8 absorbs the forged
cancel and is caught only at the page's end, where the writer's chain commits the signature it
logged: `refused chainMismatch`, not `cancelForged`. -/
def cancelForgedRow : Row where
  name := "cancelForged"
  replaces := []
  ops := settled ++ [.cancel]
  kinds := ["enroll", "install", "create", "grant", "write"]
  drive := .members (welcome ++ [
    { actor := "sponsor", act := .cmd ["write", "@shared", "3", "1"], expect := .open,
      fault := .neverForward },
    { actor := "sponsor", act := .cancelOf "sponsor", expect := .ok },
    { actor := "operator", act := .cmd ["sync"], expect := .refused "cancelForged", fault := .forgeCancel },
    ok "operator" ["read", "@shared"]])
  plant := .caught .followVerifyAll 8 (.refused "chainMismatch")

/-- A law package of `fillerPadBytes` refusal text (`fullPage`'s filler): at the deployed parameters
its install's call is 4,075 bytes (measured, PROTOCOL-70), so its log event is 4,076 and 64 of them,
the most one page holds (`recordTurnsMax`), are exactly the old budget, `frameBytesMax - 1024` =
64 × (4 + 4,076). `i < 100` names it (`f00`…`f63`), each a different package. -/
def fillerPadBytes : Nat := 3381
def filler (i : Nat) : String :=
  lawPackage (if i < 10 then s!"f0{i}" else s!"f{i}")
    s!"(inj {verdictTy} refused \"{String.ofList (List.replicate fillerPadBytes 'x')}\")"

/-- A follower a full page behind takes the page and its command's continuation back in ONE frame
(PROTOCOL-70, readers A3). The sponsor installs the queue Bell (a 36,550-byte call at the deployed
parameters) and the newcomer writes (a 540-byte call); then the operator installs 64 fillers, so each
of them is a full page behind. `receipt CALL` of each one's last call, the attempt store's confirm
after time away, pages that log back and settles `committed`. The resume that carries the page also
carries the continuation, and the continuation holds the argv, the call in hex: 73,316 bytes for the
install, 1,296 for the write. The plant is the writer paging at `frameBytesMax - 1024`: a full page
leaves 890 bytes for the continuation, the client's transport refuses the frame (`pastBound`), and
line 72, the install's receipt, is refused under both parameter sets. At the deployed parameters
line 73, the ordinary write's, is refused too (64 × 4,080 bytes is that budget exactly). -/
def fullPageRow : Row where
  name := "fullPage"
  replaces := []
  ops := everyWrite
  kinds := ["enroll", "install", "create", "grant", "write"]
  drive := .members (welcome ++ [
    okBind "sponsor" ["install", "<world/resident/Bell"] "bellPkg",
    ok "newcomer" ["write", "@shared", "2", "1", "--via", "@g"]] ++
    (List.range 64).map (fun i => ok "operator" ["install", filler i]) ++ [
    { actor := "sponsor", act := .receiptOf "sponsor", expect := .ok, prints := some "settle committed" },
    { actor := "newcomer", act := .receiptOf "newcomer", expect := .ok, prints := some "settle committed" }])
  plant := .caught .perFieldBudget 72 (.refused "pastBound")
/-- HOST-75: the one re-deriver catches a forged refusal record. The slot is taken, so the
auditor's forged post is refused `relationFull` and RECORDED; the sponsor's next write catches up
through that refusal event and reads ok. The plant is a writer that records the refusal under
another code while answering the honest name (`forgesRefusal`; line 14 reads the same either way):
a page carries only `1 ‖ call`, the sponsor's follow re-derives the honest record by its own
`judge`, and the page's stated chain, which the writer computed over its forged record, refuses the
page at line 15, `chainMismatch`. -/
def forgedRefusalRow : Row where
  name := "forgedRefusal"
  replaces := []
  ops := everyWrite
  kinds := ["enroll", "install", "create", "grant", "invoke"]
  drive := .members (welcome ++ join "sponsor" "auditor" ++ [
    okBind "sponsor" ["install", slot] "slotPkg",
    okBind "sponsor" ["create", "--pkg", "@slotPkg", "(record)"] "slot",
    okBind "sponsor" ["grant", "@slot", "anyone", "invoke:1"] "spub",
    ok "sponsor" ["invoke", "@slot", "1", "(record (k 1) (text \"first\"))"],
    { actor := "auditor", act := .cmd ["read", "@slot", "?"], expect := .ok, bind := some "slot" },
    -- the slot is taken: the kernel refuses the post `relationFull`, and the writer records it
    { actor := "auditor", act := .forge ["invoke", "@slot", "@slot.post",
        "(record (k 2) (text \"second\"))", "--via", "@spub"], expect := .refused "relationFull" },
    -- the sponsor's follow absorbs the refusal event on its way to the tip
    ok "sponsor" ["invoke", "@slot", "0", "(record (k 1))"]])
  plant := .caught .forgesRefusal 15 (.refused "chainMismatch")

/-- PROTOCOL-74 (DESIGN-TRUST T1: members compare heads). The sponsor attests its head at the tip
(`sync --attest`, bound to `att`); the operator, cold (its follow from genesis), catches up THROUGH
that position under `sync --check @att` and finds the sponsor's chain on its own fold: `shared`. A
position stated with another chain (`sync --to 2:00`: step 2 with a chain no fold has) is refused
`forkedWorld` by name on the way, the page refused. The operator, past the sponsor's head, is refused
`ahead` (its World holds only the current chain). A byte that is no attestation is `badAttestation`.
After the sponsor rotates, its earlier attestation names a key that is no longer its current one:
`staleKey`, on the World the checker caught up to. The plant is a client that drops `--to`'s anchor
(`ignoreAnchor`): line 10, the forged position, ends `ok`. -/
def forkRow : Row where
  name := "fork"
  replaces := []
  ops := everyWrite
  kinds := ["enroll", "install", "create", "grant", "write", "rotate"]
  drive := .members (welcome ++ [
    ok "newcomer" ["write", "@shared", "2", "1", "--via", "@g"],
    okBind "sponsor" ["sync", "--attest"] "att",
    { actor := "operator", act := .cmd ["sync", "--check", "@att"], expect := .ok, fault := .cold,
      prints := some "shared" },
    no "operator" ["sync", "--check", "@att"] "ahead",
    { actor := "operator", act := .cmd ["sync", "--to", "2:00"], expect := .refused "forkedWorld",
      fault := .cold },
    no "operator" ["sync", "--check", "00"] "badAttestation",
    ok "sponsor" ["rotate"],
    { actor := "operator", act := .cmd ["sync", "--check", "@att"], expect := .refused "staleKey",
      fault := .cold }])
  plant := .caught .ignoreAnchor 10 .ok

/-- A self-head object's seed: an `at` head at step 0 of THIS World, stating what the World held
there: the genesis chain and roots (`chain0`, `roots0`, bound by the harness from the genesis World;
a seed is a claim at its step, HOST-79, cv 01a17a38-366e), and `world` its origin. -/
def selfHeadSeed : String :=
  "(record (head (at (record (chain #{@chain0}) (height 0) (roots #{@roots0}) (steps 0)))) (world #{@world}))"

/-- PROTOCOL-75 (DESIGN-TRUST T2: self-heads through the writer). The sponsor installs `Std.head`
(`world/head/Head`), creates its own head object of THIS World and posts its head at the tip
(`sync --post @hs`: `invoke @hs post` with follow's own chain, height, roots and step count). The
operator, cold, catches up through the post and finds its position on its own fold (nothing to
refuse). The sponsor then creates a second head object and FORGES a post naming step 2 with a chain
no fold has (a hostile client; its own follow posts only its own head, `Proofs.Head.body_post`); the
writer admits it (the head law judges the head's monotony only). The operator, cold again, reaches
step 2 with another chain on the same page and is refused `forkedPost` by name; the page is kept
and its next `sync` proceeds. The plant is measured (no cheap mutation reaches follow's walk: the
harness's plants are a client's or the writer's): with `Head.forkedSelfPost` answering `none`, line
12 ends `ok`. -/
def selfHeadRow : Row where
  name := "selfHead"
  replaces := []
  ops := everyWrite
  kinds := ["enroll", "install", "create", "grant", "invoke"]
  drive := .members (welcome ++ [
    okBind "sponsor" ["install", "<world/head/Head"] "head",
    okBind "sponsor" ["create", "--pkg", "@head", selfHeadSeed] "hs",
    ok "sponsor" ["sync", "--post", "@hs"],
    { actor := "operator", act := .cmd ["sync"], expect := .ok, fault := .cold },
    okBind "sponsor" ["create", "--pkg", "@head", selfHeadSeed] "h2",
    { actor := "sponsor", act := .forge ["invoke", "@h2", "1",
        "(record (chain #{@sponsor}) (height 1) (roots #{@sponsor}) (steps 2))"], expect := .ok },
    { actor := "operator", act := .cmd ["sync"], expect := .refused "forkedPost", fault := .cold },
    ok "operator" ["sync"]])
  plant := .measured "Head.forkedSelfPost := none: line 12 ends ok (MEASURED on hbox, PROTOCOL-75)"

/-- PROTOCOL-77.1 (DESIGN-TRUST T3b, the consumers): the rows' World names the writer's certify key as
its one certifier (threshold 1, `Writer.authority`), so a thin member adopts a base only when the
writer's certificate of that base's head verifies under the genesis authority and certifies exactly
the World the pinned bytes decode to (`Head.certifiesWorld`). The operator seals and pins its own
World; the thin member adopts it, certified, and reads past it. The plant forges the certification
(`forgeCertificate`: one signature byte flipped by the writer): line 14, the adopt, is refused
`badCertifySignature` by name and nothing is adopted. -/
def certifiedRow : Row where
  name := "certified"
  replaces := []
  ops := everyWrite ++ [.read]
  kinds := ["enroll", "install", "create", "grant", "write"]
  drive := .members (welcome ++ join "sponsor" "thin" ++ [
    okBind "sponsor" ["grant", "@shared", "@thin", "observe,mutate"] "gt",
    ok "newcomer" ["write", "@shared", "2", "1", "--via", "@g"],
    ok "operator" ["read", "@shared", "2=1"],
    { actor := "operator", act := .seal, expect := .ok },
    okBind "operator" ["invite", "@inputs"] "pin",
    ok "thin" ["adopt", "@pin", "@operator.key"],
    ok "thin" ["read", "@shared", "2=1"]])
  plant := .caught .forgeCertificate 14 (.refused "badCertifySignature")

def rows : List Row :=
  [journey, reopen, laws, rotate, audit, paging, coldCatchUp, forgotten, refusedRow, refusedFinalRow, inviteRow, useRow, describeRow, stateRow, receiptRow, healthRow, settleRow, carry, carriedInviteWrongWorld, thin, thinStale, sealRow, basePin, pageIoRow, wrongWorld, wrongWorldRead, pay, well, bounty, grain, hermes, bar,
   langJourney, rangeRow, rangeLimitRow, bellRow, bigEventRow, wrongFollowerRow,
   uncertainHintRow, rangeInvokeRow, rangeFlagRow, beforeLogRow, bellDocRow, cancelRow, cancelForgedRow,
   fullPageRow, cancelLieRow, staleRefusingRow,
   forgedRefusalRow, forkRow, selfHeadRow, certifiedRow]

end Nanodregg.Protocol
