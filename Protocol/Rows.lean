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

namespace Nanodregg.Protocol

/-- What one line must end in. `refused` carries the refusal's name (its owner's `name`). -/
inductive Expect
  | ok
  | refused (name : String)
  /-- the attempt settles by lookup as absent: the Host never saw it -/
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
  deriving DecidableEq, Repr

def Expect.text : Expect → String
  | .ok => "ok" | .refused n => s!"refused {n}" | .absent => "absent" | .uncertain => "uncertain"
  | .unsettled n => s!"uncertain {n}" | .hang => "hang"

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
  /-- the actor, a full follower, states the pin of its own World out of band (the channel is
  Ember's, unbuilt): binds `NAME` to the digest of its World bytes and `NAME.h` to its height -/
  | attest (name : String)
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
  | rejoin
  /-- the actor signs a `log` read envelope for ITS World (from height 0, one window from 0) and
  sends it to a second writer made as `replayLog` makes one (PROTOCOL-29's cross-World read); the
  outcome is that writer's answer -/
  | readElsewhere (sameNonce : Bool)
  /-- the actor's client signs every later envelope for `n` heights (its own `Self.window`, a
  client's setting; the writer's read gate bounds it by `Bounds.windowMax`) -/
  | window (n : Nat)
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
  /-- this command's follow starts from genesis, and every `expired` a log page is refused with
  states `extra` more than the writer's height (a man in the middle on the member's path, PROTOCOL-27) -/
  | inflateExpired (extra : Nat)
  /-- the actor signs as member `victim` with the victim's CURRENT key (stolen), its own custody
  holding every other key -/
  | stolenKey (victim : String)
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
  /-- the writer refuses an expired envelope by the name alone, stating no height (PROTOCOL-12's
  shape, before PROTOCOL-19) -/
  | unstatedExpiry
  /-- the writer's read gate skips the envelope's lower bound: a `notYet` envelope is served (the
  shape before PROTOCOL-27, when an envelope was good at every height up to `validUntil`) -/
  | ignoreNotBefore
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
  deriving DecidableEq, Repr

/-- A row's plant: the mutation, and the line that must catch it with the outcome it then gets. -/
inductive Plant
  /-- under `mutation`, the lines before `line` keep their outcomes and line `line` gets `got` -/
  | caught (mutation : Mutation) (line : Nat) (got : Expect)
  /-- an `exe` row's executable runs its own plant -/
  | internal (what : String)
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
  s!"(package (imports) (state (rec)) (iface (rec ({l} (-> (rec) (-> (rec) (-> {reqTy} {verdictTy}))))))
    (methods) (laws {l})
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
  s!"(package (imports) (state {S})
    (iface (rec (add (-> {S} (-> nat (-> {reqTy} {res}))))
                (bounded (-> {S} (-> {S} (-> {reqTy} {verdictTy}))))))
    (methods add) (laws bounded)
    (body (record
      (add (fn (s {S}) (n nat) (r {reqTy})
        (record (calls {Lang.Print.noCallsText}) (state (record (total (+ (. s total) n)))))))
      (bounded (fn (old {S}) (new {S}) (r {reqTy})
        (if (<= (. new total) 1000000)
            (inj {verdictTy} ok (record))
            (inj {verdictTy} refused \"over a million\")))))))"

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
    { actor := "sponsor", act := .cmd ["write", "@shared", "2", "9"], expect := .refused "stale",
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
the writer leaves custody on the old key, which still signs (custody advances on settlement). -/
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
    { actor := "newcomer", act := .cmd ["rotate"], expect := .absent, fault := .neverForward },
    ok "newcomer" ["write", "@shared", "2", "5", "--via", "@g"],
    ok "newcomer" ["read", "@shared", "2=5"]])
  plant := .caught .advanceOnSend 12 (.refused "unknownKey")

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
no row. The rows' writer pages with a 16384-byte budget (`Writer.pageBudget`), so a hundred writes
are several pages. -/
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
PROTOCOL-19); every rows actor's window is 100, so 210 writes put the tip two windows past genesis. -/
def coldCatchUp : Row where
  name := "coldCatchUp"
  replaces := []
  ops := everyWrite
  kinds := ["enroll", "install", "create", "grant", "write"]
  drive := .members (welcome ++ join "sponsor" "auditor" ++ [
    { actor := "newcomer", act := .cmd ["write", "@shared", "2", "1", "--via", "@g"], expect := .ok,
      times := 210 },
    { actor := "auditor", act := .cmd ["read", "@shared", "2=1"], expect := .ok, fault := .cold }])
  plant := .caught .unstatedExpiry 10 (.refused "expired")

/-- PROTOCOL-27: a man in the middle on a cold follower's path inflates the height `expired`
states. Follow re-signs for the window starting at that height, and the writer refuses it `notYet`:
the inflation buys a window in the future, never a longer one (`Envelope.check_ok_within`). Under the
old gate (no lower bound) the inflated envelope reads. -/
def inflatedHeight : Row where
  name := "inflatedHeight"
  replaces := []
  ops := everyWrite
  kinds := ["enroll", "install", "create", "grant", "write"]
  drive := .members (welcome ++ join "sponsor" "auditor" ++ [
    { actor := "newcomer", act := .cmd ["write", "@shared", "2", "1", "--via", "@g"], expect := .ok,
      times := 110 },
    { actor := "auditor", act := .cmd ["read", "@shared", "2=1"], expect := .refused "notYet",
      fault := .inflateExpired 1000000 }])
  plant := .caught .ignoreNotBefore 10 .ok

/-- THIN (PROTOCOL-14, option A; minidregg's `journey.d/jthin-consent.sh`, which drove the
deleted thin consent frames 230–232): a member that never folded the log adopts the writer's
newest base, pinned by a full follower's word, then is an ordinary follower from the base on: it
re-derives the suffix and signs a write planned on it. The full follower (`operator`) catches up,
the writer seals at its tip, and the operator states the pin of its own World (`attest`, out of
band). A newer seal moves the base off the pin: a member (`late`) holding the old pin is refused
`baseMoved`. -/
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
    { actor := "operator", act := .attest "pin", expect := .ok },
    ok "thin" ["adopt", "@pin.h", "@pin"],
    ok "newcomer" ["write", "@shared", "2", "2", "--via", "@g"],
    ok "thin" ["write", "@shared", "3", "7", "--via", "@gt"],
    ok "thin" ["read", "@shared", "2=2", "3=7"],
    { actor := "operator", act := .seal, expect := .ok },
    no "late" ["adopt", "@pin.h", "@pin"] "baseMoved"])
  plant := .caught .forgeBase 17 (.refused "baseMismatch")

/-- A thin member whose pin is more than a window old (PROTOCOL-37; PROTOCOL-4's leftover, adopt's
`reSign` path). The thin member's client signs for a window of 5 heights; the operator seals and
states the pin, then the log runs 12 writes past it, fewer than the rows' seal cadence needs, so the
newest base is still the pinned one (a deployed writer's seal cadence is in bytes, its window in
heights: a pin a window old with the base unmoved is the ordinary case). `adopt`'s first envelope is signed for the pin's height + window. The
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
    { actor := "operator", act := .attest "pin", expect := .ok },
    { actor := "newcomer", act := .cmd ["write", "@shared", "2", "1", "--via", "@g"], expect := .ok,
      times := 12 },
    ok "thin" ["adopt", "@pin.h", "@pin"],
    ok "thin" ["write", "@shared", "3", "7", "--via", "@gt"],
    ok "thin" ["read", "@shared", "2=1", "3=7"]])
  plant := .caught .unstatedExpiry 15 (.refused "expired")

/-- Cross-World replay (OPS, ASSEMBLY-ops D3; reproduced on 87c721e against the `host` exe): two
`host genesis` runs with the same name and founders made two Worlds that admitted each other's
calls. KERNEL-24 binds every call to its World's origin (`Unsigned.world`, checked first;
`Kernel.Receive.admitted_elsewhere_refused`), and the origin commits to the genesis nonce. So the
writer's whole log replayed into a Store whose genesis differs ONLY in its nonce is refused
`wrongWorld`, every call, by that name. The same log into a Store of the same nonce is a restore of
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
    { actor := "operator", act := .replayLog false, expect := .refused "wrongWorld" },
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
    { actor := "sponsor", act := .cmd ["write", "@shared", "3", "1"], expect := .absent,
      fault := .neverForward },
    okBind "operator" ["create", "@permit"] "own",
    { actor := "operator", act := .cmd ["write", "@own", "2", "1"], expect := .ok, times := 110 },
    { actor := "sponsor", act := .retry, expect := .refused "expired" },
    { actor := "newcomer", act := .retry, expect := .ok },
    { actor := "operator", act := .cmd ["write", "@own", "2", "1"], expect := .ok, times := 3100 },
    { actor := "sponsor", act := .retry, expect := .unsettled "forgotten" },
    { actor := "newcomer", act := .retry, expect := .unsettled "forgotten" }])
  plant := .caught .forgottenRefused 13 (.refused "forgotten")

/-- OPS-P1's carry (KERNEL-29, HOST-28 at 6b89d6f): state crosses to a NEW World by export and
import, never by history. A committed call; an import with a wrong digest is refused
`carryMismatch` and the old writer still serves; the import with the file's digest makes the
carried World the writer. There the last committed call is still answered `ok` by lookup (the
journal is carried, PROTOCOL-30); a NEW call signed for the old origin is `wrongWorld`; a member
re-invited to the new origin writes on the carried cells, and a founder acting for the first time
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
    { actor := "sponsor", act := .forge ["write", "@shared", "3", "1"], expect := .refused "wrongWorld" },
    { actor := "newcomer", act := .rejoin, expect := .ok },
    ok "newcomer" ["write", "@shared", "2", "3", "--via", "@g"],
    ok "newcomer" ["read", "@shared", "2=3"],
    -- a founder's FIRST act after the carry: its id is the lineage's (minted at the first
    -- genesis), never recomputed from the carried origin (KERNEL-40, opacity)
    { actor := "operator", act := .rejoin, expect := .ok },
    ok "operator" ["create", "@permit"]])
  plant := .caught .importTrustsFile 7 .ok

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
the object (a mutate grant over `of:SPONSOR:W`, LEDGER-6). A deposit through a grant that is not
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
      "(record (amount 30) (arbiter #{@poster}) (asset #{@w}) (beneficiary #{@hunter}) (depositor #{@sponsor}) (phase open))"]
      "bounty",
    ok "poster" ["account", "@w", "--owner", "@bounty"],
    ok "poster" ["account", "@w", "--owner", "@hunter"],
    okBind "poster" ["grant", "@bounty", "@sponsor", "invoke:0"] "gd",
    okBind "sponsor" ["grant", "of:{@sponsor}:{@w}", "@bounty", "mutate"] "gm",
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
does not let the grantee stop it (`grantRight`). The sandbox half (the broker launching the grain,
a second world's volume refused) is CLIENT's and HOSTING's, judged by their plants, not by rows. -/
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
def bar : Row where
  name := "bar"
  replaces := ["births", "perf", "growth", "journey/G"]
  ops := everyWrite
  kinds := ["install", "create", "invoke", "write"]
  drive := .members [
    { actor := "sponsor", act := .cmd ["create"], expect := .ok, bind := some "obj", times := 64,
      withinMs := some 5000 },
    okBind "sponsor" ["install", counter] "counter",
    okBind "sponsor" ["create", "--pkg", "@counter", "(record (total 0))"] "tally",
    { actor := "sponsor", act := .cmd ["invoke", "@tally", "0", "1"], expect := .ok, times := 64,
      withinMs := some 5000 },
    no "sponsor" ["invoke", "@tally", "0", "999999"] "lawDenied",
    { actor := "operator", act := .restart, expect := .ok, withinMs := some 60000 },
    { actor := "sponsor", act := .cmd ["write", "@obj", "1", "x"], expect := .ok, withinMs := some 5000 },
    ok "sponsor" ["read", "@obj", "1=x"]]
  plant := .caught .zeroDeadline 0 .hang

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

def rows : List Row :=
  [journey, reopen, laws, rotate, audit, paging, coldCatchUp, inflatedHeight, forgotten, carry, thin, thinStale, wrongWorld, wrongWorldRead, pay, well, bounty, grain, hermes, bar,
   langJourney]

end Nanodregg.Protocol
