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
import Lang.Read

namespace Nanodregg.Protocol

/-- What one line must end in. `refused` carries the refusal's name (its owner's `name`). -/
inductive Expect
  | ok
  | refused (name : String)
  /-- the attempt settles by lookup as absent: the Host never saw it -/
  | absent
  /-- the Host's reply was `uncertain` (a failed append): a real outcome, never a guess -/
  | uncertain
  /-- the line ran past its LIVENESS deadline (`withinMs`): the system did not answer in time. A
  non-verdict by name, never a judgement of speed (Ember: no wall-clock verdict until the end, on a
  quiet box; THE BAR's ≤ 5 s is PERF's final spec, `scripts/bar.sh`, not a row criterion) -/
  | hang
  deriving DecidableEq, Repr

def Expect.text : Expect → String
  | .ok => "ok" | .refused n => s!"refused {n}" | .absent => "absent" | .uncertain => "uncertain"
  | .hang => "hang"

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
  /-- the actor's last frozen call is submitted, byte-identical, to a SECOND writer made by a second
  genesis with the same name and founders (OPS's cross-World replay) -/
  | replayElsewhere
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
def reqTy : String := Lang.Read.showTy Lang.reqTy
def verdictTy : String := Lang.Read.showTy Lang.verdictTy

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
  s!"(package (imports) (state {S})
    (iface (rec (add (-> {S} (-> nat (-> {reqTy} {S}))))
                (bounded (-> {S} (-> {S} (-> {reqTy} {verdictTy}))))))
    (methods add) (laws bounded)
    (body (record
      (add (fn (s {S}) (n nat) (r {reqTy}) (record (total (+ (. s total) n)))))
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
moved before it landed. -/
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
    ok "newcomer" ["read", "@shared", "2=8"]])
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

/-- Cross-World replay (OPS, ASSEMBLY-ops D3; reproduced on 87c721e against the `host` exe): two
`host genesis` runs with the same name and founders make two Worlds that admit each other's calls,
so a call committed in A is admitted in B. The call must be bound to its World's genesis. -/
def wrongWorld : Row where
  name := "wrongWorld"
  replaces := ["ops/replay-20261016"]
  ops := everyWrite
  kinds := ["enroll", "install", "create", "grant", "write"]
  drive := .members (welcome ++ [
    ok "newcomer" ["write", "@shared", "2", "1", "--via", "@g"],
    { actor := "newcomer", act := .replayElsewhere, expect := .refused "wrongWorld" }])
  plant := .caught .skipJudge 7 .ok
  blockedOn := some "KERNEL: a signed World binding in every call (genesis origin or a per-genesis nonce) and its refusal `wrongWorld`; the plant becomes 'B ignores the binding' when it lands"

/-- JPAY1–4, JPAY6: observed payments become credit. Pay is an installed package (LANG's to
write, `world/pay/Book`), invoked by members and by the watcher, not a receiver family. -/
def pay : Row where
  name := "pay"
  replaces := ["jpay/JPAY1", "jpay/JPAY2", "jpay/JPAY3", "jpay/JPAY4", "jpay/JPAY6"]
  ops := everyWrite
  kinds := ["install", "invoke"]
  drive := .members [
    okBind "operator" ["install", "world/pay/Book"] "book",
    ok "watcher" ["invoke", "@book", "0", "transfer-finalized"],
    no "watcher" ["invoke", "@book", "0", "transfer-finalized"] "spent"]
  plant := .caught .skipJudge 2 .ok
  blockedOn := some "LEDGER: no receiver puts a nullifier in a Turn (sealTurn's nullifiers are []), so `spent` is unreachable; LANG: the pay package world/pay/Book"

/-- K-WELL: the referee mints by grant and law; supply is conserved (LANG's `world/well/Well`). -/
def well : Row where
  name := "well"
  replaces := ["journey/KW", "seats(well)"]
  ops := everyWrite
  kinds := ["install", "invoke"]
  drive := .members [
    okBind "operator" ["install", "world/well/Well"] "well",
    ok "referee" ["invoke", "@well", "0", "10"],
    no "referee" ["invoke", "@well", "0", "1000000"] "lawDenied"]
  plant := .caught .skipJudge 2 .ok
  blockedOn := some "LEDGER: the well receivers (mint, burn, supply); LANG: the well package world/well/Well"

/-- The bounty on the seat kernel (LANG's `world/bounty/BountyEscrow`). -/
def bounty : Row where
  name := "bounty"
  replaces := ["bounty", "seats", "activity", "objective", "call", "send"]
  ops := everyWrite
  kinds := ["install", "invoke"]
  drive := .members [
    okBind "poster" ["install", "world/bounty/BountyEscrow"] "bounty",
    ok "hunter" ["invoke", "@bounty", "0", "claim"],
    no "rival" ["invoke", "@bounty", "0", "claim"] "lawDenied"]
  plant := .caught .skipJudge 2 .ok
  blockedOn := some "LEDGER: escrow accounts; LANG: the bounty package world/bounty/BountyEscrow"

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
  [journey, reopen, laws, rotate, audit, paging, coldCatchUp, thin, wrongWorld, pay, well, bounty, grain, hermes, bar,
   langJourney]

end Nanodregg.Protocol
