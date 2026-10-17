/-
# Protocol.Rows — the conformance rows, as data

The spec of the end system is these rows (CHARTER). A row is a fresh deployment, a list of member
commands (argv of `nd`, the one command language), and for each command the outcome it must get,
by name. A row names the operations its commands drive and the receiver kinds they reach, so the
reach table IS this file: `Protocol.Proofs.Rows.every_op_has_a_row` refuses an operation no row
exercises, and the size ratchet counts what is here.

Each row also names its PLANT: a mutation of the system that must turn the row red, and the step
that must catch it. A row whose plant stays green is blind and does not count.

Refusal names are the constructor names of `Kernel.Reject` (the World's checks) and of the
receivers' refusal type (`Kernel.Receive`, proposals/protocol.md §2). They are strings here until
those types are committed; a gate then resolves every name against its constructor.

Rows come from minidregg's landing rows (`scripts/pipeline/journey-rows`, main 2c27b08b). What a
minidregg row checked that nanodregg does not have (a codec child, a host-image pin, a socket
filter) is gone with the thing; what it checked about the WORLD stays.
-/
import Protocol.Table

namespace Nanodregg.Protocol

/-- What one command must end in. `refused` carries the refusal's constructor name. -/
inductive Expect
  | ok
  | refused (name : String)
  /-- the attempt settles by lookup as absent: the Host never saw it -/
  | absent
  deriving DecidableEq, Repr

/-- One line of a row: who runs it, the argv of `nd`, the outcome it must get. -/
structure Line where
  actor : String
  argv : List String
  expect : Expect
  deriving Repr

/-- How a row is driven. -/
inductive Drive
  /-- a Lean executable of this tree that drives the real receive path in-process (toy
  parameters, the real pipeline); it passes when it exits 0 and its last line is `last` -/
  | exe (name : String) (args : List String) (last : String)
  /-- members' commands, each through the one command language -/
  | members (lines : List Line)
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
  /-- the mutation that must turn the row red -/
  plant : String
  /-- the refusal or verdict by which it goes red -/
  plantRed : String
  deriving Repr

private def ok (actor : String) (argv : List String) : Line := ⟨actor, argv, .ok⟩
private def no (actor : String) (argv : List String) (name : String) : Line :=
  ⟨actor, argv, .refused name⟩

/-- Every command reads through the member's own follow, which catches up from the writer's log
(`log`) before it answers; every write is a `submit` settled by `lookup`. -/
def everyCommand : List Op := [.command, .resume, .log]
def everyWrite : List Op := everyCommand ++ [.submit, .lookup]

/-- J0–J5: a clean start, an independent newcomer, a resource, a grant, a signed read and write,
and a stranger refused for both. -/
def journey : Row where
  name := "journey"
  replaces := ["journey/J0", "journey/J1", "journey/J2", "journey/J3", "journey/J4", "journey/J5",
    "welcomecontinuity"]
  ops := everyWrite ++ [.read]
  kinds := ["enroll", "create", "grant", "write"]
  drive := .members [
    ok "sponsor" ["init"],
    ok "newcomer" ["init"],
    ok "sponsor" ["enroll", "@newcomer"],
    ok "sponsor" ["create", "shared", "--law", "permit-all"],
    ok "sponsor" ["grant", "shared", "@newcomer", "observe,mutate"],
    ok "newcomer" ["read", "shared"],
    ok "newcomer" ["write", "shared", "2", "1"],
    ok "newcomer" ["read", "shared", "--expect", "2=1"],
    no "stranger" ["read", "shared"] "unknownKey",
    no "stranger" ["write", "shared", "2", "9"] "unknownKey",
    no "sponsor" ["write", "shared", "2", "1", "--pin-stale"] "stale"]
  plant := "receiver skips the grant check on write"
  plantRed := "stranger write admitted (expected unknownKey); journey red at its 10th command"

/-- J6: stop and reopen; receipts recovered; an exact retry replays, never re-admits. -/
def reopen : Row where
  name := "reopen"
  replaces := ["journey/J6", "hostupgrade/REOPEN"]
  ops := everyWrite ++ [.read]
  kinds := ["write"]
  drive := .members [
    ok "newcomer" ["write", "shared", "2", "3"],
    ok "operator" ["host", "restart"],
    ok "newcomer" ["read", "shared", "--expect", "2=3"],
    no "newcomer" ["retry", "--last"] "replayed"]
  plant := "reopen drops the journal (decodes the checkpoint without it)"
  plantRed := "retry admitted a second time (expected replayed)"

/-- J7, J8: a law replaced keeps existing grants; deny-all refuses the newcomer and the repair. -/
def laws : Row where
  name := "laws"
  replaces := ["journey/J7", "journey/J8", "journey/J13"]
  ops := everyWrite
  kinds := ["install", "write"]
  drive := .members [
    ok "sponsor" ["law", "shared", "not(any[])"],
    ok "newcomer" ["write", "shared", "2", "7"],
    ok "sponsor" ["law", "shared", "deny-all"],
    no "newcomer" ["write", "shared", "2", "8"] "lawDenied",
    no "sponsor" ["law", "shared", "permit-all"] "lawDenied"]
  plant := "the law is evaluated against the pre-state's law instead of the installed one"
  plantRed := "newcomer write admitted under deny-all (expected lawDenied)"

/-- JROT, JROTL: pre-rotation; a stolen daily key cannot rotate; a lost reply is found by lookup. -/
def rotate : Row where
  name := "rotate"
  replaces := ["journey/JROT", "journey/JROTL"]
  ops := everyWrite
  kinds := ["rotate", "write"]
  drive := .members [
    no "thief" ["rotate", "--as", "@newcomer", "--next", "@thief-next"] "notPrecommitted",
    ok "newcomer" ["rotate"],
    no "newcomer" ["write", "shared", "2", "4", "--key", "old"] "unknownKey",
    ok "newcomer" ["write", "shared", "2", "4"],
    ok "newcomer" ["rotate", "--drop-reply"],
    ok "newcomer" ["retry", "--last", "--expect-committed"],
    ⟨"newcomer", ["rotate", "--never-forward"], .absent⟩]
  plant := "the rotation receiver accepts any key in place of the precommitted digest"
  plantRed := "thief rotation admitted (expected notPrecommitted)"

/-- JAUDIT: a follower re-derives the Store from genesis — every Turn from its event, by the same
receivers — and a flipped byte of a non-head frame in a copy is refused naming its height. -/
def audit : Row where
  name := "audit"
  replaces := ["journey/JAUDIT", "jstoreaudit"]
  ops := everyCommand
  kinds := []
  drive := .members [
    ok "auditor" ["audit", "--from", "genesis"],
    no "auditor" ["audit", "--from", "genesis", "--copy-flip", "1"] "frameMac"]
  plant := "follow folds Turns without re-running the receiver on each Turn's event"
  plantRed := "a planted Turn whose event does not derive it is accepted (expected eventMismatch)"

/-- JPAY1–4, JPAY6: observed payments become credit; the pay cell's book, tariff and refusals; a
burn funds an agent purse in one joint turn. Pay is an installed package invoked by members and
by the watcher (a member with its own seed), not a receiver family. -/
def pay : Row where
  name := "pay"
  replaces := ["jpay/JPAY1", "jpay/JPAY2", "jpay/JPAY3", "jpay/JPAY4", "jpay/JPAY6"]
  ops := everyWrite
  kinds := ["install", "invoke"]
  drive := .members [
    ok "operator" ["install", "world/pay/Book.obend"],
    ok "watcher" ["invoke", "book", "observe", "--fixture", "transfer-finalized"],
    no "watcher" ["invoke", "book", "observe", "--fixture", "transfer-failed"] "lawDenied",
    no "watcher" ["invoke", "book", "observe", "--fixture", "transfer-finalized"] "spent",
    ok "newcomer" ["invoke", "book", "pay", "lab", "week"],
    no "newcomer" ["invoke", "book", "pay", "lab", "--amount", "1"] "lawDenied",
    ok "newcomer" ["invoke", "book", "burn-to-purse", "hermes", "100"]]
  plant := "the observation nullifier is omitted from the derived Turn"
  plantRed := "a replayed observation credits twice (expected spent)"

/-- K-WELL: the referee mints by grant and law; no-grant, law-refused and overburn are refused;
supply is conserved. -/
def well : Row where
  name := "well"
  replaces := ["journey/KW", "seats(well)"]
  ops := everyWrite
  kinds := ["install", "invoke"]
  drive := .members [
    ok "operator" ["install", "world/well/Well.obend"],
    ok "referee" ["invoke", "well", "mint", "@newcomer", "10"],
    no "newcomer" ["invoke", "well", "mint", "@newcomer", "10"] "noGrant",
    no "referee" ["invoke", "well", "mint", "@newcomer", "1000000"] "lawDenied",
    no "newcomer" ["invoke", "well", "burn", "11"] "lawDenied",
    ok "newcomer" ["invoke", "well", "burn", "10"],
    ok "auditor" ["read", "well", "--expect", "supply=0"]]
  plant := "burn decrements the holder without decrementing supply"
  plantRed := "supply=0 read fails after burn (conservation)"

/-- The bounty on the seat kernel: escrow, claim, submit, approve/reject/silence/cancel, the first
claimer; the kernel refuses a double pay, reward+1 and a raid. -/
def bounty : Row where
  name := "bounty"
  replaces := ["bounty", "seats", "activity", "objective", "call", "send"]
  ops := everyWrite
  kinds := ["install", "invoke"]
  drive := .members [
    ok "poster" ["install", "world/bounty/BountyEscrow.obend"],
    ok "poster" ["invoke", "bounty", "post", "--reward", "50"],
    ok "hunter" ["invoke", "bounty", "claim"],
    no "rival" ["invoke", "bounty", "claim"] "lawDenied",
    ok "hunter" ["invoke", "bounty", "submit", "--answer", "42"],
    ok "poster" ["invoke", "bounty", "approve"],
    no "poster" ["invoke", "bounty", "approve"] "lawDenied",
    no "hunter" ["invoke", "bounty", "withdraw", "--amount", "51"] "lawDenied"]
  plant := "approve does not mark the bounty paid"
  plantRed := "second approve admitted (double pay)"

/-- m6grain: an SPK app installed and started by the user-mode broker under the one sandbox shape,
reachable over http; a second world's volume path is refused. The lifecycle decision is a
package's law; the broker verbs are physical. -/
def grain : Row where
  name := "grain"
  replaces := ["m6grain", "journey/M6"]
  ops := everyWrite ++ [.read]
  kinds := ["install", "invoke"]
  drive := .members [
    ok "operator" ["install", "world/grain/Lifecycle.obend"],
    ok "owner" ["invoke", "grain", "begin", "--spk", "test.spk"],
    ok "owner" ["grain", "start"],
    ok "owner" ["grain", "get", "/"],
    no "owner" ["grain", "mount", "--world", "b"] "crossWorldVolume",
    ok "owner" ["invoke", "grain", "stop"]]
  plant := "the broker accepts a volume path outside its world's root"
  plantRed := "cross-world mount succeeds (expected crossWorldVolume)"

/-- hermes: a hosted agent is a member with its own seed in the one sandbox shape; it performs J4,
is killed mid-attempt, restarts, and the attempt settles by lookup. -/
def hermes : Row where
  name := "hermes"
  replaces := ["hermes", "journey/M5", "journey/J14"]
  ops := everyWrite ++ [.read]
  kinds := ["write"]
  drive := .members [
    ok "sponsor" ["grant", "shared", "@hermes", "observe,mutate"],
    ok "hermes" ["write", "shared", "2", "5", "--kill-after-send"],
    ok "hermes" ["retry", "--last", "--expect-committed"],
    ok "hermes" ["read", "shared", "--expect", "2=5"]]
  plant := "the client resends a fresh signature after an uncertain reply instead of looking up"
  plantRed := "two attempts for one intent (attempt store refuses a second call)"

/-- THE BAR: N births then a cold reopen; each write p99 ≤ 5 s, cold reopen ≤ 60 s (64 per
landing, 1000 nightly). -/
def bar : Row where
  name := "bar"
  replaces := ["births", "perf", "growth", "journey/G"]
  ops := everyWrite ++ [.read]
  kinds := ["create", "write"]
  drive := .members [
    ok "sponsor" ["create", "obj-$i", "--repeat", "N"],
    ok "operator" ["host", "restart", "--cold"],
    ok "sponsor" ["read", "obj-0", "--within-ms", "60000"]]
  plant := "reopen folds the whole log instead of checkpoint + suffix"
  plantRed := "cold reopen past 60 s at N=1000"

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
  plant := "a program whose judge admits everything (skip-judge)"
  plantRed := "L4 set 101 admitted under the planted judge, so the refusal came from the law"

def rows : List Row :=
  [journey, reopen, laws, rotate, audit, pay, well, bounty, grain, hermes, bar,
   langJourney]

end Nanodregg.Protocol
