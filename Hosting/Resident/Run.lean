/-
# Hosting.Resident.Run — `resident`: THE BAR's hosted Hermes (HOSTING-27, HOSTING-31)

    resident <the plan's paths, as grain-launch passes them>

A resident grain's program (`pkg/resident`), confined by grain-launch like any grain. It can see its
package (read), its volume (read and write), its own broker socket and its own member socket, and
nothing else. Its argv must be its plan (`Args.place`), or it ends `argvNotPlan` before reading
anything. It reads `pkg/resident.conf`, ONE Lang data value at `Bell.confTy`. Then, every
`tickMs`, for at most `lifetimeTicks` ticks:
1. Until it has the bell's shape, it describes the bell (`read OBJ ?` → `Shape.read`); a package
   that is not the Bell ends it `bellShape notBell` (HOSTING-45).
2. It reads every pending ring in ONE read (`read OBJ pending K`, K = `pending`'s declared limit →
   `Ring.readAll`), lowest first.
3. It acts on `decideTick`:
   - idle: forget a kept answer whose ring is no longer pending;
   - ask (the lowest pending ring, when no kept ring is pending): first keep the intent
     (`(unanswered restart)`) for the ring, keyed by its `(notBefore, ringer)` and its text, then
     one ask on the broker socket; the answer text replaces the intent in `vol/kept-<bell>` before
     the bell sees it (every keep is synced, renamed, directory-synced and read back);
   - answer (the kept ring, still pending): invoke `answer (notBefore, ringText, ringer, text)`
     with the ring's text and the kept answer. The client pins `pending[k]` and `rings[k]` itself
     (`derivePins`); the resident names no pin.
4. The bell taking the answer forgets it. A refusal is judged by the bell's rows: if the ring is
   no longer pending (answered already: the `rings` guard refuses `rung: answered`), the answer is
   forgotten; if it is still pending, the resident probes each cell the answer cites (an aimed
   ring's `via` grant and target, `read CELL ?`): a cell found gone WITHDRAWS the answer by that
   cell's name and the queue goes on (the `use` hole); with every cited cell there, the resident ends
   `answerRefused NAME` (`program` for a method's check such as `notResident`, `grantRight` for a
   grant without the right). The kept text stays, so a restart answers again but never asks again.
A transport failure on either socket, and every member reply that did not settle (a describe or read
that did not answer `ok`; an answer that came back neither `ok` nor `refused`: `uncertain`, `behind`,
`declined`, `client`, `open`, `hostContradicted`, `pageIo`; a refusal whose re-read failed), is logged
and retried at the next tick: a not-sent ask costs nothing, a spent one is never repeated. Retries
are bounded: `retriesMax` ticks in a row that ended on one, and the resident ends `retryExhausted`
naming the last (HOSTING-48, `Proofs.ResidentRun.no_refusal_repeats_forever`); any tick that
settles starts the count again. Every line on stderr starts `resident: `.

The tick is a tree of effects (`Prog`, HOSTING-36): `tickP` builds it, `Prog.interp` performs it one
node at a time (HOSTING-37: `interp_runs`). The order above is a theorem over every path of that tree, for every reply the
sockets and the volume could give (`Proofs.ResidentRun.tick_order`, `tick_counts`): at most one
describe, first, and only without a shape; one read; at most one ask, right after the intent was
kept for its ring; at most one invoke, of the kept answer (no ask on that path) or of this tick's
answer right after it replaced the intent.

Limits, named: a ring is its key `(notBefore, ringer)` and its text. Keys are unique among the
bell's rows, but a ringer may re-use its own key once the ring is answered AND retired, by
backdating within the kernel's window; if that happens while the old answer is still kept (its
delivery unsettled) and with the same text, the new ring is answered with the kept text, never
asked twice. A ring that lands below the kept one waits for it (`decide_kept_first`): the queue
order the resident keeps is "lowest first, the ring already asked about before any other", and a
ringer's backdate by up to windowMax heights is the order's slack the resident trusts. A late
landing of an unsettled answer cannot take a re-rung ring at the same key with another text: the
answer carries the ring's text and the `rings` guard refuses it unless that is the ring's own
(`rung: text`, LANG-59); with the same text it is the same-text case above.
`answerRefused` stops the whole queue, not one ring: a restart re-delivers the kept ring first and
stops again until the operator acts. That is right for every refusal known to reach it with every
cited cell there (the resident is not the bell's, the grant lacks `invoke:0`, `rings` is full until
the owner retires), each of which refuses every ring alike. A refusal that singles out one ring by a
dead cell of its aim withdraws that ring (`Mem.withdrawn`, by the cell's name) and the queue goes on
(`Proofs.ResidentSlots.use_withdraws`, `serve_repairs`; agent_hole H4 runs it). A ring RETIRED between the read and the
answer (LANG-76: anyone may abandon an unanswered ring past its patience) is not one: its answer is
refused, the re-read no longer lists it, and the answer is forgotten and the queue goes on
(`Proofs.ResidentRun.deliver_gone_continues`; resident_bell Q7 runs it). K = `pending`'s limit is complete:
the kernel holds at most `limit` rows (`relationFull`), and a range read past K is refused, never
truncated, so a missed ring would be a failed read (logged, retried), never a silent gap. A not-sent ask whose intent cannot be
forgotten ends `volume`, and the restart answers that ring `(unanswered restart)` without having
asked: one wasted answer, no meter charge.

Provider access uses the installed leaf-SPKI pins and keybroker's provider key file. The repository
ships provider pins in `deploy/tls/pins`; the operator supplies credentials and maintains the
installed policy. A pin or credential failure is answered by name before a successful provider call.
-/
import Hosting.Resident.Args
import Hosting.Resident.Bell
import Hosting.Resident.Sockets
import Protocol.Command.Exit
import Host.File
import Lang.Contextual.Slot

namespace Nanodregg.Hosting.Resident

/-- How the resident ends, by name. A grain's exit code is the controller's to count, never a
verdict (any exit counts toward `crashLoop`); each code names one case on stderr. -/
inductive Exit
  /-- argv is not this resident's plan joined onto three roots (`Args.place`) -/
  | argvNotPlan
  /-- `pkg/resident.conf` is absent, unreadable, or larger than `confBytesMax` -/
  | confMissing
  /-- the config is not one value of `confTy` with a 32-byte bell id -/
  | confMalformed
  /-- the bell's description or state is not a bell's (`Shape.read`, `Ring.read`) -/
  | bellShape
  /-- the bell refused the answer while the ring still waits (judged by the state, `deliver`) -/
  | answerRefused
  /-- the volume could not keep a decided answer (or what it keeps does not read back) -/
  | volume
  /-- `lifetimeTicks` ran out -/
  | lifetime
  /-- `retriesMax` ticks in a row ended on a retry (the detail names the last) -/
  | retryExhausted
  /-- a member reply's stdout is not UTF-8: refused by name before any parse (law 7: it is never
  read as an empty text, so never as "nothing pending"; HOSTING-49) -/
  | undecodable
  deriving DecidableEq, Repr

namespace Exit

def all : List Exit :=
  [argvNotPlan, confMissing, confMalformed, bellShape, answerRefused, volume, lifetime, retryExhausted,
   undecodable]

def code : Exit → UInt32
  | argvNotPlan => 10 | confMissing => 11 | confMalformed => 12 | bellShape => 13
  | answerRefused => 14 | volume => 15 | lifetime => 16 | retryExhausted => 17
  | undecodable => 18

def name : Exit → String
  | argvNotPlan => "argvNotPlan" | confMissing => "confMissing" | confMalformed => "confMalformed"
  | bellShape => "bellShape" | answerRefused => "answerRefused" | volume => "volume"
  | lifetime => "lifetime" | retryExhausted => "retryExhausted" | undecodable => "undecodable"

end Exit

/-- Between two reads of the bell. -/
def tickMs : Nat := 1000

/-- Ticks in one process: millennia at `tickMs`. -/
def lifetimeTicks : Nat := 1 <<< 48

def say (s : String) : IO Unit := IO.eprintln s!"resident: {s}"

def stop (e : Exit) (detail : String) : IO UInt32 := do
  say s!"{e.name}{if detail.isEmpty then "" else " " ++ detail}"
  pure e.code

/-- An absolute path in argv, as text. -/
def pathOf (b : ByteArray) : Option System.FilePath := (String.fromUTF8? b).map System.FilePath.mk

/-- A refused command's stderr as one line. -/
def refusalLine (r : Reply) : String := ((String.fromUTF8? r.stderr).getD "?").trimAsciiEnd.toString

/-- The refusal's name in a refused command's stderr (`refused NAME …`, `StdioRefusal`). -/
def refusedName (stderr : ByteArray) : String :=
  match (String.fromUTF8? stderr).map (·.splitOn " ") with
  | some ("refused" :: n :: _) => (n.splitOn "\n").headD n
  | _ => "?"

/-- What the resident remembers between ticks. -/
structure Mem where
  shape : Option Shape
  kept : Option (Ring × ByteArray)
  /-- ticks in a row that ended on a retry (`retry`); a tick that settles sets it to 0 -/
  retries : Nat := 0
  /-- the rings whose answer was WITHDRAWN, each with the support its refusal named (the `use`
  slot); a ring leaves the list when it is no longer pending (`serve` prunes it) -/
  withdrawn : List (Ring × String) := []

/-- The memory with the withdrawn rings that are no longer in `pending` dropped: a ring that left the
queue is no longer withdrawn (if it is rung again, it is a new ring). -/
def Mem.prune (m : Mem) (pending : List Ring) : Mem :=
  { m with withdrawn := m.withdrawn.filter fun x => decide (x.1 ∈ pending) }

/-- Ticks in a row that may end on a retry before the resident ends `retryExhausted`: re-delivering
never asks, but nothing may repeat forever (law 4: a static bound on everything). 32 ticks at
`tickMs` is half a minute, during which every tick's read and answer each catch follow up by up to
`pagesPerCommandMax` pages; past it the resident ends by name and its controller's restart budget
(`Controller.restartsMax`) decides what comes next. -/
def retriesMax : Nat := 32

/-- The result of one tick: go on with this memory, or end. -/
inductive Tick
  | next (m : Mem)
  | stop (e : Exit) (detail : String)

/-- The end of a tick that did not settle: go on with one more retry counted, or end
`retryExhausted WHY` once that would be `retriesMax` in a row. -/
def retry (m : Mem) (why : String) : Tick :=
  if m.retries + 1 < retriesMax then .next { m with retries := m.retries + 1 }
  else .stop .retryExhausted why

/-- The files of one resident. -/
structure Where where
  conf : Conf
  member : String
  broker : String
  vol : System.FilePath
  kept : System.FilePath
  /-- the withdrawn rings (`Mem.withdrawn`), kept as the kept answer is -/
  noted : System.FilePath

/-- The kept file's fresh copy: its name with `.tmp` after it, so never the kept name itself
(`Proofs.ResidentVolume.keptTmp_ne`). -/
def Where.keptTmp (w : Where) : System.FilePath := ⟨w.kept.toString ++ ".tmp"⟩

/-- The pending rings an `ok` read reply lists, or how the resident ends: `undecodable` when its
stdout is not UTF-8 (refused before any parse), `bellShape` naming the row a line does not read as.
The tick's read and re-read, and the theorems' `readRings`, are this one function (HOSTING-49). -/
def readOut (sh : Shape) (r : Reply) : Except (Exit × String) (List Ring) :=
  match String.fromUTF8? r.stdout with
  | none => .error (.undecodable, "read")
  | some out => (Ring.readAll sh out).mapError (.bellShape, ·)

/-- The shape an `ok` describe reply reads as, or how the resident ends: `undecodable` when its
stdout is not UTF-8, `bellShape` naming why the description is not the configured Bell's
(`Shape.ofDescription`: `wrongObject`, `notBell`, …; READ-HOSTING B6: the reason is the detail). -/
def describeOut (c : Conf) (r : Reply) : Except (Exit × String) Shape :=
  match String.fromUTF8? r.stdout with
  | none => .error (.undecodable, "describe")
  | some out => (Shape.ofDescription c.bell out).mapError (.bellShape, ·)

/-- The withdrawn file as a kept name: a note IS a keep at `w.noted` (`keepOps w.notedAt`), so every
theorem of `Proofs.ResidentVolume` about `keepOps` and `forgetOps` holds of it at `w.notedAt`. -/
def Where.notedAt (w : Where) : Where := { w with kept := w.noted }

/-- One step on the volume, as `keep` and `forget` take them (HOSTING-37). Each is one POSIX call
(`perform`); `Volume.apply` is the contract each is trusted to meet, and the theorems of
`Proofs.ResidentVolume` are over exactly the lists `keepOps` and `forgetOps` below. -/
inductive FsOp
  /-- unlink the name when it is there -/
  | removeIfExists (p : System.FilePath)
  /-- create the name, which must not exist (`O_CREAT|O_EXCL`), and hold it open -/
  | create (p : System.FilePath)
  /-- write the text to the file held open (fresh and empty: its contents become exactly this) -/
  | write (s : String)
  /-- `fsync` the file held open -/
  | sync
  /-- rename the first name over the second -/
  | rename (a b : System.FilePath)
  /-- `fsync` the directory -/
  | syncDir (d : System.FilePath)

/-- Perform one step; the file held open, after it. -/
def perform (h : Option Host.File) : FsOp → IO (Option Host.File)
  | .removeIfExists p => do
    if ← p.pathExists then IO.FS.removeFile p
    pure h
  | .create p => do pure (some (← Host.File.open p .createNew))
  | .write s => match h with
    | some f => do f.writeAll s.toUTF8; pure h
    | none => throw (IO.userError "no file held open")
  | .sync => match h with
    | some f => do f.sync; pure h
    | none => throw (IO.userError "no file held open")
  | .rename a b => do IO.FS.rename a b; pure h
  | .syncDir d => do Host.syncDir d.toString; pure h

/-- Perform the steps in order. -/
def performAll (ops : List FsOp) : IO Unit := do
  let _ ← ops.foldlM perform none

/-- Keeping the text `s`: a fresh `kept.tmp` written and synced, renamed over the kept file, the
directory synced. -/
def keepOps (w : Where) (s : String) : List FsOp :=
  [.removeIfExists w.keptTmp, .create w.keptTmp, .write s, .sync, .rename w.keptTmp w.kept,
   .syncDir w.vol]

/-- Forgetting: the kept file unlinked, the directory synced. -/
def forgetOps (w : Where) : List FsOp := [.removeIfExists w.kept, .syncDir w.vol]

/-- Forget the kept answer, durably (`forgetOps`). -/
def forget (w : Where) : IO Bool := do
  match ← (performAll (forgetOps w)).toBaseIO with
  | .ok () => pure true
  | .error _ => pure false

/-- Keep `(r, t)` durably before anything depends on it (`keepOps`), then read it back; `false`
unless what reads back is exactly `(r, t)`. `Proofs.ResidentVolume.keep_durable`: under the
volume's contract, once these steps ran a crash leaves exactly this text; `keep_atomic`: a crash at
any step leaves the old kept text or this one, never another. -/
def keep (w : Where) (r : Ring) (t : ByteArray) : IO Bool := do
  let some s := keptText r t | return false
  let act : IO (Option (Ring × ByteArray)) := do
    performAll (keepOps w s)
    pure (keptRead (← IO.FS.readFile w.kept))
  match ← act.toBaseIO with
  | .ok back => pure (decide (back = some (r, t)))
  | .error _ => pure false

/-- Keep the withdrawn rings `l` durably (`keepOps` at `w.notedAt`), then read them back; `false` unless
what reads back is exactly `l`. -/
def note (w : Where) (l : List (Ring × String)) : IO Bool := do
  let some s := notedText l | return false
  let act : IO (Option (List (Ring × String))) := do
    performAll (keepOps w.notedAt s)
    pure (notedRead (← IO.FS.readFile w.noted))
  match ← act.toBaseIO with
  | .ok back => pure (decide (back = some l))
  | .error _ => pure false

/-- What the start does before its first tick (HOSTING-39): what the volume holds at the kept name,
made durable by running a whole keep of it again from its first step (absent: a whole forget), so
a keep or a forget that failed part way in the last life (the rename or the unlink done, the
directory sync not) can no longer be undone by a crash once this life acts on what it read. Over
the volume's contract every crash outcome after these steps reads exactly what the start read
(`Proofs.ResidentVolume.resume_durable`, with no premise on the volume but readability), and every
keep or forget after them is atomic again (`next_keep_after_resume`, `next_forget_after_resume`);
a keep stopped part way, then this, is as one completed keep or none (`keep_resumed`); and the
resume may itself fail or crash at any step without wedging a later start (`resume_atomic`). An
unreadable entry has no steps: the start ends `volume` before it. -/
def resumeOps (w : Where) : Option (Option String) → List FsOp
  | none => forgetOps w
  | some (some s) => keepOps w s
  | some none => []

/-- Run `resumeOps`, then read the kept name back; `false` unless it reads as `held` again. Only
then does it say `resumed` (the line the bell test counts at a restart). -/
def resumeAt (w : Where) (held : Option (Option String)) : IO Bool := do
  let act : IO (Option (Option String)) := do
    performAll (resumeOps w held)
    if ← w.kept.pathExists then pure (some (some (← IO.FS.readFile w.kept))) else pure none
  match ← act.toBaseIO with
  | .ok back => pure (back = held)
  | .error _ => pure false

/-- `resumeAt` the kept name, saying `resumed` when it holds. -/
def resume (w : Where) (held : Option (Option String)) : IO Bool := do
  let ok ← resumeAt w held
  if ok then say s!"resumed {if held.isSome then "the kept answer" else "nothing kept"}"
  pure ok

/-- The first tick's kept answer from what the volume holds at the kept name: absent → none;
unreadable → no seed (`volume`); a text → what it reads as, and no seed when it reads as nothing. -/
def seedOf : Option (Option String) → Option (Option (Ring × ByteArray))
  | none => some none
  | some none => none
  | some (some s) => (keptRead s).map some

/-- The first tick's withdrawn rings from what the volume holds at the withdrawn name: absent → none
withdrawn; unreadable, or a line that does not read → no seed (`volume`). -/
def notedSeed : Option (Option String) → Option (List (Ring × String))
  | none => some []
  | some none => none
  | some (some s) => notedRead s

/-- A member command the tick sends, by what it is for. Its argv is a function of it (`Cmd.argv`):
a node cannot carry one command's name and another's bytes. -/
inductive Cmd
  /-- the bell's description (`read OBJ ?`), until the shape is known -/
  | describe
  /-- the tick's one read of every pending ring, at the shape -/
  | read (sh : Shape)
  /-- `answer` for the ring with the text -/
  | invoke (sh : Shape) (r : Ring) (t : ByteArray)
  /-- `pending` again, after a refused answer, to judge the refusal -/
  | reread (sh : Shape)
  /-- `read CELL ?`, after a refused answer whose ring still waits: is a cell the answer cites still
  there (a retired or never-created cell is refused `missingCell`) -/
  | probe (c : ByteArray)

/-- The argv a command sends (an unprintable answer sends nothing: `deliverP` never builds that
node, and `answerArg_some` says it cannot arise). -/
def Cmd.argv (c : Conf) : Cmd → List ByteArray
  | .describe => describeArgv c
  | .read sh | .reread sh => pendingArgv c sh
  | .probe x => ["read".toUTF8, hexOf x, "?".toUTF8]
  | .invoke sh r t => match answerArg r t with
    | some a => invokeArgv c sh r.to a
    | none => []

/-! ## The tick as an open protocol

The tick is a term of the open calculus (`Lang.Contextual.Protocol.Prot`) at the resident's
signature `sig` (its five effects, each one call on the world outside the process; trivially
indexed) with the hole type `Hole`. A node is ONE effect and its continuation is what the tick does
with that effect's result, or a HOLE: a decision the tick leaves to a SLOT (`Lang.Contextual.Slot`),
filled when the run reaches it from the candidates whose supports hold in what the run has just read
(`fill`). Two holes:
- `serve`, after the read: which ring the tick acts on. Its candidates, in the chooser's order: the
  kept ring's answer, an ask for each pending ring lowest first, and idling. A ring's candidate cites
  two supports: the ring is pending in this read, and its answer was not withdrawn. So the kept ring is
  answered first while it waits, then the lowest waiting ring is asked about (`serveChoice_eq`: this
  is `decideTick` over the rings whose answer stands).
- `use`, after a refused answer, the re-read and, when the ring still waits, a probe of each cell the
  answer cites (`read CELL ?`): what follows. Its candidates: the slot is CLOSED (the ring is no longer
  pending: the answer landed, or the ring was retired); the answer is WITHDRAWN by the name of a cell
  of the ring's aim that the probe found gone (the `via` grant or the target; a retired cell is a
  tombstone, so the failure is permanent); or the queue STOPS (`answerRefused`), when every cell the
  ring cites is there: the refusal is then not this ring's alone, and refuses every ring alike. The
  member's refusal line does not name the cell (`refused missingCell`), so the resident reads the World. A withdrawn ring is skipped by every later `serve` while it is pending, and
  the queue goes on to the next ring: repair without a restart.
`Prog.interp` runs the term by the calculus's interpreter (`Slot.interp`), each hole filled by `fill`.
`Proofs.ResidentRun.Runs` is every path through it, over every result each effect could have; a hole's
path is its filling's. -/

/-- The resident's effects. -/
inductive Eff
  /-- one command on the member socket: `c.argv` -/
  | cmd (c : Cmd)
  /-- keep `(r, t)` durably (`keep`) -/
  | keep (r : Ring) (t : ByteArray)
  /-- forget the kept answer durably (`forget`) -/
  | forget
  /-- keep the withdrawn rings durably (`note`) -/
  | note (l : List (Ring × String))
  /-- one ask on the broker socket -/
  | ask (r : Ring) (q : Broker.Ask)
  /-- one line on stderr -/
  | say (s : String)

/-- Each effect's result. -/
def Eff.Resp : Eff → Type
  | .cmd _ => Except String Reply
  | .keep _ _ => Bool
  | .forget => Bool
  | .note _ => Bool
  | .ask _ _ => AskEnd
  | .say _ => Unit

open Nanodregg.Lang.Contextual.Protocol in
/-- The resident's signature: its effects, trivially indexed. -/
def sig : Sig Unit where
  Op := fun _ => Eff
  Resp := fun op => Eff.Resp op
  next := fun _ _ => ()

/-- The resident's holes, each named by what the run had read when it reached it. -/
inductive Hole
  /-- which ring to act on, among the rings `pending` this tick read -/
  | serve (w : Where) (sh : Shape) (m : Mem) (pending : List Ring)
  /-- what follows the refusal (stderr `line`, name `n`) of the answer for `ring`, the re-read having
  listed `pending` and the probes having found the cells `gone` -/
  | use (sh : Shape) (m : Mem) (ring : Ring) (n line : String) (pending : List Ring) (gone : List ByteArray)

open Nanodregg.Lang.Contextual.Protocol in
/-- A tick's term: an open protocol at `sig` with the resident's holes. -/
abbrev Prog (α : Type) := Prot sig (fun _ => Hole) (fun _ => α) ()

open Nanodregg.Lang.Contextual.Protocol in
@[match_pattern] abbrev Prog.done {α : Type} (a : α) : Prog α := Prot.ret (i := ()) a
open Nanodregg.Lang.Contextual.Protocol in
@[match_pattern] abbrev Prog.cmd {α : Type} (c : Cmd) (k : Except String Reply → Prog α) : Prog α :=
  Prot.call (S := sig) (i := ()) (Eff.cmd c) k
open Nanodregg.Lang.Contextual.Protocol in
@[match_pattern] abbrev Prog.keep {α : Type} (r : Ring) (t : ByteArray) (k : Bool → Prog α) : Prog α :=
  Prot.call (S := sig) (i := ()) (Eff.keep r t) k
open Nanodregg.Lang.Contextual.Protocol in
@[match_pattern] abbrev Prog.forget {α : Type} (k : Bool → Prog α) : Prog α :=
  Prot.call (S := sig) (i := ()) Eff.forget k
open Nanodregg.Lang.Contextual.Protocol in
@[match_pattern] abbrev Prog.note {α : Type} (l : List (Ring × String)) (k : Bool → Prog α) : Prog α :=
  Prot.call (S := sig) (i := ()) (Eff.note l) k
open Nanodregg.Lang.Contextual.Protocol in
@[match_pattern] abbrev Prog.ask {α : Type} (r : Ring) (q : Broker.Ask) (k : AskEnd → Prog α) : Prog α :=
  Prot.call (S := sig) (i := ()) (Eff.ask r q) k
open Nanodregg.Lang.Contextual.Protocol in
/-- A `say` node as a pattern: its continuation takes the effect's `()` result. -/
@[match_pattern] abbrev Prog.sayK {α : Type} (s : String) (k : Unit → Prog α) : Prog α :=
  Prot.call (S := sig) (i := ()) (Eff.say s) k
/-- One line on stderr, then `k`. -/
abbrev Prog.say {α : Type} (s : String) (k : Prog α) : Prog α := Prog.sayK s fun _ => k
open Nanodregg.Lang.Contextual.Protocol in
@[match_pattern] abbrev Prog.hole {α : Type} (h : Hole) : Prog α := Prot.hole (i := ()) h

/-- What performs each kind of effect, in a monad `M`. -/
structure Handler (M : Type → Type) where
  cmd : Cmd → M (Except String Reply)
  keep : Ring → ByteArray → M Bool
  forget : M Bool
  note : List (Ring × String) → M Bool
  ask : Ring → Broker.Ask → M AskEnd
  say : String → M Unit

/-- The handler's one call for an effect. -/
def Handler.call {M : Type → Type} (h : Handler M) : (op : Eff) → M (Eff.Resp op)
  | .cmd c => h.cmd c
  | .keep r t => h.keep r t
  | .forget => h.forget
  | .note l => h.note l
  | .ask r q => h.ask r q
  | .say s => h.say s

/-- The deployed handler: the member socket, the volume, the broker socket, stderr. -/
def ioHandler (w : Where) : Handler IO where
  cmd c := Resident.command w.member (c.argv w.conf)
  keep r t := Resident.keep w r t
  forget := Resident.forget w
  note l := Resident.note w l
  ask _ q := Resident.ask w.broker q
  say s := Resident.say s

/-! ## The two slots -/

open Nanodregg.Lang.Contextual.Slot

/-- What a `serve` candidate cites. -/
inductive ServeFact
  /-- the ring is pending in this tick's read -/
  | pending (r : Ring)
  /-- the ring's answer was not withdrawn -/
  | stands (r : Ring)

/-- The `serve` slot: each act on a ring cites that ring pending and its answer standing; idling cites
nothing; every act passes the judge. -/
def serveSlot : Slot ServeFact Act where
  supports := fun
    | .answer r _ => [.pending r, .stands r]
    | .ask r => [.pending r, .stands r]
    | .idle => []
  judge := fun _ => true

/-- Whether ring `r`'s answer stands: it is not among the withdrawn. -/
def stands (m : Mem) (r : Ring) : Bool := !(m.withdrawn.any fun x => x.1 == r)

/-- What a `serve` support says at this read. -/
def serveHolds (m : Mem) (pending : List Ring) : ServeFact → Bool
  | .pending r => decide (r ∈ pending)
  | .stands r => stands m r

/-- The chooser's order: the kept ring's answer, an ask for each pending ring lowest first, idling. -/
def serveOrder (m : Mem) (pending : List Ring) : List Act :=
  (match m.kept with
   | some (r, t) => [Act.answer r t]
   | none => []) ++ pending.map Act.ask ++ [Act.idle]

/-- The act the `serve` slot fills: its first usable candidate (idling is always usable). -/
def serveChoice (m : Mem) (pending : List Ring) : Act :=
  (serveSlot.alternatives (serveHolds m pending) (serveOrder m pending)).headD .idle

/-- The rings pending in this read whose answer stands. -/
def live (m : Mem) (pending : List Ring) : List Ring := pending.filter (stands m)

/-- The cells a ring's answer cites beyond the ring itself: for an aimed ring, the grant the Bell holds
on the target (`via`) and the target; none for a plain ring. -/
def aimCells (r : Ring) : List ByteArray :=
  match r.to with
  | some a => [a.via, a.target]
  | none => []

/-- What a probe of a cell (`read CELL ?`) says: `some true`, the cell is gone (refused `missingCell`:
retired, a tombstone, or never created); `some false`, it is there (`ok`, or refused for another
reason); `none`, unsettled (a transport failure or another exit: the tick is retried). -/
def probeGone : Except String Reply → Option Bool
  | .error _ => none
  | .ok r =>
    if r.exit = Protocol.CommandExit.ok.code then some false
    else if r.exit = Protocol.CommandExit.refused.code then some (refusedName r.stderr == "missingCell")
    else none

/-- What follows a refused answer. -/
inductive UseCand
  /-- the ring left `pending`: the answer is forgotten -/
  | closed
  /-- the ring waits, and the cell `c` its answer cites is gone: withdrawn by that name -/
  | withdraw (c : ByteArray)
  /-- every cell the ring cites is there: the refusal is not this ring's alone, and the queue stops
  (`answerRefused`) -/
  | stop
  deriving DecidableEq

/-- What a `use` candidate cites. -/
inductive UseFact
  /-- the ring is no longer pending -/
  | left
  /-- the ring is still pending -/
  | waits
  /-- the cell `c` was probed and is gone -/
  | gone (c : ByteArray)

/-- The `use` slot for ring `r`. -/
def useSlot : Slot UseFact UseCand where
  supports := fun
    | .closed => [.left]
    | .withdraw c => [.waits, .gone c]
    | .stop => []
  judge := fun _ => true

/-- What a `use` support says, given the re-read and the cells the probes found gone. -/
def useHolds (r : Ring) (pending : List Ring) (gone : List ByteArray) : UseFact → Bool
  | .left => decide (r ∉ pending)
  | .waits => decide (r ∈ pending)
  | .gone c => gone.any fun g => decide (g = c)

/-- The chooser's order: closed, then a withdrawal by each cell the ring cites, then stop. -/
def useOrder (r : Ring) : List UseCand := [.closed] ++ (aimCells r).map .withdraw ++ [.stop]

/-- What the `use` slot fills: its first usable candidate (stop is always usable). -/
def useChoice (r : Ring) (pending : List Ring) (gone : List ByteArray) : UseCand :=
  (useSlot.alternatives (useHolds r pending gone) (useOrder r)).headD .stop

/-- The intent kept before an ask: a restart that finds it answers the ring with it and never asks
again. -/
def intentText : ByteArray := fit (named "unanswered restart")

/-- Forget the kept answer, then go on with `next` (or end `volume`). -/
def forgetThen (next : Tick) : Prog Tick :=
  .forget fun ok => if ok then .done next else .done (.stop .volume "forget")

/-- After a refused answer whose ring still waits: probe each cell the answer cites (`read CELL ?`),
collecting those found gone, then the `use` hole. A probe that does not settle ends the tick on a
retry, the answer still kept. -/
def probesP (sh : Shape) (m : Mem) (ring : Ring) (n line : String) (pending : List Ring) :
    List ByteArray → List ByteArray → Prog Tick
  | [], gone => .hole (.use sh m ring n line pending gone)
  | c :: cs, gone => .cmd (.probe c) fun y =>
    match probeGone y with
    | some true => probesP sh m ring n line pending cs (c :: gone)
    | some false => probesP sh m ring n line pending cs gone
    | none =>
      .say s!"answer refused ({line}); probe of {Lang.Print.hex c} unsettled" <|
        .done (retry m s!"answer refused {n} ({line}); probe unsettled")

/-- After a refused answer and the re-read `pending`: a ring that still waits has the cells its answer
cites probed first; then the `use` hole. -/
def refusedP (sh : Shape) (m : Mem) (ring : Ring) (n line : String) (pending : List Ring) : Prog Tick :=
  if ring ∈ pending then probesP sh m ring n line pending (aimCells ring) []
  else .hole (.use sh m ring n line pending [])

/-- Invoke `answer` for the kept ring `ring` with `t`; what the tick does next.

A refusal is judged by the bell's ROWS, not by its name: the member surface names a method's check
only as `program`, and a kernel refusal of the retract names the row, not the reason. So after any
refusal the resident reads `pending` again. If the ring is still pending, the bell refused THIS
answer: the resident probes the cells the answer cites (`probesP`) and the `use` hole decides
(withdraw by the name of a gone cell, or stop `answerRefused NAME` with the text still kept).
Otherwise the ring was answered (a delivery that landed but whose reply was lost), or retired, and the
kept answer is forgotten. -/
def deliverP (sh : Shape) (m : Mem) (ring : Ring) (t : ByteArray) : Prog Tick :=
  match answerArg ring t with
  | none => .done (.stop .bellShape "answer unprintable (unreachable: answerArg_some)")
  | some _ =>
  .cmd (.invoke sh ring t) fun
  | .error e => .say s!"answer unsettled {e}" (.done (retry m s!"answer {e}"))
  | .ok r =>
    if r.exit = Protocol.CommandExit.ok.code then
      .say s!"answered {ring.notBefore} {Lang.Print.hex ring.ringer} {t.size} bytes" <|
        forgetThen (.next { m with kept := none, retries := 0 })
    else if r.exit = Protocol.CommandExit.refused.code then
      let n := refusedName r.stderr
      let line := refusalLine r
      let unread (why : String) : Prog Tick :=
        .say s!"answer refused ({line}); state unread {why}" <|
          .done (retry m s!"answer refused {n} ({line}); state unread {why}")
      .cmd (.reread sh) fun
      | .error e => unread e
      | .ok rr =>
        if rr.exit ≠ Protocol.CommandExit.ok.code then unread s!"exit {rr.exit}" else
        match readOut sh rr with
        | .error (x, d) => .done (.stop x d)
        | .ok pending => refusedP sh m ring n line pending
    else .say s!"answer unsettled exit {r.exit}" (.done (retry m s!"answer exit {r.exit}"))

/-- After the ask: say how it went and keep the answer `t` (the intent replaced), then deliver. -/
def answeredP (sh : Shape) (m : Mem) (ring : Ring) (t : ByteArray) : Prog Tick :=
  .say s!"asked; answer {t.size} bytes" <| .keep ring t fun ok =>
    if ok then deliverP sh { m with kept := some (ring, t) } ring t
    else .done (.stop .volume "keep")

/-- What the tick does with the pending rings it read: `decideTick`'s act. -/
def actOn (w : Where) (sh : Shape) (m : Mem) (pending : List Ring) : Prog Tick :=
  match serveChoice m pending with
  | .idle =>
    if m.kept.isSome then forgetThen (.next { m with kept := none, retries := 0 })
    else .done (.next { m with kept := none, retries := 0 })
  | .answer ring t => deliverP sh m ring t
  | .ask ring =>
    -- the intent, before a byte of the ask leaves
    .keep ring intentText fun ok =>
    if !ok then .done (.stop .volume "keep") else
    .ask ring (askOf w.conf ring) fun
    | .notSent why => .say s!"ask not sent {why}" <| forgetThen (retry { m with kept := none } s!"ask {why}")
    | .answered a => answeredP sh m ring (answerText a)
    | .lost why =>
      .say s!"ask spent, answer lost {why}" <| answeredP sh m ring (fit (named s!"unanswered {why}"))

/-- The tick's one read of every pending ring, then its act. -/
def readP (w : Where) (sh : Shape) (m : Mem) : Prog Tick :=
  .cmd (.read sh) fun
  | .error e => .say s!"read {e}" (.done (retry m s!"read {e}"))
  | .ok r =>
    if r.exit ≠ Protocol.CommandExit.ok.code then
      .say s!"read exit {r.exit} {String.fromUTF8? r.stderr |>.getD "?"}" (.done (retry m s!"read exit {r.exit}"))
    else
    match readOut sh r with
    | .error (x, d) => .done (.stop x d)
    | .ok pending => .hole (.serve w sh m pending)

/-- One tick: the shape once, then the read and the act. -/
def tickP (w : Where) (m : Mem) : Prog Tick :=
  match m.shape with
  | some sh => readP w sh m
  | none =>
    .cmd .describe fun
    | .error e => .say s!"describe {e}" (.done (retry m s!"describe {e}"))
    | .ok r =>
      if r.exit ≠ Protocol.CommandExit.ok.code then
        .say s!"describe exit {r.exit} {String.fromUTF8? r.stderr |>.getD "?"}"
          (.done (retry m s!"describe exit {r.exit}"))
      else
        match describeOut w.conf r with
        | .ok sh =>
          .say s!"bell answer method {sh.answer} pending limit {sh.pending.limit}" <|
            readP w sh { m with shape := some sh }
        | .error (x, d) => .done (.stop x d)

/-- What follows the refused answer `t` for `ring`: the `use` slot's choice. -/
def useP (m : Mem) (ring : Ring) (n line : String) (pending : List Ring) (gone : List ByteArray) :
    Prog Tick :=
  match useChoice ring pending gone with
  | .closed =>
    .say s!"answer refused ({line}); the ring is no longer pending" <|
      forgetThen (.next { m with kept := none, retries := 0 })
  | .withdraw c =>
    .say s!"answer withdrawn {ring.notBefore} {Lang.Print.hex ring.ringer}: its support {Lang.Print.hex c} is gone ({line})" <|
      .note ((ring, Lang.Print.hex c) :: m.withdrawn) fun ok =>
        if ok then
          forgetThen (.next { m with kept := none, retries := 0, withdrawn := (ring, Lang.Print.hex c) :: m.withdrawn })
        else .done (.stop .volume "withdrawn")
  | .stop => .done (.stop .answerRefused s!"{n} ({line})")

/-- Fill a hole: `serve` by the act the slot chooses, the withdrawn rings that left `pending`
dropped; `use` by `useP`. -/
def fill : Hole → Prog Tick
  | .serve w sh m pending =>
    actOn w sh (m.prune pending) pending
  | .use _ m ring n line pending gone => useP m ring n line pending gone

/-- How deep holes nest in one tick: `serve`'s filling holds `use`, whose filling holds none. -/
def holesMax : Nat := 2

/-- Perform a tick's term by a handler, holes nesting at most `n` deep: the calculus's interpreter,
each hole filled by `fill` when it is reached. A term whose holes nest deeper ends `bellShape holes`. -/
def Prog.interpN {M : Type → Type} [Monad M] (h : Handler M) (n : Nat) (p : Prog Tick) : M Tick := do
  match ← Lang.Contextual.Slot.interp (W := Empty) (fun op => h.call op) (fun hl => .ok (fill hl)) n p with
  | .done _ a => pure a
  | .withdrawn _ _ e => nomatch e
  | .bound _ _ => pure (.stop .bellShape "holes")

/-- Perform a tick's term at `holesMax`, which every tick fits (`Proofs.ResidentRun.tickP_fits`), so
no tick ends `bellShape holes`. -/
def Prog.interp {M : Type → Type} [Monad M] (h : Handler M) (p : Prog Tick) : M Tick :=
  p.interpN h holesMax

/-- One tick, performed. -/
def tick (w : Where) (m : Mem) : IO Tick := (tickP w m).interp (ioHandler w)

/-- The resident: place itself, read its config, then tick. -/
def run (args : List String) : IO UInt32 := do
  let some a := parse (args.map String.toUTF8) | stop .argvNotPlan "argv shape"
  let some p := place a | stop .argvNotPlan "not this resident's plan"
  -- every path from Lean's plan joined onto its root: equal to argv's by `accepted_is_plan`
  let path (root : ByteArray) (rel : Option Hosting.Path) := rel.bind fun r => pathOf (joinOnto root r)
  let (some pkg, some vol, some b, some mem) :=
      (path p.root p.plan.read.head?, path p.root p.plan.write.head?,
       path p.brokerRoot p.plan.broker.head?, path p.memberRoot p.plan.member.head?)
    | stop .argvNotPlan "plan paths"
  let confPath := pkg / "resident.conf"
  let text ← (do
      let md ← confPath.metadata
      if md.byteSize.toNat > confBytesMax then throw (IO.userError "tooLarge")
      IO.FS.readFile confPath).toBaseIO
  let .ok text := text | stop .confMissing confPath.toString
  let some conf := Conf.read text | stop .confMalformed ""
  -- the kept answer is named by the bell, so a config naming another bell never meets it
  let kname := s!"kept-{Lang.Print.hex conf.bell}"
  let nname := s!"withdrawn-{Lang.Print.hex conf.bell}"
  let w : Where :=
    { conf, member := mem.toString, broker := b.toString, vol, kept := vol / kname, noted := vol / nname }
  let held ← if ← w.kept.pathExists then
      match ← (IO.FS.readFile w.kept).toBaseIO with
      | .ok s => pure (some (some s))
      | .error _ => pure (some none)
    else pure none
  let some kept := seedOf held | stop .volume "kept unreadable"
  unless ← resume w held do return ← stop .volume "resume"
  let heldNoted ← if ← w.noted.pathExists then
      match ← (IO.FS.readFile w.noted).toBaseIO with
      | .ok s => pure (some (some s))
      | .error _ => pure (some none)
    else pure none
  let some withdrawn := notedSeed heldNoted | stop .volume "withdrawn unreadable"
  unless ← resumeAt w.notedAt heldNoted do return ← stop .volume "resume withdrawn"
  say s!"serving bell {Lang.Print.hex conf.bell}{if kept.isSome then " (an answer is kept)" else ""}"
  let mut m : Mem := { shape := none, kept, withdrawn }
  for _ in [0:lifetimeTicks] do
    match ← tick w m with
    | .stop e d => return ← stop e d
    | .next m' => m := m'
    IO.sleep tickMs.toUInt32
  stop .lifetime ""

end Nanodregg.Hosting.Resident
