/-
# Hosting.Resident.Run — `resident`: THE BAR's hosted Hermes (HOSTING-27)

    resident <the plan's paths, as grain-launch passes them>

A resident grain's program (`pkg/resident`), confined by grain-launch like any grain. It can see its
package (read), its volume (read and write), its own broker socket and its own member socket, and
nothing else. Its argv must be its plan (`Args.place`), or it ends `argvNotPlan` before reading
anything. It reads `pkg/resident.conf`, ONE Lang data value at `Bell.confTy`. Then, every
`tickMs`, for at most `lifetimeTicks` ticks:
1. Until it has the bell's shape, it describes the bell (`read OBJ ?` → `Shape.read`).
2. It reads the bell (`read OBJ` → `Ring.read` at the described state type).
3. It acts on `decideTick`:
   - idle: forget a kept answer the bell no longer waits for;
   - ask: first keep the intent (`(unanswered restart)`) for the ring, then one ask on the
     broker socket; the answer text replaces the intent in `vol/kept-<bell>` before the bell sees
     it (every keep is synced, renamed, directory-synced and read back);
   - answer: invoke `answer` with the kept text.
4. The bell taking the answer forgets it. A refusal is judged by the bell's state: if the ring
   is no longer waiting (answered already, `unrung`), the answer is forgotten; if it still waits,
   the resident ends `answerRefused NAME` (`program` for a method's check such as `notResident`,
   `noGrant` for a missing grant). The kept text stays, so a restart answers again but never asks
   again.
A transport failure on either socket is logged and retried at the next tick: a not-sent ask costs
nothing, a spent one is never repeated. Every line on stderr starts `resident: `.

Limits, named: a ring is identified by (ringer, text), so an identical ring arriving while an
answer for the last one is still kept (its delivery unsettled, or between a refusal and the
re-read) is answered with the kept text, or ends the resident wrongly, never asked twice; a ring
nonce in the bell's state would make the identity true. A not-sent ask whose intent cannot be
forgotten ends `volume`, and the restart answers that ring `(unanswered restart)` without having
asked: one wasted answer, no meter charge.

What still stands between this process and a real model is the operator's, not code: the provider's
leaf SPKI pin in the deployed PINS file (shipped empty, so every real call is refused `pinMismatch`
before a request byte, HOSTING-28), and a provider key in keybroker's key file (Ember's act). Until
both are in place, it answers every ring `(refused pinMismatch)` or `(refused keyMissing)`.
-/
import Hosting.Resident.Args
import Hosting.Resident.Bell
import Hosting.Resident.Sockets
import Protocol.Command.Exit
import Host.File

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
  deriving DecidableEq, Repr

namespace Exit

def all : List Exit := [argvNotPlan, confMissing, confMalformed, bellShape, answerRefused, volume, lifetime]

def code : Exit → UInt32
  | argvNotPlan => 10 | confMissing => 11 | confMalformed => 12 | bellShape => 13
  | answerRefused => 14 | volume => 15 | lifetime => 16

def name : Exit → String
  | argvNotPlan => "argvNotPlan" | confMissing => "confMissing" | confMalformed => "confMalformed"
  | bellShape => "bellShape" | answerRefused => "answerRefused" | volume => "volume"
  | lifetime => "lifetime"

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

/-- The refusal's name in a refused command's stderr (`refused NAME …`, `StdioRefusal`). -/
def refusedName (stderr : ByteArray) : String :=
  match (String.fromUTF8? stderr).map (·.splitOn " ") with
  | some ("refused" :: n :: _) => (n.splitOn "\n").headD n
  | _ => "?"

/-- What the resident remembers between ticks. -/
structure Mem where
  shape : Option Shape
  kept : Option (Ring × ByteArray)
  /-- refusals in a row whose bell state could not be re-read (`deliver`) -/
  unread : Nat := 0

/-- Refused answers in a row with the state unread before the resident ends `answerRefused`:
re-delivering never asks, but a refusal must not repeat forever. -/
def unreadMax : Nat := 8

/-- The result of one tick: go on with this memory, or end. -/
inductive Tick
  | next (m : Mem)
  | stop (e : Exit) (detail : String)

/-- The files of one resident. -/
structure Where where
  conf : Conf
  member : String
  broker : String
  vol : System.FilePath
  kept : System.FilePath
  keptTmp : System.FilePath

/-- Forget the kept answer, durably (the directory entry is synced). -/
def forget (w : Where) : IO Bool := do
  let act : IO Unit := do
    if ← w.kept.pathExists then
      IO.FS.removeFile w.kept
      Host.syncDir w.vol.toString
  match ← act.toBaseIO with
  | .ok () => pure true
  | .error _ => pure false

/-- Keep `(r, t)` durably before anything depends on it: written to a fresh file, synced
(`Host.File`), renamed over the kept file, the directory synced, and read back; `false` unless what
reads back is exactly `(r, t)` (the premise `Proofs.Resident.kept_reads` states, asserted where it
enters). -/
def keep (w : Where) (r : Ring) (t : ByteArray) : IO Bool := do
  let some s := keptText r t | return false
  let act : IO (Option (Ring × ByteArray)) := do
    if ← w.keptTmp.pathExists then IO.FS.removeFile w.keptTmp
    let f ← Host.File.open w.keptTmp .createNew
    f.writeAll s.toUTF8
    f.sync
    IO.FS.rename w.keptTmp w.kept
    Host.syncDir w.vol.toString
    pure (keptRead (← IO.FS.readFile w.kept))
  match ← act.toBaseIO with
  | .ok back => pure (decide (back = some (r, t)))
  | .error _ => pure false

/-- Invoke `answer` with `t` for the kept ring; what the tick does next.

A refusal is judged by the bell's STATE, not by its name: the member surface names a method's
check only as `program` (the bell's own reason, `unrung` or `notResident`, does not cross it). So
after any refusal the resident reads the bell again. If the same ring is still waiting, the bell
refused THIS answer: the resident ends `answerRefused NAME` with the text still kept. Otherwise the
ring was answered or replaced (the `unrung` race), and the kept answer is forgotten. -/
def deliver (w : Where) (sh : Shape) (m : Mem) (t : ByteArray) : IO Tick := do
  let some arg := answerArg t | return .stop .bellShape "answer unprintable (unreachable: answerArg_some)"
  match ← command w.member (invokeArgv w.conf sh arg) with
  | .error e =>
    say s!"answer unsettled {e}"
    pure (.next m)
  | .ok r =>
    if r.exit = Protocol.CommandExit.ok.code then
      say s!"answered {t.size} bytes"
      unless ← forget w do return .stop .volume "forget"
      pure (.next { m with kept := none, unread := 0 })
    else if r.exit = Protocol.CommandExit.refused.code then
      let n := refusedName r.stderr
      let line := ((String.fromUTF8? r.stderr).getD "?").trimAsciiEnd.toString
      let unread (why : String) : IO Tick := do
        say s!"answer refused ({line}); state unread {why}"
        if m.unread + 1 ≥ unreadMax then return .stop .answerRefused s!"{n} ({line}; state unread)"
        pure (.next { m with unread := m.unread + 1 })
      match ← command w.member (readArgv w.conf) with
      | .error e => unread e
      | .ok rr =>
        if rr.exit ≠ Protocol.CommandExit.ok.code then return ← unread s!"exit {rr.exit}"
        match Ring.read sh ((String.fromUTF8? rr.stdout).getD "").trimAsciiEnd.toString with
        | .error e => pure (.stop .bellShape e)
        | .ok pending =>
          if pending.isSome ∧ pending = m.kept.map Prod.fst then
            pure (.stop .answerRefused s!"{n} ({line})")
          else
            say s!"answer refused ({line}); the ring is no longer waiting"
            unless ← forget w do return .stop .volume "forget"
            pure (.next { m with kept := none, unread := 0 })
    else
      say s!"answer unsettled exit {r.exit}"
      pure (.next m)

/-- One tick. -/
def tick (w : Where) (m : Mem) : IO Tick := do
  -- 1. the shape, once
  let m ← match m.shape with
    | some _ => pure (some m)
    | none =>
      match ← command w.member (describeArgv w.conf) with
      | .error e => say s!"describe {e}"; pure (some m)
      | .ok r =>
        if r.exit ≠ Protocol.CommandExit.ok.code then
          say s!"describe exit {r.exit} {String.fromUTF8? r.stderr |>.getD "?"}"
          pure (some m)
        else
          match Shape.read (String.fromUTF8? r.stdout |>.getD "") with
          | .ok sh => say s!"bell answer method {sh.answer}"; pure (some { m with shape := some sh })
          | .error e => say s!"bellShape {e}"; pure none
  let some m := m | return .stop .bellShape "description"
  let some sh := m.shape | return .next m
  -- 2. the state
  match ← command w.member (readArgv w.conf) with
  | .error e => say s!"read {e}"; return .next m
  | .ok r =>
    if r.exit ≠ Protocol.CommandExit.ok.code then
      say s!"read exit {r.exit}"
      return .next m
    let line := ((String.fromUTF8? r.stdout).getD "").trimAsciiEnd.toString
    match Ring.read sh line with
    | .error e => return .stop .bellShape e
    | .ok pending =>
      -- 3. the act
      match decideTick pending m.kept with
      | .idle =>
        if m.kept.isSome then
          unless ← forget w do return .stop .volume "forget"
        return .next { m with kept := none }
      | .answer t => deliver w sh m t
      | .ask ring =>
        -- the intent, before a byte of the ask leaves: a restart that finds it answers the ring
        -- `(unanswered restart)` and never asks again
        unless ← keep w ring (fit (named "unanswered restart")) do return .stop .volume "keep"
        let t ← match ← ask w.broker (askOf w.conf ring) with
          | .notSent why => say s!"ask not sent {why}"; pure none
          | .answered a => pure (some (answerText a))
          | .lost why => say s!"ask spent, answer lost {why}"; pure (some (fit (named s!"unanswered {why}")))
        let some t := t
          | if ← forget w then return .next { m with kept := none } else return .stop .volume "forget"
        say s!"asked; answer {t.size} bytes"
        unless ← keep w ring t do return .stop .volume "keep"
        deliver w sh { m with kept := some (ring, t) } t

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
  let w : Where := { conf, member := mem.toString, broker := b.toString, vol, kept := vol / kname,
                     keptTmp := vol / (kname ++ ".tmp") }
  let kept ← if ← w.kept.pathExists then
      match ← (IO.FS.readFile w.kept).toBaseIO with
      | .ok s => pure (keptRead s |>.map some)
      | .error _ => pure none
    else pure (some none)
  let some kept := kept | stop .volume "kept unreadable"
  say s!"serving bell {Lang.Print.hex conf.bell}{if kept.isSome then " (an answer is kept)" else ""}"
  let mut m : Mem := { shape := none, kept }
  for _ in [0:lifetimeTicks] do
    match ← tick w m with
    | .stop e d => return ← stop e d
    | .next m' => m := m'
    IO.sleep tickMs.toUInt32
  stop .lifetime ""

end Nanodregg.Hosting.Resident
