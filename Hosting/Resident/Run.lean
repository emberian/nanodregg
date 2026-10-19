/-
# Hosting.Resident.Run — `resident`: THE BAR's hosted Hermes (HOSTING-27, HOSTING-31)

    resident <the plan's paths, as grain-launch passes them>

A resident grain's program (`pkg/resident`), confined by grain-launch like any grain. It can see its
package (read), its volume (read and write), its own broker socket and its own member socket, and
nothing else. Its argv must be its plan (`Args.place`), or it ends `argvNotPlan` before reading
anything. It reads `pkg/resident.conf`, ONE Lang data value at `Bell.confTy`. Then, every
`tickMs`, for at most `lifetimeTicks` ticks:
1. Until it has the bell's shape, it describes the bell (`read OBJ ?` → `Shape.read`).
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
   forgotten; if it is still pending, the resident ends `answerRefused NAME` (`program` for a
   method's check such as `notResident`, `grantRight` for a grant without the right). The kept
   text stays, so a restart answers again but never asks again.
A transport failure on either socket is logged and retried at the next tick: a not-sent ask costs
nothing, a spent one is never repeated. Every line on stderr starts `resident: `.

The tick is a tree of effects (`Prog`, HOSTING-35): `tickP` builds it, `Prog.run` performs it one
node at a time. The order above is a theorem over every path of that tree, for every reply the
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
stops again until the operator acts. That is right for every refusal known to reach it (the
resident is not the bell's, the grant lacks `invoke:0`, `answers` is full until the owner
retires), each of which refuses every ring alike; a refusal that singled out one ring would block
the rest behind it, and would need a refused marker to skip it. K = `pending`'s limit is complete:
the kernel holds at most `limit` rows (`relationFull`), and a range read past K is refused, never
truncated, so a missed ring would be a failed read (logged, retried), never a silent gap. A not-sent ask whose intent cannot be
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

/-- The argv a command sends (an unprintable answer sends nothing: `deliverP` never builds that
node, and `answerArg_some` says it cannot arise). -/
def Cmd.argv (c : Conf) : Cmd → List ByteArray
  | .describe => describeArgv c
  | .read sh | .reread sh => pendingArgv c sh
  | .invoke sh r t => match answerArg r t with
    | some a => invokeArgv c sh a
    | none => []

/-- One tick as a tree of effects (HOSTING-35): each node is ONE effect on the world outside the
process, and its continuation is what the tick does with that effect's result. `Prog.run` performs
it (the deployed path: `tick` below is `(tickP w m).run w`); `Proofs.ResidentRun.Runs` is every path
through it, over every result each effect could have, and `tick_order` is the order of effects
on every path. A continuation never returns into its caller: every node is in tail position, so the
tree is the tick's whole control flow and nothing runs between two nodes but pure code. -/
inductive Prog (α : Type) where
  | done (a : α)
  /-- one command on the member socket: `c.argv` -/
  | cmd (c : Cmd) (k : Except String Reply → Prog α)
  /-- keep `(r, t)` durably (`keep`) -/
  | keep (r : Ring) (t : ByteArray) (k : Bool → Prog α)
  /-- forget the kept answer durably (`forget`) -/
  | forget (k : Bool → Prog α)
  /-- one ask on the broker socket -/
  | ask (r : Ring) (q : Broker.Ask) (k : AskEnd → Prog α)
  /-- one line on stderr -/
  | say (s : String) (k : Prog α)

/-- Perform a tick's tree: each node's ONE effect, then its continuation on the result. -/
def Prog.run {α : Type} (w : Where) : Prog α → IO α
  | .done a => pure a
  | .cmd c k => do let r ← Resident.command w.member (c.argv w.conf); (k r).run w
  | .keep r t k => do let b ← Resident.keep w r t; (k b).run w
  | .forget k => do let b ← Resident.forget w; (k b).run w
  | .ask _ q k => do let e ← Resident.ask w.broker q; (k e).run w
  | .say s k => do Resident.say s; k.run w

/-- The intent kept before an ask: a restart that finds it answers the ring with it and never asks
again. -/
def intentText : ByteArray := fit (named "unanswered restart")

/-- Forget the kept answer, then go on with `next` (or end `volume`). -/
def forgetThen (next : Tick) : Prog Tick :=
  .forget fun ok => if ok then .done next else .done (.stop .volume "forget")

/-- Invoke `answer` for the kept ring `ring` with `t`; what the tick does next.

A refusal is judged by the bell's ROWS, not by its name: the member surface names a method's check
only as `program`, and a kernel refusal of the retract names the row, not the reason. So after any
refusal the resident reads `pending` again. If the ring is still pending, the bell refused THIS
answer: the resident ends `answerRefused NAME` with the text still kept. Otherwise the ring was
answered (a delivery that landed but whose reply was lost), and the kept answer is forgotten. -/
def deliverP (sh : Shape) (m : Mem) (ring : Ring) (t : ByteArray) : Prog Tick :=
  match answerArg ring t with
  | none => .done (.stop .bellShape "answer unprintable (unreachable: answerArg_some)")
  | some _ =>
  .cmd (.invoke sh ring t) fun
  | .error e => .say s!"answer unsettled {e}" (.done (.next m))
  | .ok r =>
    if r.exit = Protocol.CommandExit.ok.code then
      .say s!"answered {ring.notBefore} {Lang.Print.hex ring.ringer} {t.size} bytes" <|
        forgetThen (.next { m with kept := none, unread := 0 })
    else if r.exit = Protocol.CommandExit.refused.code then
      let n := refusedName r.stderr
      let line := ((String.fromUTF8? r.stderr).getD "?").trimAsciiEnd.toString
      let unread (why : String) : Prog Tick :=
        .say s!"answer refused ({line}); state unread {why}" <|
          if m.unread + 1 ≥ unreadMax then .done (.stop .answerRefused s!"{n} ({line}; state unread)")
          else .done (.next { m with unread := m.unread + 1 })
      .cmd (.reread sh) fun
      | .error e => unread e
      | .ok rr =>
        if rr.exit ≠ Protocol.CommandExit.ok.code then unread s!"exit {rr.exit}" else
        match Ring.readAll sh ((String.fromUTF8? rr.stdout).getD "") with
        | .error e => .done (.stop .bellShape e)
        | .ok pending =>
          if ring ∈ pending then .done (.stop .answerRefused s!"{n} ({line})")
          else
            .say s!"answer refused ({line}); the ring is no longer pending" <|
              forgetThen (.next { m with kept := none, unread := 0 })
    else .say s!"answer unsettled exit {r.exit}" (.done (.next m))

/-- After the ask: say how it went and keep the answer `t` (the intent replaced), then deliver. -/
def answeredP (sh : Shape) (m : Mem) (ring : Ring) (t : ByteArray) : Prog Tick :=
  .say s!"asked; answer {t.size} bytes" <| .keep ring t fun ok =>
    if ok then deliverP sh { m with kept := some (ring, t) } ring t
    else .done (.stop .volume "keep")

/-- What the tick does with the pending rings it read: `decideTick`'s act. -/
def actOn (w : Where) (sh : Shape) (m : Mem) (pending : List Ring) : Prog Tick :=
  match decideTick pending m.kept with
  | .idle =>
    if m.kept.isSome then forgetThen (.next { m with kept := none })
    else .done (.next { m with kept := none })
  | .answer ring t => deliverP sh m ring t
  | .ask ring =>
    -- the intent, before a byte of the ask leaves
    .keep ring intentText fun ok =>
    if !ok then .done (.stop .volume "keep") else
    .ask ring (askOf w.conf ring) fun
    | .notSent why => .say s!"ask not sent {why}" <| forgetThen (.next { m with kept := none })
    | .answered a => answeredP sh m ring (answerText a)
    | .lost why =>
      .say s!"ask spent, answer lost {why}" <| answeredP sh m ring (fit (named s!"unanswered {why}"))

/-- The tick's one read of every pending ring, then its act. -/
def readP (w : Where) (sh : Shape) (m : Mem) : Prog Tick :=
  .cmd (.read sh) fun
  | .error e => .say s!"read {e}" (.done (.next m))
  | .ok r =>
    if r.exit ≠ Protocol.CommandExit.ok.code then
      .say s!"read exit {r.exit} {String.fromUTF8? r.stderr |>.getD "?"}" (.done (.next m))
    else
    match Ring.readAll sh ((String.fromUTF8? r.stdout).getD "") with
    | .error e => .done (.stop .bellShape e)
    | .ok pending => actOn w sh m pending

/-- One tick: the shape once, then the read and the act. -/
def tickP (w : Where) (m : Mem) : Prog Tick :=
  match m.shape with
  | some sh => readP w sh m
  | none =>
    .cmd .describe fun
    | .error e => .say s!"describe {e}" (.done (.next m))
    | .ok r =>
      if r.exit ≠ Protocol.CommandExit.ok.code then
        .say s!"describe exit {r.exit} {String.fromUTF8? r.stderr |>.getD "?"}" (.done (.next m))
      else
        match Shape.read (String.fromUTF8? r.stdout |>.getD "") with
        | .ok sh =>
          .say s!"bell answer method {sh.answer} pending limit {sh.pending.limit}" <|
            readP w sh { m with shape := some sh }
        | .error e => .say s!"bellShape {e}" (.done (.stop .bellShape "description"))

/-- One tick, performed. -/
def tick (w : Where) (m : Mem) : IO Tick := (tickP w m).run w

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
