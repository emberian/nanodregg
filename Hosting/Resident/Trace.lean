/-
# Hosting.Resident.Trace — the vocabulary of a tick's traces (HOSTING-36)

The effects a tick performs, each with the result it had (`Ev`), and the readings of a trace the
order theorems state (`Proofs.ResidentRun`): the effects on the world (`core`: stderr dropped), a
read's rings, a description's shape, the text an ask's end leaves to keep, the asks, invokes and
describes a trace holds, and the kept answer its keeps and forgets leave. Nothing here performs
anything: the deployed exe never imports it.
-/
import Hosting.Resident.Run

namespace Nanodregg.Hosting.Resident

/-- One effect a tick performed, with the result it had. -/
inductive Ev
  | cmd (c : Cmd) (x : Except String Reply)
  | keep (r : Ring) (t : ByteArray) (ok : Bool)
  | forget (ok : Bool)
  | ask (r : Ring) (q : Broker.Ask) (x : AskEnd)
  | say (s : String)

def Ev.quiet : Ev → Bool
  | .say _ => true
  | _ => false

/-- The effects on the world: every `say` dropped. -/
def core (es : List Ev) : List Ev := es.filter fun e => !e.quiet

/-- The rings a read's reply lists, when it is a successful read the resident could parse. -/
def readRings (sh : Shape) : Except String Reply → Option (List Ring)
  | .ok r => if r.exit = Protocol.CommandExit.ok.code then
      (Ring.readAll sh ((String.fromUTF8? r.stdout).getD "")).toOption else none
  | .error _ => none

/-- The shape a describe's reply reads as. -/
def describedShape : Except String Reply → Option Shape
  | .ok r => if r.exit = Protocol.CommandExit.ok.code then
      (Shape.read (String.fromUTF8? r.stdout |>.getD "")).toOption else none
  | .error _ => none

/-- The answer text an ask's end leaves to keep: none when the ask never left. -/
def askText : AskEnd → Option ByteArray
  | .notSent _ => none
  | .answered a => some (answerText a)
  | .lost why => some (fit (named s!"unanswered {why}"))

/-- The rings a list of effects asks about, in order. -/
def asks (es : List Ev) : List Ring := es.filterMap fun | .ask r _ _ => some r | _ => none

/-- The answers a list of effects invokes, in order. -/
def invokes (es : List Ev) : List (Ring × ByteArray) :=
  es.filterMap fun | .cmd (.invoke _ r t) _ => some (r, t) | _ => none

/-- How many describes a list of effects sends. -/
def describes (es : List Ev) : Nat := (es.filter fun | .cmd .describe _ => true | _ => false).length

/-- The kept answer after a list of effects, from `k`: each successful keep sets it, each successful
forget clears it; nothing else moves it. -/
def keptAfter : Option (Ring × ByteArray) → List Ev → Option (Ring × ByteArray)
  | k, [] => k
  | _, .keep r t true :: es => keptAfter (some (r, t)) es
  | _, .forget true :: es => keptAfter none es
  | k, _ :: es => keptAfter k es

end Nanodregg.Hosting.Resident
