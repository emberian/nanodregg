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
  | note (l : List (Ring × String)) (ok : Bool)
  | ask (r : Ring) (q : Broker.Ask) (x : AskEnd)
  | say (s : String)

def Ev.quiet : Ev → Bool
  | .say _ => true
  | _ => false

/-- The effects on the world: every `say` dropped. -/
def core (es : List Ev) : List Ev := es.filter fun e => !e.quiet

/-- The rings a read's reply lists, when it is a successful read the resident could decode and parse
(`readOut`: an undecodable stdout lists nothing, HOSTING-49). -/
def readRings (sh : Shape) : Except String Reply → Option (List Ring)
  | .ok r => if r.exit = Protocol.CommandExit.ok.code then (readOut sh r).toOption else none
  | .error _ => none

/-- The shape a describe's reply reads as, for the configured bell (`describeOut`). -/
def describedShape (c : Conf) : Except String Reply → Option Shape
  | .ok r => if r.exit = Protocol.CommandExit.ok.code then (describeOut c r).toOption else none
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

/-- Every result an effect could have, by its place in the trace. -/
structure Oracle where
  cmd : Nat → Except String Reply
  keep : Nat → Bool
  forget : Nat → Bool
  note : Nat → Bool
  ask : Nat → AskEnd

/-- The recording handler: each call takes its result from the oracle at its place and appends
itself, with that result, to the trace. -/
def recorder (o : Oracle) : Handler (StateM (Nat × List Ev)) where
  cmd c := modifyGet fun (n, es) => (o.cmd n, (n + 1, es ++ [.cmd c (o.cmd n)]))
  keep r t := modifyGet fun (n, es) => (o.keep n, (n + 1, es ++ [.keep r t (o.keep n)]))
  forget := modifyGet fun (n, es) => (o.forget n, (n + 1, es ++ [.forget (o.forget n)]))
  note l := modifyGet fun (n, es) => (o.note n, (n + 1, es ++ [.note l (o.note n)]))
  ask r q := modifyGet fun (n, es) => (o.ask n, (n + 1, es ++ [.ask r q (o.ask n)]))
  say s := modify fun (n, es) => (n + 1, es ++ [.say s])

/-- A wrong interpreter, kept only as the subject of a tooth (`interpTwice_no_path`): it performs a
command node's call twice. Nothing calls it. -/
def Prog.interpTwice {M : Type → Type} [Monad M] (h : Handler M) : Prog Tick → M Tick :=
  Lang.Contextual.Protocol.fold (S := sig) (Hole := fun _ => Hole) (A := fun _ => Tick) (C := fun _ => M Tick)
    { ret := fun a => pure a
      call := fun op k => match op, k with
        | Eff.cmd c, k => do let _ ← h.cmd c; let x ← h.cmd c; k x
        | Eff.keep r t, k => do let b ← h.keep r t; k b
        | Eff.forget, k => do let b ← h.forget; k b
        | Eff.note l, k => do let b ← h.note l; k b
        | Eff.ask r q, k => do let e ← h.ask r q; k e
        | Eff.say s, k => do h.say s; k ()
      hole := fun _ => pure (.stop .bellShape "holes") }

end Nanodregg.Hosting.Resident
