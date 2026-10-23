/-
# Lang.Bell — the deployed Bell, as the terms a theorem can name (HOSTING-43 (e), HOSTING-44)

The sponsor installs `world/resident/Bell`, the core text `world/resident/Bell.ob` lowers to
(`Lang.Journey` LB0). It is an `activity` (LANG-58/59): the cursor `pending` under the generated
`queued` guard, the log `rings` under the generated waiting guard `rung`, plus the hand-written
`answer`, `ring`, `retire`, `open`, `close` and the law `bell`. Its root has no imports and no holes
and its body is a record, so the closed monitor theorem applies to it as installed
(`Lang.Proofs.Bell.bell_monitored`).

This module names the parts of that package the witness reads, built by the same generators and
lowering pieces the surface uses (`Std.activityWaiting`, `Std.activityLog`, `Surface.boundCheck`),
and `shapeOk p`: package `p` is the Bell at every one of them. `Lang.Journey`'s row LBw computes
`shapeOk` of the shipped core text, so a re-emitted Bell that changes any of them reads RED there by
name. The theorems are in `Lang.Proofs.Bell`.
-/
import Lang.Surface
import Lang.Program

namespace Nanodregg.Lang.Bell

open Nanodregg.Lang.Std

/-- The Bell's state: whether it rings, and the resident member. -/
def S : Ty := .record [("open", .bool), ("resident", .digest)]

/-- The one plan's capture: the ring's text. -/
def askCaptured : Ty := .record [("text", .bytes)]

/-- The Bell's one plan, `ask` (`(plan ask (arg (rec (text bytes))) (resp bytes) (start state)
(resume state))`), as `Surface.activityDecl` closes its functions. -/
def ask : ActivityPlan where
  name := "ask"
  captured := askCaptured
  response := Ty.bytes
  precondition := .lam S (.lam askCaptured (.lam reqTy (.bool true)))
  start := .lam S (.lam askCaptured (.lam reqTy (.var 2)))
  resume := .lam S (.lam askCaptured (.lam Ty.bytes (.lam reqTy (.var 3))))

def plans : List ActivityPlan := [ask]

/-- The resumer, `(deq req.agent state.resident)`: the request's signer is the resident. -/
def resumer : Term := .lam S (.lam reqTy (.prim .deq (.get (.var 0) "agent") (.get (.var 1) "resident")))

/-- The Bell's refusal names (`(refusals "notResident" "unrung" "text")`). -/
def names : ActivityVocabulary where
  notResumer := "notResident"
  unstarted := "unrung"
  captured := "text"

/-- The cursor, `pending`, under `queued`; the log, `rings`, under `rung` (`(limits 64 1024)`). -/
def pending : RelDecl := activityCursor plans 64 "queued"
def rings : RelDecl := activityLog plans 1024 "rung"

/-- The relations, by index: `pending` 0, `rings` 1. -/
def rels : List (Label × RelDecl) := [("pending", pending), ("rings", rings)]

def E : Ty := editTy rels

/-- `answer`'s argument type: the ring's key, the ring's text as the resident read it, the answer. -/
def answerArg : Ty := .record [("notBefore", .nat), ("ringText", .bytes), ("ringer", .digest), ("text", .bytes)]

def answerRes : Ty := resultTy S [] E 2

/-- `answer`'s declared type: no reads, no calls, two edits. -/
def answerTy : Ty := methodTy S answerArg [] (.record []) E 2

/-- The ring's key, from `answer`'s argument (`(record (agent arg.ringer) (notBefore arg.notBefore))`). -/
def ringKey : Term := .record [("agent", .get (.var 1) "ringer"), ("notBefore", .get (.var 1) "notBefore")]

/-- `answer`'s body under its bound checks: the resident's check, then the upsert of `rings` at the
ring's key to `answered (some (ask arg.text))` with capture `ask {text := arg.ringText}`, and the
retract of `pending` there. -/
def answerBody : Term :=
  .ite (.prim .deq (.get (.var 0) "agent") (.get (.var 2) "resident"))
    (resultT (.record []) (.var 2) (.record [
      ("e0", someCallT E (.inj E "rings" (.inj (relEditTy rings) "upsert" (.record [("key", ringKey),
        ("val", .record [
          ("answered", someCallT (activityResponses plans) (.inj (activityResponses plans) "ask" (.get (.var 1) "text"))),
          ("captured", .inj (activityCaptured plans) "ask" (.record [("text", .get (.var 1) "ringText")]))])])))),
      ("e1", someCallT E (.inj E "pending" (.inj (relEditTy pending) "retract" (.record [("key", ringKey)]))))]))
    (.refuse answerRes "notResident".toUTF8)

/-- `answer`'s argument bounds, `(ringText (bytes 1 2000))` and `(text (bytes 1 2000))`. -/
def answerBounds : List Surface.Bound := [⟨["ringText"], true, 1, 2000⟩, ⟨["text"], true, 1, 2000⟩]

/-- The `answer` method term, as the surface lowers it (`Surface.wrapMethod`). -/
def answer : Term :=
  .lam (.record []) (.lam S (.lam answerArg (.lam reqTy (Surface.boundCheck answerRes answerBounds answerBody))))

/-- The `rung` guard: the generated waiting guard over the Bell's log. -/
def rung : Term := activityWaiting S plans rings resumer names

/-- The two body fields the witness reads. -/
def bodyOk : Term → Bool
  | .record fs => decide (Row.find? "answer" fs = some answer) && decide (Row.find? "rung" fs = some rung)
  | _ => false

/-- **Package `p` is the Bell** at every place the witness reads: a root with no imports and no
holes, the Bell's state and relations, `answer`'s declared type, and the body fields `answer` and
`rung`. -/
def shapeOk (p : Package) : Bool :=
  decide (p.imports = []) && decide (p.holes = []) && decide (p.state = S) && decide (p.rels = rels) &&
    decide (Row.find? "answer" (recordRow p.iface) = some answerTy) && bodyOk p.body

/-- An `answer` argument: the ring's key `(notBefore, ringer)`, its text, the answer text. -/
def answerData (nb : Nat) (ringText ringer text : ByteArray) : Data :=
  .record [("notBefore", .nat nb), ("ringText", .bytes ringText), ("ringer", .digest ringer), ("text", .bytes text)]

/-- A ring's key as data. -/
def keyData (nb : Nat) (ringer : ByteArray) : Data :=
  .record [("agent", .digest ringer), ("notBefore", .nat nb)]

/-- An answered ring's `rings` value: `answered (some (ask text))`, captured `ask {text := ringText}`. -/
def answeredVal (ringText text : ByteArray) : Data :=
  .record [("answered", .inj "some" (.inj "ask" (.bytes text))),
    ("captured", .inj "ask" (.record [("text", .bytes ringText)]))]

/-- The edits data `answer` returns for `answerData nb x k y`: `rings` upserted at the ring's key to
`answeredVal x y`, `pending` retracted there. -/
def answerEdits (nb : Nat) (x k y : ByteArray) : Data :=
  .record [("e0", .inj "some" (.inj "rings" (.inj "upsert" (.record [("key", keyData nb k), ("val", answeredVal x y)])))),
    ("e1", .inj "some" (.inj "pending" (.inj "retract" (.record [("key", keyData nb k)]))))]

end Nanodregg.Lang.Bell
