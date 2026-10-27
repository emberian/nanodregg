/-
# Lang.Bell — the deployed Bell, as the terms a theorem can name (HOSTING-43 (e), HOSTING-44)

The sponsor installs `world/resident/Bell`, the core text `world/resident/Bell.ob` lowers to
(`Lang.Journey` LB0). It is an `activity` (LANG-58/59): the cursor `pending` under the generated
`queued` guard, the log `rings` under the generated waiting guard `rung`, plus the hand-written
`answer`, `ring`, `retire`, `open`, `close` and the law `bell`. Its root has no imports and no holes
and its body is a record, so the closed monitor theorem applies to it as installed
(`Lang.Proofs.Bell.bell_monitored`).

HOSTING-53 (the inbox): the ring's capture is `{text, to}` with `to` an optional AIM (`aimTy`); `answer`'s
argument echoes it and, for an aimed ring, returns one typed nested call (`forwardT`) to the aim's target
in the same Turn, besides the two edits. The resident pins nothing new: the `rung` guard compares the
capture, so an answer that drops or alters the aim is refused `rung: text`.

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

/-- An AIM (HOSTING-53): where a ring's answer is delivered. The target object, the index of its
method (the `propose` of a `Std.hole` at `bytes`: the document's section, LANG-83), the grant the
Bell object holds on it (the forward's `via`, and its justification: the candidate's support is
`(cell = via, pin = via)`, the doc row's own shape), and the candidate id the ringer chose. -/
def aimTy : Ty := .record [("cand", .digest), ("method", .nat), ("target", .digest), ("via", .digest)]

/-- A candidate's support, as `Std.hole` declares it (`holeSupport`). -/
def supportTy : Ty := .record [("cell", .digest), ("pin", .digest)]

/-- The argument of the target's `propose` (`Std.hole`'s `proposal` at `V := bytes`): what the
forward sends. -/
def proposalTy : Ty := .record [("cand", .digest), ("s0", optTy supportTy), ("s1", optTy supportTy), ("value", .bytes)]

/-- The one plan's capture: the ring's text and its optional aim. Immutable with the ring (the
`rung` guard compares the capture), so an answer must echo the aim the ring was rung with. -/
def askCaptured : Ty := .record [("text", .bytes), ("to", optTy aimTy)]

/-- `ring`'s argument type: the text and the optional aim (`(rec (text (bytes 1 2000)) (to (option Aim)))`,
the bounds being checks). -/
def ringArg : Ty := .record [("text", .bytes), ("to", optTy aimTy)]

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

/-- `answer`'s argument type: the ring's key, the ring's text and aim as the resident read them,
the answer. -/
def answerArg : Ty :=
  .record [("notBefore", .nat), ("ringText", .bytes), ("ringer", .digest), ("text", .bytes), ("to", optTy aimTy)]

/-- `answer`'s one call slot: an `invoke` whose argument is a `proposalTy` (LANG-77's typed slot). -/
def callK : Ty := .sum [("invoke", invokeArm proposalTy)]

def answerRes : Ty := resultTy S [callK] E 2

/-- `answer`'s declared type: no reads, one invoke slot at `proposalTy`, two edits. -/
def answerTy : Ty := methodTy S answerArg [callK] (.record []) E 2

/-- The ring's key, from `answer`'s argument at de Bruijn index `a`
(`(record (agent arg.ringer) (notBefore arg.notBefore))`). -/
def ringKeyAt (a : Nat) : Term := .record [("agent", .get (.var a) "ringer"), ("notBefore", .get (.var a) "notBefore")]

/-- The ring's key under the method's four binders (arg = 1). -/
def ringKey : Term := ringKeyAt 1

/-- `answer`'s two edits with the argument at index `a`: the upsert of `rings` at the ring's key to
`answered (some (ask arg.text))` with capture `ask {text := arg.ringText, to := arg.to}`, and the
retract of `pending` there. -/
def answerEditsT (a : Nat) : Term :=
  .record [
    ("e0", someCallT E (.inj E "rings" (.inj (relEditTy rings) "upsert" (.record [("key", ringKeyAt a),
      ("val", .record [
        ("answered", someCallT (activityResponses plans) (.inj (activityResponses plans) "ask" (.get (.var a) "text"))),
        ("captured", .inj (activityCaptured plans) "ask" (.record [("text", .get (.var a) "ringText"), ("to", .get (.var a) "to")]))])])))),
    ("e1", someCallT E (.inj E "pending" (.inj (relEditTy pending) "retract" (.record [("key", ringKeyAt a)]))))]

/-- The forward (HOSTING-53): under the `some` arm's binder (the aim at 0, the argument at 2), one
`invoke` of the aim's target at its method with `proposalTy` `{cand := aim.cand, s0 := some {cell :=
aim.via, pin := aim.via}, s1 := none, value := arg.text}`, budget 100000, through the aim's grant. -/
def forwardT : Term :=
  someCallT callK (.inj callK "invoke" (.record [
    ("args", .record [
      ("cand", .get (.var 0) "cand"),
      ("s0", .inj (optTy supportTy) "some" (.record [("cell", .get (.var 0) "via"), ("pin", .get (.var 0) "via")])),
      ("s1", .inj (optTy supportTy) "none" (.record [])),
      ("value", .get (.var 2) "text")]),
    ("budget", natT 100000),
    ("method", .get (.var 0) "method"),
    ("obj", .get (.var 0) "target"),
    ("via", .inj (optTy .digest) "some" (.get (.var 0) "via"))]))

/-- `answer`'s body under its bound checks: the resident's check, then by the argument's aim: none,
the two edits and no call; some, the two edits and the forward. Under the arm's binder the request
is 1, the argument 2, the state 3. -/
def answerBody : Term :=
  .ite (.prim .deq (.get (.var 0) "agent") (.get (.var 2) "resident"))
    (.case (.get (.var 1) "to") [
      ("none", resultT (callsT [noCallT callK]) (.var 3) (answerEditsT 2)),
      ("some", resultT (callsT [forwardT]) (.var 3) (answerEditsT 2))])
    (.refuse answerRes "notResident".toUTF8)

/-- `answer`'s argument bounds, `(ringText (bytes 1 2000))` and `(text (bytes 1 2000))`. -/
def answerBounds : List Surface.Bound := [⟨["ringText"], true, 1, 2000⟩, ⟨["text"], true, 1, 2000⟩]

/-- The `answer` method term, as the surface lowers it (`Surface.wrapMethod`). -/
def answer : Term :=
  .lam (.record []) (.lam S (.lam answerArg (.lam reqTy (Surface.boundCheck answerRes answerBounds answerBody))))

/-- The Bell's declared patience (`(patience 2048)`, LANG-76): an unanswered ring may be retired by
anyone from its key's `notBefore` + 2048 on. -/
def patience : Nat := 2048

/-- The `rung` guard: the generated waiting guard over the Bell's log, at its patience. -/
def rung : Term := activityWaiting S plans rings resumer names (some patience)

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

/-- An aim as data: `{cand, method, target, via}`. -/
def aimData (cand : ByteArray) (method : Nat) (target via : ByteArray) : Data :=
  .record [("cand", .digest cand), ("method", .nat method), ("target", .digest target), ("via", .digest via)]

/-- An optional aim as data. -/
def toData : Option Data → Data
  | none => .inj "none" (.record [])
  | some a => .inj "some" a

/-- An `answer` argument: the ring's key `(notBefore, ringer)`, its text and aim, the answer text. -/
def answerData (nb : Nat) (ringText ringer text : ByteArray) (to : Option Data) : Data :=
  .record [("notBefore", .nat nb), ("ringText", .bytes ringText), ("ringer", .digest ringer), ("text", .bytes text),
    ("to", toData to)]

/-- A ring's key as data. -/
def keyData (nb : Nat) (ringer : ByteArray) : Data :=
  .record [("agent", .digest ringer), ("notBefore", .nat nb)]

/-- An answered ring's `rings` value: `answered (some (ask text))`, captured `ask {text := ringText,
to := aim}`. -/
def answeredVal (ringText text : ByteArray) (to : Option Data) : Data :=
  .record [("answered", .inj "some" (.inj "ask" (.bytes text))),
    ("captured", .inj "ask" (.record [("text", .bytes ringText), ("to", toData to)]))]

/-- The edits data `answer` returns for `answerData nb x k y to`: `rings` upserted at the ring's key
to `answeredVal x y to`, `pending` retracted there. -/
def answerEdits (nb : Nat) (x k y : ByteArray) (to : Option Data) : Data :=
  .record [("e0", .inj "some" (.inj "rings" (.inj "upsert" (.record [("key", keyData nb k), ("val", answeredVal x y to)])))),
    ("e1", .inj "some" (.inj "pending" (.inj "retract" (.record [("key", keyData nb k)]))))]

/-- The argument of the forward (`proposalTy`): the candidate `cand`, supported by the grant `via`
itself (`s0 = some {cell := via, pin := via}`, the doc row's own shape), no second support, the answer
`y` as the value. -/
def proposalData (cand via y : ByteArray) : Data :=
  .record [("cand", .digest cand), ("s0", .inj "some" (.record [("cell", .digest via), ("pin", .digest via)])),
    ("s1", .inj "none" (.record [])), ("value", .bytes y)]

/-- The relation of the target whose row the forward's support cites: `Std.hole`'s `facts`. -/
def forwardRel : String := "facts"

/-- The key of that row: the forward's support is the Bell's grant `via` itself (`proposalData`'s
`s0 = {cell via, pin via}`), so the target's `propose` judges it by the fact row at `cell via`. A
hole's facts are read as the CALLER's points (`Std.holeFactsView`: complete observation of the keys
the caller pinned, never a derivation's ask), so the answer's signer pins this row of the target
(`--pin TARGET/facts KEY`, HOSTING-58); without it the forward is refused `unpinned support0`. -/
def forwardKey (via : ByteArray) : Data := .record [("cell", .digest via)]

/-- The call data `answer` returns for an aim `{cand, method, target, via}` and the answer `y`: the
invoke of `target` at `method` with `proposalData cand via y`, budget 100000, via `via`. -/
def forwardData (cand : ByteArray) (method : Nat) (target via y : ByteArray) : Data :=
  .inj "invoke" (.record [("args", proposalData cand via y), ("budget", .nat 100000), ("method", .nat method),
    ("obj", .digest target), ("via", .inj "some" (.digest via))])

/-- The calls row of an unaimed answer: the one slot empty. -/
def noCalls : Data := .record [("c0", .inj "none" (.record []))]

/-- The calls row of an aimed answer: the one slot holds the forward. -/
def forwardCalls (cand : ByteArray) (method : Nat) (target via y : ByteArray) : Data :=
  .record [("c0", .inj "some" (forwardData cand method target via y))]

end Nanodregg.Lang.Bell
