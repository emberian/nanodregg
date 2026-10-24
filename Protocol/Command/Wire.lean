/-
# Protocol.Command.Wire — a follow step on follow.sock

`Reply.bytes` is what `host follow` writes for a step (`Step.frame` over Protocol.Table's layouts);
`Reply.ofBytes` is the client's reading of it, and the only one (CLIENT-10's generated reader is
the same layout). A reply with a field past `Bounds.frameBytesMax`, or fields past it together, or a `host` step whose op is not
relayable (`Op.relayable`: never `submit`, which goes only through the attempt store), has no
bytes: `none`. Round trip: `Protocol.Proofs.Wire.ofBytes_bytes`.
-/
import Protocol.Command.Machine
import Protocol.Frames

namespace Nanodregg.Protocol.Command

open Nanodregg.Codec

/-- The `op` field of a `host` step: a relayable op's code, or nothing. -/
def relayCode (op : Op) :
    Option { b : UInt8 // ((Op.relayable.map fun o => (o.name, o.code)).map Prod.snd).toArray.contains b = true } :=
  if h : ((Op.relayable.map fun o => (o.name, o.code)).map Prod.snd).toArray.contains op.code = true
  then some ⟨op.code, h⟩ else none

def Reply.frame : Reply → Option Step.Frame
  | .done e o r => do pure ⟨.done, (e, ← Text.fit _ o, ← Text.fit _ r, ())⟩
  | .sign m k => do pure ⟨.sign, (← Text.fit _ m, ← Text.fit _ k, ())⟩
  | .host op p k => do pure ⟨.host, (← relayCode op, ← Text.fit _ p, ← Text.fit _ k, ())⟩
  | .submit c k => do pure ⟨.submit, (← Text.fit _ c, ← Text.fit _ k, ())⟩
  | .precommit k => do pure ⟨.precommit, (← Text.fit _ k, ())⟩
  | .signNext m k => do pure ⟨.signNext, (← Text.fit _ m, ← Text.fit _ k, ())⟩
  | .signIncoming m k => do pure ⟨.signIncoming, (← Text.fit _ m, ← Text.fit _ k, ())⟩

def Reply.ofFrame : Step.Frame → Option Reply
  | ⟨.done, (e, o, r, ())⟩ => some (.done e o.1 r.1)
  | ⟨.sign, (m, k, ())⟩ => some (.sign m.1 k.1)
  | ⟨.host, (c, p, k, ())⟩ => (Op.ofCode? c.1).map fun op => .host op p.1 k.1
  | ⟨.submit, (c, k, ())⟩ => some (.submit c.1 k.1)
  | ⟨.precommit, (k, ())⟩ => some (.precommit k.1)
  | ⟨.signNext, (m, k, ())⟩ => some (.signNext m.1 k.1)
  | ⟨.signIncoming, (m, k, ())⟩ => some (.signIncoming m.1 k.1)

/-- The step's bytes, when they fit ONE frame as a whole (`bodyFits`: the status byte and every
field together, PROTOCOL-70); a reply whose fields each fit but whose sum does not has none, and
`host follow` refuses the step `stepTooLarge` by name instead of writing a frame the client's
transport refuses. -/
def Reply.bytes (r : Reply) : Option ByteArray :=
  r.frame.bind fun f => let b := Step.frame.bytes f; if bodyFits b then some b else none

def Reply.ofBytes (b : ByteArray) : Option Reply :=
  match Step.frame.decode b with
  | .ok f => Reply.ofFrame f
  | .error _ => none

end Nanodregg.Protocol.Command
