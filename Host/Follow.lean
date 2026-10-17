/-
# Host.Follow — `host follow`: the member's own Store, folded with the audit, driven by steps

    loop, one frame at a time (conn, op, payload) from the supervisor:
      command(argv)      → Command.start on follow's World                     → a step
      resume(k, result)  → Command.step: absorbs any log page it carried, every event re-derived
                           (PROTOCOL-4)                                        → a step
      Turns absorbed     → appended to follow's own segment as one batch record, durably, BEFORE
                           the step is answered (`Host.append`, the writer's own append path)

Follow decides nothing the kernel does not: `Command.step` derives, `Receive.audit` re-derives on
reopen. Its Store is the same format as the writer's (key, segment of batch records, sealed base)
and is opened by the same `openWriter`, with `Deployed.auditStep` as the fold. So a follower that
has audited once reopens from its own newest base plus at most `tailMax` of its own log, not from
genesis (ROOT ruling 10-16). A logged event that does not re-derive is refused by the step
(`eventMismatch`), and a page whose stated chain is not follow's fold by `chainMismatch`. Both are
PROTOCOL's names, carried in the step's `done`.

Refusals before the machine, by name: `undecodableCommand`, `undecodableResume`, `wrongSocket`
(submit, lookup, read, log belong to host.sock), `unknownOp`, `stepTooLarge` (a step with no wire
bytes).
-/
import Host.Deployed
import Protocol.Command.Wire

namespace Nanodregg.Host.Follow

open Nanodregg.Kernel Nanodregg.Codec Nanodregg.Host.Deployed Nanodregg.Protocol

/-- Why follow refuses a frame before the machine sees it (law 7). -/
inductive Refusal where
  | undecodableCommand
  | undecodableResume
  | wrongSocket (op : Protocol.Op)
  | unknownOp (code : UInt8)
  | stepTooLarge
  deriving Repr

def Refusal.name : Refusal → String
  | .undecodableCommand => "undecodableCommand"
  | .undecodableResume => "undecodableResume"
  | .wrongSocket _ => "wrongSocket"
  | .unknownOp _ => "unknownOp"
  | .stepTooLarge => "stepTooLarge"

/-- How many heights a call or envelope follow plans stays valid. -/
def window : Nat := 128

/-- One frame's answer: follow's World after it, the Turns it absorbed, the reply. Generic in the
`Ctx`, so PROTOCOL's rows drive this very function on their toy digest. -/
def answer {D : Type} [Ord D] [DecidableEq D] (X : Receive.Ctx D) (me : Command.Self D) (w : World D)
    (f : Frame) : World D × List (Turn D) × UInt8 × ByteArray :=
  let refused (r : Refusal) := (w, [], named r.name)
  let stepOut (w' : World D) (ts : List (Turn D)) (r : Command.Reply) :=
    match r.bytes with
    | some b => (w', ts, Status.ok.code, b)
    | none => (w', ts, named Refusal.stepTooLarge.name)
  match Protocol.Op.ofCode? f.op with
  | none => refused (.unknownOp f.op)
  | some .command =>
    match commandFrame.decode f.payload with
    | .error _ => refused .undecodableCommand
    | .ok v => stepOut w [] (Command.start X me w (Text.unlist v.1.1))
  | some .resume =>
    match resumeFrame.decode f.payload with
    | .error _ => refused .undecodableResume
    | .ok (k, result, ()) =>
      let (w', ts, r) := Command.step X me w k.1 result.1
      stepOut w' ts r
  | some op => refused (.wrongSocket op)

/-- The follower loop: one frame at a time, at most `fuel` frames. -/
def loop (keys : Keys) (me : Command.Self D) (store : Store) (ck : Checkpoint (World D)) (port : Port) :
    Nat → Resident (World D) → IO (Exit × Resident (World D))
  | 0, r => finish .fuel r
  | fuel + 1, r => do
    let r ← match ← reap r with
      | .ok r => pure r
      | .error f => return (.sealFailed f, { r with pending := none })
    let some f ← port.recv | finish .eof r
    let (w', ts, status, payload) := answer X me r.world f
    if ts.isEmpty then
      port.send ⟨f.conn, status, payload⟩
      loop keys me store ck port fuel { r with world := w' }
    else
      match ← append recorder keys.segment ck c store r w' (recorder.encode w' ts.toArray) with
      | .error e =>
        port.send ⟨f.conn, Status.uncertain.code, ByteArray.empty⟩
        finish e r
      | .ok r =>
        port.send ⟨f.conn, status, payload⟩
        loop keys me store ck port fuel r

end Nanodregg.Host.Follow
