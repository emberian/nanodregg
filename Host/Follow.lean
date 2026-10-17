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

/-- One frame's answer: follow's state after it (its World and any base download in progress),
what to make durable before replying (`Command.Persist`), the reply. Generic in the `Ctx` and the
way a base is read (`Protocol.Thin.Base`), so PROTOCOL's rows drive this very function on their
toy digest. -/
def answer {D : Type} [Ord D] [DecidableEq D] (X : Receive.Ctx D) (B : Protocol.Thin.Base (World D))
    (me : Command.Self D) (fs : Command.Follow D) (f : Frame) :
    Command.Follow D × Command.Persist D × UInt8 × ByteArray :=
  let refused (r : Refusal) := (fs, .turns [], named r.name)
  let stepOut (fs' : Command.Follow D) (p : Command.Persist D) (r : Command.Reply) :=
    match r.bytes with
    | some b => (fs', p, Status.ok.code, b)
    | none => (fs', p, named Refusal.stepTooLarge.name)
  match Protocol.Op.ofCode? f.op with
  | none => refused (.unknownOp f.op)
  | some .command =>
    match commandFrame.decode f.payload with
    | .error _ => refused .undecodableCommand
    | .ok v => stepOut fs (.turns []) (Command.start X me fs (Text.unlist v.1.1))
  | some .resume =>
    match resumeFrame.decode f.payload with
    | .error _ => refused .undecodableResume
    | .ok (k, result, ()) =>
      let (fs', p, r) := Command.step X B me fs k.1 result.1
      stepOut fs' p r
  | some op => refused (.wrongSocket op)

/-- The follower loop: one frame at a time, at most `fuel` frames. `dl` is the base download in
progress, held in memory only (a restart starts it again). Absorbed Turns are appended through
`Host.append` BEFORE the step is answered; an adopted base is sealed as follow's own newest base
at its segment position (no record before it belongs to the adopted World's history, so the index
restarts empty) BEFORE the step is answered. -/
def loop (keys : Keys) (me : Command.Self D) (store : Store) (ck : Checkpoint (World D)) (port : Port) :
    Nat → Option Protocol.Thin.Download → Resident (World D) → IO (Exit × Resident (World D))
  | 0, _, r => finish .fuel r
  | fuel + 1, dl, r => do
    let r ← match ← reap r with
      | .ok r => pure r
      | .error f => return (.sealFailed f, { r with pending := none })
    let some f ← port.recv | finish .eof r
    let (fs', p, status, payload) :=
      answer X ⟨world, World.height, keys.worldDigest, c.worldBytesMax⟩ me ⟨r.world, dl⟩ f
    match p with
    | .turns [] =>
      port.send ⟨f.conn, status, payload⟩
      loop keys me store ck port fuel fs'.download { r with world := fs'.world }
    | .turns ts =>
      match ← append recorder keys.segment ck c store r fs'.world (recorder.encode fs'.world ts.toArray) with
      | .error e =>
        port.send ⟨f.conn, Status.uncertain.code, ByteArray.empty⟩
        finish e r
      | .ok r =>
        port.send ⟨f.conn, status, payload⟩
        loop keys me store ck port fuel fs'.download r
    | .adopt w' =>
      let r ← match r.pending with
        | none => pure r
        | some pd => match ← settle pd with
          | .ok sealed => pure { r with sealed, pending := none }
          | .error e => return (.sealFailed e, { r with pending := none })
      match ← settle (← spawnSeal ck recorder.mark w' r.pos #[]) with
      | .error e =>
        port.send ⟨f.conn, Status.uncertain.code, ByteArray.empty⟩
        return (.sealFailed e, { r with pending := none })
      | .ok sealed =>
        port.send ⟨f.conn, status, payload⟩
        loop keys me store ck port fuel fs'.download
          { r with world := w', sealed, index := #[], pending := none }

end Nanodregg.Host.Follow
