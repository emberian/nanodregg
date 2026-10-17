/-
# Host.Serve — the writer's dispatch over PROTOCOL's table: what `host serve` answers

The `Machine` the loop runs, for one `Kernel.Receive.Ctx`. The Host decides nothing: every verdict
is the kernel's or the receive layer's.

* `submit` — decode the signed call (`Ctx.decodeCall`); a txId already journaled answers `ok` with
  the original receipt and derives nothing (KERNEL-7); otherwise `Receive.receive` derives the Turn
  and the loop admits it with `World.admit`. This is `Receive.submit` cut at the point where the loop
  batches (`Host.Proofs.Serve.admitBatch_submit`).
* `lookup` — the same call bytes: `ok` with the receipt if journaled; otherwise `refused expired`
  when the call's signed window ended at or before this World's height (final: it can never be
  admitted, `Host.Proofs.Serve.lookup_expired_final` over KERNEL's `absent_final`), else `absent`
  (it may still land: HOST-8).
* `log` — PROTOCOL's read envelope (`Envelope.check`: a live member, its current key, the signature,
  a follow grant live to a root, then `validUntil`; refused by `ReadRefusal.payload`, which for
  `expired` states the World's height, PROTOCOL-19) against the World as the batch has advanced it, so
  a revocation earlier in the batch applies; then a page of the durable log from `start`, built
  after the batch's sync (`Host.Page`);
* `read` — the same envelope, then a page of the newest base's World bytes from byte `start`
  (`readReplyLayout`: height, total, digest, chain, bytes; HOST-15);
  `command`, `resume` belong to `follow.sock` and are refused `wrongSocket`.

A receipt is `u64 height ‖ turn digest`. A refusal's payload is its NAME as UTF-8, from its owner's
total `name` (`Receive.Refusal.name`, `Reject.name`, `FrameRefusal.name`): never a parse failure
posing as a verdict, never a derived `Repr` (law 7, ROOT ruling 2026-10-16).
-/
import Host.Batch
import Host.Wire
import Kernel.Receive.Submit
import Protocol.Table
import Protocol.Envelope

namespace Nanodregg.Host

open Nanodregg.Kernel Nanodregg.Kernel.Receive

variable {D : Type} [Ord D] [DecidableEq D]

/-- Why the writer refuses a frame before any kernel decision. -/
inductive FrameRefusal where
  | unknownOp (code : UInt8)
  | undecodableCall
  | notServed (op : Protocol.Op)
  | wrongSocket (op : Protocol.Op)
  /-- the resident stopped before this frame reached a batch: nothing of it was admitted, and
  resending it to the restarted Host is safe -/
  | stopped
  /-- `lookup`: the call is not journaled and its window ended at or before this World's height,
  so no admission of it can ever happen (`lookup_expired_final`); `absent` would leave the caller
  waiting on a call that is dead -/
  | expired
  /-- a hang-up (PROTOCOL-23) whose payload names no `CloseReason`: the supervisor is broken -/
  | badHangup
  deriving Repr

/-- The refusal's name on the wire. -/
def FrameRefusal.name : FrameRefusal → String
  | .unknownOp _ => "unknownOp"
  | .undecodableCall => "undecodableCall"
  | .notServed _ => "notServed"
  | .wrongSocket _ => "wrongSocket"
  | .stopped => "stopped"
  | .expired => "expired"
  | .badHangup => "badHangup"

/-- A `refused` reply carrying a refusal's name. -/
def named (name : String) : UInt8 × ByteArray :=
  (Protocol.Status.refused.code, name.toUTF8)

def receipt (X : Ctx D) (height : Nat) (d : D) : ByteArray :=
  Codec.Stream.u64.bytes (UInt64.ofNat height) ++ X.env.bytes d

/-- A hang-up frame's one reply (PROTOCOL-23): the supervisor ended connection `f.conn`; the child
acknowledges it by name, `closed ‖ the same reason` (`Protocol.ack`), and changes nothing else.
`none`: `f` is not a hang-up. Every child of a supervisor answers hang-ups with this function. -/
def hangUpAnswer (f : Frame) : Option (UInt8 × ByteArray) :=
  match Protocol.childKindOf? f.op with
  | some .hangup =>
    some (match Protocol.CloseReason.ofBytes? f.payload with
      | some r => (Protocol.Status.closed.code, r.name.toUTF8)
      | none => named FrameRefusal.badHangup.name)
  | _ => none

/-- A frame's answer from the World as the batch has advanced it. -/
def handle (X : Ctx D) (w : World D) (f : Frame) : Answer (World D) (Turn D) :=
  let refuse := fun (p : UInt8 × ByteArray) => Answer.reply p.1 p.2
  match Protocol.Op.ofCode? f.op with
  | none =>
    match hangUpAnswer f with
    | some p => refuse p
    | none => refuse (named (FrameRefusal.unknownOp f.op).name)
  | some .submit =>
    match X.decodeCall f.payload with
    | none => refuse (named FrameRefusal.undecodableCall.name)
    | some c =>
      match w.journal[txIdOf X c]? with
      | some (h, d) => .reply Protocol.Status.ok.code (receipt X h d)
      | none =>
        match receive X w c with
        | .error r => refuse (named r.name)
        | .ok t => .admit t fun w' => receipt X w'.height (turnDigest X.env t)
  | some .lookup =>
    match X.decodeCall f.payload with
    | none => refuse (named FrameRefusal.undecodableCall.name)
    | some c =>
      match w.journal[txIdOf X c]? with
      | some (h, d) => .reply Protocol.Status.ok.code (receipt X h d)
      | none =>
        if c.unsigned.validUntil ≤ w.height then refuse (named FrameRefusal.expired.name)
        else .reply Protocol.Status.absent.code ByteArray.empty
  | some .read =>
    match Protocol.Envelope.ofBytes X f.payload with
    | none => refuse (named Protocol.ReadRefusal.badEnvelope.name)
    | some e =>
      match Protocol.Envelope.check X w e with
      | .error r => .reply Protocol.Status.refused.code r.payload
      | .ok () => .defer (.read e.start)
  | some .log =>
    match Protocol.Envelope.ofBytes X f.payload with
    | none => refuse (named Protocol.ReadRefusal.badEnvelope.name)
    | some e =>
      match Protocol.Envelope.check X w e with
      | .error r => .reply Protocol.Status.refused.code r.payload
      | .ok () => .defer (.log e.start)
  | some .command => refuse (named (FrameRefusal.wrongSocket .command).name)
  | some .resume => refuse (named (FrameRefusal.wrongSocket .resume).name)

/-- A Turn the kernel rejects at admission. `replayed` here means an identical call earlier in the
same batch was staged: answer with its receipt, as for any journaled call. -/
def onReject (X : Ctx D) (w : World D) (t : Turn D) (r : Reject D) : UInt8 × ByteArray :=
  match r with
  | .replayed _ =>
    match w.journal[t.txId]? with
    | some (h, d) => (Protocol.Status.ok.code, receipt X h d)
    | none => named r.name
  | _ => named r.name

/-- The writer's machine. -/
def machine (X : Ctx D) : Machine (World D) (Turn D) (Reject D) Frame D where
  admit := World.admit X.env
  note := World.root X.env
  handle := handle X
  refuse := onReject X
  ok := Protocol.Status.ok.code

end Nanodregg.Host
