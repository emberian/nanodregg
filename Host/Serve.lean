/-
# Host.Serve — the writer's dispatch over PROTOCOL's table: what `host serve` answers

The `Machine` the loop runs, for one `Kernel.Receive.Ctx`. The Host decides nothing: every verdict
is the kernel's or the receive layer's.

* `submit` — decode the signed call (`Ctx.decodeCall`); a txId already journaled answers `ok` with
  the original receipt and derives nothing (KERNEL-7); otherwise `Receive.receive` derives the Turn
  and the loop admits it with `World.admit`. This is `Receive.submit` cut at the point where the loop
  batches (`Host.Proofs.Serve.admitBatch_submit`).
* `lookup` — the same call bytes: `ok` with the receipt if journaled, `absent` otherwise (HOST-8).
* `log` — PROTOCOL's read envelope (`Envelope.check`: a live member, its current key, the signature,
  `validUntil`, a follow grant live to a root) against the World as the batch has advanced it, so
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
  deriving Repr

/-- The refusal's name on the wire. -/
def FrameRefusal.name : FrameRefusal → String
  | .unknownOp _ => "unknownOp"
  | .undecodableCall => "undecodableCall"
  | .notServed _ => "notServed"
  | .wrongSocket _ => "wrongSocket"
  | .stopped => "stopped"

/-- A `refused` reply carrying a refusal's name. -/
def named (name : String) : UInt8 × ByteArray :=
  (Protocol.Status.refused.code, name.toUTF8)

def receipt (X : Ctx D) (height : Nat) (d : D) : ByteArray :=
  Codec.Stream.u64.bytes (UInt64.ofNat height) ++ X.env.bytes d

/-- A frame's answer from the World as the batch has advanced it. -/
def handle (X : Ctx D) (w : World D) (f : Frame) : Answer (World D) (Turn D) :=
  let refuse := fun (p : UInt8 × ByteArray) => Answer.reply p.1 p.2
  match Protocol.Op.ofCode? f.op with
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
      | none => .reply Protocol.Status.absent.code ByteArray.empty
  | some .read =>
    match Protocol.Envelope.ofBytes X f.payload with
    | none => refuse (named Protocol.ReadRefusal.badEnvelope.name)
    | some e =>
      match Protocol.Envelope.check X w e with
      | .error r => refuse (named r.name)
      | .ok () => .defer (.read e.start)
  | some .log =>
    match Protocol.Envelope.ofBytes X f.payload with
    | none => refuse (named Protocol.ReadRefusal.badEnvelope.name)
    | some e =>
      match Protocol.Envelope.check X w e with
      | .error r => refuse (named r.name)
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
def machine (X : Ctx D) : Machine (World D) (Turn D) (Reject D) Frame where
  admit := World.admit X.env
  handle := handle X
  refuse := onReject X
  ok := Protocol.Status.ok.code

end Nanodregg.Host
