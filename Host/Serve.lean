/-
# Host.Serve — the writer's dispatch over PROTOCOL's table: what `host serve` answers

The `Machine` the loop runs, for one `Kernel.Receive.Ctx`. The Host decides nothing: every verdict
is the kernel's or the receive layer's.

* `submit` — decode the signed call (`Ctx.decodeCall`); a txId already journaled answers `ok` with
  the original receipt and derives nothing (KERNEL-7); otherwise `Receive.receive` derives the Turn
  and the loop admits it with `World.admit`. This is `Receive.submit` cut at the point where the loop
  batches (`Host.Proofs.Serve.admitBatch_submit`).
* `lookup` — the same call bytes: `ok` with the receipt if journaled, `absent` otherwise (HOST-8).
* `read`, `log` — refused `notServed` by name until the signed read envelope exists (HOST-11);
  `command`, `resume` belong to `follow.sock` and are refused `wrongSocket`.

A receipt is `u64 height ‖ turn digest`. A refusal's payload is its constructor rendered as UTF-8
(`repr`): a name, never a parse failure posing as a verdict (law 7); CODEC's refusal codec replaces
the rendering when it exists.
-/
import Host.Batch
import Host.Wire
import Kernel.Receive.Submit
import Protocol.Table

namespace Nanodregg.Host

open Nanodregg.Kernel Nanodregg.Kernel.Receive

variable {D : Type} [Ord D] [DecidableEq D] [Repr D]

/-- Why the writer refuses a frame before any kernel decision. -/
inductive FrameRefusal where
  | unknownOp (code : UInt8)
  | undecodableCall
  | notServed (op : Protocol.Op)
  | wrongSocket (op : Protocol.Op)
  deriving Repr

def named {α : Type} [Repr α] (a : α) : UInt8 × ByteArray :=
  (Protocol.Status.refused.code, (toString (repr a)).toUTF8)

def receipt (X : Ctx D) (height : Nat) (d : D) : ByteArray :=
  Codec.Stream.u64.bytes (UInt64.ofNat height) ++ X.env.bytes d

/-- A frame's answer from the World as the batch has advanced it. -/
def handle (X : Ctx D) (w : World D) (f : Frame) : Answer (World D) (Turn D) :=
  let refuse := fun (p : UInt8 × ByteArray) => Answer.reply p.1 p.2
  match Protocol.Op.ofCode? f.op with
  | none => refuse (named (FrameRefusal.unknownOp f.op))
  | some .submit =>
    match X.decodeCall f.payload with
    | none => refuse (named FrameRefusal.undecodableCall)
    | some c =>
      match w.journal[txIdOf X c]? with
      | some (h, d) => .reply Protocol.Status.ok.code (receipt X h d)
      | none =>
        match receive X w c with
        | .error r => refuse (named r)
        | .ok t => .admit t fun w' => receipt X w'.height (turnDigest X.env t)
  | some .lookup =>
    match X.decodeCall f.payload with
    | none => refuse (named FrameRefusal.undecodableCall)
    | some c =>
      match w.journal[txIdOf X c]? with
      | some (h, d) => .reply Protocol.Status.ok.code (receipt X h d)
      | none => .reply Protocol.Status.absent.code ByteArray.empty
  | some .read => refuse (named (FrameRefusal.notServed .read))
  | some .log => refuse (named (FrameRefusal.notServed .log))
  | some .command => refuse (named (FrameRefusal.wrongSocket .command))
  | some .resume => refuse (named (FrameRefusal.wrongSocket .resume))

/-- A Turn the kernel rejects at admission. `replayed` here means an identical call earlier in the
same batch was staged: answer with its receipt, as for any journaled call. -/
def onReject (X : Ctx D) (w : World D) (t : Turn D) (r : Reject D) : UInt8 × ByteArray :=
  match r with
  | .replayed _ =>
    match w.journal[t.txId]? with
    | some (h, d) => (Protocol.Status.ok.code, receipt X h d)
    | none => named r
  | _ => named r

/-- The writer's machine. -/
def machine (X : Ctx D) : Machine (World D) (Turn D) (Reject D) Frame where
  admit := World.admit X.env
  handle := handle X
  refuse := onReject X
  ok := Protocol.Status.ok.code

end Nanodregg.Host
