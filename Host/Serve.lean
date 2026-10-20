/-
# Host.Serve — the writer's dispatch over PROTOCOL's table: what `host serve` answers

The `Machine` the loop runs, for one `Kernel.Receive.Ctx`. The Host decides nothing: every verdict
is the kernel's or the receive layer's.

* `submit` — decode the signed call (`Ctx.decodeCall`; an undecodable frame is `declined`: nothing
  authenticated it, PROTOCOL-41); a txId already journaled answers `ok` with the original receipt and
  derives nothing (KERNEL-7); otherwise the Host judges the call ONCE with `Receive.judge`
  (KERNEL-44, KERNEL-47) and commits exactly what it returns: `admitted` commits the Turn (`ok`, the
  receipt), `recorded` commits the refusal as a step of the log (`refused NAME`, final within the
  window: `judge_recorded_final`), `declined` commits nothing. The status of every refused reply is
  PROTOCOL's one rule, `Protocol.Settle.verdictReply` (`refused` when final, `declined` when not).
  The Host's step is `Receive.judge`'s (`Host.Proofs.Serve.step_submit`).
* `lookup` — the same call bytes: `ok` with the receipt if journaled; `refused NAME` if its
  transaction id holds a recorded refusal (the name of its recorded code, `Receive.codeName`:
  `Kernel.refused_answers`); otherwise, once the journal may have pruned the call's entry
  (`Kernel.journalForgets`: `notBefore + 2 * windowMax ≤ height`, KERNEL-33), `uncertain` with
  payload `forgotten` (no longer answerable: the outcome is in the log, never `refused`, never
  `absent`); otherwise `refused expired` when the call's signed window ended at or before this
  World's height (never committed, `Kernel.fold_answers`, and final: it can never be admitted,
  `Host.Proofs.Serve.lookup_expired_final` over KERNEL's `absent_final`), else `absent` (it may
  still land: HOST-8). A `submit` of an un-journaled, unrecorded call past `journalForgets` answers
  the same `uncertain forgotten`: the kernel would refuse it by its window
  (`Receive.submit_forgotten`), which for a call committed long ago would be a false `refused`.
* `log` — PROTOCOL's read envelope (`Envelope.check`: a live member, its current key, the signature,
  a follow grant live to a root, then `validUntil`; refused by `ReadRefusal.payload`, which for
  `expired` states the World's height, PROTOCOL-19) against the World as the batch has advanced it, so
  a revocation earlier in the batch applies; then a page of the durable log from `start`, built
  after the batch's sync (`Host.Page`);
* `read` — the same envelope, then a page of the newest base's World bytes from byte `start`
  (`readReplyLayout`: height, total, digest, chain, bytes; HOST-15);
* `cancel` — a member's cancel of its own signed call (KERNEL-60's C1, HOST-66): the payload is
  `Protocol.cancelEvent sig call`, the very bytes of page event tag 2, read by
  `Protocol.cancelParts` (a first byte other than `eventCancel`, or parts that do not read,
  are declined `undecodableCall`: one encoding per cancel, on the wire as in the log); a call already
  journaled answers `ok` with its receipt (a cancel never undoes an admitted call); past
  `journalForgets` an unrecorded call answers `uncertain forgotten`, as `submit` does; otherwise the
  Host decides ONCE with `Receive.cancel` and commits exactly what it returns: `recorded` commits the
  cancel record (`refused cancelled`, final; it reaches followers as event tag 2), `declined`
  commits nothing. `Host.Proofs.Serve.step_cancel`.
  `command`, `resume` belong to `follow.sock` and are refused `wrongSocket`.

A receipt is `u64 height ‖ turn digest`. A refusal's payload is its NAME as UTF-8, from its owner's
total `name` (`Receive.Refusal.name`, `Reject.name`, `FrameRefusal.name`): never a parse failure
posing as a verdict, never a derived `Repr` (law 7, ROOT ruling 2026-10-16).
-/
import Host.Batch
import Host.Wire
import Kernel.Receive.Submit
import Protocol.Settle
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

/-- A `declined` reply (PROTOCOL-41): refused by name, NOT final, nothing recorded. -/
def declined (name : String) : UInt8 × ByteArray :=
  (Protocol.Status.declined.code, name.toUTF8)

/-- The name a recorded refusal's code answers with (`Receive.codeName`); a code with no name is
never recorded (`Kernel.codeName_code`), and would answer `refusedFinal`. -/
def recordedName (code : Nat) : String :=
  (codeName code).getD "refusedFinal"

/-- The reply to a submit that `Receive.judge` did not admit: PROTOCOL's status rule. -/
def settled (X : Ctx D) (w : World D) (c : Call D) (o : Outcome D) : UInt8 × ByteArray :=
  match Protocol.Settle.verdictReply X w c o with
  | some (st, name) => (st.code, name.toUTF8)
  | none => named "admitted"

/-- The answer for an un-journaled call past `Kernel.journalForgets` (KERNEL-33): `uncertain`, so
the client resolves it from the log and never resubmits or concludes `refused`. -/
def forgotten : UInt8 × ByteArray :=
  (Protocol.Status.uncertain.code, "forgotten".toUTF8)

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
def handle (X : Ctx D) (w : World D) (f : Frame) : Answer (World D) (Step D) :=
  let refuse := fun (p : UInt8 × ByteArray) => Answer.reply p.1 p.2
  match Protocol.Op.ofCode? f.op with
  | none =>
    match hangUpAnswer f with
    | some p => refuse p
    | none => refuse (named (FrameRefusal.unknownOp f.op).name)
  | some .submit =>
    match X.decodeCall f.payload with
    | none => refuse (declined FrameRefusal.undecodableCall.name)
    | some c =>
      match w.journalAt X.env (txIdOf X c) with
      | some (h, d) => .reply Protocol.Status.ok.code (receipt X h d)
      | none =>
        if (refusedAnswer X w c).isNone && journalForgets w.height c.unsigned.notBefore then refuse forgotten else
        match judge X w c with
        | .admitted t w' => .commit (.turn t) w' Protocol.Status.ok.code (receipt X w'.height (turnDigest X.env t))
        | .recorded v r w' =>
          let (st, p) := settled X w c (.recorded v r w')
          .commit (.refusal r) w' st p
        | .declined v => refuse (settled X w c (.declined v))
  | some .lookup =>
    match X.decodeCall f.payload with
    | none => refuse (named FrameRefusal.undecodableCall.name)
    | some c =>
      match w.journalAt X.env (txIdOf X c) with
      | some (h, d) => .reply Protocol.Status.ok.code (receipt X h d)
      | none =>
        match refusedAnswer X w c with
        | some code => refuse (named (recordedName code))
        | none =>
        if journalForgets w.height c.unsigned.notBefore then refuse forgotten
        else if c.unsigned.validUntil ≤ w.height then refuse (named FrameRefusal.expired.name)
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
  | some .cancel =>
    match (if f.payload[0]? = some Protocol.eventCancel then Protocol.cancelParts f.payload else none) with
    | none => refuse (declined FrameRefusal.undecodableCall.name)
    | some (sig, cb) =>
      match X.decodeCall cb with
      | none => refuse (declined FrameRefusal.undecodableCall.name)
      | some c =>
        match w.journalAt X.env (txIdOf X c) with
        | some (h, d) => .reply Protocol.Status.ok.code (receipt X h d)
        | none =>
          if (refusedAnswer X w c).isNone && journalForgets w.height c.unsigned.notBefore then refuse forgotten else
          match cancel X w c sig with
          | .recorded v r w' =>
            let (st, p) := settled X w c (.recorded v r w')
            .commit (.refusal r) w' st p
          | o => refuse (settled X w c o)
  | some .command => refuse (named (FrameRefusal.wrongSocket .command).name)
  | some .resume => refuse (named (FrameRefusal.wrongSocket .resume).name)

/-- The writer's machine: every step it commits is `World.step`'s (`Host.Proofs.Serve.machine_commits`). -/
def machine (X : Ctx D) : Machine (World D) (Step D) Frame D where
  note := World.roots X.env
  handle := handle X
  ok := Protocol.Status.ok.code

end Nanodregg.Host
