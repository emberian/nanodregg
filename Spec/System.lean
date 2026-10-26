/-
# Spec.System — the deployed entry points, as one record

The top-level claims (`Spec.Proofs.Claims`) are predicates on a `System`: every component a claim
ranges over is a field, so a trivial system (one component replaced by what a lazy implementation
would do) can be plugged in, and the claim's floor is a theorem that it refuses that system
(`Spec.Proofs.Floor`). `deployed` fills every field with the definition the binaries run.

The fields are the decisions, not their callers: the kernel's derivation of a signed call
(`receive`), its re-judge of a logged refusal (`recordedBy`), the admission of a Turn and the
record of a refusal (`admit`, `refuse`), the writer's verdict on a submitted call (`submit`),
one frame of the member's command machine (`follow`, run by `host follow`), the member's
settlement of its own call (`settle`), and the writer's answer to a frame (`handle`). What a field
does not vary (the call codec, the signature check, the Lang program, the hash) is `X`.
-/
import Kernel.Receive.Rederive
import Kernel.Receive.Follow
import Protocol.Command.Machine
import Host.Serve
import Host.Deployed

namespace Nanodregg.Spec

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Protocol Nanodregg.Codec

structure System (D : Type) [Ord D] [DecidableEq D] where
  /-- the context every field reads through: encodings, hash, call codec, `verify`, the program -/
  X : Ctx D
  /-- the digest codec a receipt is written in -/
  dc : Codec.Stream D
  /-- how follow reads an adopted base: its World codec, step count, pin digest, size bound -/
  B : Thin.Base (World D)
  /-- the kernel's derivation of a signed call into a Turn (`Receive.receive`) -/
  receive : World D → Call D → Except (Refusal D) (Turn D)
  /-- the kernel's re-judge of a logged refusal (`Receive.recordedBy`) -/
  recordedBy : World D → Call D → Refused D → Outcome D
  /-- admission of a Turn (`World.admit`) -/
  admit : World D → Turn D → Except (Reject D) (World D)
  /-- the record of a refusal (`World.refuse`) -/
  refuse : World D → Refused D → Except (Reject D) (World D)
  /-- the writer's verdict on a submitted call (`Receive.submit`) -/
  submit : World D → Call D → Except (Verdict D) (Turn D × World D)
  /-- one frame of the member's command machine (`Command.step`, what `host follow` answers) -/
  follow : Command.Self D → Command.Follow D → ByteArray → ByteArray →
    Command.Follow D × Command.Persist D × Command.Reply
  /-- the member's settlement of its own call on its own World (`Command.settleOf`) -/
  settle : Command.Self D → World D → Call D → Settle.Verdict D
  /-- the writer's answer to a frame on its World (`Host.handle`) -/
  handle : World D → Host.Frame → Host.Answer (World D) (Step D)

variable {D : Type} [Ord D] [DecidableEq D]

namespace System

/-- One step of a log under the system's kernel (`World.step`'s shape). -/
def step (S : System D) (w : World D) : Step D → Except (Reject D) (World D)
  | .turn t => S.admit w t
  | .refusal r => S.refuse w r

/-- A log under the system's kernel (`World.fold`'s shape): the World it reaches, or the index of
the first step refused. -/
def fold (S : System D) (w : World D) : List (Step D) → Except (Nat × Reject D) (World D)
  | [] => .ok w
  | s :: rest =>
      match S.step w s with
      | .ok w' =>
          match S.fold w' rest with
          | .ok w'' => .ok w''
          | .error (i, r) => .error (i + 1, r)
      | .error r => .error (0, r)

end System

/-- The system the binaries run, over the deployed `Ctx` (`Host.Deployed.X`). `worldDigest` is the
Store's pin digest (`Keys.worldDigest`), which `host follow` reads from its Store's keys; the base
`host follow` hands the command machine is exactly this one (`Host/Follow.lean`, `answer`'s call). -/
def deployed (worldDigest : ByteArray → ByteArray) : System Digest where
  X := Host.Deployed.X
  dc := Codec.Deployed.digestCodec
  B := ⟨Host.Deployed.world, World.steps, worldDigest, Host.Deployed.c.worldBytesMax⟩
  receive := receive Host.Deployed.X
  recordedBy := recordedBy Host.Deployed.X
  admit := World.admit Host.Deployed.X.env
  refuse := World.refuse Host.Deployed.X.env
  submit := submit Host.Deployed.X
  follow := Command.step Host.Deployed.X Codec.Deployed.digestCodec
    ⟨Host.Deployed.world, World.steps, worldDigest, Host.Deployed.c.worldBytesMax⟩
  settle := Command.settleOf Host.Deployed.X
  handle := Host.handle Host.Deployed.X

end Nanodregg.Spec
