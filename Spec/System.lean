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
settlement of its own call (`settle`), the writer's answer to a frame (`handle`), the receipt check
a law's foreign read runs (`rc`), the check of a receipt against a held head (`receiptCheck`), the writer's reopen after a crash (`reopen`), the exchange package
(`exchange`), the resident's bell check and its act on the rings (`bellAccept`, `ringAct`), its keep of the
kept answer (`keep`), the one-party escrow package (`escrow`). What a field
does not vary (the call codec, the signature check, the Lang program, the hash) is `X`.
-/
import Kernel.Receive.Rederive
import Kernel.Receive.Follow
import Protocol.Command.Machine
import Host.Serve
import Host.Deployed
import Host.Keys
import Host.Open
import Lang.StdOfferEscrow
import Lang.Bell
import Hosting.Resident.Run
import Ledger.Escrow

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
  /-- the check a Lang law's receipt read runs against a held head (`Protocol.Foreign.check`, the
  check `Host.Deployed.X`'s program is built over: `deployed_program_reads`) -/
  rc : Lang.ReceiptCheck
  /-- the check of a receipt against a head a member holds of a World (`Protocol.Receipt.check`:
  the head's height and roots, the call's id and `notBefore`, the receipt), to its answer -/
  receiptCheck : Nat → D → D → Nat → Receipt.Receipt D → Except Receipt.Refusal (Receipt.Answer D)
  /-- the writer's open of its Store after a crash: keys, base file, header, index, segment
  (`Host.openWith` at the deployed instance) -/
  reopen : Host.Keys → ByteArray → ByteArray → ByteArray → ByteArray →
    Except (Host.StoreFault (Host.Record.Fault (Reject D))) (Host.Opening (World D))
  /-- the two-party exchange package the stdlib installs (`Lang.Std.offerEscrowPackageOf`) -/
  exchange : List Lang.Label → List Lang.Label → Nat → Nat → Nat → Nat → Lang.Package
  /-- the resident's check of the configured bell's package (`Lang.Bell.shapeOk`) -/
  bellAccept : Lang.Package → Bool
  /-- the resident's act on the rings a tick read (`Hosting.Resident.actOn`) -/
  ringAct : Hosting.Resident.Where → Hosting.Resident.Shape → Hosting.Resident.Mem →
    List Hosting.Resident.Ring → Hosting.Resident.Prog Hosting.Resident.Tick
  /-- the resident's write of its kept answer, as volume operations (`Hosting.Resident.keepOps`;
  the restart's resume is built from it) -/
  keep : Hosting.Resident.Where → String → List Hosting.Resident.FsOp
  /-- the one-party escrow package LEDGER installs (`Ledger.Escrow.escrow`) -/
  escrow : Lang.Package

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
  rc := Protocol.Foreign.check Codec.Deployed.env Codec.Deployed.digestCodec
  receiptCheck := Receipt.check Host.Deployed.X.env
  reopen := fun keys file H I seg => Id.run (Host.openWith keys Host.Deployed.c Host.Deployed.world
    Host.Deployed.recorder.mark Host.Deployed.originChain Host.Deployed.foldStep file H seg.size I.size
    (Host.segReader I) (Host.segReader seg))
  exchange := Lang.Std.offerEscrowPackageOf
  bellAccept := Lang.Bell.shapeOk
  ringAct := Hosting.Resident.actOn
  keep := Hosting.Resident.keepOps
  escrow := Ledger.Escrow.escrow

/-- The digest a Store pins a World's bytes by: `Host.Keys.ofKey`'s `worldDigest`, which does not
depend on the Store's key (an unkeyed digest under `domBaseDigest`, HOST-15). `deployed storeDigest`
is the system every deployed Store runs. -/
def storeDigest (b : ByteArray) : ByteArray := (Codec.Hash.digest Host.domBaseDigest b).bytes

end Nanodregg.Spec
