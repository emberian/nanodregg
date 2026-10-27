/-
# Spec.Sim.Durable — the amnesiac open and the Store the §5 floor and inhabited fact read

Tooling (a `Sim` module, closure C9: no deployed module imports it). `amnesiac d` is `deployed d`
with its writer's open replaced by one that forgets the segment; `dKeys`/`dImg`/`dRecord`/`dSeg` are
a deployed Store holding the run's genesis World and one appended record (the founder's rotate,
`Spec.Sim.Run.wCall`, as the writer stages it). What is computed of them is `Spec.Proofs.Durable`'s
`run_reopen`.
-/
import Spec.Sim.Run

namespace Nanodregg.Spec

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Protocol Nanodregg.Codec

/-- **The amnesiac open**: it reads and checks the Store as the deployed open does, then returns
the base's World at the base's position, whatever the segment holds past it. -/
def amnesiacOpen (keys : Host.Keys) (file H I seg : ByteArray) :
    Except (Host.StoreFault (Host.Record.Fault (Reject Digest))) (Host.Opening (World Digest)) :=
  match Id.run (Host.openWith keys Host.Deployed.c Host.Deployed.world Host.Deployed.recorder.mark
      Host.Deployed.originChain Host.Deployed.foldStep file H seg.size I.size (Host.segReader I)
      (Host.segReader seg)) with
  | .error e => .error e
  | .ok o =>
    match Host.Base.read keys Host.Deployed.c Host.Deployed.world file with
    | .error e => .error (.base e)
    | .ok (b, _, _) =>
      .ok { o with opened := ⟨b.world, 0, 0, b.tag.bytes, 0⟩, pos := ⟨b.offset, b.tag⟩, index := #[] }

/-- **The amnesiac writer**: the deployed system whose reopen forgets the segment. -/
def amnesiac (d : ByteArray → ByteArray) : System Digest := { deployed d with reopen := amnesiacOpen }

/-- A Store key's keys, under the deployed shape stamp. -/
def dKeys : Host.Keys := Host.Keys.ofKey oneDigest Host.Deployed.shapes

/-- What deployed genesis writes for the run's genesis World. -/
def dImg : Host.Image :=
  match Host.genesisImage dKeys Host.Deployed.c Host.Deployed.world Host.Deployed.recorder.mark wGenesis with
  | .ok i => i
  | .error _ => ⟨.empty, .empty, .empty, .empty, .empty⟩

/-- The record the writer appends for the run's rotate: the staged Turn with the roots after it. -/
def dRecord : ByteArray :=
  (Host.Record.codec Codec.Deployed.digestCodec).bytes
    (match submit Xd wGenesis wCall with
     | .ok (t, w) => [(.turn t, World.roots Xd.env w)]
     | .error _ => [])

/-- The segment after that append: genesis's origin frame, then the record's frame, chained from
the origin frame's tag (its last 32 bytes). -/
def dSeg : ByteArray :=
  dImg.segment ++ Host.Log.frame dKeys.segment
    (dImg.segment.extract (dImg.segment.size - Host.Log.tagBytes) dImg.segment.size) dRecord

end Nanodregg.Spec
