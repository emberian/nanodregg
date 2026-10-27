/-
# Spec.Sim.Foreign — the inputs of §9's floor and inhabited run (tooling, closure C9)

The check that accepts any head and its trivial system (`acceptingHead`), the cells and receipt
bytes the floor and the inhabited fact hand a receipt check, at the deployed `Ctx`. What is computed
of these is stated in `Spec.Proofs.Foreign`.
-/
import Spec.Sim.Run

namespace Nanodregg.Spec

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Protocol Nanodregg.Codec

/-- The run's transaction id. -/
def wTx : Digest := txIdOf Xd wCall

/-- What the lazy check shows of every receipt: the run's call, committed at height 1. -/
def seenAny : Lang.Seen := ⟨1, oneDigest.bytes, wTx.bytes⟩

/-- **The check that accepts any head**: whatever the cell and the bytes, a committed call. -/
def acceptAll : Lang.ReceiptCheck := fun _ _ => .ok seenAny

/-- **The accepting-head system**: the deployed system whose receipt check is `acceptAll`. -/
def acceptingHead (d : ByteArray → ByteArray) : System Digest := { deployed d with rc := acceptAll }

/-- A cell that is no head object (kind 0). -/
def plainCell : Cell := { kind := 0, discipline := .rom, slots := [] }

/-- Receipt bytes that decode: the genesis World's (absent) receipt for the run's call. -/
def rbAny : ByteArray :=
  (Receipt.bytes Xd.env Codec.Deployed.digestCodec (Receipt.build Xd.env wGenesis wTx)).getD .empty

/-- A head object's cell holding `w`'s head (`Std.headPackage` in its package slot, its state the
`at` head of `w`'s chain, height, roots and steps, and `w`'s origin). Not a cell of any World: the
claim ranges over every cell a check is handed. -/
def headCellOf (w : World Digest) : Cell :=
  { kind := kindObject, discipline := .ram,
    slots := (slotPackage, Xd.env.bytes (Protocol.Foreign.headPackageId Xd.env)) ::
      (Lang.stateSlots (Lang.recordRow Lang.Std.headStateTy)
        [("head", .inj "at" (Lang.Std.atRec w.chain.bytes w.height (w.roots Xd.env).bytes w.steps)),
         ("world", .digest w.origin.bytes)] 0).getD [] }

/-- `w`'s receipt for the run's call, as bytes. -/
def rbOf (w : World Digest) : ByteArray :=
  (Receipt.bytes Xd.env Codec.Deployed.digestCodec (Receipt.build Xd.env w wTx)).getD .empty

end Nanodregg.Spec
