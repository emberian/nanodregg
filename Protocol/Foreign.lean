/-
# Protocol.Foreign — a receipt from another World, checked against a head this World holds (E5)

`check E dc` is the deployed `Lang.ReceiptCheck` (`Host.Deployed.X` passes it to `Lang.program`): the
point's cell must be an object of `Std.headPackage` (`Lang.headView`, else `notHead`) holding an
`at` head (a `forked` one checks nothing: `forkedHead`); the receipt's bytes must decode
(`badReceipt`); `Receipt.check` against the head's height and roots must answer `committed`
(`headMismatch` / `pathMismatch` / `forgotten` by the check's own names; `refused` and `absent`
are `notCommitted`: acting on them needs the call's window, which the receipt does not carry).
The column then shows the committed height, turn digest and transaction id.

What it means is `Proofs.Foreign.foreign_receipt_sound`: under the named premise that the held head
is the head of a fold of A from A's genesis (head freshness: B holds A head, not THE head), the
transaction was admitted in that fold at that height, or the hash collides among a listed set.
-/
import Protocol.Receipt
import Lang.StdHead

namespace Nanodregg.Protocol.Foreign

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Codec

variable {D : Type} [Ord D] [DecidableEq D]

/-- `Std.headPackage`'s canonical bytes (empty if it had none, which `headPackage_encodes` refutes). -/
def headPackageBytes : ByteArray := (Lang.Wire.encodePackage Lang.Std.headPackage).getD .empty

/-- The deployed id of `Std.headPackage`: its package cell's content digest (`install`, KERNEL-3). -/
def headPackageId (E : Env D) : D :=
  romIdOf E { kind := kindPackage, discipline := .rom, slots := [(0, headPackageBytes)] }

/-- THE deployed receipt check. -/
def check (E : Env D) (dc : Stream D) : Lang.ReceiptCheck := fun cell rb =>
  let digestOf (b : ByteArray) : Option D := (dc.decode b).toOption
  match Lang.headView digestOf (E.bytes (headPackageId E)) cell with
  | none => .error "notHead"
  | some (.forked _) => .error "forkedHead"
  | some (.at _ height rootsB _) =>
    match digestOf rootsB, Receipt.ofBytes E dc rb with
    | none, _ => .error "notHead"
    | _, none => .error "badReceipt"
    | some roots, some r =>
      match Receipt.check E height roots r.txId 0 r with
      | .ok (.committed h td) => .ok ⟨h, E.bytes td, E.bytes r.txId⟩
      | .ok _ => .error "notCommitted"
      | .error e => .error e.name

end Nanodregg.Protocol.Foreign
