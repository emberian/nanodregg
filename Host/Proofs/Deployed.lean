/-
# Host.Proofs.Deployed — the deployed instance meets the premises of the generic open theorems

* `originChain_genesis` / `genesis_origin_passes` (HOST-25) — for every World `host genesis` makes
  (`Receive.genesisWorld`, what `Receive.genesis` returns: `genesis_ok`), the deployed `originChain` is the chain `recorder.mark` writes into the origin
  frame (KERNEL's `genesis_chain`), and the deployed genesis image passes the origin check;
* `indexEntries_pages` (HOST-31) — the generic index round trip with its one premise
  (`worldBytesMax < 2^32`) discharged at the deployed cadence;
* `foldStep_originChain` (HOST-25) — a record the deployed reopen folds keeps `originChain`
  (`Record.step_origin`, from KERNEL's `fold_origin`), so every later base's World states the chain
  the origin frame holds.
-/
import Host.Deployed
import Host.Proofs.Base
import Host.Proofs.Carry
import Codec.Proofs.Deployed

namespace Nanodregg.Host.Deployed

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Codec

theorem originChain_genesis (name nonce : ByteArray) (allowance : Nat) (founders : List (ByteArray × D)) :
    originChain (Receive.genesisWorld X name nonce allowance founders) =
      (recorder.mark (Receive.genesisWorld X name nonce allowance founders)).2 := by
  simp only [originChain, recorder, Receive.genesis_chain]

theorem genesis_origin_passes {F : Type} (keys : Keys) (name nonce : ByteArray) (allowance : Nat)
    (founders : List (ByteArray × D)) {img : Image}
    (h : genesisImage keys c world recorder.mark (Receive.genesisWorld X name nonce allowance founders) = .ok img) :
    originFault (F := F) keys.segment (img.segment.extract 0 (originLen img.segment.size))
      (originChain (Receive.genesisWorld X name nonce allowance founders)) = none :=
  genesisImage_origin keys c world recorder.mark originChain _ h
    (by show (Receive.genesisWorld X name nonce allowance founders).chain.bytes.size ≤ chainBytesMax
        rw [Digest.size_eq]; decide)
    (originChain_genesis name nonce allowance founders)

theorem foldStep_originChain {w w' : World D} {r : ByteArray} (h : foldStep w r = .ok w') :
    originChain w' = originChain w := by
  unfold originChain
  rw [Record.step_origin h]

/-- `indexEntries_pages` at the deployed cadence: every `index.log` the deployed seals write from
genesis reads back as every entry handed to them, in order (HOST-31; `worldBytesMax` = 2^28 fits
a frame's u32 length). -/
theorem indexEntries_pages (keys : Keys) (ess : List (Array Entry)) {bytes : ByteArray} {pos : Position}
    (h : Base.pages keys c indexStart ess = .ok (bytes, pos)) :
    indexEntries keys.index c pos.tag bytes = .ok (ess.map Array.toList).flatten.toArray ∧
      pos.offset = bytes.size :=
  Host.indexEntries_pages keys c (by decide) ess h

/-- `Carry.world_carried` at the deployed codec (HOST-28): a file `host import` accepts hashes to
the operator's digest, and the World it makes holds exactly the file's carried bytes at its anchor
height. The codec premise is CODEC's `digestCodec_lawful`. -/
theorem import_carried {name nonce : ByteArray} {want : Codec.Digest} {f : ByteArray} {r : Carry.Read D}
    {w₀ : World D} (h : Carry.importWorld X Codec.Deployed.digestCodec name nonce want f = .ok (w₀, r)) :
    Carry.digestOf f = want ∧
      (Codec.Kernel.carried X.env Codec.Deployed.digestCodec).bytes w₀.carried = f.extract r.carriedAt f.size ∧
      w₀.height = r.head.height :=
  have ⟨hr, hw⟩ := Carry.importWorld_ok h
  Carry.world_carried Codec.Deployed.digestCodec_lawful.on hr hw

/-- `Carry.exportFile_reads` at the deployed codec: what `host export` writes, `host import`
reads back under the printed digest, to the exported World's carried bytes and height. -/
theorem export_reads {w : World D} {f : ByteArray}
    (h : Carry.exportFile X.env Codec.Deployed.digestCodec w = .ok f) :
    ∃ r, Carry.read X.env Codec.Deployed.digestCodec (Carry.digestOf f) f = .ok r ∧
      (Codec.Kernel.carried X.env Codec.Deployed.digestCodec).bytes r.carried =
        (Codec.Kernel.carried X.env Codec.Deployed.digestCodec).bytes w.carried ∧
      r.head = ⟨w.origin, w.height, w.chain⟩ :=
  Carry.exportFile_reads h

end Nanodregg.Host.Deployed
