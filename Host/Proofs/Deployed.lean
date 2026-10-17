/-
# Host.Proofs.Deployed — the deployed instance meets the premises of the generic open theorems

* `originChain_genesis` / `genesis_origin_passes` (HOST-25) — for every World `host genesis` makes
  (`Receive.genesisWorld`, what `Receive.genesis` returns: `genesis_ok`), the deployed `originChain` is the chain `recorder.mark` writes into the origin
  frame (KERNEL's `genesis_chain`), and the deployed genesis image passes the origin check;
* `mark_chain_width` (HOST-33) — every chain the deployed loop puts in an index entry is the width
  the deployed Store's entries hold (`Keys.ofKey`'s `chainBytes`), so `entryUnfit`'s chain arm
  cannot fire at the deployed instance (the generic round trip, `entriesSeq_read`, has no premise);
* `foldStep_originChain` (HOST-25) — a record the deployed reopen folds keeps `originChain`
  (`Record.step_origin`, from KERNEL's `fold_origin`), so every later base's World states the chain
  the origin frame holds;
* `openWith_journalOk` (KERNEL-41) — the World the deployed writer's open returns has a `JournalOk`
  journal (a canonical trie, every entry in its window, heights distinct): its base's World because
  the deployed World codec read it (`Codec.Deployed.world_get_journalOk`), every record after it by
  `Record.foldlM_journalOk`; with `Host.admitBatch_journalOk`, every World the loop holds is, and the
  `JournalCanon` premise of `Host.lookup_expired_final` / `lookup_expired_never_committed` is
  discharged there.
-/
import Host.Deployed
import Host.Proofs.Base
import Host.Proofs.Carry
import Host.Proofs.Backup
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

/-- **The deployed chain is the deployed entry's width** (HOST-33): the chain `recorder.mark`
writes into every index entry is `chainBytes` long for every Store key, so no deployed seal is
refused `entryUnfit` for its chain. -/
theorem mark_chain_width (key : Codec.Digest) (w : World D) :
    (recorder.mark w).2.size = (Keys.ofKey key shapes).chainBytes := by
  simp only [recorder, Keys.ofKey, Codec.Digest.size_eq]

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


/-- **The World the deployed writer opens to is `JournalOk`** (KERNEL-41), whatever base file and
segment bytes the open reads. -/
theorem openWith_journalOk {keys : Keys} {file I S : ByteArray} {o : Opening (World D)}
    (h : Id.run (openWith keys c world recorder.mark originChain foldStep file S.size I.size
      (segReader I) (segReader S)) = .ok o) :
    o.opened.world.JournalOk X.env := by
  obtain ⟨b, _n, _d, rs, hb, hf, -⟩ := openWith_world keys c world recorder.mark originChain foldStep file I S h
  obtain ⟨r, _, _, hd, _⟩ := Base.read_decode keys c world file hb
  simp only [Codec.Stream.decode] at hd
  split at hd
  · rename_i v j hget
    split at hd
    · cases hd
      obtain ⟨x, hx, hacc⟩ := Codec.Stream.refine_get_inner hget
      obtain ⟨_j, hw⟩ := Codec.Stream.product_get_fst hx
      obtain ⟨xw, xo, xt, xio, xit⟩ := x
      simp only [Option.some.injEq] at hacc
      subst hacc
      exact Record.foldlM_journalOk (Codec.Deployed.world_get_journalOk hw) hf
    · cases hd
  · cases hd

end Nanodregg.Host.Deployed
