/-
# Host.Proofs.Deployed — the deployed instance meets the premises of the generic open theorems

* `originChain_genesis` / `genesis_origin_passes` (HOST-25) — for every World `host genesis` makes
  (`Receive.genesis`), the deployed `originChain` is the chain `recorder.mark` writes into the origin
  frame (KERNEL's `genesis_chain`), and the deployed genesis image passes the origin check;
* `foldStep_originChain` (HOST-25) — a record the deployed reopen folds keeps `originChain`
  (`Record.step_origin`, from KERNEL's `fold_origin`), so every later base's World states the chain
  the origin frame holds.
-/
import Host.Deployed
import Host.Proofs.Base

namespace Nanodregg.Host.Deployed

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Codec

theorem originChain_genesis (name nonce : ByteArray) (allowance : Nat) (founders : List (ByteArray × D)) :
    originChain (Receive.genesis X name nonce allowance founders) =
      (recorder.mark (Receive.genesis X name nonce allowance founders)).2 := by
  simp only [originChain, recorder, Receive.genesis_chain]

theorem genesis_origin_passes {F : Type} (keys : Keys) (name nonce : ByteArray) (allowance : Nat)
    (founders : List (ByteArray × D)) {img : Image}
    (h : genesisImage keys c world recorder.mark (Receive.genesis X name nonce allowance founders) = .ok img) :
    originFault (F := F) keys.segment (img.segment.extract 0 (originLen img.segment.size))
      (originChain (Receive.genesis X name nonce allowance founders)) = none :=
  genesisImage_origin keys c world recorder.mark originChain _ h
    (by show (Receive.genesis X name nonce allowance founders).chain.bytes.size ≤ chainBytesMax
        rw [Digest.size_eq]; decide)
    (originChain_genesis name nonce allowance founders)

theorem foldStep_originChain {w w' : World D} {r : ByteArray} (h : foldStep w r = .ok w') :
    originChain w' = originChain w := by
  unfold originChain
  rw [Record.step_origin h]

end Nanodregg.Host.Deployed
