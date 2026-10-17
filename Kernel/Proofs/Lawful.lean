/-
# Kernel.Proofs.Lawful — what the kernel's theorems assume of an `Env`, in one place (KERNEL-37)

`Env.Lawful E n` gathers every premise about an `Env` that a kernel theorem takes:

* `size`: every digest's bytes have one size `n`, and `n_le`: `n ≤ 32`, so a slot's bits fit the
  trie's depth;
* `bytes_inj`: a digest is determined by its bytes;
* `turnBytes_injOn`: a bounded turn is determined by its bytes (`TurnBytesInjOn`; over ALL turns
  the deployed codec is not injective, so no theorem assumes the unrestricted form);
* `cellBytes_injOn`: a cell that fits (`Codec.Kernel.Cell.Fits`, the cells the kernel keeps) is
  determined by its bytes (`InjOn`; the deployed cell codec is not injective on every cell,
  CODEC-12).

A theorem stated over a lawful `Env` takes `hE : E.Lawful n` and nothing else of the `Env`. The
deployed `Env` is lawful at 32 (`Kernel.Receive.deployed_lawful`, from CODEC's theorems), so every
such theorem holds at the deployed codec with no premise about it.
-/
import Kernel.World
import Codec.Proofs.Kernel

namespace Nanodregg.Kernel

variable {D : Type}

/-- `E.turnBytes` is injective on the turns `checkBounds` passes. That is what the deployed codec
proves (`Codec.Proofs.Deployed.turnBytes_injective`). Over ALL turns it is false there: `nat64`
truncates a counter past 2^64, so two turns that differ only in such a counter share their bytes.
No theorem here assumes the unrestricted form. -/
def TurnBytesInjOn [Ord D] (E : Env D) : Prop :=
  ∀ {t t' : Turn D}, checkBounds t = .ok () → checkBounds t' = .ok () →
    E.turnBytes t = E.turnBytes t' → t = t'

/-- The cell codec is injective on `F`. -/
def InjOn (F : Cell → Prop) (E : Env D) : Prop :=
  ∀ a b, F a → F b → E.cellBytes a = E.cellBytes b → a = b

/-- **What the kernel assumes of an `Env`**, at digest size `n`. -/
structure Env.Lawful [Ord D] (E : Env D) (n : Nat) : Prop where
  size : ∀ d, (E.bytes d).size = n
  n_le : n ≤ 32
  bytes_inj : Function.Injective E.bytes
  turnBytes_injOn : TurnBytesInjOn E
  cellBytes_injOn : InjOn Nanodregg.Codec.Kernel.Cell.Fits E

/-- The pointwise form of `bytes_inj` (the shape the receivers' proofs apply). -/
theorem Env.Lawful.bytes_eq [Ord D] {E : Env D} {n : Nat} (hE : E.Lawful n) {a b : D}
    (h : E.bytes a = E.bytes b) : a = b :=
  hE.bytes_inj h

/-- **The premise can fail**: an `Env` whose digests share their bytes is not lawful at any size, so
`Env.Lawful` is a real premise (satisfied at the deployed codec: `Receive.deployed_lawful`). -/
theorem Env.Lawful.refutable (n : Nat) :
    ¬ ({ hash := fun _ _ => false, bytes := fun _ => ByteArray.empty, turnBytes := fun _ => ByteArray.empty,
         cellBytes := fun _ => ByteArray.empty } : Env Bool).Lawful n :=
  fun h => Bool.noConfusion (h.bytes_inj (a₁ := true) (a₂ := false) rfl)

end Nanodregg.Kernel
