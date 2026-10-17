import Codec.Kernel
import Codec.World
import Codec.Hash
import Codec.Ed25519

/-!
# Codec.Deployed — the one deployed `Env` and `Ctx`

The kernel is generic in its digest and hash. This module fixes them for deployment: digests are
`Codec.Digest` (32 bytes), the hash is cSHAKE256 with the domain as customization (`Hash.digest`),
turns, cells and calls are encoded by `Codec.Kernel`, and signatures are checked by RFC 8032
Ed25519 (`Ed25519.verify`). LANG supplies the `Program`. The facts the kernel's theorems take as
premises are proved for this instance in `Codec.Proofs.Deployed`.
-/

namespace Nanodregg.Codec.Deployed

open Nanodregg.Kernel Nanodregg.Kernel.Receive

/-- The deployed digest's codec: its 32 bytes. -/
abbrev digestCodec : Stream Digest := Stream.digest

def env : Env Digest where
  hash := Hash.digest
  bytes := Digest.bytes
  turnBytes := Nanodregg.Codec.Kernel.turnBytes digestCodec
  cellBytes := Nanodregg.Codec.Kernel.cellBytes

def ctx (program : Program Digest) : Ctx Digest where
  env := env
  unsignedBytes := Nanodregg.Codec.Kernel.unsignedBytes digestCodec
  callBytes := Nanodregg.Codec.Kernel.callBytes digestCodec
  decodeCall := Nanodregg.Codec.Kernel.decodeCall digestCodec
  digestOf := Digest.ofBytes?
  verify := Ed25519.verify
  program := program

/-- The checkpoint's codec. -/
def world : Stream (World Digest) := Nanodregg.Codec.Kernel.world env digestCodec

end Nanodregg.Codec.Deployed
