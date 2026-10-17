/-
# Kernel.Sim.Deployed — the generator under the DEPLOYED parameters

The same `Kernel.Sim.Gen` run as the toy, with every parameter the deployment's: digests are
CODEC's 32-byte `Digest`, the hash is cSHAKE256 with the domain as customization, turns, cells and
calls are CODEC's codecs, a call is read back by CODEC's canonical `decodeCall` (the auditor
decodes the bytes the log holds), and signatures are RFC 8032 Ed25519,
signed by `Ed25519.sign` and checked by `Ed25519.verify`. Only the program is the generator's
two-law stub; LANG's real program runs in `lang-journey`.

A Sim secret is a tag string; its Ed25519 seed is the 32-byte cSHAKE256 digest of it under the
domain `nanodregg/sim/seed`, so every member has a well-formed seed and distinct tags give distinct
keys (up to a cSHAKE collision).
-/
import Kernel.Sim.Gen
import Codec.Deployed

namespace Nanodregg.Kernel.Sim.Deployed

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Codec

/-- The 32-byte Ed25519 seed of a Sim secret. -/
def seed (secret : ByteArray) : ByteArray := (Deployed.env.hash "nanodregg/sim/seed" secret).bytes

def params : Gen.Params Digest :=
  { name := "deployed parameters (Digest, cSHAKE256, CODEC codecs and decodeCall, Ed25519)"
    ctx := Deployed.ctx Gen.program
    pub := fun s => Ed25519.publicKey (seed s)
    sign := fun s m => Ed25519.sign (seed s) m
    zero := Digest.zero }

end Nanodregg.Kernel.Sim.Deployed
