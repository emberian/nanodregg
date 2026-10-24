/-
# Protocol.Rows.Deployed — the member rows at the DEPLOYED parameters

`host`'s own instance (`Host.Deployed`): its `Ctx` (`Host.Deployed.X`: the 32-byte `Codec.Digest`,
cSHAKE256 with the domain as customization, CODEC's codecs and `decodeCall`, RFC 8032 Ed25519 and
LANG's program), its World codec, and its Store sealers (`Host.Keys.ofKey`: KMAC256 under a Store
key, the unkeyed base digest, the deployed shape stamp). Custody's keys are Ed25519: a rows secret
is a tag string, its seed the Kernel Sim's deployed seed of it (`Kernel.Sim.Deployed.seed`, the
cSHAKE256 digest under `nanodregg/sim/seed`), its public key `Ed25519.publicKey` of that seed.
-/
import Protocol.Rows.Params
import Host.Deployed
import Kernel.Sim.Deployed

namespace Nanodregg.Protocol.Rows.Params

open Nanodregg.Codec

/-- The rows' Store key: fixed, a test parameter, as `host genesis` would read one from its key file. -/
def storeKey : Digest := Hash.digest "nanodregg/rows/store-key/v1" "rows".toUTF8

def deployed : Params Digest :=
  { name := "deployed parameters (Digest, cSHAKE256, Ed25519, KMAC256 Store tags)"
    ctx := Host.Deployed.X
    receipts := Protocol.Foreign.check Codec.Deployed.env Codec.Deployed.digestCodec
    dc := Deployed.digestCodec
    world := Host.Deployed.world
    pub := fun s => Ed25519.publicKey (Kernel.Sim.Deployed.seed s)
    sign := fun s m => Ed25519.sign (Kernel.Sim.Deployed.seed s) m
    keys := Host.Keys.ofKey storeKey Host.Deployed.shapes
    -- a write's event and record are about four times the toy's (32-byte digests and keys, 64-byte
    -- signatures, against 8 and 8): the toy's seal threshold times four keeps every row's shape
    sealMinBytes := 4 * 8192 }

end Nanodregg.Protocol.Rows.Params
