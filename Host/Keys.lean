/-
# Host.Keys — the deployed Store sealers: KMAC256 under the Store key (HOST-16)

Segment frames and the base are tagged with `Codec.Hash.mac` under the one Store key, in two
domains, so a base frame never verifies as a segment frame or the reverse. The key is an
integrity-at-rest key: it catches corruption, splicing and frames copied from another Store; it
does not stop anyone who can write STORE, and nothing derives authority, consent or a member's
identity from it (HOST-16).
-/
import Host.Base
import Codec.Hash

namespace Nanodregg.Host

open Nanodregg.Codec

def domSegment : String := "nanodregg/host/segment/v1"
def domBase : String := "nanodregg/host/base/v1"

def macSealer (key : Digest) (domain : String) : Log.Sealer where
  tag b := (Hash.mac key domain b).bytes
  tag_size b := (Hash.mac key domain b).size_eq

def Keys.ofKey (key : Digest) : Keys where
  segment := macSealer key domSegment
  base := macSealer key domBase
  worldDigest b := (Hash.digest domBase b).bytes

end Nanodregg.Host
