/-
# Host.Keys — the deployed Store sealers: KMAC256 under the Store key (HOST-16)

Segment frames, index entries and the base are tagged with `Codec.Hash.mac` under the one Store
key, in three domains, so no frame of one file verifies as another file's. The key is an
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
def domIndex : String := "nanodregg/host/index/v1"
/-- The UNKEYED digest a thin member pins (HOST-15): its own customization string, never the base
MAC's (HOST-26: one string, one purpose). -/
def domBaseDigest : String := "nanodregg/host/base-digest/v1"

def macSealer (key : Digest) (domain : String) : Log.Sealer where
  tag b := (Hash.mac key domain b).bytes
  tag_size b := (Hash.mac key domain b).size_eq

/-- The keys of a Store under `key`, judging its bases under the shape stamp `shapes`. -/
def Keys.ofKey (key : Digest) (shapes : Digest) : Keys where
  segment := macSealer key domSegment
  base := macSealer key domBase
  index := macSealer key domIndex
  worldDigest b := (Hash.digest domBaseDigest b).bytes
  shapes := shapes
  chainBytes := Digest.width

end Nanodregg.Host
