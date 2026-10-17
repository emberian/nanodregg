/-
# Host.Base — the sealed whole-World base, and what open reads (HOST-14)

    STORE/base.world = one Log frame (under the base sealer) of
                       world bytes ‖ u64 offset ‖ tag32

`offset` is where in `seg.log` the batches after this World begin, and `tag` is the segment's
chain tag there (the `prev` of the frame at `offset`). The World part is exactly CODEC's World
codec, so its digest is a function of the World's contents (`Codec.Proofs.World.world_bytes_equiv`):
a full follower can countersign it, and a thin member can trust it (HOST-15).

A base is replaced atomically (`base.tmp` → sync → rename → sync dir), so a crash leaves either the
old base or the new one, never a torn one. A base that does not verify is therefore not a crash:
it is refused `baseCorrupt` by name, and open does not fall back to folding the whole log.

Open reads the base (at most `Log.frameMax c.baseRecordMax` bytes) and the segment from `offset`,
and `tailRead` refuses a tail longer than `c.tailMax` by name (`tailTooLong`), so open reads one
base and at most two cadences and a frame of log (`Host.Proofs.Base.tailRead_le`). The loop never
writes a longer tail (`Host.Loop.Tail`).
-/
import Host.Bounds
import Codec.Raw
import Codec.World

namespace Nanodregg.Host

open Nanodregg.Codec

/-- What a base holds. -/
structure Base (W : Type) where
  world : W
  offset : Nat
  tag : Digest

/-- The base record's codec, over the World's. -/
def Base.codec {W : Type} (world : Stream W) : Stream (Base W) :=
  Stream.refine "host/base" (Stream.product world (Stream.product Stream.nat64 Stream.digest))
    (fun (w, o, t) => some ⟨w, o, t⟩) (fun b => (b.world, b.offset, b.tag))

/-- A tag as a digest (every tag is `Log.tagBytes` long). -/
def tagDigest (s : Log.Sealer) (b : ByteArray) : Digest := ⟨s.tag b, s.tag_size b⟩

/-- The tag a fresh segment chains from: 32 zero bytes. -/
def segmentInitial : ByteArray := Digest.zero.bytes

/-- The `prev` of the base's one frame. -/
def baseInitial : ByteArray := Digest.zero.bytes

/-- The keyed tags of one Store: its segment frames and its base, under separate domains. -/
structure Keys where
  segment : Log.Sealer
  base : Log.Sealer

/-- Why a seal did not produce a base (law 7). -/
inductive SealFault where
  /-- the World encodes to more than `worldBytesMax`: the size at which HOST-14 must change -/
  | worldTooLarge (bytes : Nat)
  | io (detail : String)
  deriving Repr

def SealFault.name : SealFault → String
  | .worldTooLarge _ => "worldTooLarge"
  | .io _ => "io"

/-- The base file's bytes for `w` at `offset`/`tag`, or why not. The size is checked before
anything is encoded. -/
def Base.file {W : Type} (keys : Keys) (c : Cadence) (world : Stream W) (w : W) (offset : Nat)
    (tag : Digest) : Except SealFault ByteArray :=
  if c.worldBytesMax < world.size w then .error (.worldTooLarge (world.size w)) else
  .ok (Log.frame keys.base baseInitial ((Base.codec world).bytes ⟨w, offset, tag⟩))

/-- Why a Store's base does not open (law 7). -/
inductive BaseFault where
  /-- no `base.world`: the Store was never created by `host genesis` -/
  | noBase
  /-- larger than one base frame can be -/
  | baseTooLarge (bytes : Nat)
  /-- the frame does not verify under this Store's key -/
  | baseCorrupt
  | baseUndecodable (r : Codec.Refusal)
  /-- the segment is shorter than the offset the base starts from -/
  | segmentShort (size offset : Nat)
  /-- more segment bytes after the base than the loop ever writes -/
  | tailTooLong (bytes max : Nat)
  deriving Repr

def BaseFault.name : BaseFault → String
  | .noBase => "noBase"
  | .baseTooLarge _ => "baseTooLarge"
  | .baseCorrupt => "baseCorrupt"
  | .baseUndecodable _ => "baseUndecodable"
  | .segmentShort _ _ => "segmentShort"
  | .tailTooLong _ _ => "tailTooLong"

/-- The base a base file holds, and its World's encoded size. -/
def Base.read {W : Type} (keys : Keys) (c : Cadence) (world : Stream W) (file : ByteArray) :
    Except BaseFault (Base W × Nat) :=
  if Log.frameMax c.baseRecordMax < file.size then .error (.baseTooLarge file.size) else
  match Log.frameAt keys.base c.baseRecordMax file 0 baseInitial with
  | none => .error .baseCorrupt
  | some r =>
    if r.next ≠ file.size then .error .baseCorrupt else
    match (Base.codec world).decode r.record with
    | .error e => .error (.baseUndecodable e)
    | .ok b => .ok (b, r.record.size - 8 - Log.tagBytes)

/-- How many segment bytes open reads after a base at `offset` whose World is `baseBytes` long,
in a segment of `size` bytes. -/
def tailRead (c : Cadence) (baseBytes offset size : Nat) : Except BaseFault Nat :=
  if size < offset then .error (.segmentShort size offset)
  else if c.tailMax baseBytes < size - offset then .error (.tailTooLong (size - offset) (c.tailMax baseBytes))
  else .ok (size - offset)

/-! ## The seal policy: a pure function the loop calls -/

/-- The newest durable base, as the loop counts it: the segment offset it starts from and its
World's encoded size. -/
structure Sealed where
  offset : Nat
  bytes : Nat

/-- Where the segment stands: every byte before `offset` is synced, and `tag` chains the next
frame. -/
structure Position where
  offset : Nat
  tag : Digest

/-- What the loop does before appending a frame of `n` bytes at segment offset `pos`. -/
inductive Gate where
  /-- the tail stays within `tailMax`: append -/
  | commit
  /-- a seal is in flight: wait for it, then ask again -/
  | waitPending
  /-- no seal is in flight: seal the World as it stands, wait for it, then ask again -/
  | sealNow

def gate (c : Cadence) (sealed : Sealed) (pending : Bool) (pos n : Nat) : Gate :=
  if pos + n - sealed.offset ≤ c.tailMax sealed.bytes then .commit
  else if pending then .waitPending else .sealNow

/-- After a commit that reached `pos`: start a seal in the background? -/
def shouldSeal (c : Cadence) (sealed : Sealed) (pending : Bool) (pos : Nat) : Bool :=
  !pending && decide (c.cadence sealed.bytes ≤ pos - sealed.offset)

end Nanodregg.Host
