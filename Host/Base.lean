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

/-- One record of the segment, as `log` finds it: the World's height and chain BEFORE the record
(`chain` in `Env.bytes`), and the frame's offset. -/
structure Entry where
  height : Nat
  offset : Nat
  chain : ByteArray

/-- The widest chain an entry carries (the deployed digest is 32 bytes). -/
def chainBytesMax : Nat := 64

def Entry.codec : Stream Entry :=
  Stream.refine "host/entry" (Stream.product Stream.nat64 (Stream.product Stream.nat64 (Stream.rawBytes chainBytesMax)))
    (fun (h, o, c) => some ⟨h, o, c⟩) (fun e => (e.height, e.offset, e.chain))

/-- What a base holds: the World, where the segment after it starts, and the index of every
record before it (so `log` can page from any height without reading the segment from 0). -/
structure Base (W : Type) where
  world : W
  offset : Nat
  tag : Digest
  index : List Entry

/-- The most index entries a base carries. -/
def indexMax : Nat := 2 ^ 32 - 1

/-- The base record's codec, over the World's. -/
def Base.codec {W : Type} (world : Stream W) : Stream (Base W) :=
  Stream.refine "host/base"
    (Stream.product world (Stream.product Stream.nat64 (Stream.product Stream.digest
      (Stream.rawList indexMax Entry.codec))))
    (fun (w, o, t, i) => some ⟨w, o, t, i⟩) (fun b => (b.world, b.offset, b.tag, b.index))

/-- A tag as a digest (every tag is `Log.tagBytes` long). -/
def tagDigest (s : Log.Sealer) (b : ByteArray) : Digest := ⟨s.tag b, s.tag_size b⟩

/-- The tag a fresh segment chains from: 32 zero bytes. -/
def segmentInitial : ByteArray := Digest.zero.bytes

/-- The `prev` of the base's one frame. -/
def baseInitial : ByteArray := Digest.zero.bytes

/-- The keyed tags of one Store (its segment frames and its base, under separate domains), and the
UNKEYED digest of a base's World bytes, which a thin member pins (HOST-15). -/
structure Keys where
  segment : Log.Sealer
  base : Log.Sealer
  worldDigest : ByteArray → ByteArray

/-- Why a seal did not produce a base (law 7). -/
inductive SealFault where
  /-- the World encodes to more than `worldBytesMax`: the size at which HOST-14 must change -/
  | worldTooLarge (bytes : Nat)
  /-- the index encodes to more than `worldBytesMax` (each record admits a Turn, which adds more
  than an entry's bytes to the World, so this is past the World's own bound) -/
  | indexTooLarge (bytes : Nat)
  | io (detail : String)
  deriving Repr

def SealFault.name : SealFault → String
  | .worldTooLarge _ => "worldTooLarge"
  | .indexTooLarge _ => "indexTooLarge"
  | .io _ => "io"

/-- The base file's bytes for `w` at `offset`/`tag`, or why not. The size is checked before
anything is encoded. -/
def Base.file {W : Type} (keys : Keys) (c : Cadence) (world : Stream W) (w : W) (offset : Nat)
    (tag : Digest) (index : List Entry) : Except SealFault ByteArray :=
  let ib := (Stream.rawList indexMax Entry.codec).size index
  if c.worldBytesMax < world.size w then .error (.worldTooLarge (world.size w)) else
  if c.worldBytesMax < ib then .error (.indexTooLarge ib) else
  .ok (Log.frame keys.base baseInitial ((Base.codec world).bytes ⟨w, offset, tag, index⟩))

/-- Where a base file's World bytes are: right after the frame's length field. -/
def worldStart : Nat := 4

/-- The World bytes of a base file whose World is `bytes` long. -/
def worldBytesOf (file : ByteArray) (bytes : Nat) : ByteArray :=
  file.extract worldStart (worldStart + bytes)

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
    Except BaseFault (Base W × Nat × ByteArray) :=
  if Log.frameMax c.baseRecordMax < file.size then .error (.baseTooLarge file.size) else
  match Log.frameAt keys.base c.baseRecordMax file 0 baseInitial with
  | none => .error .baseCorrupt
  | some r =>
    if r.next ≠ file.size then .error .baseCorrupt else
    match (Base.codec world).decode r.record with
    | .error e => .error (.baseUndecodable e)
    | .ok b => .ok (b, world.size b.world, keys.worldDigest (worldBytesOf file (world.size b.world)))

/-- How many segment bytes open reads after a base at `offset` whose World is `baseBytes` long,
in a segment of `size` bytes. -/
def tailRead (c : Cadence) (baseBytes offset size : Nat) : Except BaseFault Nat :=
  if size < offset then .error (.segmentShort size offset)
  else if c.tailMax baseBytes < size - offset then .error (.tailTooLong (size - offset) (c.tailMax baseBytes))
  else .ok (size - offset)

/-! ## The seal policy: a pure function the loop calls -/

/-- The newest durable base, as the loop counts it: the segment offset it starts from, its World's
encoded size, height and chain (`Env.bytes`), and the digest of its World bytes (what `read`
pages state, HOST-15). -/
structure Sealed where
  offset : Nat
  bytes : Nat
  height : Nat
  chain : ByteArray
  digest : ByteArray

/-- The genesis base as the loop counts it: offset 0, the World `w`, its mark and digest. -/
def Sealed.genesis {W : Type} (keys : Keys) (world : Stream W) (mark : W → Nat × ByteArray) (w : W) :
    Sealed :=
  ⟨0, world.size w, (mark w).1, (mark w).2, keys.worldDigest (world.bytes w)⟩

/-- Where the segment stands: every byte before `offset` is synced, and `tag` chains the next
frame. -/
structure Position where
  offset : Nat
  tag : Digest

/-- The bytes of the frame holding `record`. -/
def frameSize (record : ByteArray) : Nat := 4 + record.size + Log.tagBytes

/-- After a commit that reached `pos`: start a seal in the background? -/
def shouldSeal (c : Cadence) (sealed : Sealed) (pending : Bool) (pos : Nat) : Bool :=
  !pending && decide (c.cadence sealed.bytes ≤ pos - sealed.offset)

end Nanodregg.Host
