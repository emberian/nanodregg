/-
# Host.Base — the sealed whole-World base, and what open reads (HOST-14)

    STORE/base.world = one Log frame (under the base sealer) of
                       shapes32 ‖ world bytes ‖ u64 offset ‖ tag32 ‖ u64 indexOffset ‖ indexTag32
    STORE/index.log  = Log frames (under the index sealer), one PAGE per seal: the entries
                       written since the base before it (HOST-30)

`shapes32` is the SHAPE STAMP (D2, HOST-20): the digest of the tags of the base codec (which holds
CODEC's World codec) and of the batch record codec, `Base.shapeStamp`. A Store's bytes are
judged under the shapes of the binary that opens it: a base whose stamp is not the running one is
refused `shapeMismatch` by name, after its MAC verifies and BEFORE any byte of it is decoded. No
segment byte is ever read without its base (`openWith` reads the base first and the segment only
from the base's offset), so the base's stamp covers the batch records after it: an old shape
refuses to load, it is never reinterpreted (law 1).

`offset` is where in `seg.log` the batches after this World begin, and `tag` is the segment's
chain tag there (the `prev` of the frame at `offset`). `indexOffset` and `indexTag` name the
`index.log` prefix whose pages are the index of every record before `offset`, the same way: a
seal appends ONE page and syncs it before the base that names it is installed, so a base never
names a page that is not durable, and bytes past `indexOffset` are an orphan page of a seal whose
base never landed (HOST-30). The base holds no entries: a seal writes only the entries since
the last base, never the whole history (HOST-17's count). The World part is exactly CODEC's World
codec, so its digest is a function of the World's contents (`Codec.Proofs.World.world_bytes_equiv`):
a full follower can countersign it, and a thin member can trust it (HOST-15).

A base is replaced atomically (`base.tmp` → sync → rename → sync dir), so a crash leaves either the
old base or the new one, never a torn one. A base that does not verify is therefore not a crash:
it is refused `baseCorrupt` by name, and open does not fall back to folding the whole log.

Open reads the base (at most `Log.frameMax c.baseRecordMax` bytes), the origin frame at 0 (at most
`originMax` bytes, checked against the base World's origin, HOST-25) and the segment from `offset`,
and `tailRead` refuses a tail longer than `c.tailMax` by name (`tailTooLong`), so open reads one
base and at most two cadences and a frame of log (`Host.Proofs.Base.tailRead_le`). The loop never
writes a longer tail (`Host.Loop.Tail`).
-/
import Host.Bounds
import Codec.Raw
import Codec.World
import Codec.Tag

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

/-- An entry `Entry.codec` spells and reads back exactly: a u64 height and offset, and a chain of
at most `chainBytesMax` bytes (`Host.Proofs.Base.Entry.codec_lawfulOn`). `Base.page` refuses a
page holding any other (`entryUnfit`), so every page on disk decodes to the entries it was
written from. -/
def Entry.fits (e : Entry) : Bool :=
  decide (e.height < 2 ^ 64) && decide (e.offset < 2 ^ 64) && decide (e.chain.size ≤ chainBytesMax)

/-- What a base holds: the World, where the segment after it starts, and where the index of
every record before it ends in `index.log` (so `log` can page from any height without reading
the segment from 0). -/
structure Base (W : Type) where
  world : W
  offset : Nat
  tag : Digest
  indexOffset : Nat
  indexTag : Digest

/-- The most index entries one page carries. -/
def indexMax : Nat := 2 ^ 32 - 1

/-- One page of `index.log`: the entries of the records a seal adds to the index. -/
def Entry.page : Stream (List Entry) := Stream.rawList indexMax Entry.codec

/-- The base record's codec, over the World's. -/
def Base.codec {W : Type} (world : Stream W) : Stream (Base W) :=
  Stream.refine "host/base"
    (Stream.product world (Stream.product Stream.nat64 (Stream.product Stream.digest
      (Stream.product Stream.nat64 Stream.digest))))
    (fun (w, o, t, io, it) => some ⟨w, o, t, io, it⟩)
    (fun b => (b.world, b.offset, b.tag, b.indexOffset, b.indexTag))

/-- The domain of the shape stamp. -/
def domShapes : String := "nanodregg/host/shapes/v1"

/-- The shape stamp of a Store whose bases hold `world` and whose segment holds `record`s: the
digest of CODEC's content-addressed tags (`Tag.of`) of the base codec and the batch record codec.
The base codec's shape contains the World codec's and the index entry's, so a change to any of
the World, the base or a batch record changes the stamp (`Codec.Proofs.Tag.Tag.of_eq`: equal tags
mean equal labels and shapes). Computed from the codecs, never written as a literal. -/
def Base.shapeStamp {W R : Type} (world : Stream W) (record : Stream R) : Digest :=
  Hash.digest domShapes ((Tag.of "host/base" (Base.codec world)).bytes ++ (Tag.of "host/batch" record).bytes)

/-- The width of the stamp at the head of a base record (a digest). -/
def stampBytes : Nat := 32

/-- A tag as a digest (every tag is `Log.tagBytes` long). -/
def tagDigest (s : Log.Sealer) (b : ByteArray) : Digest := ⟨s.tag b, s.tag_size b⟩

/-- The tag a fresh segment chains from: 32 zero bytes. -/
def segmentInitial : ByteArray := Digest.zero.bytes

/-- The `prev` of the base's one frame. -/
def baseInitial : ByteArray := Digest.zero.bytes

/-- The tag a fresh `index.log` chains from: 32 zero bytes. -/
def indexInitial : ByteArray := Digest.zero.bytes

/-- Where an append-only file stands: every byte before `offset` is synced, and `tag` chains the
next frame. -/
structure Position where
  offset : Nat
  tag : Digest

/-- An empty `index.log`: nothing written, chained from `indexInitial`. -/
def indexStart : Position := ⟨0, Digest.zero⟩

/-- The keyed tags of one Store (its segment frames and its base, under separate domains), and the
UNKEYED digest of a base's World bytes, which a thin member pins (HOST-15). -/
structure Keys where
  segment : Log.Sealer
  base : Log.Sealer
  /-- the pages of `index.log` (HOST-30) -/
  index : Log.Sealer
  worldDigest : ByteArray → ByteArray
  /-- the shape stamp this binary writes and accepts (`Base.shapeStamp`, D2): unkeyed, a
  function of the codecs alone -/
  shapes : Digest

/-- Why a seal did not produce a base (law 7). -/
inductive SealFault where
  /-- the World encodes to more than `worldBytesMax`: the size at which HOST-14 must change -/
  | worldTooLarge (bytes : Nat)
  /-- `index.log` would grow past `worldBytesMax` with this seal's page: the same lifetime bound
  the whole index had inside the base before HOST-30, now checked in O(1) -/
  | indexTooLarge (bytes : Nat)
  /-- the `index`-th entry of a page is outside `Entry.codec`'s domain (`Entry.fits`): its page
  would not read back as written. Unreachable at the deployed chain (32 bytes); a defect -/
  | entryUnfit (index : Nat)
  /-- `index.log` is `size` bytes, not the `offset` where the newest base's prefix ends: a page
  appended now would land elsewhere than the base about to name it. Another process wrote or
  truncated the file; a restart's open truncates an orphan or refuses `indexShort` -/
  | indexMoved (size offset : Nat)
  | io (detail : String)
  deriving Repr

def SealFault.name : SealFault → String
  | .worldTooLarge _ => "worldTooLarge"
  | .indexTooLarge _ => "indexTooLarge"
  | .entryUnfit _ => "entryUnfit"
  | .indexMoved _ _ => "indexMoved"
  | .io _ => "io"

/-- The base file's bytes for `w` at the segment position `seg`, naming the `index.log` prefix
`index`, or why not. The size is checked before anything is encoded. -/
def Base.file {W : Type} (keys : Keys) (c : Cadence) (world : Stream W) (w : W) (seg : Position)
    (index : Position) : Except SealFault ByteArray :=
  if c.worldBytesMax < world.size w then .error (.worldTooLarge (world.size w)) else
  .ok (Log.frame keys.base baseInitial
    (keys.shapes.bytes ++ (Base.codec world).bytes ⟨w, seg.offset, seg.tag, index.offset, index.tag⟩))

/-- The page a seal appends to `index.log` at `at_` for the entries since the last base, and the
position after it; no entries, no page. Refuses, before encoding, an entry outside the codec's
domain (`entryUnfit`, `Entry.fits`) and a page past `indexMax` entries or one after which the file would pass
`worldBytesMax` (`indexTooLarge`), so a page it returns reads back as exactly these entries
(`Host.Proofs.Base.indexEntries_pages`). -/
def Base.page (keys : Keys) (c : Cadence) (at_ : Position) (entries : Array Entry) :
    Except SealFault (ByteArray × Position) :=
  if entries.isEmpty then .ok (ByteArray.empty, at_) else
  match entries.toList.findIdx? (fun e => !e.fits) with
  | some i => .error (.entryUnfit i)
  | none =>
  let n := at_.offset + Log.frameMax (Entry.page.size entries.toList)
  if c.worldBytesMax < n ∨ indexMax < entries.size then .error (.indexTooLarge n) else
  let r := Entry.page.bytes entries.toList
  .ok (Log.frame keys.index at_.tag.bytes r,
    ⟨at_.offset + Log.frameMax r.size, tagDigest keys.index (at_.tag.bytes ++ r)⟩)

/-- The `index.log` bytes successive seals append from `at_`, one `Base.page` per seal, and the
position after them: what `Host.Proofs.Base.indexEntries_pages` reads back. -/
def Base.pages (keys : Keys) (c : Cadence) : Position → List (Array Entry) →
    Except SealFault (ByteArray × Position)
  | at_, [] => .ok (ByteArray.empty, at_)
  | at_, es :: ess =>
    match Base.page keys c at_ es with
    | .error f => .error f
    | .ok (p, at') =>
      match Base.pages keys c at' ess with
      | .error f => .error f
      | .ok (ps, at'') => .ok (p ++ ps, at'')

/-- What one seal writes, checked before anything is written: that `index.log` (`indexSize` bytes
now) ends exactly where the newest base's prefix `ipos` ends, so the page appended at the file's
end is the page framed at `ipos` (`indexMoved` otherwise); the World's size; then the page for
`entries` at `ipos`, then the base naming the index prefix up to that page's end. Both
checkpoints (files, memory) seal through this one function. -/
def Base.seal {W : Type} (keys : Keys) (c : Cadence) (world : Stream W) (w : W) (seg ipos : Position)
    (entries : Array Entry) (indexSize : Nat) : Except SealFault (ByteArray × Position × ByteArray) :=
  if indexSize ≠ ipos.offset then .error (.indexMoved indexSize ipos.offset) else
  if c.worldBytesMax < world.size w then .error (.worldTooLarge (world.size w)) else
  match Base.page keys c ipos entries with
  | .error f => .error f
  | .ok (page, ipos') =>
    match Base.file keys c world w seg ipos' with
    | .error f => .error f
    | .ok file => .ok (page, ipos', file)

/-- A Store as genesis writes it, before any file exists: the segment holding ONE frame, the
ORIGIN frame `Log.frame keys.segment segmentInitial origin` whose record is the genesis World's
chain (`(mark w₀).2`: the Store's identity at height 0), and the base of `w₀` at that frame's end,
chained from its tag. So every base sits after a frame of its own segment, and the 32 bytes
before any base's offset are that base's tag (HOST-18). Writers of a Store (`Host.genesis` on
files, `Host.Sim.memGenesis` in memory) write exactly these bytes; the loop's start state is what
opening them gives (one start path). -/
structure Image where
  segment : ByteArray
  base : ByteArray
  /-- `index.log` at genesis: empty (no record precedes the origin) -/
  index : ByteArray

def genesisImage {W : Type} (keys : Keys) (c : Cadence) (world : Stream W)
    (mark : W → Nat × ByteArray) (w₀ : W) : Except SealFault Image :=
  let origin := (mark w₀).2
  let segment := Log.frame keys.segment segmentInitial origin
  match Base.file keys c world w₀ ⟨segment.size, tagDigest keys.segment (segmentInitial ++ origin)⟩ indexStart with
  | .error f => .error f
  | .ok base => .ok ⟨segment, base, ByteArray.empty⟩

/-- Where a base file's World bytes are: after the frame's length field and the shape stamp. -/
def worldStart : Nat := 4 + stampBytes

/-- The World bytes of a base file whose World is `bytes` long. -/
def worldBytesOf (file : ByteArray) (bytes : Nat) : ByteArray :=
  file.extract worldStart (worldStart + bytes)

/-! ## The Store layout, as data (HOST-30; OPS renders RUNBOOK and the backup plants from it) -/

/-- How a Store file changes over its life. -/
inductive FileKind where
  /-- written by genesis, never again -/
  | once
  /-- only ever appended to: a longer copy holds every byte a shorter one does -/
  | appendOnly
  /-- replaced whole and atomically (through `base.tmp`) -/
  | replaced
  /-- never read by an open, never backed up -/
  | transient
  deriving DecidableEq, Repr

structure StoreFile where
  name : String
  kind : FileKind
  holds : String

namespace Store

/-- Every file of a Store directory, in the order genesis writes them. A seal appends a page to
`index.log` and syncs it before `base.tmp` is renamed over `base.world`; a batch is appended to
`seg.log` and synced before it is answered. -/
def layout : List StoreFile :=
  [⟨"key", .once, "32 bytes, mode 0600: the integrity-at-rest key (HOST-16)"⟩,
   ⟨"seg.log", .appendOnly, "the frames (Host.Log) from genesis's origin frame: one batch record per frame; its append handle is flock'd, the writer lock"⟩,
   ⟨"index.log", .appendOnly, "one keyed page per seal: the index entries of the records since the base before it (HOST-30)"⟩,
   ⟨"base.world", .replaced, "the newest sealed base: the World, the seg.log position after it and the index.log prefix it names"⟩,
   ⟨"base.tmp", .transient, "a base being installed; a crash may leave one, which no open reads"⟩]

/-- The order a backup copies a LIVE Store's files in: the key, then the base, then the
append-only files, so each append-only copy is at least as long as the prefix the copied base
names (a longer one is a torn tail or an orphan page, which an open handles). -/
def backupOrder : List String := ["key", "base.world", "index.log", "seg.log"]

end Store

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
  /-- the 32 bytes before the base's offset are not the base's tag (or there are not 32): the
  segment is not the one this base was sealed over (another Store's, or a pre-HOST-18 Store
  whose base sat at offset 0). Never read as a torn tail, so nothing is truncated (HOST-18). -/
  | foreignSegment
  /-- the base was written under other shapes (`stored`, the stamp on disk) than the running
  binary's (`running`): an old (or a newer) shape refuses, never decoded (D2, HOST-20) -/
  | shapeMismatch (stored running : Array UInt8)
  /-- the segment's origin frame verifies under this Store's key but states another World's
  genesis chain than the base World's origin (two Stores sharing a key file, one's seg.log
  spliced over the other's; HOST-25) -/
  | foreignOrigin
  /-- `index.log` is shorter than the prefix the base names: a copy cut short, or the file
  truncated (HOST-30) -/
  | indexShort (size offset : Nat)
  /-- the pages of `index.log` before the base's `indexOffset` do not verify under this Store's
  key, do not end at the tag the base names, or do not decode (HOST-30) -/
  | indexCorrupt
  deriving Repr

def BaseFault.name : BaseFault → String
  | .noBase => "noBase"
  | .baseTooLarge _ => "baseTooLarge"
  | .baseCorrupt => "baseCorrupt"
  | .baseUndecodable _ => "baseUndecodable"
  | .segmentShort _ _ => "segmentShort"
  | .tailTooLong _ _ => "tailTooLong"
  | .foreignSegment => "foreignSegment"
  | .shapeMismatch _ _ => "shapeMismatch"
  | .foreignOrigin => "foreignOrigin"
  | .indexShort _ _ => "indexShort"
  | .indexCorrupt => "indexCorrupt"

/-- The base a base file holds, and its World's encoded size. -/
def Base.read {W : Type} (keys : Keys) (c : Cadence) (world : Stream W) (file : ByteArray) :
    Except BaseFault (Base W × Nat × ByteArray) :=
  if Log.frameMax c.baseRecordMax < file.size then .error (.baseTooLarge file.size) else
  match Log.frameAt keys.base c.baseRecordMax file 0 baseInitial with
  | none => .error .baseCorrupt
  | some r =>
    if r.next ≠ file.size then .error .baseCorrupt else
    let stored := r.record.extract 0 stampBytes
    if stored ≠ keys.shapes.bytes then .error (.shapeMismatch stored.data keys.shapes.bytes.data) else
    match (Base.codec world).decode (r.record.extract stampBytes r.record.size) with
    | .error e => .error (.baseUndecodable e)
    | .ok b => .ok (b, world.size b.world, keys.worldDigest (worldBytesOf file (world.size b.world)))

/-- The index a base names, from the `bytes` of `index.log` before its `indexOffset`: every frame
verifies from `indexInitial`, the bytes end exactly at a frame that chains to `indexTag`, and each
page decodes. Anything else is `indexCorrupt`, never a shorter index. -/
def indexEntries (s : Log.Sealer) (c : Cadence) (indexTag : Digest) (bytes : ByteArray) :
    Except BaseFault (Array Entry) :=
  let rv := Log.recover s c.worldBytesMax indexInitial bytes
  if rv.validLen ≠ bytes.size ∨ rv.lastTag ≠ indexTag.bytes then .error .indexCorrupt else
  rv.records.foldlM (fun acc r => match Entry.page.decode r with
    | .ok es => .ok (acc ++ es.toArray)
    | .error _ => .error .indexCorrupt) #[]

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
  /-- the `index.log` prefix this base names (HOST-30) -/
  index : Position
  /-- the entries that prefix holds: the next seal's page starts at this entry -/
  indexCount : Nat

/-- The bytes of the frame holding `record`. -/
def frameSize (record : ByteArray) : Nat := 4 + record.size + Log.tagBytes

/-- After a commit that reached `pos`: start a seal in the background? -/
def shouldSeal (c : Cadence) (sealed : Sealed) (pending : Bool) (pos : Nat) : Bool :=
  !pending && decide (c.cadence sealed.bytes ≤ pos - sealed.offset)

end Nanodregg.Host
