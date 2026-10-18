/-
# Host.Base — the sealed whole-World base, and what open reads (HOST-14)

    STORE/base.world = one Log frame (under the base sealer) of
                       shapes32 ‖ world bytes ‖ u64 offset ‖ tag32 ‖ u64 indexCount ‖ indexLast32
    STORE/index.log  = fixed-width ENTRIES, one per record before the newest base, entry k at
                       byte k · entryBytes: u64 steps ‖ u64 offset ‖ chain ‖ tag32, the tag the
                       index sealer over (origin chain ‖ u64 k ‖ steps ‖ offset ‖ chain)
                       (HOST-33, `Keys.forStore`)

`shapes32` is the SHAPE STAMP (D2, HOST-20): the digest of the tags of the base codec (which holds
CODEC's World codec) and of the batch record codec, and of the index entry layout
(`entryLayout`), `Base.shapeStamp`. A Store's bytes are judged under the shapes of the binary that
opens it: a base whose stamp is not the running one is refused `shapeMismatch` by name, after its
MAC verifies and BEFORE any byte of it is decoded. No segment byte is ever read without its base
(`openWith` reads the base first and the segment only from the base's offset), so the base's stamp
covers the batch records after it and the entries before its count: an old shape refuses to load,
it is never reinterpreted (law 1).

`offset` is where in `seg.log` the batches after this World begin, and `tag` is the segment's
chain tag there (the `prev` of the frame at `offset`). `indexCount` is how many entries of
`index.log` index the records before `offset`, and `indexLast` is the tag of the last of them
(`Digest.zero` at count 0): a seal appends the entries since the last base and syncs them before
the base that counts them is installed, so a base never counts an entry that is not durable, and
bytes past `indexCount · entryBytes` are ORPHAN entries of a seal whose base never landed. Each
entry's tag covers its position, so an entry cannot be moved, reordered or spliced; the base's
`indexLast` binds its count to the one entry open reads (HOST-33). Open reads ONE entry, not the
index; a `log` page reads O(log indexCount) of them, each checked by its tag on that read
(`Host.Page.entryAt`), and `host check` checks every one (`indexClean`). The base holds no entries:
a seal writes only the entries since the last base (HOST-17's count). The World part is exactly
CODEC's World codec, whose decode is exact (`Codec.Kernel.world_decode_iff`: `decode b = .ok w ↔
b = bytes w`), so its digest is a function of the World: a full follower can countersign it, and a thin member can
trust it (HOST-15).

A base is replaced atomically (`base.tmp` → sync → rename → sync dir), so a crash leaves either the
old base or the new one, never a torn one. A base that does not verify is therefore not a crash:
it is refused `baseCorrupt` by name, and open does not fall back to folding the whole log.

Open reads the base (at most `Log.frameMax c.baseRecordMax` bytes), the origin frame at 0 (at most
`originMax` bytes, checked against the base World's origin, HOST-25), the base's last index entry
(`entryBytes`), and the segment from `offset`, and `tailRead` refuses a tail longer than
`c.tailMax` by name (`tailTooLong`), so open reads one base, one entry and at most two cadences and
a frame of log (`Host.Proofs.Base.tailRead_le`). The loop never writes a longer tail
(`Host.Loop.Tail`).
-/
import Host.Bounds
import Codec.Raw
import Codec.World
import Codec.Tag

namespace Nanodregg.Host

open Nanodregg.Codec

/-- One record of the segment, as `log` finds it: the World's step count and chain BEFORE the
record (`chain` in `Env.bytes`), and the frame's offset. The log's position is its STEP count, not
its height (KERNEL-47 amendment 1: a recorded refusal is a step that leaves the height as it was, so
two records can begin at one height; they never begin at one step count). -/
structure Entry where
  steps : Nat
  offset : Nat
  chain : ByteArray

/-- The widest chain the origin frame carries (the deployed digest is 32 bytes): `originMax`. -/
def chainBytesMax : Nat := 64

/-- An entry the index can hold: a u64 step count and offset, and a chain of exactly `w` bytes (the
Store's chain width, `Keys.chainBytes`). `Base.entries` refuses any other (`entryUnfit`), so
every entry on disk reads back as the entry it was written from (`Host.Proofs.Base.Entry.read_bytes`). -/
def Entry.fits (w : Nat) (e : Entry) : Bool :=
  decide (e.steps < 2 ^ 64) && decide (e.offset < 2 ^ 64) && decide (e.chain.size = w)

/-- The layout of an index entry, as a version the shape stamp covers: the entry is fixed-width
bytes, not a CODEC stream, so its layout enters the stamp by name. -/
def entryLayout : String := "host/index/entry/v3: u64 steps, u64 offset, chain, mac32 over the Store's origin chain ++ u64 position ++ those"

/-- What a base holds: the World, where the segment after it starts, and how many entries of
`index.log` index the records before it (so `log` can page from any step without reading the
segment from 0), with the last one's tag. -/
structure Base (W : Type) where
  world : W
  offset : Nat
  tag : Digest
  /-- the entries of `index.log` that index the records before `offset` -/
  indexCount : Nat
  /-- the tag of entry `indexCount - 1` (`Digest.zero` at count 0) -/
  indexLast : Digest

/-- The most entries an `index.log` holds: a Store's lifetime in records. It bounds a page's
binary search at 33 entry reads (HOST-33: `indexTooLarge` past it). -/
def indexMax : Nat := 2 ^ 32 - 1

/-- The base record's codec, over the World's. -/
def Base.codec {W : Type} (world : Stream W) : Stream (Base W) :=
  Stream.refine "host/base/index-count"
    (Stream.product world (Stream.product Stream.nat64 (Stream.product Stream.digest
      (Stream.product Stream.nat64 Stream.digest))))
    (fun (w, o, t, ic, il) => some ⟨w, o, t, ic, il⟩)
    (fun b => (b.world, b.offset, b.tag, b.indexCount, b.indexLast))

/-- The domain of the shape stamp. -/
def domShapes : String := "nanodregg/host/shapes/v1"

/-- The shape stamp of a Store whose bases hold `world` and whose segment holds `record`s: the
digest of CODEC's content-addressed tags (`Tag.of`) of the base codec and the batch record codec,
and of the index entry layout by name (`entryLayout`). The base codec's shape contains the World
codec's, so a change to any of the World, the base, a batch record or an entry changes the stamp
(`Codec.Proofs.Tag.Tag.of_eq`: equal tags mean equal labels and shapes). The codecs' part is
computed from them, never written as a literal. -/
def Base.shapeStamp {W R : Type} (world : Stream W) (record : Stream R) : Digest :=
  Hash.digest domShapes ((Tag.of "host/base" (Base.codec world)).bytes ++ (Tag.of "host/batch" record).bytes ++
    entryLayout.toUTF8)

/-- A tag as a digest (every tag is `Log.tagBytes` long). -/
def tagDigest (s : Log.Sealer) (b : ByteArray) : Digest := ⟨s.tag b, s.tag_size b⟩

/-- The tag a fresh segment chains from: 32 zero bytes. -/
def segmentInitial : ByteArray := Digest.zero.bytes

/-- The `prev` of the base's one frame. -/
def baseInitial : ByteArray := Digest.zero.bytes

/-- Where an append-only file stands: every byte before `offset` is synced, and `tag` chains the
next frame. -/
structure Position where
  offset : Nat
  tag : Digest

/-- What a base names of `index.log`: how many entries index the records before its offset, and
the tag of the last of them (HOST-33). -/
structure IndexAt where
  count : Nat
  last : Digest

/-- An empty `index.log`: no entry, no last tag. -/
def indexStart : IndexAt := ⟨0, Digest.zero⟩

/-- The keyed tags of one Store (its segment frames and its base, under separate domains), and the
UNKEYED digest of a base's World bytes, which a thin member pins (HOST-15). -/
structure Keys where
  segment : Log.Sealer
  base : Log.Sealer
  /-- the entries of `index.log` (HOST-30, HOST-33) -/
  index : Log.Sealer
  worldDigest : ByteArray → ByteArray
  /-- the shape stamp this binary writes and accepts (`Base.shapeStamp`, D2): unkeyed, a
  function of the codecs alone -/
  shapes : Digest
  /-- the width of the World's chain (`Env.bytes` of a digest) in an index entry: 32 deployed -/
  chainBytes : Nat

/-- The keys of ONE Store: the index sealer tags `sid ++ msg`, where `sid` is the Store's identity,
the genesis chain of its World's origin (what its origin frame holds, HOST-25). So an entry of
another Store under the same key file does not read back here (HOST-33's law-6 read: the entry tag
covers its position, the Store and its fields). The segment and base sealers are unchanged. -/
def Keys.forStore (keys : Keys) (sid : ByteArray) : Keys :=
  { keys with index := ⟨fun b => keys.index.tag (sid ++ b), fun b => keys.index.tag_size (sid ++ b)⟩ }

/-- The bytes of one index entry. -/
def entryBytes (keys : Keys) : Nat := 16 + keys.chainBytes + Log.tagBytes

/-- What an entry's tag covers, less its position: `u64 steps ‖ u64 offset ‖ chain`. -/
def Entry.body (e : Entry) : ByteArray :=
  Stream.nat64.bytes e.steps ++ Stream.nat64.bytes e.offset ++ e.chain

/-- Entry `k`'s tag: the index sealer over `u64 k ‖ body`, so the tag names the position. -/
def Entry.tag (keys : Keys) (k : Nat) (e : Entry) : Digest :=
  tagDigest keys.index (Stream.nat64.bytes k ++ e.body)

/-- Entry `k` on disk: its body, then its tag. -/
def Entry.bytes (keys : Keys) (k : Nat) (e : Entry) : ByteArray := e.body ++ (e.tag keys k).bytes

/-- The entry `b` holds AS ENTRY `k`, or none: the entry its fields spell, accepted only if
`Entry.bytes keys k` of it is exactly `b`. So its tag verified at position k and the bytes are
the one spelling of that entry (`Host.Proofs.Base.Entry.read_sound`); a read never returns an
entry whose tag failed. -/
def Entry.read (keys : Keys) (k : Nat) (b : ByteArray) : Option Entry :=
  match Stream.nat64.decode (b.extract 0 8), Stream.nat64.decode (b.extract 8 16) with
  | .ok h, .ok o =>
    let e : Entry := ⟨h, o, b.extract 16 (16 + keys.chainBytes)⟩
    if Entry.bytes keys k e = b then some e else none
  | _, _ => none

/-- Entries `k, k+1, …` as `index.log` holds them, from byte `k · entryBytes`. -/
def Entry.run (keys : Keys) : Nat → List Entry → ByteArray
  | _, [] => ByteArray.empty
  | k, e :: es => Entry.bytes keys k e ++ Entry.run keys (k + 1) es

/-- Why a seal did not produce a base (law 7). -/
inductive SealFault where
  /-- the World encodes to more than `worldBytesMax`: the size at which HOST-14 must change -/
  | worldTooLarge (bytes : Nat)
  /-- `index.log` would hold more than `indexMax` entries with this seal's: the Store's lifetime
  in records (HOST-33; before it, the index's bytes against `worldBytesMax`) -/
  | indexTooLarge (count : Nat)
  /-- the `index`-th entry a seal is handed is outside the entry layout (`Entry.fits`: a u64
  height or offset, a chain of the Store's width): it would not read back as written.
  Unreachable at the deployed chain (32 bytes, `Kernel` digests); a defect -/
  | entryUnfit (index : Nat)
  /-- `index.log` is `size` bytes, not `offset`, the end of the entries the newest base counts:
  entries appended now would land elsewhere than the positions their tags name. Another process
  wrote or truncated the file; a restart's open truncates orphans or refuses `indexShort` -/
  | indexMoved (size offset : Nat)
  | io (detail : String)
  deriving Repr

def SealFault.name : SealFault → String
  | .worldTooLarge _ => "worldTooLarge"
  | .indexTooLarge _ => "indexTooLarge"
  | .entryUnfit _ => "entryUnfit"
  | .indexMoved _ _ => "indexMoved"
  | .io _ => "io"

/-- The base file's bytes for `w` at the segment position `seg`, counting the entries `index`
names, or why not. The size is checked before anything is encoded. -/
def Base.file {W : Type} (keys : Keys) (c : Cadence) (world : Stream W) (w : W) (seg : Position)
    (index : IndexAt) : Except SealFault ByteArray :=
  if c.worldBytesMax < world.size w then .error (.worldTooLarge (world.size w)) else
  .ok (Log.frame keys.base baseInitial
    (keys.shapes.bytes ++ (Base.codec world).bytes ⟨w, seg.offset, seg.tag, index.count, index.last⟩))

/-- The entries a seal appends to `index.log` after the `ix.count` already there, and what the base
names after them; no entries, no bytes. Refuses, before encoding, an entry outside the layout
(`entryUnfit`, `Entry.fits`) and a count past `indexMax` (`indexTooLarge`), so the bytes it
returns read back, entry by entry and position by position, as exactly these entries
(`Host.Proofs.Base.run_read`). -/
def Base.entries (keys : Keys) (ix : IndexAt) (es : Array Entry) : Except SealFault (ByteArray × IndexAt) :=
  match es.toList.findIdx? (fun e => !e.fits keys.chainBytes) with
  | some i => .error (.entryUnfit i)
  | none =>
  if indexMax < ix.count + es.size then .error (.indexTooLarge (ix.count + es.size)) else
  match es.back? with
  | none => .ok (ByteArray.empty, ix)
  | some e => .ok (Entry.run keys ix.count es.toList, ⟨ix.count + es.size, e.tag keys (ix.count + es.size - 1)⟩)

/-- The `index.log` bytes successive seals append from `ix`, one `Base.entries` per seal, and what
the last base names: what `Host.Proofs.Index.entriesSeq_read` reads back. -/
def Base.entriesSeq (keys : Keys) : IndexAt → List (Array Entry) → Except SealFault (ByteArray × IndexAt)
  | ix, [] => .ok (ByteArray.empty, ix)
  | ix, es :: ess =>
    match Base.entries keys ix es with
    | .error f => .error f
    | .ok (p, ix') =>
      match Base.entriesSeq keys ix' ess with
      | .error f => .error f
      | .ok (ps, ix'') => .ok (p ++ ps, ix'')

/-- What one seal writes, checked before anything is written: that `index.log` (`indexSize` bytes
now) ends exactly where the entries the newest base counts end (`ix.count · entryBytes`), so
the entries appended at the file's end sit at the positions their tags name (`indexMoved`
otherwise); the World's size; then the entries since the last base, then the base counting them.
Both checkpoints (files, memory) seal through this one function. -/
def Base.seal {W : Type} (keys : Keys) (c : Cadence) (world : Stream W) (w : W) (seg : Position) (ix : IndexAt)
    (entries : Array Entry) (indexSize : Nat) : Except SealFault (ByteArray × IndexAt × ByteArray) :=
  if indexSize ≠ ix.count * entryBytes keys then .error (.indexMoved indexSize (ix.count * entryBytes keys)) else
  if c.worldBytesMax < world.size w then .error (.worldTooLarge (world.size w)) else
  match Base.entries keys ix entries with
  | .error f => .error f
  | .ok (page, ix') =>
    match Base.file keys c world w seg ix' with
    | .error f => .error f
    | .ok file => .ok (page, ix', file)

/-- A Store as genesis writes it, before any file exists: the segment holding ONE frame, the
ORIGIN frame `Log.frame keys.segment segmentInitial origin` whose record is the genesis World's
chain (`(mark w₀).2`: the Store's identity at step 0), and the base of `w₀` at that frame's end,
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

/-- A file every Store directory holds (a row of `Store.layout`, `base.tmp` aside). -/
inductive StorePart where
  | key
  | segment
  | index
  | base
  deriving DecidableEq, Repr

/-- The file's name in the Store directory. -/
def StorePart.name : StorePart → String
  | .key => "key"
  | .segment => "seg.log"
  | .index => "index.log"
  | .base => "base.world"

/-- Every file a Store holds, in the order the open checks them. -/
def StorePart.all : List StorePart := [.key, .segment, .index, .base]

namespace Store

/-- Every file of a Store directory, in the order genesis writes them. A seal appends its entries
to `index.log` and syncs them before `base.tmp` is renamed over `base.world`; a batch is appended
to `seg.log` and synced before it is answered. -/
def layout : List StoreFile :=
  [⟨StorePart.key.name, .once, "32 bytes, mode 0600: the integrity-at-rest key (HOST-16)"⟩,
   ⟨StorePart.segment.name, .appendOnly, "the frames (Host.Log) from genesis's origin frame: one batch record per frame; its append handle is flock'd, the writer lock"⟩,
   ⟨StorePart.index.name, .appendOnly, "fixed-width keyed entries, one per record before the newest base, each tagged with its position: what log pages binary-search (HOST-33)"⟩,
   ⟨StorePart.base.name, .replaced, "the newest sealed base: the World, the seg.log position after it, and how many index.log entries it counts with the last one's tag"⟩,
   ⟨"base.tmp", .transient, "a base being installed; a crash may leave one, which no open reads"⟩]

/-- The order a backup copies a LIVE Store's files in: the key, then the base, then the
append-only files, so each append-only copy is at least as long as the prefix the copied base
names (a longer one is a torn tail or orphan entries, which an open handles). -/
def backupOrder : List String := [StorePart.key, .base, .index, .segment].map (·.name)

end Store

/-- Why a Store's base does not open (law 7). -/
inductive BaseFault where
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
  /-- `index.log` is shorter than the entries the base counts (`indexCount · entryBytes`): a copy
  cut short, or the file truncated (HOST-30) -/
  | indexShort (size offset : Nat)
  /-- the last entry the base counts does not read back as an entry at its position under this
  Store's key (`Entry.read`), or its tag is not the `indexLast` the base names (HOST-33: the one
  entry open reads; `host check` reads them all) -/
  | indexCorrupt
  deriving Repr

def BaseFault.name : BaseFault → String
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

/-- Where the last entry of `count` sits in `index.log`, and how many bytes open reads there: one
entry, or none at count 0. -/
def lastAt (keys : Keys) (count : Nat) : Nat × Nat :=
  if count = 0 then (0, 0) else ((count - 1) * entryBytes keys, entryBytes keys)

/-- The one index check open makes (HOST-33), over the bytes `lastAt` read: at count 0 nothing,
and the base names no last tag; otherwise those bytes read back as entry `count - 1` at its own
position (`Entry.read`), and its tag is the `indexLast` the base names. The entries before it are
checked when a page reads them (`Host.Page.entryAt`) and by `host check` (`indexClean`). -/
def indexNamed (keys : Keys) (count : Nat) (last : Digest) (bytes : ByteArray) : Option BaseFault :=
  if count = 0 then (if last = Digest.zero then none else some .indexCorrupt) else
  match Entry.read keys (count - 1) bytes with
  | none => some .indexCorrupt
  | some e => if e.tag keys (count - 1) = last then none else some .indexCorrupt

/-- `host check`'s whole-index audit (HOST-33 condition 1): `bytes` are the entries a base counts,
`offsets` the offsets of the record frames before its offset (`Log.recover` of the history, the
origin frame left out). There are as many as the base counts, `bytes` is exactly them, every
entry reads back at its position (`Entry.read`), names its record's offset, and its step count does
not fall. The first entry that fails, or none. -/
def indexClean (keys : Keys) (bytes : ByteArray) (count : Nat) (offsets : List Nat) : Option Nat :=
  if offsets.length ≠ count ∨ bytes.size ≠ count * entryBytes keys then some (min count offsets.length) else
  go 0 0 offsets
where
  go : Nat → Nat → List Nat → Option Nat
    | _, _, [] => none
    | k, h, off :: rest =>
      match Entry.read keys k (bytes.extract (k * entryBytes keys) (k * entryBytes keys + entryBytes keys)) with
      | some e => if e.offset = off ∧ h ≤ e.steps then go (k + 1) e.steps rest else some k
      | none => some k

/-- The offsets of the record frames `Log.recover` finds in a segment prefix, the origin frame
(the first) left out: what entry k of the index must name (`indexClean`). -/
def recordOffsets (records : List ByteArray) : List Nat :=
  ((records.foldl (fun (acc : Nat × List Nat) r => (acc.1 + 4 + r.size + Log.tagBytes, acc.1 :: acc.2)) (0, [])).2.reverse).drop 1

/-- How many segment bytes open reads after a base at `offset` whose World is `baseBytes` long,
in a segment of `size` bytes. -/
def tailRead (c : Cadence) (baseBytes offset size : Nat) : Except BaseFault Nat :=
  if size < offset then .error (.segmentShort size offset)
  else if c.tailMax baseBytes < size - offset then .error (.tailTooLong (size - offset) (c.tailMax baseBytes))
  else .ok (size - offset)

/-! ## The seal policy: a pure function the loop calls -/

/-- The newest durable base, as the loop counts it: the segment offset it starts from, its World's
encoded size, step count (its position in the log, `Recorder.mark`) and chain (`Env.bytes`), and
the digest of its World bytes (what `read` pages state, HOST-15). -/
structure Sealed where
  offset : Nat
  bytes : Nat
  steps : Nat
  chain : ByteArray
  digest : ByteArray
  /-- the entries of `index.log` this base counts, and the last one's tag: the next seal's
  entries start at `index.count` (HOST-33) -/
  index : IndexAt

/-- The bytes of the frame holding `record`. -/
def frameSize (record : ByteArray) : Nat := 4 + record.size + Log.tagBytes

/-- After a commit that reached `pos`: start a seal in the background? -/
def shouldSeal (c : Cadence) (sealed : Sealed) (pending : Bool) (pos : Nat) : Bool :=
  !pending && decide (c.cadence sealed.bytes ≤ pos - sealed.offset)

end Nanodregg.Host
