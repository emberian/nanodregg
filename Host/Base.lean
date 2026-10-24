/-
# Host.Base — the sealed whole-World base, and what open reads (HOST-14)

    STORE/base.world = one Log frame (under the base sealer) of
                       shapes32 ‖ world bytes ‖ u64 offset ‖ tag32 ‖ u64 indexCount ‖ indexLast32 ‖
                       u64 retainedFrom ‖ u64 indexFrom (`Base.codec`, HOST-64), the file then
                       carrying `Host.Physical`'s u64 generation ‖ mac32 trailer (HOST-71)
    STORE/index.<k0>.log = fixed-width ENTRIES, one per record before the newest base, entry k at
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

`offset` is where in the (logical) segment the batches after this World begin, and `tag` is the segment's
chain tag there (the `prev` of the frame at `offset`). `indexCount` is how many entries of
the index file index the records before `offset`, and `indexLast` is the tag of the last of them
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

Open reads the base (at most `Log.frameMax c.baseRecordMax` bytes), the checkpoint header of the
base's own segment file (`Host.Open.headerFault`, HOST-64: it verifies, states the genesis chain of
the base World's origin, HOST-25, which the origin frame at offset 0 carried before a Store could drop
the files holding it, and the base's own position), the base's last index entry
(`entryBytes`), the record that entry names (at most a frame and a tag, checked to be the frame
ending at `offset`, `lastFrame`, HOST-63; a base counting none must sit at the origin frame's end,
HOST-65), and the segment from `offset`, and `tailRead` refuses a tail longer than
`c.tailMax` by name (`tailTooLong`), so open reads one base, one entry, its record, and at most two cadences and
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
the index file index the records before it (so `log` can page from any step without reading the
segment from 0), with the last one's tag. -/
structure Base (W : Type) where
  world : W
  offset : Nat
  tag : Digest
  /-- the entries of the index file that index the records before `offset` -/
  indexCount : Nat
  /-- the tag of entry `indexCount - 1` (`Digest.zero` at count 0) -/
  indexLast : Digest
  /-- the logical offset of the oldest segment file the Store keeps (`seg.<retainedFrom>.log`; 0 while
  it keeps its whole history, HOST-64) -/
  retainedFrom : Nat
  /-- the first index entry the Store keeps: the index file is `index.<indexFrom>.log` (HOST-64) -/
  indexFrom : Nat

/-- The most entries an index file holds: a Store's lifetime in records. It bounds a page's
binary search at 33 entry reads (HOST-33: `indexTooLarge` past it). -/
def indexMax : Nat := 2 ^ 32 - 1

/-- The base record's codec, over the World's. It refuses, by its label, a base keeping a segment
file past its own offset or an index entry past its count (HOST-64: `Base.file` never writes one,
`positionUnfit`), so every base that decodes keeps only what precedes it (`Base.codec_decode_keep`). -/
def Base.codec {W : Type} (world : Stream W) : Stream (Base W) :=
  Stream.refine "host/base/retained"
    (Stream.product world (Stream.product Stream.nat64 (Stream.product Stream.digest
      (Stream.product Stream.nat64 (Stream.product Stream.digest (Stream.product Stream.nat64 Stream.nat64))))))
    (fun (w, o, t, ic, il, rf, k0) => if rf ≤ o ∧ k0 ≤ ic then some ⟨w, o, t, ic, il, rf, k0⟩ else none)
    (fun b => (b.world, b.offset, b.tag, b.indexCount, b.indexLast, b.retainedFrom, b.indexFrom))

/-- The layout of a segment file's checkpoint header (`Host.Segment`), as a version the shape stamp
covers: fixed-width bytes, not a CODEC stream, so its layout enters the stamp by name (HOST-64). -/
def headerLayout : String :=
  "host/segment/header/v2: physical base and header append u64 generation and domain-separated mac32; identity = generation*2^64+start; logical u64 start, u64 steps, u64 indexCount, u64 prev, tag32, origin, chain, mac32 under the checkpoint sealer"

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
    entryLayout.toUTF8 ++ headerLayout.toUTF8)

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

/-- What a base names of the index file: how many entries index the records before its offset, and
the tag of the last of them (HOST-33). -/
structure IndexAt where
  count : Nat
  last : Digest

/-- An empty index file: no entry, no last tag. -/
def indexStart : IndexAt := ⟨0, Digest.zero⟩

/-- The keyed tags of one Store (its segment frames and its base, under separate domains), and the
UNKEYED digest of a base's World bytes, which a thin member pins (HOST-15). -/
structure Keys where
  segment : Log.Sealer
  base : Log.Sealer
  /-- the entries of the index file (HOST-30, HOST-33) -/
  index : Log.Sealer
  /-- the checkpoint header of each segment file (HOST-64) -/
  checkpoint : Log.Sealer
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

/-! ## A segment file's checkpoint header (HOST-64; `Host.Segment`) -/

/-- A segment file's checkpoint header. -/
structure Header where
  start : Nat
  steps : Nat
  indexCount : Nat
  prev : Nat
  tag : Digest
  origin : ByteArray
  chain : ByteArray

/-- What the header's tag covers. -/
def Header.body (h : Header) : ByteArray :=
  Stream.nat64.bytes h.start ++ Stream.nat64.bytes h.steps ++ Stream.nat64.bytes h.indexCount ++
    Stream.nat64.bytes h.prev ++ h.tag.bytes ++ h.origin ++ h.chain

/-- A header the layout can hold at chain width `w`. -/
def Header.fits (w : Nat) (h : Header) : Bool :=
  decide (h.start < 2 ^ 64) && decide (h.steps < 2 ^ 64) && decide (h.indexCount < 2 ^ 64) &&
    decide (h.prev < 2 ^ 64) && decide (h.origin.size = w) && decide (h.chain.size = w)

/-- The header's bytes on disk: its body, then the checkpoint sealer's tag over it. -/
def Header.bytes (keys : Keys) (h : Header) : ByteArray :=
  h.body ++ (tagDigest keys.checkpoint h.body).bytes

/-- The bytes of a header at the Store's chain width. -/
def headerBytes (keys : Keys) : Nat := 64 + 2 * keys.chainBytes + Log.tagBytes

/-- The header `b` holds, or none: the header its fields spell, accepted only if `Header.bytes` of
it is exactly `b` (its tag verified, and `b` is that header's one spelling). -/
def Header.read (keys : Keys) (b : ByteArray) : Option Header :=
  match Stream.nat64.decode (b.extract 0 8), Stream.nat64.decode (b.extract 8 16),
      Stream.nat64.decode (b.extract 16 24), Stream.nat64.decode (b.extract 24 32),
      Digest.ofBytes? (b.extract 32 64) with
  | .ok s, .ok st, .ok ic, .ok p, some t =>
    let w := keys.chainBytes
    let h : Header := ⟨s, st, ic, p, t, b.extract 64 (64 + w), b.extract (64 + w) (64 + 2 * w)⟩
    if Header.bytes keys h = b then some h else none
  | _, _, _, _, _ => none

/-- The header of the file a seal starts at `pos`, the World there marked `mark`, after `count`
entries, the newest file before it starting at `prev`. -/
def Header.at (pos : Position) (mark : Nat × ByteArray) (count prev : Nat) (origin : ByteArray) : Header :=
  ⟨pos.offset, mark.1, count, prev, pos.tag, origin, mark.2⟩

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

/-- Entries `k, k+1, …` as the index file holds them, from byte `k · entryBytes`. -/
def Entry.run (keys : Keys) : Nat → List Entry → ByteArray
  | _, [] => ByteArray.empty
  | k, e :: es => Entry.bytes keys k e ++ Entry.run keys (k + 1) es

/-- Why a seal did not produce a base (law 7). -/
inductive SealFault where
  /-- the World encodes to more than `worldBytesMax`: the size at which HOST-14 must change -/
  | worldTooLarge (bytes : Nat)
  /-- the index file would hold more than `indexMax` entries with this seal's: the Store's lifetime
  in records (HOST-33; before it, the index's bytes against `worldBytesMax`) -/
  | indexTooLarge (count : Nat)
  /-- the `index`-th entry a seal is handed is outside the entry layout (`Entry.fits`: a u64
  height or offset, a chain of the Store's width): it would not read back as written.
  Unreachable at the deployed chain (32 bytes, `Kernel` digests); a defect -/
  | entryUnfit (index : Nat)
  /-- the segment position the base would name is at or past 2^64: the base layout writes it as a
  u64 its reader (`Base.read`) would refuse, so the writer refuses it first (HOST-41's law: every
  encode on a write path refuses over the bound its decode enforces). Unreachable for a position
  inside a segment the process could hold; a defect, the same class as `entryUnfit`. Also: the
  newest segment file already starts at that position and its header does not state it (the seal's
  World's step count and chain, the entries before it, the Store's origin: `headerFault`), so the base
  could not name that file (`Checkpoint.rotate`'s reuse, HOST-64 F6) -/
  | positionUnfit (offset : Nat)
  /-- the index file is `size` bytes, not `offset`, the end of the entries the newest base counts:
  entries appended now would land elsewhere than the positions their tags name. Another process
  wrote or truncated the file; a restart's open truncates orphans or refuses `indexShort` -/
  | indexMoved (size offset : Nat)
  | io (detail : String)
  deriving Repr

def SealFault.name : SealFault → String
  | .worldTooLarge _ => "worldTooLarge"
  | .indexTooLarge _ => "indexTooLarge"
  | .entryUnfit _ => "entryUnfit"
  | .positionUnfit _ => "positionUnfit"
  | .indexMoved _ _ => "indexMoved"
  | .io _ => "io"

/-- What a base keeps of the files before it (HOST-64): the oldest segment file and the first index
entry. `⟨0, 0⟩` keeps everything. -/
structure Keep where
  retainedFrom : Nat
  indexFrom : Nat

/-- Keep everything: the default, and every Store genesis writes. -/
def Keep.all : Keep := ⟨0, 0⟩

/-- The base file's bytes for `w` at the segment position `seg`, keeping `keep` (a retained offset
past the base's own is refused `positionUnfit`: the base would name no file it sits in), counting the entries `index`
names, or why not. The size, then the position's u64 bound (`positionUnfit`, the bound `Base.read`
enforces on the offset), are checked before anything is encoded. -/
def Base.file {W : Type} (keys : Keys) (c : Cadence) (world : Stream W) (w : W) (seg : Position)
    (index : IndexAt) (keep : Keep) : Except SealFault ByteArray :=
  if c.worldBytesMax < world.size w then .error (.worldTooLarge (world.size w)) else
  if 2 ^ 64 ≤ seg.offset then .error (.positionUnfit seg.offset) else
  if seg.offset < keep.retainedFrom ∨ index.count < keep.indexFrom then .error (.positionUnfit keep.retainedFrom) else
  .ok (Log.frame keys.base baseInitial
    (keys.shapes.bytes ++ (Base.codec world).bytes
      ⟨w, seg.offset, seg.tag, index.count, index.last, keep.retainedFrom, keep.indexFrom⟩))

/-- The entries a seal appends to the index file after the `ix.count` already there, and what the base
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

/-- The index file bytes successive seals append from `ix`, one `Base.entries` per seal, and what
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

/-- What one seal writes, checked before anything is written: that the index file (`indexSize` bytes
now) ends exactly where the entries the newest base counts end (`ix.count · entryBytes`), so
the entries appended at the file's end sit at the positions their tags name (`indexMoved`
otherwise); the World's size; then the entries since the last base, then the base counting them.
Both checkpoints (files, memory) seal through this one function. -/
def Base.seal {W : Type} (keys : Keys) (c : Cadence) (world : Stream W) (w : W) (seg : Position) (ix : IndexAt)
    (entries : Array Entry) (indexSize : Nat) (keep : Keep) : Except SealFault (ByteArray × IndexAt × ByteArray) :=
  if indexSize ≠ ix.count * entryBytes keys then .error (.indexMoved indexSize (ix.count * entryBytes keys)) else
  if c.worldBytesMax < world.size w then .error (.worldTooLarge (world.size w)) else
  match Base.entries keys ix entries with
  | .error f => .error f
  | .ok (page, ix') =>
    match Base.file keys c world w seg ix' keep with
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
  /-- the logical segment: the origin frame -/
  segment : ByteArray
  base : ByteArray
  /-- `index.0.log` at genesis: empty (no record precedes the origin) -/
  index : ByteArray
  /-- `seg.0.log`'s checkpoint header (the origin frame's file, HOST-64) -/
  header0 : ByteArray
  /-- the header of the base's own file, `seg.<segment.size>.log`, whose body is empty -/
  header : ByteArray

def genesisImage {W : Type} (keys : Keys) (c : Cadence) (world : Stream W)
    (mark : W → Nat × ByteArray) (w₀ : W) : Except SealFault Image :=
  let origin := (mark w₀).2
  let segment := Log.frame keys.segment segmentInitial origin
  let pos : Position := ⟨segment.size, tagDigest keys.segment (segmentInitial ++ origin)⟩
  match Base.file keys c world w₀ pos indexStart Keep.all with
  | .error f => .error f
  | .ok base => .ok ⟨segment, base, ByteArray.empty,
      Header.bytes keys (Header.at ⟨0, Digest.zero⟩ (mark w₀) 0 0 origin),
      Header.bytes keys (Header.at pos (mark w₀) 0 0 origin)⟩

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
  /-- the segment file with physical identity `start` (HOST-71); its header names the logical offset -/
  | segment (start : Nat)
  /-- the index file holding entries from `k0` (HOST-64) -/
  | index (k0 : Nat)
  | base
  deriving DecidableEq, Repr

/-- The file's name in the Store directory. -/
def StorePart.name : StorePart → String
  | .key => "key"
  | .segment o => s!"seg.{o}.log"
  | .index k0 => s!"index.{k0}.log"
  | .base => "base.world"

/-- The file's FAMILY as the layout and the runbook name it: a segment file is `seg.<o>.log` whatever
its physical identity, an index file `index.<k0>.log`. -/
def StorePart.pattern : StorePart → String
  | .key => "key"
  | .segment _ => "seg.<o>.log"
  | .index _ => "index.<k0>.log"
  | .base => "base.world"

/-- One part of each family, in the order the open checks them (a check over a family names its
member at the place: `missing seg.<o>.log` with the physical identity). -/
def StorePart.families : List StorePart := [.key, .segment 0, .index 0, .base]

namespace Store

/-- Every file of a Store directory, in the order genesis writes them (a pattern names a family:
`<o>` a segment file's physical identity, `<k0>` the first index entry the base keeps). A seal appends its
entries to the index file and syncs them before `base.tmp` is renamed over `base.world`; a batch is
appended to the newest segment file and synced before it is answered; a seal starts a new segment
file first (HOST-64). -/
def layout : List StoreFile :=
  [⟨StorePart.key.name, .once, "32 bytes, mode 0600: the integrity-at-rest key (HOST-16); its read handle is flock'd, the writer lock"⟩,
   ⟨(StorePart.segment 0).pattern, .appendOnly, "an authenticated physical header (Host.Physical), then frames (Host.Log) from the header's logical start; o is generation * 2^64 + start, not a logical offset; the atomic base selects the generation; only its newest file is appended to; adoption creates a fresh generation without replacing old headers; retention drops files before retainedFrom in the selected generation"⟩,
   ⟨(StorePart.index 0).pattern, .appendOnly, "fixed-width keyed entries k0, k0+1, ..., one per record before the newest base, each tagged with its position: what log pages binary-search (HOST-33); k0 is the base's indexFrom, 0 unless a drop moved it"⟩,
   ⟨StorePart.base.name, .replaced, "the newest sealed base: the World, logical segment position, index count and last tag, retainedFrom and indexFrom, plus the authenticated generation selecting its physical segment files; the complete base is published atomically"⟩,
   ⟨"base.tmp", .transient, "a base being installed; a crash may leave one, which no open reads"⟩,
   ⟨"seg.tmp", .transient, "a segment file being started; a crash may leave one, which no open reads"⟩,
   ⟨"index.tmp", .transient, "a kept index being written by a drop; a crash may leave one, which no open reads"⟩]

/-- The order a backup copies a LIVE Store's files in: the key, then the base, then the
append-only files (the index file the base names, then the segment files from its retainedFrom,
oldest first), so each append-only copy is at least as long as the prefix the copied base names (a
longer one is a torn tail or orphan entries, which an open handles). -/
def backupOrder : List String := [StorePart.key, .base, .index 0, .segment 0].map (·.pattern)

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
  genesis chain than the base World's origin (two Stores sharing a key file, one's segment files
  spliced over the other's; HOST-25) -/
  | foreignOrigin
  /-- the index file is shorter than the entries the base counts (`indexCount · entryBytes`): a copy
  cut short, or the file truncated (HOST-30) -/
  | indexShort (size offset : Nat)
  /-- the last entry the base counts does not read back as an entry at its position under this
  Store's key (`Entry.read`), or its tag is not the `indexLast` the base names (HOST-33: the one
  entry open reads; `host check` reads them all), or its record does not begin before the base's
  World (its step count is not below the base's, HOST-53), or the record it names is not the frame
  that ends at the base's offset (`lastFrame`, HOST-63), or the base counts none and does not sit at
  the origin frame's end (HOST-65) -/
  | indexCorrupt
  /-- the base's own segment file is shorter than a checkpoint header, or its header does not verify
  under the Store's key (HOST-64) -/
  | checkpointCorrupt
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
  | .checkpointCorrupt => "checkpointCorrupt"

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

/-- Where the last entry of `count` sits in the index file, and how many bytes open reads there: one
entry, or none at count 0. -/
def lastAt (keys : Keys) (count : Nat) : Nat × Nat :=
  if count = 0 then (0, 0) else ((count - 1) * entryBytes keys, entryBytes keys)

/-- The one index check open makes (HOST-33), over the bytes `lastAt` read: at count 0 nothing,
and the base names no last tag; otherwise those bytes read back as entry `count - 1` at its own
position (`Entry.read`), its tag is the `indexLast` the base names, and its record began before
the base's World (`e.steps < before`, `before` the base World's step count, HOST-53: every record
moves the step count, so a base at step 0 counts no entry, `Host.Deployed.openWith_steps_zero`).
The entries before it are checked when a page reads them (`Host.Page.entryAt`) and by `host check`
(`indexClean`). -/
def indexNamed (keys : Keys) (count : Nat) (last : Digest) (before : Nat) (bytes : ByteArray) :
    Option BaseFault :=
  if count = 0 then (if last = Digest.zero then none else some .indexCorrupt) else
  match Entry.read keys (count - 1) bytes with
  | none => some .indexCorrupt
  | some e => if e.tag keys (count - 1) = last ∧ e.steps < before then none else some .indexCorrupt

/-- The last entry of `count`, as `lastAt`'s bytes hold it at its position: none at count 0 (and
none when it does not read back, which `indexNamed` has already refused). -/
def lastEntry (keys : Keys) (count : Nat) (bytes : ByteArray) : Option Entry :=
  if count = 0 then none else Entry.read keys (count - 1) bytes

/-- The segment range open reads for the base's last entry `e` (HOST-63): from the 32 bytes before
the entry's offset (the tag its frame chains from) to the base's offset, or none when the entry
does not name a place one frame before the base: its offset less than 32 bytes into the segment (no tag before it to chain from), at
or past the base, or more than one frame (`Log.frameMax recordMax`) before it. -/
def lastRange (recordMax offset : Nat) (e : Entry) : Option (Nat × Nat) :=
  if Log.tagBytes ≤ e.offset ∧ e.offset < offset ∧ offset - e.offset ≤ Log.frameMax recordMax then
    some (e.offset - Log.tagBytes, offset - e.offset + Log.tagBytes)
  else none

/-- The check open makes on the record the base's last entry names (HOST-63, HOST-53's alternative
(d)), over the bytes `lastRange` read: the frame after their first 32 bytes verifies against them
under the segment sealer and ends exactly at their end, the base's offset. So the one entry open
reads names a frame that verifies and ends at the base's offset (`indexCorrupt` otherwise). -/
def lastFrame (s : Log.Sealer) (recordMax : Nat) (bytes : ByteArray) : Option BaseFault :=
  match Log.frameAt s recordMax bytes Log.tagBytes (bytes.extract 0 Log.tagBytes) with
  | some rd => if rd.next = bytes.size then none else some .indexCorrupt
  | none => some .indexCorrupt

/-- `host check`'s whole-index audit (HOST-33 condition 1): `bytes` are the entries a base counts,
`offsets` the offsets of the record frames before its offset (`Log.recover` of the history, the
origin frame left out). There are as many as the base counts, `bytes` is exactly them, every
entry reads back at its position (`Entry.read`), names its record's offset, and its step count does
not fall; and the first kept entry's step count is `steps`, the oldest kept file's header's (HOST-68:
the run begins at the step count the header states; `Host.Proofs.StoreIndex`). The first entry that
fails, or none. -/
def indexClean (keys : Keys) (bytes : ByteArray) (k0 count : Nat) (offsets : List Nat) (steps : Nat) : Option Nat :=
  if k0 + offsets.length ≠ count ∨ bytes.size ≠ (count - k0) * entryBytes keys then
    some (k0 + min (count - k0) offsets.length) else
  match offsets with
  | [] => none
  | _ :: _ =>
    -- the first kept entry's record is the first after the oldest kept file's header, which states
    -- the step count there (HOST-68): entry k0 claims exactly it, or is refused at k0
    match Entry.read keys k0 (bytes.extract 0 (entryBytes keys)) with
    | some e => if e.steps = steps then go k0 0 offsets else some k0
    | none => some k0
where
  go : Nat → Nat → List Nat → Option Nat
    | _, _, [] => none
    | k, h, off :: rest =>
      match Entry.read keys k (bytes.extract ((k - k0) * entryBytes keys) ((k - k0) * entryBytes keys + entryBytes keys)) with
      | some e => if e.offset = off ∧ h ≤ e.steps then go (k + 1) e.steps rest else some k
      | none => some k

/-- The logical offsets of the record frames `Log.recover` finds in segment bytes starting at
`start`. -/
def recordOffsetsFrom (start : Nat) (records : List ByteArray) : List Nat :=
  (records.foldl (fun (acc : Nat × List Nat) r => (acc.1 + 4 + r.size + Log.tagBytes, acc.1 :: acc.2)) (start, [])).2.reverse

/-- The offsets of the record frames `Log.recover` finds in a segment prefix from 0, the origin
frame (the first) left out: what entry k of the index must name (`indexClean`). -/
def recordOffsets (records : List ByteArray) : List Nat := (recordOffsetsFrom 0 records).drop 1

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
  /-- the entries of the index file this base counts, and the last one's tag: the next seal's
  entries start at `index.count` (HOST-33) -/
  index : IndexAt

/-- The bytes of the frame holding `record`. -/
def frameSize (record : ByteArray) : Nat := 4 + record.size + Log.tagBytes

/-- After a commit that reached `pos`: start a seal in the background? -/
def shouldSeal (c : Cadence) (sealed : Sealed) (pending : Bool) (pos : Nat) : Bool :=
  !pending && decide (c.cadence sealed.bytes ≤ pos - sealed.offset)

end Nanodregg.Host
