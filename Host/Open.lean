/-
# Host.Open — what a Store opens to

    openLog s recordMax step w₀ initial log

reads the segment bytes after a base (`initial` is the tag they chain from, `w₀` the base's World)
with `Log.recover`, and folds every verifying record with `step` (for the Host: decode the batch
record and `World.admit` each Turn, then check the chain the record states). Nothing else
advances a World on open (HOST-14: there are no deltas).

* `corrupt off` — a frame verifies after bad bytes: acknowledged data follows, so the Store does
  not open and nothing is truncated (HOST-12);
* `record i f` — the `i`-th verifying record does not fold: written by a different build or a
  different kernel, refused by name, never skipped;
* otherwise the World, the frame count, where the valid bytes end, the tag to chain the next
  frame from, and `torn`: the bytes past `validLen` that are the one unsynced frame. The writer
  truncates them; a follower never does (it reads them as "not yet written").

The follower and the reopening writer run this same function: one open, one fold.

Before the tail is folded, the one open (`openWith`) checks the checkpoint header of the base's own
segment file (`headerFault`, HOST-64): it must verify (`checkpointCorrupt`), state the genesis chain
of the base World's origin (`foreignOrigin`, HOST-25, which the origin frame at offset 0 carried
before a Store could drop the files holding it) and the base's own position (`foreignSegment`). Its theorems are in
`Host.Proofs.Base`. Every `corrupt` offset the open reports is absolute in the segment.

Theorems (`Host.Proofs.Open`): `open_encodeAll` (a clean segment opens to the fold of exactly the
records written), `open_torn` (a segment whose last frame was cut opens to the fold of the frames
before it, `torn` = the cut), and `open_sound` (for ANY bytes, the World opened is the fold of
records that are literally the bytes before `validLen`).
-/
import Host.Segment

namespace Nanodregg.Host

/-- Why a Store does not open (law 7). -/
inductive OpenFault (F : Type) where
  /-- bad bytes at `offset` with a verifying frame after them -/
  | corrupt (offset : Nat)
  /-- the `index`-th verifying record does not fold -/
  | record (index : Nat) (fault : F)
  deriving Repr

structure Opened (W : Type) where
  world : W
  records : Nat
  validLen : Nat
  lastTag : ByteArray
  /-- the torn tail's length past `validLen` (0 when the segment ends clean) -/
  torn : Nat

variable {W F : Type}

/-- Fold the records in order; a refusal names the record's index. -/
def foldRecords (step : W → ByteArray → Except F W) : W → Nat → List ByteArray → Except (OpenFault F) W
  | w, _, [] => .ok w
  | w, i, r :: rs =>
    match step w r with
    | .ok w' => foldRecords step w' (i + 1) rs
    | .error f => .error (.record i f)

def tornOf : Log.Tail → Nat
  | .torn n => n
  | _ => 0

def openLog (s : Log.Sealer) (recordMax : Nat) (step : W → ByteArray → Except F W) (w₀ : W)
    (initial log : ByteArray) : Except (OpenFault F) (Opened W) :=
  let rv := Log.recover s recordMax initial log
  match rv.tail with
  | .corrupt off => .error (.corrupt off)
  | tail =>
    match foldRecords step w₀ 0 rv.records with
    | .ok w => .ok ⟨w, rv.records.length, rv.validLen, rv.lastTag, tornOf tail⟩
    | .error e => .error e

/-- Why a Store does not open (law 7). -/
inductive StoreFault (F : Type) where
  /-- another writer holds the segment's lock -/
  | locked
  /-- genesis on a directory that already holds a Store file -/
  | exists
  /-- the key file is not exactly 32 bytes -/
  | badKey (bytes : Nat)
  /-- `file` is absent from an existing STORE directory: refused before any handle opens, so no
  open, append or truncate ever re-creates it (HOST-35) -/
  | missing (file : StorePart)
  /-- a read returned fewer bytes than the size said: the file changed under us -/
  | shortRead (got want : Nat)
  | base (fault : BaseFault)
  | log (fault : OpenFault F)
  /-- genesis could not seal its base -/
  | seal (fault : SealFault)
  /-- the opened chain tag is not 32 bytes (a broken `Sealer`) -/
  | tagWidth
  deriving Repr

def StoreFault.name {F : Type} : StoreFault F → String
  | .locked => "locked"
  | .exists => "exists"
  | .badKey _ => "badKey"
  | .missing _ => "missing"
  | .shortRead _ _ => "shortRead"
  | .base f => f.name
  | .log (.corrupt _) => "corrupt"
  | .log (.record _ _) => "record"
  | .seal f => f.name
  | .tagWidth => "tagWidth"

/-- The refusal as stderr states it: the name, and for `missing` the file (one status, one name;
the file is the operator's detail). -/
def StoreFault.text {F : Type} : StoreFault F → String
  | .missing f => "missing " ++ f.name
  | f => f.name

/-- What the one open reads: the base, and the World the segment after it folds to. -/
structure Opening (W : Type) where
  opened : Opened W
  /-- the base's offset, and its World's encoded size -/
  sealed : Sealed
  /-- where the valid segment ends (absolute), and its chain tag -/
  pos : Position
  /-- one entry per record of the tail: the entries since the base (the base's own are on disk,
  `sealed.index.count` of them; HOST-33) -/
  index : Array Entry
  /-- the index file bytes past the entries the base counts: orphan entries of a seal whose base
  never landed. The writer truncates them; a follower ignores them (HOST-30) -/
  orphan : Nat

/-- Fold one record and index it: the World's mark before it, at the frame's offset. -/
def indexed (mark : W → Nat × ByteArray) (step : W → ByteArray → Except F W) :
    W × Array Entry × Nat → ByteArray → Except F (W × Array Entry × Nat)
  | (w, idx, off), r => do
    let w' ← step w r
    let (h, chain) := mark w
    pure (w', idx.push ⟨h, off, chain⟩, off + frameSize r)

/-- A log fault with its offset made absolute: `openLog` reads the tail from `base`. -/
def OpenFault.shift (base : Nat) : OpenFault F → OpenFault F
  | .corrupt off => .corrupt (base + off)
  | .record i f => .record i f

/-- The record check of the base's last entry (HOST-63): at count 0 the frame before the base is
the origin frame, so the base must sit at its end, `originEnd` (`indexCorrupt` otherwise, HOST-65:
entry 0 is then the Store's first record, `Host.Proofs.StoreIndex`); otherwise the entry's range
(`lastRange`, `indexCorrupt` when it names no place one frame before the base) read in one read,
`shortRead` when it comes back short, and `lastFrame` over it. -/
def lastFrameFault {m : Type → Type} [Monad m] (s : Log.Sealer) (recordMax originEnd offset : Nat)
    (e? : Option Entry) (readTail : Nat → Nat → m (Except (StoreFault F) ByteArray)) : m (Option (StoreFault F)) :=
  match e? with
  | none => pure (if offset = originEnd then none else some (.base .indexCorrupt))
  | some e =>
    match lastRange recordMax offset e with
    | none => pure (some (.base .indexCorrupt))
    | some (at_, len) => do
      match ← readTail at_ len with
      | .error f => pure (some f)
      | .ok fb =>
        if fb.size ≠ len then pure (some (.shortRead fb.size len)) else
        pure ((lastFrame s recordMax fb).map .base)

/-- The one open, given the base file's bytes, the segment's size and a reader of the segment
(`IO` over the file for `host`, `Id` over bytes in the simulation): verify and decode the base,
bound the tail (`tailRead`), read exactly that tail AND the 32 bytes before it in one read,
refuse `foreignSegment` unless those 32 bytes are the base's tag (every base sits after a frame
of its own segment: `genesisImage`, HOST-18), check `header`, the checkpoint header of the base's own
segment file, and refuse unless it verifies (`checkpointCorrupt`), states `origin b.world`, the
genesis chain of the base World's own origin (`foreignOrigin`, HOST-25: the origin frame at offset 0
said this before a Store could drop it), and states the base's own position (`foreignSegment`,
`headerFault`, HOST-64), refuse `indexShort` unless the index file (`indexSize`
bytes, `readIndex` its reader) holds every entry the base counts and `indexCorrupt` past
`indexMax`, read the ONE entry the base names last (`lastAt`) and refuse `indexCorrupt` unless it
reads back at its position with the base's `indexLast` and begins before the base's World
(`indexNamed`, HOST-33, HOST-53), read the record that entry names and refuse `indexCorrupt`
unless it is the frame ending at the base's offset, or, when the base counts none, unless the base
sits at the origin frame's end (`lastFrameFault`, HOST-63, HOST-65), and `openLog` the
tail from the base's World, indexing it from an empty Array (the entries since the base). Open
reads no other entry: a page checks the ones it reads, `host check` all of them. A `corrupt`
offset is absolute in the segment. -/
def openWith {m : Type → Type} [Monad m] (keys : Keys) (c : Cadence) (world : Codec.Stream W)
    (mark : W → Nat × ByteArray) (origin : W → ByteArray) (step : W → ByteArray → Except F W)
    (file header : ByteArray) (size : Nat) (indexSize : Nat)
    (readIndex : Nat → Nat → m (Except (StoreFault F) ByteArray))
    (readTail : Nat → Nat → m (Except (StoreFault F) ByteArray)) : m (Except (StoreFault F) (Opening W)) := do
  if Log.frameMax c.baseRecordMax < file.size then return .error (.base (.baseTooLarge file.size)) else
  match Base.read keys c world file with
  | .error e => return .error (.base e)
  | .ok (b, baseBytes, digest) =>
  match tailRead c baseBytes b.offset size with
  | .error e => return .error (.base e)
  | .ok len =>
  if b.offset < Log.tagBytes then return .error (.base .foreignSegment) else
  match ← readTail (b.offset - Log.tagBytes) (Log.tagBytes + len) with
  | .error e => return .error e
  | .ok read =>
  if read.size ≠ Log.tagBytes + len then return .error (.shortRead read.size (Log.tagBytes + len)) else
  if read.extract 0 Log.tagBytes ≠ b.tag.bytes then return .error (.base .foreignSegment) else
  match headerFault keys header (origin b.world) b.offset b.tag (mark b.world) b.indexCount with
  | some f => return .error (.base f)
  | none =>
  if indexMax < b.indexCount then return .error (.base .indexCorrupt) else
  if indexSize < b.indexCount * entryBytes keys then
    return .error (.base (.indexShort indexSize (b.indexCount * entryBytes keys))) else
  match ← readIndex (lastAt keys b.indexCount).1 (lastAt keys b.indexCount).2 with
  | .error e => return .error e
  | .ok ib =>
  if ib.size ≠ (lastAt keys b.indexCount).2 then return .error (.shortRead ib.size (lastAt keys b.indexCount).2) else
  match indexNamed (keys.forStore (origin b.world)) b.indexCount b.indexLast (mark b.world).1 ib with
  | some e => return .error (.base e)
  | none =>
  match ← lastFrameFault keys.segment c.recordBytesMax (frameSize (origin b.world)) b.offset
      (lastEntry (keys.forStore (origin b.world)) b.indexCount ib) readTail with
  | some f => return .error f
  | none =>
  let tail := read.extract Log.tagBytes read.size
  match openLog keys.segment c.recordBytesMax (indexed mark step) (b.world, #[], b.offset)
      b.tag.bytes tail with
  | .error e => return .error (.log (e.shift b.offset))
  | .ok o =>
    match Codec.Digest.ofBytes? o.lastTag with
    | none => return .error .tagWidth
    | some tag =>
      let opened : Opened W := ⟨o.world.1, o.records, o.validLen, o.lastTag, o.torn⟩
      let (h, chain) := mark b.world
      return .ok ⟨opened, ⟨b.offset, baseBytes, h, chain, digest, ⟨b.indexCount, b.indexLast⟩⟩,
        ⟨b.offset + o.validLen, tag⟩, o.world.2.1, indexSize - b.indexCount * entryBytes keys⟩

/-- The segment reader over bytes in memory (the simulation, every in-memory Store). -/
def segReader {F : Type} (seg : ByteArray) : Nat → Nat → Id (Except (StoreFault F) ByteArray) :=
  fun off len => pure (.ok (seg.extract off (off + len)))

end Nanodregg.Host
