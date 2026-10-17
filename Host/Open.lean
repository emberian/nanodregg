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

Theorems (`Host.Proofs.Open`): `open_encodeAll` (a clean segment opens to the fold of exactly the
records written), `open_torn` (a segment whose last frame was cut opens to the fold of the frames
before it, `torn` = the cut), and `open_sound` (for ANY bytes, the World opened is the fold of
records that are literally the bytes before `validLen`).
-/
import Host.Base

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
  | .shortRead _ _ => "shortRead"
  | .base f => f.name
  | .log (.corrupt _) => "corrupt"
  | .log (.record _ _) => "record"
  | .seal f => f.name
  | .tagWidth => "tagWidth"

/-- What the one open reads: the base, and the World the segment after it folds to. -/
structure Opening (W : Type) where
  opened : Opened W
  /-- the base's offset, and its World's encoded size -/
  sealed : Sealed
  /-- where the valid segment ends (absolute), and its chain tag -/
  pos : Position
  /-- the base's index, then one entry per record of the tail -/
  index : Array Entry

/-- Fold one record and index it: the World's mark before it, at the frame's offset. -/
def indexed (mark : W → Nat × ByteArray) (step : W → ByteArray → Except F W) :
    W × Array Entry × Nat → ByteArray → Except F (W × Array Entry × Nat)
  | (w, idx, off), r => do
    let w' ← step w r
    let (h, chain) := mark w
    pure (w', idx.push ⟨h, off, chain⟩, off + frameSize r)

/-- The one open, given the base file's bytes, the segment's size and a reader of the segment
(`IO` over the file for `host`, `Id` over bytes in the simulation): verify and decode the base,
bound the tail (`tailRead`), read exactly that tail, and `openLog` it from the base's World. -/
def openWith {m : Type → Type} [Monad m] (keys : Keys) (c : Cadence) (world : Codec.Stream W)
    (mark : W → Nat × ByteArray) (step : W → ByteArray → Except F W) (file : ByteArray) (size : Nat)
    (readTail : Nat → Nat → m (Except (StoreFault F) ByteArray)) : m (Except (StoreFault F) (Opening W)) := do
  if Log.frameMax c.baseRecordMax < file.size then return .error (.base (.baseTooLarge file.size)) else
  match Base.read keys c world file with
  | .error e => return .error (.base e)
  | .ok (b, baseBytes) =>
  match tailRead c baseBytes b.offset size with
  | .error e => return .error (.base e)
  | .ok len =>
  match ← readTail b.offset len with
  | .error e => return .error e
  | .ok tail =>
  if tail.size ≠ len then return .error (.shortRead tail.size len) else
  match openLog keys.segment c.recordBytesMax (indexed mark step) (b.world, b.index.toArray, b.offset)
      b.tag.bytes tail with
  | .error e => return .error (.log e)
  | .ok o =>
    match Codec.Digest.ofBytes? o.lastTag with
    | none => return .error .tagWidth
    | some tag =>
      let opened : Opened W := ⟨o.world.1, o.records, o.validLen, o.lastTag, o.torn⟩
      return .ok ⟨opened, ⟨b.offset, baseBytes⟩, ⟨b.offset + o.validLen, tag⟩, o.world.2.1⟩

end Nanodregg.Host
