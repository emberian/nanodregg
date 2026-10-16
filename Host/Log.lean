/-
# Host.Log — the record framing of one Store segment

A segment is a sequence of frames. A frame holds one record — opaque bytes; for the Host, one
encoded batch — and a tag:

    frame prev r = le32 r.size ‖ r ‖ tag (prev ‖ r)

`prev` is the previous frame's tag (the segment's `initial` for the first), so the tags chain:
a frame cannot be dropped, reordered or spliced in from another segment without a tag failing.

`recover` reads a segment from the start and returns the longest prefix of frames that verify,
the offset where it ends, and a verdict on what follows:

* `clean` — nothing follows;
* `torn n` — `n` bytes follow, `n ≤ frameMax`: at most one frame can be unsynced at a crash
  (every batch is fsynced before the next is written), so this is the torn tail and the writer
  truncates it;
* `corrupt off` — more than one frame's worth of bytes past `off` do not verify: refuse to open.

Theorems (`Host.Proofs.Log`): `recover_encodeAll` (a clean segment reads back exactly),
`recover_torn` (a segment whose last frame was cut anywhere reads back as the frames before it,
`torn` with the cut length), and `encodeAll_recover` (whatever bytes are on disk, the records
`recover` returns re-encode to exactly the bytes before `validLen`: it never invents a record).
-/
namespace Nanodregg.Host.Log

/-- Bytes in a tag. -/
def tagBytes : Nat := 32

/-- The keyed tag function. `tag` is CODEC's MAC under the Store key; the Host only needs its
size. -/
structure Sealer where
  tag : ByteArray → ByteArray
  tag_size : ∀ b, (tag b).size = tagBytes

/-! ## Little-endian u32

HOST-5: a private twin of CODEC's `u32le`, deleted the day `Codec.Stream` lands. -/

/-- `n mod 2^32`, little-endian. -/
def le32 (n : Nat) : ByteArray :=
  ⟨#[UInt8.ofNat n, UInt8.ofNat (n / 256), UInt8.ofNat (n / 65536), UInt8.ofNat (n / 16777216)]⟩

/-- The value of four bytes, little-endian (bytes past the end read as 0). -/
def ofLe32 (b : ByteArray) : Nat :=
  b[0]!.toNat + 256 * b[1]!.toNat + 65536 * b[2]!.toNat + 16777216 * b[3]!.toNat

/-- The u32 at `off`, if four bytes are there. -/
def readLe32 (log : ByteArray) (off : Nat) : Option Nat :=
  if off + 4 ≤ log.size then some (ofLe32 (log.extract off (off + 4))) else none

/-! ## Frames -/

/-- The largest frame a record of at most `recordMax` bytes makes. -/
def frameMax (recordMax : Nat) : Nat := 4 + recordMax + tagBytes

/-- One frame: length, record, tag over the previous tag and the record. -/
def frame (s : Sealer) (prev r : ByteArray) : ByteArray :=
  le32 r.size ++ r ++ s.tag (prev ++ r)

/-- The tag after a sequence of records. -/
def lastTag (s : Sealer) : ByteArray → List ByteArray → ByteArray
  | prev, [] => prev
  | prev, r :: rs => lastTag s (s.tag (prev ++ r)) rs

/-- A segment holding `rs`, chained from `prev`. -/
def encodeAll (s : Sealer) : ByteArray → List ByteArray → ByteArray
  | _, [] => ByteArray.empty
  | prev, r :: rs => frame s prev r ++ encodeAll s (s.tag (prev ++ r)) rs

/-! ## Recovery -/

/-- What follows the last verifying frame. -/
inductive Tail where
  | clean
  | torn (bytes : Nat)
  | corrupt (offset : Nat)
  deriving DecidableEq, Repr

structure Recovered where
  records : List ByteArray
  validLen : Nat
  lastTag : ByteArray
  tail : Tail

/-- Bytes past `off` that do not form a verifying frame: a torn tail if no more than one frame,
corruption otherwise. -/
def badTail (recordMax : Nat) (log : ByteArray) (off : Nat) : Tail :=
  if log.size - off ≤ frameMax recordMax then .torn (log.size - off) else .corrupt off

inductive Step where
  | stop (tail : Tail)
  | next (record : ByteArray) (off : Nat) (tag : ByteArray)

/-- Read one frame at `off`. -/
def step (s : Sealer) (recordMax : Nat) (log : ByteArray) (off : Nat) (prev : ByteArray) : Step :=
  if log.size ≤ off then .stop .clean else
  match readLe32 log off with
  | none => .stop (badTail recordMax log off)
  | some len =>
    if recordMax < len then .stop (badTail recordMax log off) else
    if log.size < off + 4 + len + tagBytes then .stop (badTail recordMax log off) else
    let r := log.extract (off + 4) (off + 4 + len)
    let t := log.extract (off + 4 + len) (off + 4 + len + tagBytes)
    if s.tag (prev ++ r) = t then .next r (off + 4 + len + tagBytes) t
    else .stop (badTail recordMax log off)

/-- Read frames until one does not verify; `fuel` bounds the frames read. -/
def go (s : Sealer) (recordMax : Nat) (log : ByteArray) :
    Nat → Nat → ByteArray → List ByteArray → Recovered
  | 0, off, prev, acc => ⟨acc.reverse, off, prev, .corrupt off⟩
  | fuel + 1, off, prev, acc =>
    match step s recordMax log off prev with
    | .stop tail => ⟨acc.reverse, off, prev, tail⟩
    | .next r off' t => go s recordMax log fuel off' t (r :: acc)

/-- Every frame is at least `4 + tagBytes` bytes, so `log.size + 1` frames of fuel always
suffice (`Host.Proofs.Log.go_fuel`): fuel exhaustion is unreachable, not a verdict. -/
def recover (s : Sealer) (recordMax : Nat) (initial log : ByteArray) : Recovered :=
  go s recordMax log (log.size + 1) 0 initial []

end Nanodregg.Host.Log
