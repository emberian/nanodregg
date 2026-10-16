/-
# Host.Log — the record framing of one Store segment

A segment is a sequence of frames. A frame holds one record — opaque bytes; for the Host, one
encoded batch — and a tag:

    frame prev r = u32 r.size ‖ r ‖ tag (prev ‖ r)

`prev` is the previous frame's tag (the segment's `initial` for the first), so the tags chain:
a frame cannot be dropped, reordered or spliced in from another segment without a tag failing.

`recover` reads a segment from the start and returns the longest prefix of frames that verify,
the offset where it ends, and a verdict on what follows:

* `clean` — nothing follows;
* `torn n` — `n` bytes follow that could be the one unsynced frame (every batch is fsynced
  before the next is written, so only the last frame can be torn): `n ≤ frameMax` and no frame
  verifies anywhere after them; the writer truncates them;
* `corrupt off` — the bytes at `off` do not verify but a frame verifies later, or there are more
  than one frame's worth: acknowledged data would be lost by truncating, so refuse to open.

The one undecidable case is stated, not hidden: a corruption inside the LAST frame looks exactly
like a torn write of it. A client holding that frame's receipt sees the height go back; the
follower that folded it refuses the shorter log.

Theorems (`Host.Proofs.Log`): `recover_encodeAll` (a clean segment reads back exactly),
`recover_torn` (a segment whose last frame was cut anywhere reads back as the frames before it,
`torn` with the cut length, given no frame verifies inside the cut — what an unforgeable tag
guarantees), and `encodeAll_recover` (whatever bytes are on disk, the records
`recover` returns re-encode to exactly the bytes before `validLen`: it never invents a record).
-/
import Codec.Stream

namespace Nanodregg.Host.Log

/-- Bytes in a tag. -/
def tagBytes : Nat := 32

/-- The keyed tag function. `tag` is CODEC's MAC under the Store key; the Host only needs its
size. -/
structure Sealer where
  tag : ByteArray → ByteArray
  tag_size : ∀ b, (tag b).size = tagBytes

/-- A frame's length field: CODEC's one little-endian `u32` (`Codec.Stream.u32`). -/
def lenBytes (n : Nat) : ByteArray := Codec.Stream.u32.bytes (UInt32.ofNat n)

/-- The length field at `off`, if four bytes are there. -/
def lenAt (log : ByteArray) (off : Nat) : Option Nat :=
  match Codec.Stream.u32.get log off with
  | .ok (v, _) => some v.toNat
  | .error _ => none

/-! ## Frames -/

/-- The largest frame a record of at most `recordMax` bytes makes. -/
def frameMax (recordMax : Nat) : Nat := 4 + recordMax + tagBytes

/-- One frame: length, record, tag over the previous tag and the record. -/
def frame (s : Sealer) (prev r : ByteArray) : ByteArray :=
  lenBytes r.size ++ r ++ s.tag (prev ++ r)

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

/-- One verifying frame read at an offset: its record, the offset after it, its tag. -/
structure Read where
  record : ByteArray
  next : Nat
  tag : ByteArray

/-- The frame at `off`, if one is there and its tag chains from `prev`. -/
def frameAt (s : Sealer) (recordMax : Nat) (log : ByteArray) (off : Nat) (prev : ByteArray) :
    Option Read :=
  match lenAt log off with
  | none => none
  | some len =>
    if recordMax < len then none else
    if log.size < off + 4 + len + tagBytes then none else
    let r := log.extract (off + 4) (off + 4 + len)
    let t := log.extract (off + 4 + len) (off + 4 + len + tagBytes)
    if s.tag (prev ++ r) = t then some ⟨r, off + 4 + len + tagBytes, t⟩ else none

/-- A frame verifies at `o` against the 32 bytes before it (every frame but a segment's first is
preceded on disk by the tag it chains from). -/
def verifiesAt (s : Sealer) (recordMax : Nat) (log : ByteArray) (o : Nat) : Bool :=
  decide (tagBytes ≤ o) && (frameAt s recordMax log o (log.extract (o - tagBytes) o)).isSome

/-- Bytes past `off` that do not form a verifying frame. They are the torn tail only if they
could be the one unsynced frame: no more than `frameMax` of them, and no frame verifies anywhere
after `off` (a verifying frame later means synced, acknowledged data follows the bad bytes, so
truncating would drop it). Otherwise they are corruption. -/
def badTail (s : Sealer) (recordMax : Nat) (log : ByteArray) (off : Nat) : Tail :=
  if frameMax recordMax < log.size - off then .corrupt off
  else if (List.range (log.size - off)).any (fun i => verifiesAt s recordMax log (off + 1 + i))
    then .corrupt off
  else .torn (log.size - off)

inductive Step where
  | stop (tail : Tail)
  | next (record : ByteArray) (off : Nat) (tag : ByteArray)

/-- Read one frame at `off`. -/
def step (s : Sealer) (recordMax : Nat) (log : ByteArray) (off : Nat) (prev : ByteArray) : Step :=
  if log.size ≤ off then .stop .clean else
  match frameAt s recordMax log off prev with
  | some r => .next r.record r.next r.tag
  | none => .stop (badTail s recordMax log off)

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
