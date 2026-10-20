/-
# Host.Segment — the segment as files, each opened by a checkpoint header (HOST-64; KERNEL-44 Part 2)

    STORE/seg.<o>.log = header ‖ the segment's bytes [o, o + body)
    header            = u64 start ‖ u64 steps ‖ u64 indexCount ‖ u64 prev ‖ tag32 ‖ origin ‖ chain
                        ‖ mac32, the checkpoint sealer (`Keys.checkpoint`) over everything before it

The SEGMENT is one logical byte sequence, exactly the bytes `seg.log` held before the split: the same
frames, the same tag chain, absolute offsets. Every base, index entry and page names a LOGICAL
offset; a file holds one slice of it. Its header states where the slice starts (`start`, also the
file's name), the segment tag there (`tag`, the `prev` of the slice's first frame), the World's
step count and chain there, how many index entries index the records before it (`indexCount`), the
genesis chain of the Store's origin (`origin`, the Store's identity, HOST-25), and where the file
before it starts (`prev`; the first file names itself).

The loop starts a new file exactly where it starts a seal (`Host.Loop.spawnSeal` → `Checkpoint.rotate`),
so every base sits at the start of its own file and names it by its offset. Genesis writes
`seg.0.log` (the origin frame) and the empty file of its base.

The header binds the position as (steps, chain), not the base's digest: the digest exists only once
the seal Task has encoded the World, after the file was started (ROOT, R1). The chain commits every
step before `start` (a dropped prefix included) and the World's roots; base.world's own MAC binds the
digest.

A Store keeps the files from `retainedFrom` (the base names it) on; files before it were DROPPED by a
retention count (`host serve --retain N`, `Host.Store`). The default keeps everything: `retainedFrom` = 0
for ever, and the logical segment and index bytes are those of a Store before the split.
-/
import Host.Base

namespace Nanodregg.Host

open Nanodregg.Codec

/-- The header check of a base's own file (HOST-64): the header must verify (`checkpointCorrupt`),
state the base World's origin (`foreignOrigin`, HOST-25's identity, which the origin frame at offset 0
carried before files could be dropped), and state the base's own position: its offset, its tag, its
World's step count and chain, and the entries it counts (`foreignSegment`: the file is not the one
this base was sealed at). -/
def headerFault (keys : Keys) (b : ByteArray) (origin : ByteArray) (offset : Nat) (tag : Digest)
    (mark : Nat × ByteArray) (indexCount : Nat) : Option BaseFault :=
  match Header.read keys b with
  | none => some .checkpointCorrupt
  | some h =>
    if h.origin ≠ origin then some .foreignOrigin
    else if h.start = offset ∧ h.tag = tag ∧ h.steps = mark.1 ∧ h.chain = mark.2 ∧ h.indexCount = indexCount
      then none
    else some .foreignSegment

/-- The offset, retained offset and first index entry a base file names, read from the fixed-width
fields at its end (`Base.codec` ends u64 offset ‖ tag ‖ u64 count ‖ last ‖ u64 retainedFrom ‖ u64
indexFrom, then the frame's tag). Unauthenticated here: they only choose which files the open
reads, and `openWith` then verifies the base and requires the header of `seg.<offset>.log` to state
the base's own position (`foreignSegment`), and every index entry to read back at its position. -/
def Base.peek (file : ByteArray) : Option (Nat × Nat × Nat) :=
  let e := file.size
  if e < 128 then none else
  match Stream.nat64.decode (file.extract (e - 128) (e - 120)),
      Stream.nat64.decode (file.extract (e - 48) (e - 40)),
      Stream.nat64.decode (file.extract (e - 40) (e - 32)) with
  | .ok o, .ok r, .ok k => some (o, r, k)
  | _, _, _ => none

/-! ## The logical segment across files (`Host.Store.Segs.read`'s core, HOST-64's follow-up) -/

/-- The logical bytes `[cur, stop)` from the files starting at `starts` (ascending), where `rd o p n`
reads `n` body bytes of the file starting at `o` from body offset `p`. It stops at `stop`, at a file
starting past `cur` (a gap: nothing is read across it), and at a short read (the segment's end).
`Host.Proofs.Segs.segGather_logical`: over files that are slices of one logical sequence `L`, this is
`L.extract cur stop`. -/
def segGather {m : Type → Type} [Monad m] (rd : Nat → Nat → Nat → m ByteArray) :
    List Nat → Nat → Nat → m ByteArray
  | [], _, _ => pure .empty
  | o :: rest, cur, stop =>
    if stop ≤ cur ∨ cur < o then pure .empty else
    match rest.head? with
    | none => rd o (cur - o) (stop - cur)
    | some n =>
      if n ≤ cur then segGather rd rest cur stop else do
        let want := min stop n - cur
        let got ← rd o (cur - o) want
        if got.size < want then pure got else
        return got ++ (← segGather rd rest (cur + got.size) stop)

/-- `len` logical bytes from `off` across the files `starts` (fewer at the segment's end). The
`Log.tagBytes` bytes before the oldest file (the tag its first frame chains from, HOST-18's preceding
tag) are served from that file's header (`tagAt first`, which the header's MAC binds); anything
further before it is not held, and reads as nothing. `Host.Store.Segs.read` is this over the files;
`Host.Proofs.Segs.segRead_logical` states it returns the logical extract. -/
def segRead {m : Type → Type} [Monad m] {E : Type} (tagAt : Nat → m (Except E ByteArray))
    (rd : Nat → Nat → Nat → m ByteArray) (starts : List Nat) (off len : Nat) : m (Except E ByteArray) := do
  let stop := off + len
  match starts with
  | [] => return .ok .empty
  | first :: _ =>
    if off < first then
      if first - off ≤ Log.tagBytes then
        match ← tagAt first with
        | .error e => return .error e
        | .ok tag =>
          let t := tag.extract (Log.tagBytes - (first - off)) Log.tagBytes
          let t := t.extract 0 (min t.size (stop - off))
          return .ok (t ++ (← segGather rd starts (off + t.size) stop))
      else return .ok .empty
    else return .ok (← segGather rd starts off stop)

/-- A retention count: `none` keeps every file (the default); `some n` keeps the `n` newest files,
`n` at least `retainFloor`. -/
abbrev Retain := Option Nat

/-- The fewest files a finite retention keeps: the base's own file and the one before it, which holds
the base's last indexed record (the open's last-frame check reads it, HOST-63). -/
def retainFloor : Nat := 2

/-- `--retain N`: `N` parses and is at least the floor; `retainBelowFloor` otherwise. -/
def Retain.parse (s : String) : Except String Retain :=
  match s.toNat? with
  | none => .error "usage retain"
  | some n => if n < retainFloor then .error "retainBelowFloor" else .ok (some n)

end Nanodregg.Host
