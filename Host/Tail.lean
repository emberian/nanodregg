/-
# Host.Tail — following a Store's segment from outside the loop, never writing (HOSTING-7)

A tail is a reader of ONE Store's files that is not the Store's writer: the hosting controller
(`Hosting.Controller`, a per-Store exe run by the operator) follows its World's log this way. It
opens with THE open (`openAt` over a fresh read handle: no lock, no truncation), then absorbs each
newly appended stretch of the segment with the same `Log.recover` and the same per-record step the
open folds with, so it is not a second replayer: its World after every record is the one a reopen
of the Store at that record's end would reach (`Host.Proofs.Tail.absorb_encodeAll`).

    Tail.open  — the open, and the position after the last whole frame
    Tail.next  — read at most one frame bound of what was appended since (O(appended bytes)),
                 absorb every whole frame, return each record's output in order
    Tail.await — `next`, sleeping `tailPollMs` between empty reads, at most `rounds` times

The step returns an output per record (`Deployed.tailStep`: the record's Turns), so the caller
sees what each batch did without decoding anything itself. A cut last frame is the writer
mid-append: it is left for the next call, never refused and never truncated. Bad bytes with a
verifying frame after them are `corrupt` at their absolute offset, and a full frame bound of bytes
holding no whole frame is `corrupt` at the tail's position (no frame is longer than the bound).
-/
import Host.Store

namespace Nanodregg.Host

variable {W F O : Type}

/-- Where a tail stands: the World it has folded to, and the end of the last whole frame it
absorbed with that frame's tag (the `prev` of the next). -/
structure Tail (W : Type) where
  world : W
  pos : Position

/-- Fold the records in order, collecting each one's output; a refusal names the record's index
counted from the tail's position. -/
def absorbRecords (step : W → ByteArray → Except F (W × O)) :
    W → Array O → Nat → List ByteArray → Except (OpenFault F) (W × Array O)
  | w, os, _, [] => .ok (w, os)
  | w, os, i, r :: rs =>
    match step w r with
    | .ok (w', o) => absorbRecords step w' (os.push o) (i + 1) rs
    | .error f => .error (.record i f)

/-- Absorb `log`, the segment bytes from `t.pos.offset` (at most one frame bound of them;
`capped` says the segment holds more past them). Pure: `Log.recover` chained from the tail's
tag, then the step over every whole frame. -/
def Tail.absorb (s : Log.Sealer) (recordMax : Nat) (step : W → ByteArray → Except F (W × O))
    (t : Tail W) (log : ByteArray) (capped : Bool) : Except (StoreFault F) (Tail W × Array O) :=
  let rv := Log.recover s recordMax t.pos.tag.bytes log
  match rv.tail with
  | .corrupt off => .error (.log (.corrupt (t.pos.offset + off)))
  | _ =>
    if capped && rv.records.isEmpty then .error (.log (.corrupt t.pos.offset)) else
    match absorbRecords step t.world #[] 0 rv.records with
    | .error e => .error (.log e)
    | .ok (w, os) =>
      match Codec.Digest.ofBytes? rv.lastTag with
      | none => .error .tagWidth
      | some tag => .ok (⟨w, ⟨t.pos.offset + rv.validLen, tag⟩⟩, os)

/-- Open `dir` to follow it: the one open over fresh read handles (no lock, no truncation), with
the tail step's World. Returns the tail and the logical segment reader its `next` reads through
(`Segs`: a new segment file the writer starts is found by name when the tail passes its end, HOST-64). -/
def Tail.open (dir : System.FilePath) (keys : Keys) (c : Cadence) (world : Codec.Stream W)
    (mark : W → Nat × ByteArray) (origin : W → ByteArray) (step : W → ByteArray → Except F (W × O)) :
    IO (Except (StoreFault F) (Tail W × Segs)) := do
  match ← openAt dir keys c world mark origin (fun w r => (step w r).map Prod.fst) with
  | .error e => return .error e
  | .ok (o, fs) => return .ok (⟨o.opened.world, o.pos⟩, fs.segs)

/-- What was appended since `t`, absorbed: one read of at most `Log.frameMax c.recordBytesMax`
bytes at the tail's position (so a call costs O(appended bytes), bounded), every whole frame
folded. Nothing new: the tail unchanged and no outputs. -/
def Tail.next (keys : Keys) (c : Cadence) (step : W → ByteArray → Except F (W × O)) (seg : Segs)
    (t : Tail W) : IO (Except (StoreFault F) (Tail W × Array O)) := do
  let size ← match ← seg.size with
    | .ok n => pure n
    | .error e => return .error e.store
  if size ≤ t.pos.offset then return .ok (t, #[])
  let bound := Log.frameMax c.recordBytesMax
  let len := min (size - t.pos.offset) bound
  let bytes ← match ← seg.read t.pos.offset len with
    | .ok b => pure b
    | .error e => return .error e.store
  if bytes.size ≠ len then return .error (.shortRead bytes.size len)
  return Tail.absorb keys.segment c.recordBytesMax step t bytes (decide (bound < size - t.pos.offset))

/-- `next` until it absorbs something, sleeping `tailPollMs` between empty reads, at most `rounds`
reads (a deadline of `rounds · tailPollMs`); spent, the tail is returned unchanged with no
outputs. There is no change notification: polling with a stated bound is the mechanism. -/
def Tail.await (keys : Keys) (c : Cadence) (step : W → ByteArray → Except F (W × O)) (seg : Segs)
    (t : Tail W) : Nat → IO (Except (StoreFault F) (Tail W × Array O))
  | 0 => return .ok (t, #[])
  | rounds + 1 => do
    match ← Tail.next keys c step seg t with
    | .ok (t', os) =>
      if os.isEmpty && t'.pos.offset == t.pos.offset then
        IO.sleep tailPollMs.toUInt32
        Tail.await keys c step seg t' rounds
      else return .ok (t', os)
    | .error e => return .error e

end Nanodregg.Host
