/-
# Host.Page — a `log` page, read from the durable segment

    page start = the events of Turns at heights start+1, start+2, … in log order, as many as fit
                 `budget` bytes, then the height and chain after the last of them

The index (`Host.Base.Entry`, one per record, carried by the base and rebuilt for the tail at
open) locates the record holding height `start + 1` by binary search. From there, frames are read
in order. Each is verified under the segment sealer against the tag before it: a frame that does
not verify is refused `corrupt` by name, never served. Each record is decoded, and the chain
is advanced Turn by Turn from the entry's chain, so a page may end inside a record and still
state the exact chain after its last event. Work: O(log records) to locate, then O(page bytes).
The page holds durable records only: the loop builds it after the batch's sync.

`build` is generic in the reader's monad: `IO` over the segment file for `host serve`, `Id` over
bytes in the simulation.
-/
import Host.Base
import Host.Record
import Protocol.Frames
import Protocol.Command.Text

namespace Nanodregg.Host.Page

open Nanodregg.Kernel Nanodregg.Codec

variable {D : Type} [Ord D] [DecidableEq D]

/-- Why a page is not served (law 7). -/
inductive Fault where
  /-- the frame at `offset` does not verify, or its record does not decode -/
  | corrupt (offset : Nat)
  /-- an index entry's chain is not a digest -/
  | badIndex (offset : Nat)
  /-- the page does not fit the reply layout's bounds (unreachable under `budget`) -/
  | tooLarge
  /-- a `read` from past the end of the base's World bytes -/
  | pastEnd (start total : Nat)
  /-- the base file is shorter than its World: it changed under the read -/
  | shortBase
  deriving Repr

def Fault.name : Fault → String
  | .corrupt _ => "corrupt"
  | .badIndex _ => "badIndex"
  | .tooLarge => "tooLarge"
  | .pastEnd _ _ => "pastEnd"
  | .shortBase => "shortBase"

/-- The deployed page budget: a reply frame, less room for the counts, the height and the chain. -/
def budget : Nat := Protocol.Bounds.frameBytesMax - 1024

/-- The last entry whose height is at most `start` (entries ascend by height; 0 if none). -/
def locate (index : Array Entry) (start : Nat) : Nat :=
  go index.size 0 index.size
where
  /-- invariant: the answer is in `[lo, hi)`; each step halves the range -/
  go : Nat → Nat → Nat → Nat
    | 0, lo, _ => lo
    | fuel + 1, lo, hi =>
      if hi ≤ lo + 1 then lo else
      let mid := (lo + hi) / 2
      if (index[mid]?.map fun e => decide (e.height ≤ start)).getD false then go fuel mid hi else go fuel lo mid

/-- What the walk has served so far. -/
structure Acc where
  events : Array ByteArray := #[]
  bytes : Nat := 0
  /-- the height and chain after the last Turn walked (served or skipped) -/
  height : Nat
  chain : ByteArray
  full : Bool := false

variable {m : Type → Type} [Monad m]

/-- One record's Turns: skip those at or below `start`, serve the rest while they fit. -/
def walkTurns (E : Env D) (budget start : Nat) (chain₀ : D) (h₀ : Nat) (ts : List (Turn D)) (acc : Acc) : Acc :=
  (ts.foldl (fun (st : Acc × D × Nat) t =>
    let (a, c, h) := st
    if a.full then st else
    let c' := chainNext E c t
    let h' := h + 1
    if h' ≤ start then ({ a with height := h', chain := E.bytes c' }, c', h')
    else if budget < a.bytes + 4 + t.event.size then ({ a with full := true }, c, h)
    else ({ a with events := a.events.push t.event, bytes := a.bytes + 4 + t.event.size,
                   height := h', chain := E.bytes c' }, c', h')) (acc, chain₀, h₀)).1

/-- The frame of `e`, verified against the tag before it. -/
def frameOf (s : Log.Sealer) (recordMax : Nat) (read : Nat → Nat → m ByteArray) (e : Entry) :
    m (Option ByteArray) := do
  let prev ← if e.offset = 0 then pure segmentInitial else read (e.offset - Log.tagBytes) Log.tagBytes
  let head ← read e.offset 4
  match Log.lenAt head 0 with
  | none => return none
  | some len =>
    if recordMax < len then return none
    let buf ← read e.offset (4 + len + Log.tagBytes)
    return (Log.frameAt s recordMax buf 0 prev).map (·.record)

/-- A page from `start`. `now` is the World's height and chain (an empty page states them). -/
def build (E : Env D) (dc : Stream D) (digestOf : ByteArray → Option D) (s : Log.Sealer)
    (recordMax budget : Nat) (read : Nat → Nat → m ByteArray) (index : Array Entry) (now : Nat × ByteArray)
    (start : Nat) : m (Except Fault Acc) := do
  if now.1 ≤ start then return .ok ⟨#[], 0, now.1, now.2, false⟩
  let i := locate index start
  go (index.size - i) i none
where
  go : Nat → Nat → Option Acc → m (Except Fault Acc)
    | 0, _, acc => return .ok (acc.getD ⟨#[], 0, now.1, now.2, false⟩)
    | fuel + 1, i, acc => do
      match index[i]? with
      | none => return .ok (acc.getD ⟨#[], 0, now.1, now.2, false⟩)
      | some e =>
        if (acc.map (·.full)).getD false then return .ok (acc.getD ⟨#[], 0, now.1, now.2, false⟩)
        match ← frameOf s recordMax read e with
        | none => return .error (.corrupt e.offset)
        | some r =>
          match (Record.codec dc).decode r, digestOf e.chain with
          | .error _, _ => return .error (.corrupt e.offset)
          | _, none => return .error (.badIndex e.offset)
          | .ok (ts, _), some c =>
            let a := acc.getD { height := e.height, chain := e.chain }
            go fuel (i + 1) (some (walkTurns E budget start c e.height ts a))

/-- The page on the wire: `logReplyLayout` (events, height u64, chain, tip u64), `tip` the World's
height the page was built at (a member pages again until its height reaches it). -/
def bytes (a : Acc) (tip : Nat) : Except Fault ByteArray :=
  let f := Protocol.Text.fit Protocol.Bounds.frameBytesMax
  match Protocol.Text.fitList Protocol.Bounds.frameBytesMax a.events.toList,
      f (Protocol.Text.u64 a.height), f a.chain, f (Protocol.Text.u64 tip) with
  | some l, some h, some c, some t => .ok (Protocol.logReplyFrame.bytes (l, h, c, t, ()))
  | _, _, _, _ => .error .tooLarge

/-- A `read` page (HOST-15): the newest base's World bytes from byte `start`, at most `budget` of
them, with the base's height, total size, digest and chain (`readReplyLayout`). `readBase off len`
reads the base file. A seal that replaces the file between pages changes the stated digest, and
the member restarts. A reader that sees the new file under the old header produces bytes that do not hash
to the stated digest, and the member's `Thin.accept` refuses them. One pread, O(page). -/
def basePage (budget : Nat) (readBase : Nat → Nat → m ByteArray) (sealed : Sealed) (start : Nat) :
    m (Except Fault ByteArray) := do
  if sealed.bytes < start then return .error (.pastEnd start sealed.bytes)
  let len := min budget (sealed.bytes - start)
  let b ← readBase (worldStart + start) len
  if b.size ≠ len then return .error .shortBase
  let f := Protocol.Text.fit Protocol.Bounds.frameBytesMax
  match f (Protocol.Text.u64 sealed.height), f (Protocol.Text.u64 sealed.bytes), f sealed.digest,
      f sealed.chain, f b with
  | some h, some t, some d, some c, some p => return .ok (Protocol.readReplyFrame.bytes (h, t, d, c, p, ()))
  | _, _, _, _, _ => return .error .tooLarge

end Nanodregg.Host.Page
