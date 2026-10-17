/-
# Host.Page — a `log` page, read from the durable segment

    page start = the events of Turns at heights start+1, start+2, … in log order, as many as fit
                 `budget` bytes, then the height and chain after the last of them

The index (`Host.Base.Entry`, one per record: the newest base's on disk in `index.log`, the tail's
in the loop's memory) locates the record holding height `start + 1` by binary search (`locate`),
reading each probed entry through `entryAt`, which checks a disk entry by its tag AT ITS POSITION
(`Entry.read`) on that read: an entry that does not read back is refused `badIndex` by name, and
no page is built from it (HOST-33; `Host.Proofs.Page.build_located`). From the located record,
frames are read in order by offset (`walk`), each verified under the segment sealer against the
tag before it: a frame that does not verify is refused `corrupt` by name, never served. Each record
is decoded, and the chain is advanced Turn by Turn from the entry's chain with the roots the record
states beside each Turn (`chainNext E c t roots`, HOST-29, KERNEL-41; the writer's reopen checked every stated
pair against its own admission), so a page may end inside a record and still state the exact chain
after its last event, without admitting anything. Work: at most 1 + ⌈log₂ count⌉ entry reads to
locate, then O(page bytes). The page holds durable records only: the loop builds it after the
batch's sync.

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
  /-- index entry `k` does not read back as an entry at its position under the Store's key (its
  tag failed, or it is not on disk), or its chain is not a digest (HOST-33) -/
  | badIndex (k : Nat)
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

/-- What the walk has served so far. -/
structure Acc where
  events : Array ByteArray := #[]
  bytes : Nat := 0
  /-- the height and chain after the last Turn walked (served or skipped) -/
  height : Nat
  chain : ByteArray
  full : Bool := false

variable {m : Type → Type} [Monad m]

/-- One record's (Turn, roots) pairs: skip those at or below `start`, serve the rest while they fit;
with the chain and height after the last Turn walked. -/
def walkTurnsAt (E : Env D) (budget start : Nat) (chain₀ : D) (h₀ : Nat) (ts : List (Turn D × (D × D))) (acc : Acc) :
    Acc × D × Nat :=
  ts.foldl (fun (st : Acc × D × Nat) (t, root) =>
    let (a, c, h) := st
    if a.full then st else
    let c' := chainNext E c t root
    let h' := h + 1
    if h' ≤ start then ({ a with height := h', chain := E.bytes c' }, c', h')
    else if budget < a.bytes + 4 + t.event.size then ({ a with full := true }, c, h)
    else ({ a with events := a.events.push t.event, bytes := a.bytes + 4 + t.event.size,
                   height := h', chain := E.bytes c' }, c', h')) (acc, chain₀, h₀)

/-- One record's (Turn, roots) pairs walked (`walkTurnsAt`): what the page holds after it. -/
def walkTurns (E : Env D) (budget start : Nat) (chain₀ : D) (h₀ : Nat) (ts : List (Turn D × (D × D))) (acc : Acc) : Acc :=
  (walkTurnsAt E budget start chain₀ h₀ ts acc).1

/-- Index entry `k`: the first `disk` from `index.log` (`readIndex off len`), each read back AT ITS
POSITION (`Entry.read`: its tag over `k` and its fields, under the Store's key), else `badIndex k`;
past them, the loop's own entries since the base (`mem`). The only way a page meets an entry. -/
def entryAt (keys : Keys) (readIndex : Nat → Nat → m ByteArray) (disk : Nat) (mem : Array Entry) (k : Nat) :
    m (Except Fault Entry) := do
  if k < disk then
    match Entry.read keys k (← readIndex (k * entryBytes keys) (entryBytes keys)) with
    | some e => return .ok e
    | none => return .error (.badIndex k)
  else
    match mem[k - disk]? with
    | some e => return .ok e
    | none => return .error (.badIndex k)

/-- The last entry in `[0, count)` whose height is at most `start` (entries ascend by height;
entry 0 if none), with its position: a binary search over `get`, reading entry 0 and then one
entry per halving (at most 1 + ⌈log₂ count⌉ reads), refused by the first read that fails. The
entry it returns is the one `get` returned at that position (`Host.Proofs.Page.locate_got`). -/
def locate (get : Nat → m (Except Fault Entry)) (count start : Nat) : m (Except Fault (Nat × Entry)) := do
  match ← get 0 with
  | .error f => return .error f
  | .ok e₀ => go count 0 count e₀
where
  /-- invariant: the answer is in `[lo, hi)` and `e` is entry `lo`; each step halves the range -/
  go : Nat → Nat → Nat → Entry → m (Except Fault (Nat × Entry))
    | 0, lo, _, e => return .ok (lo, e)
    | fuel + 1, lo, hi, e => do
      if hi ≤ lo + 1 then return .ok (lo, e)
      let mid := (lo + hi) / 2
      match ← get mid with
      | .error f => return .error f
      | .ok em => if em.height ≤ start then go fuel mid hi em else go fuel lo mid e

/-- The frame at `off`, verified against the tag before it. -/
def frameOf (s : Log.Sealer) (recordMax : Nat) (read : Nat → Nat → m ByteArray) (off : Nat) :
    m (Option ByteArray) := do
  -- every record sits after a frame of its own segment (genesis's origin frame: HOST-18)
  let prev ← read (off - Log.tagBytes) Log.tagBytes
  let head ← read off 4
  match Log.lenAt head 0 with
  | none => return none
  | some len =>
    if recordMax < len then return none
    let buf ← read off (4 + len + Log.tagBytes)
    return (Log.frameAt s recordMax buf 0 prev).map (·.record)

/-- The frames from `off` to `endOff` (the durable end), at most `fuel` of them, walked into
`acc` with the chain `c` and height `acc.height` before the frame at `off`: each frame verified
(`frameOf`) and decoded, else `corrupt off`. Stops when the page is full. -/
def walk (E : Env D) (dc : Stream D) (s : Log.Sealer) (recordMax budget : Nat) (read : Nat → Nat → m ByteArray)
    (endOff start : Nat) : Nat → Nat → D → Acc → m (Except Fault Acc)
  | 0, _, _, acc => return .ok acc
  | fuel + 1, off, c, acc => do
    if acc.full || decide (endOff ≤ off) then return .ok acc
    match ← frameOf s recordMax read off with
    | none => return .error (.corrupt off)
    | some r =>
      match (Record.codec dc).decode r with
      | .error _ => return .error (.corrupt off)
      | .ok ts =>
        let (a, c', _) := walkTurnsAt E budget start c acc.height ts acc
        walk E dc s recordMax budget read endOff start fuel (off + frameSize r) c' a

/-- A page from `start`. `get`/`count` are the index (`entryAt` over `index.log` and the loop's
entries), `endOff` the durable end of the segment, `now` the World's height and chain (an empty
page states them). The page is built from ONE entry, the one `locate` returns, and the segment
bytes after it. -/
def build (E : Env D) (dc : Stream D) (digestOf : ByteArray → Option D) (s : Log.Sealer)
    (recordMax budget : Nat) (read : Nat → Nat → m ByteArray) (get : Nat → m (Except Fault Entry))
    (count endOff : Nat) (now : Nat × ByteArray) (start : Nat) : m (Except Fault Acc) := do
  if now.1 ≤ start ∨ count = 0 then return .ok ⟨#[], 0, now.1, now.2, false⟩
  match ← locate get count start with
  | .error f => return .error f
  | .ok (k, e) =>
    match digestOf e.chain with
    | none => return .error (.badIndex k)
    | some c =>
      let a : Acc := { height := e.height, chain := e.chain }
      walk E dc s recordMax budget read endOff start (count - k) e.offset c a

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
