/-
# Host.Page — a `log` page, read from the durable segment

    page start = the events of the steps start+1, start+2, … in log order, as many as fit
                 `budget` bytes and at most `recordTurnsMax`, then the step count and chain after
                 the last of them

A position in the log is a STEP count (KERNEL-47 amendment 1): every step, an admitted Turn or a
recorded refusal, is one event of a page, `0 ‖ the call` for a Turn (its `event`) and `1 ‖ the call`
for a recorded refusal (its `event`), PROTOCOL-8's tagged event. The follower (`host follow`)
re-derives each one by `Protocol.Command.absorbStep` and takes the same step: an honest writer's
events are absorbed as exactly its steps (`Host.Proofs.Refine`: `host_run_absorbed`,
`honest_page_absorbed`, HOST-75).

The index (`Host.Base.Entry`, one per record: the newest base's on disk in the index file, the tail's
in the loop's memory) locates the record holding step `start + 1` by binary search (`locate`),
reading each probed entry through `entryAt`, which checks a disk entry by its tag AT ITS POSITION
(`Entry.read`) on that read: an entry that does not read back is refused `badIndex` by name, and
no page is built from it (HOST-33; `Host.Proofs.Page.build_located`). From the located record,
frames are read in order by offset (`walk`), each verified under the segment sealer against the
tag before it: a frame that does not verify is refused `corrupt` by name, never served. Each record
is decoded, and the chain is advanced step by step from the entry's chain with the roots digest the
record states beside each step (`stepLink E c s roots`, HOST-29, KERNEL-47; the writer's reopen
checked every stated pair against its own step), so a page may end inside a record and still state
the exact chain after its last event, without taking any step. A page holds at most
`recordTurnsMax` events (`Host.Proofs.Page.build_events_le`): a follower appends one page's steps as
ONE record, and a record holds at most that many, so a page never holds more steps than its
follower may write. Work: at most 1 + ⌈log₂ count⌉ entry reads to
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
  /-- a `log` page from `start` before `first`, the step count this Store's log begins at (a Store
  `host import` made from a World at step `first`, or a follower Store that adopted a base there,
  Host/Follow.lean): the steps through `first` are in no record here, so no page from `start` can be
  served (HOST-61) -/
  | beforeLog (start first : Nat)
  /-- a `log` page from `start` before `first`, the step count at the oldest segment file this Store
  keeps: the records before it were dropped by a retention count (HOST-64). The remedy is a served
  base (a thin join) or the archive's copy, never this Store -/
  | checkpointed (start first : Nat)
  deriving Repr

def Fault.name : Fault → String
  | .corrupt _ => "corrupt"
  | .badIndex _ => "badIndex"
  | .tooLarge => "tooLarge"
  | .pastEnd _ _ => "pastEnd"
  | .shortBase => "shortBase"
  | .beforeLog _ _ => "beforeLog"
  | .checkpointed _ _ => "checkpointed"

/-- The deployed page budget: PROTOCOL's `pageBytesMax`, the frame less the continuation that
asked for the page and every byte of framing, so the page and the continuation travel back to
follow in ONE frame (PROTOCOL-70; it was `frameBytesMax - 1024`, a bound on the page as one field). -/
def budget : Nat := Protocol.Bounds.pageBytesMax

/-- What the walk has served so far. -/
structure Acc where
  events : Array ByteArray := #[]
  bytes : Nat := 0
  /-- the step count and chain after the last step walked (served or skipped) -/
  steps : Nat
  chain : ByteArray
  full : Bool := false

/-- The bytes a page's events take on the wire: each one's `u32` length and its bytes (what `bytes`
counts as the walk serves, `Host.Proofs.Page.build_within`). -/
def Acc.eventBytes (a : Acc) : Nat := (a.events.toList.map (4 + ·.size)).sum

variable {m : Type → Type} [Monad m]

/-- A step's event on a page (PROTOCOL-8, PROTOCOL-60): the kernel's `Step.event` behind its tag
(`Protocol.eventBytes`): `0 ‖ call` for an admitted Turn, `1 ‖ call` for a recorded refusal with no
cancel signature, and `2 ‖ nat64 n ‖ sig ‖ call` for a recorded cancel, whose `n`-byte signature the
follower needs to re-record the writer's exact record (KERNEL-60). -/
def stepEvent (s : Step D) : ByteArray := Protocol.eventBytes s.event

/-- One (step, roots) pair against what the page holds, the chain and the step count before it: a
step at or below `start` is skipped (the count and chain move); past it, the step's event is served
while it fits `budget` and the page holds fewer than `recordTurnsMax` events, else the page is
`full` (nothing after is walked). -/
def walkStep (E : Env D) (budget start : Nat) (st : Acc × D × Nat) (x : Step D × D) : Acc × D × Nat :=
  let (a, c, h) := st
  let (t, root) := x
  if a.full then st else
  let c' := stepLink E c t root
  let h' := h + 1
  let ev := stepEvent t
  if h' ≤ start then ({ a with steps := h', chain := E.bytes c' }, c', h')
  else if recordTurnsMax ≤ a.events.size ∨ budget < a.bytes + 4 + ev.size then
    ({ a with full := true }, c, h)
  else ({ a with events := a.events.push ev, bytes := a.bytes + 4 + ev.size,
                 steps := h', chain := E.bytes c', full := recordTurnsMax ≤ a.events.size + 1 }, c', h')

/-- One record's (step, roots) pairs walked in order (`walkStep`): skip those at or below `start`,
serve the rest while they fit `budget` and the page holds fewer than `recordTurnsMax` events; with
the chain and step count after the last step walked. -/
def walkTurnsAt (E : Env D) (budget start : Nat) (chain₀ : D) (h₀ : Nat) (ts : List (Step D × D)) (acc : Acc) :
    Acc × D × Nat :=
  ts.foldl (walkStep E budget start) (acc, chain₀, h₀)

/-- One record's (step, roots) pairs walked (`walkTurnsAt`): what the page holds after it. -/
def walkTurns (E : Env D) (budget start : Nat) (chain₀ : D) (h₀ : Nat) (ts : List (Step D × D)) (acc : Acc) : Acc :=
  (walkTurnsAt E budget start chain₀ h₀ ts acc).1

/-- Index entry `k`: the first `disk` from the index file (`readIndex off len`), each read back AT ITS
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

/-- The last entry in `[0, count)` whose step count is at most `start` (entries ascend by steps;
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
      | .ok em => if em.steps ≤ start then go fuel mid hi em else go fuel lo mid e

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
`acc` with the chain `c` and step count `acc.steps` before the frame at `off`: each frame verified
(`frameOf`) and decoded to at least one step, else `corrupt off` (a record of no steps is refused as
the open's `Record.stepTurns` refuses it `empty`, HOST-49/HOST-54: a page walks records BEFORE the
base too, which no open folds). Stops when the page is full. -/
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
      | .ok [] => return .error (.corrupt off)
      | .ok ts =>
        let (a, c', _) := walkTurnsAt E budget start c acc.steps ts acc
        walk E dc s recordMax budget read endOff start fuel (off + frameSize r) c' a

/-- A page from `start`. `get`/`count` are the index (`entryAt` over the index file and the loop's
entries), `endOff` the durable end of the segment, `now` the World's step count and chain (an
empty page states them). The page is built from ONE entry, the one `locate` returns, and the segment
bytes after it. A page from before the log is refused `beforeLog` by name (HOST-61): no index
(`count = 0`) under a World past `start`, or a located entry past `start` (`locate` returns entry 0
when none is at or below it). Both are a Store whose log begins after `start` (one `host import` made
at a later step, or a follower Store that adopted a base there), and serving it would state steps
the member never asked for. -/
def build (E : Env D) (dc : Stream D) (digestOf : ByteArray → Option D) (s : Log.Sealer)
    (recordMax budget : Nat) (read : Nat → Nat → m ByteArray) (get : Nat → m (Except Fault Entry))
    (count endOff : Nat) (now : Nat × ByteArray) (start : Nat) : m (Except Fault Acc) := do
  if now.1 ≤ start then return .ok ⟨#[], 0, now.1, now.2, false⟩
  if count = 0 then return .error (.beforeLog start now.1)
  match ← locate get count start with
  | .error f => return .error f
  | .ok (k, e) =>
    if start < e.steps then return .error (.beforeLog start e.steps)
    match digestOf e.chain with
    | none => return .error (.badIndex k)
    | some c =>
      let a : Acc := { steps := e.steps, chain := e.chain }
      walk E dc s recordMax budget read endOff start (count - k) e.offset c a

/-- A `log` page over the files a base KEEPS (HOST-64): `build` over the index from the first kept
entry `k0` (entry `k0 + k` as the page's `k`, `count` the absolute entry count), so no page reads an
entry or a frame the Store dropped. A page from before the first kept record is `checkpointed` when
the Store dropped history (`k0 > 0`), `beforeLog` otherwise (HOST-61: the log itself begins later).
The deployed pager (`Host.Deployed.pageKept`) and host-file-sim run this one function. -/
def kept (E : Env D) (dc : Stream D) (digestOf : ByteArray → Option D) (s : Log.Sealer)
    (recordMax budget k0 : Nat) (read : Nat → Nat → m ByteArray) (get : Nat → m (Except Fault Entry))
    (count endOff : Nat) (now : Nat × ByteArray) (start : Nat) : m (Except Fault Acc) := do
  match ← build E dc digestOf s recordMax budget read (fun k => get (k0 + k)) (count - k0) endOff now start with
  | .error (.beforeLog st f) => return .error (if 0 < k0 then .checkpointed st f else .beforeLog st f)
  | x => return x

/-- The page on the wire: `logReplyLayout` (events, steps u64, chain, tipSteps u64, tipHeight u64,
baseSteps u64, baseDigest): `tipSteps` and `tipHeight` the World's step count and height the page
was built at (a member pages again until its step count reaches `tipSteps`; it signs its next
envelope from `tipHeight`, since windows are in heights); `baseSteps` and `baseDigest` the newest
DURABLE base's when the page was built (`Sealed.steps`, `Sealed.digest`: the base a thin member
adopts, PROTOCOL-47). A seal racing the page makes them stale; the inviter then refuses
`noBase` or `baseMismatch`, never pins them. -/
def bytes (a : Acc) (tipSteps tipHeight baseSteps : Nat) (baseDigest : ByteArray) : Except Fault ByteArray :=
  let f := Protocol.Text.fit Protocol.Bounds.frameBytesMax
  match Protocol.Text.fitList Protocol.Bounds.frameBytesMax a.events.toList,
      f (Protocol.Text.u64 a.steps), f a.chain, f (Protocol.Text.u64 tipSteps), f (Protocol.Text.u64 tipHeight),
      f (Protocol.Text.u64 baseSteps), f baseDigest with
  | some l, some h, some c, some t, some th, some bs, some bd =>
      .ok (Protocol.logReplyFrame.bytes (l, h, c, t, th, bs, bd, ()))
  | _, _, _, _, _, _, _ => .error .tooLarge

/-- A `read` page (HOST-15): the newest base's World bytes from byte `start`, at most `budget` of
them less the certificate's encoding, with the base's step count, total size, digest and chain and
the writer's certificate of the base's head (`readReplyLayout`; `cert` empty when the writer holds
none, PROTOCOL-77.1; it is served as read, never checked here: the member decides it). `readBase off
len` reads the base file. A seal that replaces the file between pages changes the stated digest, and
the member restarts. A reader that sees the new file under the old header produces bytes that do not hash
to the stated digest, and the member's `Thin.accept` refuses them. One pread, O(page). -/
def basePage (budget : Nat) (readBase : Nat → Nat → m ByteArray) (sealed : Sealed) (cert : ByteArray)
    (start : Nat) : m (Except Fault ByteArray) := do
  if sealed.bytes < start then return .error (.pastEnd start sealed.bytes)
  let len := min (budget - (4 + cert.size)) (sealed.bytes - start)
  let b ← readBase (worldStart + start) len
  if b.size ≠ len then return .error .shortBase
  let f := Protocol.Text.fit Protocol.Bounds.frameBytesMax
  match f (Protocol.Text.u64 sealed.steps), f (Protocol.Text.u64 sealed.bytes), f sealed.digest,
      f sealed.chain, f b, f cert with
  | some h, some t, some d, some c, some p, some k =>
      return .ok (Protocol.readReplyFrame.bytes (h, t, d, c, p, k, ()))
  | _, _, _, _, _, _ => return .error .tooLarge

end Nanodregg.Host.Page
