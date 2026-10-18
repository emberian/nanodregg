/-
# Host.Check — `host check STORE [--anchor STEPS:CHAIN_HEX]` (ASSEMBLY-ops D6; ROOT 2026-10-16)

The writer's own open (`openFollower`: the same `openAt`, no lock, nothing written, a torn tail
read as not yet written), folded with the writer's `foldStep` (every step taken by `World.step`: a recorded refusal is
checked as a Turn is, its bounds, window, budget and stated roots), then one line on stdout:

    STATUS height=H steps=N chain=C base_offset=O base_steps=B seg_bytes=S records=R torn=T use=U anchor=A

`use=U` (PROTOCOL-43's count on a real Store, cv 01a14de7-225e) is the number of distinct objects
made by one member and used by another (`Protocol.Use.shared`) over EVERY call the segment
committed: the open does not fold the history before the base, so the calls come from the records
(`Log.recover` of the segment to `seg_bytes`, each record by `Record.codec`, each admitted Turn's
`event`, which is the call's bytes, by `X.decodeCall`, in log order), and the World `Use.shared` reads
for makers is the opened one. A record or event that does not decode is refused `corrupt` with the
name `corrupt use-record K` / `corrupt use-event K` (K counts the record frames after
the origin frame / the Turns, from 0), never skipped; that is unreachable for a Store this Host wrote (it wrote each record by the
same codec, and admission decoded each call). When a checkpoint drops history (KERNEL-44 Part 2),
`use` counts since the oldest retained base and must say so.

`anchor=none` says the check certified integrity and position only: a copy cut at a frame boundary,
or a rollback to an older complete copy, opens cleanly and is NOT detected without an anchor
(the frame-aligned prefix of a log is a valid, shorter log). With an anchor (a member follower's
head: its step count with its chain; a position in the log is a step count, KERNEL-47, since a
recorded refusal is a step at an unchanged height) the Store must reach the anchor's step count
(`behindAnchor`) and hold the anchor's chain there (`chainMismatch`); the chain at a past step is
read through the base's index exactly as a `log` page computes it (`Page.build`).

The open reads only the base, its last index entry and the tail after it. A backup is also the
history every follower pages from step 0, so `check` then reads the segment before the base and
requires it to recover clean from `segmentInitial` to exactly the base's offset (`historyClean`):
a damaged frame there is `corrupt`, which the open alone never sees. Then it reads EVERY entry the
base counts and requires each to read back at its position under the Store's key, to name the
offset of its own record frame, with step counts that never fall (`indexClean`, HOST-33 condition 1):
a damaged entry there is `indexCorrupt`, which the open (one entry) does not see and a page sees
only when it reads that entry. O(segment + index), off any request path.

It trusts the base: it re-derives nothing (that is `host follow`'s audit). It is integrity, position
and chain, not lawfulness.
-/
import Host.Deployed
import Host.Exit
import Protocol.Use

namespace Nanodregg.Host.Check

open Nanodregg.Kernel Nanodregg.Codec Nanodregg.Host.Deployed

/-- A point the Store must have reached: a step count and the chain after it. -/
structure Anchor where
  steps : Nat
  chain : ByteArray

/-- `STEPS:CHAIN_HEX`, the chain a 32-byte digest. -/
def Anchor.parse (s : String) : Option Anchor :=
  match s.splitOn ":" with
  | [h, c] => do
    let steps ← h.toNat?
    let chain ← Protocol.Text.ofHex c
    if chain.size ≠ 32 then none
    return ⟨steps, chain⟩
  | _ => none

/-- The anchor's verdict, given the Store's step count and its chain at the anchor's step count
(`chainAt`, meaningful only when the anchor is not above `now`). -/
def Anchor.verdict (a : Anchor) (now : Nat) (chainAt : ByteArray) : Option Status :=
  if now < a.steps then some .behindAnchor
  else if chainAt = a.chain then none
  else some .chainMismatch

def statusLine (o : Opening (World D)) (use : Nat) (anchor : String) : String :=
  s!"STATUS height={o.opened.world.height} steps={o.opened.world.steps} chain={o.opened.world.chain.toHex} base_offset={o.sealed.offset} base_steps={o.sealed.steps} seg_bytes={o.pos.offset} records={o.opened.records} torn={o.opened.torn} use={use} anchor={anchor}"

/-- The Turns of a segment's records, in log order; `.error K` names the first record (counted
from `i`) that does not decode. -/
def turnsOf : Nat → List ByteArray → Except Nat (List (Turn D))
  | _, [] => .ok []
  | i, r :: rs =>
    match (Record.codec Codec.Deployed.digestCodec).decode r with
    | .error _ => .error i
    | .ok ps => (Step.turns (ps.map Prod.fst) ++ ·) <$> turnsOf (i + 1) rs

/-- Each Turn's call (its `event` is the call's bytes); `.error K` names the first Turn (counted from
`i`) whose event does not decode. -/
def callsOf : Nat → List (Turn D) → Except Nat (List (Receive.Call D))
  | _, [] => .ok []
  | i, t :: ts =>
    match X.decodeCall t.event with
    | none => .error i
    | some c => (c :: ·) <$> callsOf (i + 1) ts

/-- Every call the records committed, in log order; a refusal's name otherwise. -/
def recordCalls (records : List ByteArray) : Except String (List (Receive.Call D)) :=
  match turnsOf 0 records with
  | .error k => .error s!"corrupt use-record {k}"
  | .ok ts =>
    match callsOf 0 ts with
    | .error k => .error s!"corrupt use-event {k}"
    | .ok cs => .ok cs

/-- The calls of the whole segment to `seg_bytes` (history and tail), recovered clean record by
record. -/
def callsAt (store : String) (keys : Keys) (o : Opening (World D)) :
    IO (Except String (List (Receive.Call D))) := do
  let seg ← File.open (segmentPath store) .read
  let bytes ← seg.readAt 0 o.pos.offset.toUSize
  unless bytes.size = o.pos.offset do return .error Status.shortRead.name
  let rv := Log.recover keys.segment c.recordBytesMax segmentInitial bytes
  unless rv.tail == .clean && rv.validLen == o.pos.offset do return .error "corrupt use-segment"
  -- the first frame is genesis's origin frame, not a record (HOST-18, `recordOffsets`)
  return recordCalls (rv.records.drop 1)

/-- `use=U`: `Protocol.Use.shared` over every call the segment committed, makers read from the
opened World. -/
def useAt (store : String) (keys : Keys) (o : Opening (World D)) : IO (Except String Nat) := do
  return (← callsAt store keys o).map fun cs => (Protocol.Use.shared X o.opened.world cs).length

def refuse (s : Status) (name : String := s.name) : IO UInt32 := do
  IO.eprintln s!"refused {name}"
  return s.code.toUInt32

/-- The chain after step `h ≤ now`: a `log` page from `h` with no room for events. -/
def chainAt (store : System.FilePath) (keys : Keys) (o : Opening (World D)) (h : Nat) :
    IO (Except Page.Fault ByteArray) := do
  let seg ← File.open (segmentPath store) .read
  let idx ← File.open (indexPath store) .read
  let r ← Page.build X.env Codec.Deployed.digestCodec X.digestOf keys.segment c.recordBytesMax 0
    (fun off len => seg.readAt off.toUInt64 len.toUSize)
    (Page.entryAt (keys.forStore (originChain o.opened.world)) (fun off len => idx.readAt off.toUInt64 len.toUSize)
      o.sealed.index.count o.index)
    (o.sealed.index.count + o.index.size) o.pos.offset (recorder.mark o.opened.world) h
  return r.map (·.chain)

/-- The segment before the base recovers clean, frame by frame, to exactly `offset`. -/
def historyClean (keys : Keys) (prefix_ : ByteArray) (offset : Nat) : Bool :=
  let rv := Log.recover keys.segment c.recordBytesMax segmentInitial prefix_
  rv.tail == .clean && rv.validLen == offset

/-- The read-only open `check` and `export` share: the key, `openFollower`, the segment before
the base recovering clean (`historyClean`), and every index entry the base counts reading back at
its position and naming its record's offset (`indexClean`); a refusal is its status and name. -/
def openClean (store : String) : IO (Except (Status × String) (Keys × Opening (World D))) := do
  match ← (readKey store : IO (Except (StoreFault (Record.Fault (Reject D))) Digest)) with
  | .error f => return .error (f.status, f.text)
  | .ok key =>
    let keys := Keys.ofKey key shapes
    match ← openFollower store keys c world recorder.mark originChain foldStep with
    | .error f => return .error (f.status, f.text)
    | .ok o =>
      let seg ← File.open (segmentPath store) .read
      let prefix_ ← seg.readAt 0 o.sealed.offset.toUSize
      unless prefix_.size = o.sealed.offset do return .error (.shortRead, Status.shortRead.name)
      unless historyClean keys prefix_ o.sealed.offset do return .error (.corrupt, "corrupt history")
      let records := (Log.recover keys.segment c.recordBytesMax segmentInitial prefix_).records
      let n := o.sealed.index.count
      let ib ← (← File.open (indexPath store) .read).readAt 0 (n * entryBytes keys).toUSize
      match indexClean (keys.forStore (originChain o.opened.world)) ib n (recordOffsets records) with
      | some k => return .error (.indexCorrupt, s!"indexCorrupt entry {k}")
      | none => return .ok (keys, o)

def run (store : String) (anchor : Option Anchor) : IO UInt32 := do
  match ← openClean store with
  | .error (s, n) => refuse s n
  | .ok (keys, o) =>
      match ← useAt store keys o with
      | .error n => refuse (if n = Status.shortRead.name then .shortRead else .corrupt) n
      | .ok use =>
      match anchor with
      | none => IO.println (statusLine o use "none"); return 0
      | some a =>
        let now := o.opened.world.steps
        let at_ ← if now < a.steps then pure (.ok ByteArray.empty) else chainAt store keys o a.steps
        match at_ with
        | .error f => refuse f.status f.name
        | .ok ch =>
          match a.verdict now ch with
          | some s =>
            IO.println (statusLine o use s!"{a.steps}:{Protocol.Text.toHex a.chain}")
            refuse s
          | none =>
            IO.println (statusLine o use "ok"); return 0

end Nanodregg.Host.Check
