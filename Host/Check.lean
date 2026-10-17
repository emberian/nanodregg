/-
# Host.Check — `host check STORE [--anchor HEIGHT:CHAIN_HEX]` (ASSEMBLY-ops D6; ROOT 2026-10-16)

The writer's own open (`openFollower`: the same `openAt`, no lock, nothing written, a torn tail
read as not yet written), folded with the writer's `foldStep`, then one line on stdout:

    STATUS height=H chain=C base_offset=O base_height=B seg_bytes=S records=R torn=T anchor=A

`anchor=none` says the check certified integrity and height only: a copy cut at a frame boundary,
or a rollback to an older complete copy, opens cleanly and is NOT detected without an anchor
(the frame-aligned prefix of a log is a valid, shorter log). With an anchor (a member follower's
head, or the highest receipt height with its chain) the Store must reach the anchor's height
(`behindAnchor`) and hold the anchor's chain there (`chainMismatch`); the chain at a past height
is read through the base's index exactly as a `log` page computes it (`Page.build`).

The open reads only the base and the tail after it. A backup is also the history every follower
pages from height 0, so `check` then reads the segment before the base and requires it to
recover clean from `segmentInitial` to exactly the base's offset (`historyClean`): a damaged
frame there is `corrupt`, which the open alone never sees. O(segment), off any request path.

It trusts the base: it re-derives nothing (that is `host follow`'s audit). It is integrity, height
and chain, not lawfulness.
-/
import Host.Deployed
import Host.Exit

namespace Nanodregg.Host.Check

open Nanodregg.Kernel Nanodregg.Codec Nanodregg.Host.Deployed

/-- A point the Store must have reached: a height and the chain after it. -/
structure Anchor where
  height : Nat
  chain : ByteArray

/-- `HEIGHT:CHAIN_HEX`, the chain a 32-byte digest. -/
def Anchor.parse (s : String) : Option Anchor :=
  match s.splitOn ":" with
  | [h, c] => do
    let height ← h.toNat?
    let chain ← Protocol.Text.ofHex c
    if chain.size ≠ 32 then none
    return ⟨height, chain⟩
  | _ => none

/-- The anchor's verdict, given the Store's height and its chain at the anchor's height
(`chainAt`, meaningful only when the anchor is not above `now`). -/
def Anchor.verdict (a : Anchor) (now : Nat) (chainAt : ByteArray) : Option Status :=
  if now < a.height then some .behindAnchor
  else if chainAt = a.chain then none
  else some .chainMismatch

def statusLine (o : Opening (World D)) (anchor : String) : String :=
  s!"STATUS height={o.opened.world.height} chain={o.opened.world.chain.toHex} base_offset={o.sealed.offset} base_height={o.sealed.height} seg_bytes={o.pos.offset} records={o.opened.records} torn={o.opened.torn} anchor={anchor}"

def refuse (s : Status) (name : String := s.name) : IO UInt32 := do
  IO.eprintln s!"refused {name}"
  return s.code.toUInt32

/-- The chain after height `h ≤ now`: a `log` page from `h` with no room for events. -/
def chainAt (store : System.FilePath) (keys : Keys) (o : Opening (World D)) (h : Nat) :
    IO (Except Page.Fault ByteArray) := do
  let seg ← File.open (segmentPath store) .read
  let r ← Page.build X.env Codec.Deployed.digestCodec X.digestOf keys.segment c.recordBytesMax 0
    (fun off len => seg.readAt off.toUInt64 len.toUSize) o.index (recorder.mark o.opened.world) h
  return r.map (·.chain)

/-- The segment before the base recovers clean, frame by frame, to exactly `offset`. -/
def historyClean (keys : Keys) (prefix_ : ByteArray) (offset : Nat) : Bool :=
  let rv := Log.recover keys.segment c.recordBytesMax segmentInitial prefix_
  rv.tail == .clean && rv.validLen == offset

def run (store : String) (anchor : Option Anchor) : IO UInt32 := do
  match ← (readKey store : IO (Except (StoreFault (Record.Fault (Reject D))) Digest)) with
  | .error f => refuse f.status f.name
  | .ok key =>
    let keys := Keys.ofKey key shapes
    match ← openFollower store keys c world recorder.mark foldStep with
    | .error f => refuse f.status f.name
    | .ok o =>
      let seg ← File.open (segmentPath store) .read
      let prefix_ ← seg.readAt 0 o.sealed.offset.toUSize
      unless prefix_.size = o.sealed.offset do return ← refuse .shortRead
      unless historyClean keys prefix_ o.sealed.offset do return ← refuse .corrupt "corrupt history"
      match anchor with
      | none => IO.println (statusLine o "none"); return 0
      | some a =>
        let now := o.opened.world.height
        let at_ ← if now < a.height then pure (.ok ByteArray.empty) else chainAt store keys o a.height
        match at_ with
        | .error f => refuse f.status f.name
        | .ok ch =>
          match a.verdict now ch with
          | some s =>
            IO.println (statusLine o s!"{a.height}:{Protocol.Text.toHex a.chain}")
            refuse s
          | none =>
            IO.println (statusLine o "ok"); return 0

end Nanodregg.Host.Check
