/-
# Host.Check — `host check STORE [--anchor STEPS:CHAIN_HEX]` (ASSEMBLY-ops D6; ROOT 2026-10-16)

The writer's own open (`openAt`, through `Check.openClean`: no lock, nothing written, a torn tail
read as not yet written), folded with the writer's `foldStep` (every step taken by `World.step`: a recorded refusal is
checked as a Turn is, its bounds, window, budget and stated roots), then one line on stdout:

    STATUS height=H steps=N chain=C base_offset=O base_steps=B seg_bytes=S records=R torn=T use=U retained_from=F anchor=A

`retained_from=F` is the step count at the oldest segment file the Store keeps (its checkpoint
header's): 0 when the Store keeps its whole history; past it when a retention count dropped the files
before (HOST-64, KERNEL-44 Part 2). Everything `check` verifies, it verifies FROM there.

`use=U` (PROTOCOL-43's count on a real Store, cv 01a14de7-225e) is the number of distinct objects
made by one member and used by another (`Protocol.Use.shared`) over EVERY call the segment
committed SINCE `retained_from` (the records the Store keeps): the open does not fold the history
before the base, so the calls come from the records (`Log.recover` of the kept segment to `seg_bytes`, each record by `Record.codec`, each admitted Turn's
`event`, which is the call's bytes, by `X.decodeCall`, in log order), and the World `Use.shared` reads
for makers is the opened one. A record or event that does not decode, or a record that holds no step
(HOST-54), is refused `corrupt` with the
name `corrupt use-record K` / `corrupt use-event K` (K counts the record frames after
the origin frame / the Turns, from 0), never skipped; that is unreachable for a Store this Host wrote (it wrote each record by the
same codec, and admission decoded each call).

`anchor=none` says the check certified integrity and position only: a copy cut at a frame boundary,
or a rollback to an older complete copy, opens cleanly and is NOT detected without an anchor
(the frame-aligned prefix of a log is a valid, shorter log). With an anchor (a member follower's
head: its step count with its chain; a position in the log is a step count, KERNEL-47, since a
recorded refusal is a step at an unchanged height) the Store must reach the anchor's step count
(`behindAnchor`) and hold the anchor's chain there (`chainMismatch`); the chain at a past step is
read through the base's index exactly as a `log` page computes it (`Page.build`).

The open reads only the base, its last index entry and the tail after it. A backup is also the
history every follower pages from, so `check` then walks the segment files from the base's back to
the oldest the base keeps (`retainedFrom`): every header must verify (`checkpointCorrupt`), name its
own file, the Store's origin and its predecessor, and end where its successor starts
(`foreignSegment`); a kept file that is absent is `missing seg.<o>.log`. It reads the kept segment
before the base and requires it to recover clean from the oldest header's tag to exactly the base's
offset (`historyClean`): a damaged frame there is `corrupt`, which the open alone never sees. When it
keeps the whole history, the first frame must be the origin frame stating the base World's genesis
chain (`foreignOrigin`, HOST-25: the open now checks the base's header instead). Then it reads EVERY
entry the base keeps (from `indexFrom`) and requires each to read back at its position under the
Store's key, to name the offset of its own record frame, with step counts that never fall
(`indexClean`, HOST-33 condition 1): a damaged entry there is `indexCorrupt`, which the open (one
entry) does not see and a page sees only when it reads that entry. O(kept segment + kept index),
off any request path.

It trusts the base: it re-derives nothing (that is `host follow`'s, `Receive.rederive`). It is integrity, position
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

def statusLine (o : Opening (World D)) (use from_ : Nat) (anchor : String) : String :=
  s!"STATUS height={o.opened.world.height} steps={o.opened.world.steps} chain={o.opened.world.chain.toHex} base_offset={o.sealed.offset} base_steps={o.sealed.steps} seg_bytes={o.pos.offset} records={o.opened.records} torn={o.opened.torn} use={use} retained_from={from_} anchor={anchor}"

/-- The Turns of a segment's records, in log order; `.error K` names the first record (counted
from `i`) that does not decode, or that holds no step (HOST-54: refused as the open's
`Record.stepTurns` refuses it `empty`; `check` reads the records BEFORE the base too, which no open
folds). -/
def turnsOf : Nat → List ByteArray → Except Nat (List (Turn D))
  | _, [] => .ok []
  | i, r :: rs =>
    match (Record.codec Codec.Deployed.digestCodec).decode r with
    | .error _ => .error i
    | .ok [] => .error i
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

/-- What `check` verified of the kept files: the open, the oldest kept file's header, and the kept
segment from it to the end of the valid log. -/
structure Kept where
  keys : Keys
  opening : Opening (World D)
  files : Files
  oldest : Header
  /-- the logical segment `[oldest.start, opening.pos.offset)` -/
  bytes : ByteArray

/-- The records of the kept segment, recovered clean from the oldest header's tag; the origin frame
(the first frame of a Store that keeps its whole history) left out. -/
def Kept.records (k : Kept) : List ByteArray :=
  let rs := (Log.recover k.keys.segment c.recordBytesMax k.oldest.tag.bytes k.bytes).records
  if k.oldest.start = 0 then rs.drop 1 else rs

/-- Every call the kept records committed, in log order. -/
def Kept.calls (k : Kept) : Except String (List (Receive.Call D)) := recordCalls k.records

/-- `use=U`: `Protocol.Use.shared` over every call the kept records committed, makers read from the
opened World. -/
def Kept.use (k : Kept) : Except String Nat :=
  k.calls.map fun cs => (Protocol.Use.shared X k.opening.opened.world cs).length

def refuse (s : Status) (name : String := s.name) : IO UInt32 := do
  IO.eprintln s!"refused {name}"
  return s.code.toUInt32

/-- The chain after step `h ≤ now`: a `log` page from `h` with no room for events (budget 0), over
the kept files (`Page.kept`: `checkpointed` below them). -/
def chainAt (store : System.FilePath) (k : Kept) (h : Nat) : IO (Except Page.Fault ByteArray) := do
  let o := k.opening
  let files : PageFiles := ⟨store, k.keys, originChain o.opened.world,
    ← IO.mkRef (k.files.retainedFrom, k.files.indexFrom), ← IO.mkRef #[o.sealed.offset], ← IO.mkRef k.files.generation⟩
  let (k0, read, readIndex) ← files.readers
  -- budget 0: the page holds no event, so its chain is the chain AT step `h`
  let r ← Page.kept X.env Codec.Deployed.digestCodec X.digestOf k.keys.segment c.recordBytesMax 0 k0 read
    (Page.entryAt (k.keys.forStore (originChain o.opened.world)) readIndex o.sealed.index.count o.index)
    (o.sealed.index.count + o.index.size) o.pos.offset (recorder.mark o.opened.world) h
  return r.map (·.chain)

/-- The kept segment before the base recovers clean, frame by frame, from the oldest kept header's
tag to exactly `len` bytes. -/
def historyClean (keys : Keys) (recordMax : Nat) (from_ : ByteArray) (prefix_ : ByteArray) (len : Nat) : Bool :=
  let rv := Log.recover keys.segment recordMax from_ prefix_
  rv.tail == .clean && rv.validLen == len

/-- Every kept file, the base's (at `baseOffset`) back to `retainedFrom`, verified: its header
(`checkpointCorrupt`, `missing seg.<o>.log`), its origin (`foreignOrigin`), its predecessor ending
where it starts (`foreignSegment`), and the walk ending exactly at `retainedFrom` with the header
counting `indexFrom` entries (`indexCorrupt from`). The oldest kept header. -/
def keptHeaders (store : System.FilePath) (keys : Keys) (origin : ByteArray) (baseOffset : Nat) (fs : Files) :
    IO (Except (Status × String) Header) := do
  match ← filesBack store keys baseOffset fs.retainedFrom fs.generation with
  | .error e => return .error ((e.store : StoreFault Unit).status, e.text)
  | .ok hs =>
    let some (oldest, ho) := hs.getLast? | return .error (.corrupt, "corrupt history")
    unless oldest = fs.retainedFrom do return .error (.foreignSegment, "foreignSegment")
    for (s, h) in hs do
      unless h.origin = origin do return .error (.foreignOrigin, "foreignOrigin")
      if s ≠ oldest then
        let body ← match ← readHeader store keys h.prev fs.generation with
          | .ok (_, _, b) => pure b
          | .error e => return .error ((e.store : StoreFault Unit).status, e.text)
        if h.prev + body < s then return .error (.segmentShort, "segmentShort")
        unless h.prev + body = s do return .error (.foreignSegment, "foreignSegment")
    unless ho.indexCount = fs.indexFrom do return .error (.indexCorrupt, "indexCorrupt from")
    return .ok ho

/-- `check`'s verification of the kept files after the one open `o` (generic in the World: `host
check` runs it at the deployed one, host-file-sim at the toy one): the kept files' headers
(`keptHeaders`), the kept segment before the base recovering clean (`historyClean`) and, kept from
genesis, opening with the origin frame stating `origin` (`foreignOrigin`), and every index entry the
base keeps reading back at its position and naming its record's offset, the first at the oldest kept
header's step count (`indexClean`, HOST-68). The oldest
kept header and the kept segment `[oldest.start, o.pos.offset)`; a refusal is its status and name. -/
def keptClean {W : Type} (store : System.FilePath) (keys : Keys) (recordMax : Nat) (origin : ByteArray)
    (o : Opening W) (fs : Files) : IO (Except (Status × String) (Header × ByteArray)) := do
  match ← keptHeaders store keys origin o.sealed.offset fs with
  | .error e => return .error e
  | .ok oldest =>
  let len := o.pos.offset - oldest.start
  let bytes ← match ← fs.segs.read oldest.start len with
    | .ok b => pure b
    | .error e => return .error ((e.store : StoreFault Unit).status, e.text)
  unless bytes.size = len do return .error (.shortRead, Status.shortRead.name)
  let hist := bytes.extract 0 (o.sealed.offset - oldest.start)
  -- kept from genesis, the first frame is the origin frame: one that verifies and states another
  -- World's genesis chain is `foreignOrigin` (HOST-25), named before the history walk
  if oldest.start = 0 then
    if let some r := Log.frameAt keys.segment chainBytesMax hist 0 segmentInitial then
      unless r.record = origin do return .error (.foreignOrigin, "foreignOrigin")
  unless historyClean keys recordMax oldest.tag.bytes hist (o.sealed.offset - oldest.start) do
    return .error (.corrupt, "corrupt history")
  let records := (Log.recover keys.segment recordMax oldest.tag.bytes hist).records
  if oldest.start = 0 then
    unless records.head? = some origin do return .error (.foreignOrigin, "foreignOrigin")
  let n := o.sealed.index.count
  let k0 := fs.indexFrom
  let ib ← (← File.open (indexPathAt store k0) .read).readAt 0 ((n - k0) * entryBytes keys).toUSize
  let offs := recordOffsetsFrom oldest.start records
  let offs := if oldest.start = 0 then offs.drop 1 else offs
  match indexClean (keys.forStore origin) ib k0 n offs oldest.steps with
  | some j => return .error (.indexCorrupt, s!"indexCorrupt entry {j}")
  | none => return .ok (oldest, bytes)

/-- The read-only open `check` and `export` share: the key, the one open, then `keptClean`. -/
def openClean (store : String) : IO (Except (Status × String) Kept) := do
  match ← (readKey store : IO (Except (StoreFault (Record.Fault (Reject D))) Digest)) with
  | .error f => return .error (f.status, f.text)
  | .ok key =>
    let keys := Keys.ofKey key shapes
    match ← openAt store keys c world recorder.mark originChain foldStep with
    | .error f => return .error (f.status, f.text)
    | .ok (o, fs) =>
      match ← keptClean store keys c.recordBytesMax (originChain o.opened.world) o fs with
      | .error e => return .error e
      | .ok (oldest, bytes) => return .ok ⟨keys, o, fs, oldest, bytes⟩

def run (store : String) (anchor : Option Anchor) : IO UInt32 := do
  match ← openClean store with
  | .error (s, n) => refuse s n
  | .ok k =>
      let o := k.opening
      let from_ := k.oldest.steps
      match k.use with
      | .error n => refuse .corrupt n
      | .ok use =>
      match anchor with
      | none => IO.println (statusLine o use from_ "none"); return 0
      | some a =>
        let now := o.opened.world.steps
        let at_ ← if now < a.steps then pure (.ok ByteArray.empty) else chainAt store k a.steps
        match at_ with
        | .error f => refuse f.status f.name
        | .ok ch =>
          match a.verdict now ch with
          | some s =>
            IO.println (statusLine o use from_ s!"{a.steps}:{Protocol.Text.toHex a.chain}")
            refuse s
          | none =>
            IO.println (statusLine o use from_ "ok"); return 0

end Nanodregg.Host.Check
