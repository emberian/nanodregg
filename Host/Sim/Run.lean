/-
# Host.Sim.Run — the loop end to end, and the crash plants

`Nanodregg.Host.Sim.run [seed]` drives `serve` (the deployed loop) over the
in-memory disk with toy parameters, admitting every Turn through `Kernel.World.admit`, and checks:

1. one reply per request; a resend of the same txId (the same bytes, or other bytes under it:
   a txId is the digest of the signed call, KERNEL-7) answers `ok` with the original receipt and
   admits nothing; double spends answer `refused`;
2. `recover` of the disk is `clean`, and `World.fold` of the recovered records from genesis
   reaches the loop's World (height and chain);
3. a different seeded batch split reaches the same chain;
4. plant-fsync-fail: the 4th sync throws; the batch's replies are all `uncertain`; the loop stops;
   for every crash cut of the unsynced frame, `recover` returns the synced batches (and the
   failed batch only if all its bytes are there), `torn` with the cut length otherwise;
5. plant-flip-byte / plant-flip-header: a flipped byte in the first frame (body or length) of a
   multi-frame segment is `corrupt`; plant-flip-last-frame: a flip in the last frame reads as
   `torn` (the one case no format can decide; DESIGN §4).

6. the base (HOST-14): the loop seals at the toy cadence; a reopen reads one base and at most
   `tailMax` of segment; plant-crash-before-rename: for every seal, the previous base with the
   segment as it stood when the new base became durable opens to the new base's World;
   plant-tail-too-long: the genesis base with the whole segment is refused `tailTooLong`;
   plant-base-flip: a flipped byte in the base is `baseCorrupt`; plant-world-too-large: a
   `worldBytesMax` the World outgrows stops the loop `sealFailed worldTooLarge`.

Returns 0 iff every check holds; each failure prints `FAIL <name>`. `lake exe host-sim SEED`
(`Host.Sim.Main`) is the exe; standing runs seeds 1 2 3.
-/
import Host.Sim.MemStore
import Host.Sim.Toy
import Kernel.World
import Host.Open
import Host.Page

namespace Nanodregg.Host.Sim

open Nanodregg.Kernel

/-- A deterministic generator (64-bit LCG). -/
def lcg (s : Nat) : Nat := (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

def receipt (h d : Nat) : ByteArray := le64 h ++ le64 d

def machine : Machine (World Nat) (Turn Nat) (Reject Nat) Frame where
  admit := World.admit env
  handle _ f :=
    match turnCodec.decode f.payload with
    | .ok t => .admit t fun w' => receipt w'.height (turnDigest env t)
    | .error _ => .reply Protocol.Status.refused.code "undecodable".toUTF8
  refuse w t r :=
    match r with
    | .replayed h => match w.journal[t.txId]? with
      | some (_, d) => (Protocol.Status.ok.code, receipt h d)
      | none => (Protocol.Status.refused.code, r.name.toUTF8)
    | _ => (Protocol.Status.refused.code, r.name.toUTF8)
  ok := Protocol.Status.ok.code

def genesis : World Nat := World.genesis env "sim".toUTF8 (2 ^ 40)

inductive Kind | fresh | replay | sameTxId | doubleSpend
  deriving DecidableEq

/-- `n` requests from a seed: each a fresh turn, an exact replay, other bytes under a used txId, or a double spend. -/
def scenario (seed n : Nat) : List (Frame × Kind) :=
  (go n seed [] []).reverse
where
  go : Nat → Nat → List (Turn Nat) → List (Frame × Kind) → List (Frame × Kind)
    | 0, _, _, acc => acc
    | k + 1, s, made, acc =>
      let s' := lcg s
      let i := acc.length
      let pick := (s' / 65536) % 10
      let (t, kind) :=
        match made with
        | [] => (mkTurn (1000 + i) 0 1024 [5000 + i], Kind.fresh)
        | m :: _ =>
          if pick < 7 then (mkTurn (1000 + i) 0 1024 [5000 + i], .fresh)
          else if pick < 8 then (m, .replay)
          else if pick < 9 then (mkTurn m.txId 0 1024 [9000 + i], .sameTxId)
          else (mkTurn (1000 + i) 0 1024 m.nullifiers, .doubleSpend)
      let f : Frame := ⟨UInt32.ofNat i, Protocol.Op.submit.code, turnCodec.bytes t⟩
      go k s' (if kind = .fresh then t :: made else made) ((f, kind) :: acc)

/-- Seeded batch boundaries: `true` = the next frame is already queued. -/
def splits (seed n : Nat) : List Bool :=
  (List.range n).foldl (fun (s, acc) _ => let s' := lcg s; (s', ((s' / 4096) % 3 != 0) :: acc))
    (seed, []) |>.2.reverse

abbrev Fault := StoreFault (Record.Fault (Reject Nat))

/-- The one open over an in-memory image: `openWith` reading bytes. -/
def reopenWith (c : Cadence) (base seg : ByteArray) : Except Fault (Opening (World Nat)) :=
  Id.run (openWith keys c world recorder.mark foldStep base seg.size fun off len =>
    pure (.ok (seg.extract off (off + len))))

def reopen (base seg : ByteArray) : Except Fault (Opening (World Nat)) := reopenWith cadence base seg

def faultName (r : Except Fault (Opening (World Nat))) : String :=
  match r with
  | .error f => f.name
  | .ok _ => "opened"

/-- A Store as genesis leaves it: the genesis base at offset 0 and an empty segment. -/
def genesisBases (c : Cadence) : Bases :=
  match Base.file keys c world genesis 0 Codec.Digest.zero [] with
  | .ok file => { file, history := #[(file, 0)] }
  | .error _ => {}

def genesisResident : Resident (World Nat) :=
  { world := genesis, pos := ⟨0, Codec.Digest.zero⟩, sealed := ⟨0, world.size genesis⟩, index := #[] }

structure RunResult where
  exit : Exit
  resident : Resident (World Nat)
  replies : Array Reply
  disk : Disk
  bases : Bases

/-- Serve `frames` from a disk, its bases, and the state they opened to. -/
def serveFrom (c : Cadence) (seed : Nat) (frames : List Frame) (failSyncAt : Option Nat) (d : Disk)
    (b : Bases) (r : Resident (World Nat)) : IO RunResult := do
  let disk ← IO.mkRef d
  let bases ← IO.mkRef b
  let fr ← IO.mkRef frames
  let sp ← IO.mkRef (splits seed frames.length)
  let sent ← IO.mkRef #[]
  let (exit, r) ← serve machine recorder keys.segment (memCheckpoint disk bases keys c world) c
    (memStore disk failSyncAt) (fun _ _ => pure (0, ByteArray.empty)) (scriptPort fr sp sent) ⟨16, 1 <<< 20⟩
    (frames.length + 1) r none
  return ⟨exit, r, ← sent.get, ← disk.get, ← bases.get⟩

def runWith (c : Cadence) (seed : Nat) (frames : List Frame) (failSyncAt : Option Nat) : IO RunResult :=
  serveFrom c seed frames failSyncAt {} (genesisBases c) genesisResident

def runOnce (seed : Nat) (frames : List Frame) (failSyncAt : Option Nat) : IO RunResult :=
  runWith cadence seed frames failSyncAt

def isCorrupt (r : Except Fault (Opening (World Nat))) (off : Nat) : Bool :=
  match r with
  | .error (.log (.corrupt o)) => o = off
  | _ => false

/-- `a / b` to three decimals, as standing's waste gate reads it (`b = 0` prints the numerator). -/
def ratio (a b : Nat) : String :=
  if b = 0 then toString a else
  let m := (a * 1000 + b / 2) / b
  let frac := toString (m % 1000)
  s!"{m / 1000}.{"".pushn '0' (3 - frac.length)}{frac}"

def check (name : String) (ok : Bool) (failures : IO.Ref Nat) : IO Unit := do
  if ok then IO.println s!"PASS {name}" else
    IO.println s!"FAIL {name}"; failures.modify (· + 1)

def sameWorld (a b : World Nat) : Bool := a.height == b.height && a.chain == b.chain

def run (args : List String) : IO UInt32 := do
  let seed := (args.head? >>= String.toNat?).getD 1
  let failures ← IO.mkRef 0
  let sc := scenario seed 200
  let frames := sc.map (·.1)
  let r ← runOnce seed frames none
  let w := r.resident.world
  let statusOf (k : Kind) := sc.zip r.replies.toList |>.filter (·.1.2 = k) |>.map (·.2.status)
  check "one reply per request" (r.replies.size = 200) failures
  check "loop ended at eof" (match r.exit with | .eof => true | _ => false) failures
  check "fresh turns admitted" ((statusOf .fresh).all (· = Protocol.Status.ok.code)) failures
  check "replays answered ok" ((statusOf .replay).all (· = Protocol.Status.ok.code)) failures
  check "a used txId answers ok, admitting nothing" ((statusOf .sameTxId).all (· = Protocol.Status.ok.code)) failures
  check "double spends refused" ((statusOf .doubleSpend).all (· = Protocol.Status.refused.code)) failures
  check "height = fresh turns" (w.height = (statusOf .fresh).length) failures
  let seals := r.bases.history.size - 1
  IO.println s!"admitted {w.height} turns in {r.disk.syncs} batches, {r.disk.synced.size} bytes, {seals} seals"
  let opened := reopen r.bases.file r.disk.synced
  check "open clean: the whole image, no torn tail"
    (match opened with | .ok o => o.opened.torn = 0 ∧ o.pos.offset = r.disk.synced.size | .error _ => false) failures
  check "open = loop World (height, chain)"
    (match opened with | .ok o => sameWorld o.opened.world w | .error _ => false) failures
  check "the loop sealed at the cadence (at least two bases after genesis)" (2 ≤ seals) failures
  check "open reads one base and at most tailMax of segment"
    (match opened with
     | .ok o => decide (o.pos.offset - o.sealed.offset ≤ cadence.tailMax o.sealed.bytes)
     | .error _ => false) failures
  -- plant-crash-before-rename: base k-1 with the segment as it stood when base k became durable
  let mut renameOk := true
  for k in List.range seals do
    let (older, _) := r.bases.history[k]!
    let (newer, durableAt) := r.bases.history[k + 1]!
    let seg := r.disk.synced.extract 0 durableAt
    match reopen older seg, reopen newer seg with
    | .ok a, .ok b =>
      unless sameWorld a.opened.world b.opened.world && a.pos.offset = b.pos.offset do
        renameOk := false; IO.println s!"  seal {k + 1}: the older base folds to a different World"
    | a, b =>
      renameOk := false; IO.println s!"  seal {k + 1}: older {faultName a}, newer {faultName b}"
  check s!"plant-crash-before-rename at each of {seals} seals: the older base + tail = the newer base" renameOk failures
  check "plant-tail-too-long: the genesis base with the whole segment is refused `tailTooLong`"
    (faultName (reopen r.bases.history[0]!.1 r.disk.synced) = "tailTooLong") failures
  check "plant-base-flip: a flipped base byte is `baseCorrupt`"
    (faultName (reopen (flipByte r.bases.file 40) r.disk.synced) = "baseCorrupt") failures
  -- waste (law 5): work done ÷ work the operation must do
  let records := (Log.recover keys.segment cadence.recordBytesMax segmentInitial r.disk.synced).records
  let turns := records.foldl (fun acc rec => match (Record.codec dc).decode rec with
    | .ok (ts, _) => acc ++ ts | .error _ => acc) []
  let admittedBytes := turns.foldl (fun n t => n + (turnCodec.bytes t).size) 0
  -- log pages (Host.Page) over the durable segment and the loop's index
  let page (budget start : Nat) := Id.run (Page.build env dc digestOf keys.segment cadence.recordBytesMax
    budget (fun off len => pure (r.disk.synced.extract off (off + len))) r.resident.index
    (recorder.mark w) start)
  let mut start := 0
  let mut served := 0
  let mut pagesOk := true
  let mut pageCount := 0
  for _ in List.range (w.height + 1) do
    if w.height ≤ start then break
    match page 40 start with
    | .error f => pagesOk := false; IO.println s!"  page from {start}: {f.name}"; break
    | .ok a =>
      if a.height ≤ start then pagesOk := false; break
      -- the stated chain is the chain of the log's first `a.height` Turns
      unless a.chain = env.bytes (chainOf env genesis.chain (turns.take a.height)) do
        pagesOk := false; IO.println s!"  page from {start} states a wrong chain at {a.height}"
      -- a page ending anywhere states the chain the rest of the log continues from
      match page Page.budget start with
      | .ok whole => unless whole.height = w.height ∧ whole.chain = env.bytes w.chain do pagesOk := false
      | .error _ => pagesOk := false
      served := served + a.events.size; start := a.height; pageCount := pageCount + 1
  -- a one-event page from EVERY height, mid-record ones included
  for s in List.range w.height do
    match page 4 s with
    | .ok a =>
      unless a.height = s + 1 ∧ a.chain = env.bytes (chainOf env genesis.chain (turns.take (s + 1))) do
        pagesOk := false; IO.println s!"  one-event page from {s}: height {a.height}"
    | .error f => pagesOk := false; IO.println s!"  one-event page from {s}: {f.name}"
  let lastOk := match page 40 start with
    | .ok a => a.events.size = 0 ∧ a.height = w.height ∧ a.chain = env.bytes w.chain
    | .error _ => false
  check s!"log pages: {pageCount} pages of 10 events serve every event once, each page states the log's chain at its last height; a one-event page from every height"
    (pagesOk && served = w.height && lastOk) failures
  check "plant-page-flip: a flipped byte in a served frame is refused `corrupt`"
    (match Id.run (Page.build env dc digestOf keys.segment cadence.recordBytesMax Page.budget
        (fun off len => pure ((flipByte r.disk.synced 6).extract off (off + len))) r.resident.index
        (recorder.mark w) 0) with
     | .error f => f.name = "corrupt" | .ok _ => false) failures
  IO.println s!"WASTE submit bytes-per-turn {ratio r.disk.synced.size admittedBytes}"
  IO.println s!"WASTE submit fsyncs-per-batch {ratio r.disk.syncs records.length}"
  let tailBytes := match opened with | .ok o => o.pos.offset - o.sealed.offset | .error _ => 0
  -- what open must read: the base record (World, offset, tag, index) and the tail; the excess is
  -- the base's own frame
  let needed := r.bases.file.size - 4 - Log.tagBytes + tailBytes
  IO.println s!"WASTE open bytes-read-per-record {ratio (r.bases.file.size + tailBytes) needed}"
  let genesisBytes := r.bases.history[0]!.1.size
  IO.println s!"WASTE seal bytes-per-appended-byte {ratio (r.bases.written - genesisBytes) r.disk.synced.size}"
  let r2 ← runOnce (seed + 7919) frames none
  IO.println s!"second split: {r2.disk.syncs} batches"
  check "a different batch split reaches the same chain" (r2.resident.world.chain = w.chain) failures
  -- plant-world-too-large
  let tiny := { cadence with worldBytesMax := 400 }
  let t ← runWith tiny seed frames none
  check "plant-world-too-large: the loop stops `sealFailed worldTooLarge`"
    (match t.exit with | .sealFailed f => f.name = "worldTooLarge" | _ => false) failures
  -- plant-fsync-fail, then plant-restart-at-every-cut
  let p ← runOnce seed frames (some 3)
  let pendingSize := p.disk.pending.size
  check "plant-fsync-fail: loop stops uncertain"
    (match p.exit with | .uncertain _ => true | _ => false) failures
  let uncertainN := (p.replies.toList.filter (·.status = Protocol.Status.uncertain.code)).length
  let lastBatch := p.replies.toList.drop (p.replies.size - uncertainN)
  check "plant-fsync-fail: the batch's replies are uncertain"
    (0 < uncertainN ∧ lastBatch.all (·.status = Protocol.Status.uncertain.code) ∧ pendingSize > 0) failures
  let baseOpen := reopen p.bases.file p.disk.synced
  let baseRecords := match baseOpen with | .ok o => o.opened.records | .error _ => 0
  check "plant-fsync-fail: synced prefix opens" (match baseOpen with | .ok o => o.pos.offset = p.disk.synced.size | .error _ => false) failures
  -- every crash cut of the unsynced frame: open (truncating the torn tail, as the writer does),
  -- resend the uncertain batch and the rest, and reach the no-crash chain.
  let resend := frames.drop (p.replies.size - uncertainN)
  let mut cutsOk := true
  for cut in List.range (pendingSize + 1) do
    match reopen p.bases.file (crashImage p.disk cut) with
    | .error e =>
      cutsOk := false; IO.println s!"  cut {cut}: open refused {e.name}"
    | .ok o =>
      let expectTorn := if cut = pendingSize then 0 else cut
      let expectRecords := if cut = pendingSize then baseRecords + 1 else baseRecords
      let img := (crashImage p.disk cut).extract 0 o.pos.offset
      let q ← serveFrom cadence seed resend none { synced := img } p.bases
        { world := o.opened.world, pos := o.pos, sealed := o.sealed, index := o.index }
      let finalOk : Bool := match reopen q.bases.file q.disk.synced with
        | .ok o' => o'.opened.torn = 0 && sameWorld o'.opened.world w && sameWorld q.resident.world w
        | .error _ => false
      unless decide (o.opened.torn = expectTorn ∧ o.opened.records = expectRecords) && finalOk do
        cutsOk := false
        IO.println s!"  cut {cut}: torn {o.opened.torn} records {o.opened.records} final {finalOk}"
  check s!"plant-restart-at-every-cut 0..{pendingSize}: open, truncate, resend, reach the no-crash chain" cutsOk failures
  -- the flip plants, on a multi-frame tail: the genesis base with the segment up to the first seal
  let (g, _) := r.bases.history[0]!
  let firstSeg := r.disk.synced.extract 0 r.bases.history[1]!.2
  let full := match reopen g firstSeg with | .ok o => o.opened.records | .error _ => 0
  check "plant-flip-byte: corrupt" (1 < full && isCorrupt (reopen g (flipByte firstSeg 6)) 0) failures
  check "plant-flip-header: corrupt (the frames after it are found by the forward scan)"
    (isCorrupt (reopen g (flipByte firstSeg 0)) 0) failures
  check "plant-flip-last-frame: torn (the stated undecidable case: one frame lost, loudly)"
    (match reopen g (flipByte firstSeg (firstSeg.size - 1)) with
     | .ok o => 0 < o.opened.torn ∧ o.opened.records + 1 = full
     | .error _ => false) failures
  let n ← failures.get
  IO.println (if n = 0 then "ALL PASS" else s!"{n} FAILED")
  return (if n = 0 then 0 else 1)

end Nanodregg.Host.Sim
