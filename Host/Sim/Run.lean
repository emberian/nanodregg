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
import Host.Serve
import Host.Tail
import Kernel.Sim

namespace Nanodregg.Host.Sim

open Nanodregg.Kernel

/-- A deterministic generator (64-bit LCG). -/
def lcg (s : Nat) : Nat := (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

def receipt (h d : Nat) : ByteArray := le64 h ++ le64 d

def machine : Machine (World Nat) (Turn Nat) (Reject Nat) Frame where
  admit := World.admit env
  handle _ f :=
    match hangUpAnswer f with
    | some (st, p) => .reply st p
    | none =>
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
  Id.run (openWith keys c world recorder.mark foldStep base seg.size (segReader seg))

def reopen (base seg : ByteArray) : Except Fault (Opening (World Nat)) := reopenWith cadence base seg

def faultName (r : Except Fault (Opening (World Nat))) : String :=
  match r with
  | .error f => f.name
  | .ok _ => "opened"

/-- The in-memory Store as genesis leaves it (`memGenesis`). -/
def genesisStore (c : Cadence) : Except Fault (Disk × Bases × Resident (World Nat)) :=
  memGenesis keys c world recorder.mark foldStep genesis

structure RunResult where
  exit : Exit
  resident : Resident (World Nat)
  replies : Array Reply
  disk : Disk
  bases : Bases
  /-- in-process reopens at fuel restarts -/
  reopens : Nat
  /-- fuel returns at which the replies sent were not the frames taken from the port -/
  unanswered : Nat

/-- The in-process reopen of a fuel restart over the in-memory image (what `Host.reopenAt` does over
the files): the one open of the newest base and the synced segment; unsynced bytes are a divergence. -/
def memReopen (c : Cadence) (disk : IO.Ref Disk) (bases : IO.Ref Bases) (reopens : IO.Ref Nat) :
    IO (Except Exit (Resident (World Nat))) := do
  reopens.modify (· + 1)
  let d ← disk.get
  if 0 < d.pending.size then return .error .reopenDiverged
  match reopenWith c (← bases.get).file d.synced with
  | .error f => return .error (.reopenFailed f.name)
  | .ok o => return if o.opened.torn = 0 then .ok { world := o.opened.world, pos := o.pos, sealed := o.sealed, index := o.index } else .error .reopenDiverged

/-- Serve `frames` from a disk, its bases, and the state they opened to, in rounds of `roundFuel`
batches, each ending in an in-process reopen (`Host.restarts`, D4). -/
def serveFrom (c : Cadence) (seed : Nat) (frames : List Frame) (failSyncAt : Option Nat) (d : Disk)
    (b : Bases) (r : Resident (World Nat)) (roundFuel : Nat := frames.length + 1)
    (limits : Limits := ⟨16, 1 <<< 20⟩) (dropUnread : Bool := false) : IO RunResult := do
  let disk ← IO.mkRef d
  let bases ← IO.mkRef b
  let fr ← IO.mkRef frames
  let sp ← IO.mkRef (splits seed frames.length)
  let sent ← IO.mkRef #[]
  let reopens ← IO.mkRef 0
  let unanswered ← IO.mkRef 0
  -- at every fuel return, before the reopen: every frame taken from the port has its reply
  let reopen : IO (Except Exit (Resident (World Nat))) := do
    let taken := frames.length - (← fr.get).length
    if (← sent.get).size ≠ taken then
      unanswered.modify (· + 1)
      unless dropUnread do  -- the plant run expects it; its check reads the count
          IO.println s!"FAIL requests = replies at fuel return {← reopens.get}: {taken} taken, {(← sent.get).size} answered"
    memReopen c disk bases reopens
  let (exit, r) ← restarts (serve machine recorder keys.segment (memCheckpoint disk bases keys c world) c
      (memStore disk failSyncAt) (fun _ _ => pure (0, ByteArray.empty))
      (if dropUnread then { scriptPort fr sp sent with unread := fun _ => pure () } else scriptPort fr sp sent)
      limits roundFuel)
    reopen recorder.mark (frames.length + 2) r
  return ⟨exit, r, ← sent.get, ← disk.get, ← bases.get, ← reopens.get, ← unanswered.get⟩

def runWith (c : Cadence) (seed : Nat) (frames : List Frame) (failSyncAt : Option Nat)
    (roundFuel : Nat := frames.length + 1) (limits : Limits := ⟨16, 1 <<< 20⟩) (dropUnread := false) :
    IO RunResult := do
  match genesisStore c with
  | .ok (d, b, r) => serveFrom c seed frames failSyncAt d b r roundFuel limits dropUnread
  | .error f => throw (IO.userError s!"genesis: {f.name}")

/-- Where the log after genesis's origin frame starts (every record the loop writes is after it). -/
def origin : Position :=
  match genesisStore cadence with
  | .ok (_, _, r) => r.pos
  | .error _ => ⟨0, Codec.Digest.zero⟩

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
  -- read pages (HOST-15): the newest base's World bytes, paged at 100 bytes
  let basesRef ← IO.mkRef r.bases
  let mut got := ByteArray.empty
  let mut readOk := true
  let mut readPages := 0
  for _ in List.range (r.resident.sealed.bytes / 100 + 2) do
    if r.resident.sealed.bytes ≤ got.size then break
    let (st, p) ← memBasePage 100 basesRef r.resident got.size
    match Protocol.readReplyFrame.decode p with
    | .ok (h, t, d, c, b, ()) =>
      unless st = Protocol.Status.ok.code ∧ Protocol.Text.ofU64 h.1 = some r.resident.sealed.height do
        readOk := false
      unless Protocol.Text.ofU64 t.1 = some r.resident.sealed.bytes ∧ d.1 = r.resident.sealed.digest ∧
          c.1 = r.resident.sealed.chain ∧ 0 < b.1.size do readOk := false
      got := got ++ b.1; readPages := readPages + 1
    | .error _ => readOk := false; break
  check s!"read pages: {readPages} pages assemble the base's World bytes, and they hash to the stated digest"
    (readOk && got == worldBytesOf r.bases.file r.resident.sealed.bytes &&
      keys.worldDigest got == r.resident.sealed.digest) failures
  check "plant-read-past-end: a read past the World bytes is refused `pastEnd`"
    ((← memBasePage 100 basesRef r.resident (r.resident.sealed.bytes + 1)).2 == "pastEnd".toUTF8) failures
  -- waste (law 5): work done ÷ work the operation must do
  let records := (Log.recover keys.segment cadence.recordBytesMax origin.tag.bytes
    (r.disk.synced.extract origin.offset r.disk.synced.size)).records
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
        (fun off len => pure ((flipByte r.disk.synced (origin.offset + 6)).extract off (off + len))) r.resident.index
        (recorder.mark w) 0) with
     | .error f => f.name = "corrupt" | .ok _ => false) failures
  IO.println s!"WASTE submit bytes-per-turn {ratio (r.disk.synced.size - origin.offset) admittedBytes}"
  IO.println s!"WASTE submit fsyncs-per-batch {ratio r.disk.syncs records.length}"
  let tailBytes := match opened with | .ok o => o.pos.offset - o.sealed.offset | .error _ => 0
  -- what open must read: the base record (World, offset, tag, index) and the tail; the excess is
  -- the base's own frame
  let needed := r.bases.file.size - 4 - Log.tagBytes + tailBytes
  IO.println s!"WASTE open bytes-read-per-record {ratio (r.bases.file.size + tailBytes) needed}"
  let genesisBytes := r.bases.history[0]!.1.size
  IO.println s!"WASTE seal bytes-per-appended-byte {ratio (r.bases.written - genesisBytes) r.disk.synced.size}"
  -- plant-tail (HOSTING-7): a tail opened at genesis absorbs the writer's whole segment one frame
  -- bound at a time and reaches the writer's World, with every admitted Turn reported once in order.
  -- Its mutation: a byte flipped inside an early frame must be refused `corrupt`, not skipped.
  let tailRun (seg : ByteArray) : Except String (Tail (World Nat) × Nat × Nat) := Id.run do
    let mut t : Tail (World Nat) := ⟨genesis, origin⟩
    let mut turns := 0
    let mut calls := 0
    let bound := Log.frameMax cadence.recordBytesMax
    for _ in [0:seg.size + 1] do
      if seg.size ≤ t.pos.offset then break
      let len := min (seg.size - t.pos.offset) bound
      match Tail.absorb keys.segment cadence.recordBytesMax tailStep t
          (seg.extract t.pos.offset (t.pos.offset + len)) (decide (bound < seg.size - t.pos.offset)) with
      | .error f => return .error f.name
      | .ok (t', os) =>
        calls := calls + 1
        turns := turns + os.foldl (fun n ts => n + ts.length) 0
        if t'.pos.offset == t.pos.offset then return .error "stuck"
        t := t'
    return .ok (t, turns, calls)
  match tailRun r.disk.synced with
  | .ok (t, turns, calls) =>
    check s!"plant-tail: a tail from genesis reaches the writer's World in {calls} reads, every one of {turns} Turns reported once"
      (sameWorld t.world r.resident.world && turns = r.resident.world.height && 1 < calls &&
        t.pos.offset = r.disk.synced.size) failures
  | .error e => check s!"plant-tail: a tail from genesis reaches the writer's World ({e})" false failures
  check "plant-tail: a flipped byte in an early frame is refused `corrupt`, never skipped"
    (match tailRun (flipByte r.disk.synced (origin.offset + 6)) with
     | .error e => e = "corrupt"
     | .ok _ => false) failures
  let r2 ← runOnce (seed + 7919) frames none
  IO.println s!"second split: {r2.disk.syncs} batches"
  check "a different batch split reaches the same chain" (r2.resident.world.chain = w.chain) failures
  -- D4: rounds of 3 batches, each ending in an in-process reopen from the image, and batches cut
  -- by bytes so frames are put back into the port (at round ends too)
  let tight : Limits := ⟨16, 3 * (frames.head?.map (·.payload.size)).getD 1⟩
  let f3 ← runWith cadence seed frames none 3 tight
  let ref ← runWith cadence seed frames none (frames.length + 1) tight
  check s!"fuel restarts: {f3.reopens} in-process reopens, one reply per request, the same replies in the same order as without restarts, the same chain"
    (2 ≤ f3.reopens && f3.replies.size = 200 && (match f3.exit with | .eof => true | _ => false) &&
      sameWorld f3.resident.world w &&
      (f3.replies.toList.zip ref.replies.toList).all fun (a, b) => a.conn == b.conn && a.status == b.status && a.payload == b.payload)
    failures
  check s!"requests = replies at every one of {f3.reopens} fuel returns" (f3.unanswered = 0) failures
  let dropped ← runWith cadence seed frames none 3 tight (dropUnread := true)
  check s!"plant-drop-unread: a port that drops a put-back frame loses replies ({dropped.replies.size} of 200), so the check above can see a dropped frame"
    (dropped.replies.size < 200 && 0 < dropped.unanswered) failures
  -- plant-reopen-diverged: a reopen that loses the last synced frame is refused, never served from
  let fr ← IO.mkRef frames
  let sp ← IO.mkRef (splits seed frames.length)
  let sent ← IO.mkRef #[]
  let (gd, gb, gr) ← match genesisStore cadence with
    | .ok g => pure g
    | .error f => throw (IO.userError s!"genesis: {f.name}")
  let disk ← IO.mkRef gd
  let bases ← IO.mkRef gb
  let (dexit, _) ← restarts (serve machine recorder keys.segment (memCheckpoint disk bases keys cadence world)
      cadence (memStore disk none) (fun _ _ => pure (0, ByteArray.empty)) (scriptPort fr sp sent)
      ⟨16, 1 <<< 20⟩ 3)
    (do
      let d ← disk.get
      match reopenWith cadence (← bases.get).file (d.synced.extract 0 (d.synced.size - 1)) with
      | .error f => return .error (.reopenFailed f.name)
      | .ok o => return .ok { world := o.opened.world, pos := o.pos, sealed := o.sealed, index := o.index }) recorder.mark 10 gr
  check "plant-reopen-diverged: a reopen missing the last synced byte stops the resident `reopenDiverged`"
    (match dexit with | .reopenDiverged => true | _ => false) failures
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
  check "plant-flip-byte: corrupt" (1 < full && isCorrupt (reopen g (flipByte firstSeg (origin.offset + 6))) 0) failures
  check "plant-flip-header: corrupt (the frames after it are found by the forward scan)"
    (isCorrupt (reopen g (flipByte firstSeg origin.offset)) 0) failures
  check "plant-flip-last-frame: torn (the stated undecidable case: one frame lost, loudly)"
    (match reopen g (flipByte firstSeg (firstSeg.size - 1)) with
     | .ok o => 0 < o.opened.torn ∧ o.opened.records + 1 = full
     | .error _ => false) failures
  -- plant-foreign-segment (HOST-18): another Store's segment (the same records under another
  -- key) under this Store's bases. Before HOST-18 it opened as a torn tail of up to frameMax
  -- bytes and the writer truncated it (87c721e: records=0 torn=1750, truncated to 0).
  let other : Log.Sealer := fnvSealer 7
  let foreignOf (seg : ByteArray) : ByteArray :=
    Log.encodeAll other segmentInitial (Log.recover keys.segment cadence.recordBytesMax segmentInitial seg).records
  let foreignFirst := foreignOf firstSeg
  let foreignAll := foreignOf r.disk.synced
  -- the mutation happened: same length, different bytes at the genesis base's anchor
  check "plant-foreign-segment fires: the foreign segment differs at the anchor, same length"
    (foreignFirst.size = firstSeg.size && foreignAll.size = r.disk.synced.size &&
      foreignFirst.extract 0 origin.offset != firstSeg.extract 0 origin.offset) failures
  check "plant-foreign-segment: under the genesis base, refused `foreignSegment` (not torn)"
    (faultName (reopen g foreignFirst) = "foreignSegment") failures
  check "plant-foreign-segment: under the newest base (offset > 0), refused `foreignSegment`"
    (0 < (match reopen r.bases.file r.disk.synced with | .ok o => o.sealed.offset | .error _ => 0) &&
      faultName (reopen r.bases.file foreignAll) = "foreignSegment") failures
  -- plant-old-shape (D2, HOST-20): the newest base re-sealed, byte for byte the same base, by a
  -- binary whose batch record admits one more Turn (another batch shape, so another stamp). The
  -- running binary must refuse it `shapeMismatch` by name; the binary that wrote it opens it.
  let oldKeys : Keys := { keys with shapes := Base.shapeStamp world (Codec.Kernel.batch (recordTurnsMax + 1) dc) }
  let oldBase : Option ByteArray :=
    match Base.read keys cadence world r.bases.file with
    | .ok (b, _, _) =>
      match Base.file oldKeys cadence world b.world b.offset b.tag b.index with
      | .ok f => some f
      | .error _ => none
    | .error _ => none
  match oldBase with
  | none => check "plant-old-shape: the newest base re-seals under the old shapes" false failures
  | some ob =>
    check "plant-old-shape fires: another stamp, and the writing binary opens it"
      (oldKeys.shapes.bytes != keys.shapes.bytes &&
        faultName (Id.run (openWith oldKeys cadence world recorder.mark foldStep ob r.disk.synced.size
          (segReader r.disk.synced))) = "opened") failures
    check "plant-old-shape: the running binary refuses the old shape `shapeMismatch` (never decoded)"
      (faultName (reopen ob r.disk.synced) = "shapeMismatch") failures
  -- plant-lookup-expired (HOST-21): the writer's `lookup` arm (Host.handle) over the kernel-sim
  -- Ctx (CODEC's call codec and decodeCall). At genesis (height 0) an un-journaled call whose window
  -- ends at 0 can never be admitted: `refused expired`; one ending at 1 may still land: `absent`.
  let kx := Kernel.Sim.ctx
  let kw : World Kernel.Sim.D := World.genesis kx.env "lookup".toUTF8 (2 ^ 40)
  let callUntil (v : Nat) : Receive.Call Kernel.Sim.D :=
    { unsigned := { member := 0, key := ByteArray.empty, notBefore := 0, validUntil := v, pins := [],
                    maxCharge := 0, body := .revoke 0 },
      signature := ByteArray.empty }
  let lookupAt (v : Nat) : String :=
    match handle kx kw ⟨0, Protocol.Op.lookup.code, kx.callBytes (callUntil v)⟩ with
    | .reply s p =>
      if s == Protocol.Status.absent.code then "absent"
      else if s == Protocol.Status.refused.code then (String.fromUTF8? p).getD "?" else "other"
    | _ => "other"
  check "plant-lookup-expired fires: the call decodes, and its window is the one asked"
    ((kx.decodeCall (kx.callBytes (callUntil 0))).map (·.unsigned.validUntil) == some 0) failures
  check "plant-lookup-expired: a dead call's lookup answers `refused expired`, not `absent`"
    (lookupAt 0 == "expired") failures
  check "plant-lookup-expired: a call that may still land answers `absent`"
    (lookupAt 1 == "absent") failures
  -- plant-hangup (PROTOCOL-23): a hang-up after every 7th request, for connections that are not
  -- the requests' own; each is acknowledged exactly once by name, and every other reply is the
  -- reply of the run without them
  let hangs := (List.range 200).filter (· % 7 = 3)
  let mixed := (frames.zipIdx.flatMap fun (f, i) =>
    if hangs.contains i then [f, ⟨UInt32.ofNat (900000 + i), Protocol.hangupCode, "idle".toUTF8⟩] else [f])
  let h ← runOnce seed mixed none
  let (acks, rest) := h.replies.toList.partition (900000 ≤ ·.conn.toNat)
  check s!"plant-hangup: {hangs.length} hang-ups mid-batch each acked once `closed idle`, no other reply changed"
    (acks.length = hangs.length &&
      acks.all (fun a => a.status = Protocol.Status.closed.code && a.payload == "idle".toUTF8) &&
      (acks.map (·.conn.toNat)) == hangs.map (900000 + ·) &&
      rest.map (fun a => (a.conn, a.status, a.payload)) == r.replies.toList.map (fun a => (a.conn, a.status, a.payload)) &&
      h.resident.world.chain = w.chain) failures
  let n ← failures.get
  IO.println (if n = 0 then "ALL PASS" else s!"{n} FAILED")
  return (if n = 0 then 0 else 1)

end Nanodregg.Host.Sim
