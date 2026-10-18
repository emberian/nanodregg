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
   `worldBytesMax` the World outgrows stops the loop `sealFailed worldTooLarge`; plant-world-at-cap: a
   World of exactly `worldBytesMax` bytes is written and opens to itself (HOST-39: the base bound
   counts the stamp).

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
import Host.Carry

namespace Nanodregg.Host.Sim

open Nanodregg.Kernel

/-- A deterministic generator (64-bit LCG). -/
def lcg (s : Nat) : Nat := (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

def receipt (h d : Nat) : ByteArray := le64 h ++ le64 d

/-- The toy frames carry a STEP (CODEC's `step` codec: a Turn, or a refusal record): the sim
exercises the log, the open and the pages, not the receive layer (`Host.handle` is `Receive.judge`'s,
`Host.Proofs.Serve.step_submit`). Every step is committed through `World.step`. -/
def stepCodec : Codec.Stream (Step Nat) := Codec.Kernel.step dc

def submitFrame (i : Nat) (s : Step Nat) : Frame := ⟨UInt32.ofNat i, Protocol.Op.submit.code, stepCodec.bytes s⟩

def machine : Machine (World Nat) (Step Nat) Frame Nat where
  note := World.roots env
  handle w f :=
    match hangUpAnswer f with
    | some (st, p) => .reply st p
    | none =>
    match stepCodec.decode f.payload with
    | .ok s =>
      match World.step env w s with
      | .ok w' =>
        match s with
        | .turn t => .commit s w' Protocol.Status.ok.code (receipt w'.height (turnDigest env t))
        | .refusal r => .commit s w' Protocol.Status.refused.code (le64 r.code)
      | .error (.replayed h) =>
        match s with
        | .turn t => match w.journalAt env t.txId with
          | some (_, d) => .reply Protocol.Status.ok.code (receipt h d)
          | none => .reply Protocol.Status.refused.code "replayed".toUTF8
        | .refusal _ => .reply Protocol.Status.refused.code "replayed".toUTF8
      | .error r => .reply Protocol.Status.refused.code r.name.toUTF8
    | .error _ => .reply Protocol.Status.refused.code "undecodable".toUTF8
  ok := Protocol.Status.ok.code

def genesis : World Nat := World.genesis env (env.hash "nanodregg/host-sim/origin/v1" "sim".toUTF8) (2 ^ 40)

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
      let f : Frame := submitFrame i (.turn t)
      go k s' (if kind = .fresh then t :: made else made) ((f, kind) :: acc)

/-- Seeded batch boundaries: `true` = the next frame is already queued. -/
def splits (seed n : Nat) : List Bool :=
  (List.range n).foldl (fun (s, acc) _ => let s' := lcg s; (s', ((s' / 4096) % 3 != 0) :: acc))
    (seed, []) |>.2.reverse

abbrev Fault := StoreFault (Record.Fault (Reject Nat))

/-- The one open over an in-memory image: `openWith` reading bytes. -/
def reopenWith (c : Cadence) (index base seg : ByteArray) : Except Fault (Opening (World Nat)) :=
  Id.run (openWith keys c world recorder.mark originChain foldStep base seg.size index.size (segReader index)
    (segReader seg))

/-- The open of a base and segment under the `index.log` bytes `index`. -/
def reopenIn (index base seg : ByteArray) : Except Fault (Opening (World Nat)) := reopenWith cadence index base seg

def faultName (r : Except Fault (Opening (World Nat))) : String :=
  match r with
  | .error f => f.name
  | .ok _ => "opened"

/-- Every entry `index` holds at its position, while each reads back (`Entry.read`). -/
def entriesOf (k : Keys) (index : ByteArray) : List Entry :=
  go (index.size / entryBytes k) 0 []
where
  go : Nat → Nat → List Entry → List Entry
    | 0, _, acc => acc.reverse
    | n + 1, i, acc =>
      match Entry.read k i (index.extract (i * entryBytes k) (i * entryBytes k + entryBytes k)) with
      | some e => go n (i + 1) (e :: acc)
      | none => acc.reverse

/-- A `log` page over an in-memory Store (`Page.build` with `Page.entryAt`, as `Host.Deployed.pager`
does over the files), with the number of index entries it read (its getter counts each call). -/
def memPage (index seg : ByteArray) (r : Resident (World Nat)) (budget start : Nat) :
    Except Page.Fault Page.Acc × Nat :=
  let get (i : Nat) : StateM Nat (Except Page.Fault Entry) := do
    modify (· + 1)
    Page.entryAt (keys.forStore (originChain r.world)) (fun off len => pure (index.extract off (off + len)))
      r.sealed.index.count r.index i
  (Page.build env dc digestOf keys.segment cadence.recordBytesMax budget
    (fun off len => pure (seg.extract off (off + len))) get (r.sealed.index.count + r.index.size) r.pos.offset
    (recorder.mark r.world) start).run 0

/-- 1 + ⌈log₂ n⌉ for n ≥ 1: the most entries `Page.locate` reads over n. -/
def probeBound (n : Nat) : Nat := 1 + (Nat.log2 (2 * n - 1))

/-- The in-memory Store as genesis leaves it (`memGenesis`). -/
def genesisStore (c : Cadence) : Except Fault (Disk × Bases × Resident (World Nat)) :=
  memGenesis keys c world recorder.mark originChain foldStep genesis

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
  let b ← bases.get
  match reopenWith c b.index b.file d.synced with
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
  let (exit, r) ← restarts (serve machine recorder keys.segment (memCheckpoint disk bases keys c world originChain) c
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

/-- HOST-17's count at one Store length: a run of `n` fresh Turns (seeded batch splits), and at
its LAST seal the index bytes that seal wrote (its page in `index.log`, HOST-30), the segment
bytes appended since the base before it, the base file's size, and how many seals the run made.
Before HOST-30 the base re-encoded one entry per record ever written, so the term grew with the
batches; a page holds only the entries since the last base. -/
def indexTerm (seed n : Nat) : IO (Nat × Nat × Nat × Nat) := do
  let frames : List Frame := (List.range n).map fun i =>
    submitFrame i (.turn (mkTurn (1000 + i) 0 1024 [5000 + i]))
  let r ← runOnce seed frames none
  let h := r.bases.history
  if h.size < 2 then return (0, 0, 0, h.size - 1)
  let ix := r.bases.indexAt
  match Base.read keys cadence world h[h.size - 1]!.1, Base.read keys cadence world h[h.size - 2]!.1 with
  | .ok (b, _, _), .ok (a, _, _) =>
    return (ix[h.size - 1]! - ix[h.size - 2]!, b.offset - a.offset, h[h.size - 1]!.1.size, h.size - 1)
  | _, _ => return (0, 0, 0, h.size - 1)

/-- The Store lengths (fresh Turns) HOST-17's count is measured at. -/
def indexLengths : List Nat := [100, 200, 400, 800]

/-- HOST-33's two counts at one Store length (a run of `n` fresh Turns): the most index entries a
one-event `log` page reads, over a page from EVERY height (against `probeBound` of the index
size: O(log records), law 5), and the entries the loop holds against the records past its newest
base, counted independently by `Log.recover` (RAM O(tail), not O(records)). Also: every page is
served (none refused). -/
def entryRows (seed n : Nat) (failures : IO.Ref Nat) : IO Unit := do
  let frames : List Frame := (List.range n).map fun i =>
    submitFrame i (.turn (mkTurn (1000 + i) 0 1024 [5000 + i]))
  let r ← runOnce seed frames none
  let total := r.resident.sealed.index.count + r.resident.index.size
  let mut most := 0
  let mut served := true
  for s in List.range r.resident.world.height do
    let (p, probes) := memPage r.bases.index r.disk.synced r.resident 5 s
    if probes > most then most := probes
    match p with
    | .ok a => served := served && a.steps == s + 1
    | .error _ => served := false
  let records := (Log.recover keys.segment cadence.recordBytesMax segmentInitial r.disk.synced).records.length - 1
  let past := records - r.resident.sealed.index.count
  check s!"index pages at {n} turns: a one-event page from every one of {r.resident.world.height} heights is served, reading at most {most} of {total} entries ({probeBound total} bound)"
    (served && 0 < most && most ≤ probeBound total && total = records) failures
  IO.println s!"page index entries read per request at {n} turns: {most} (bound {probeBound total} over {total} entries)"
  IO.println s!"WASTE page index-entries-read-per-log-bound-at-{n} {ratio most (probeBound total)}"
  IO.println s!"loop at {n} turns: {r.resident.index.size} entries held, {past} records past the newest base ({r.resident.sealed.index.count} on disk)"
  IO.println s!"WASTE loop resident-entries-per-record-past-base-at-{n} {ratio r.resident.index.size past}"

/-- HOST-33's index plants, under the run's newest base (which counts a non-empty index). The ruled
move (condition 5): a corrupt MIDDLE entry was refused at open; it is now refused at first read
(`badIndex`, never served) or by `host check` (`indexClean`). -/
def entryPlants (r : RunResult) (failures : IO.Ref Nat) : IO Unit := do
  let reopen := reopenIn r.bases.index
  let opened := reopen r.bases.file r.disk.synced
  let count := match opened with | .ok o => o.sealed.index.count | .error _ => 0
  let eb := entryBytes keys
  let named := count * eb
  let sk := keys.forStore (originChain genesis)
  let honest := entriesOf sk r.bases.index
  let records := (Log.recover keys.segment cadence.recordBytesMax segmentInitial r.disk.synced).records
  let offsets := recordOffsets (records.take (count + 1))
  check s!"index control: the newest base counts {count} entries, index.log holds exactly them, every one reads back and names its record's offset (`indexClean` none)"
    (1 < count && r.bases.index.size = named && honest.length = count &&
      indexClean sk r.bases.index count offsets == none) failures
  check "plant-index-short: index.log one byte short of the entries the base counts is refused `indexShort`"
    (faultName (reopenIn (r.bases.index.extract 0 (named - 1)) r.bases.file r.disk.synced) = "indexShort") failures
  check "plant-index-last-flip: a flipped byte in the last entry (the one open reads) is refused `indexCorrupt`"
    (faultName (reopenIn (flipByte r.bases.index (named - eb / 2)) r.bases.file r.disk.synced) = "indexCorrupt") failures
  let otherKeys : Keys := { keys with index := fnvSealer 9 }
  let retagged := Entry.run (otherKeys.forStore (originChain genesis)) 0 honest
  check "plant-index-other-key: the same entries tagged under another key are refused `indexCorrupt`"
    (retagged.size = named && retagged != r.bases.index &&
      faultName (reopenIn retagged r.bases.file r.disk.synced) = "indexCorrupt") failures
  -- plant-index-other-store (HOST-33's law-6 read): the same entries tagged for ANOTHER Store under
  -- the SAME key file (HOST-25's shared-key case). Spliced whole, open refuses the last; spliced
  -- into the middle, `host check` refuses it and no page is built from it
  let otherWorld : World Nat := World.genesis env (env.hash "nanodregg/host-sim/origin/v1" "other".toUTF8) (2 ^ 40)
  let os := keys.forStore (originChain otherWorld)
  let foreign := Entry.run os 0 honest
  let midK := count / 2
  let spliced := r.bases.index.extract 0 (midK * eb) ++ foreign.extract (midK * eb) (midK * eb + eb) ++
    r.bases.index.extract (midK * eb + eb) named
  check "plant-index-other-store: entries tagged for another Store under the same key: whole, open refuses `indexCorrupt`; one in the middle, open opens and `host check` refuses it at its position"
    (originChain otherWorld != originChain genesis && foreign.size = named && spliced != r.bases.index &&
      faultName (reopenIn foreign r.bases.file r.disk.synced) = "indexCorrupt" &&
      faultName (reopenIn spliced r.bases.file r.disk.synced) = "opened" &&
      indexClean sk spliced count offsets == some midK) failures
  let raw := r.bases.index.extract eb (2 * eb) ++ r.bases.index.extract 0 eb ++ r.bases.index.extract (2 * eb) named
  let retagSwap := match honest with
    | a :: b :: rest => Entry.run sk 0 (b :: a :: rest) | _ => r.bases.index
  check "plant-index-swap: entries 0 and 1 swapped are refused by `host check` at entry 0: as bytes (each tag names its own position), and re-tagged at the new positions (each names another record's offset)"
    (raw != r.bases.index && retagSwap != r.bases.index &&
      indexClean sk raw count offsets == some 0 && indexClean sk retagSwap count offsets == some 0) failures
  -- the ruled move: every entry the base counts flipped in turn (one at a time). Open still opens;
  -- `host check` refuses that entry; and EVERY page from every height is either refused
  -- `badIndex k` (it read the entry) or is byte for byte the honest page (it did not): no page is
  -- ever built from it
  let honestPage (s : Nat) := (memPage r.bases.index r.disk.synced r.resident 40 s).1
  let mut opens := true
  let mut checked := true
  let mut neverServed := true
  let mut refusedSome := 0
  for k in List.range count do
    let bad := flipByte r.bases.index (k * eb + 9)
    unless k + 1 = count do
      opens := opens && faultName (reopenIn bad r.bases.file r.disk.synced) == "opened"
    checked := checked && indexClean sk bad count offsets == some k
    for s in (List.range r.resident.world.height).filter (· % 5 = k % 5) do
      match (memPage bad r.disk.synced r.resident 40 s).1, honestPage s with
      | .error (.badIndex j), _ => neverServed := neverServed && j == k; refusedSome := refusedSome + 1
      | .ok a, .ok b => neverServed := neverServed && a.events == b.events && a.steps == b.steps && a.chain == b.chain
      | _, _ => neverServed := false
  check s!"plant-index-middle-flip: each of the {count - 1} entries before the last, flipped, still opens (HOST-33 moved the check)" opens failures
  check s!"plant-index-middle-flip: `host check`'s `indexClean` refuses each of the {count} flipped entries by position" checked failures
  check s!"plant-index-middle-flip: no page is built from a flipped entry; {refusedSome} pages read one and were refused `badIndex` at its position, every other page is the honest page"
    (neverServed && 0 < refusedSome) failures
  check "the reopened Store holds the loop's entries since the base, and counts the loop's on disk"
    (match opened with
     | .ok o => o.sealed.index.count = r.resident.sealed.index.count && o.index.size = r.resident.index.size &&
         (o.index.toList.zip r.resident.index.toList).all fun (x, y) => x.steps == y.steps && x.offset == y.offset && x.chain == y.chain
     | .error _ => false) failures

/-- The cadence HOST-14's at-size count runs under: the deployed RATIOS at toy scale. The seal
floor is small against the World, so a Store of THE BAR's 1000 records seals in the base/4 regime
the deployed Store reaches once its World passes 4 MiB (`Cadence.deployed`: sealMin 1 MiB). -/
def sizeCadence : Cadence := { cadence with sealMinBytes := 256 }

/-- HOST-14 at size, as counts (no timing): one run under `sizeCadence`. -/
structure SizeCount where
  turns : Nat
  seals : Nat
  /-- bytes seals wrote: every page and every base after genesis's -/
  sealed : Nat
  pages : Nat
  genesisBase : Nat
  finalBase : Nat
  appended : Nat
  /-- bytes the final reopen reads: the base file, the one index entry, the origin frame, the tail -/
  read : Nat
  /-- what HOST-14 + HOST-33 allow it: the base file + one index entry + the origin frame + `tailMax` -/
  bound : Nat
  named : Nat
  /-- bytes the sealers hash: each frame's prev tag + record in seg.log, every page, every base -/
  hashed : Nat

/-- `n` Turns made by `mk` (fresh txIds), served under `sizeCadence`, and counted. -/
def sizeTerm (seed n : Nat) (mk : Nat → Turn Nat) : IO SizeCount := do
  let frames : List Frame := (List.range n).map fun i =>
    submitFrame i (.turn (mk i))
  let r ← runWith sizeCadence seed frames none
  let genesisBase := r.bases.history[0]!.1.size
  let hashedOf (s : Log.Sealer) (initial log : ByteArray) : Nat :=
    ((Log.recover s (1 <<< 30) initial log).records.map (·.size + Log.tagBytes)).foldl (· + ·) 0
  -- an entry's tag hashes the Store's origin chain, its u64 position and its body
  let hashed := hashedOf keys.segment segmentInitial r.disk.synced +
    r.bases.index.size / entryBytes keys * (keys.chainBytes + 8 + entryBytes keys - Log.tagBytes) +
    (r.bases.history.toList.drop 1).foldl (fun a (f, _) => a + (f.size - 4)) 0
  let c : SizeCount := ⟨n, r.bases.history.size - 1, r.bases.written - genesisBase, r.bases.index.size,
    genesisBase, r.bases.file.size, r.disk.synced.size, 0, 1, 0, hashed⟩
  match reopenWith sizeCadence r.bases.index r.bases.file r.disk.synced with
  | .error _ => return c
  | .ok o =>
    -- the one entry open reads (HOST-33)
    let named := (lastAt keys o.sealed.index.count).2
    let head := r.bases.file.size + named + originLen o.sealed.offset
    let read := head + (o.pos.offset - o.sealed.offset)
    let bound := head + sizeCadence.tailMax o.sealed.bytes
    return ⟨c.turns, c.seals, c.sealed, c.pages, c.genesisBase, c.finalBase, c.appended, read, bound, named, c.hashed⟩

/-- A Turn that spends a fresh nullifier: the World grows by one nullifier per Turn. -/
def growTurn (i : Nat) : Turn Nat := mkTurn (1000 + i) 0 1024 [5000 + i]

/-- A Turn that touches nothing and spends nothing, in a window around its height: the World
stays the same size (its journal is pruned to the window, KERNEL-33), while the log and the index
grow with history. -/
def steadyTurn (i : Nat) : Turn Nat := mkTurn (1000 + i) (i - min i 400) (i + 400) []

/-- HOST-32's plant (`Host.Proofs.Backup.openWith_backup` on the run's own Store). For every base
k the run installed before its last: the LIVE Store at the instant just before base k+1 was
renamed in (base k, index.log with base k+1's page as an orphan, seg.log as base k+1 found it: a
non-empty tail, which crash-before-rename shows opens), and a backup that copied base k and then
the files as they stand at the end (`Store.backupOrder`). The backup opens to base k with at
least the live records and EXACTLY the frames `recover` finds past base k's offset (an
independent count), or refuses `tailTooLong`; and a copy in the WRONG order (seg.log as it stood
one base earlier, under base k) is refused `segmentShort`. -/
def backupPlants (r : RunResult) (failures : IO.Ref Nat) : IO Unit := do
  let h := r.bases.history
  let mut opened := 0
  let mut held := true
  let mut wrongOrder := true
  for k in [0:h.size - 1] do
    let (file, segAt) := h[k]!
    let liveSeg := r.disk.synced.extract 0 h[k + 1]!.2
    let live := reopenIn (r.bases.index.extract 0 r.bases.indexAt[k + 1]!) file liveSeg
    match live, reopenIn r.bases.index file r.disk.synced with
    | .ok lo, .ok bo =>
      let tagK := match Base.read keys cadence world file with
        | .ok (b, _, _) => b.tag.bytes
        | .error _ => ByteArray.empty
      let frames := (Log.recover keys.segment cadence.recordBytesMax tagK
        (r.disk.synced.extract lo.sealed.offset r.disk.synced.size)).records.length
      if 0 < lo.opened.records then opened := opened + 1
      held := held && bo.sealed.offset == lo.sealed.offset && lo.opened.records ≤ bo.opened.records &&
        bo.opened.records == frames && lo.pos.offset ≤ bo.pos.offset
    | .ok _, .error f => held := held && f.name == "tailTooLong"
    | .error _, _ => held := false
    if 0 < k then
      wrongOrder := wrongOrder &&
        faultName (reopenIn r.bases.index file (r.disk.synced.extract 0 h[k - 1]!.2)) == "segmentShort"
    let _ := segAt
  check "plant-backup fires: at least two live Stores with a non-empty tail have a backup that opens" (2 ≤ opened) failures
  check "plant-backup: every backup in backupOrder opens to its base with at least the live records and exactly the frames past it, or refuses `tailTooLong`"
    held failures
  check "plant-backup-wrong-order: seg.log copied before a later base is refused `segmentShort`, never opened short"
    wrongOrder failures

/-- HOST-14's at-size rows: THE BAR's 1000 records in a growing World, and a steady World at 1000
and 4000 records. -/
def sizeRows (seed : Nat) : IO Unit := do
  -- every count as text; the rows HOST-14/HOST-33 pin as WASTE lines
  let show_ (label : String) (c : SizeCount) (pins : List String) : IO Unit := do
    IO.println s!"size {label} at {c.turns} turns: {c.seals} seals; base {c.genesisBase} -> {c.finalBase} bytes, index.log {c.pages} (prefix {c.named}), segment {c.appended}; seals wrote {c.sealed}; the reopen read {c.read} of {c.bound}; sealers hashed {c.hashed}"
    -- HOST-14 corrected (HOST-33): a seal writes at most 4x the bytes appended since the base
    -- before it, plus that base's growth since (telescoping), plus its page
    let rows : List (String × String) :=
      [("seal base-bytes-net-of-growth-per-appended-byte", ratio (c.sealed - c.pages - (c.finalBase - c.genesisBase)) c.appended),
       ("seal bytes-per-appended-byte", ratio c.sealed c.appended),
       ("open bytes-read-per-allowed-byte", ratio c.read c.bound),
       ("open index-bytes-per-base-byte", ratio c.named c.finalBase),
       ("seal hashed-bytes-per-appended-byte", ratio c.hashed c.appended)]
    for (m, v) in rows do
      let line := s!"{m}-{label}-at-{c.turns} {v}"
      if pins.contains m then IO.println s!"WASTE {line}" else IO.println s!"count {line}"
  show_ "grow" (← sizeTerm seed 1000 growTurn)
    ["seal base-bytes-net-of-growth-per-appended-byte", "seal bytes-per-appended-byte",
     "open bytes-read-per-allowed-byte", "seal hashed-bytes-per-appended-byte"]
  show_ "steady" (← sizeTerm seed 1000 steadyTurn) []
  show_ "steady" (← sizeTerm seed 4000 steadyTurn) ["open index-bytes-per-base-byte"]
  show_ "steady" (← sizeTerm seed 8000 steadyTurn)
    ["open index-bytes-per-base-byte", "seal base-bytes-net-of-growth-per-appended-byte"]

/-- HOST-28's plants, over the toy Ctx (`Kernel.Sim.ctx`, its u64 digest codec): the carried file
of a World with a journal entry is exported and imported through the deployed pure functions
(`Carry.exportFile`, `Carry.read`, `Carry.world`); a flipped byte under the original digest is
refused `digest`; another stamp (digest recomputed) `shapeMismatch`; a head whose anchor height is
not the carried height `anchor`; two imports under two nonces are two Worlds. -/
def carryPlants (failures : IO.Ref Nat) : IO Unit := do
  let kx := Kernel.Sim.ctx
  let kdc := Kernel.Sim.dc
  let kw₀ : World Kernel.Sim.D := World.genesis kx.env (kx.env.hash "nanodregg/host-sim/origin/v1" "carry".toUTF8) (2 ^ 40)
  let kw : World Kernel.Sim.D := { kw₀ with height := 7, journal := kw₀.journal.insert (journalSpec kx.env) 42 (5, 99) }
  let cbytes (w : World Kernel.Sim.D) := (Codec.Kernel.carried kx.env kdc).bytes w.carried
  match Carry.exportFile kx.env kdc kw with
  | .error f => check s!"plant-carry: export of a World with a journal entry ({f.name})" false failures
  | .ok f =>
    let want := Carry.digestOf f
    let imported (n : UInt8) := match Carry.importWorld kx kdc "carried".toUTF8 (ByteArray.mk (Array.replicate 32 n)) want f with
      | .ok (w, _) => some w
      | .error _ => none
    match imported 1, imported 2 with
    | some a, some b =>
      check "plant-carry: export then import keeps the carried bytes and the height, under a new origin"
        (cbytes a == cbytes kw && a.height == kw.height && a.origin != kw.origin && (a.journalAt kx.env 42).isSome) failures
      check "plant-carry: two imports under two nonces are two Worlds" (a.origin != b.origin) failures
    | _, _ => check "plant-carry: the exported file imports" false failures
    let refusedAs (want' : Codec.Digest) (g : ByteArray) : String :=
      match Carry.read kx.env kdc want' g with
      | .ok _ => "read"
      | .error e => e.name
    let flipped := flipByte f (f.size - 1)
    check "plant-carry-flip: a carried byte flipped in transit, under the original digest, is refused `digest`"
      (flipped != f && refusedAs want flipped == "digest") failures
    let otherStamp := flipByte f 0
    check "plant-carry-stamp: another stamp (digest recomputed) is refused `shapeMismatch` before decoding"
      (refusedAs (Carry.digestOf otherStamp) otherStamp == "shapeMismatch") failures
    -- the head's height is the u64 after the 32-byte stamp and the 8-byte origin
    let liar := flipByte f (Carry.stampBytes + 8)
    check "plant-carry-anchor: a head whose anchor height is not the carried height is refused `anchor`"
      (refusedAs (Carry.digestOf liar) liar == "anchor") failures
    check "plant-carry: the file reads back under its digest (control)" (refusedAs want f == "read") failures

/-- HOST-31's plants: a seal refuses an `index.log` that is not the size of the base's prefix
(`indexMoved`), and a page refuses an entry its codec cannot spell (`entryUnfit`). -/
def indexPlants (seed : Nat) (frames : List Frame) (r : RunResult) (failures : IO.Ref Nat) : IO Unit := do
  backupPlants r failures
  entryPlants r failures
  for n in indexLengths do entryRows seed n failures
  sizeRows seed
  carryPlants failures
  -- plant-index-moved (HOST-31): index.log one byte longer than the prefix the base names
  match genesisStore cadence with
  | .error _ => check "plant-index-moved: genesis opens" false failures
  | .ok (gd, gb, gres) =>
    let mv ← serveFrom cadence seed frames none gd { gb with index := gb.index.push 0 } gres
    let stopped := match mv.exit with | .sealFailed f => f.name = "indexMoved" | _ => false
    check "plant-index-moved: an index.log a byte past the base's prefix stops the first seal `sealFailed indexMoved`, and no base is installed"
      (stopped && mv.bases.history.size = 1) failures
    check "plant-index-moved: the restart's open of that Store opens to genesis with the stray byte as a 1-byte orphan (the writer truncates it)"
      (match reopenIn mv.bases.index mv.bases.file mv.disk.synced with
        | .ok o => o.orphan = 1 && o.opened.torn = 0 | .error _ => false) failures
  -- plant-entry-unfit (HOST-31, HOST-33): an entry whose chain is not the Store's width
  let fitE : Entry := ⟨0, 0, ByteArray.mk (Array.replicate keys.chainBytes 0)⟩
  let wideE : Entry := ⟨0, 0, ByteArray.mk (Array.replicate (keys.chainBytes + 1) 0)⟩
  check "plant-entry-unfit: a seal handed a second entry whose chain is one byte wider than the Store's is refused `entryUnfit 1`"
    (match Base.entries keys indexStart #[fitE, wideE] with | .error (.entryUnfit 1) => true | _ => false) failures
  check "plant-entry-unfit control: the same entries at the Store's width are written, one entryBytes each"
    (match Base.entries keys indexStart #[fitE, fitE] with | .ok (p, ix) => p.size = 2 * entryBytes keys && ix.count = 2 | .error _ => false) failures
  check "plant-index-too-large: a seal past indexMax entries is refused `indexTooLarge`, before encoding"
    (match Base.entries keys ⟨indexMax, Codec.Digest.zero⟩ #[fitE] with | .error (.indexTooLarge _) => true | _ => false) failures

/-- KERNEL-33's lookup arm through the writer's `handle` (the plant-lookup-expired Ctx and call). -/
def forgottenPlants (failures : IO.Ref Nat) : IO Unit := do
  let kx := Kernel.Sim.ctx
  let kw : World Kernel.Sim.D := World.genesis kx.env (kx.env.hash "nanodregg/host-sim/origin/v1" "lookup".toUTF8) (2 ^ 40)
  let callUntil (v : Nat) : Receive.Call Kernel.Sim.D :=
    { unsigned := { world := kw.origin, member := 0, key := ByteArray.empty, notBefore := 0, validUntil := v, pins := [],
                    maxCharge := 0, body := .revoke 0 },
      signature := ByteArray.empty }
  -- plant-lookup-forgotten (KERNEL-33): the same dead call at the World heights either side of
  -- `journalForgets` (notBefore 0 + 2 * windowMax): `expired` just below, `uncertain forgotten` at it
  let lookupHigh (h : Nat) : String :=
    match handle kx { kw with height := h } ⟨0, Protocol.Op.lookup.code, kx.callBytes (callUntil 0)⟩ with
    | .reply s p =>
      if s == Protocol.Status.uncertain.code then "uncertain " ++ (String.fromUTF8? p).getD "?"
      else if s == Protocol.Status.refused.code then (String.fromUTF8? p).getD "?" else "other"
    | _ => "other"
  check "plant-lookup-forgotten: below journalForgets a dead call is still `refused expired`"
    (lookupHigh (2 * Kernel.Bounds.windowMax - 1) == "expired") failures
  check "plant-lookup-forgotten: at journalForgets it is `uncertain forgotten`, never `refused`"
    (lookupHigh (2 * Kernel.Bounds.windowMax) == "uncertain forgotten") failures

/-- A recorded refusal as the toy log carries it (KERNEL-44): authenticated and in its window by
construction; the toy machine records it through `World.step` like any step. -/
def refusedAt (i : Nat) : Refused Nat :=
  { txId := 70000 + i, member := 9, notBefore := 0, validUntil := 1024, code := 3, event := "refused".toUTF8 }

/-- The refusals day's plants (KERNEL-44, KERNEL-47; HOST-42 in decisions/host.md):
* `plant-refusal-survives-reopen`: three refusals recorded between thirty Turns, served across fuel
  restarts (every restart's reopen must agree on steps and chain), are each in the World the one
  open of the Store reaches, at their transaction ids, and the step count counts them;
* `plant-steps-differ`: a reopen whose World agrees on height and chain but not on steps is refused
  `reopenDiverged`; the same reopen judged by (height, chain), the position before this day, passes
  (the tooth: a position in heights is blind to a lost refusal step);
* `plant-lookup-recorded`: a `lookup` of a recorded transaction id answers `refused stale` (the
  recorded code's name), where the World without the record answers `absent` (the code before this
  day); past `journalForgets` it still answers `refused stale` while the record is kept, and once the
  prune at a multiple of `windowMax` drops it, `uncertain forgotten`, never `absent`. -/
def refusalPlants (seed : Nat) (failures : IO.Ref Nat) : IO Unit := do
  let frames : List Frame := (List.range 33).map fun i =>
    if i % 11 = 5 then submitFrame i (.refusal (refusedAt i)) else submitFrame i (.turn (mkTurn (1000 + i) 0 1024 [5000 + i]))
  let ids := [5, 16, 27].map (70000 + ·)
  let r ← runWith cadence seed frames none 4
  let w := r.resident.world
  check s!"refusal steps: 30 Turns and 3 recorded refusals reach height {w.height}, steps {w.steps}"
    (w.height = 30 && w.steps = 33 && r.replies.size = 33) failures
  check s!"refusal steps: each recorded refusal is answered `refused`, across {r.reopens} fuel restarts that agreed on (steps, chain)"
    (0 < r.reopens && (r.replies.toList.filter (·.status == Protocol.Status.refused.code)).length = 3 &&
      (r.replies.toList.filter (·.payload == le64 3)).length = 3 &&
      (match r.exit with | .eof => true | _ => false)) failures
  let opened := reopenIn r.bases.index r.bases.file r.disk.synced
  check "plant-refusal-survives-reopen: the one open reaches the loop's World, every recorded refusal at its txId, steps counted"
    (match opened with
     | .ok o => sameWorld o.opened.world w && o.opened.world.steps = 33 &&
         ids.all fun id => match o.opened.world.refusalAt env (.tx id) with
           | some (.refused _ 3 _) => true
           | _ => false
     | .error _ => false) failures
  -- plant-steps-differ: the same reopen, its World's step count one off
  let doctored (mark : World Nat → Nat × ByteArray) : IO Exit := do
    let fr ← IO.mkRef frames
    let sp ← IO.mkRef (splits seed frames.length)
    let sent ← IO.mkRef #[]
    let (gd, gb, gr) ← match genesisStore cadence with
      | .ok g => pure g
      | .error f => throw (IO.userError s!"genesis: {f.name}")
    let disk ← IO.mkRef gd
    let bases ← IO.mkRef gb
    let (e, _) ← restarts (serve machine recorder keys.segment (memCheckpoint disk bases keys cadence world originChain)
        cadence (memStore disk none) (fun _ _ => pure (0, ByteArray.empty)) (scriptPort fr sp sent)
        ⟨16, 1 <<< 20⟩ 3)
      (do
        let d ← disk.get
        let b ← bases.get
        match reopenWith cadence b.index b.file d.synced with
        | .error f => return .error (.reopenFailed f.name)
        | .ok o => return .ok { world := { o.opened.world with steps := o.opened.world.steps + 1 }, pos := o.pos,
                                sealed := o.sealed, index := o.index }) mark 20 gr
    return e
  let byHeight ← doctored fun v => (v.height, env.bytes v.chain)
  check "plant-steps-differ: a reopen one step off is refused `reopenDiverged` by (steps, chain)"
    (match ← doctored recorder.mark with | .reopenDiverged => true | _ => false) failures
  check "plant-steps-differ fires: judged by (height, chain) the same reopen is NOT refused"
    (match byHeight with | .reopenDiverged => false | _ => true) failures
  -- plant-lookup-recorded (Kernel.Sim's ctx: the real handler over toy parameters)
  let kx := Kernel.Sim.ctx
  let kw : World Kernel.Sim.D := World.genesis kx.env (kx.env.hash "nanodregg/host-sim/origin/v1" "refused".toUTF8) (2 ^ 40)
  let c : Receive.Call Kernel.Sim.D :=
    { unsigned := { world := kw.origin, member := 7, key := ByteArray.empty, notBefore := 0, validUntil := 100, pins := [],
                    maxCharge := 0, body := .revoke 0 },
      signature := ByteArray.empty }
  let lookupOn (v : World Kernel.Sim.D) : String :=
    match handle kx v ⟨0, Protocol.Op.lookup.code, kx.callBytes c⟩ with
    | .reply s p =>
      if s == Protocol.Status.uncertain.code then "uncertain " ++ (String.fromUTF8? p).getD "?"
      else if s == Protocol.Status.refused.code then "refused " ++ (String.fromUTF8? p).getD "?"
      else if s == Protocol.Status.absent.code then "absent" else "other"
    | _ => "other"
  let W := Kernel.Bounds.windowMax
  match World.refuse kx.env kw (Receive.refusedOf kx c (.rejected (.stale 0))) with
  | .error e => check s!"plant-lookup-recorded: the refusal records ({e.name})" false failures
  | .ok w₁ =>
    check "plant-lookup-recorded: a recorded txId answers `refused stale`" (lookupOn w₁ == "refused stale") failures
    check "plant-lookup-recorded fires: without the record (the code before KERNEL-44) it answers `absent`"
      (lookupOn kw == "absent") failures
    let w₂ := { w₁ with height := 3 * W - 1 }
    check "plant-lookup-recorded: past journalForgets, while the record is kept, still `refused stale`"
      (journalForgets w₂.height 0 && lookupOn w₂ == "refused stale") failures
    let t₀ : Turn Kernel.Sim.D := { txId := 424242, notBefore := 3 * W - 10, validUntil := 3 * W + 10, touches := [],
                                    creates := [], nullifiers := [], charge := 0, event := ByteArray.empty }
    match World.admit kx.env w₂ { t₀ with charge := t₀.weight } with
    | .error e => check s!"plant-lookup-recorded: the turn at height 3·windowMax admits ({e.name})" false failures
    | .ok w₃ =>
      check "plant-lookup-recorded: the prune at 3·windowMax drops the record, and lookup answers `uncertain forgotten`"
        ((w₃.refusalAt kx.env (.tx (Receive.txIdOf kx c))).isNone && lookupOn w₃ == "uncertain forgotten") failures

/-- A priced Turn on `w`, open from the next height (K17-SIM's recipe, Kernel/Sim/Gen's `probeRows`). -/
def rowsMk {D : Type} [Ord D] [DecidableEq D] (E : Env D) (w : World D) (tag : String) (touches : List (Touch D))
    (creates : List (D × Cell)) (rows : List (RowTouch D)) : Turn D :=
  let t0 : Turn D := ⟨E.hash "nanodregg/host-sim/rows" (tag.toUTF8 ++ E.bytes w.chain), w.height + 1,
    w.height + 64, touches, creates, [], 0, ByteArray.empty, rows, []⟩
  ⟨t0.txId, t0.notBefore, t0.validUntil, t0.touches, t0.creates, t0.nullifiers, t0.weight, t0.event, t0.rows, t0.ranges⟩

/-- The two rows Turns from `w` (KERNEL-46/48): a parent cell born with one declared relation (limit 3,
cap 10, key width 2, retractable), then one row inserted under it with the parent pinned. -/
def rowsTurns {D : Type} [Ord D] [DecidableEq D] (E : Env D) (w : World D) : Except (Reject D) (List (Turn D) × World D) := do
  let t1₀ := rowsMk E w "create" [] [] []
  let p := cellIdOf E t1₀.txId 0
  let cell : Cell := ⟨2, .ram, [(16, ByteArray.empty)]⟩
  let t1 := rowsMk E w "create" [] [(p, cell)] [⟨.head p 0, none, .declare 3 10 2 true⟩]
  let w1 ← World.admit E w t1
  let keep : Touch D := ⟨p, pinOf E (w1.live E p), .keep⟩
  let t2 := rowsMk E w1 "insert" [keep] [] [⟨.row ⟨p, 0, "a0".toUTF8⟩, none, .insert 2 "v-a0".toUTF8⟩]
  let w2 ← World.admit E w1 t2
  return ([t1, t2], w2)

/-- The rows day's plants (KERNEL-46/48, HOST-44):
* `plant-rows-survive-reopen`: a parent with a declared relation and one row, served through the toy
  loop as two Turns, is in the World the one open of the Store reaches: the same rows listing, the
  same rows root, its head counting the row;
* `plant-rows-carry`: a World holding rows exports and imports (Kernel.Sim's ctx, the real carry codec)
  with its rows in the carried bytes, the head and the row read back after the import; the control
  (the same World with its rows emptied) exports DIFFERENT carried bytes, so a carry that dropped rows
  would be caught. -/
def rowsPlants (seed : Nat) (failures : IO.Ref Nat) : IO Unit := do
  match rowsTurns env genesis with
  | .error e => check s!"plant-rows-survive-reopen: the two rows Turns admit at the toy env ({e.name})" false failures
  | .ok (ts, wk) =>
    let frames := ts.zipIdx.map fun (t, i) => submitFrame i (.turn t)
    -- a cadence that seals after every batch, so the reopen reads the rows from a SEALED BASE (the
    -- World codec), not only by replaying the records
    let eager : Cadence := { cadence with sealMinBytes := 1 }
    let r ← runWith eager seed frames none
    let w := r.resident.world
    check s!"plant-rows-survive-reopen fires: the newest base holds both rows Turns (base steps {r.resident.sealed.steps})"
      (r.resident.sealed.steps = 2) failures
    check s!"plant-rows-survive-reopen fires: the loop holds {w.rows.toList.length} rows entries (a head and a row)"
      (w.rows.toList.length = 2 && w.rows.toList == wk.rows.toList) failures
    let p := cellIdOf env (rowsMk env genesis "create" [] [] []).txId 0
    match reopenWith eager r.bases.index r.bases.file r.disk.synced with
    | .error f => check s!"plant-rows-survive-reopen: the Store opens ({f.name})" false failures
    | .ok o =>
      check "plant-rows-survive-reopen: the one open (from the base, no record replayed) reaches the same rows listing and root, the head counting its row"
        (o.opened.records = 0 && o.opened.world.rows.toList == w.rows.toList && o.opened.world.rowsRoot env == w.rowsRoot env &&
          (match headOf env o.opened.world.rows p 0 with | some (1, 2, 3, 10, 2, true) => true | _ => false) &&
          rowAt env o.opened.world.rows (.row ⟨p, 0, "a0".toUTF8⟩) == some (.row 2 "v-a0".toUTF8)) failures
  let kx := Kernel.Sim.ctx
  let kdc := Kernel.Sim.dc
  let kw₀ : World Kernel.Sim.D := World.genesis kx.env (kx.env.hash "nanodregg/host-sim/origin/v1" "rows".toUTF8) (2 ^ 40)
  match rowsTurns kx.env kw₀ with
  | .error e => check s!"plant-rows-carry: the rows Turns admit at Kernel.Sim's env ({e.name})" false failures
  | .ok (_, kw) =>
    let cbytes (v : World Kernel.Sim.D) := (Codec.Kernel.carried kx.env kdc).bytes v.carried
    check "plant-rows-carry fires: the carried bytes of the World with rows differ from the same World without them"
      (cbytes kw != cbytes (World.mk kw.trie kw.journal kw.refusals .empty kw.height kw.steps kw.chain kw.allowance kw.origin)) failures
    match Carry.exportFile kx.env kdc kw with
    | .error f => check s!"plant-rows-carry: export of a World with rows ({f.name})" false failures
    | .ok f =>
      match Carry.importWorld kx kdc "rows".toUTF8 (ByteArray.mk (Array.replicate 32 3)) (Carry.digestOf f) f with
      | .error _ => check "plant-rows-carry: the exported file imports" false failures
      | .ok (a, _) =>
        check "plant-rows-carry: export then import keeps the rows (listing and root) under a new origin"
          (a.rows.toList == kw.rows.toList && a.rowsRoot kx.env == kw.rowsRoot kx.env && cbytes a == cbytes kw &&
            a.origin != kw.origin) failures

/-- HOST-43's plants: the operator's seal (`Loop.sealNow`, the act `host seal STORE` runs over the
files) over the in-memory Store.
* `plant-seal-verb`: a Store with a tail past its newest base, sealed: the newest base is at the
  tip, and the one open of the Store replays no record and reaches the same World and position;
* `plant-seal-again`: a second seal at the sealed position writes nothing (no base, no entry);
* `plant-member-seal`: no member op seals: a frame naming no op of PROTOCOL's table (whatever a
  member sends to ask for a seal) is refused `unknownOp` by name, and stages nothing. -/
def sealPlants (seed : Nat) (frames : List Frame) (failures : IO.Ref Nat) : IO Unit := do
  let r ← runOnce seed (frames.take 37) none
  check s!"plant-seal-verb fires: the Store has a tail past its newest base ({r.resident.pos.offset - r.resident.sealed.offset} bytes)"
    (r.resident.sealed.offset < r.resident.pos.offset) failures
  let disk ← IO.mkRef r.disk
  let bases ← IO.mkRef r.bases
  let ck := memCheckpoint disk bases keys cadence world originChain
  match ← sealNow ck recorder.mark r.resident with
  | .error f => check s!"plant-seal-verb: the seal ({f.name})" false failures
  | .ok r₁ =>
    let b₁ ← bases.get
    check "plant-seal-verb: the newest base is at the tip"
      (r₁.sealed.offset = r.resident.pos.offset && r₁.sealed.steps = r.resident.world.steps) failures
    check "plant-seal-verb: the one open replays no record and reaches the same World and position"
      (match reopenIn b₁.index b₁.file (← disk.get).synced with
       | .ok o => o.opened.records = 0 && sameWorld o.opened.world r.resident.world &&
           o.opened.world.steps = r.resident.world.steps && o.pos.offset = r.resident.pos.offset
       | .error _ => false) failures
    match ← sealNow ck recorder.mark r₁ with
    | .error f => check s!"plant-seal-again: the second seal ({f.name})" false failures
    | .ok r₂ =>
      let b₂ ← bases.get
      check "plant-seal-again: a second seal at the sealed position writes nothing"
        (b₂.written = b₁.written && b₂.history.size = b₁.history.size && b₂.index.size = b₁.index.size &&
          r₂.sealed.offset = r₁.sealed.offset) failures
  -- a member cannot ask for a seal: the real handler, Kernel.Sim's ctx
  let kx := Kernel.Sim.ctx
  let kw : World Kernel.Sim.D := World.genesis kx.env (kx.env.hash "nanodregg/host-sim/origin/v1" "seal".toUTF8) (2 ^ 40)
  let free := (List.range 256).filter fun b => (Protocol.Op.ofCode? b.toUInt8).isNone && (Protocol.childKindOf? b.toUInt8).isNone
  -- the tooth: the member op table is pinned; a new op (a seal request among them) reds this until
  -- HOST re-reads it, so an op that seals cannot arrive unseen
  check "plant-member-seal fires: PROTOCOL's member op table is exactly submit, lookup, read, log, command, resume (no op seals)"
    (Protocol.Op.all.map Protocol.Op.code == [1, 2, 3, 4, 5, 6].map Nat.toUInt8) failures
  check s!"plant-member-seal fires: {free.length} op codes name no op (any of them is what a seal request would be)"
    (free.length = 249) failures
  check "plant-member-seal: every frame naming no op is refused `unknownOp` and stages nothing"
    (free.all fun b => match handle kx kw ⟨0, b.toUInt8, ByteArray.empty⟩ with
      | .reply st p => st == Protocol.Status.refused.code && p == "unknownOp".toUTF8
      | _ => false) failures

/-- plant-page-io (HOST-48): the real `serve` over the in-memory Store, with log requests deferred
(the plant machine defers every `log` frame, as `Host.handle` does after the envelope check) and a
pager whose FIRST page throws an IO error (an unreadable base.world or segment mid-service). The
loop must refuse that one page `refused pageIo`, answer every other request exactly as a run whose
pager never throws (its control), and end `eof` with the same World: the writer serves on. Before
HOST-48 the error escaped `serve` and `serving` restarted the whole writer (`ioServing`). -/
def pageIoPlant (seed : Nat) (failures : IO.Ref Nat) : IO Unit := do
  let p := "plant-page-io"
  let submits := ((scenario seed 12).map (·.1))
  let logAt (i : Nat) : Frame := ⟨UInt32.ofNat (800000 + i), Protocol.Op.log.code, ByteArray.empty⟩
  let frames := submits.take 4 ++ [logAt 0] ++ (submits.drop 4).take 4 ++ [logAt 1] ++ submits.drop 8
  let pm : Machine (World Nat) (Step Nat) Frame Nat :=
    { machine with handle := fun w f => if f.op == Protocol.Op.log.code then .defer (.log 0) else machine.handle w f }
  let go (throwFirst : Bool) : IO (Except String (Exit × Resident (World Nat) × Array Reply × Nat)) := do
    let fr ← IO.mkRef frames
    let sp ← IO.mkRef (splits seed frames.length)
    let sent ← IO.mkRef #[]
    let calls ← IO.mkRef 0
    let (gd, gb, gr) ← match genesisStore cadence with
      | .ok g => pure g
      | .error f => throw (IO.userError s!"genesis: {f.name}")
    let disk ← IO.mkRef gd
    let bases ← IO.mkRef gb
    let pager : Resident (World Nat) → Deferred → IO (UInt8 × ByteArray) := fun _ _ => do
      let n ← calls.modifyGet fun n => (n, n + 1)
      if throwFirst && n == 0 then throw (IO.userError "plant: base.world unreadable")
      return (Protocol.Status.ok.code, "page".toUTF8)
    try
      let (e, r) ← restarts (serve pm recorder keys.segment (memCheckpoint disk bases keys cadence world originChain)
          cadence (memStore disk none) pager (scriptPort fr sp sent) ⟨16, 1 <<< 20⟩ 5)
        (do
          let d ← disk.get
          let b ← bases.get
          match reopenWith cadence b.index b.file d.synced with
          | .error f => return .error (.reopenFailed f.name)
          | .ok o => return .ok { world := o.opened.world, pos := o.pos, sealed := o.sealed, index := o.index })
        recorder.mark (frames.length + 1) gr
      return .ok (e, r, ← sent.get, ← calls.get)
    catch err => return .error s!"the IO error escaped the loop ({err})"
  match ← go true, ← go false with
  | .error e, _ => check s!"{p}: the writer serves on ({e})" false failures
  | _, .error e => check s!"{p}-control: the honest run serves ({e})" false failures
  | .ok (e, r, sent, calls), .ok (ce, cr, csent, _) =>
    check s!"{p} fires: the pager was asked {calls} times and its first page threw" (2 ≤ calls) failures
    let byConn (rs : Array Reply) (c : Nat) : List (UInt8 × ByteArray) :=
      (rs.toList.filter (·.conn.toNat == c)).map fun a => (a.status, a.payload)
    check s!"{p}: the first log page is refused `pageIo`, the second is served"
      (byConn sent 800000 == [pageIoReply] && byConn sent 800001 == [(Protocol.Status.ok.code, "page".toUTF8)]) failures
    let others (rs : Array Reply) := (rs.toList.filter (·.conn.toNat != 800000)).map fun a => (a.conn, a.status, a.payload)
    check s!"{p}: the loop ends `{e.name}` with one reply per request ({sent.size} of {frames.length}), every other reply and the World as the control's"
      ((match e, ce with | .eof, .eof => true | _, _ => false) && sent.size == frames.length &&
        csent.size == frames.length && others sent == others csent && sameWorld r.world cr.world) failures

/-- plant-seal-count (HOST-50): a checkpoint whose base counts one entry more than the loop handed
it. `settle`'s pair assertion refuses it (`sealFailed io`, a restart), so `Resident.install` never
drops entries the base does not count (`Host.install_total`'s premise). Its control, the honest
checkpoint over the same frames, seals and ends `eof`. -/
def sealCountPlant (seed : Nat) (frames : List Frame) (failures : IO.Ref Nat) : IO Unit := do
  let p := "plant-seal-count"
  let go (lie : Bool) : IO (Exit × Nat) := do
    let fr ← IO.mkRef frames
    let sp ← IO.mkRef (splits seed frames.length)
    let sent ← IO.mkRef #[]
    let (gd, gb, gr) ← match genesisStore cadence with
      | .ok g => pure g
      | .error f => throw (IO.userError s!"genesis: {f.name}")
    let disk ← IO.mkRef gd
    let bases ← IO.mkRef gb
    let seals ← IO.mkRef 0
    let ck := memCheckpoint disk bases keys cadence world originChain
    let ck' : Checkpoint (World Nat) := { ck with write := fun w seg es ip => do
      seals.modify (· + 1)
      match ← ck.write w seg es ip with
      | .ok (b, d, ix) => return .ok (b, d, if lie then { ix with count := ix.count + 1 } else ix)
      | .error f => return .error f }
    let (e, _) ← serve machine recorder keys.segment ck' cadence (memStore disk none)
      (fun _ _ => pure (0, ByteArray.empty)) (scriptPort fr sp sent) ⟨16, 1 <<< 20⟩ (frames.length + 1) gr
    return (e, ← seals.get)
  let (ce, cs) ← go false
  check s!"{p}-control: the honest checkpoint seals {cs} times and the run ends `{ce.name}`"
    (0 < cs && (match ce with | .eof => true | _ => false)) failures
  let (e, _) ← go true
  check s!"{p}: a base counting one entry more than handed is refused `sealFailed io` ({e.name})"
    (match e with | .sealFailed (.io d) => d.startsWith "seal returned index count" | _ => false) failures

/-- The plants that need only the seed and the scenario: one call in `run`, whose `do` block is at
the elaborator's depth. -/
def laterPlants (seed : Nat) (frames : List Frame) (failures : IO.Ref Nat) : IO Unit := do
  forgottenPlants failures
  refusalPlants seed failures
  rowsPlants seed failures
  sealPlants seed frames failures
  pageIoPlant seed failures
  sealCountPlant seed frames failures

/-- `host-sim [SEED] [--harness-control]`; any other argument is refused (exit 2), never read as seed 1.
`--harness-control` (GATES-15) adds one check nothing meets to the ordinary run, so the run must end
`FAIL harness-control …` / `N FAILED`: the known-red control gates/runs.py runs before reading a verdict. -/
def run (args : List String) : IO UInt32 := do
  let control := args.contains "--harness-control"
  let some seed := (match args.filter (· != "--harness-control") with
      | [] => some 1
      | [s] => s.toNat?
      | _ => none)
    | IO.eprintln s!"usage: host-sim [SEED] [--harness-control] (got {args})"; return 2
  let failures ← IO.mkRef 0
  let sc := scenario seed 200
  let frames := sc.map (·.1)
  let r ← runOnce seed frames none
  let w := r.resident.world
  -- every open of this run's bases reads its `index.log` (HOST-30)
  let reopen := reopenIn r.bases.index
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
    | .ok _, .ok b =>
      -- the index as it stood after the newer seal: the older base counts fewer entries, and the
      -- newer seal's entries are ORPHANS to it (HOST-30), which the open leaves out and reports
      let olderNamed := r.bases.indexAt[k]!
      let newerPage := r.bases.indexAt[k + 1]! - olderNamed
      let a := match reopenIn (r.bases.index.extract 0 r.bases.indexAt[k + 1]!) older seg with
        | .ok o => some o | .error _ => none
      unless (a.map fun o => sameWorld o.opened.world b.opened.world && o.pos.offset = b.pos.offset &&
          o.orphan = newerPage && o.sealed.index.count * entryBytes keys = olderNamed &&
          o.sealed.index.count + o.index.size = b.sealed.index.count + b.index.size).getD false do
        renameOk := false; IO.println s!"  seal {k + 1}: the older base with the newer page as an orphan folds elsewhere"
    | a, b =>
      renameOk := false; IO.println s!"  seal {k + 1}: older {faultName a}, newer {faultName b}"
  check s!"plant-crash-before-rename at each of {seals} seals: the older base + tail = the newer base, the newer entries orphans it leaves out (HOST-30)" renameOk failures
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
      unless st = Protocol.Status.ok.code ∧ Protocol.Text.ofU64 h.1 = some r.resident.sealed.steps do
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
  let stated := records.foldl (fun acc rec => match (Record.codec dc).decode rec with
    | .ok ps => acc ++ ps | .error _ => acc) []
  -- the (step, roots) pairs recomputed by taking the logged steps from genesis: the page checks
  -- below compare against THESE, never against the roots the records state
  let turns : List (Step Nat × Nat) := ((stated.map Prod.fst).foldl
    (fun (acc : World Nat × Array (Step Nat × Nat)) t => match World.step env acc.1 t with
      | .ok w' => (w', acc.2.push (t, World.roots env w'))
      | .error _ => acc) (genesis, #[])).2.toList
  let admittedBytes := turns.foldl (fun n t => n + (match t.1 with
    | .turn t => (turnCodec.bytes t).size | .refusal _ => 0)) 0
  -- log pages (Host.Page) over the durable segment, index.log and the loop's entries since the base
  let page (budget start : Nat) := (memPage r.bases.index r.disk.synced r.resident budget start).1
  let mut start := 0
  let mut served := 0
  let mut pagesOk := true
  let mut pageCount := 0
  for _ in List.range (w.steps + 1) do
    if w.steps ≤ start then break
    match page 50 start with
    | .error f => pagesOk := false; IO.println s!"  page from {start}: {f.name}"; break
    | .ok a =>
      if a.steps ≤ start then pagesOk := false; break
      -- the stated chain is the chain of the log's first `a.steps` steps
      unless a.chain = env.bytes (chainOf env genesis.chain (turns.take a.steps)) do
        pagesOk := false; IO.println s!"  page from {start} states a wrong chain at {a.steps}"
      -- a deployed-budget page from anywhere holds the rest of the log up to one record's steps
      -- (`recordTurnsMax`, `Page.build_events_le`) and states the chain at its last step
      match page Page.budget start with
      | .ok whole =>
        unless whole.events.size = min recordTurnsMax (w.steps - start) ∧
            whole.steps = start + whole.events.size ∧
            whole.chain = env.bytes (chainOf env genesis.chain (turns.take whole.steps)) do
          pagesOk := false; IO.println s!"  deployed-budget page from {start}: {whole.events.size} events to {whole.steps}"
      | .error _ => pagesOk := false
      served := served + a.events.size; start := a.steps; pageCount := pageCount + 1
  -- a one-event page from EVERY step, mid-record ones included
  for s in List.range w.steps do
    match page 5 s with
    | .ok a =>
      unless a.steps = s + 1 ∧ a.chain = env.bytes (chainOf env genesis.chain (turns.take (s + 1))) do
        pagesOk := false; IO.println s!"  one-event page from {s}: steps {a.steps}"
    | .error f => pagesOk := false; IO.println s!"  one-event page from {s}: {f.name}"
  let lastOk := match page 50 start with
    | .ok a => a.events.size = 0 ∧ a.steps = w.steps ∧ a.chain = env.bytes w.chain
    | .error _ => false
  check s!"log pages: {pageCount} pages of 10 events serve every event once, each page states the log's chain at its last step; a deployed-budget page from each holds at most recordTurnsMax events; a one-event page from every step"
    (pagesOk && served = w.steps && lastOk) failures
  check "plant-page-flip: a flipped byte in a served frame is refused `corrupt`"
    (match (memPage r.bases.index (flipByte r.disk.synced (origin.offset + 6)) r.resident Page.budget 0).1 with
     | .error f => f.name = "corrupt" | .ok _ => false) failures
  IO.println s!"WASTE submit bytes-per-turn {ratio (r.disk.synced.size - origin.offset) admittedBytes}"
  IO.println s!"WASTE submit fsyncs-per-batch {ratio r.disk.syncs records.length}"
  let tailBytes := match opened with | .ok o => o.pos.offset - o.sealed.offset | .error _ => 0
  -- what open must read: the base record (World, offsets, tags), the one index entry it names
  -- (HOST-33), and the tail; the excess is the base's frame
  let named := match opened with | .ok o => (lastAt keys o.sealed.index.count).2 | .error _ => 0
  let needed := r.bases.file.size - 4 - Log.tagBytes + named + tailBytes
  IO.println s!"WASTE open bytes-read-per-record {ratio (r.bases.file.size + named + tailBytes) needed}"
  -- law 5 (HOST-30): a seal is handed the entries since the last base, never the loop's index
  IO.println s!"index entries handed to seals: {r.bases.handed} for the {r.resident.sealed.index.count} entries the newest base counts"
  IO.println s!"WASTE seal entries-handed-per-entry {ratio r.bases.handed r.resident.sealed.index.count}"
  let genesisBytes := r.bases.history[0]!.1.size
  IO.println s!"WASTE seal bytes-per-appended-byte {ratio (r.bases.written - genesisBytes) r.disk.synced.size}"
  -- HOST-17/HOST-30: the index bytes a seal writes at several Store lengths (one page each)
  for n in indexLengths do
    let (ib, appended, file, seals) ← indexTerm seed n
    IO.println s!"index term at {n} turns: {seals} seals; the last base is {file} bytes, the last page {ib}, after {appended} appended bytes"
    IO.println s!"WASTE seal index-bytes-per-appended-byte-at-{n} {ratio ib appended}"
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
  let (dexit, _) ← restarts (serve machine recorder keys.segment (memCheckpoint disk bases keys cadence world originChain)
      cadence (memStore disk none) (fun _ _ => pure (0, ByteArray.empty)) (scriptPort fr sp sent)
      ⟨16, 1 <<< 20⟩ 3)
    (do
      let d ← disk.get
      let b ← bases.get
      match reopenWith cadence b.index b.file (d.synced.extract 0 (d.synced.size - 1)) with
      | .error f => return .error (.reopenFailed f.name)
      | .ok o => return .ok { world := o.opened.world, pos := o.pos, sealed := o.sealed, index := o.index }) recorder.mark 10 gr
  check "plant-reopen-diverged: a reopen missing the last synced byte stops the resident `reopenDiverged`"
    (match dexit with | .reopenDiverged => true | _ => false) failures
  -- plant-world-too-large
  let tiny := { cadence with worldBytesMax := 400 }
  let t ← runWith tiny seed frames none
  check "plant-world-too-large: the loop stops `sealFailed worldTooLarge`"
    (match t.exit with | .sealFailed f => f.name = "worldTooLarge" | _ => false) failures
  -- plant-world-at-cap: a World of EXACTLY `worldBytesMax` bytes is the largest `Base.file` writes;
  -- genesis writes it and the one open reads it back (`Cadence.baseRecordMax` counts the stamp)
  let atCap := { cadence with worldBytesMax := world.size genesis }
  let capOpen : Except Fault (Opening (World Nat)) := match genesisStore atCap with
    | .ok (d, b, _) => reopenWith atCap b.index b.file d.synced
    | .error f => .error f
  check s!"plant-world-at-cap: a World of exactly worldBytesMax = {atCap.worldBytesMax} bytes is written by genesis and opens to itself ({faultName capOpen})"
    ((world.bytes genesis).size == atCap.worldBytesMax && match capOpen with
      | .ok o => world.bytes o.opened.world == world.bytes genesis && o.opened.records == 0 && o.opened.torn == 0
      | .error _ => false) failures
  indexPlants seed frames r failures
  -- plant-fsync-fail, then plant-restart-at-every-cut
  let p ← runOnce seed frames (some 3)
  let pendingSize := p.disk.pending.size
  check "plant-fsync-fail: loop stops uncertain"
    (match p.exit with | .uncertain _ => true | _ => false) failures
  let uncertainN := (p.replies.toList.filter (·.status = Protocol.Status.uncertain.code)).length
  let lastBatch := p.replies.toList.drop (p.replies.size - uncertainN)
  check "plant-fsync-fail: the batch's replies are uncertain"
    (0 < uncertainN ∧ lastBatch.all (·.status = Protocol.Status.uncertain.code) ∧ pendingSize > 0) failures
  let baseOpen := reopenIn p.bases.index p.bases.file p.disk.synced
  let baseRecords := match baseOpen with | .ok o => o.opened.records | .error _ => 0
  check "plant-fsync-fail: synced prefix opens" (match baseOpen with | .ok o => o.pos.offset = p.disk.synced.size | .error _ => false) failures
  -- every crash cut of the unsynced frame: open (truncating the torn tail, as the writer does),
  -- resend the uncertain batch and the rest, and reach the no-crash chain.
  let resend := frames.drop (p.replies.size - uncertainN)
  let mut cutsOk := true
  for cut in List.range (pendingSize + 1) do
    match reopenIn p.bases.index p.bases.file (crashImage p.disk cut) with
    | .error e =>
      cutsOk := false; IO.println s!"  cut {cut}: open refused {e.name}"
    | .ok o =>
      let expectTorn := if cut = pendingSize then 0 else cut
      let expectRecords := if cut = pendingSize then baseRecords + 1 else baseRecords
      let img := (crashImage p.disk cut).extract 0 o.pos.offset
      let q ← serveFrom cadence seed resend none { synced := img } p.bases
        { world := o.opened.world, pos := o.pos, sealed := o.sealed, index := o.index }
      let finalOk : Bool := match reopenIn q.bases.index q.bases.file q.disk.synced with
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
  check "plant-flip-byte: corrupt" (1 < full && isCorrupt (reopen g (flipByte firstSeg (origin.offset + 6))) origin.offset) failures
  check "plant-flip-header: corrupt (the frames after it are found by the forward scan)"
    (isCorrupt (reopen g (flipByte firstSeg origin.offset)) origin.offset) failures
  -- plant-flip-root (HOST-29, KERNEL-7's tooth for `Rooted`): the first record re-encoded with
  -- the roots digest stated beside its first step changed, and the segment re-sealed after the
  -- origin frame (so every tag verifies): the writer's reopen takes the step and refuses the stated
  -- pair. The digest is one (KERNEL-47: cells', journal's and refusals' roots under `rootsDigest`,
  -- `Kernel.rootsDigest_inj`), so one flip reaches every root it commits.
  let rootFlipped : Option ByteArray :=
    let rv := Log.recover keys.segment cadence.recordBytesMax segmentInitial firstSeg
    match rv.records with
    | o :: r0 :: rest => match (Record.codec dc).decode r0 with
      | .ok ((t, roots) :: ps) =>
        (Record.encode dc (((t, roots + 1) :: ps).toArray)).map fun r =>
          Log.encodeAll keys.segment segmentInitial (o :: r :: rest)
      | _ => none
    | _ => none
  match rootFlipped with
  | none => check "plant-flip-root: the first record decodes into (step, roots) pairs" false failures
  | some seg =>
    check "plant-flip-root fires: the re-sealed segment differs from the written one, same length"
      (seg.size = firstSeg.size && seg != firstSeg) failures
    check "plant-flip-root: the stated roots digest flipped is refused `rootMismatch` at record 0, step 0"
      (match reopen g seg with
       | .error (.log (.record 0 (.rootMismatch 0))) => true
       | _ => false) failures
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
  -- plant-origin-flip (HOST-25, OPS's `corrupt history`): a byte flipped inside the origin frame's
  -- RECORD (offset 5: past the length field, before the tag, so the anchor HOST-18 compares is
  -- untouched). Before HOST-25 no open read [0, origin.offset) and both opened clean.
  let newestOffset := match reopen r.bases.file r.disk.synced with | .ok o => o.sealed.offset | .error _ => 0
  check "plant-origin-flip: under the newest base (past the first record), refused `corrupt` at 0"
    (origin.offset < newestOffset && isCorrupt (reopen r.bases.file (flipByte r.disk.synced 5)) 0) failures
  check "plant-origin-flip: under the genesis base, refused `corrupt` at 0"
    (isCorrupt (reopen g (flipByte firstSeg 5)) 0) failures
  -- plant-foreign-origin (HOST-25): another World's origin frame (another origin, the SAME key)
  -- spliced over this Store's. Under the newest base it verifies and states another genesis chain:
  -- `foreignOrigin`. Under the genesis base its tag is the anchor, so HOST-18 names it first.
  let otherWorld : World Nat := World.genesis env (env.hash "nanodregg/host-sim/origin/v1" "other".toUTF8) (2 ^ 40)
  let otherFrame := Log.frame keys.segment segmentInitial (recorder.mark otherWorld).2
  let splice (seg : ByteArray) : ByteArray := otherFrame ++ seg.extract origin.offset seg.size
  check "plant-foreign-origin fires: another origin, a frame of the same size, other bytes"
    (otherWorld.origin != genesis.origin && otherFrame.size = origin.offset &&
      otherFrame != r.disk.synced.extract 0 origin.offset) failures
  check "plant-foreign-origin: under the newest base, refused `foreignOrigin`"
    (faultName (reopen r.bases.file (splice r.disk.synced)) = "foreignOrigin") failures
  check "plant-foreign-origin: under the genesis base, refused `foreignSegment` (the anchor first)"
    (faultName (reopen g (splice firstSeg)) = "foreignSegment") failures
  -- plant-old-shape (D2, HOST-20): the newest base re-sealed, byte for byte the same base, by a
  -- binary whose batch record admits one more Turn (another batch shape, so another stamp). The
  -- running binary must refuse it `shapeMismatch` by name; the binary that wrote it opens it.
  let oldKeys : Keys := { keys with shapes := Base.shapeStamp world (Codec.Kernel.batch (recordTurnsMax + 1) dc) }
  let oldBase : Option ByteArray :=
    match Base.read keys cadence world r.bases.file with
    | .ok (b, _, _) =>
      match Base.file oldKeys cadence world b.world ⟨b.offset, b.tag⟩ ⟨b.indexCount, b.indexLast⟩ with
      | .ok f => some f
      | .error _ => none
    | .error _ => none
  match oldBase with
  | none => check "plant-old-shape: the newest base re-seals under the old shapes" false failures
  | some ob =>
    check "plant-old-shape fires: another stamp, and the writing binary opens it"
      (oldKeys.shapes.bytes != keys.shapes.bytes &&
        faultName (Id.run (openWith oldKeys cadence world recorder.mark originChain foldStep ob r.disk.synced.size
          r.bases.index.size (segReader r.bases.index)
          (segReader r.disk.synced))) = "opened") failures
    check "plant-old-shape: the running binary refuses the old shape `shapeMismatch` (never decoded)"
      (faultName (reopen ob r.disk.synced) = "shapeMismatch") failures
  -- plant-lookup-expired (HOST-21): the writer's `lookup` arm (Host.handle) over the kernel-sim
  -- Ctx (CODEC's call codec and decodeCall). At genesis (height 0) an un-journaled call whose window
  -- ends at 0 can never be admitted: `refused expired`; one ending at 1 may still land: `absent`.
  let kx := Kernel.Sim.ctx
  let kw : World Kernel.Sim.D := World.genesis kx.env (kx.env.hash "nanodregg/host-sim/origin/v1" "lookup".toUTF8) (2 ^ 40)
  let callUntil (v : Nat) : Receive.Call Kernel.Sim.D :=
    { unsigned := { world := kw.origin, member := 0, key := ByteArray.empty, notBefore := 0, validUntil := v, pins := [],
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
  laterPlants seed frames failures
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
  if control then check "harness-control: GATES-15's known-red control, an expectation nothing meets (this run must read RED)" false failures
  let n ← failures.get
  IO.println (if n = 0 then "ALL PASS" else s!"{n} FAILED")
  return (if n = 0 then 0 else 1)

end Nanodregg.Host.Sim
