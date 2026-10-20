/-
# Host.Sim.File — the loop over a real Store directory (Host.Store, Host/c/file.c, real KMAC keys)

`run [seed]`, in a fresh temporary directory it removes afterwards:
1. `genesis` creates the Store (key, empty segment, genesis base); a second genesis is refused
   `exists`; `openWriter` opens it to genesis, and the seeded scenario is served through
   `fileStore` (real `write` + `F_FULLFSYNC`/`fdatasync`) with the deployed asynchronous seal
   (`fileCheckpoint`: base.tmp → sync → rename → sync dir) at the toy cadence;
2. plant-second-writer: while the first writer lives, a second `openWriter` is refused `locked`;
3. plant-crash-mid-seal: a stale `base.tmp` (a truncated base) and half of one more frame are left
   behind the writer's back (a crash during a seal, mid-write); `openFollower` reports the torn
   tail and changes nothing; `openWriter` truncates it, ignores the tmp, and opens to the loop's
   height and chain; serving more turns seals over the tmp, and a reopen is clean;
4. plant-foreign-key: the Store opened under another Store's key is refused `baseCorrupt`;
   plant-foreign-frame: a frame of the tail re-tagged under another key (the same record, the
   same length) is refused `corrupt` by the forward scan.
5. plant-missing-FILE, per Store file (HOST-35): removed from a fresh Store, the open refuses
   `missing FILE` by name and the writer never re-creates it.
6. plant-backup-restart (HOST-32, `restartPlants`): a backup whose writer restarts (cutting a torn
   tail of seg.log and an orphan of index.log) between the base copy and the later copies, right
   after the copy or after sealing a newer base, opens to the copied base with at least the live
   records; its control, seg.log cut below the live valid end, does not.
7. plant-record-over-bound / plant-frame-over-bound (HOST-47, `boundPlants`): a record one byte over
   the derived `recordBytesMax` is refused `recordTooLarge` by the writer's append and `corrupt` by the
   open; at exactly the bound, appended / past the length gate.
8. plant-empty-record (HOST-49, `emptyPlants`): a verifying frame of a record of no steps is refused
   `emptyRecord` by both opens; the append of an empty batch writes nothing.
Prints `FAIL <check>` per failure and `ALL PASS` when none.
-/
import Host.Store
import Host.Keys
import Host.Sim.Run
import Host.Cli
import Host.Sim.Files

namespace Nanodregg.Host.Sim.File

open Nanodregg.Kernel Nanodregg.Host.Sim Nanodregg.Codec

abbrev Fault := StoreFault (Record.Fault (Reject Nat))

/-- The deployed KMAC sealers under `key`, with the toy World's chain width in an index entry (the
toy digest is a u64, `keys.chainBytes`). -/
def fileKeys (key : Digest) : Keys := { Keys.ofKey key shapes with chainBytes := keys.chainBytes }

def newKey : IO Digest := do
  match Digest.ofBytes? (← IO.getRandomBytes 32) with
  | some k => pure k
  | none => throw (IO.userError "getRandomBytes: not 32 bytes")

/-- Serve `frames` as the writer of `dir`; return what the loop holds and whether a second writer
was refused. The writer (and its lock) is released when this returns. -/
def serveDir (dir : System.FilePath) (keys : Keys) (c : Cadence) (seed : Nat) (frames : List Frame)
    (roundFuel : Nat := 5) (viaChannel : Bool := false) (retain : Retain := none) :
    IO (Except String (Resident (World Nat) × Bool)) := do
  match ← (openWriter dir keys c world recorder.mark originChain foldStep retain : IO (Except Fault _)) with
  | .error e => return .error s!"open: {e.name}"
  | .ok wr =>
    let fr ← IO.mkRef frames
    let sp ← IO.mkRef (splits seed frames.length)
    let sent ← IO.mkRef #[]
    let o := wr.opening
    -- `viaChannel`: the frames go through the DEPLOYED port (`channelPort`: a closeable channel
    -- and the one-frame `unread` slot), all queued, with batches cut by bytes so frames are put
    -- back at round ends
    let (port, limits) ← if viaChannel then do
        let ch ← Std.CloseableChannel.Sync.new
        for f in frames do discard <| (ch.send f).toBaseIO
        discard <| (ch.close).toBaseIO
        let p := channelPort ch (← IO.mkRef none) fun r => sent.modify (·.push r)
        pure (p, (⟨16, 3 * (frames.head?.map (·.payload.size)).getD 1⟩ : Limits))
      else pure (scriptPort fr sp sent, (⟨16, 1 <<< 20⟩ : Limits))
    -- rounds of `roundFuel` batches, each ending in the real in-process reopen of the files (D4)
    let (exit, r) ← restarts (serve machine recorder keys.segment (fileCheckpoint dir keys c world recorder.mark originChain wr) c
        (fileStore wr) (fun _ _ => pure (0, ByteArray.empty)) port limits roundFuel)
      (reopenAt dir keys c world recorder.mark originChain foldStep) recorder.mark (frames.length + 1) o.resident
    let second ← (openWriter dir keys c world recorder.mark originChain foldStep : IO (Except Fault _))
    let refused := match second with | .error .locked => true | _ => false
    wr.hold  -- the writer's lock is alive up to here
    let replies := (← sent.get).size
    match exit with
    | .eof =>
      if replies ≠ frames.length then
        return .error s!"{frames.length} requests, {replies} replies"
      return .ok (r, refused)
    | e => return .error s!"serve ended {e.name}"

def follow (dir : System.FilePath) (keys : Keys) (c : Cadence) : IO (Except Fault (Opening (World Nat))) :=
  openFollower dir keys c world recorder.mark originChain foldStep

def fileSize (p : System.FilePath) : IO Nat := do
  return (← (← File.open p .read).size).toNat

/-- plant-missing-FILE (HOST-35): a fresh genesis Store (index count 0, where an absent index.log
was never short of anything) with one file removed. The removal is asserted first; then
`readKey` (for the key) or `openFollower`, and `openWriter`, refuse `missing FILE` by name, and the
file is still absent afterwards (the append mode never re-creates it). -/
def missingPlants (root : System.FilePath) (key : Digest) (keys : Keys) (failures : IO.Ref Nat) : IO Unit := do
  -- the parts of a genesis Store: the key, the origin frame's seg.0.log, the base's empty file, the
  -- empty index.0.log and the base
  let probe := root / "missing-probe"
  let _ ← (Host.genesis probe key keys cadence world recorder.mark Sim.genesis : IO (Except Fault Unit))
  let segs := (← segFiles probe).toList.map (StorePart.segment ·.1)
  check s!"plant-missing fires: genesis writes two segment files ({segs.length})" (segs.length == 2) failures
  for f in ([StorePart.key] ++ segs ++ [StorePart.index 0, StorePart.base] : List StorePart) do
    let dir := root / s!"missing-{f.name}"
    let made ← (Host.genesis dir key keys cadence world recorder.mark Sim.genesis : IO (Except Fault Unit))
    check s!"plant-missing-{f.name}: genesis made the Store" (match made with | .ok () => true | .error _ => false) failures
    IO.FS.removeFile (f.path dir)
    check s!"plant-missing-{f.name} fires: the file is absent before the open" (!(← (f.path dir).pathExists)) failures
    let isMissing {α : Type} : Except Fault α → Bool
      | .error (.missing g) => g == f
      | _ => false
    if f == .key then
      let k ← (readKey dir : IO (Except Fault Digest))
      check s!"plant-missing-{f.name}: readKey refuses `missing {f.name}`" (isMissing k) failures
    else
      let o ← follow dir keys cadence
      check s!"plant-missing-{f.name}: the follower open refuses `missing {f.name}`" (isMissing o) failures
    let w ← (openWriter dir keys cadence world recorder.mark originChain foldStep : IO (Except Fault _))
    check s!"plant-missing-{f.name}: openWriter refuses `missing {f.name}` and never re-creates it"
      (isMissing w && !(← (f.path dir).pathExists)) failures
  -- the append mode itself never creates (no O_CREAT): the race past `missingOf` cannot re-create
  -- a Store file either; this plant reaches the open directly, with no check in front of it
  let p := root / "append-absent"
  check "plant-append-never-creates fires: its directory exists, the file does not"
    ((← root.isDir) && !(← p.pathExists)) failures
  let opened ← try (do let _ ← File.open p .append; pure true) catch _ => pure false
  check "plant-append-never-creates: append-opening an absent file fails and creates nothing"
    (!opened && !(← p.pathExists)) failures
  -- a sync of a file unlinked under its handle fails (its bytes are in a nameless inode): the
  -- control syncs the same handle while linked
  let q := root / "unlinked"
  writeNew q (ByteArray.mk #[1])
  let h ← File.open q .append
  let linked ← try (do h.writeAll (ByteArray.mk #[2]); h.sync; pure true) catch _ => pure false
  IO.FS.removeFile q
  let unlinked ← try (do h.writeAll (ByteArray.mk #[3]); h.sync; pure true) catch _ => pure false
  check "plant-sync-unlinked control: the handle syncs while its file is named" linked failures
  check "plant-sync-unlinked: the same handle's sync fails once its file is unlinked" (!unlinked) failures
  -- a seal over a Store whose base.world was removed under the writer refuses, and does not
  -- re-create it by its rename
  let d := root / "seal-no-base"
  let _ ← (Host.genesis d key keys cadence world recorder.mark Sim.genesis : IO (Except Fault Unit))
  match ← (openWriter d keys cadence world recorder.mark originChain foldStep : IO (Except Fault _)) with
  | .error e => check s!"plant-seal-missing-base: the writer opens ({e.name})" false failures
  | .ok wr =>
    IO.FS.removeFile (basePath d)
    let o := wr.opening
    let r ← (fileCheckpoint d keys cadence world recorder.mark originChain wr).write
      o.opened.world o.pos #[] o.sealed.index
    check "plant-seal-missing-base: the seal refuses `io` and base.world stays absent"
      ((match r with | .error (.io _) => true | _ => false) && !(← (basePath d).pathExists)) failures

/-- plant-backup-restart (HOST-32, `openWith_backup_restart`): a live backup whose writer RESTARTS
between the copy of `base.world` and the copies of `index.log` and `seg.log`. The Store serves and
seals; a follower open is the live Store at the copy instant (every byte it read was synced by the
writer); base.world is copied. With `sealFirst` the writer then serves until it seals a NEWER base
(asserted). Then half a frame is appended to seg.log (a torn tail) and half an entry to index.log
(an orphan), both asserted (each file grew); `openWriter` restarts, in its own scope so its handle
and lock are released before the next writer opens (asserted: a fresh handle takes the lock), and
cuts both back (asserted: seg.log to its open's valid end, index.log to its base's
`count · entryBytes`); the writer serves on and seals again. The later copies are the cuts plus
appends and NOT the torn files plus appends (asserted: `openWith_backup` alone does not cover
them). The backup must open to the copied base with at least the live records. The control copies
seg.log as it stood at the copy with its last whole frame cut off (below the live valid end): it
must NOT open to at least the live records, so the plant tells the two apart. -/
def restartPlant (root : System.FilePath) (key : Digest) (keys : Keys) (seed : Nat) (frames : List Frame)
    (sealFirst : Bool) (failures : IO.Ref Nat) : IO Unit := do
  let p := if sealFirst then "plant-backup-restart-newer-base" else "plant-backup-restart"
  let dir := root / "live"
  let _ ← (Host.genesis dir key keys cadence world recorder.mark Sim.genesis : IO (Except Fault Unit))
  match ← serveDir dir keys cadence seed (frames.take 120) with
  | .error e => check s!"{p}: the writer serves ({e})" false failures
  | .ok _ =>
  -- a few frames more, so the live tail after the newest base holds records
  match ← serveDir dir keys cadence seed ((frames.drop 120).take 3) with
  | .error e => check s!"{p}: the writer serves a tail ({e})" false failures
  | .ok _ =>
  match ← follow dir keys cadence with
  | .error e => check s!"{p}: the live Store opens at the copy ({e.name})" false failures
  | .ok live =>
  check s!"{p} fires: the live Store sealed (its base is off genesis) and its tail holds records"
    (0 < live.sealed.offset && 0 < live.opened.records) failures
  let baseCopy ← IO.FS.readBinFile (basePath dir)
  let segAtCopy ← logical dir (headerBytes keys)
  let rest := if sealFirst then frames.drop 163 else frames.drop 123
  if sealFirst then
    match ← serveDir dir keys cadence seed ((frames.drop 123).take 40) with
    | .error e => check s!"{p}: the writer serves to a newer base ({e})" false failures
    | .ok (r1, _) =>
      check s!"{p} fires: the writer sealed a newer base after the copy, before the restart"
        (live.sealed.offset < r1.sealed.offset) failures
  match ← follow dir keys cadence with
  | .error e => check s!"{p}: the Store opens before the tear ({e.name})" false failures
  | .ok cur =>
  let segBefore ← logicalSize dir (headerBytes keys)
  let idxBefore ← fileSize (← indexFile dir)
  let extra := Log.frame keys.segment cur.pos.tag.bytes
    ((Record.codec dc).bytes [(.turn (mkTurn 77777 0 1024 [77777]), 0)])
  let half := extra.extract 0 (extra.size / 2)
  let orphan := ByteArray.mk (Array.replicate (entryBytes keys / 2) 0xAB)
  let f ← File.open (← newestSeg dir) .append
  f.writeAll half
  f.sync
  let g ← File.open (← indexFile dir) .append
  g.writeAll orphan
  g.sync
  let segTorn ← logicalSize dir (headerBytes keys)
  let idxTorn ← fileSize (← indexFile dir)
  check s!"{p} fires: half a frame appended to seg.log and half an entry to index.log, both grew"
    (segBefore = cur.pos.offset && segBefore < segTorn &&
      idxBefore = cur.sealed.index.count * entryBytes keys && idxBefore < idxTorn) failures
  let tornSeg ← logical dir (headerBytes keys)
  let tornIdx ← IO.FS.readBinFile (← indexFile dir)
  -- the restart, scoped: only a Bool leaves it, so the Writer (its handles and lock) is freed here
  let opened ← do
    let w ← (openWriter dir keys cadence world recorder.mark originChain foldStep : IO (Except Fault _))
    pure (match w with | .ok _ => true | .error _ => false)
  let released ← do
    let h ← File.open (keyPath dir) .read
    h.tryLock
  let segCut ← logicalSize dir (headerBytes keys)
  let idxCut ← fileSize (← indexFile dir)
  check s!"{p}: the restart opens, cuts seg.log to its valid end and index.log to count · entryBytes, and releases its lock"
    (opened && released && segCut = cur.pos.offset && idxCut = cur.sealed.index.count * entryBytes keys)
    failures
  let segCutBytes ← logical dir (headerBytes keys)
  let idxCutBytes ← IO.FS.readBinFile (← indexFile dir)
  match ← serveDir dir keys cadence seed rest with
  | .error e => check s!"{p}: the restarted writer serves on ({e})" false failures
  | .ok (r2, _) =>
  check s!"{p} fires: the restarted writer sealed again (its base moved past the copied one)"
    (cur.sealed.offset < r2.sealed.offset) failures
  let idx ← IO.FS.readBinFile (← indexFile dir)
  let seg ← logical dir (headerBytes keys)
  check s!"{p} fires: the later seg.log and index.log are the cuts plus appends, NOT the torn files plus appends"
    (seg.extract 0 segCutBytes.size == segCutBytes && seg.extract 0 tornSeg.size != tornSeg &&
      idx.extract 0 idxCutBytes.size == idxCutBytes && idx.extract 0 tornIdx.size != tornIdx) failures
  let keyBytes ← IO.FS.readBinFile (keyPath dir)
  let idxName := ((← indexFile dir).fileName).getD ""
  let writeBackup (d : System.FilePath) (s : ByteArray) : IO Unit := do
    IO.FS.createDirAll d
    IO.FS.writeBinFile (keyPath d) keyBytes
    IO.FS.writeBinFile (basePath d) baseCopy
    IO.FS.writeBinFile (d / idxName) idx
    copySegs dir d
    writeLogical d (headerBytes keys) s
  let atLeast : Except Fault (Opening (World Nat)) → Bool
    | .ok o => o.sealed.offset == live.sealed.offset && live.opened.records ≤ o.opened.records
    | .error _ => false
  let outcome : Except Fault (Opening (World Nat)) → String
    | .ok o => s!"opened at base {o.sealed.offset} with {o.opened.records} records, live {live.opened.records} at base {live.sealed.offset}"
    | .error e => s!"refused {e.name}"
  writeBackup (root / "backup") seg
  let b ← follow (root / "backup") keys cadence
  check s!"{p}: the backup opens to the copied base with at least the live records ({outcome b})"
    (atLeast b) failures
  -- the control: seg.log as it stood at the copy, its last whole frame cut off
  let rv := Log.recover keys.segment cadence.recordBytesMax segmentInitial segAtCopy
  let lastLen := (rv.records.getLast?.map frameSize).getD 0
  let short := segAtCopy.extract 0 (segAtCopy.size - lastLen)
  check s!"{p} control fires: seg.log cut by its last whole frame, below the live valid end"
    (segAtCopy.size == live.pos.offset && rv.validLen == segAtCopy.size && 0 < lastLen &&
      short.size < live.pos.offset) failures
  writeBackup (root / "short") short
  let s ← follow (root / "short") keys cadence
  check s!"{p} control: the short copy does NOT open to at least the live records ({outcome s})"
    (!atLeast s) failures

/-- Both restart orders: a restart right after the base copy, and one after the writer sealed a
newer base. -/
def restartPlants (root : System.FilePath) (key : Digest) (keys : Keys) (seed : Nat) (frames : List Frame)
    (failures : IO.Ref Nat) : IO Unit := do
  restartPlant (root / "after-copy") key keys seed frames false failures
  restartPlant (root / "after-newer-base") key keys seed frames true failures

/-- The wide plants' cadence: the deployed record bound (so the byte bound does not mask the Turn
bound) and no seal in the scenario (the writer's whole log is its tail). -/
def wide : Cadence := { cadence with sealMinBytes := 1 <<< 20, recordBytesMax := Cadence.deployed.recordBytesMax }

/-- A `log` page from `start` over a Store's files, as `Host.Deployed.pager` builds it: the
deployed `Page.build` and `Page.budget`, the index read through `Page.entryAt`. -/
def filePage (keys : Keys) (seg idx : ByteArray) (o : Opening (World Nat)) (start : Nat) :
    Except Page.Fault Page.Acc :=
  Id.run (Page.build env dc digestOf keys.segment wide.recordBytesMax Page.budget
    (fun off len => pure (seg.extract off (off + len)))
    (Page.entryAt (keys.forStore (originChain o.opened.world)) (fun off len => pure (idx.extract off (off + len)))
      o.sealed.index.count o.index)
    (o.sealed.index.count + o.index.size) o.pos.offset (recorder.mark o.opened.world) start)

/-- The follower's append (`Host.Follow.loop`'s `.steps ts` arm): the pairs it absorbed from one
page, taken by its own World (`runRooted`: each step taken, its stated roots digest checked), then
appended as ONE record through `Host.append` with the deployed recorder's call. -/
def followAppend (fdir : System.FilePath) (keys : Keys) (fwr : Writer (World Nat)) (r : Resident (World Nat))
    (ps : List (Step Nat × Nat)) : IO (Except String (Resident (World Nat))) := do
  match Record.runRooted (World.step env) (World.roots env) 0 r.world ps with
  | .error f => return .error s!"the follower refuses the page ({f.name})"
  | .ok w' =>
    match ← append recorder keys.segment (fileCheckpoint fdir keys wide world recorder.mark originChain fwr) wide
        (fileStore fwr) r w' ps.toArray with
    | .error e => return .error e.name
    | .ok r => return .ok r

/-- plant-follow-wide-page: a writer log of more steps than one record may hold
(`recordTurnsMax`), caught up by a fresh follower from step 0 page by page through the deployed
`Page.build`, each page's steps appended as one record (`followAppend`), then the follower Store
reopened through the one open. Every page holds at most `recordTurnsMax` events, and the reopen
reaches the writer's World. plant-follow-wide-page-refused: the whole log's pairs handed to the
follower's append as ONE page (a writer that ignores the bound) are refused `recordTooLarge` by
name, nothing is written, and the follower Store still opens. -/
def wideFollowPlant (root : System.FilePath) (key : Digest) (keys : Keys) (failures : IO.Ref Nat) : IO Unit := do
  let p := "plant-follow-wide-page"
  let n := 100
  let frames : List Frame := (List.range n).map fun i =>
    submitFrame i (.turn (mkTurn (1000 + i) 0 1024 [5000 + i]))
  let wdir := root / "writer"
  let _ ← (Host.genesis wdir key keys wide world recorder.mark Sim.genesis : IO (Except Fault Unit))
  match ← serveDir wdir keys wide 1 frames with
  | .error e => check s!"{p}: the writer serves {n} Turns ({e})" false failures
  | .ok (wr, _) =>
  check s!"{p} fires: the writer log holds {wr.world.steps} Turns, more than one record may ({recordTurnsMax})"
    (recordTurnsMax < wr.world.steps) failures
  match ← follow wdir keys wide with
  | .error e => check s!"{p}: the writer Store opens ({e.name})" false failures
  | .ok o =>
  let seg ← logical wdir (headerBytes keys)
  let idx ← IO.FS.readBinFile (← indexFile wdir)
  -- the writer records pairs in log order (its origin frame first, not a batch)
  let rv := Log.recover keys.segment wide.recordBytesMax segmentInitial seg
  let pairs := (rv.records.drop 1).foldl (fun acc r =>
    match (Record.codec dc).decode r with
    | .ok ps => acc ++ ps
    | .error _ => acc) []
  check s!"{p} fires: the writer records decode to its {wr.world.steps} Turns"
    (pairs.length = wr.world.steps) failures
  -- the honest catch-up
  let fdir := root / "follower"
  let _ ← (Host.genesis fdir key keys wide world recorder.mark Sim.genesis : IO (Except Fault Unit))
  let caught ← do
    match ← (openWriter fdir keys wide world recorder.mark originChain foldStep : IO (Except Fault _)) with
    | .error e => pure (Except.error s!"open {e.name}")
    | .ok fwr =>
      let mut r := fwr.opening.resident
      let mut sizes : Array Nat := #[]
      let mut err : Option String := none
      for _ in [0:n + 1] do
        if wr.world.steps ≤ r.world.steps then break
        match filePage keys seg idx o r.world.steps with
        | .error f => err := some s!"page {f.name}"; break
        | .ok a =>
          sizes := sizes.push a.events.size
          let ps := (pairs.drop r.world.steps).take a.events.size
          match ← followAppend fdir keys fwr r ps with
          | .error e => err := some e; break
          | .ok r' => r := r'
      fwr.hold
      pure (match err with | some e => .error e | none => .ok (r, sizes))
  match caught with
  | .error e =>
    check s!"{p}: the follower catches up page by page ({e})" false failures
  | .ok (r, sizes) =>
    let most := sizes.foldl max 0
    check s!"{p}: every page holds at most recordTurnsMax = {recordTurnsMax} events (pages {sizes.toList})"
      (most ≤ recordTurnsMax) failures
    check s!"{p}: the follower reached the writer World in {sizes.size} pages" (sameWorld r.world wr.world) failures
    let re ← follow fdir keys wide
    check s!"{p}: the follower Store reopens through the open to the writer World ({match re with | .ok _ => "opened" | .error e => e.name})"
      (match re with | .ok o => sameWorld o.opened.world wr.world | .error _ => false) failures
  -- a writer that ignores the bound: the whole log as ONE page
  let q := "plant-follow-wide-page-refused"
  let gdir := root / "greedy"
  let _ ← (Host.genesis gdir key keys wide world recorder.mark Sim.genesis : IO (Except Fault Unit))
  check s!"{q} fires: the one page holds {pairs.length} pairs, more than recordTurnsMax" (recordTurnsMax < pairs.length) failures
  let before ← logicalSize gdir (headerBytes keys)
  let res ← do
    match ← (openWriter gdir keys wide world recorder.mark originChain foldStep : IO (Except Fault _)) with
    | .error e => pure (Except.error s!"open {e.name}")
    | .ok fwr =>
      let x ← followAppend gdir keys fwr fwr.opening.resident pairs
      fwr.hold
      pure x
  let after ← logicalSize gdir (headerBytes keys)
  check s!"{q}: the follower append refuses `recordTooLarge` and writes nothing ({match res with | .ok _ => "appended" | .error e => e}, seg.log {before} -> {after})"
    ((match res with | .error e => e = "recordTooLarge" | .ok _ => false) && before = after) failures
  let re ← follow gdir keys wide
  check s!"{q}: the follower Store still opens ({match re with | .ok _ => "opened" | .error e => e.name})"
    (match re with | .ok _ => true | .error _ => false) failures

/-- plant-record-over-bound / plant-frame-over-bound (HOST-47): the deployed `recordBytesMax` is
DERIVED (`recordBytesDerived`, the largest record of steps `World.step` took,
`Host.Deployed.recorder_encode_size_le`), half the 32 MiB it replaced, and it bites on both sides at
exactly that number. Writer: one never-judged refusal whose call makes the record `bound + 1` bytes is
refused `recordTooLarge` by the real `append` and seg.log is unchanged; its control, `bound` bytes, is
appended (one frame). Reader: a frame that VERIFIES under the Store key, holding `bound + 1` bytes, is
refused `corrupt` by the writer's open (past the length gate it is more than one frame's worth, so it
is never a torn tail) and seg.log is unchanged; its control, `bound` bytes, passes the length gate and is
refused `record` (undecodable). Both read red at the old 32 MiB bound. -/
def boundPlants (root : System.FilePath) (key : Digest) (keys : Keys) (failures : IO.Ref Nat) : IO Unit := do
  -- the DERIVED number (from Kernel's and CODEC's bounds), not the cadence's field: the plant reads
  -- red if the deployed cadence stops being it
  let bound := recordBytesDerived
  -- a record of `n` bytes: count, choice byte, five u64 fields, the call's length, the call, the
  -- (empty) cancel signature's length (KERNEL-60), the roots
  let pair (n : Nat) : Step Nat × Nat :=
    (.refusal ⟨1, 2, 0, 1, 0, ByteArray.mk (Array.replicate (n - 61) 0), ByteArray.empty⟩, 0)
  let p := "plant-record-over-bound"
  for (tag, n) in [("", bound + 1), ("-control", bound)] do
    let dir := root / s!"writer{tag}"
    let _ ← (Host.genesis dir key keys wide world recorder.mark Sim.genesis : IO (Except Fault Unit))
    let staged := #[pair n]
    let size := (Record.encode dc staged).map (·.size)
    check s!"{p}{tag} fires: the record is {size} bytes, want {n} (the derived bound is {bound}, the deployed cadence's {wide.recordBytesMax})" (size == some n) failures
    let before ← logicalSize dir (headerBytes keys)
    let res ← do
      match ← (openWriter dir keys wide world recorder.mark originChain foldStep : IO (Except Fault _)) with
      | .error e => pure (Except.error s!"open {e.name}")
      | .ok fwr =>
        let r := fwr.opening.resident
        let x ← append recorder keys.segment (fileCheckpoint dir keys wide world recorder.mark originChain fwr)
          wide (fileStore fwr) r r.world staged
        fwr.hold
        pure (match x with | .error e => Except.error e.name | .ok _ => Except.ok ())
    let after ← logicalSize dir (headerBytes keys)
    let shown := match res with | .ok () => "appended" | .error e => e
    if tag == "" then
      check s!"{p}: the append refuses `recordTooLarge` and writes nothing ({shown}, seg.log {before} -> {after})"
        ((match res with | .error e => e == "recordTooLarge" | .ok () => false) && before == after) failures
    else
      check s!"{p}-control: a record of exactly the bound is appended as one frame ({shown}, seg.log {before} -> {after})"
        ((match res with | .ok () => true | .error _ => false) && after == before + Log.frameMax n) failures
  let q := "plant-frame-over-bound"
  for (tag, n, want) in [("", bound + 1, "corrupt"), ("-control", bound, "record")] do
    let dir := root / s!"reader{tag}"
    let _ ← (Host.genesis dir key keys wide world recorder.mark Sim.genesis : IO (Except Fault Unit))
    let seg ← logical dir (headerBytes keys)
    -- every frame ends with its tag: the tag the next frame chains from is the segment's last 32 bytes
    let prev := seg.extract (seg.size - Log.tagBytes) seg.size
    let fr := Log.frame keys.segment prev (ByteArray.mk (Array.replicate n 255))
    let f ← File.open (← newestSeg dir) .append
    f.writeAll fr
    f.sync
    let before ← logicalSize dir (headerBytes keys)
    check s!"{q}{tag} fires: the appended frame is {fr.size} bytes over a {n}-byte record" (before == seg.size + Log.frameMax n) failures
    let opened ← (openWriter dir keys wide world recorder.mark originChain foldStep : IO (Except Fault _))
    let after ← logicalSize dir (headerBytes keys)
    let name := match opened with | .ok _ => "opened" | .error e => e.name
    check s!"{q}{tag}: a verifying frame of a {n}-byte record is refused `{want}` and the file is unchanged ({name}, seg.log {before} -> {after})"
      (name == want && before == after) failures

/-- plant-import-budget (HOST-56, KERNEL-55): the deployed `host import` decision (`Cli.importWith`,
the function `importVerb` runs at `IO`) over carried files of real deployed genesis Worlds, exported
by the deployed `Carry.exportFile`; the first effect it reaches is recorded. A World carrying 2^40
is refused `allowancePastBound`; a World carrying exactly `allowanceMax` whose founders weigh past
`genesisWeightMax` PASSES the allowance arm and is refused `potentialPastBound` (the arm an
allowance check alone misses). CONTROLS through the same path: one founder at `allowanceMax`, and
founders just under `genesisWeightMax`, reach `genesis`. -/
def budgetPlants (failures : IO.Ref Nat) : IO Unit := do
  let p := "plant-import-budget"
  let X := Nanodregg.Host.Deployed.X
  let keyOf (i : Nat) : ByteArray := Stream.nat64.bytes i ++ ByteArray.mk (Array.replicate 24 7)
  let fs (n : Nat) := (List.range n).map fun i => (keyOf i, Receive.nextKeyDigest X (keyOf (i + 1)))
  let nonce := ByteArray.mk (Array.replicate 32 1)
  let worldOf (allowance n : Nat) : Option (World Nanodregg.Host.Deployed.D) :=
    match Receive.genesis X "budget".toUTF8 nonce allowance (fs n) with
    | .ok w => some w
    | .error _ => none
  let importOf (w : World Nanodregg.Host.Deployed.D) : IO String := do
    match Carry.exportFile X.env Codec.Deployed.digestCodec w with
    | .error f => pure s!"export {f.name}"
    | .ok bytes =>
      let first ← IO.mkRef "none"
      let mark (e : String) : IO Unit := do if (← first.get) == "none" then first.set e
      let _ ← Cli.importWith (m := IO) (name := "imported") (digestHex := (Carry.digestOf bytes).toHex)
        { nonce := pure (.ok nonce), readIn := pure (.ok bytes), key := pure (some Digest.zero),
          genesis := fun _ _ => do mark "genesis"; pure (.error .locked),
          reopen := fun _ => do mark "reopen"; pure (.error .locked),
          refuse := fun s _ => do mark s!"refused {s.name}"; pure 1,
          report := fun _ => pure () }
      first.get
  let w1 := (worldOf allowanceMax 1).map (·.weight) |>.getD 0
  let w2 := (worldOf allowanceMax 2).map (·.weight) |>.getD 0
  let per := w2 - w1
  let over := (genesisWeightMax - w1) / max per 1 + 2
  let under := (genesisWeightMax - w1) / max per 1 - 1
  let shown (o : Option (World Nanodregg.Host.Deployed.D)) : IO String := match o with
    | some w => do pure s!"{← importOf w} (weight {w.weight}, allowance {w.allowance})"
    | none => pure "genesis refused"
  let big := worldOf (2 ^ 40) 1
  let heavy := worldOf allowanceMax over
  let ctl := worldOf allowanceMax 1
  let light := worldOf allowanceMax under
  let sBig ← shown big
  let sHeavy ← shown heavy
  let sCtl ← shown ctl
  let sLight ← shown light
  check s!"{p}: a World carrying 2^40 is refused `allowancePastBound` ({sBig})"
    (sBig.startsWith "refused allowancePastBound") failures
  check s!"{p}: a World at allowanceMax with {over} founders past genesisWeightMax {genesisWeightMax} passes the allowance arm and is refused `potentialPastBound` ({sHeavy})"
    (0 < per && (heavy.map (fun w => decide (w.allowance ≤ allowanceMax) && decide (genesisWeightMax < w.weight)) |>.getD false) &&
      sHeavy.startsWith "refused potentialPastBound") failures
  check s!"{p}-control: one founder at allowanceMax reaches genesis ({sCtl}); {under} founders under genesisWeightMax reach genesis ({sLight})"
    (sCtl.startsWith "genesis" && sLight.startsWith "genesis" &&
      (light.map (fun w => decide (w.weight ≤ genesisWeightMax)) |>.getD false)) failures

/-- plant-empty-record (HOST-49, HOST-21's adopt argument): every record a Store holds advances its
step count, so a World at step 0 has no record past its base (`Host.Deployed.openWith_steps_zero`).
Reader: a frame that VERIFIES under the Store key, holding the codec's own bytes of NO steps, appended
to a fresh Store, is refused by the open as record 0's `emptyRecord`, and seg.log is unchanged (before
HOST-49 it opened as one record at step 0: a Store at step 0 holding a record, the case adopt's
`notAtGenesis` measure cannot see). Writer: the real `append` of an empty batch writes nothing and
returns the resident unchanged; its control, one step, appends one frame. -/
def emptyPlants (root : System.FilePath) (key : Digest) (keys : Keys) (failures : IO.Ref Nat) : IO Unit := do
  let p := "plant-empty-record"
  let dir := root / "reader"
  let _ ← (Host.genesis dir key keys cadence world recorder.mark Sim.genesis : IO (Except Fault Unit))
  let seg ← logical dir (headerBytes keys)
  let prev := seg.extract (seg.size - Log.tagBytes) seg.size
  let rec0 := (Record.codec dc).bytes []
  let f ← File.open (← newestSeg dir) .append
  f.writeAll (Log.frame keys.segment prev rec0)
  f.sync
  let before ← logicalSize dir (headerBytes keys)
  check s!"{p} fires: a verifying frame of the {rec0.size}-byte record of no steps follows the genesis base ({seg.size} -> {before})"
    (before == seg.size + Log.frameMax rec0.size) failures
  let o ← follow dir keys cadence
  let w ← (openWriter dir keys cadence world recorder.mark originChain foldStep : IO (Except Fault _))
  let after ← logicalSize dir (headerBytes keys)
  let isEmpty {α : Type} : Except Fault α → Bool
    | .error (.log (.record 0 f)) => f.name == "emptyRecord"
    | _ => false
  let shown {α : Type} : Except Fault α → String
    | .error (.log (.record i f)) => s!"record {i} {f.name}"
    | .error e => e.name
    | .ok _ => "opened"
  check s!"{p}: the follower and writer opens refuse record 0 `emptyRecord` and the file is unchanged ({shown o}, {shown w}, seg.log {before} -> {after})"
    (isEmpty o && isEmpty w && before == after) failures
  -- the pager's side (HOST-54): a page walks records BEFORE the base too, which no open folds, so
  -- `Page.walk` refuses the verifying frame of no steps `corrupt` at its offset by itself; CONTROL:
  -- the same frame holding one step walks
  let walkAt (r : ByteArray) : String :=
    let buf := seg ++ Log.frame keys.segment prev r
    match Id.run (Page.walk env dc keys.segment cadence.recordBytesMax 1000
        (fun off len => pure (buf.extract off (off + len))) buf.size 0 1 seg.size 0
        { steps := 0, chain := ByteArray.empty }) with
    | .error (.corrupt off) => s!"corrupt {off}"
    | .error _ => "refused"
    | .ok _ => "walked"
  let rec1 := (Record.codec dc).bytes [(.turn (mkTurn 77777 0 1024 [77777]), 0)]
  check s!"{p}-page: Page.walk refuses the frame of no steps `corrupt {seg.size}` ({walkAt rec0}); control: one step walks ({walkAt rec1})"
    (walkAt rec0 == s!"corrupt {seg.size}" && walkAt rec1 == "walked") failures
  -- the writer's side: the one append path writes nothing for an empty batch
  for (tag, staged) in [("", (#[] : Array (Step Nat × Nat))),
      ("-control", #[(.turn (mkTurn 4242 0 1024 [4242]), 0)])] do
    let dir := root / s!"writer{tag}"
    let _ ← (Host.genesis dir key keys cadence world recorder.mark Sim.genesis : IO (Except Fault Unit))
    let before ← logicalSize dir (headerBytes keys)
    let res ← do
      match ← (openWriter dir keys cadence world recorder.mark originChain foldStep : IO (Except Fault _)) with
      | .error e => pure (Except.error s!"open {e.name}")
      | .ok fwr =>
        let r := fwr.opening.resident
        let x ← append recorder keys.segment (fileCheckpoint dir keys cadence world recorder.mark originChain fwr)
          cadence (fileStore fwr) r r.world staged
        fwr.hold
        pure (match x with
          | .error e => Except.error e.name
          | .ok r' => Except.ok (r'.pos.offset == r.pos.offset && r'.index.size == r.index.size))
    let after ← logicalSize dir (headerBytes keys)
    let shownR := match res with | .ok b => s!"appended, resident unchanged={b}" | .error e => e
    if tag == "" then
      check s!"{p}-writer: the append of an empty batch writes nothing and leaves the resident unchanged ({shownR}, seg.log {before} -> {after})"
        ((match res with | .ok b => b | .error _ => false) && before == after) failures
    else
      check s!"{p}-writer-control: one step appends one frame ({shownR}, seg.log {before} -> {after})"
        ((match res with | .ok b => !b | .error _ => false) && before < after) failures

/-- plant-position-unfit (HOST-51, HOST-46's runtime witness): the deployed file checkpoint
(`fileCheckpoint`: `Base.seal` → base.tmp → sync → rename) asked to seal a base at segment position
2^64, a position the base layout's u64 cannot spell, refuses `positionUnfit` by name BEFORE writing:
base.world and index.log are byte-identical after it and the Store still opens. Its control, the same
seal at the Store's real position, installs. (An OPEN cannot be shown such a base: the layout has no
spelling for it, which is exactly why the writer must refuse first, HOST-41's law.) -/
def positionPlant (root : System.FilePath) (key : Digest) (keys : Keys) (failures : IO.Ref Nat) : IO Unit := do
  let p := "plant-position-unfit"
  for (tag, far) in [("", true), ("-control", false)] do
    let dir := root / s!"position{tag}"
    let _ ← (Host.genesis dir key keys cadence world recorder.mark Sim.genesis : IO (Except Fault Unit))
    match ← (openWriter dir keys cadence world recorder.mark originChain foldStep : IO (Except Fault _)) with
    | .error e => check s!"{p}{tag}: open ({e.name})" false failures
    | .ok fwr =>
      let r := fwr.opening.resident
      let base0 ← IO.FS.readBinFile (basePath dir)
      let idx0 ← IO.FS.readBinFile (← indexFile dir)
      let ck := fileCheckpoint dir keys cadence world recorder.mark originChain fwr (async := false)
      let pos : Position := if far then ⟨2 ^ 64, r.pos.tag⟩ else r.pos
      let res ← ck.write r.world pos #[] r.sealed.index
      fwr.hold
      let base1 ← IO.FS.readBinFile (basePath dir)
      let idx1 ← IO.FS.readBinFile (← indexFile dir)
      let shown := match res with | .ok _ => "installed" | .error f => f.name
      if far then
        check s!"{p}: a seal at position 2^64 is refused `positionUnfit` and base.world and index.log are unchanged ({shown})"
          ((match res with | .error (.positionUnfit o) => o == 2 ^ 64 | _ => false) && base1 == base0 && idx1 == idx0) failures
        let re ← follow dir keys cadence
        check s!"{p}: the Store still opens ({match re with | .ok _ => "opened" | .error e => e.name})"
          (match re with | .ok _ => true | .error _ => false) failures
      else
        check s!"{p}-control: the same seal at the real position {r.pos.offset} installs ({shown})"
          (match res with | .ok _ => true | .error _ => false) failures

/-- What the deployed `host check` verifies of the kept files (`Check.keptClean`, the one function),
at the toy World: the one open, then the kept headers, history and index. -/
def checkKept (dir : System.FilePath) (keys : Keys) :
    IO (Except String (Opening (World Nat) × Files × Header × ByteArray)) := do
  match ← (openAt dir keys cadence world recorder.mark originChain foldStep : IO (Except Fault _)) with
  | .error f => return .error f.text
  | .ok (o, fs) =>
    match ← Check.keptClean dir keys cadence.recordBytesMax (originChain o.opened.world) o fs with
    | .error (_, n) => return .error n
    | .ok (h, b) => return .ok (o, fs, h, b)

/-- A `log` page from `start` over a Store's kept files, as the deployed pager builds it
(`Page.kept` through `PageFiles.readers`, at the toy World). -/
def keptPage (dir : System.FilePath) (keys : Keys) (o : Opening (World Nat)) (fs : Files) (start : Nat) :
    IO (Except Page.Fault Page.Acc) := do
  let files : PageFiles := ⟨dir, keys, originChain o.opened.world, ← IO.mkRef (fs.retainedFrom, fs.indexFrom),
    ← IO.mkRef #[o.sealed.offset]⟩
  let (k0, read, readIndex) ← files.readers
  Page.kept env dc digestOf keys.segment cadence.recordBytesMax Page.budget k0 read
    (Page.entryAt (keys.forStore (originChain o.opened.world)) readIndex o.sealed.index.count o.index)
    (o.sealed.index.count + o.index.size) o.pos.offset (recorder.mark o.opened.world) start

/-- The checkpoint plants (HOST-64, KERNEL-44 Part 2). The same frames are served under the same key
twice: keeping every file (the default) and keeping the `retainFloor` = 2 newest (`--retain 2`).

* plant-retain-all: the Store keeps every file from `seg.0.log`; its logical segment recovers clean
  from `segmentInitial` with the origin frame first (exactly a pre-HOST-64 `seg.log`), its index is
  `index.0.log`, and `host check`'s verification (`Check.keptClean`) passes from offset 0;
* plant-retain-two: exactly the two newest segment files remain, the base names the older as
  `retainedFrom` (past 0) and the first kept entry as `indexFrom` (past 0), and `keptClean` passes
  from the oldest kept header (at a step count past 0: `retained_from`);
* plant-retain-bytes: dropping changes no logical byte: the kept Store's segment is the full one's
  from `retainedFrom` on, and its index file the full one's entries from `indexFrom` on;
* plant-checkpointed: a `log` page from step 0 over the kept Store is refused `checkpointed` (the
  full Store's control serves it; the kept Store's page from its oldest kept step serves);
* plant-header-flip / -origin / -position: the base's own file's header with one byte flipped is
  refused `checkpointCorrupt`; re-sealed under the Store's key stating another origin, `foreignOrigin`;
  stating another step count, `foreignSegment` (the control copy opens);
* plant-origin-frame: a byte flipped in the origin frame's record is not read by the open (it
  opens) and is refused `corrupt history` by the check (HOST-25's check moved from the open to
  `host check`, which reads the kept history);
* plant-missing-kept: the base's own file removed, the open refuses `missing seg.<o>.log`; the older
  kept file removed, the open or the check refuses `missing seg.<o>.log` naming it. -/
def checkpointPlants (root : System.FilePath) (key : Digest) (keys : Keys) (seed : Nat) (frames : List Frame)
    (failures : IO.Ref Nat) : IO Unit := do
  let all := root / "retain-all"
  let two := root / "retain-two"
  for d in [all, two] do
    let _ ← (Host.genesis d key keys cadence world recorder.mark Sim.genesis : IO (Except Fault Unit))
  let ra ← serveDir all keys cadence seed frames
  let rb ← serveDir two keys cadence seed frames (retain := some retainFloor)
  match ra, rb with
  | .error e, _ => check s!"plant-retain: the full Store serves ({e})" false failures
  | _, .error e => check s!"plant-retain: the kept Store serves ({e})" false failures
  | .ok _, .ok _ =>
  let fa ← segFiles all
  let fb ← segFiles two
  check s!"plant-retain fires: the full Store started more than {retainFloor} segment files ({fa.size})"
    (retainFloor < fa.size) failures
  match ← checkKept all keys, ← checkKept two keys with
  | .error e, _ => check s!"plant-retain-all: the full Store passes the check ({e})" false failures
  | _, .error e => check s!"plant-retain-two: the kept Store passes the check ({e})" false failures
  | .ok (oa, fsa, ha, _), .ok (ob, fsb, hb, _) =>
  let la ← logical all (headerBytes keys)
  let rv := Log.recover keys.segment cadence.recordBytesMax segmentInitial la
  check s!"plant-retain-all: every file kept from seg.0.log, the logical segment a clean seg.log from segmentInitial with the origin frame first, index.0.log, checked from 0"
    ((fa[0]?.map (·.1)) == some 0 && fsa.retainedFrom == 0 && fsa.indexFrom == 0 && ha.start == 0 &&
      rv.tail == .clean && rv.validLen == la.size && la.size == oa.pos.offset &&
      rv.records.head? == some (originChain oa.opened.world) &&
      ((← indexFile all).fileName == some "index.0.log")) failures
  check s!"plant-retain-two: exactly the {retainFloor} newest files remain ({fb.toList.map (·.1)}), retained_from={hb.steps} at offset {fsb.retainedFrom}, index_from={fsb.indexFrom}, checked from the oldest kept header"
    (fb.size == retainFloor && (fb[0]?.map (·.1)) == some fsb.retainedFrom && 0 < fsb.retainedFrom &&
      0 < fsb.indexFrom && hb.start == fsb.retainedFrom && 0 < hb.steps &&
      ((fb.back?.map (·.1)) == some ob.sealed.offset)) failures
  let lb ← logical two (headerBytes keys)
  let ia ← IO.FS.readBinFile (← indexFile all)
  let ib ← IO.FS.readBinFile (← indexFile two)
  let eb := entryBytes keys
  let n := min ib.size (ia.size - fsb.indexFrom * eb)
  check s!"plant-retain-bytes: the kept Store's segment is the full one's from {fsb.retainedFrom}, its index the full one's from entry {fsb.indexFrom}"
    (fsb.retainedFrom + lb.size == la.size && lb == la.extract fsb.retainedFrom la.size &&
      0 < n && ib.extract 0 n == ia.extract (fsb.indexFrom * eb) (fsb.indexFrom * eb + n) &&
      sameWorld oa.opened.world ob.opened.world) failures
  -- plant-checkpointed
  let pa ← keptPage all keys oa fsa 0
  let pb ← keptPage two keys ob fsb 0
  let pc ← keptPage two keys ob fsb hb.steps
  let shownP : Except Page.Fault Page.Acc → String
    | .ok a => s!"served {a.events.size} events"
    | .error f => f.name
  check s!"plant-checkpointed: a page from step 0 over the kept Store is refused `checkpointed` ({shownP pb}); controls: the full Store serves it ({shownP pa}), the kept Store serves from its oldest kept step {hb.steps} ({shownP pc})"
    ((match pb with | .error (.checkpointed 0 f) => f == hb.steps | _ => false) &&
      (match pa with | .ok a => 0 < a.events.size | .error _ => false) &&
      (match pc with | .ok a => 0 < a.events.size | .error _ => false)) failures
  -- the header plants, each on a copy of the full Store
  let baseFile := segPath all oa.sealed.offset
  let hbytes := (← IO.FS.readBinFile baseFile).extract 0 (headerBytes keys)
  match Header.read keys hbytes with
  | none => check "plant-header: the base's file's header reads" false failures
  | some h =>
  let other := ByteArray.mk (Array.replicate keys.chainBytes 0x55)
  let cases : List (String × String × ByteArray) :=
    [("control", "opened", hbytes),
     ("flip", "checkpointCorrupt", flipByte hbytes 40),
     ("origin", "foreignOrigin", Header.bytes keys { h with origin := other }),
     ("position", "foreignSegment", Header.bytes keys { h with steps := h.steps + 1 })]
  for (tag, want, hb') in cases do
    let d := root / s!"header-{tag}"
    copyStore all d
    let f := segPath d oa.sealed.offset
    let b ← IO.FS.readBinFile f
    IO.FS.writeBinFile f (hb' ++ b.extract (headerBytes keys) b.size)
    let got := match ← follow d keys cadence with | .ok _ => "opened" | .error e => e.name
    check s!"plant-header-{tag}: the base's own file's header {if tag == "control" then "as written opens" else s!"is refused `{want}`"} ({got})"
      (got == want) failures
  -- plant-origin-frame (HOST-25 under HOST-64): the open no longer reads the origin frame at 0 (a
  -- Store keeping fewer files has none); `host check` verifies it whenever it is kept
  let d0 := root / "origin-frame-flip"
  copyStore all d0
  let f0 := segPath d0 0
  let b0 ← IO.FS.readBinFile f0
  IO.FS.writeBinFile f0 (flipByte b0 (headerBytes keys + 5))
  let opened := match ← follow d0 keys cadence with | .ok _ => "opened" | .error e => e.name
  let checked ← match ← checkKept d0 keys with | .ok _ => pure "checked" | .error e => pure e
  check s!"plant-origin-frame: a byte flipped in the origin frame's record (seg.0.log): the open never reads it ({opened}), the check refuses `corrupt history` ({checked})"
    (opened == "opened" && checked == "corrupt history") failures
  -- plant-missing-kept
  let older := (fb[0]?.map (·.1)).getD 0
  let d1 := root / "missing-base-file"
  copyStore two d1
  IO.FS.removeFile (segPath d1 ob.sealed.offset)
  let m1 := match ← follow d1 keys cadence with | .ok _ => "opened" | .error e => e.text
  check s!"plant-missing-kept: the base's own file removed, the open refuses `missing seg.{ob.sealed.offset}.log` ({m1})"
    (m1 == s!"missing seg.{ob.sealed.offset}.log") failures
  let d2 := root / "missing-older-file"
  copyStore two d2
  IO.FS.removeFile (segPath d2 older)
  let m2 ← match ← checkKept d2 keys with | .ok _ => pure "checked" | .error e => pure e
  check s!"plant-missing-kept: the older kept file removed, the open or the check refuses `missing seg.{older}.log` ({m2})"
    (m2 == s!"missing seg.{older}.log") failures

def body (seed : Nat) (dirA dirB : System.FilePath) (control : Bool := false) : IO UInt32 := do
  let failures ← IO.mkRef 0
  let frames := (scenario seed 200).map (·.1)
  let key ← newKey
  let keys := fileKeys key
  do
    let dir := dirA
    let made ← (Host.genesis dir key keys cadence world recorder.mark Sim.genesis : IO (Except Fault Unit))
    check "genesis creates the Store" (match made with | .ok () => true | .error _ => false) failures
    let again ← (Host.genesis dir key keys cadence world recorder.mark Sim.genesis : IO (Except Fault Unit))
    check "a second genesis is refused `exists`"
      (match again with | .error .exists => true | _ => false) failures
    match ← serveDir dir keys cadence seed (frames.take 120) with
    | .error e => check s!"writer serves the scenario ({e})" false failures
    | .ok (r, refused) =>
      check "writer serves the scenario and seals (the base moved off genesis)"
        (0 < r.world.height ∧ 0 < r.sealed.offset) failures
      check "plant-second-writer: refused `locked` while the first lives" refused failures
      -- plant-crash-mid-seal: a truncated base.tmp and half of one more frame
      let baseBytes ← IO.FS.readBinFile (basePath dir)
      IO.FS.writeBinFile (baseTmpPath dir) (baseBytes.extract 0 (baseBytes.size / 2))
      let extra := Log.frame keys.segment r.pos.tag.bytes
        ((Record.codec dc).bytes [(.turn (mkTurn 77777 0 1024 [77777]), 0)])
      let half := extra.extract 0 (extra.size / 2)
      let f ← File.open (← newestSeg dir) .append
      f.writeAll half
      f.sync
      let before ← logicalSize dir (headerBytes keys)
      match ← follow dir keys cadence with
      | .error e => check s!"plant-crash-mid-seal: follower opens ({e.name})" false failures
      | .ok o =>
        let after ← logicalSize dir (headerBytes keys)
        check "plant-crash-mid-seal: follower sees the torn tail and truncates nothing"
          (o.opened.torn = half.size ∧ before = after ∧
            sameWorld o.opened.world r.world) failures
      -- plant-foreign-key
      let other := fileKeys (← newKey)
      check "plant-foreign-key: the Store under another key is refused `baseCorrupt`"
        (match ← follow dir other cadence with | .error f => f.name = "baseCorrupt" | _ => false) failures
      match ← serveDir dir keys cadence seed (frames.drop 120) (viaChannel := true) with
      | .error e => check s!"plant-crash-mid-seal: writer reopens and serves ({e})" false failures
      | .ok (r2, _) =>
        check "plant-crash-mid-seal: writer truncated the tail, ignored the tmp, served on, through the deployed channelPort in rounds of 5 with frames put back, one reply per request"
          (r.world.height < r2.world.height) failures
        let size ← logicalSize dir (headerBytes keys)
        let reopened ← follow dir keys cadence
        check "reopen after the crash is clean and reaches the loop's World"
          (match reopened with
           | .ok o => o.opened.torn = 0 && sameWorld o.opened.world r2.world && o.pos.offset == size
           | .error _ => false) failures
  -- plant-foreign-frame, on a Store that never seals (its tail is every frame)
  do
    let dir := dirB
    let still := { cadence with sealMinBytes := 1 <<< 20, recordBytesMax := 1 <<< 16 }
    let _ ← (Host.genesis dir key keys still world recorder.mark Sim.genesis : IO (Except Fault Unit))
    match ← serveDir dir keys still seed (frames.take 60) with
    | .error e => check s!"plant-foreign-frame: serve ({e})" false failures
    | .ok _ =>
      let seg ← logical dir (headerBytes keys)
      let rv := Log.recover keys.segment still.recordBytesMax segmentInitial seg
      match rv.records with
      | o0 :: r1 :: _ :: _ :: _ =>
        -- the first frame after genesis's origin frame, re-sealed under another key
        let cut := frameSize o0
        let foreign := Log.frame (fileKeys (← newKey)).segment segmentInitial r1
        let spliced := seg.extract 0 cut ++ foreign ++ seg.extract (cut + foreign.size) seg.size
        writeLogical dir (headerBytes keys) spliced
        check "plant-foreign-frame: a frame under another key is refused `corrupt`"
          (match ← follow dir keys still with | .error f => f.name = "corrupt" | _ => false) failures
      | _ => check "plant-foreign-frame: at least three frames" false failures
    -- plant-foreign-segment (HOST-18, HOST-64), two fresh Stores under this temp dir: another
    -- Store's segment files copied over this Store's; the writer must refuse them by name and
    -- truncate nothing (before HOST-18 it opened as a torn tail and the writer truncated it). Under
    -- another key the copied files' headers do not verify: `checkpointCorrupt` (the header
    -- plants below refuse `foreignOrigin` and `foreignSegment` under this Store's own key)
    let dir2 := dir / "theirs"
    let dir := dir / "mine"
    let _ ← (Host.genesis dir key keys still world recorder.mark Sim.genesis : IO (Except Fault Unit))
    do
      let key2 ← newKey
      let keys2 := fileKeys key2
      let _ ← (Host.genesis dir2 key2 keys2 still world recorder.mark Sim.genesis : IO (Except Fault Unit))
      match ← serveDir dir2 keys2 still seed (frames.take 30) with
      | .error e => check s!"plant-foreign-segment: the other Store serves ({e})" false failures
      | .ok _ =>
        let mine ← logical dir (headerBytes keys)
        let theirs ← logical dir2 (headerBytes keys2)
        removeSegs dir
        copySegs dir2 dir
        let before ← logicalSize dir (headerBytes keys)
        check "plant-foreign-segment fires: the copied segment is another Store's (longer, other bytes)"
          (mine.size < theirs.size && mine != theirs.extract 0 mine.size) failures
        let opened ← (openWriter dir keys still world recorder.mark originChain foldStep : IO (Except Fault _))
        let after ← logicalSize dir (headerBytes keys)
        check s!"plant-foreign-segment: the writer refuses `checkpointCorrupt` and the files are unchanged ({match opened with | .error f => f.name | .ok _ => "opened"})"
          ((match opened with | .error f => f.name = "checkpointCorrupt" | .ok _ => false) && before = after) failures
  missingPlants (dirB / "missing") key keys failures
  restartPlants (dirB / "restart") key keys seed frames failures
  wideFollowPlant (dirB / "wide") key keys failures
  boundPlants (dirB / "bound") key keys failures
  emptyPlants (dirB / "empty") key keys failures
  budgetPlants failures
  positionPlant (dirB / "position") key keys failures
  checkpointPlants (dirB / "checkpoint") key keys seed frames failures
  if control then check "harness-control: GATES-15's known-red control, an expectation nothing meets (this run must read RED)" false failures
  let n ← failures.get
  IO.println (if n = 0 then "ALL PASS" else s!"{n} FAILED")
  return (if n = 0 then 0 else 1)

/-- `host-file-sim SEED [DIR]`: the Stores live under a fresh `DIR/run-<seed>-<random hex>/`
(DIR defaults to `.lake/host-file-sim`), which this run creates, refuses to reuse, and removes
when it ends (D9: no runtime temp-file primitive; they abort under a missing TMPDIR). -/
def run (args : List String) : IO UInt32 := do
  -- `--harness-control` (GATES-15): one check nothing meets, inside the ordinary run. Any other
  -- argument that is not `SEED [DIR]` is refused, never read as seed 1 or as a directory.
  let control := args.contains "--harness-control"
  let (some seed, root) := (match args.filter (· != "--harness-control") with
      | [] => (some 1, ".lake/host-file-sim")
      | [s] => (s.toNat?, ".lake/host-file-sim")
      | [s, d] => (s.toNat?, d)
      | _ => (none, ""))
    | IO.eprintln s!"usage: host-file-sim [SEED [DIR]] [--harness-control] (got {args})"; return 2
  let root : System.FilePath := root
  let runDir := root / s!"run-{seed}-{← IO.rand 0 (1 <<< 30)}"
  if ← runDir.pathExists then
    IO.eprintln s!"refused exists {runDir}"; return 2
  IO.FS.createDirAll runDir
  try body seed (runDir / "a") (runDir / "b") control
  finally IO.FS.removeDirAll runDir

end Nanodregg.Host.Sim.File
