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
Prints `FAIL <check>` per failure and `ALL PASS` when none.
-/
import Host.Store
import Host.Keys
import Host.Sim.Run

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
    (roundFuel : Nat := 5) (viaChannel : Bool := false) :
    IO (Except String (Resident (World Nat) × Bool)) := do
  match ← (openWriter dir keys c world recorder.mark originChain foldStep : IO (Except Fault _)) with
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
    let (exit, r) ← restarts (serve machine recorder keys.segment (fileCheckpoint dir keys c world recorder.mark originChain wr.index) c
        (fileStore wr.segment) (fun _ _ => pure (0, ByteArray.empty)) port limits roundFuel)
      (reopenAt dir keys c world recorder.mark originChain foldStep) recorder.mark (frames.length + 1) o.resident
    let second ← (openWriter dir keys c world recorder.mark originChain foldStep : IO (Except Fault _))
    let refused := match second with | .error .locked => true | _ => false
    wr.segment.sync  -- the writer's handle (and so its lock) is alive up to here
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
  for f in StorePart.all do
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
    let r ← (fileCheckpoint d keys cadence world recorder.mark originChain wr.index).write
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
  let segAtCopy ← IO.FS.readBinFile (segmentPath dir)
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
  let segBefore ← fileSize (segmentPath dir)
  let idxBefore ← fileSize (indexPath dir)
  let extra := Log.frame keys.segment cur.pos.tag.bytes
    (recorder.encode cur.opened.world #[(mkTurn 77777 0 1024 [77777], 0)])
  let half := extra.extract 0 (extra.size / 2)
  let orphan := ByteArray.mk (Array.replicate (entryBytes keys / 2) 0xAB)
  let f ← File.open (segmentPath dir) .append
  f.writeAll half
  f.sync
  let g ← File.open (indexPath dir) .append
  g.writeAll orphan
  g.sync
  let segTorn ← fileSize (segmentPath dir)
  let idxTorn ← fileSize (indexPath dir)
  check s!"{p} fires: half a frame appended to seg.log and half an entry to index.log, both grew"
    (segBefore = cur.pos.offset && segBefore < segTorn &&
      idxBefore = cur.sealed.index.count * entryBytes keys && idxBefore < idxTorn) failures
  let tornSeg ← IO.FS.readBinFile (segmentPath dir)
  let tornIdx ← IO.FS.readBinFile (indexPath dir)
  -- the restart, scoped: only a Bool leaves it, so the Writer (its handles and lock) is freed here
  let opened ← do
    let w ← (openWriter dir keys cadence world recorder.mark originChain foldStep : IO (Except Fault _))
    pure (match w with | .ok _ => true | .error _ => false)
  let released ← do
    let h ← File.open (segmentPath dir) .append
    h.tryLock
  let segCut ← fileSize (segmentPath dir)
  let idxCut ← fileSize (indexPath dir)
  check s!"{p}: the restart opens, cuts seg.log to its valid end and index.log to count · entryBytes, and releases its lock"
    (opened && released && segCut = cur.pos.offset && idxCut = cur.sealed.index.count * entryBytes keys)
    failures
  let segCutBytes ← IO.FS.readBinFile (segmentPath dir)
  let idxCutBytes ← IO.FS.readBinFile (indexPath dir)
  match ← serveDir dir keys cadence seed rest with
  | .error e => check s!"{p}: the restarted writer serves on ({e})" false failures
  | .ok (r2, _) =>
  check s!"{p} fires: the restarted writer sealed again (its base moved past the copied one)"
    (cur.sealed.offset < r2.sealed.offset) failures
  let idx ← IO.FS.readBinFile (indexPath dir)
  let seg ← IO.FS.readBinFile (segmentPath dir)
  check s!"{p} fires: the later seg.log and index.log are the cuts plus appends, NOT the torn files plus appends"
    (seg.extract 0 segCutBytes.size == segCutBytes && seg.extract 0 tornSeg.size != tornSeg &&
      idx.extract 0 idxCutBytes.size == idxCutBytes && idx.extract 0 tornIdx.size != tornIdx) failures
  let keyBytes ← IO.FS.readBinFile (keyPath dir)
  let writeBackup (d : System.FilePath) (s : ByteArray) : IO Unit := do
    IO.FS.createDirAll d
    IO.FS.writeBinFile (keyPath d) keyBytes
    IO.FS.writeBinFile (basePath d) baseCopy
    IO.FS.writeBinFile (indexPath d) idx
    IO.FS.writeBinFile (segmentPath d) s
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

def body (seed : Nat) (dirA dirB : System.FilePath) : IO UInt32 := do
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
        (recorder.encode r.world #[(mkTurn 77777 0 1024 [77777], 0)])
      let half := extra.extract 0 (extra.size / 2)
      let f ← File.open (segmentPath dir) .append
      f.writeAll half
      f.sync
      let before ← fileSize (segmentPath dir)
      match ← follow dir keys cadence with
      | .error e => check s!"plant-crash-mid-seal: follower opens ({e.name})" false failures
      | .ok o =>
        let after ← fileSize (segmentPath dir)
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
        let size ← fileSize (segmentPath dir)
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
      let seg ← IO.FS.readBinFile (segmentPath dir)
      let rv := Log.recover keys.segment still.recordBytesMax segmentInitial seg
      match rv.records with
      | o0 :: r1 :: _ :: _ :: _ =>
        -- the first frame after genesis's origin frame, re-sealed under another key
        let cut := frameSize o0
        let foreign := Log.frame (fileKeys (← newKey)).segment segmentInitial r1
        let spliced := seg.extract 0 cut ++ foreign ++ seg.extract (cut + foreign.size) seg.size
        IO.FS.writeBinFile (segmentPath dir) spliced
        check "plant-foreign-frame: a frame under another key is refused `corrupt`"
          (match ← follow dir keys still with | .error f => f.name = "corrupt" | _ => false) failures
      | _ => check "plant-foreign-frame: at least three frames" false failures
    -- plant-foreign-segment (HOST-18), two fresh Stores under this temp dir: another Store's
    -- seg.log copied over this Store's; the writer must refuse it by name and truncate nothing
    -- (before HOST-18 it opened as a torn tail and the writer truncated it to the base's offset)
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
        let mine ← IO.FS.readBinFile (segmentPath dir)
        let theirs ← IO.FS.readBinFile (segmentPath dir2)
        IO.FS.writeBinFile (segmentPath dir) theirs
        let before ← fileSize (segmentPath dir)
        check "plant-foreign-segment fires: the copied segment is another Store's (longer, other bytes)"
          (mine.size < theirs.size && mine != theirs.extract 0 mine.size) failures
        let opened ← (openWriter dir keys still world recorder.mark originChain foldStep : IO (Except Fault _))
        let after ← fileSize (segmentPath dir)
        check "plant-foreign-segment: the writer refuses `foreignSegment` and the file is unchanged"
          ((match opened with | .error f => f.name = "foreignSegment" | .ok _ => false) && before = after) failures
  missingPlants (dirB / "missing") key keys failures
  restartPlants (dirB / "restart") key keys seed frames failures
  let n ← failures.get
  IO.println (if n = 0 then "ALL PASS" else s!"{n} FAILED")
  return (if n = 0 then 0 else 1)

/-- `host-file-sim SEED [DIR]`: the Stores live under a fresh `DIR/run-<seed>-<random hex>/`
(DIR defaults to `.lake/host-file-sim`), which this run creates, refuses to reuse, and removes
when it ends (D9: no runtime temp-file primitive; they abort under a missing TMPDIR). -/
def run (args : List String) : IO UInt32 := do
  let seed := (args.head? >>= String.toNat?).getD 1
  let root : System.FilePath := (args.drop 1).head?.getD ".lake/host-file-sim"
  let runDir := root / s!"run-{seed}-{← IO.rand 0 (1 <<< 30)}"
  if ← runDir.pathExists then
    IO.eprintln s!"refused exists {runDir}"; return 2
  IO.FS.createDirAll runDir
  try body seed (runDir / "a") (runDir / "b")
  finally IO.FS.removeDirAll runDir

end Nanodregg.Host.Sim.File
