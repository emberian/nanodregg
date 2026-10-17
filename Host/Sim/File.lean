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
Prints `FAIL <check>` per failure and `ALL PASS` when none.
-/
import Host.Store
import Host.Keys
import Host.Sim.Run

namespace Nanodregg.Host.Sim.File

open Nanodregg.Kernel Nanodregg.Host.Sim Nanodregg.Codec

abbrev Fault := StoreFault (Record.Fault (Reject Nat))

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
    let (exit, r) ← restarts (serve machine recorder keys.segment (fileCheckpoint dir keys c world recorder.mark wr.index) c
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

def body (seed : Nat) (dirA dirB : System.FilePath) : IO UInt32 := do
  let failures ← IO.mkRef 0
  let frames := (scenario seed 200).map (·.1)
  let key ← newKey
  let keys := Keys.ofKey key shapes
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
      let other := Keys.ofKey (← newKey) shapes
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
        let foreign := Log.frame (Keys.ofKey (← newKey) shapes).segment segmentInitial r1
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
      let keys2 := Keys.ofKey key2 shapes
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
