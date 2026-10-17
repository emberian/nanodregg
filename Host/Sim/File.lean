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
def serveDir (dir : System.FilePath) (keys : Keys) (c : Cadence) (seed : Nat) (frames : List Frame) :
    IO (Except String (Resident (World Nat) × Bool)) := do
  match ← (openWriter dir keys c world foldStep : IO (Except Fault _)) with
  | .error e => return .error s!"open: {e.name}"
  | .ok wr =>
    let fr ← IO.mkRef frames
    let sp ← IO.mkRef (splits seed frames.length)
    let sent ← IO.mkRef #[]
    let o := wr.opening
    let (exit, r) ← serve machine (Record.encode dc) keys.segment (fileCheckpoint dir keys c world) c
      (fileStore wr.segment) (scriptPort fr sp sent) ⟨16, 1 <<< 20⟩ (frames.length + 1)
      { world := o.opened.world, pos := o.pos, sealed := o.sealed } none
    let second ← (openWriter dir keys c world foldStep : IO (Except Fault _))
    let refused := match second with | .error .locked => true | _ => false
    wr.segment.sync  -- the writer's handle (and so its lock) is alive up to here
    match exit with
    | .eof => return .ok (r, refused)
    | e => return .error s!"serve ended {e.name}"

def follow (dir : System.FilePath) (keys : Keys) (c : Cadence) : IO (Except Fault (Opening (World Nat))) :=
  openFollower dir keys c world foldStep

def fileSize (p : System.FilePath) : IO Nat := do
  return (← (← File.open p .read).size).toNat

def run (args : List String) : IO UInt32 := do
  let seed := (args.head? >>= String.toNat?).getD 1
  let failures ← IO.mkRef 0
  let frames := (scenario seed 200).map (·.1)
  let key ← newKey
  let keys := Keys.ofKey key
  IO.FS.withTempDir fun dir => do
    let made ← (Host.genesis dir key keys cadence world Sim.genesis : IO (Except Fault Unit))
    check "genesis creates the Store" (match made with | .ok () => true | .error _ => false) failures
    let again ← (Host.genesis dir key keys cadence world Sim.genesis : IO (Except Fault Unit))
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
        (Record.encode dc r.world #[mkTurn 77777 0 1024 [77777]])
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
      let other := Keys.ofKey (← newKey)
      check "plant-foreign-key: the Store under another key is refused `baseCorrupt`"
        (match ← follow dir other cadence with | .error f => f.name = "baseCorrupt" | _ => false) failures
      match ← serveDir dir keys cadence seed (frames.drop 120) with
      | .error e => check s!"plant-crash-mid-seal: writer reopens and serves ({e})" false failures
      | .ok (r2, _) =>
        check "plant-crash-mid-seal: writer truncated the tail, ignored the tmp, served on"
          (r.world.height < r2.world.height) failures
        let size ← fileSize (segmentPath dir)
        let reopened ← follow dir keys cadence
        check "reopen after the crash is clean and reaches the loop's World"
          (match reopened with
           | .ok o => o.opened.torn = 0 && sameWorld o.opened.world r2.world && o.pos.offset == size
           | .error _ => false) failures
  -- plant-foreign-frame, on a Store that never seals (its tail is every frame)
  IO.FS.withTempDir fun dir => do
    let still := { cadence with sealMinBytes := 1 <<< 20, recordBytesMax := 1 <<< 16 }
    let _ ← (Host.genesis dir key keys still world Sim.genesis : IO (Except Fault Unit))
    match ← serveDir dir keys still seed (frames.take 60) with
    | .error e => check s!"plant-foreign-frame: serve ({e})" false failures
    | .ok _ =>
      let seg ← IO.FS.readBinFile (segmentPath dir)
      let rv := Log.recover keys.segment still.recordBytesMax segmentInitial seg
      match rv.records with
      | r0 :: _ :: _ :: _ =>
        let foreign := Log.frame (Keys.ofKey (← newKey)).segment segmentInitial r0
        let spliced := foreign ++ seg.extract foreign.size seg.size
        IO.FS.writeBinFile (segmentPath dir) spliced
        check "plant-foreign-frame: a frame under another key is refused `corrupt`"
          (match ← follow dir keys still with | .error f => f.name = "corrupt" | _ => false) failures
      | _ => check "plant-foreign-frame: at least three frames" false failures
  let n ← failures.get
  IO.println (if n = 0 then "ALL PASS" else s!"{n} FAILED")
  return (if n = 0 then 0 else 1)

end Nanodregg.Host.Sim.File
