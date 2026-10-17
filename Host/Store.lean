/-
# Host.Store — a Store directory: genesis, the writer, the follower, and the base on disk

    STORE/key          32 bytes, 0600: the integrity-at-rest key (HOST-16); written once by genesis
    STORE/seg.log      the frames (Host.Log), append-only; its append handle is flock'd
    STORE/base.world   the newest sealed base (Host.Base); replaced atomically through base.tmp

The lock IS the append handle: `openWriter` flocks the descriptor it appends through, so no byte
can be appended without the lock, and the lock lives exactly as long as that handle (a separate
LOCK handle is released at its last use in compiled Lean: host-file-sim's plant-second-writer).

`openAt` is the one open: read the base (bounded before it is read), read the segment from the
base's offset (bounded by `tailRead`), and `openLog` the tail from the base's World. The writer
then truncates the torn tail and syncs before anything is appended; a follower writes nothing and
reads a torn tail as "not yet written". Physical IO is `Host.File` (Host/c/file.c), so this module
runs only in a linked executable.
-/
import Host.File
import Host.Open

namespace Nanodregg.Host

open Nanodregg.Codec (Digest Stream)

def keyPath (dir : System.FilePath) : System.FilePath := dir / "key"
def segmentPath (dir : System.FilePath) : System.FilePath := dir / "seg.log"
def basePath (dir : System.FilePath) : System.FilePath := dir / "base.world"
def baseTmpPath (dir : System.FilePath) : System.FilePath := dir / "base.tmp"

variable {W F : Type}

/-- A whole file of at most `max` bytes, or why not. -/
def readBounded (path : System.FilePath) (max : Nat) (tooLarge : Nat → StoreFault F) :
    IO (Except (StoreFault F) ByteArray) := do
  let f ← File.open path .read
  let size := (← f.size).toNat
  if max < size then return .error (tooLarge size)
  let bytes ← f.readAt 0 size.toUSize
  if bytes.size ≠ size then return .error (.shortRead bytes.size size)
  return .ok bytes

/-- Create `path` (refusing an existing file) holding `bytes`, durably. -/
def writeNew (path : System.FilePath) (bytes : ByteArray) : IO Unit := do
  let f ← File.open path .createNew
  f.writeAll bytes
  f.sync

/-- The Store key. -/
def readKey (dir : System.FilePath) : IO (Except (StoreFault F) Digest) := do
  match ← readBounded (keyPath dir) 32 .badKey with
  | .error e => return .error e
  | .ok b => match Digest.ofBytes? b with
    | some k => return .ok k
    | none => return .error (.badKey b.size)

/-- The base sealer over a Store directory: `base.tmp` → sync → rename over `base.world` → sync
the directory. A crash leaves the old base or the new one. -/
def fileCheckpoint (dir : System.FilePath) (keys : Keys) (c : Cadence) (world : Stream W)
    (async : Bool := true) : Checkpoint W where
  async
  write w offset tag := do
    match Base.file keys c world w offset tag with
    | .error f => return .error f
    | .ok bytes =>
      try
        if ← (baseTmpPath dir).pathExists then IO.FS.removeFile (baseTmpPath dir)
        writeNew (baseTmpPath dir) bytes
        IO.FS.rename (baseTmpPath dir) (basePath dir)
        syncDir dir.toString
        return .ok (world.size w)
      catch e => return .error (.io (toString e))

/-- The one open (writer and follower) over a Store directory: `openWith` reading the files. -/
def openAt (dir : System.FilePath) (keys : Keys) (c : Cadence) (world : Stream W)
    (step : W → ByteArray → Except F W) (segment : File) : IO (Except (StoreFault F) (Opening W)) := do
  unless ← (basePath dir).pathExists do return .error (.base .noBase)
  match ← readBounded (basePath dir) (Log.frameMax c.baseRecordMax) (fun n => .base (.baseTooLarge n)) with
  | .error e => return .error e
  | .ok file =>
    let size := (← segment.size).toNat
    openWith keys c world step file size fun off len => do
      let tail ← segment.readAt off.toUInt64 len.toUSize
      if tail.size = len then return .ok tail else return .error (.shortRead tail.size len)

/-- An open writer: the locked append handle, and the loop's state. -/
structure Writer (W : Type) where
  segment : File
  opening : Opening W

/-- Open the Store as its one writer: lock, open, truncate the torn tail, sync. A stale
`base.tmp` (a crash mid-seal) is never read; the next seal replaces it. -/
def openWriter (dir : System.FilePath) (keys : Keys) (c : Cadence) (world : Stream W)
    (step : W → ByteArray → Except F W) : IO (Except (StoreFault F) (Writer W)) := do
  let segment ← File.open (segmentPath dir) .append
  unless ← segment.tryLock do return .error .locked
  match ← openAt dir keys c world step (← File.open (segmentPath dir) .read) with
  | .error e => return .error e
  | .ok o =>
    if 0 < o.opened.torn then
      segment.truncate o.pos.offset.toUInt64
      segment.sync
    return .ok ⟨segment, o⟩

/-- Open the Store as a follower of its directory: the same open, no lock, nothing written. -/
def openFollower (dir : System.FilePath) (keys : Keys) (c : Cadence) (world : Stream W)
    (step : W → ByteArray → Except F W) : IO (Except (StoreFault F) (Opening W)) := do
  openAt dir keys c world step (← File.open (segmentPath dir) .read)

/-- Create a Store holding `w₀` under `key`: the key, an empty segment, and the base at offset 0.
Refuses a directory that already holds any of them. -/
def genesis (dir : System.FilePath) (key : Digest) (keys : Keys) (c : Cadence) (world : Stream W)
    (w₀ : W) : IO (Except (StoreFault F) Unit) := do
  for p in [keyPath dir, segmentPath dir, basePath dir, baseTmpPath dir] do
    if ← p.pathExists then return .error .exists
  IO.FS.createDirAll dir
  writeNew (keyPath dir) key.bytes
  writeNew (segmentPath dir) ByteArray.empty
  syncDir dir.toString
  match ← (fileCheckpoint dir keys c world).write w₀ 0 ⟨segmentInitial, Digest.zero.size_eq⟩ with
  | .error f => return .error (.seal f)
  | .ok _ => return .ok ()

end Nanodregg.Host
