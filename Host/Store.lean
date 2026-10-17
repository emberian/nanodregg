/-
# Host.Store — opening a Store directory: the writer and the follower

    STORE/seg.log   the frames (Host.Log), append-only; its append handle is flock'd

The lock IS the append handle: `openWriter` flocks the descriptor it appends through, so no byte
can be appended without the lock, and the lock lives exactly as long as that handle. (A separate
LOCK file's handle is released the moment Lean's refcount drops it, which in compiled code is its
last use, not the end of the writer: host-file-sim's plant-second-writer caught exactly that.)

`openWriter`: take the lock (a second writer is refused `locked` by name), read the segment, run
`openLog` (the one open, `Host.Open`), and truncate the torn tail, then sync, before anything is
appended, so a later crash cannot bring the torn bytes back in front of a new frame.
`openFollower`: no lock and no truncation. A follower reads the torn tail as "not yet written".

The segment is read whole: `segmentBytesMax` bounds it, and a larger segment is refused `tooLarge`
by name, never read partially. The base (HOST-14) will shorten that read to one base plus one cadence.
Physical IO is `Host.File` (Host/c/file.c), so this module runs only in a linked executable.
-/
import Host.File
import Host.Open

namespace Nanodregg.Host

/-- Bytes of segment one open reads (until the base lands, the whole log; HOST-14 condition 4). -/
def segmentBytesMax : Nat := 1 <<< 30

/-- Why a Store does not open (law 7). -/
inductive StoreFault (F : Type) where
  /-- another writer holds the segment's lock -/
  | locked
  /-- the segment is larger than `segmentBytesMax` -/
  | tooLarge (bytes : Nat)
  /-- a read returned fewer bytes than the size said: the file changed under us -/
  | shortRead (got want : Nat)
  | log (fault : OpenFault F)
  deriving Repr

/-- An open writer: the locked append handle, and what was opened. -/
structure Writer (W : Type) where
  segment : File
  opened : Opened W

variable {W F : Type}

def segmentPath (dir : System.FilePath) : System.FilePath := dir / "seg.log"

/-- The whole segment, bounded. -/
def readSegment (dir : System.FilePath) : IO (Except (StoreFault F) ByteArray) := do
  let f ← File.open (segmentPath dir) .read
  let size := (← f.size).toNat
  if segmentBytesMax < size then return .error (.tooLarge size)
  let bytes ← f.readAt 0 size.toUSize
  if bytes.size ≠ size then return .error (.shortRead bytes.size size)
  return .ok bytes

/-- Open the Store as its one writer. -/
def openWriter (dir : System.FilePath) (s : Log.Sealer) (recordMax : Nat)
    (step : W → ByteArray → Except F W) (w₀ : W) (initial : ByteArray) :
    IO (Except (StoreFault F) (Writer W)) := do
  let segment ← File.open (segmentPath dir) .append
  unless ← segment.tryLock do return .error .locked
  syncDir dir.toString
  match ← readSegment dir with
  | .error e => return .error e
  | .ok bytes =>
    match openLog s recordMax step w₀ initial bytes with
    | .error e => return .error (.log e)
    | .ok o =>
      if 0 < o.torn then
        segment.truncate o.validLen.toUInt64
        segment.sync
      return .ok ⟨segment, o⟩

/-- Open the Store as a follower: the same open, no lock, nothing written. -/
def openFollower (dir : System.FilePath) (s : Log.Sealer) (recordMax : Nat)
    (step : W → ByteArray → Except F W) (w₀ : W) (initial : ByteArray) :
    IO (Except (StoreFault F) (Opened W)) := do
  match ← readSegment dir with
  | .error e => return .error e
  | .ok bytes =>
    match openLog s recordMax step w₀ initial bytes with
    | .error e => return .error (.log e)
    | .ok o => return .ok o

end Nanodregg.Host
