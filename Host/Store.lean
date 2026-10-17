/-
# Host.Store — a Store directory: genesis, the writer, the follower, and the base on disk

    STORE/key          32 bytes, 0600: the integrity-at-rest key (HOST-16); written once by genesis
    STORE/seg.log      the frames (Host.Log), append-only, from genesis's origin frame; its
                       append handle is flock'd
    STORE/index.log    one MAC'd page per seal: the index entries since the base before it (HOST-30)
    STORE/base.world   the newest sealed base (Host.Base); replaced atomically through base.tmp

(The layout as data, with the backup copy order: `Host.Store.layout`, `Host.Store.backupOrder`.)

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
def indexPath (dir : System.FilePath) : System.FilePath := dir / "index.log"
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

/-- Make `bytes` the Store's base: `base.tmp` → sync → rename over `base.world` → sync the
directory. A crash leaves the old base or the new one. -/
def installBase (dir : System.FilePath) (bytes : ByteArray) : IO Unit := do
  if ← (baseTmpPath dir).pathExists then IO.FS.removeFile (baseTmpPath dir)
  writeNew (baseTmpPath dir) bytes
  IO.FS.rename (baseTmpPath dir) (basePath dir)
  syncDir dir.toString

/-- The base sealer over a Store directory, appending pages through `index` (the writer's
`index.log` append handle). Both encodings are checked before anything is written; then the page
is appended and synced, and only then is the base naming it installed (`installBase`), so a crash
leaves the old base with at most an orphan page after its prefix (HOST-30). Never silent (D8):
every seal writes one `STATUS seal` line to stderr, installed or refused by name. -/
def fileCheckpoint (dir : System.FilePath) (keys : Keys) (c : Cadence) (world : Stream W)
    (mark : W → Nat × ByteArray) (index : File) (async : Bool := true) : Checkpoint W where
  async
  write w seg entries ipos := do
    let at_ := s!"height={(mark w).1} offset={seg.offset} entries={entries.size} index_offset={ipos.offset}"
    match Base.seal keys c world w seg ipos entries with
    | .error f =>
      IO.eprintln s!"STATUS seal {at_} refused={f.name}"
      return .error f
    | .ok (page, ipos', bytes) =>
      try
        unless page.isEmpty do
          index.writeAll page
          index.sync
        installBase dir bytes
        IO.eprintln s!"STATUS seal {at_} base_bytes={bytes.size} world_bytes={world.size w} page_bytes={page.size}"
        return .ok (world.size w, keys.worldDigest (worldBytesOf bytes (world.size w)), ipos')
      catch e =>
        IO.eprintln s!"STATUS seal {at_} refused=io"
        return .error (.io (toString e))

/-- The one open (writer and follower) over a Store directory: `openWith` reading the files. -/
def openAt (dir : System.FilePath) (keys : Keys) (c : Cadence) (world : Stream W)
    (mark : W → Nat × ByteArray) (origin : W → ByteArray) (step : W → ByteArray → Except F W) (segment : File) : IO (Except (StoreFault F) (Opening W)) := do
  unless ← (basePath dir).pathExists do return .error (.base .noBase)
  match ← readBounded (basePath dir) (Log.frameMax c.baseRecordMax) (fun n => .base (.baseTooLarge n)) with
  | .error e => return .error e
  | .ok file =>
    let size := (← segment.size).toNat
    let index ← File.open (indexPath dir) .read
    let indexSize := (← index.size).toNat
    openWith keys c world mark origin step file size indexSize
      (fun off len => do return .ok (← index.readAt off.toUInt64 len.toUSize))
      fun off len => do return .ok (← segment.readAt off.toUInt64 len.toUSize)

/-- The loop's state as an open leaves it. -/
def Opening.resident (o : Opening W) : Resident W :=
  { world := o.opened.world, pos := o.pos, sealed := o.sealed, index := o.index }

/-- The reopen of a fuel restart (`Host.restarts`): the one open, through a fresh read handle (the
writer's locked append handle stays the lock). A torn tail here is bytes the loop never synced, a
divergence, never something to truncate. -/
def reopenAt (dir : System.FilePath) (keys : Keys) (c : Cadence) (world : Stream W)
    (mark : W → Nat × ByteArray) (origin : W → ByteArray) (step : W → ByteArray → Except F W) : IO (Except Exit (Resident W)) := do
  match ← openAt dir keys c world mark origin step (← File.open (segmentPath dir) .read) with
  | .error f => return .error (.reopenFailed f.name)
  | .ok o => return if o.opened.torn = 0 then .ok o.resident else .error .reopenDiverged

/-- An open writer: the locked append handle, the `index.log` append handle, and the loop's state. -/
structure Writer (W : Type) where
  segment : File
  index : File
  opening : Opening W

/-- Open the Store as its one writer: lock, open, truncate the torn tail and any orphan index page
(bytes past the prefix the base names: never a byte the base names, `Opening.orphan`), sync. A
stale `base.tmp` (a crash mid-seal) is never read; the next seal replaces it. -/
def openWriter (dir : System.FilePath) (keys : Keys) (c : Cadence) (world : Stream W)
    (mark : W → Nat × ByteArray) (origin : W → ByteArray) (step : W → ByteArray → Except F W) : IO (Except (StoreFault F) (Writer W)) := do
  let segment ← File.open (segmentPath dir) .append
  unless ← segment.tryLock do return .error .locked
  match ← openAt dir keys c world mark origin step (← File.open (segmentPath dir) .read) with
  | .error e => return .error e
  | .ok o =>
    if 0 < o.opened.torn then
      segment.truncate o.pos.offset.toUInt64
      segment.sync
    let index ← File.open (indexPath dir) .append
    if 0 < o.orphan then
      index.truncate o.sealed.index.offset.toUInt64
      index.sync
    return .ok ⟨segment, index, o⟩

/-- Open the Store as a follower of its directory: the same open, no lock, nothing written. -/
def openFollower (dir : System.FilePath) (keys : Keys) (c : Cadence) (world : Stream W)
    (mark : W → Nat × ByteArray) (origin : W → ByteArray) (step : W → ByteArray → Except F W) :
    IO (Except (StoreFault F) (Opening W)) := do
  openAt dir keys c world mark origin step (← File.open (segmentPath dir) .read)

/-- Create a Store holding `w₀` under `key`: the key, then `genesisImage`'s segment (its origin
frame), its empty `index.log` and base, each durable before the next (`Store.layout`'s order). Refuses a directory that already holds any of
them; a genesis that crashed part way leaves such a directory, which opens `noBase` and is
removed by the operator. -/
def genesis (dir : System.FilePath) (key : Digest) (keys : Keys) (c : Cadence) (world : Stream W)
    (mark : W → Nat × ByteArray) (w₀ : W) : IO (Except (StoreFault F) Unit) := do
  for p in [keyPath dir, segmentPath dir, indexPath dir, basePath dir, baseTmpPath dir] do
    if ← p.pathExists then return .error .exists
  match genesisImage keys c world mark w₀ with
  | .error f => return .error (.seal f)
  | .ok img =>
    IO.FS.createDirAll dir
    writeNew (keyPath dir) key.bytes
    writeNew (segmentPath dir) img.segment
    writeNew (indexPath dir) img.index
    syncDir dir.toString
    installBase dir img.base
    return .ok ()

end Nanodregg.Host
