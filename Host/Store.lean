/-
# Host.Store — a Store directory: genesis, the writer, the follower, and the files on disk

    STORE/key            32 bytes, 0600: the integrity-at-rest key (HOST-16); written once by genesis;
                         its read handle is flock'd: THE writer lock (HOST-64)
    STORE/seg.<o>.log    one slice of the segment from logical offset o, opened by its checkpoint
                         header (Host.Segment): one file per seal start; the newest is appended to
    STORE/index.<k0>.log fixed-width MAC'd entries k0, k0+1, … (one per record before the newest
                         base, each tagged with its position: HOST-30, HOST-33); the base names k0
    STORE/base.world     the newest sealed base (Host.Base); replaced atomically through base.tmp

(The layout as data, with the backup copy order: `Host.Store.layout`, `Host.Store.backupOrder`.)

The segment is ONE logical byte sequence (Host.Segment): every base, entry and page names a logical
offset, and `Segs` reads logical ranges across the files. A base sits at the start of its own file
(`seg.<base offset>.log`), so the open reads that file's header, the file, its successors (the tail),
and at most the file before it (the base's last indexed record, HOST-63): O(1) files.

The lock is the key file's read handle, flock'd for the writer's life (`Writer.lock`, kept by
`Writer.hold`): the append handle moves to each new file, the lock does not.

`openAt` is the one open: the base (bounded before it is read), the files its offset names, and
`openWith` over logical readers. The writer then truncates the torn tail (in the newest file only:
a new file is started only after a synced commit) and syncs before anything is appended; a follower
writes nothing and reads a torn tail as "not yet written". Physical IO is `Host.File`
(Host/c/file.c), so this module runs only in a linked executable.

RETENTION (HOST-64, KERNEL-44 Part 2). A writer given `--retain N` (N ≥ 2) keeps the N newest
segment files: at each base install it names the oldest kept file (`retainedFrom`) and the first kept
index entry (`indexFrom`), rewrites the kept entries to `index.<indexFrom>.log` BEFORE the base naming
it is installed, and unlinks what it dropped after. A crash leaves surplus files, never a missing one;
a writer with a finite retention removes the surplus at open. Without `--retain` nothing is dropped.
-/
import Host.File
import Host.Open

namespace Nanodregg.Host

open Nanodregg.Codec (Digest Stream)

def StorePart.path (dir : System.FilePath) (f : StorePart) : System.FilePath := dir / f.name

def keyPath (dir : System.FilePath) : System.FilePath := StorePart.key.path dir
def basePath (dir : System.FilePath) : System.FilePath := StorePart.base.path dir
def segPath (dir : System.FilePath) (o : Nat) : System.FilePath := (StorePart.segment o).path dir
def indexPathAt (dir : System.FilePath) (k0 : Nat) : System.FilePath := (StorePart.index k0).path dir
def baseTmpPath (dir : System.FilePath) : System.FilePath := dir / "base.tmp"
def segTmpPath (dir : System.FilePath) : System.FilePath := dir / "seg.tmp"
def indexTmpPath (dir : System.FilePath) : System.FilePath := dir / "index.tmp"

/-- The first of `files` absent from `dir`, or none. Every open runs it before its first handle
(HOST-35), so a missing Store file is refused `missing` by name, never an IO exception from the
open, and never re-created (the append mode does not create, `Host/c/file.c`). A file removed
between this check and its open is the open's IO error: `io` from `host`, never unnamed. -/
def missingOf {F : Type} (dir : System.FilePath) : List StorePart → IO (Option (StoreFault F))
  | [] => pure none
  | f :: fs => do
    if ← (f.path dir).pathExists then missingOf dir fs else pure (some (.missing f))

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
  -- a STORE directory without its key file is refused `missing key` (law 7), never an IO exception
  -- from the open below; an absent STORE path stays `io` (the path is wrong, store-plants' missing-store)
  if ← dir.pathExists then
    if let some f ← missingOf dir [.key] then return .error f
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

/-! ## The segment files -/

/-- Why a segment file is not read (each refuses by name: `missing seg.<o>.log`, `checkpointCorrupt`,
`foreignSegment`). -/
inductive SegFault where
  | missing (start : Nat)
  /-- the file is shorter than a header, or its header does not verify under the Store's key -/
  | corrupt (start : Nat)
  /-- the header verifies but names another position or predecessor than the file's place -/
  | foreign (start : Nat)
  /-- the header verifies but states another Store's origin than the file it follows or precedes:
  one of the two is another Store's (HOST-25's name; the open checks the base's own against its World) -/
  | foreignOrigin (start : Nat)
  /-- the file before `next` ends at `stop`, short of `next` (a copy cut short): the segment is
  shorter than the offset the next file starts at -/
  | short (stop next : Nat)

def SegFault.store {F : Type} : SegFault → StoreFault F
  | .missing o => .missing (.segment o)
  | .corrupt _ => .base .checkpointCorrupt
  | .foreign _ => .base .foreignSegment
  | .foreignOrigin _ => .base .foreignOrigin
  | .short stop next => .base (.segmentShort stop next)

/-- The header of `seg.<o>.log`, verified and naming `o`, with the file's body size. -/
def readHeader (dir : System.FilePath) (keys : Keys) (o : Nat) :
    IO (Except SegFault (Header × ByteArray × Nat)) := do
  unless ← (segPath dir o).pathExists do return .error (.missing o)
  let f ← File.open (segPath dir o) .read
  let size := (← f.size).toNat
  if size < headerBytes keys then return .error (.corrupt o)
  let hb ← f.readAt 0 (headerBytes keys).toUSize
  match Header.read keys hb with
  | none => return .error (.corrupt o)
  | some h => if h.start = o then return .ok (h, hb, size - headerBytes keys) else return .error (.foreign o)

/-- The logical segment of one Store, read across its files: `starts` are the known files' starts,
ascending and contiguous (each file's body ends where the next starts), never below `floor` (the
oldest retained file). The newest known file may still grow; a file after it is found by name
(`seg.<end>.log`) when a read or `size` passes its end. -/
structure Segs where
  dir : System.FilePath
  keys : Keys
  origin : ByteArray
  starts : IO.Ref (Array Nat)
  floor : Nat

/-- The body size of a known file. -/
def Segs.body (s : Segs) (o : Nat) : IO Nat := do
  let f ← File.open (segPath s.dir o) .read
  return (← f.size).toNat - headerBytes s.keys

/-- Learn every file after the newest known one; the logical end of the segment. A successor's
header must verify, name its own start, the Store's origin and its predecessor (`foreignSegment`). -/
def Segs.size (s : Segs) : IO (Except SegFault Nat) := do
  let mut starts ← s.starts.get
  let some last := starts.back? | return .ok s.floor
  let mut cur := last
  let mut stop := cur + (← s.body cur)
  for _ in [0:1 <<< 20] do
    -- an empty file has no successor: a rotation at its start is none (`fileCheckpoint.rotate`)
    if stop = cur then break
    unless ← (segPath s.dir stop).pathExists do break
    match ← readHeader s.dir s.keys stop with
    | .error e => return .error e
    | .ok (h, _, body) =>
      if h.prev ≠ cur then return .error (.foreign stop)
      if h.origin ≠ s.origin then return .error (.foreignOrigin stop)
      starts := starts.push stop
      cur := stop
      stop := stop + body
  s.starts.set starts
  return .ok stop

/-- Learn the files before the oldest known one, down to the one holding logical offset `off`, never
below `floor`. Each header must name its successor's `prev` (`foreignSegment`). -/
def Segs.cover (s : Segs) (off : Nat) : IO (Except SegFault Unit) := do
  let mut starts ← s.starts.get
  for _ in [0:1 <<< 20] do
    let some first := starts[0]? | break
    if first ≤ off ∨ first ≤ s.floor then break
    match ← readHeader s.dir s.keys first with
    | .error e => return .error e
    | .ok (h, _, _) =>
      if first ≤ h.prev then break
      if h.prev < s.floor then break
      match ← readHeader s.dir s.keys h.prev with
      | .error e => return .error e
      | .ok (hp, _, body) =>
        if hp.start + body < first then return .error (.short (hp.start + body) first)
        if hp.start + body ≠ first then return .error (.foreign h.prev)
        if hp.origin ≠ s.origin then return .error (.foreignOrigin h.prev)
        starts := #[h.prev] ++ starts
  s.starts.set starts
  return .ok ()

/-- `len` logical bytes from `off` (fewer at the segment's end): the files covering `off` learned
(`cover`, `size`, which check each header and the contiguity), then `segRead` over them, a file's
body read past its header. The 32 bytes before the oldest retained file are served from that file's
header tag (`segRead`). `Host.Proofs.Segs.segRead_logical`: over files that are slices of the logical
segment, this is its extract. -/
def Segs.read (s : Segs) (off len : Nat) : IO (Except SegFault ByteArray) := do
  if let .error e ← s.cover off then return .error e
  if let .error e ← s.size then return .error e
  let starts ← s.starts.get
  segRead (fun o => return (← readHeader s.dir s.keys o).map (·.1.tag.bytes))
    (fun o p n => do
      let f ← File.open (segPath s.dir o) .read
      f.readAt (headerBytes s.keys + p).toUInt64 n.toUSize)
    starts.toList off len

def SegFault.text : SegFault → String
  | .missing o => s!"missing seg.{o}.log"
  | .corrupt _ => "checkpointCorrupt"
  | .foreign _ => "foreignSegment"
  | .foreignOrigin _ => "foreignOrigin"
  | .short _ _ => "segmentShort"

/-- What a `log` page reads (HOST-64): the files the newest base keeps, as the writer's `kept`
names them (`retainedFrom`, `indexFrom`), and the starts the pages have learned (shared across pages;
a drop forgets the ones below the new `retainedFrom`). -/
structure PageFiles where
  dir : System.FilePath
  keys : Keys
  origin : ByteArray
  kept : IO.Ref (Nat × Nat)
  starts : IO.Ref (Array Nat)

/-- The first kept index entry and the logical readers of the segment and the index for one page.
A segment file the page needs and does not find is an IO error naming it (`missing seg.<o>.log`),
which the loop answers `pageIo` (HOST-48); `host check` refuses it by name. -/
def PageFiles.readers (p : PageFiles) :
    IO (Nat × (Nat → Nat → IO ByteArray) × (Nat → Nat → IO ByteArray)) := do
  let (rf, k0) ← p.kept.get
  p.starts.modify fun a => let a := a.filter (rf ≤ ·); if a.isEmpty then #[rf] else a
  let segs : Segs := ⟨p.dir, p.keys, p.origin, p.starts, rf⟩
  let idx ← File.open (indexPathAt p.dir k0) .read
  let eb := entryBytes p.keys
  return (k0,
    fun off len => do
      match ← segs.read off len with
      | .ok b => pure b
      | .error e => throw (IO.userError e.text),
    fun off len => do
      if off < k0 * eb then return ByteArray.empty
      idx.readAt (off - k0 * eb).toUInt64 len.toUSize)

/-- What an open learned of the files: the logical segment reader, the newest file's start, and
what the base keeps (`retainedFrom`, `indexFrom`). -/
structure Files where
  segs : Segs
  newest : Nat
  retainedFrom : Nat
  indexFrom : Nat

/-- The one open (writer and follower) over a Store directory: `base.world` present (`missing`
otherwise, before any handle opens); the base's file and index file present; then `openWith` over
the base's header and logical readers of the segment and the index. -/
def openAt (dir : System.FilePath) (keys : Keys) (c : Cadence) (world : Stream W)
    (mark : W → Nat × ByteArray) (origin : W → ByteArray) (step : W → ByteArray → Except F W) :
    IO (Except (StoreFault F) (Opening W × Files)) := do
  if let some f ← missingOf dir [.base] then return .error f
  match ← readBounded (basePath dir) (Log.frameMax c.baseRecordMax) (fun n => .base (.baseTooLarge n)) with
  | .error e => return .error e
  | .ok file =>
    -- an unreadable trailer is not a base: the open refuses it by Base.read's own name
    let (o, rf, k0) := (Base.peek file).getD (0, 0, 0)
    if let some f ← missingOf dir [.segment o, .index k0] then return .error f
    let hb ← match ← readHeader dir keys o with
      | .ok (_, hb, _) => pure hb
      | .error (.missing o) => return .error (.missing (.segment o))
      | .error _ =>
        -- the bytes as they are: `openWith`'s header check names the fault
        let f ← File.open (segPath dir o) .read
        f.readAt 0 (headerBytes keys).toUSize
    let segs : Segs := ⟨dir, keys, (Header.read keys hb).map (·.origin) |>.getD ByteArray.empty,
      ← IO.mkRef #[o], rf⟩
    let size ← match ← segs.size with
      | .ok n => pure n
      | .error e => return .error e.store
    let index ← File.open (indexPathAt dir k0) .read
    let eb := entryBytes keys
    let indexSize := k0 * eb + (← index.size).toNat
    let r ← openWith keys c world mark origin step file hb size indexSize
      (fun off len => do
        if off < k0 * eb then return .ok ByteArray.empty
        return .ok (← index.readAt (off - k0 * eb).toUInt64 len.toUSize))
      fun off len => do
        match ← segs.read off len with
        | .ok b => return .ok b
        | .error e => return .error e.store
    match r with
    | .error e => return .error e
    | .ok op =>
      let newest := (← segs.starts.get).back?.getD o
      return .ok (op, ⟨segs, newest, rf, k0⟩)

/-- The loop's state as an open leaves it. -/
def Opening.resident (o : Opening W) : Resident W :=
  { world := o.opened.world, pos := o.pos, sealed := o.sealed, index := o.index }

/-- The reopen of a fuel restart (`Host.restarts`): the one open, through fresh read handles (the
writer's lock stays held). A torn tail here is bytes the loop never synced, a divergence, never
something to truncate. -/
def reopenAt (dir : System.FilePath) (keys : Keys) (c : Cadence) (world : Stream W)
    (mark : W → Nat × ByteArray) (origin : W → ByteArray) (step : W → ByteArray → Except F W) : IO (Except Exit (Resident W)) := do
  match ← openAt dir keys c world mark origin step with
  | .error f => return .error (.reopenFailed f.text)
  | .ok (o, _) => return if o.opened.torn = 0 then .ok o.resident else .error .reopenDiverged

/-- An open writer: the lock, the append handle of the newest segment file and its start, the
index append handle, what the newest base keeps (`retainedFrom`, `indexFrom`), the retention, and
the loop's state. The handles move (`Checkpoint.rotate`, a drop); the lock does not. -/
structure Writer (W : Type) where
  lock : File
  segment : IO.Ref File
  newest : IO.Ref Nat
  index : IO.Ref File
  kept : IO.Ref (Nat × Nat)
  retain : Retain
  opening : Opening W

/-- Keep the writer's lock to here: the lock's handle lives as long as a later use of it. -/
def Writer.hold (wr : Writer W) : IO Unit := do
  let _ ← wr.lock.tryLock

/-- Unlink every Store file outside what the base keeps: segment files before `retainedFrom`, index
files other than `indexFrom`'s, and stale `seg.tmp` / `index.tmp`. Only a writer with a finite
retention runs it (only a drop leaves such files: a crash between the base install and the unlinks). -/
def removeSurplus (dir : System.FilePath) (rf k0 : Nat) : IO Unit := do
  for e in ← dir.readDir do
    let n := e.fileName
    let surplus : Bool :=
      n == "seg.tmp" || n == "index.tmp" ||
      (match n.splitOn "." with
        | ["seg", x, "log"] => match x.toNat? with | some v => decide (v < rf) | none => false
        | ["index", x, "log"] => match x.toNat? with | some v => v != k0 | none => false
        | _ => false)
    if surplus then IO.FS.removeFile e.path
  syncDir dir.toString

/-- Open the Store as its one writer: lock the key, open, truncate the torn tail (in the newest file)
and any orphan index entries (bytes past the entries the base counts: never a byte of one it counts,
`Opening.orphan`), sync. A stale `base.tmp` (a crash mid-seal) is never read; the next seal replaces
it. Every file the open reads is checked present first (`missing`), and the append mode never creates
one: the writer writes only into files genesis, a rotation or a drop made (HOST-35). -/
def openWriter (dir : System.FilePath) (keys : Keys) (c : Cadence) (world : Stream W)
    (mark : W → Nat × ByteArray) (origin : W → ByteArray) (step : W → ByteArray → Except F W)
    (retain : Retain := none) : IO (Except (StoreFault F) (Writer W)) := do
  if let some f ← missingOf dir [.key, .base] then return .error f
  let lock ← File.open (keyPath dir) .read
  unless ← lock.tryLock do return .error .locked
  match ← openAt dir keys c world mark origin step with
  | .error e => return .error e
  | .ok (o, fs) =>
    let segment ← File.open (segPath dir fs.newest) .append
    if 0 < o.opened.torn then
      -- a torn tail is only ever in the newest file: a file is started after a synced commit
      if o.pos.offset < fs.newest then return .error (.log (.corrupt o.pos.offset))
      segment.truncate (headerBytes keys + (o.pos.offset - fs.newest)).toUInt64
      segment.sync
    let index ← File.open (indexPathAt dir fs.indexFrom) .append
    if 0 < o.orphan then
      index.truncate ((o.sealed.index.count - fs.indexFrom) * entryBytes keys).toUInt64
      index.sync
    if retain.isSome then removeSurplus dir fs.retainedFrom fs.indexFrom
    return .ok ⟨lock, ← IO.mkRef segment, ← IO.mkRef fs.newest, ← IO.mkRef index,
      ← IO.mkRef (fs.retainedFrom, fs.indexFrom), retain, o⟩

/-- Open the Store as a follower of its directory: the same open, no lock, nothing written. -/
def openFollower (dir : System.FilePath) (keys : Keys) (c : Cadence) (world : Stream W)
    (mark : W → Nat × ByteArray) (origin : W → ByteArray) (step : W → ByteArray → Except F W) :
    IO (Except (StoreFault F) (Opening W)) := do
  return (← openAt dir keys c world mark origin step).map Prod.fst

/-- The loop's store over the writer's newest segment file. -/
def fileStore (wr : Writer W) : Store where
  append bytes := do (← wr.segment.get).writeAll bytes
  sync := do (← wr.segment.get).sync

/-- The files from `newest` back to `floor` (walking each header's `prev`), newest first. -/
def filesBack (dir : System.FilePath) (keys : Keys) (newest floor : Nat) :
    IO (Except SegFault (List (Nat × Header))) := do
  let mut acc : Array (Nat × Header) := #[]
  let mut cur := newest
  for _ in [0:1 <<< 20] do
    match ← readHeader dir keys cur with
    | .error e => return .error e
    | .ok (h, _, _) =>
      acc := acc.push (cur, h)
      if cur ≤ floor ∨ cur ≤ h.prev then break
      cur := h.prev
  return .ok acc.toList

/-- What a drop keeping the `n` newest files (ending with `newest`, none below `floor`) keeps and
unlinks: the oldest kept file's start, its header's index count (the first kept entry), and the
starts of the files before it. -/
def keepFrom (dir : System.FilePath) (keys : Keys) (newest floor n : Nat) :
    IO (Except SegFault (Nat × Nat × List Nat)) := do
  match ← filesBack dir keys newest floor with
  | .error e => return .error e
  | .ok fs =>
    let kept := fs.take n
    match kept.getLast? with
    | none => return .error (.missing newest)
    | some (o, h) => return .ok (o, h.indexCount, (fs.drop n).map Prod.fst)

/-- The base sealer over a Store directory (`Base.seal`), with the writer's handles.

`rotate` starts the file a seal at `pos` will name (HOST-64): its header (the position, the World's
step count and chain, the entries before it, the newest file before it) written to `seg.tmp`, synced,
renamed to `seg.<pos>.log`, the directory synced, and the append handle moved to it. When the
newest file already starts at `pos` (a seal at the position of a seal that never installed, or of the
base the writer opened at) nothing is written, and that file is reused only if its header passes
`headerFault` at the place the base will name: else `positionUnfit` (HOST-64 F6;
`Host.Proofs.Seal.sealed_opens_reused` states the reused header then opens).

`write` checks `index.<indexFrom>.log` ends exactly where the entries the newest base counts end
(`indexMoved`), and both encodings, before anything is written. Keeping everything, it appends the
entries since the last base and syncs them, then installs the base counting them (HOST-30, HOST-33).
With `retain = some n` it first finds the `n` newest files (`keepFrom`); when that moves the first kept
index entry, the kept entries and the new ones are written to `index.<k0'>.log` (through `index.tmp`,
synced, renamed, directory synced) BEFORE the base naming `k0'` is installed; after the install the
dropped segment files and the old index are unlinked. A crash leaves the old base with every file it
names, or the new base with every file it names and surplus files a finite-retention writer removes
at open. Never silent (D8): every seal writes one `STATUS seal` line to stderr, installed or refused
by name. -/
def fileCheckpoint (dir : System.FilePath) (keys : Keys) (c : Cadence) (world : Stream W)
    (mark : W → Nat × ByteArray) (origin : W → ByteArray) (wr : Writer W) (async : Bool := true) : Checkpoint W where
  async
  rotate w pos count := do
    let newest ← wr.newest.get
    if newest = pos.offset then
      -- the newest file already starts here (a seal at the position of one that never installed,
      -- or of the base the writer opened at): it is the file this seal names only if its header
      -- passes the open's own check at the place the base will name (`headerFault`, HOST-64 F6);
      -- otherwise the seal refuses `positionUnfit` before anything is written
      try
        let f ← File.open (segPath dir pos.offset) .read
        let hb ← f.readAt 0 (headerBytes keys).toUSize
        match headerFault keys hb (origin w) pos.offset pos.tag (mark w) count with
        | none => return .ok ()
        | some f =>
          -- the operator's distinction from a position past 2^64: the header's own fault, by name
          IO.eprintln s!"STATUS rotate offset={pos.offset} reused=seg.{pos.offset}.log refused=positionUnfit header={f.name}"
          return .error (.positionUnfit pos.offset)
      catch e => return .error (.io (toString e))
    let h := Header.at pos (mark w) count newest (origin w)
    unless h.fits keys.chainBytes do return .error (.positionUnfit pos.offset)
    try
      if ← (segTmpPath dir).pathExists then IO.FS.removeFile (segTmpPath dir)
      if ← (segPath dir pos.offset).pathExists then return .error (.io s!"seg.{pos.offset}.log exists")
      writeNew (segTmpPath dir) (Header.bytes keys h)
      IO.FS.rename (segTmpPath dir) (segPath dir pos.offset)
      syncDir dir.toString
      wr.segment.set (← File.open (segPath dir pos.offset) .append)
      wr.newest.set pos.offset
      return .ok ()
    catch e => return .error (.io (toString e))
  write w seg entries ipos := do
    let at_ := s!"height={(mark w).1} offset={seg.offset} entries={entries.size} index_count={ipos.count}"
    let (rf, k0) ← wr.kept.get
    let eb := entryBytes keys
    let (rf', k0', dropped) ← match wr.retain with
      | none => pure (rf, k0, [])
      | some n =>
        match ← keepFrom dir keys seg.offset rf n with
        | .ok x => pure x
        | .error _ =>
          IO.eprintln s!"STATUS seal {at_} refused=checkpointCorrupt"
          return .error (.io "checkpointCorrupt")
    let index ← wr.index.get
    match Base.seal (keys.forStore (origin w)) c world w seg ipos entries (k0 * eb + (← index.size).toNat)
        ⟨rf', k0'⟩ with
    | .error f =>
      IO.eprintln s!"STATUS seal {at_} refused={f.name}"
      return .error f
    | .ok (page, ipos', bytes) =>
      -- a seal never re-creates a base.world removed under the writer (the rename would): it
      -- refuses, and the restart's open refuses `missing base.world` (HOST-35)
      if let some f ← (missingOf dir [.base] : IO (Option (StoreFault Unit))) then
        IO.eprintln s!"STATUS seal {at_} refused=io"
        return .error (.io f.text)
      try
        if k0' = k0 then
          unless page.isEmpty do
            index.writeAll page
            index.sync
        else
          let old ← (← File.open (indexPathAt dir k0) .read).readAt ((k0' - k0) * eb).toUInt64
            ((ipos.count - k0') * eb).toUSize
          if old.size ≠ (ipos.count - k0') * eb then
            IO.eprintln s!"STATUS seal {at_} refused=io"
            return .error (.io "index short at drop")
          if ← (indexTmpPath dir).pathExists then IO.FS.removeFile (indexTmpPath dir)
          if ← (indexPathAt dir k0').pathExists then IO.FS.removeFile (indexPathAt dir k0')
          writeNew (indexTmpPath dir) (old ++ page)
          IO.FS.rename (indexTmpPath dir) (indexPathAt dir k0')
          syncDir dir.toString
        installBase dir bytes
        if k0' ≠ k0 then
          wr.index.set (← File.open (indexPathAt dir k0') .append)
          IO.FS.removeFile (indexPathAt dir k0)
        for o in dropped do
          if ← (segPath dir o).pathExists then IO.FS.removeFile (segPath dir o)
        unless dropped.isEmpty && k0' = k0 do syncDir dir.toString
        wr.kept.set (rf', k0')
        IO.eprintln s!"STATUS seal {at_} base_bytes={bytes.size} world_bytes={world.size w} entry_bytes={page.size} retained_from_offset={rf'} index_from={k0'} dropped={dropped.length}"
        return .ok (world.size w, keys.worldDigest (worldBytesOf bytes (world.size w)), ipos')
      catch e =>
        IO.eprintln s!"STATUS seal {at_} refused=io"
        return .error (.io (toString e))

/-- Create a Store holding `w₀` under `key`: the key, then `genesisImage`'s files (the origin
frame's `seg.0.log`, the base's empty `seg.<o>.log`, the empty `index.0.log`) and base, each durable
before the next (`Store.layout`'s order). Refuses a directory that already holds any of them; a
genesis that crashed part way leaves such a directory, which opens `missing` (the first file it
never wrote) and is removed by the operator. -/
def genesis (dir : System.FilePath) (key : Digest) (keys : Keys) (c : Cadence) (world : Stream W)
    (mark : W → Nat × ByteArray) (w₀ : W) : IO (Except (StoreFault F) Unit) := do
  match genesisImage keys c world mark w₀ with
  | .error f => return .error (.seal f)
  | .ok img =>
    for p in [keyPath dir, segPath dir 0, segPath dir img.segment.size, indexPathAt dir 0, basePath dir,
        baseTmpPath dir] do
      if ← p.pathExists then return .error .exists
    IO.FS.createDirAll dir
    writeNew (keyPath dir) key.bytes
    writeNew (segPath dir 0) (img.header0 ++ img.segment)
    writeNew (segPath dir img.segment.size) img.header
    writeNew (indexPathAt dir 0) img.index
    syncDir dir.toString
    installBase dir img.base
    return .ok ()

end Nanodregg.Host
