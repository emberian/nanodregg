/-
# Host.Sim.Files — a Store directory's files as the plants handle them (HOST-64)

The segment is one logical byte sequence held by the files `seg.<o>.log` (`Host.Segment`). The
plants (host-file-sim at the toy World, OPS's store-plants through the real `host`) copy, cut,
splice and flip the LOGICAL segment, exactly the bytes `seg.log` held before HOST-64, and these
helpers map it onto the files: each file keeps its checkpoint header (`hdr` bytes,
`Host.headerBytes`) and holds its slice. Nothing here is on a Store's serving path.
-/
import Host.Store

namespace Nanodregg.Host.Sim

/-- The segment files of a Store directory, `(start, path)`, ascending by start. -/
def segFiles (dir : System.FilePath) : IO (Array (Nat × System.FilePath)) := do
  let mut out : Array (Nat × System.FilePath) := #[]
  for e in ← dir.readDir do
    match e.fileName.splitOn "." with
    | ["seg", x, "log"] => if let some o := x.toNat? then out := out.push (o, e.path)
    | _ => pure ()
  return out.qsort (fun a b => a.1 < b.1)

/-- The newest segment file: the one the writer appends to. -/
def newestSeg (dir : System.FilePath) : IO System.FilePath := do
  match (← segFiles dir).back? with
  | some (_, p) => pure p
  | none => throw (IO.userError s!"no segment file in {dir}")

/-- The Store's one index file, `index.<k0>.log`. -/
def indexFile (dir : System.FilePath) : IO System.FilePath := do
  for e in ← dir.readDir do
    match e.fileName.splitOn "." with
    | ["index", x, "log"] => if x.toNat?.isSome then return e.path
    | _ => pure ()
  throw (IO.userError s!"no index file in {dir}")

/-- The logical segment from the oldest file's start: each file's bytes after its header, in order
(a Store that keeps everything: exactly the bytes `seg.log` held before HOST-64). -/
def logical (dir : System.FilePath) (hdr : Nat) : IO ByteArray := do
  let mut out := ByteArray.empty
  for (_, p) in ← segFiles dir do
    let b ← IO.FS.readBinFile p
    out := out ++ b.extract hdr b.size
  return out

/-- The logical end of the segment: the newest file's start plus its body. -/
def logicalSize (dir : System.FilePath) (hdr : Nat) : IO Nat := do
  match (← segFiles dir).back? with
  | some (o, p) => return o + ((← IO.FS.readBinFile p).size - hdr)
  | none => return 0

/-- Rewrite the files of `dir` to hold the logical segment `bytes` (from the oldest file's start):
each file keeps its header and holds its slice (empty past the end of `bytes`). -/
def writeLogical (dir : System.FilePath) (hdr : Nat) (bytes : ByteArray) : IO Unit := do
  let fs ← segFiles dir
  let first := (fs[0]?.map (·.1)).getD 0
  for i in [0:fs.size] do
    let (o, p) := fs[i]!
    let stop := (fs[i + 1]?.map (·.1)).getD (first + bytes.size)
    let h := (← IO.FS.readBinFile p).extract 0 hdr
    IO.FS.writeBinFile p (h ++ bytes.extract (o - first) (stop - first))

/-- Copy every segment file of `src` into `dst` (by name), oldest first. -/
def copySegs (src dst : System.FilePath) : IO Unit := do
  for (_, p) in ← segFiles src do
    IO.FS.writeBinFile (dst / (p.fileName.getD "")) (← IO.FS.readBinFile p)

/-- Remove every segment file of `dir`. -/
def removeSegs (dir : System.FilePath) : IO Unit := do
  for (_, p) in ← segFiles dir do IO.FS.removeFile p

/-- A backup of `src` into `dst` in `Store.backupOrder`: the key, the base, the index file, then the
segment files oldest first. -/
def copyStore (src dst : System.FilePath) : IO Unit := do
  IO.FS.createDirAll dst
  IO.FS.writeBinFile (keyPath dst) (← IO.FS.readBinFile (keyPath src))
  IO.FS.writeBinFile (basePath dst) (← IO.FS.readBinFile (basePath src))
  let ix ← indexFile src
  IO.FS.writeBinFile (dst / (ix.fileName.getD "")) (← IO.FS.readBinFile ix)
  copySegs src dst

/-- Every Store file of `dir` (transients aside), by name, with its bytes: a snapshot two runs of
the same Store compare. -/
def snapshot (dir : System.FilePath) : IO (List (String × ByteArray)) := do
  let mut out : Array (String × ByteArray) := #[]
  for e in ← dir.readDir do
    unless e.fileName.endsWith ".tmp" do out := out.push (e.fileName, ← IO.FS.readBinFile e.path)
  return (out.qsort (fun a b => a.1 < b.1)).toList

end Nanodregg.Host.Sim
