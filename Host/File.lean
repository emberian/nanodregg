/-
# Host.File — the Store's physical IO (`Host/c/file.c`)

Nine POSIX calls behind an opaque handle; the descriptor closes when the handle is freed.
Every failure is an `IO` error naming the call and errno, and nothing retries: the loop answers
`uncertain` and stops (HOST-4). On Darwin `sync` is `F_FULLFSYNC` and fails rather than falling
back to a weaker `fsync`.

Linked into the `host` executable only; the interpreter (and so the simulation) never calls
these: it drives the loop over `Host.Sim.MemStore`.
-/
import Host.Loop

namespace Nanodregg.Host

opaque FilePointed : NonemptyType
/-- An open file descriptor. -/
def File : Type := FilePointed.type
instance : Nonempty File := FilePointed.property

/-- How a file is opened. -/
inductive OpenMode where
  | read
  /-- append, created 0600 if absent -/
  | append
  /-- write, created 0600, refusing an existing file -/
  | createNew

def OpenMode.code : OpenMode → UInt8
  | .read => 0
  | .append => 1
  | .createNew => 2

@[extern "nd_file_open"] opaque File.openRaw (path : @& String) (mode : UInt8) : IO File
@[extern "nd_file_write_all"] opaque File.writeAll (f : @& File) (bytes : @& ByteArray) : IO Unit
@[extern "nd_file_sync"] opaque File.sync (f : @& File) : IO Unit
@[extern "nd_file_size"] opaque File.size (f : @& File) : IO UInt64
@[extern "nd_file_read_at"] opaque File.readAt (f : @& File) (off : UInt64) (len : USize) : IO ByteArray
@[extern "nd_file_truncate"] opaque File.truncate (f : @& File) (len : UInt64) : IO Unit
@[extern "nd_file_try_lock"] opaque File.tryLock (f : @& File) : IO Bool
@[extern "nd_dir_sync"] opaque syncDir (path : @& String) : IO Unit

def File.open (path : System.FilePath) (mode : OpenMode) : IO File :=
  File.openRaw path.toString mode.code

/-- The loop's store over an open segment. -/
def fileStore (f : File) : Store where
  append := f.writeAll
  sync := f.sync

end Nanodregg.Host
