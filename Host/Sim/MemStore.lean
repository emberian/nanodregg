/-
# Host.Sim.MemStore — an in-memory disk for the loop, with the crash plants

`synced` is what survived the last successful `sync`; `pending` is appended since. A crash keeps
`synced` plus any prefix of `pending` (`crashImage cut`). The plants are a property of this disk,
not code in the loop: `failSyncAt n` makes the n-th sync throw (the loop must answer the batch
`uncertain` and stop), and `crashImage` / `flipByte` produce the bytes `recover` must judge.
-/
import Host.Loop

namespace Nanodregg.Host.Sim

structure Disk where
  synced : ByteArray := ByteArray.empty
  pending : ByteArray := ByteArray.empty
  syncs : Nat := 0

/-- A store over a disk reference; `failSyncAt n`: the `n`-th sync (0-based) fails with EIO. -/
def memStore (disk : IO.Ref Disk) (failSyncAt : Option Nat) : Store where
  append bytes := disk.modify fun d => { d with pending := d.pending ++ bytes }
  sync := do
    let d ← disk.get
    if failSyncAt = some d.syncs then
      disk.set { d with syncs := d.syncs + 1 }
      throw (IO.userError "plant: fsync EIO")
    disk.set { synced := d.synced ++ d.pending, pending := ByteArray.empty, syncs := d.syncs + 1 }

/-- What a crash leaves: the synced bytes and the first `cut` unsynced ones. -/
def crashImage (d : Disk) (cut : Nat) : ByteArray :=
  d.synced ++ d.pending.extract 0 cut

/-- Flip one byte (xor 0x01) at `i`; out of range leaves the bytes unchanged. -/
def flipByte (b : ByteArray) (i : Nat) : ByteArray :=
  if h : i < b.size then b.set i (b[i] ^^^ 1) h else b

/-- A port that serves a fixed list of frames; `split` decides, per frame after the first of a
batch, whether it is already queued (the seeded batch boundaries). -/
def scriptPort (frames : IO.Ref (List Frame)) (split : IO.Ref (List Bool))
    (sent : IO.Ref (Array Reply)) : Port where
  recv := do
    match ← frames.get with
    | [] => pure none
    | f :: rest => frames.set rest; pure (some f)
  poll := do
    let queued ← match ← split.get with
      | [] => pure true
      | b :: rest => split.set rest; pure b
    if !queued then return none
    match ← frames.get with
    | [] => pure none
    | f :: rest => frames.set rest; pure (some f)
  send r := sent.modify (·.push r)

end Nanodregg.Host.Sim
