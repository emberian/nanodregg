/-
# Kernel.Bounds — the static bound on everything a Turn and a Cell may carry

One table. `World.admit` checks a Turn against it before anything else and refuses by the
`Bound` that was exceeded. Rust consumers get these numbers generated from this file, never
hand-copied (law 2).
-/
namespace Nanodregg.Kernel

/-- The name of each bound, carried by `Reject.overBound` on the wire. -/
inductive Bound
  | touches | opsPerWrite | creates | nullifiers
  | event | slotsPerCell | slotKey | valueBytes | window | weight
  deriving DecidableEq, Repr

namespace Bounds

/-- Cells a turn observes (each read, written or retired cell once). -/
def touchesMax : Nat := 512
def opsPerWriteMax : Nat := 256
def createsMax : Nat := 64
def nullifiersMax : Nat := 64
def eventBytesMax : Nat := 65536
def slotsPerCellMax : Nat := 1024
/-- Slot keys are below `2^32`, so they encode in four bytes. -/
def slotKeyLimit : Nat := 4294967296
def valueBytesMax : Nat := 65536
/-- The widest validity window, in heights. Bounds how long a transaction id must be remembered. -/
def windowMax : Nat := 1024
/-- The most one turn may weigh (its charge: log record plus World growth). The per-field bounds
alone allow a turn of ~8.6 GB (64 born cells of 1024 slots of 64 KiB, and as much again in
writes); this is the aggregate bound HOST budgets a frame and a batch by. Four events' worth: a
turn's effect restates its call (the event) about once, and observes up to `touchesMax` cells. -/
def weightMax : Nat := 4 * eventBytesMax

end Bounds
end Nanodregg.Kernel
