/-
# Kernel.Bounds — the static bound on everything a Turn and a Cell may carry

One table. `World.admit` checks a Turn against it before anything else and refuses by the
`Bound` that was exceeded. Rust consumers get these numbers generated from this file, never
hand-copied (law 2).
-/
namespace Nanodregg.Kernel

/-- The name of each bound, carried by `Reject.overBound` on the wire. -/
inductive Bound
  | legs | opsPerLeg | pins | creates | retires | nullifiers
  | event | slotsPerCell | slotKey | valueBytes | window
  deriving DecidableEq, Repr

namespace Bounds

def legsMax : Nat := 256
def opsPerLegMax : Nat := 256
def pinsMax : Nat := 512
def createsMax : Nat := 64
def retiresMax : Nat := 64
def nullifiersMax : Nat := 64
def eventBytesMax : Nat := 65536
def slotsPerCellMax : Nat := 1024
/-- Slot keys are below `2^32`, so they encode in four bytes. -/
def slotKeyLimit : Nat := 4294967296
def valueBytesMax : Nat := 65536
/-- The widest validity window, in heights. Bounds how long a transaction id must be remembered. -/
def windowMax : Nat := 1024

end Bounds
end Nanodregg.Kernel
