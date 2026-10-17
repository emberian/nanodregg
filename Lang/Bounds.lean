/-
# Lang.Bounds — the static bounds of the language (law 4)

Every value a program can build is bounded, so one machine step is bounded work: a natural is
below `2^64`, a byte string fits one kernel slot. An arithmetic result outside a bound is a named
fault (`Lang.Fault`), never a wrap and never an unbounded allocation.
-/
import Kernel.Bounds

namespace Nanodregg.Lang.Bounds

/-- Naturals are below `2^64`. -/
def natLimit : Nat := 18446744073709551616

/-- A byte string fits one kernel slot value. -/
def bytesMax : Nat := Kernel.Bounds.valueBytesMax

/-- A digest is at most 32 bytes: the deployed digest is 32, the Sim's 8. Whether bytes of that
size ARE a digest is the World's `digestOf`, asked where an id enters a run (LANG-38). -/
def digestBytesMax : Nat := 32

/-- The machine's stack bound. A consensus constant, not part of a budget: two executors given
different tick budgets agree on every final outcome (`Lang.Proofs.Run.run_agree`) only because
they share this bound. -/
def stackMax : Nat := 4096

end Nanodregg.Lang.Bounds
