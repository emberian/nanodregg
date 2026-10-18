/-
# Host.Bounds — every static bound the Host keeps (law 4)

One table, like `Kernel.Bounds`. A `Cadence` is passed to the loop and to open as a parameter, so
the simulation runs the deployed code with toy numbers (`Host.Sim`) and `host serve` runs it with
`Cadence.deployed`.

HOST-14: the loop seals the whole World into a base when the segment bytes appended since the
newest durable base reach `cadence` (`max sealMinBytes (baseBytes / 4)`), in a Task, off the
loop. Open reads that one base and the segment after it, and that tail is at most `tailMax`: two
cadences (one being sealed in flight, one since) and one frame. The loop cannot append past it
(`Host.Loop.commitBatch` takes the bound as a proof argument), and open refuses a longer tail by
name (`Host.Base.tailRead`).

HOST-22 (as ruled): an open re-verifies nothing. Writer and follower both reopen with
`World.fold` (O(touched) per Turn), so the byte bound is the bound on open work.
-/
import Host.Log
import Codec.Kernel

namespace Nanodregg.Host

/-- How long a tail (`Host.Tail.await`) sleeps between reads that found nothing new, in ms. -/
def tailPollMs : Nat := 50

/-- The most Turns one batch record holds: the loop's batch bound (CODEC's batch codec is bounded by it). -/
def recordTurnsMax : Nat := 64

/-- The width of the shape stamp at the head of a base record (a digest, `Base.shapeStamp`). -/
def stampBytes : Nat := 32

/-! ## The largest batch record, derived (HOST-47)

A record is CODEC's `batch recordTurnsMax digestCodec` (`Host.Record.codec`): a `u32` count, then
at most `recordTurnsMax` pairs of a step and the 32-byte roots digest after it. A step is CODEC's
choice byte and either a Turn, whose bytes are its log weight (`Codec.Kernel.turn_size_logWeight`),
at most its weight, at most `weightMax` once admitted (`Kernel.admit_weight`); or a recorded refusal:
two digests, three `u64`s, and the signed call as `u32` length and at most `callMax` bytes
(`checkRefusedBounds`). `Host.Deployed.recorder_encode_size_le` proves every record the deployed
writer or follower encodes from steps `World.step` took is within `recordBytesDerived`. -/

/-- The deployed digest's width on the wire (`Codec.Deployed.digestCodec`). -/
def digestBytes : Nat := 32

/-- The widest recorded refusal on the wire. -/
def refusedBytesMax : Nat := 2 * digestBytes + 3 * 8 + 4 + Codec.Kernel.callMax

/-- The widest step on the wire: the choice byte and the wider of a Turn and a refusal. -/
def stepBytesMax : Nat := 1 + max Kernel.Bounds.weightMax refusedBytesMax

/-- The largest batch record of steps `World.step` took: 16,779,332 bytes (16 MiB + 2116). -/
def recordBytesDerived : Nat := 4 + recordTurnsMax * (stepBytesMax + digestBytes)

structure Cadence where
  /-- the fewest segment bytes between two seals -/
  sealMinBytes : Nat
  /-- the largest encoded World a base may hold (`Base.SealFault.worldTooLarge` past it) -/
  worldBytesMax : Nat
  /-- the largest batch record a frame may hold -/
  recordBytesMax : Nat

namespace Cadence

/-- Segment bytes between two seals, for a newest durable base of `baseBytes`. Sealing every
quarter of the base's own size amortises to at most four sealed bytes per appended byte, plus the
floor. -/
def cadence (c : Cadence) (baseBytes : Nat) : Nat := max c.sealMinBytes (baseBytes / 4)

/-- The most segment bytes after the newest durable base: one cadence being sealed, one more
while the seal runs, and the frame that crossed. -/
def tailMax (c : Cadence) (baseBytes : Nat) : Nat :=
  2 * c.cadence baseBytes + Log.frameMax c.recordBytesMax

/-- A base record: the shape stamp (`stampBytes`), the World's bytes (bounded by `worldBytesMax`,
`Base.file`), the segment offset (u64) and tag (32) it starts from, and the `index.log` count (u64)
and tag (32) it names. So every base `Base.file` writes is within one base frame
(`Host.Proofs.Genesis.Base.read_file`). -/
def baseRecordMax (c : Cadence) : Nat := c.worldBytesMax + stampBytes + 2 * (8 + Log.tagBytes)

/-- `host serve`'s numbers. The base: `worldBytesMax` is the reader's bound on a base World (open
refuses a larger base file `baseTooLarge` before decoding it) and the seal's encode twin
(`worldTooLarge`). It is NOT yet derived: it is the old literal, which PERF-2 measured reopening in
120.7 s against THE BAR's 60 s at its own size. KERNEL-55 (ROOT Q1 = B) is to derive it (HOST-57):
`Host.Cli.budget_reaches` bounds the WEIGHT of every World a budget-admitted World folds to, under
KERNEL's Canon, Slotted and RowsCanon premises (proved for genesis Worlds; composed for imported and
joined ones by cv 01a150ed-7bf7), and CODEC's size equality (`world_size_le`, cv 01a150a3-2523, not yet
a theorem) is to turn that weight into bytes. The derivation replaces this literal, never sits beside
it. A record: 64 turns
of steps `World.step` took, `recordBytesDerived` (HOST-47: it was 32 MiB, twice that, and the torn-tail
window `Log.frameMax recordBytesMax` with it). -/
def deployed : Cadence where
  sealMinBytes := 1 <<< 20
  worldBytesMax := 1 <<< 28
  recordBytesMax := recordBytesDerived

end Cadence

/-- The genesis allowance of a deployed Store, and the most a World this binary genesises, joins or
imports may carry (`allowancePastBound`, HOST-56): KERNEL-15's useful life. PRIMARY (KERNEL-55, ROOT
Q1 = B): the World bound is derived from it, never the other way. -/
def allowanceMax : Nat := 1 <<< 27

/-- The most weight a World this binary genesises, joins or imports may hold beside its allowance
(HOST-56, HOST's choice): ~7,000 founders' cells at a genesis. Together with `allowanceMax` it fixes
the most storage potential an admitted World carries (`Host.Cli.potentialMax`). -/
def genesisWeightMax : Nat := 1 <<< 20

end Nanodregg.Host
