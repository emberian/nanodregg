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

HOST-22: the tail is bounded in TURNS too. Every Turn of the tail is re-folded at open, and a
follower's fold re-derives each one, signature verify included (`Receive.audit`), so bytes alone let
a tail of small Turns cost ~90k verifies (~36 s) at `worldBytesMax`. The loop also seals when
`sealTurns` Turns have been admitted since the newest durable base. The tail then holds at most
`tailTurnsMax` = two turn cadences and a record's Turns (`Host.Loop.withinTail`). Open refuses more
by name (`tailTooManyTurns`), and `Host.Proofs.Base.openWith_turns` bounds the Turns an open folds.
-/
import Host.Log

namespace Nanodregg.Host

/-- The most Turns one batch record holds: the loop's batch bound (CODEC's batch codec is bounded by it). -/
def recordTurnsMax : Nat := 64

structure Cadence where
  /-- the fewest segment bytes between two seals -/
  sealMinBytes : Nat
  /-- the largest encoded World a base may hold (`Base.SealFault.worldTooLarge` past it) -/
  worldBytesMax : Nat
  /-- the largest batch record a frame may hold -/
  recordBytesMax : Nat
  /-- the most Turns admitted after the newest durable base before the loop seals again (HOST-22) -/
  sealTurns : Nat

namespace Cadence

/-- Segment bytes between two seals, for a newest durable base of `baseBytes`. Sealing every
quarter of the base's own size amortises to at most four sealed bytes per appended byte, plus the
floor. -/
def cadence (c : Cadence) (baseBytes : Nat) : Nat := max c.sealMinBytes (baseBytes / 4)

/-- The most segment bytes after the newest durable base: one cadence being sealed, one more
while the seal runs, and the frame that crossed. -/
def tailMax (c : Cadence) (baseBytes : Nat) : Nat :=
  2 * c.cadence baseBytes + Log.frameMax c.recordBytesMax

/-- The most Turns after the newest durable base: one turn cadence being sealed, one more while
the seal runs, and the record that crossed (HOST-22). An open folds (and a follower re-verifies)
at most this many. -/
def tailTurnsMax (c : Cadence) : Nat := 2 * c.sealTurns + recordTurnsMax

/-- A base record: the World's bytes, the segment offset (u64) and tag (32) it starts from, and
its index (each bounded by `worldBytesMax`, `Base.file`). -/
def baseRecordMax (c : Cadence) : Nat := 2 * c.worldBytesMax + 8 + Log.tagBytes

/-- `host serve`'s numbers. The base: THE BAR's World is ~290 KB (HOST-14), so 256 MiB is ~900 BAR
stores; at CODEC's measured KMAC (184 MB/s) its seal is ~1.5 s of Task time and its decode at open
is the dominant term of a cold reopen (measured in decisions/host.md HOST-14). A record: 64 turns
of at most `Kernel.Bounds.weightMax` weight each, with room for the encoding's length fields. A
turn cadence of 2^13: a follower's cold open re-verifies at most 2·2^13 + 64 = 16448 signatures
(~6.6 s at CODEC's ~0.4 ms Ed25519 verify), against ~90k under the byte bound alone (HOST-22). -/
def deployed : Cadence where
  sealMinBytes := 1 <<< 20
  worldBytesMax := 1 <<< 28
  recordBytesMax := 1 <<< 25
  sealTurns := 1 <<< 13

end Cadence

/-- The genesis allowance of a deployed Store: half of `worldBytesMax`. `fold_world_weight`
(KERNEL-18) bounds the World's weight by its genesis weight plus the allowance; the other half is
headroom for the encoding's per-entry overhead over `World.weight`, which the seal asserts
(`worldTooLarge`), since CODEC's `size ≤ c · weight` is not yet a theorem. -/
def allowanceMax : Nat := Cadence.deployed.worldBytesMax / 2

end Nanodregg.Host
