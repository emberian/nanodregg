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
  /-- a call's event bytes past `Bounds.eventBytesMax`, or a cancel's signature past
  `Bounds.cancelBytesMax` (`checkRefusedBounds`): one name for two bounds -/
  | event | slotsPerCell | slotKey | valueBytes | window | weight | counter | denoms | rows
  /-- a cell's or row's version, or a relation's floor, would reach `Bounds.counterLimit` (KERNEL-54) -/
  | version
  /-- a Turn's `ticks` past `Bounds.treeTicksMax` or `counterLimit` (DESIGN-OBS §1.3: a forged log cannot
  jump the meter) -/
  | ticks
  deriving DecidableEq, Repr

namespace Bounds

/-- Cells a turn observes (each read, written or retired cell once). -/
def touchesMax : Nat := 512
def opsPerWriteMax : Nat := 256
def createsMax : Nat := 64
def nullifiersMax : Nat := 64
def eventBytesMax : Nat := 65536
/-- A cancel record's signature (KERNEL-60): an Ed25519 signature is 64 bytes. -/
def cancelBytesMax : Nat := 64
def slotsPerCellMax : Nat := 1024
/-- Slot keys are below `2^32`, so they encode in four bytes. -/
def slotKeyLimit : Nat := 4294967296
def valueBytesMax : Nat := 65536
/-- Every counter a turn carries (window ends, charge) is below `2^64`, and a cell kind below
`2^32`, so CODEC's fixed-width encoding is injective on every admitted turn (CODEC-4). A World's
height is below every admitted window end, so it is below `2^64` too (`admit_window`). -/
def counterLimit : Nat := 18446744073709551616
def kindLimit : Nat := 4294967296
/-- The widest validity window, in heights. Bounds how long a transaction id must be remembered. -/
def windowMax : Nat := 1024
/-- The most journal entries a World holds: every World a genesis reaches holds fewer
(`Kernel.reach_journal_bounded`, KERNEL-33), and so does every World folded from a carry of one
(`Receive.carry_fold_journal_bounded`), so a carry's `journalTooLong` never fires on a reached
World (`Receive.carry_journal_fits`) and its journal listing is bounded (KERNEL-29). -/
def journalMax : Nat := 3 * windowMax
/-- The most one turn may weigh (its charge: log record plus World growth). The per-field bounds
alone allow a turn of ~8.6 GB (64 born cells of 1024 slots of 64 KiB, and as much again in
writes); this is the aggregate bound HOST budgets a frame and a batch by. Four events' worth: a
turn's effect restates its call (the event) about once, and observes up to `touchesMax` cells. -/
def weightMax : Nat := 4 * eventBytesMax
/-- Distinct denominations whose value one turn moves (LEDGER-2): a swap needs two, a fee in a
third asset three. The per-denomination sum is then an association list of at most this many
entries, O(touches) to build. -/
def denomsMax : Nat := 8
/-- A denomination's bytes (a digest's: the id of the cell that bore it). -/
def denomBytesMax : Nat := 64
/-- The World trie's depth (KERNEL-23): one kind bit, then 256 id bits (a 32-byte digest). A proof
carries at most this many siblings, and a leaf holds two keys only past it. -/
def trieDepth : Nat := 257
/-- The journal trie's depth (KERNEL-41): the 256 bits of a transaction id (a 32-byte digest). -/
def journalDepth : Nat := 256
/-- The refusals trie's depth (KERNEL-47 amendment 4): its keys are 41 bytes (a kind byte, a 32-byte
digest, eight bytes). -/
def refusalDepth : Nat := 328
/-- The authenticated, in-window refusals one member may have recorded per window of `windowMax`
heights (KERNEL-44): a flood costs the flooder this many records per window, then `refusalBudget`. -/
def refusalsPerWindow : Nat := 16
/-- The authenticated, in-window refusals the World records per window, all members together
(KERNEL-55 R1): past it a refusal is declined `refusalsFull`, a liveness cost on refusal finality
until the window turns, never on admission (~C/16 members at their own budget exhaust it:
`refusalsFull_independent`, the cap binds where the per-member budget does not). It bounds the refusals trie by a kernel fold theorem with
no receive premise (`Kernel.Proofs.RefusalsBound.fold_refusals_bounded`): a record lives while
`H < h + 2 * windowMax` at the multiples of `windowMax`, so the records of exactly three windows
coexist (the current one and the two before), at most `3 * refusalsPerWindowMax` `tx` leaves; the
counts are the current window's, at most one per member with a record in it, so at most
`refusalsPerWindowMax`; and one `total`. At 16,384: 49,152 records, 16,384 counts, 1 total. -/
def refusalsPerWindowMax : Nat := 16384
/-- The calls one method run may return (LEDGER-5, LANG-23: LANG's `callsTy` has this arity). -/
def callsMax : Nat := 8
/-- How deep a tree of calls may nest below the signed call (an object's call is depth 1). -/
def callDepthMax : Nat := 4
/-- The ticks one call's whole tree of runs may use (KERNEL-28 (c), LEDGER-8 (e)): the signed
top-level budget, capped here. Sized from two measured numbers, not guessed: it must admit the
budget PROTOCOL's client signs for every invoke (`invokeBudget` = 100000), and 2^17 is the least
power of two that does; THE BAR's invoke measures 30 ticks per call (gates/waste.tsv), so the cap
is ~4000 such runs. -/
def treeTicksMax : Nat := 131072

/-- The ticks one member's admitted Turns may spend per window of `windowMax` heights (DESIGN-OBS
§1.3, the meter): sixteen full-budget trees, by analogy with `refusalsPerWindow`; at THE BAR's ~30
ticks per invoke, ~70,000 invokes per member per window. A Turn past it is `ticksBudget`, recorded. -/
def ticksPerWindow : Nat := 16 * treeTicksMax

/-- A row key's width bound (LANG-44 (e) said 64; KERNEL-48 raises it to 128: a key of two digests in Lang's data encoding, each with CODEC's length byte, is 66 bytes, and CoAuthor's ballots are keyed {pick, voter}). -/
def keyBytesMax : Nat := 128
/-- The rows trie's depth (KERNEL-46 amendment 1, cv 01a14f7e): a 32-byte parent, the relation (a
LEB128 below 256: at most two bytes), the tag, the length (LEB128 of at most `keyBytesMax` = 128: at
most two bytes), then at most `keyBytesMax` key bytes. -/
def rowDepth : Nat := 256 + 40 + 8 * keyBytesMax
/-- A relation's row limit (LANG-44 (e), delvetalk's). -/
def rowsPerRelationMax : Nat := 4096
/-- Row touches per turn, and range reads per turn (KERNEL-48). -/
def rowsMax : Nat := 32
def rangesMax : Nat := 4

end Bounds
end Nanodregg.Kernel
