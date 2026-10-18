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
  | event | slotsPerCell | slotKey | valueBytes | window | weight | counter | denoms | rows
  /-- a cell's or row's version, or a relation's floor, would reach `Bounds.counterLimit` (KERNEL-54) -/
  | version
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

/-- A row key's width bound (LANG-44 (e) said 64; KERNEL-48 raises it to 128: a key of two digests in Lang's data encoding, each with CODEC's length byte, is 66 bytes, and CoAuthor's ballots are keyed {pick, voter}). -/
def keyBytesMax : Nat := 128
/-- The rows trie's depth (KERNEL-46 amendment 1): a 32-byte parent, the relation, the tag and the
length bytes, then at most `keyBytesMax` key bytes. -/
def rowDepth : Nat := 256 + 24 + 8 * keyBytesMax
/-- A relation's row limit (LANG-44 (e), delvetalk's). -/
def rowsPerRelationMax : Nat := 4096
/-- Row touches per turn, and range reads per turn (KERNEL-48). -/
def rowsMax : Nat := 32
def rangesMax : Nat := 4

end Bounds
end Nanodregg.Kernel
