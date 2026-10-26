import Codec.World

/-!
# Codec.WorldSize — the measures a World's encoded size is stated in (cv 01a150a3-2523)

The named numbers HOST reads for its `worldBytesMax` (`entrySlack`, `worldFixed`, `journalBytes`,
`refusalsBytes`) and the per-entry counts the exact size names; their theorems are
`Codec.Proofs.WorldSize`'s (`world_size_eq`, `world_size_le`). Specification measures, O(World), never
computed on the request path.
-/

namespace Nanodregg.Codec.Kernel

open Nanodregg.Kernel Nanodregg.Codec.Stream

variable {D : Type} [Ord D]

/-! ## The named measures -/

/-- The worst ratio of an entry's wire bytes to its weight, `(numerator, denominator)`: an empty live
cell at a ten-byte version, 54 bytes for a weight of 49 (`world_size_slack_tight`). -/
def entrySlack : Nat × Nat := (54, 49)

/-- The bytes of a World that are no entry's: the four listings' u32 counts, the height, the step
count and the allowance (u64 each), the chain and the origin (32 each). -/
def worldFixed : Nat := 4 * 4 + 3 * 8 + 2 * 32

/-- The journal's bytes on the wire: 72 per entry (transaction id, u64 height, turn digest). -/
def journalBytes (w : World D) : Nat := 72 * w.journal.toList.length

/-- One refusals entry's bytes on the wire: the key (a kind byte, the digest, a `count`'s or
`total`'s window u64) and the leaf (a kind byte; a refused leaf's height and code u64 and its member,
a count's u64). -/
def refusalEntryBytes : WindowSlot D × RefusalLeaf D → Nat
  | (k, v) =>
    (match k with
      | .refusal (.tx _) => 33 | .refusal (.count _ _) => 41 | .refusal (.total _ _) => 41 | .meter (.ticks _ _) => 41) +
    (match v with | .refused _ _ _ => 49 | .count _ => 9)

/-- The refusals' bytes on the wire, entry by entry. -/
def refusalsBytes (w : World D) : Nat := (w.refusals.toList.map refusalEntryBytes).sum

/-- 1 at a live cell entry. -/
def cellItemLive : Slot D × Leaf → Nat
  | (_, .entry (.live _ _)) => 1
  | _ => 0

/-- 1 at a tombstone. -/
def cellItemTomb : Slot D × Leaf → Nat
  | (_, .entry .tomb) => 1
  | _ => 0

/-- 1 at a spent nullifier. -/
def cellItemSpent : Slot D × Leaf → Nat
  | (_, .spent) => 1
  | _ => 0

/-- A live cell's version varint width (0 elsewhere). -/
def cellItemVersion : Slot D × Leaf → Nat
  | (_, .entry (.live _ v)) => varint64.size v
  | _ => 0

/-- A rows entry's varint width: a head's floor, a row's version. -/
def rowItemVersion : RowSlot D × RowLeaf → Nat
  | (_, .head _ _ _ _ _ _ f) => varint64.size f
  | (_, .row _ _ u) => varint64.size u

/-- The World's live cells. -/
def liveCount (w : World D) : Nat := (w.trie.toList.map cellItemLive).sum
/-- The World's tombstones. -/
def tombCount (w : World D) : Nat := (w.trie.toList.map cellItemTomb).sum
/-- The World's spent nullifiers. -/
def spentCount (w : World D) : Nat := (w.trie.toList.map cellItemSpent).sum
/-- The World's rows entries (heads and rows). -/
def rowsCount (w : World D) : Nat := w.rows.toList.length
/-- The bytes the World's version varints take (live cells' versions, heads' floors, rows' versions). -/
def versionBytes (w : World D) : Nat :=
  (w.trie.toList.map cellItemVersion).sum + (w.rows.toList.map rowItemVersion).sum

/-- 1 at a refused transaction's entry. -/
def refusalItemTx : WindowSlot D × RefusalLeaf D → Nat
  | (.refusal (.tx _), _) => 1
  | _ => 0

/-! ## The slack's witness (`world_size_slack_tight`) -/

/-- An empty live cell at version `2^63`: weight 49 (id 32, version charge 8, cell 9), written in 54
(slot 33, two tags, a ten-byte varint, cell 9). -/
def slackItem (d : D) : Slot D × Leaf := (.cell d, .entry (.live ⟨0, .ram, []⟩ (2 ^ 63)))

/-- A World holding only `slackItem d`: no journal, refusals or rows. -/
def slackWorld (E : Env D) (d : D) : World D :=
  { trie := Trie.build (trieSpec E) (trieSpec E).depth 0 [slackItem d], journal := .empty,
    refusals := .empty, rows := .empty, height := 0, steps := 0, chain := d, allowance := 0, origin := d }

end Nanodregg.Codec.Kernel
