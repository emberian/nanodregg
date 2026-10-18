/-
# Kernel.Sim.Shadow — the journal a log would leave if `commit` never pruned (KERNEL-38)

SPECIFICATION ONLY: no deployed path computes it. `Kernel.Proofs.Journal.fold_journal_filter`
states that the real fold's journal is this one filtered to the entries `kept` at the last prune
height, and `fold_prune_check` that the real World checks every windowed retry exactly as the same
World carrying the never-pruned journal. `kernel-sim`'s journal probe runs the same definitions beside the real
fold (`journal-shadow:filtered`, `journal-shadow-reuse:replayed`).
-/
import Kernel.World

namespace Nanodregg.Kernel

variable {D : Type} [Ord D]

/-- The last height at or below `h` at which `commit` pruned: the greatest multiple of
`Bounds.windowMax` that is at most `h`. -/
def lastPrune (h : Nat) : Nat := h - h % Bounds.windowMax

/-- The never-pruning journal along a log: from journal `J` at height `h`, each turn's entry is (a recorded refusal adds none
and no height)
inserted at its height, as `commit` inserts it, and nothing is removed (a recycled id keeps its
latest entry). It decides nothing: it is the real fold's journal only for a log the real fold
admitted (the theorems take `World.fold … = .ok`). It is a journal, not a second fold: a fold that
read its own unpruned journal would refuse a recycled transaction id `replayed`, so it would not
follow the log at all. -/
def shadowJournal [DecidableEq D] (E : Env D) : Nat → Journal D → List (Step D) → Journal D
  | _, J, [] => J
  | h, J, .turn t :: l => shadowJournal E (h + 1) (J.insert (journalSpec E) t.txId (h + 1, turnDigest E t)) l
  | h, J, .refusal _ :: l => shadowJournal E h J l

end Nanodregg.Kernel
