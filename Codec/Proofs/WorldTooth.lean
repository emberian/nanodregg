import Codec.Proofs.World
import Kernel.Sim

/-!
# The World codec's teeth (CODEC-19), over `Kernel.Sim`'s toy parameters

`cells` reads a trie back only from its own listing. These are the instances that show the check
bites: the canonical listing of a two-slot trie (a cell slot and a nullifier slot, parting at bit 0,
the kind: cell first) decodes, and the same two entries in the other order
are refused `kernel/trie-order` by name; a slot holding the leaf of the other kind is refused
`kernel/leaf-fit` before any trie is built.
-/

namespace Nanodregg.Codec.Kernel

open Nanodregg.Kernel Nanodregg.Codec.Stream

/-- The listing is the canonical trie's own: it decodes, and lists back the same entries. -/
theorem cells_reads_canonical_listing :
    (match (cells Sim.env Sim.dc).decode ((fitList Sim.dc).bytes [(.cell 0, .entry .tomb), (.nullifier 0, .spent)]) with
     | .ok t => t.toList == [(.cell 0, .entry .tomb), (.nullifier 0, .spent)]
     | .error _ => false) = true := by decide +kernel

/-- The plant: the same entries swapped are refused `kernel/trie-order` by name. -/
theorem cells_refuses_swapped_listing :
    (match (cells Sim.env Sim.dc).decode ((fitList Sim.dc).bytes [(.nullifier 0, .spent), (.cell 0, .entry .tomb)]) with
     | .error (.rejected _ "kernel/trie-order") => true
     | _ => false) = true := by decide +kernel

/-- A nullifier slot holding a cell entry is refused `kernel/leaf-fit` by name. -/
theorem cells_refuses_misfit_leaf :
    (match (cells Sim.env Sim.dc).decode
        ((rawList worldMax (product (slot Sim.dc) leaf)).bytes [(.nullifier 0, .entry .tomb)]) with
     | .error (.rejected _ "kernel/leaf-fit") => true
     | _ => false) = true := by decide +kernel

/-! ## The carried codec's teeth (CODEC-22) -/

/-- A carried state whose journal ascends by transaction id decodes, and lists back the same journal. -/
theorem carried_reads_ascending_journal :
    (match (carried Sim.env Sim.dc).decode
        ((carriedWire Sim.env Sim.dc).bytes (.empty, 5, 7, [(1, (2, 3)), (4, (5, 6))])) with
     | .ok c => c.journal.toList == [(1, (2, 3)), (4, (5, 6))] && c.allowance == 5 && c.height == 7
     | .error _ => false) = true := by decide +kernel

/-- The plant: the same journal entries swapped are refused `kernel/ascending` by name. -/
theorem carried_refuses_swapped_journal :
    (match (carried Sim.env Sim.dc).decode
        ((carriedWire Sim.env Sim.dc).bytes (.empty, 5, 7, [(4, (5, 6)), (1, (2, 3))])) with
     | .error (.rejected _ "kernel/ascending") => true
     | _ => false) = true := by decide +kernel

/-- A transaction id listed twice is refused `kernel/ascending` too: the order is strict. -/
theorem carried_refuses_repeated_txId :
    (match (carried Sim.env Sim.dc).decode
        ((carriedWire Sim.env Sim.dc).bytes (.empty, 5, 7, [(1, (2, 3)), (1, (5, 6))])) with
     | .error (.rejected _ "kernel/ascending") => true
     | _ => false) = true := by decide +kernel

end Nanodregg.Codec.Kernel
