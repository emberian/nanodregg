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

/-! ## The journal's teeth (KERNEL-39, CODEC-28)

`journalFits` sorts the heights with `List.mergeSort` (well-founded recursion, which the kernel does not
reduce), so these are stated through `world_decode_wire_ok` / `world_decode_wire_refused` and the
journal check is discharged by `simp` (the windowed one) or by KERNEL's own refutations
(`journalFits_future`, `journalFits_twice`). -/

private theorem empty_wireFits (l : List (Sim.D × (Nat × Sim.D))) (hl : l.length ≤ Bounds.journalMax)
    (ha : ascendingBy Prod.fst l = true) (hp : ∀ p ∈ l, p.2.1 < 2 ^ 64) :
    WireFits Sim.env (fun _ => True) (.empty, l, 7, 0, 0, 0) :=
  ⟨⟨⟨⟨by simp [Trie.T.toList, worldMax], by simp [Trie.T.toList]⟩, by simp [Trie.T.toList]⟩,
    Trie.canon_empty _ 0⟩, ⟨⟨hl, fun p hp' => ⟨trivial, hp p hp', trivial⟩⟩, ha⟩, show 7 < 2 ^ 64 by decide, trivial, show 0 < 2 ^ 64 by decide,
    trivial⟩

/-- A journal inside the window decodes: entries at heights 6 and 7 of a World at height 7. -/
theorem world_reads_windowed_journal :
    (world Sim.env Sim.dc).decode ((worldWire Sim.env Sim.dc).bytes (.empty, [(1, (6, 3)), (2, (7, 4))], 7, 0, 0, 0)) =
      .ok (ofWire (.empty, [(1, (6, 3)), (2, (7, 4))], 7, 0, 0, 0)) :=
  world_decode_wire_ok u64_lawful.on (empty_wireFits _ (by decide) (by decide) (by decide))
    (by simp [journalFits, List.mergeSort, ascendingNat, Bounds.windowMax])

/-- The plant: an entry above the World's height (never pruned, `replayed` forever) is refused
`kernel/journal` by name. -/
theorem world_refuses_future_entry :
    (world Sim.env Sim.dc).decode ((worldWire Sim.env Sim.dc).bytes (.empty, [(1, (8, 3))], 7, 0, 0, 0)) =
      .error (.rejected 0 "kernel/journal") :=
  world_decode_wire_refused u64_lawful.on (empty_wireFits _ (by decide) (by decide) (by decide))
    (journalFits_future 7 1 3)

/-- Two entries at one height (two admissions in one turn) are refused `kernel/journal`. -/
theorem world_refuses_shared_height :
    (world Sim.env Sim.dc).decode ((worldWire Sim.env Sim.dc).bytes (.empty, [(1, (7, 3)), (2, (7, 4))], 7, 0, 0, 0)) =
      .error (.rejected 0 "kernel/journal") :=
  world_decode_wire_refused u64_lawful.on (empty_wireFits _ (by decide) (by decide) (by decide))
    (journalFits_twice 7 1 2 3 4)

/-- A journal count past `Bounds.journalMax` is refused `pastBound` before one entry is read. -/
theorem world_refuses_oversized_journal :
    (match (world Sim.env Sim.dc).decode
        ((cells Sim.env Sim.dc).bytes .empty ++ Stream.u32.bytes (UInt32.ofNat (Bounds.journalMax + 1))) with
     | .error (.pastBound _ _ _) => true
     | _ => false) = true := by decide +kernel

end Nanodregg.Codec.Kernel
