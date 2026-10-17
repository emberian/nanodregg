import Codec.Proofs.Carried
import Kernel.Sim

/-!
# The World codec's teeth (CODEC-19), over `Kernel.Sim`'s toy parameters

`cells` reads a trie back only from its own listing. These are the instances that show the check
bites: the canonical listing of a two-slot trie (a cell slot and a nullifier slot, parting at bit 0,
the kind: cell first) decodes, and the same two entries in the other order
are refused `kernel/trie-order` by name; a slot holding the leaf of the other kind is refused
`kernel/leaf-fit` before any trie is built. (The journal's order teeth are at the deployed digest,
`Codec.Proofs.TrieOrderDeployed`.)
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

/-! ## The journal's teeth (KERNEL-39, KERNEL-41, CODEC-28)

`journalFits` sorts the heights with `List.mergeSort` (well-founded recursion, which the kernel does not
reduce), so these are stated through `world_decode_wire_ok` / `world_decode_wire_refused` and the
journal check is discharged by `simp` (the windowed one) or by KERNEL's own refutations
(`journalFits_future`, `journalFits_twice`). The journal is a trie (`journalSpec`): `jt l` is the
canonical trie of a listing, and `jt_toList` reads its listing back (the two ids part at byte 0). -/

/-- The canonical journal trie of a listing, at Sim's parameters. -/
private abbrev jt (l : List (Sim.D × (Nat × Sim.D))) : Journal Sim.D :=
  Trie.build (journalSpec Sim.env) (journalSpec Sim.env).depth 0 l

private theorem jt_one (k d : Sim.D) (hh : Nat) : (jt [(k, (hh, d))]).toList = [(k, (hh, d))] := by
  cases hd : (journalSpec Sim.env).depth <;> simp [jt, Trie.build, Trie.mkLeaf, Trie.T.toList, hd]

private theorem jt_window : (jt [(1, (6, 3)), (2, (7, 4))]).toList = [(1, (6, 3)), (2, (7, 4))] := by
  decide +kernel

private theorem jt_shared : (jt [(1, (7, 3)), (2, (7, 4))]).toList = [(1, (7, 3)), (2, (7, 4))] := by
  decide +kernel

private theorem jt_wireFits (l : List (Sim.D × (Nat × Sim.D))) (hl : l.length ≤ Bounds.journalMax)
    (hn : (l.map Prod.fst).Nodup) (ht : (jt l).toList = l) (hp : ∀ p ∈ l, p.2.1 < 2 ^ 64) :
    WireFits Sim.env (fun _ => True) (.empty, jt l, 7, 0, 0, 0) :=
  ⟨⟨⟨⟨by simp [Trie.T.toList, worldMax], by simp [Trie.T.toList]⟩, by simp [Trie.T.toList]⟩,
    Trie.canon_empty _ 0⟩,
    ⟨⟨by rw [ht]; exact hl, fun p hp' => ⟨trivial, hp p (ht ▸ hp'), trivial⟩⟩, Trie.canon_build _ 0 l hn⟩,
    show 7 < 2 ^ 64 by decide, trivial, show 0 < 2 ^ 64 by decide, trivial⟩

/-- A journal inside the window decodes: entries at heights 6 and 7 of a World at height 7. -/
theorem world_reads_windowed_journal :
    (world Sim.env Sim.dc).decode ((worldWire Sim.env Sim.dc).bytes (.empty, jt [(1, (6, 3)), (2, (7, 4))], 7, 0, 0, 0)) =
      .ok (ofWire (.empty, jt [(1, (6, 3)), (2, (7, 4))], 7, 0, 0, 0)) :=
  world_decode_wire_ok u64_lawful.on (jt_wireFits _ (by decide) (by decide) jt_window (by decide))
    (by show journalFits 7 (jt [(1, (6, 3)), (2, (7, 4))]).toList = true
        rw [jt_window]; simp [journalFits, List.mergeSort, ascendingNat, Bounds.windowMax])

/-- The plant: an entry above the World's height (never pruned, `replayed` forever) is refused
`kernel/journal` by name. -/
theorem world_refuses_future_entry :
    (world Sim.env Sim.dc).decode ((worldWire Sim.env Sim.dc).bytes (.empty, jt [(1, (8, 3))], 7, 0, 0, 0)) =
      .error (.rejected 0 "kernel/journal") :=
  world_decode_wire_refused u64_lawful.on (jt_wireFits _ (by decide) (by decide) (jt_one _ _ _) (by decide))
    (by show journalFits 7 (jt [(1, (8, 3))]).toList = false
        rw [jt_one]; exact journalFits_future 7 1 3)

/-- Two entries at one height (two admissions in one turn) are refused `kernel/journal`. -/
theorem world_refuses_shared_height :
    (world Sim.env Sim.dc).decode ((worldWire Sim.env Sim.dc).bytes (.empty, jt [(1, (7, 3)), (2, (7, 4))], 7, 0, 0, 0)) =
      .error (.rejected 0 "kernel/journal") :=
  world_decode_wire_refused u64_lawful.on (jt_wireFits _ (by decide) (by decide) jt_shared (by decide))
    (by show journalFits 7 (jt [(1, (7, 3)), (2, (7, 4))]).toList = false
        rw [jt_shared]; exact journalFits_twice 7 1 2 3 4)

/-- A carried state whose journal is the window's at its height decodes, exactly (KERNEL-41). -/
theorem carried_reads_windowed_journal :
    (carried Sim.env Sim.dc).decode ((carriedWire Sim.env Sim.dc).bytes (.empty, 5, 7, jt [(1, (6, 3)), (2, (7, 4))])) =
      .ok ⟨.empty, 5, 7, jt [(1, (6, 3)), (2, (7, 4))]⟩ := by
  have hw := jt_wireFits _ (by decide) (by decide) jt_window (by decide)
  show (carried Sim.env Sim.dc).decode ((carried Sim.env Sim.dc).bytes ⟨.empty, 5, 7, jt [(1, (6, 3)), (2, (7, 4))]⟩) = _
  exact carried_decode_bytes (c := ⟨.empty, 5, 7, jt [(1, (6, 3)), (2, (7, 4))]⟩) u64_lawful.on ⟨hw.1, show 5 < 2 ^ 64 by decide, show 7 < 2 ^ 64 by decide, hw.2.1,
    by rw [jt_window]; simp [journalFits, List.mergeSort, ascendingNat, Bounds.windowMax]⟩

/-- **The plant (HOST-11's find)**: a carried state with an entry above its height is refused
`kernel/carried-journal` by name, before any import could genesis-write a Store from it. -/
theorem carried_refuses_future_entry :
    (carried Sim.env Sim.dc).decode ((carriedWire Sim.env Sim.dc).bytes (.empty, 5, 7, jt [(1, (8, 3))])) =
      .error (.rejected 0 "kernel/carried-journal") := by
  have hw := jt_wireFits _ (by decide) (by decide) (jt_one 1 3 8) (by decide)
  exact carried_decode_wire_refused u64_lawful.on ⟨hw.1, show 5 < 2 ^ 64 by decide, show 7 < 2 ^ 64 by decide, hw.2.1⟩
    (by show journalFits 7 (jt [(1, (8, 3))]).toList = false
        rw [jt_one]; exact journalFits_future 7 1 3)

/-! ## The carried codec's teeth (CODEC-22, KERNEL-41) -/

private def jl : Stream (List (Sim.D × (Nat × Sim.D))) :=
  rawList Bounds.journalMax (product Sim.dc (product nat64 Sim.dc))

private def carriedRaw (l : List (Sim.D × (Nat × Sim.D))) : ByteArray :=
  (cells Sim.env Sim.dc).bytes .empty ++ nat64.bytes 5 ++ nat64.bytes 7 ++ jl.bytes l

/-- The plant: the same journal entries swapped are refused `kernel/journal-order` by name. -/
theorem carried_refuses_swapped_journal :
    (match (carried Sim.env Sim.dc).decode (carriedRaw [(2, (5, 6)), (1, (2, 3))]) with
     | .error (.rejected _ "kernel/journal-order") => true
     | _ => false) = true := by decide +kernel

/-- A transaction id listed twice is refused `kernel/journal-order` too: no leaf holds a key twice. -/
theorem carried_refuses_repeated_txId :
    (match (carried Sim.env Sim.dc).decode (carriedRaw [(1, (2, 3)), (1, (5, 6))]) with
     | .error (.rejected _ "kernel/journal-order") => true
     | _ => false) = true := by decide +kernel

/-- A journal count past `Bounds.journalMax` is refused `pastBound` before one entry is read. -/
theorem world_refuses_oversized_journal :
    (match (world Sim.env Sim.dc).decode
        ((cells Sim.env Sim.dc).bytes .empty ++ Stream.u32.bytes (UInt32.ofNat (Bounds.journalMax + 1))) with
     | .error (.pastBound _ _ _) => true
     | _ => false) = true := by decide +kernel

end Nanodregg.Codec.Kernel
