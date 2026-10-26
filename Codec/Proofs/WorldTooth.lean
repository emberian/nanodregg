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

private theorem rowsFits_empty : rowsFits Sim.env (Trie.T.empty : Rows Sim.D).toList = true := by
  simp [rowsFits, ascendingBytes, Trie.T.toList]

private theorem rowsHeaded_empty : rowsHeaded (Trie.T.empty : Rows Sim.D).toList = true := by
  simp [rowsHeaded, Trie.T.toList]

private theorem rowsParented_empty (t : Cells Sim.D) : rowsParented Sim.env t (Trie.T.empty : Rows Sim.D) = true := by
  simp [rowsParented, Trie.T.toList]

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
    WireFits Sim.env (fun _ => True) (.empty, jt l, (.empty : Refusals Sim.D), (.empty : Rows Sim.D), 7, 7, 0, 0, 0) :=
  ⟨⟨⟨⟨by simp [Trie.T.toList, worldMax], by simp [Trie.T.toList]⟩, by simp [Trie.T.toList]⟩,
    Trie.canon_empty _ 0⟩,
    ⟨⟨by rw [ht]; exact hl, fun p hp' => ⟨trivial, hp p (ht ▸ hp'), trivial⟩⟩, Trie.canon_build _ 0 l hn⟩,
    ⟨⟨by simp [Trie.T.toList, worldMax], by simp [Trie.T.toList]⟩, Trie.canon_empty _ 0⟩, ⟨⟨by simp [Trie.T.toList, worldMax], by simp [Trie.T.toList]⟩, Trie.canon_empty _ 0⟩,
    show 7 < 2 ^ 64 by decide, show 7 < 2 ^ 64 by decide, trivial, show 0 < 2 ^ 64 by decide, trivial⟩

/-- A journal inside the window decodes: entries at heights 6 and 7 of a World at height 7. -/
theorem world_reads_windowed_journal :
    (world Sim.env Sim.dc).decode ((worldWire Sim.env Sim.dc).bytes (.empty, jt [(1, (6, 3)), (2, (7, 4))], (.empty : Refusals Sim.D), (.empty : Rows Sim.D), 7, 7, 0, 0, 0)) =
      .ok (ofWire (.empty, jt [(1, (6, 3)), (2, (7, 4))], (.empty : Refusals Sim.D), (.empty : Rows Sim.D), 7, 7, 0, 0, 0)) :=
  world_decode_wire_ok u64_lawful.on (jt_wireFits _ (by decide) (by decide) jt_window (by decide))
    (by show journalFits 7 (jt [(1, (6, 3)), (2, (7, 4))]).toList = true
        rw [jt_window]; simp [journalFits, List.mergeSort, ascendingNat, Bounds.windowMax])
    (by simp [refusalsFits, ofWire, Trie.T.toList]) (by simp [refusalsDisjoint, ofWire, Trie.T.toList])
    (by decide) (by simp [refusalsCounted, ofWire, refusalTally, Trie.T.toList]) rowsFits_empty rowsHeaded_empty (rowsParented_empty _) (by decide)

/-- The plant: an entry above the World's height (never pruned, `replayed` forever) is refused
`kernel/journal` by name. -/
theorem world_refuses_future_entry :
    (world Sim.env Sim.dc).decode ((worldWire Sim.env Sim.dc).bytes (.empty, jt [(1, (8, 3))], (.empty : Refusals Sim.D), (.empty : Rows Sim.D), 7, 7, 0, 0, 0)) =
      .error (.rejected 0 "kernel/journal") :=
  world_decode_wire_refused u64_lawful.on (jt_wireFits _ (by decide) (by decide) (jt_one _ _ _) (by decide))
    (by show journalFits 7 (jt [(1, (8, 3))]).toList = false
        rw [jt_one]; exact journalFits_future 7 1 3)

/-- Two entries at one height (two admissions in one turn) are refused `kernel/journal`. -/
theorem world_refuses_shared_height :
    (world Sim.env Sim.dc).decode ((worldWire Sim.env Sim.dc).bytes (.empty, jt [(1, (7, 3)), (2, (7, 4))], (.empty : Refusals Sim.D), (.empty : Rows Sim.D), 7, 7, 0, 0, 0)) =
      .error (.rejected 0 "kernel/journal") :=
  world_decode_wire_refused u64_lawful.on (jt_wireFits _ (by decide) (by decide) jt_shared (by decide))
    (by show journalFits 7 (jt [(1, (7, 3)), (2, (7, 4))]).toList = false
        rw [jt_shared]; exact journalFits_twice 7 1 2 3 4)

/-- A carried state whose journal is the window's at its height decodes, exactly (KERNEL-41). -/
theorem carried_reads_windowed_journal :
    (carried Sim.env Sim.dc).decode ((carriedWire Sim.env Sim.dc).bytes (.empty, 5, 7, jt [(1, (6, 3)), (2, (7, 4))], .empty)) =
      .ok ⟨.empty, 5, 7, jt [(1, (6, 3)), (2, (7, 4))], .empty⟩ := by
  have hw := jt_wireFits _ (by decide) (by decide) jt_window (by decide)
  show (carried Sim.env Sim.dc).decode ((carried Sim.env Sim.dc).bytes ⟨.empty, 5, 7, jt [(1, (6, 3)), (2, (7, 4))], .empty⟩) = _
  exact carried_decode_bytes (c := ⟨.empty, 5, 7, jt [(1, (6, 3)), (2, (7, 4))], .empty⟩) u64_lawful.on ⟨hw.1, show 5 < 2 ^ 64 by decide, show 7 < 2 ^ 64 by decide, hw.2.1,
    by rw [jt_window]; simp [journalFits, List.mergeSort, ascendingNat, Bounds.windowMax],
    ⟨⟨⟨by simp [Trie.T.toList, worldMax], by simp [Trie.T.toList]⟩, Trie.canon_empty _ 0⟩, rowsFits_empty, rowsHeaded_empty, rowsParented_empty _⟩⟩

/-- **The plant (HOST-11's find)**: a carried state with an entry above its height is refused
`kernel/carried-journal` by name, before any import could genesis-write a Store from it. -/
theorem carried_refuses_future_entry :
    (carried Sim.env Sim.dc).decode ((carriedWire Sim.env Sim.dc).bytes (.empty, 5, 7, jt [(1, (8, 3))], .empty)) =
      .error (.rejected 0 "kernel/carried-journal") := by
  have hw := jt_wireFits _ (by decide) (by decide) (jt_one 1 3 8) (by decide)
  exact carried_decode_wire_refused u64_lawful.on ⟨hw.1, show 5 < 2 ^ 64 by decide, show 7 < 2 ^ 64 by decide, hw.2.1,
    ⟨⟨by simp [Trie.T.toList, worldMax], by simp [Trie.T.toList]⟩, Trie.canon_empty _ 0⟩⟩
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

/-! ## The refusals' teeth (KERNEL-44, KERNEL-47)

A World at height 7 (window 0) whose refusals hold one refused call and one member's count. The
per-window budget's boundary: a count of `Bounds.refusalsPerWindow` (16) reads back, 17 is refused
`kernel/refusals`; so is a refusal recorded above the height it could have been admitted at, and a
`tx` key holding a count. A height above the step count is refused `kernel/steps`. -/

/-- The canonical refusals trie of a listing, at Sim's parameters. -/
private abbrev rt (l : List (WindowSlot Sim.D × RefusalLeaf Sim.D)) : Refusals Sim.D :=
  Trie.build (refusalSpec Sim.env) (refusalSpec Sim.env).depth 0 l

/-- A World wire at height 7, empty cells and journal, with refusals `r` and `steps` steps. -/
private abbrev rx (r : Refusals Sim.D) (steps : Nat) : WorldWire Sim.D :=
  (.empty, (.empty : Journal Sim.D), r, (.empty : Rows Sim.D), 7, steps, 0, 0, 0)

private theorem rx_wireFits (l : List (WindowSlot Sim.D × RefusalLeaf Sim.D)) (steps : Nat) (hst : steps < 2 ^ 64)
    (hl : l.length ≤ worldMax) (hn : (l.map Prod.fst).Nodup) (ht : (rt l).toList = l)
    (hp : ∀ p ∈ l, RefusalLeaf.Fits p.2) :
    WireFits Sim.env (fun _ => True) (rx (rt l) steps) :=
  ⟨⟨⟨⟨by simp [Trie.T.toList, worldMax], by simp [Trie.T.toList]⟩, by simp [Trie.T.toList]⟩,
    Trie.canon_empty _ 0⟩,
    ⟨⟨by simp [Trie.T.toList, Bounds.journalMax, Bounds.windowMax], by simp [Trie.T.toList]⟩, Trie.canon_empty _ 0⟩,
    ⟨⟨by rw [ht]; exact hl, fun p hp' => by
        refine ⟨?_, RefusalLeaf.wireFits_of_fits (fun _ => trivial) (hp p (ht ▸ hp'))⟩
        obtain ⟨k | k, v⟩ := p <;> cases k <;> trivial⟩, Trie.canon_build _ 0 l hn⟩, ⟨⟨by simp [Trie.T.toList, worldMax], by simp [Trie.T.toList]⟩, Trie.canon_empty _ 0⟩,
    show 7 < 2 ^ 64 by decide, hst, trivial, show 0 < 2 ^ 64 by decide, trivial⟩

/-- Member 2's `n` refusals recorded at height 7 (transaction ids 1 to `n`), its count `n`, and the
World's window total `n` under the origin 0 (KERNEL-55 R1). -/
private abbrev atCount (n : Nat) : List (WindowSlot Sim.D × RefusalLeaf Sim.D) :=
  (List.range n).map (fun i => (.refusal (.tx (UInt64.ofNat (i + 1))), .refused 7 3 2)) ++ [(.refusal (.count 2 0), .count n), (.refusal (.total 0 0), .count n)]

private theorem rt_atCount1 : (rt (atCount 1)).toList = atCount 1 := by
  decide +kernel

private theorem rt_atCount16 : (rt (atCount 16)).toList = atCount 16 := by
  decide +kernel

private theorem rt_atCount17 : (rt (atCount 17)).toList = atCount 17 := by
  decide +kernel

private theorem atCount_fits (n : Nat) (hn : n < 2 ^ 64) : ∀ p ∈ atCount n, RefusalLeaf.Fits p.2 := by
  intro p hp
  simp only [atCount, List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with ⟨i, -, rfl⟩ | rfl | rfl
  · exact ⟨by decide, by decide⟩
  · exact hn
  · exact hn

private theorem atCount_wireFits (n steps : Nat) (hn : n < 2 ^ 64) (hst : steps < 2 ^ 64)
    (hl : (atCount n).length ≤ worldMax) (hnd : ((atCount n).map Prod.fst).Nodup)
    (ht : (rt (atCount n)).toList = atCount n) :
    WireFits Sim.env (fun _ => True) (rx (rt (atCount n)) steps) :=
  rx_wireFits _ steps hst hl hnd ht (atCount_fits n hn)

private theorem journalFits_empty : journalFits 7 (Trie.T.empty : Journal Sim.D).toList = true := by
  simp [journalFits, Trie.T.toList, ascendingNat]

/-- At the per-window budget: a member's count of exactly `Bounds.refusalsPerWindow`, with its sixteen
records (23 steps: seven Turns and sixteen refusals), reads back. -/
theorem world_reads_refusals_at_budget :
    (world Sim.env Sim.dc).decode ((worldWire Sim.env Sim.dc).bytes (rx (rt (atCount 16)) 23)) =
      .ok (ofWire (rx (rt (atCount 16)) 23)) :=
  world_decode_wire_ok u64_lawful.on
    (atCount_wireFits 16 23 (by decide) (by decide) (by decide +kernel) (by decide +kernel) rt_atCount16) journalFits_empty
    (by show refusalsFits 7 (rt (atCount 16)).toList = true
        rw [rt_atCount16]; decide +kernel)
    (by decide +kernel) (by decide) (by decide +kernel) rowsFits_empty rowsHeaded_empty (rowsParented_empty _) (by decide)

/-- **The plant**: one past the budget, a count of 17, is refused `kernel/refusals` by name. -/
theorem world_refuses_count_past_budget :
    (world Sim.env Sim.dc).decode ((worldWire Sim.env Sim.dc).bytes (rx (rt (atCount 17)) 24)) =
      .error (.rejected 0 "kernel/refusals") :=
  world_decode_wire_refusalsRefused u64_lawful.on
    (atCount_wireFits 17 24 (by decide) (by decide) (by decide +kernel) (by decide +kernel) rt_atCount17) journalFits_empty
    (by show refusalsFits 7 (rt (atCount 17)).toList = false
        rw [rt_atCount17]; decide +kernel)

private theorem rt_one (k : WindowSlot Sim.D) (v : RefusalLeaf Sim.D) : (rt [(k, v)]).toList = [(k, v)] := by
  cases hd : (refusalSpec Sim.env).depth <;> simp [rt, Trie.build, Trie.mkLeaf, Trie.T.toList, hd]

/-- **The plant**: a call recorded refused at height 9 in a World at height 7 (above `height + 1`, the
height it could have been admitted at) is refused `kernel/refusals`. -/
theorem world_refuses_future_refusal :
    (world Sim.env Sim.dc).decode ((worldWire Sim.env Sim.dc).bytes (rx (rt [(.refusal (.tx 1), .refused 9 3 2)]) 7)) =
      .error (.rejected 0 "kernel/refusals") :=
  world_decode_wire_refusalsRefused u64_lawful.on
    (rx_wireFits _ 7 (by decide) (by simp [worldMax]) (by simp) (rt_one _ _)
      (by intro p hp; simp at hp; subst hp; exact ⟨by decide, by decide⟩))
    journalFits_empty
    (by show refusalsFits 7 (rt [(.refusal (.tx 1), .refused 9 3 2)]).toList = false
        rw [rt_one]; decide)

/-- **The plant**: a refused-call key holding a count is refused `kernel/refusals`. -/
theorem world_refuses_misfit_refusal :
    (world Sim.env Sim.dc).decode ((worldWire Sim.env Sim.dc).bytes (rx (rt [(.refusal (.tx 1), .count 1)]) 7)) =
      .error (.rejected 0 "kernel/refusals") :=
  world_decode_wire_refusalsRefused u64_lawful.on
    (rx_wireFits _ 7 (by decide) (by simp [worldMax]) (by simp) (rt_one _ _)
      (by intro p hp; simp at hp; subst hp; show 1 < 2 ^ 64; decide))
    journalFits_empty
    (by show refusalsFits 7 (rt [(.refusal (.tx 1), .count 1)]).toList = false
        rw [rt_one]; decide)

/-- **The plant**: a World at height 7 that has taken 6 steps is refused `kernel/steps`; at 7 steps
(`world_reads_refusals_at_budget`) it reads back. -/
theorem world_refuses_height_past_steps :
    (world Sim.env Sim.dc).decode ((worldWire Sim.env Sim.dc).bytes (rx .empty 6)) =
      .error (.rejected 0 "kernel/steps") :=
  world_decode_wire_stepsRefused u64_lawful.on
    (rx_wireFits [] 6 (by decide) (by simp) (by simp) (by simp [rt, Trie.build, Trie.T.toList]) (by simp))
    journalFits_empty (by simp [refusalsFits, ofWire, Trie.T.toList])
    (by simp [refusalsDisjoint, ofWire, Trie.T.toList]) (by decide)

/-- **The plant**: the refusals listing in the other order is refused `kernel/refusal-order` by name. -/
theorem refusals_refuses_swapped_listing :
    (match (refusalsTrie Sim.env Sim.dc).decode
        ((rawList worldMax (product (refusalSlot Sim.dc) (refusalLeaf Sim.dc))).bytes
          [(.refusal (.count 2 0), .count 1), (.refusal (.tx 1), .refused 7 3 2)]) with
     | .error (.rejected _ "kernel/refusal-order") => true
     | _ => false) = true := by decide +kernel

/-- The canonical order reads back. -/
theorem refusals_reads_canonical_listing :
    (match (refusalsTrie Sim.env Sim.dc).decode
        ((rawList worldMax (product (refusalSlot Sim.dc) (refusalLeaf Sim.dc))).bytes
          [(.refusal (.tx 1), .refused 7 3 2), (.refusal (.count 2 0), .count 1)]) with
     | .ok t => t.toList == [(.refusal (.tx 1), .refused 7 3 2), (.refusal (.count 2 0), .count 1)]
     | .error _ => false) = true := by decide +kernel

/-- **The plant**: transaction id 1 both journaled (admitted at height 7) and recorded refused is
refused `kernel/refusals-disjoint` by name; no fold reaches it (KERNEL's `fold_refusalsDisjoint`). -/
theorem world_refuses_refused_and_journaled :
    (world Sim.env Sim.dc).decode ((worldWire Sim.env Sim.dc).bytes
        (.empty, jt [(1, (7, 3))], rt [(.refusal (.tx 1), .refused 7 3 2)], (.empty : Rows Sim.D), 7, 7, 0, 0, 0)) =
      .error (.rejected 0 "kernel/refusals-disjoint") := by
  have hj := jt_wireFits [(1, (7, 3))] (by decide) (by decide) (jt_one _ _ _) (by decide)
  have hr := rx_wireFits [(.refusal (.tx 1), .refused 7 3 2)] 7 (by decide) (by simp [worldMax]) (by simp) (rt_one _ _)
    (by intro p hp; simp at hp; subst hp; exact ⟨by decide, by decide⟩)
  exact world_decode_wire_disjointRefused u64_lawful.on
    ⟨hj.1, hj.2.1, hr.2.2.1, hj.2.2.2⟩
    (by show journalFits 7 (jt [(1, (7, 3))]).toList = true
        rw [jt_one]; simp [journalFits, ascendingNat, Bounds.windowMax])
    (by show refusalsFits 7 (rt [(.refusal (.tx 1), .refused 7 3 2)]).toList = true
        rw [rt_one]; decide)
    (by decide +kernel)

/-! ### The window's edges, and each accepted twin (the vacuity read's finding 6)

`ry H r steps` is the World wire at height `H`. At `H = 4096` (a window boundary, `H % 1024 = 0`) a call
refused at height 2049 is still kept (`4096 < 2049 + 2048`) and one refused at 2048 is stale. -/

private abbrev ry (H : Nat) (r : Refusals Sim.D) (steps : Nat) : WorldWire Sim.D :=
  (.empty, (.empty : Journal Sim.D), r, (.empty : Rows Sim.D), H, steps, 0, 0, 0)

private theorem ry_one_wireFits (H steps : Nat) (hH : H < 2 ^ 64) (hst : steps < 2 ^ 64) (k : WindowSlot Sim.D)
    (v : RefusalLeaf Sim.D) (hv : RefusalLeaf.Fits v) : WireFits Sim.env (fun _ => True) (ry H (rt [(k, v)]) steps) :=
  ⟨⟨⟨⟨by simp [Trie.T.toList, worldMax], by simp [Trie.T.toList]⟩, by simp [Trie.T.toList]⟩,
    Trie.canon_empty _ 0⟩,
    ⟨⟨by simp [Trie.T.toList, Bounds.journalMax, Bounds.windowMax], by simp [Trie.T.toList]⟩, Trie.canon_empty _ 0⟩,
    ⟨⟨by rw [rt_one]; simp [worldMax], fun p hp' => by
        rw [rt_one] at hp'; simp at hp'; subst hp'
        exact ⟨by rcases k with k | k <;> cases k <;> trivial, RefusalLeaf.wireFits_of_fits (fun _ => trivial) hv⟩⟩, Trie.canon_build _ 0 _ (by simp)⟩, ⟨⟨by simp [Trie.T.toList, worldMax], by simp [Trie.T.toList]⟩, Trie.canon_empty _ 0⟩,
    hH, hst, trivial, show 0 < 2 ^ 64 by decide, trivial⟩

private theorem journalFits_nil (H : Nat) : journalFits H (Trie.T.empty : Journal Sim.D).toList = true := by
  simp [journalFits, Trie.T.toList, ascendingNat]

private theorem triple_fits (k k' k'' : WindowSlot Sim.D) {h c n : Nat} {m : Sim.D} (hh : h < 2 ^ 64) (hc : c < 2 ^ 64)
    (hn : n < 2 ^ 64) :
    ∀ p ∈ [(k, RefusalLeaf.refused h c m), (k', RefusalLeaf.count n), (k'', RefusalLeaf.count n)], RefusalLeaf.Fits p.2 := by
  intro p hp
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact ⟨hh, hc⟩
  · exact hn
  · exact hn

/-- A call refused at `height + 1` (8, at height 7), the height it would have been admitted at, reads
back (with its member's count, and the step it cost): the accepted twin of
`world_refuses_future_refusal`. -/
theorem world_reads_refusal_at_next_height :
    (world Sim.env Sim.dc).decode ((worldWire Sim.env Sim.dc).bytes (rx (rt [(.refusal (.tx 1), .refused 8 3 2), (.refusal (.count 2 0), .count 1), (.refusal (.total 0 0), .count 1)]) 8)) =
      .ok (ofWire (rx (rt [(.refusal (.tx 1), .refused 8 3 2), (.refusal (.count 2 0), .count 1), (.refusal (.total 0 0), .count 1)]) 8)) :=
  world_decode_wire_ok u64_lawful.on
    (rx_wireFits _ 8 (by decide) (by simp [worldMax]) (by decide) (by decide +kernel)
      (triple_fits _ _ _ (by decide) (by decide) (by decide)))
    journalFits_empty (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) rowsFits_empty
    rowsHeaded_empty (rowsParented_empty _) (by decide)

/-- At a window boundary, a call refused 2048 heights ago is still kept (2049 at height 4096)... -/
theorem world_reads_refusal_at_window_edge :
    (world Sim.env Sim.dc).decode ((worldWire Sim.env Sim.dc).bytes (ry 4096 (rt [(.refusal (.tx 1), .refused 2049 3 2)]) 4097)) =
      .ok (ofWire (ry 4096 (rt [(.refusal (.tx 1), .refused 2049 3 2)]) 4097)) :=
  world_decode_wire_ok u64_lawful.on (ry_one_wireFits 4096 4097 (by decide) (by decide) _ _ ⟨by decide, by decide⟩)
    (journalFits_nil 4096) (by dsimp only [ofWire, ry]; rw [rt_one]; decide) (by decide +kernel) (by decide)
    (by decide +kernel) rowsFits_empty
    rowsHeaded_empty (rowsParented_empty _) (by decide)

/-- **The plant**: ...and one height older (2048) is stale, refused `kernel/refusals` (it should have
been pruned). -/
theorem world_refuses_stale_refusal :
    (world Sim.env Sim.dc).decode ((worldWire Sim.env Sim.dc).bytes (ry 4096 (rt [(.refusal (.tx 1), .refused 2048 3 2)]) 4096)) =
      .error (.rejected 0 "kernel/refusals") :=
  world_decode_wire_refusalsRefused u64_lawful.on (ry_one_wireFits 4096 4096 (by decide) (by decide) _ _ ⟨by decide, by decide⟩)
    (journalFits_nil 4096) (by dsimp only [ofWire, ry]; rw [rt_one]; decide)

/-- A count for the current window (0, at height 7), with the one record it counts, reads back... -/
theorem world_reads_current_window_count :
    (world Sim.env Sim.dc).decode ((worldWire Sim.env Sim.dc).bytes (rx (rt (atCount 1)) 8)) =
      .ok (ofWire (rx (rt (atCount 1)) 8)) :=
  world_decode_wire_ok u64_lawful.on
    (atCount_wireFits 1 8 (by decide) (by decide) (by decide +kernel) (by decide +kernel) rt_atCount1)
    journalFits_empty (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) rowsFits_empty
    rowsHeaded_empty (rowsParented_empty _) (by decide)

/-- **The plant**: ...and a count for another window (1) is refused `kernel/refusals`. -/
theorem world_refuses_past_window_count :
    (world Sim.env Sim.dc).decode ((worldWire Sim.env Sim.dc).bytes (ry 7 (rt [(.refusal (.count 2 1), .count 1)]) 7)) =
      .error (.rejected 0 "kernel/refusals") :=
  world_decode_wire_refusalsRefused u64_lawful.on (ry_one_wireFits 7 7 (by decide) (by decide) _ _ (show _ < 2 ^ 64 by decide))
    (journalFits_nil 7) (by dsimp only [ofWire, ry]; rw [rt_one]; decide)

/-- **The plant**: a count of 0 (a key the kernel never writes) is refused `kernel/refusals`. -/
theorem world_refuses_zero_count :
    (world Sim.env Sim.dc).decode ((worldWire Sim.env Sim.dc).bytes (ry 7 (rt [(.refusal (.count 2 0), .count 0)]) 7)) =
      .error (.rejected 0 "kernel/refusals") :=
  world_decode_wire_refusalsRefused u64_lawful.on (ry_one_wireFits 7 7 (by decide) (by decide) _ _ (show _ < 2 ^ 64 by decide))
    (journalFits_nil 7) (by dsimp only [ofWire, ry]; rw [rt_one]; decide)

/-- **The plant**: a count key holding a refused leaf is refused `kernel/refusals` (the other misfit). -/
theorem world_refuses_misfit_count_key :
    (world Sim.env Sim.dc).decode ((worldWire Sim.env Sim.dc).bytes (ry 7 (rt [(.refusal (.count 2 0), .refused 7 3 2)]) 7)) =
      .error (.rejected 0 "kernel/refusals") :=
  world_decode_wire_refusalsRefused u64_lawful.on (ry_one_wireFits 7 7 (by decide) (by decide) _ _ ⟨by decide, by decide⟩)
    (journalFits_nil 7) (by dsimp only [ofWire, ry]; rw [rt_one]; decide)

/-- The accepted twin of `world_refuses_height_past_steps`: the same World with 7 steps reads back. -/
theorem world_reads_height_eq_steps :
    (world Sim.env Sim.dc).decode ((worldWire Sim.env Sim.dc).bytes (rx .empty 7)) =
      .ok (ofWire (rx .empty 7)) :=
  world_decode_wire_ok u64_lawful.on
    (rx_wireFits [] 7 (by decide) (by simp) (by simp) (by simp [rt, Trie.build, Trie.T.toList]) (by simp))
    journalFits_empty (by simp [refusalsFits, ofWire, Trie.T.toList])
    (by simp [refusalsDisjoint, ofWire, Trie.T.toList]) (by decide)
    (by simp [refusalsCounted, ofWire, refusalTally, Trie.T.toList]) rowsFits_empty rowsHeaded_empty (rowsParented_empty _) (by decide)

/-- The accepted twin of `world_refuses_refused_and_journaled`: id 1 journaled, id 2 refused (and
counted, eight steps: seven Turns and the refusal). -/
theorem world_reads_refused_not_journaled :
    (world Sim.env Sim.dc).decode ((worldWire Sim.env Sim.dc).bytes
        (.empty, jt [(1, (7, 3))], rt [(.refusal (.tx 2), .refused 7 3 2), (.refusal (.count 2 0), .count 1), (.refusal (.total 0 0), .count 1)], (.empty : Rows Sim.D), 7, 8, 0, 0, 0)) =
      .ok (ofWire (.empty, jt [(1, (7, 3))], rt [(.refusal (.tx 2), .refused 7 3 2), (.refusal (.count 2 0), .count 1), (.refusal (.total 0 0), .count 1)], (.empty : Rows Sim.D), 7, 8, 0, 0, 0)) := by
  have hj := jt_wireFits [(1, (7, 3))] (by decide) (by decide) (jt_one _ _ _) (by decide)
  have hr := rx_wireFits [(.refusal (.tx 2), .refused 7 3 2), (.refusal (.count 2 0), .count 1), (.refusal (.total 0 0), .count 1)] 8 (by decide) (by simp [worldMax]) (by decide)
    (by decide +kernel) (triple_fits _ _ _ (by decide) (by decide) (by decide))
  exact world_decode_wire_ok u64_lawful.on
    ⟨hj.1, hj.2.1, hr.2.2.1, hr.2.2.2⟩
    (by show journalFits 7 (jt [(1, (7, 3))]).toList = true
        rw [jt_one]; simp [journalFits, ascendingNat, Bounds.windowMax])
    (by decide +kernel)
    (by decide +kernel) (by decide) (by decide +kernel) rowsFits_empty rowsHeaded_empty (rowsParented_empty _) (by decide)

/-- **The plant**: a call recorded refused at height 0 (a fold records `height + 1 ≥ 1`) is refused
`kernel/refusals`. -/
theorem world_refuses_refusal_at_zero :
    (world Sim.env Sim.dc).decode ((worldWire Sim.env Sim.dc).bytes (ry 7 (rt [(.refusal (.tx 1), .refused 0 3 2)]) 7)) =
      .error (.rejected 0 "kernel/refusals") :=
  world_decode_wire_refusalsRefused u64_lawful.on (ry_one_wireFits 7 7 (by decide) (by decide) _ _ ⟨by decide, by decide⟩)
    (journalFits_nil 7) (by dsimp only [ofWire, ry]; rw [rt_one]; decide)

/-! ## The counts' teeth (KERNEL-50, `kernel/refusals-counted`)

A World at height 7 whose refusals hold three refusals recorded this window, two charged to member 2
and one to member 5, and the two members' counts: `charged 2 1` is the history's (it reads back, at 10
steps: seven Turns and three refusals). Every other pairing of counts (one of 2's charges moved to 5,
or one dropped), and the right counts at too few steps, are refused `kernel/refusals-counted` by
name, although every earlier check passes them: each count is within the budget and of the current
window, so `kernel/refusals` admits it. -/

private abbrev charged (a b : Nat) (t : Nat := 3) : List (WindowSlot Sim.D × RefusalLeaf Sim.D) :=
  [(.refusal (.tx 1), .refused 7 3 2), (.refusal (.tx 2), .refused 7 3 2), (.refusal (.tx 3), .refused 7 3 5), (.refusal (.count 2 0), .count a),
   (.refusal (.count 5 0), .count b), (.refusal (.total 0 0), .count t)]

private theorem rt_charged21 : (rt (charged 2 1)).toList = charged 2 1 := by decide +kernel
private theorem rt_charged12 : (rt (charged 1 2)).toList = charged 1 2 := by decide +kernel
private theorem rt_charged11 : (rt (charged 1 1)).toList = charged 1 1 := by decide +kernel

private theorem charged_wireFits (a b steps : Nat) {t : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (hst : steps < 2 ^ 64)
    (htt : t < 2 ^ 64) (ht : (rt (charged a b t)).toList = charged a b t) :
    WireFits Sim.env (fun _ => True) (rx (rt (charged a b t)) steps) :=
  rx_wireFits _ steps hst (by simp [worldMax]) (by simp [charged]) ht (by
    intro p hp
    simp only [charged, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, by decide⟩
    · exact ⟨by decide, by decide⟩
    · exact ⟨by decide, by decide⟩
    · exact ha
    · exact hb
    · exact htt)

/-- The counts the history wrote read back. -/
theorem world_reads_counted_charges :
    (world Sim.env Sim.dc).decode ((worldWire Sim.env Sim.dc).bytes (rx (rt (charged 2 1)) 10)) =
      .ok (ofWire (rx (rt (charged 2 1)) 10)) :=
  world_decode_wire_ok u64_lawful.on (charged_wireFits 2 1 10 (by decide) (by decide) (by decide) (by decide) rt_charged21)
    journalFits_empty (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) rowsFits_empty
    rowsHeaded_empty (rowsParented_empty _) (by decide)

/-- **The plant** (KERNEL's `refusalsCounted_moved`): one of member 2's charges moved to member 5, the
records untouched and the sum of the counts unchanged, is refused `kernel/refusals-counted`. -/
theorem world_refuses_moved_charge :
    (world Sim.env Sim.dc).decode ((worldWire Sim.env Sim.dc).bytes (rx (rt (charged 1 2)) 10)) =
      .error (.rejected 0 "kernel/refusals-counted") :=
  world_decode_wire_countedRefused u64_lawful.on (charged_wireFits 1 2 10 (by decide) (by decide) (by decide) (by decide) rt_charged12)
    journalFits_empty (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

/-- **The plant**: one of member 2's charges dropped (its budget partly reset) is refused
`kernel/refusals-counted`. -/
theorem world_refuses_lowered_charge :
    (world Sim.env Sim.dc).decode ((worldWire Sim.env Sim.dc).bytes (rx (rt (charged 1 1)) 10)) =
      .error (.rejected 0 "kernel/refusals-counted") :=
  world_decode_wire_countedRefused u64_lawful.on (charged_wireFits 1 1 10 (by decide) (by decide) (by decide) (by decide) rt_charged11)
    journalFits_empty (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

/-! ## The World's refusals cap (KERNEL-55 R1)

The window total, a `count` leaf under the third key kind `total` (origin, window), is at most
`Bounds.refusalsPerWindowMax` (C = 16384) by `kernel/refusals`, and is its records' (all members
together, present iff there is one) by `kernel/refusals-counted`. The cap's boundary pair is the
listing check (`refusalsFits`) alone; the records-backed twin at C is `codec-vectors`' row (C records
are past what `decide` should evaluate). -/

/-- At the cap: a total of exactly C, of the current window, is a leaf `refusalsFits` admits. -/
theorem refusalsFits_total_at_cap :
    refusalsFits 7 [((.refusal (.total 0 0) : WindowSlot Sim.D), (.count Bounds.refusalsPerWindowMax : RefusalLeaf Sim.D))] = true := by
  decide

/-- **The plant**: one past the cap, a total of C + 1, is refused `kernel/refusals` by name. -/
theorem world_refuses_total_past_cap :
    (world Sim.env Sim.dc).decode ((worldWire Sim.env Sim.dc).bytes
        (ry 7 (rt [(.refusal (.total 0 0), .count (Bounds.refusalsPerWindowMax + 1))]) 7)) =
      .error (.rejected 0 "kernel/refusals") :=
  world_decode_wire_refusalsRefused u64_lawful.on (ry_one_wireFits 7 7 (by decide) (by decide) _ _ (show _ < 2 ^ 64 by decide))
    (journalFits_nil 7) (by dsimp only [ofWire, ry]; rw [rt_one]; decide)

private theorem rt_charged214 : (rt (charged 2 1 4)).toList = charged 2 1 4 := by decide +kernel

/-- **The plant**: the history's counts with the window total one over its three records is refused
`kernel/refusals-counted` by name (`kernel/refusals` admits it: 4 is within the cap);
`world_reads_counted_charges` is its accepted twin at 3. -/
theorem world_refuses_total_over_records :
    (world Sim.env Sim.dc).decode ((worldWire Sim.env Sim.dc).bytes (rx (rt (charged 2 1 4)) 10)) =
      .error (.rejected 0 "kernel/refusals-counted") :=
  world_decode_wire_countedRefused u64_lawful.on (charged_wireFits 2 1 10 (by decide) (by decide) (by decide) (by decide) rt_charged214)
    journalFits_empty (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

private abbrev strayTotal : List (WindowSlot Sim.D × RefusalLeaf Sim.D) := charged 2 1 ++ [(.refusal (.total 1 0), .count 3)]

private theorem rt_strayTotal : (rt strayTotal).toList = strayTotal := by decide +kernel

/-- **The plant**: the history's records, counts and total, and a second total of the same window and
count under a digest that is not the World's origin (1, where the origin is 0), is refused
`kernel/refusals-counted` by name: `refusalsFits` admits it (the listing check reads no origin), so only
the counted check's `o = w.origin` refuses it. `world_reads_counted_charges` is its accepted twin. -/
theorem world_refuses_stray_total :
    (world Sim.env Sim.dc).decode ((worldWire Sim.env Sim.dc).bytes (rx (rt strayTotal) 10)) =
      .error (.rejected 0 "kernel/refusals-counted") :=
  world_decode_wire_countedRefused u64_lawful.on
    (rx_wireFits _ 10 (by decide) (by simp [worldMax]) (by decide) rt_strayTotal (by
      intro p hp
      simp only [strayTotal, List.cons_append, List.nil_append, List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨by decide, by decide⟩
      · exact ⟨by decide, by decide⟩
      · exact ⟨by decide, by decide⟩
      · show 2 < 2 ^ 64; decide
      · show 1 < 2 ^ 64; decide
      · show 3 < 2 ^ 64; decide
      · show 3 < 2 ^ 64; decide))
    journalFits_empty (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

private abbrev untotalled : List (WindowSlot Sim.D × RefusalLeaf Sim.D) := (charged 2 1).take 5

private theorem rt_untotalled : (rt untotalled).toList = untotalled := by decide +kernel

/-- **The plant**: the history's records and counts with no window total is refused
`kernel/refusals-counted` by name (a window with a record holds its total). -/
theorem world_refuses_missing_total :
    (world Sim.env Sim.dc).decode ((worldWire Sim.env Sim.dc).bytes (rx (rt untotalled) 10)) =
      .error (.rejected 0 "kernel/refusals-counted") :=
  world_decode_wire_countedRefused u64_lawful.on
    (rx_wireFits _ 10 (by decide) (by simp [worldMax]) (by decide) rt_untotalled (by
      intro p hp
      simp only [untotalled, List.take, List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl
      · exact ⟨by decide, by decide⟩
      · exact ⟨by decide, by decide⟩
      · exact ⟨by decide, by decide⟩
      · show 2 < 2 ^ 64; decide
      · show 1 < 2 ^ 64; decide))
    journalFits_empty (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

/-- **The plant**: the history's counts at nine steps (three refusals and height 7 need ten; the height
alone, which `kernel/steps` checks, is within nine) are refused `kernel/refusals-counted`. -/
theorem world_refuses_records_past_steps :
    (world Sim.env Sim.dc).decode ((worldWire Sim.env Sim.dc).bytes (rx (rt (charged 2 1)) 9)) =
      .error (.rejected 0 "kernel/refusals-counted") :=
  world_decode_wire_countedRefused u64_lawful.on (charged_wireFits 2 1 9 (by decide) (by decide) (by decide) (by decide) rt_charged21)
    journalFits_empty (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

/-! ## The rows' teeth (KERNEL-46/48, CODEC-33)

A World at height 7 whose rows hold one relation (parent 1, relation 7) declared with a limit of 4 rows,
a cap of 40 and a key width of 2. The cap's boundary: a relation summing exactly its cap reads back, one
past it is refused `kernel/rows`. A head counting a row it does not hold is refused
`kernel/rows-headed`; the same head with its row reads back. The listing in the other order is refused
`kernel/row-order`. -/

/-- The canonical rows trie of a listing, at Sim's parameters. -/
private abbrev wr (l : List (RowSlot Sim.D × RowLeaf)) : Rows Sim.D :=
  Trie.build (rowSpec Sim.env) (rowSpec Sim.env).depth 0 l

/-- The cells listing of a World holding one live cell, id 1 (the relations' parent). -/
private abbrev parentCells : List (Slot Sim.D × Leaf) := [(.cell 1, .entry (.live ⟨0, .ram, []⟩ 0))]

/-- The cells trie holding the parent, at Sim's parameters. -/
private abbrev pc (b : Bool) : Cells Sim.D :=
  if b then Trie.build (trieSpec Sim.env) (trieSpec Sim.env).depth 0 parentCells else .empty

private theorem pc_toList : (pc true).toList = parentCells := by
  cases hd : (trieSpec Sim.env).depth <;> simp [pc, parentCells, Trie.build, Trie.mkLeaf, Trie.T.toList, hd]

private theorem pc_fits (b : Bool) : CellsFits Sim.env (fun _ => True) (pc b) := by
  cases b
  · exact ⟨⟨⟨by simp [pc, Trie.T.toList, worldMax], by simp [pc, Trie.T.toList]⟩, by simp [pc, Trie.T.toList]⟩,
      Trie.canon_empty _ 0⟩
  · refine ⟨⟨⟨by rw [pc_toList]; simp [worldMax], fun p hp => ?_⟩, fun p hp => ?_⟩, ?_⟩
    · rw [pc_toList] at hp; simp only [parentCells, List.mem_cons, List.mem_nil_iff, or_false] at hp; subst hp
      exact ⟨trivial, ⟨by decide, by simp [Slots.Fits, Bounds.slotsPerCellMax]⟩, by decide⟩
    · rw [pc_toList] at hp; simp only [parentCells, List.mem_cons, List.mem_nil_iff, or_false] at hp; subst hp; rfl
    · exact Trie.canon_build _ 0 _ (by simp [parentCells])

/-- A World wire at height 7, empty but for its rows and, if `b`, the live parent cell 1. -/
private abbrev wxp (b : Bool) (r : Rows Sim.D) : WorldWire Sim.D :=
  (pc b, (.empty : Journal Sim.D), (.empty : Refusals Sim.D), r, 7, 7, 0, 0, 0)

private abbrev wx (r : Rows Sim.D) : WorldWire Sim.D := wxp true r

private theorem wxp_wireFits (b : Bool) (l : List (RowSlot Sim.D × RowLeaf)) (hl : l.length ≤ worldMax)
    (hn : (l.map Prod.fst).Nodup) (ht : (wr l).toList = l)
    (hp : ∀ p ∈ l, RowSlot.Fits (fun _ => True) p.1 ∧ RowLeaf.Fits p.2) :
    WireFits Sim.env (fun _ => True) (wxp b (wr l)) :=
  ⟨pc_fits b,
    ⟨⟨by simp [Trie.T.toList, Bounds.journalMax, Bounds.windowMax], by simp [Trie.T.toList]⟩, Trie.canon_empty _ 0⟩,
    ⟨⟨by simp [Trie.T.toList, worldMax], by simp [Trie.T.toList]⟩, Trie.canon_empty _ 0⟩,
    ⟨⟨by rw [ht]; exact hl, fun p hp' => hp p (ht ▸ hp')⟩, Trie.canon_build _ 0 l hn⟩,
    show 7 < 2 ^ 64 by decide, show 7 < 2 ^ 64 by decide, trivial, show 0 < 2 ^ 64 by decide, trivial⟩

private theorem wx_wireFits (l : List (RowSlot Sim.D × RowLeaf)) (hl : l.length ≤ worldMax)
    (hn : (l.map Prod.fst).Nodup) (ht : (wr l).toList = l)
    (hp : ∀ p ∈ l, RowSlot.Fits (fun _ => True) p.1 ∧ RowLeaf.Fits p.2) :
    WireFits Sim.env (fun _ => True) (wx (wr l)) :=
  wxp_wireFits true l hl hn ht hp

private abbrev capped (sum : Nat) : List (RowSlot Sim.D × RowLeaf) :=
  [(.head 1 7, .head 1 sum 4 40 2 true 0), (.row ⟨1, 7, ⟨#[3, 4]⟩⟩, .row sum ByteArray.empty 0)]

private theorem wr_capped40 : (wr (capped 40)).toList = capped 40 := by decide +kernel
private theorem wr_capped41 : (wr (capped 41)).toList = capped 41 := by decide +kernel

private theorem capped_wireFits (sum : Nat) (hs : sum < 2 ^ 64) (ht : (wr (capped sum)).toList = capped sum) :
    WireFits Sim.env (fun _ => True) (wx (wr (capped sum))) :=
  wx_wireFits _ (by simp [worldMax]) (by simp [capped]) ht (by
    intro p hp; simp only [capped, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl
    · exact ⟨⟨trivial, by decide⟩, by decide, hs, by decide, by decide, by decide⟩
    · exact ⟨⟨trivial, by decide, by decide⟩, hs, by decide⟩)

private theorem refusals_nil : refusalsFits 7 (Trie.T.empty : Refusals Sim.D).toList = true := by
  simp [refusalsFits, Trie.T.toList]

private theorem disjoint_nil (r : Rows Sim.D) : refusalsDisjoint Sim.env (ofWire (wx r)) = true := by
  simp [refusalsDisjoint, ofWire, Trie.T.toList]

private theorem counted_nil (b : Bool) (r : Rows Sim.D) : refusalsCounted Sim.env (ofWire (wxp b r)) = true := by
  simp [refusalsCounted, ofWire, refusalTally, Trie.T.toList]

/-- **The plant**: a relation whose one row's amount (41) passes its cap (40), its head counting and
summing it, is refused `kernel/rows` by name. -/
theorem world_refuses_sum_past_cap :
    (world Sim.env Sim.dc).decode ((worldWire Sim.env Sim.dc).bytes (wx (wr (capped 41)))) =
      .error (.rejected 0 "kernel/rows") :=
  world_decode_wire_rowsRefused u64_lawful.on (capped_wireFits 41 (by decide) wr_capped41) journalFits_empty
    refusals_nil (disjoint_nil _) (by decide) (counted_nil _ _)
    (by show rowsFits Sim.env (wr (capped 41)).toList = false
        rw [wr_capped41]; decide +kernel)

/-- The twin at the cap: the same relation summing exactly its cap (40) reads back. -/
theorem world_reads_sum_at_cap :
    (world Sim.env Sim.dc).decode ((worldWire Sim.env Sim.dc).bytes (wx (wr (capped 40)))) =
      .ok (ofWire (wx (wr (capped 40)))) :=
  world_decode_wire_ok u64_lawful.on (capped_wireFits 40 (by decide) wr_capped40) journalFits_empty refusals_nil
    (disjoint_nil _) (by decide) (counted_nil _ _)
    (by show rowsFits Sim.env (wr (capped 40)).toList = true
        rw [wr_capped40]; decide +kernel)
    (by show rowsHeaded (wr (capped 40)).toList = true
        rw [wr_capped40]; decide) (by decide +kernel) (by decide +kernel)

private abbrev declared : List (RowSlot Sim.D × RowLeaf) := [(.head 1 7, .head 0 0 4 40 2 true 0)]

private theorem wr_declared : (wr declared).toList = declared := by
  cases hd : (rowSpec Sim.env).depth <;> simp [wr, declared, Trie.build, Trie.mkLeaf, Trie.T.toList, hd]

/-- A declared relation holding no rows (count 0, sum 0) reads back. -/
theorem world_reads_declared_relation :
    (world Sim.env Sim.dc).decode ((worldWire Sim.env Sim.dc).bytes (wx (wr declared))) =
      .ok (ofWire (wx (wr declared))) :=
  world_decode_wire_ok u64_lawful.on
    (wx_wireFits _ (by simp [worldMax]) (by simp) wr_declared (by
      intro p hp; simp only [declared, List.mem_cons, List.mem_nil_iff, or_false] at hp; subst hp
      exact ⟨⟨trivial, by decide⟩, by decide, by decide, by decide, by decide, by decide⟩))
    journalFits_empty refusals_nil (disjoint_nil _) (by decide) (counted_nil _ _)
    (by show rowsFits Sim.env (wr declared).toList = true
        rw [wr_declared]; decide)
    (by show rowsHeaded (wr declared).toList = true
        rw [wr_declared]; decide) (by decide +kernel) (by decide +kernel)

private abbrev headed (count : Nat) : List (RowSlot Sim.D × RowLeaf) :=
  [(.head 1 7, .head count 5 4 40 2 true 0), (.row ⟨1, 7, ⟨#[3, 4]⟩⟩, .row 5 ByteArray.empty 0)]

private theorem wr_headed1 : (wr (headed 1)).toList = headed 1 := by decide +kernel
private theorem wr_headed2 : (wr (headed 2)).toList = headed 2 := by decide +kernel

private theorem headed_wireFits (count : Nat) (hc : count < 2 ^ 64) (ht : (wr (headed count)).toList = headed count) :
    WireFits Sim.env (fun _ => True) (wx (wr (headed count))) :=
  wx_wireFits _ (by simp [worldMax]) (by simp [headed]) ht (by
    intro p hp; simp only [headed, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl
    · exact ⟨⟨trivial, by decide⟩, hc, by decide, by decide, by decide, by decide⟩
    · exact ⟨⟨trivial, by decide, by decide⟩, by decide, by decide⟩)

/-- A head counting and summing its one row reads back: the twin of `world_refuses_uncounted_row`. -/
theorem world_reads_counted_row :
    (world Sim.env Sim.dc).decode ((worldWire Sim.env Sim.dc).bytes (wx (wr (headed 1)))) =
      .ok (ofWire (wx (wr (headed 1)))) :=
  world_decode_wire_ok u64_lawful.on (headed_wireFits 1 (by decide) wr_headed1) journalFits_empty refusals_nil
    (disjoint_nil _) (by decide) (counted_nil _ _)
    (by show rowsFits Sim.env (wr (headed 1)).toList = true
        rw [wr_headed1]; decide +kernel)
    (by show rowsHeaded (wr (headed 1)).toList = true
        rw [wr_headed1]; decide +kernel) (by decide +kernel) (by decide +kernel)

/-- **The plant**: the same relation with its parent absent (no cell 1) is refused `kernel/rows-parented`
by name: a head is born only under a cell its turn creates and goes with its parent, so no fold reaches
it. Its twin is `world_reads_counted_row`. -/
theorem world_refuses_orphan_relation :
    (world Sim.env Sim.dc).decode ((worldWire Sim.env Sim.dc).bytes (wxp false (wr (headed 1)))) =
      .error (.rejected 0 "kernel/rows-parented") :=
  world_decode_wire_parentedRefused u64_lawful.on
    (wxp_wireFits false _ (by simp [worldMax]) (by simp [headed]) wr_headed1 (by
      intro p hp; simp only [headed, List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl
      · exact ⟨⟨trivial, by decide⟩, by decide, by decide, by decide, by decide, by decide⟩
      · exact ⟨⟨trivial, by decide, by decide⟩, by decide, by decide⟩))
    journalFits_empty refusals_nil (by simp [refusalsDisjoint, ofWire, Trie.T.toList]) (by decide) (counted_nil _ _)
    (by show rowsFits Sim.env (wr (headed 1)).toList = true
        rw [wr_headed1]; decide +kernel)
    (by show rowsHeaded (wr (headed 1)).toList = true
        rw [wr_headed1]; decide +kernel) (by decide +kernel)

/-- **The plant**: the same head counting two rows (it holds one) is refused `kernel/rows-headed`. -/
theorem world_refuses_uncounted_row :
    (world Sim.env Sim.dc).decode ((worldWire Sim.env Sim.dc).bytes (wx (wr (headed 2)))) =
      .error (.rejected 0 "kernel/rows-headed") :=
  world_decode_wire_headedRefused u64_lawful.on (headed_wireFits 2 (by decide) wr_headed2) journalFits_empty
    refusals_nil (disjoint_nil _) (by decide) (counted_nil _ _)
    (by show rowsFits Sim.env (wr (headed 2)).toList = true
        rw [wr_headed2]; decide +kernel)
    (by show rowsHeaded (wr (headed 2)).toList = false
        rw [wr_headed2]; decide +kernel)

/-- **The plant**: the rows listing in the other order (the row before its head) is refused
`kernel/row-order` by name. -/
theorem rows_refuses_swapped_listing :
    (match (rowsTrie Sim.env Sim.dc).decode
        ((rawList worldMax (product (rowKey Sim.dc) rowLeaf)).bytes (headed 1).reverse) with
     | .error (.rejected _ "kernel/row-order") => true
     | _ => false) = true := by decide +kernel

/-- The canonical order reads back. -/
theorem rows_reads_canonical_listing :
    (match (rowsTrie Sim.env Sim.dc).decode
        ((rawList worldMax (product (rowKey Sim.dc) rowLeaf)).bytes (headed 1)) with
     | .ok t => t.toList == headed 1
     | .error _ => false) = true := by decide +kernel

/-- **The plant**: a row key whose length varint claims 129 bytes (`81 01`, cv 01a14f7e), one past
`Bounds.keyBytesMax`, is refused `pastBound` at that length, before any key byte is read. -/
theorem rowKey_refuses_wide_key :
    (match (rowKey Sim.dc).decode (Sim.dc.bytes 1 ++ ⟨#[7, 1, 0x81, 0x01]⟩) with
     | .error (.pastBound _ 128 129) => true
     | _ => false) = true := by decide +kernel

/-- **The plant** (cv 01a14f7e): relation 256 as its varint (`80 02`) is refused `kernel/row-key` by
name. Under the one-byte relation it wrapped to relation 0; as a varint it is its own number, and the
kernel's bound refuses it. -/
theorem rowKey_refuses_relation_256 :
    (match (rowKey Sim.dc).decode (Sim.dc.bytes 1 ++ ⟨#[0x80, 0x02, 0]⟩) with
     | .error (.rejected _ "kernel/row-key") => true
     | _ => false) = true := by decide +kernel

/-- The twin: relation 255 (`ff 01`, two bytes) reads back as the head of relation 255. -/
theorem rowKey_reads_relation_255 :
    (match (rowKey Sim.dc).decode (Sim.dc.bytes 1 ++ ⟨#[0xff, 0x01, 0]⟩) with
     | .ok s => decide (s = .head 1 255)
     | .error _ => false) = true := by decide +kernel

/-- The twin: a key of exactly `Bounds.keyBytesMax` bytes is within the codec's domain, so it reads back. -/
theorem rowKey_reads_widest_key (k : ByteArray) (hk : k.size = Bounds.keyBytesMax) :
    (rowKey Sim.dc).decode ((rowKey Sim.dc).bytes (.row ⟨1, 7, k⟩)) = .ok (.row ⟨1, 7, k⟩) :=
  (rowKey_lawfulOn u64_lawful.on).decode_bytes ⟨trivial, show (7 : Nat) < 256 by decide, Nat.le_of_eq hk⟩

/-! ### The kind byte is load-bearing (KERNEL-17's ask, for `rows_separateOn`) -/

/-- The rows key bytes WITHOUT the kind byte: a head `parent ‖ rel`, a row `parent ‖ rel ‖ |k| ‖ k`. -/
private def keyNoKind (E : Env Sim.D) : RowSlot Sim.D → ByteArray
  | .head p rel => E.bytes p ++ byte8 rel
  | .row key => E.bytes key.parent ++ byte8 key.rel ++ byte8 key.k.size ++ key.k

private theorem byteBit_append_zero (a : ByteArray) (i : Nat) : byteBit (a ++ ⟨#[0]⟩) i = byteBit a i := by
  unfold byteBit
  by_cases h1 : i / 8 < a.size
  · have h2 : i / 8 < (a ++ ⟨#[0]⟩).size := by simp [ByteArray.size_append]; omega
    rw [dif_pos h2, dif_pos h1, ByteArray.getElem_append_left h1]
  · rw [dif_neg h1]
    by_cases h3 : i / 8 < (a ++ ⟨#[0]⟩).size
    · rw [dif_pos h3]
      have he : i / 8 = a.size := by simp [ByteArray.size_append] at h3; omega
      have : (a ++ ⟨#[0]⟩)[i / 8] = 0 := by
        rw [ByteArray.getElem_append_right (by omega)]; simp [he]
      rw [this]; simp
    · rw [dif_neg h3]

/-- **The tooth**: without the kind byte, the head of relation 7 under parent 1 and the row of that
relation with the empty key are two different keys within bounds whose bits agree everywhere (`byteBit`
reads past a string's end as 0, and the row's length byte is 0), so the rows trie could not separate
them. KERNEL's `rows_separateOn` (Kernel/Proofs/RowsSep.lean) rests on the kind byte. -/
theorem rows_kindByte_needed :
    RowSlot.Fits (fun _ => True) (RowSlot.head (1 : Sim.D) 7) ∧
      RowSlot.Fits (fun _ => True) (RowSlot.row ⟨(1 : Sim.D), 7, ByteArray.empty⟩) ∧
      RowSlot.head (1 : Sim.D) 7 ≠ RowSlot.row ⟨1, 7, ByteArray.empty⟩ ∧
      ∀ i, byteBit (keyNoKind Sim.env (.head 1 7)) i = byteBit (keyNoKind Sim.env (.row ⟨1, 7, ByteArray.empty⟩)) i := by
  refine And.intro (by simp [RowSlot.Fits]) (And.intro (by simp [RowSlot.Fits]) (And.intro ?_ fun i => ?_))
  · intro h; cases h
  have e : keyNoKind Sim.env (.row ⟨1, 7, ByteArray.empty⟩) = keyNoKind Sim.env (.head 1 7) ++ ⟨#[0]⟩ := by
    simp only [keyNoKind, byte8, ByteArray.append_empty, ByteArray.size_empty]; rfl
  rw [e, byteBit_append_zero]

/-- The carried twin: a carried state whose head counts its one row reads back, exactly. -/
theorem carried_reads_counted_row :
    (carried Sim.env Sim.dc).decode ((carriedWire Sim.env Sim.dc).bytes (pc true, 5, 7, .empty, wr (headed 1))) =
      .ok ⟨pc true, 5, 7, .empty, wr (headed 1)⟩ := by
  have hw := headed_wireFits 1 (by decide) wr_headed1
  show (carried Sim.env Sim.dc).decode ((carried Sim.env Sim.dc).bytes ⟨pc true, 5, 7, .empty, wr (headed 1)⟩) = _
  exact carried_decode_bytes u64_lawful.on ⟨hw.1, show 5 < 2 ^ 64 by decide, show 7 < 2 ^ 64 by decide, hw.2.1,
    by simp [journalFits, Trie.T.toList, ascendingNat],
    ⟨hw.2.2.2.1, by show rowsFits Sim.env (wr (headed 1)).toList = true
                    rw [wr_headed1]; decide +kernel,
     by show rowsHeaded (wr (headed 1)).toList = true
        rw [wr_headed1]; decide +kernel,
     by decide +kernel⟩⟩

/-- **The plant**: the same carried state without its parent cell is refused
`kernel/carried-rows-parented` by name. -/
theorem carried_refuses_orphan_relation :
    (carried Sim.env Sim.dc).decode ((carriedWire Sim.env Sim.dc).bytes (.empty, 5, 7, .empty, wr (headed 1))) =
      .error (.rejected 0 "kernel/carried-rows-parented") := by
  have hw := wxp_wireFits false (headed 1) (by simp [worldMax]) (by simp [headed]) wr_headed1 (by
      intro p hp; simp only [headed, List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl
      · exact ⟨⟨trivial, by decide⟩, by decide, by decide, by decide, by decide, by decide⟩
      · exact ⟨⟨trivial, by decide, by decide⟩, by decide, by decide⟩)
  exact carried_decode_wire_parentedRefused u64_lawful.on
    ⟨hw.1, show 5 < 2 ^ 64 by decide, show 7 < 2 ^ 64 by decide, hw.2.1, hw.2.2.2.1⟩
    (by simp [journalFits, carriedOfWire, Trie.T.toList, ascendingNat])
    (by show rowsFits Sim.env (wr (headed 1)).toList = true
        rw [wr_headed1]; decide +kernel)
    (by show rowsHeaded (wr (headed 1)).toList = true
        rw [wr_headed1]; decide +kernel)
    (by decide +kernel)

/-- **The plant**: a carried state whose relation sums past its cap is refused `kernel/carried-rows`. -/
theorem carried_refuses_sum_past_cap :
    (carried Sim.env Sim.dc).decode ((carriedWire Sim.env Sim.dc).bytes (pc true, 5, 7, .empty, wr (capped 41))) =
      .error (.rejected 0 "kernel/carried-rows") := by
  have hw := capped_wireFits 41 (by decide) wr_capped41
  exact carried_decode_wire_rowsRefused u64_lawful.on
    ⟨hw.1, show 5 < 2 ^ 64 by decide, show 7 < 2 ^ 64 by decide, hw.2.1, hw.2.2.2.1⟩
    (by simp [journalFits, carriedOfWire, Trie.T.toList, ascendingNat])
    (by show rowsFits Sim.env (wr (capped 41)).toList = false
        rw [wr_capped41]; decide +kernel)

/-- **The plant**: a carried state whose rows hold a head counting a row it does not hold is refused
`kernel/carried-rows-headed`, before any import could genesis-write a Store from it. -/
theorem carried_refuses_uncounted_row :
    (carried Sim.env Sim.dc).decode ((carriedWire Sim.env Sim.dc).bytes (pc true, 5, 7, .empty, wr (headed 2))) =
      .error (.rejected 0 "kernel/carried-rows-headed") := by
  have hw := headed_wireFits 2 (by decide) wr_headed2
  exact carried_decode_wire_headedRefused u64_lawful.on
    ⟨hw.1, show 5 < 2 ^ 64 by decide, show 7 < 2 ^ 64 by decide, hw.2.1, hw.2.2.2.1⟩
    (by simp [journalFits, carriedOfWire, Trie.T.toList, ascendingNat])
    (by show rowsFits Sim.env (wr (headed 2)).toList = true
        rw [wr_headed2]; decide +kernel)
    (by show rowsHeaded (wr (headed 2)).toList = false
        rw [wr_headed2]; decide +kernel)

/-! ## The proof wire's teeth (KERNEL-49 (a), `kernel/proof`)

A path's bits must ascend below the trie's depth: each plant beside the twin it differs from by one
bit. -/

/-- The deepest bit a journal node can branch on (`journalDepth - 1`) reads back. -/
theorem proof_reads_deepest_bit :
    (match (proof (journalSpec Sim.env) Sim.dc Sim.dc).decode
        ((proofWire Bounds.journalDepth Sim.dc Sim.dc).bytes (some [(0, 0)], [(Bounds.journalDepth - 1, 0)])) with
     | .ok p => p.sibs == [(Bounds.journalDepth - 1, 0)]
     | .error _ => false) = true := by decide +kernel

/-- The plant: one bit past it (`journalDepth`) is refused `kernel/proof` by name. -/
theorem proof_refuses_past_depth :
    (match (proof (journalSpec Sim.env) Sim.dc Sim.dc).decode
        ((proofWire Bounds.journalDepth Sim.dc Sim.dc).bytes (some [(0, 0)], [(Bounds.journalDepth, 0)])) with
     | .error (.rejected _ "kernel/proof") => true
     | _ => false) = true := by decide +kernel

/-- Two siblings at ascending bits over a leaf read back. -/
theorem proof_reads_ascending_bits :
    (match (proof (journalSpec Sim.env) Sim.dc Sim.dc).decode
        ((proofWire Bounds.journalDepth Sim.dc Sim.dc).bytes (some [(0, 0)], [(5, 0), (6, 1)])) with
     | .ok p => p.sibs == [(5, 0), (6, 1)]
     | .error _ => false) = true := by decide +kernel

/-- The plant: the same two siblings at one bit twice are refused `kernel/proof` by name (a node's
child branches below it). -/
theorem proof_refuses_repeated_bit :
    (match (proof (journalSpec Sim.env) Sim.dc Sim.dc).decode
        ((proofWire Bounds.journalDepth Sim.dc Sim.dc).bytes (some [(0, 0)], [(5, 0), (5, 1)])) with
     | .error (.rejected _ "kernel/proof") => true
     | _ => false) = true := by decide +kernel

/-- The empty trie's proof (no sibling) reads back. -/
theorem proof_reads_empty_trie :
    (match (proof (journalSpec Sim.env) Sim.dc Sim.dc).decode
        ((proofWire Bounds.journalDepth Sim.dc Sim.dc).bytes (none, [])) with
     | .ok p => p.term.isNone && p.sibs.isEmpty
     | .error _ => false) = true := by decide +kernel

/-- The plant: an empty end under a sibling is refused `kernel/proof` by name (no node has an empty
child). -/
theorem proof_refuses_empty_under_sibling :
    (match (proof (journalSpec Sim.env) Sim.dc Sim.dc).decode
        ((proofWire Bounds.journalDepth Sim.dc Sim.dc).bytes (none, [(5, 0)])) with
     | .error (.rejected _ "kernel/proof") => true
     | _ => false) = true := by decide +kernel

/-- The plant: a leaf with no entry is refused `kernel/proof` by name (no leaf is empty). -/
theorem proof_refuses_empty_leaf :
    (match (proof (journalSpec Sim.env) Sim.dc Sim.dc).decode
        ((proofWire Bounds.journalDepth Sim.dc Sim.dc).bytes (some [], [(5, 0)])) with
     | .error (.rejected _ "kernel/proof") => true
     | _ => false) = true := by decide +kernel

end Nanodregg.Codec.Kernel
