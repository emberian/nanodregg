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
    WireFits Sim.env (fun _ => True) (.empty, jt l, (.empty : Refusals Sim.D), 7, 7, 0, 0, 0) :=
  ⟨⟨⟨⟨by simp [Trie.T.toList, worldMax], by simp [Trie.T.toList]⟩, by simp [Trie.T.toList]⟩,
    Trie.canon_empty _ 0⟩,
    ⟨⟨by rw [ht]; exact hl, fun p hp' => ⟨trivial, hp p (ht ▸ hp'), trivial⟩⟩, Trie.canon_build _ 0 l hn⟩,
    ⟨⟨by simp [Trie.T.toList, worldMax], by simp [Trie.T.toList]⟩, Trie.canon_empty _ 0⟩,
    show 7 < 2 ^ 64 by decide, show 7 < 2 ^ 64 by decide, trivial, show 0 < 2 ^ 64 by decide, trivial⟩

/-- A journal inside the window decodes: entries at heights 6 and 7 of a World at height 7. -/
theorem world_reads_windowed_journal :
    (world Sim.env Sim.dc).decode ((worldWire Sim.env Sim.dc).bytes (.empty, jt [(1, (6, 3)), (2, (7, 4))], (.empty : Refusals Sim.D), 7, 7, 0, 0, 0)) =
      .ok (ofWire (.empty, jt [(1, (6, 3)), (2, (7, 4))], (.empty : Refusals Sim.D), 7, 7, 0, 0, 0)) :=
  world_decode_wire_ok u64_lawful.on (jt_wireFits _ (by decide) (by decide) jt_window (by decide))
    (by show journalFits 7 (jt [(1, (6, 3)), (2, (7, 4))]).toList = true
        rw [jt_window]; simp [journalFits, List.mergeSort, ascendingNat, Bounds.windowMax])
    (by simp [refusalsFits, Trie.T.toList]) (by simp [refusalsDisjoint, ofWire, Trie.T.toList])
    (by decide) (by decide)

/-- The plant: an entry above the World's height (never pruned, `replayed` forever) is refused
`kernel/journal` by name. -/
theorem world_refuses_future_entry :
    (world Sim.env Sim.dc).decode ((worldWire Sim.env Sim.dc).bytes (.empty, jt [(1, (8, 3))], (.empty : Refusals Sim.D), 7, 7, 0, 0, 0)) =
      .error (.rejected 0 "kernel/journal") :=
  world_decode_wire_refused u64_lawful.on (jt_wireFits _ (by decide) (by decide) (jt_one _ _ _) (by decide))
    (by show journalFits 7 (jt [(1, (8, 3))]).toList = false
        rw [jt_one]; exact journalFits_future 7 1 3)

/-- Two entries at one height (two admissions in one turn) are refused `kernel/journal`. -/
theorem world_refuses_shared_height :
    (world Sim.env Sim.dc).decode ((worldWire Sim.env Sim.dc).bytes (.empty, jt [(1, (7, 3)), (2, (7, 4))], (.empty : Refusals Sim.D), 7, 7, 0, 0, 0)) =
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

/-! ## The refusals' teeth (KERNEL-44, KERNEL-47)

A World at height 7 (window 0) whose refusals hold one refused call and one member's count. The
per-window budget's boundary: a count of `Bounds.refusalsPerWindow` (16) reads back, 17 is refused
`kernel/refusals`; so is a refusal recorded above the height it could have been admitted at, and a
`tx` key holding a count. A height above the step count is refused `kernel/steps`. -/

/-- The canonical refusals trie of a listing, at Sim's parameters. -/
private abbrev rt (l : List (RefusalSlot Sim.D × RefusalLeaf)) : Refusals Sim.D :=
  Trie.build (refusalSpec Sim.env) (refusalSpec Sim.env).depth 0 l

/-- A World wire at height 7, empty cells and journal, with refusals `r` and `steps` steps. -/
private abbrev rx (r : Refusals Sim.D) (steps : Nat) : WorldWire Sim.D :=
  (.empty, (.empty : Journal Sim.D), r, 7, steps, 0, 0, 0)

private theorem rx_wireFits (l : List (RefusalSlot Sim.D × RefusalLeaf)) (steps : Nat) (hst : steps < 2 ^ 64)
    (hl : l.length ≤ worldMax) (hn : (l.map Prod.fst).Nodup) (ht : (rt l).toList = l)
    (hp : ∀ p ∈ l, RefusalLeaf.Fits p.2) :
    WireFits Sim.env (fun _ => True) (rx (rt l) steps) :=
  ⟨⟨⟨⟨by simp [Trie.T.toList, worldMax], by simp [Trie.T.toList]⟩, by simp [Trie.T.toList]⟩,
    Trie.canon_empty _ 0⟩,
    ⟨⟨by simp [Trie.T.toList, Bounds.journalMax, Bounds.windowMax], by simp [Trie.T.toList]⟩, Trie.canon_empty _ 0⟩,
    ⟨⟨by rw [ht]; exact hl, fun p hp' => by
        refine ⟨?_, hp p (ht ▸ hp')⟩
        cases p.1 <;> trivial⟩, Trie.canon_build _ 0 l hn⟩,
    show 7 < 2 ^ 64 by decide, hst, trivial, show 0 < 2 ^ 64 by decide, trivial⟩

private abbrev atCount (n : Nat) : List (RefusalSlot Sim.D × RefusalLeaf) :=
  [(.tx 1, .refused 7 3), (.count 2 0, .count n)]

private theorem rt_atCount16 : (rt (atCount 16)).toList = atCount 16 := by
  decide +kernel

private theorem rt_atCount17 : (rt (atCount 17)).toList = atCount 17 := by
  decide +kernel

private theorem atCount_fits (n : Nat) (hn : n < 2 ^ 64) : ∀ p ∈ atCount n, RefusalLeaf.Fits p.2 := by
  intro p hp
  simp only [atCount, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl
  · exact ⟨by decide, by decide⟩
  · exact hn

private theorem atCount_wireFits (n : Nat) (hn : n < 2 ^ 64) (ht : (rt (atCount n)).toList = atCount n) :
    WireFits Sim.env (fun _ => True) (rx (rt (atCount n)) 7) :=
  rx_wireFits _ 7 (by decide) (by simp [worldMax]) (by simp [atCount]) ht (atCount_fits n hn)

private theorem journalFits_empty : journalFits 7 (Trie.T.empty : Journal Sim.D).toList = true := by
  simp [journalFits, Trie.T.toList, ascendingNat]

/-- At the per-window budget: a member's count of exactly `Bounds.refusalsPerWindow` reads back. -/
theorem world_reads_refusals_at_budget :
    (world Sim.env Sim.dc).decode ((worldWire Sim.env Sim.dc).bytes (rx (rt (atCount 16)) 7)) =
      .ok (ofWire (rx (rt (atCount 16)) 7)) :=
  world_decode_wire_ok u64_lawful.on (atCount_wireFits 16 (by decide) rt_atCount16) journalFits_empty
    (by show refusalsFits 7 (rt (atCount 16)).toList = true
        rw [rt_atCount16]; decide)
    (by decide +kernel) (by decide) (by decide)

/-- **The plant**: one past the budget, a count of 17, is refused `kernel/refusals` by name. -/
theorem world_refuses_count_past_budget :
    (world Sim.env Sim.dc).decode ((worldWire Sim.env Sim.dc).bytes (rx (rt (atCount 17)) 7)) =
      .error (.rejected 0 "kernel/refusals") :=
  world_decode_wire_refusalsRefused u64_lawful.on (atCount_wireFits 17 (by decide) rt_atCount17) journalFits_empty
    (by show refusalsFits 7 (rt (atCount 17)).toList = false
        rw [rt_atCount17]; decide)

private theorem rt_one (k : RefusalSlot Sim.D) (v : RefusalLeaf) : (rt [(k, v)]).toList = [(k, v)] := by
  cases hd : (refusalSpec Sim.env).depth <;> simp [rt, Trie.build, Trie.mkLeaf, Trie.T.toList, hd]

/-- **The plant**: a call recorded refused at height 9 in a World at height 7 (above `height + 1`, the
height it could have been admitted at) is refused `kernel/refusals`. -/
theorem world_refuses_future_refusal :
    (world Sim.env Sim.dc).decode ((worldWire Sim.env Sim.dc).bytes (rx (rt [(.tx 1, .refused 9 3)]) 7)) =
      .error (.rejected 0 "kernel/refusals") :=
  world_decode_wire_refusalsRefused u64_lawful.on
    (rx_wireFits _ 7 (by decide) (by simp [worldMax]) (by simp) (rt_one _ _)
      (by intro p hp; simp at hp; subst hp; exact ⟨by decide, by decide⟩))
    journalFits_empty
    (by show refusalsFits 7 (rt [(.tx 1, .refused 9 3)]).toList = false
        rw [rt_one]; decide)

/-- **The plant**: a refused-call key holding a count is refused `kernel/refusals`. -/
theorem world_refuses_misfit_refusal :
    (world Sim.env Sim.dc).decode ((worldWire Sim.env Sim.dc).bytes (rx (rt [(.tx 1, .count 1)]) 7)) =
      .error (.rejected 0 "kernel/refusals") :=
  world_decode_wire_refusalsRefused u64_lawful.on
    (rx_wireFits _ 7 (by decide) (by simp [worldMax]) (by simp) (rt_one _ _)
      (by intro p hp; simp at hp; subst hp; show 1 < 2 ^ 64; decide))
    journalFits_empty
    (by show refusalsFits 7 (rt [(.tx 1, .count 1)]).toList = false
        rw [rt_one]; decide)

/-- **The plant**: a World at height 7 that has taken 6 steps is refused `kernel/steps`; at 7 steps
(`world_reads_refusals_at_budget`) it reads back. -/
theorem world_refuses_height_past_steps :
    (world Sim.env Sim.dc).decode ((worldWire Sim.env Sim.dc).bytes (rx .empty 6)) =
      .error (.rejected 0 "kernel/steps") :=
  world_decode_wire_stepsRefused u64_lawful.on
    (rx_wireFits [] 6 (by decide) (by simp) (by simp) (by simp [rt, Trie.build, Trie.T.toList]) (by simp))
    journalFits_empty (by simp [refusalsFits, Trie.T.toList])
    (by simp [refusalsDisjoint, ofWire, Trie.T.toList]) (by decide)

/-- **The plant**: the refusals listing in the other order is refused `kernel/refusal-order` by name. -/
theorem refusals_refuses_swapped_listing :
    (match (refusalsTrie Sim.env Sim.dc).decode
        ((rawList worldMax (product (refusalSlot Sim.dc) refusalLeaf)).bytes
          [(.count 2 0, .count 1), (.tx 1, .refused 7 3)]) with
     | .error (.rejected _ "kernel/refusal-order") => true
     | _ => false) = true := by decide +kernel

/-- The canonical order reads back. -/
theorem refusals_reads_canonical_listing :
    (match (refusalsTrie Sim.env Sim.dc).decode
        ((rawList worldMax (product (refusalSlot Sim.dc) refusalLeaf)).bytes
          [(.tx 1, .refused 7 3), (.count 2 0, .count 1)]) with
     | .ok t => t.toList == [(.tx 1, .refused 7 3), (.count 2 0, .count 1)]
     | .error _ => false) = true := by decide +kernel

/-- **The plant**: transaction id 1 both journaled (admitted at height 7) and recorded refused is
refused `kernel/refusals-disjoint` by name; no fold reaches it (KERNEL's `fold_refusalsDisjoint`). -/
theorem world_refuses_refused_and_journaled :
    (world Sim.env Sim.dc).decode ((worldWire Sim.env Sim.dc).bytes
        (.empty, jt [(1, (7, 3))], rt [(.tx 1, .refused 7 3)], 7, 7, 0, 0, 0)) =
      .error (.rejected 0 "kernel/refusals-disjoint") := by
  have hj := jt_wireFits [(1, (7, 3))] (by decide) (by decide) (jt_one _ _ _) (by decide)
  have hr := rx_wireFits [(.tx 1, .refused 7 3)] 7 (by decide) (by simp [worldMax]) (by simp) (rt_one _ _)
    (by intro p hp; simp at hp; subst hp; exact ⟨by decide, by decide⟩)
  exact world_decode_wire_disjointRefused u64_lawful.on
    ⟨hj.1, hj.2.1, hr.2.2.1, hj.2.2.2⟩
    (by show journalFits 7 (jt [(1, (7, 3))]).toList = true
        rw [jt_one]; simp [journalFits, ascendingNat, Bounds.windowMax])
    (by show refusalsFits 7 (rt [(.tx 1, .refused 7 3)]).toList = true
        rw [rt_one]; decide)
    (by decide +kernel)

/-! ### The window's edges, and each accepted twin (the vacuity read's finding 6)

`ry H r steps` is the World wire at height `H`. At `H = 4096` (a window boundary, `H % 1024 = 0`) a call
refused at height 2049 is still kept (`4096 < 2049 + 2048`) and one refused at 2048 is stale. -/

private abbrev ry (H : Nat) (r : Refusals Sim.D) (steps : Nat) : WorldWire Sim.D :=
  (.empty, (.empty : Journal Sim.D), r, H, steps, 0, 0, 0)

private theorem ry_one_wireFits (H : Nat) (hH : H < 2 ^ 64) (k : RefusalSlot Sim.D) (v : RefusalLeaf)
    (hv : RefusalLeaf.Fits v) : WireFits Sim.env (fun _ => True) (ry H (rt [(k, v)]) H) :=
  ⟨⟨⟨⟨by simp [Trie.T.toList, worldMax], by simp [Trie.T.toList]⟩, by simp [Trie.T.toList]⟩,
    Trie.canon_empty _ 0⟩,
    ⟨⟨by simp [Trie.T.toList, Bounds.journalMax, Bounds.windowMax], by simp [Trie.T.toList]⟩, Trie.canon_empty _ 0⟩,
    ⟨⟨by rw [rt_one]; simp [worldMax], fun p hp' => by
        rw [rt_one] at hp'; simp at hp'; subst hp'
        exact ⟨by cases k <;> trivial, hv⟩⟩, Trie.canon_build _ 0 _ (by simp)⟩,
    hH, hH, trivial, show 0 < 2 ^ 64 by decide, trivial⟩

private theorem journalFits_nil (H : Nat) : journalFits H (Trie.T.empty : Journal Sim.D).toList = true := by
  simp [journalFits, Trie.T.toList, ascendingNat]

/-- A call refused at `height + 1` (8, at height 7), the height it would have been admitted at, reads
back: the accepted twin of `world_refuses_future_refusal`. -/
theorem world_reads_refusal_at_next_height :
    (world Sim.env Sim.dc).decode ((worldWire Sim.env Sim.dc).bytes (ry 7 (rt [(.tx 1, .refused 8 3)]) 7)) =
      .ok (ofWire (ry 7 (rt [(.tx 1, .refused 8 3)]) 7)) :=
  world_decode_wire_ok u64_lawful.on (ry_one_wireFits 7 (by decide) _ _ ⟨by decide, by decide⟩)
    (journalFits_nil 7) (by rw [rt_one]; decide) (by decide +kernel) (by decide) (by decide)

/-- At a window boundary, a call refused 2048 heights ago is still kept (2049 at height 4096)... -/
theorem world_reads_refusal_at_window_edge :
    (world Sim.env Sim.dc).decode ((worldWire Sim.env Sim.dc).bytes (ry 4096 (rt [(.tx 1, .refused 2049 3)]) 4096)) =
      .ok (ofWire (ry 4096 (rt [(.tx 1, .refused 2049 3)]) 4096)) :=
  world_decode_wire_ok u64_lawful.on (ry_one_wireFits 4096 (by decide) _ _ ⟨by decide, by decide⟩)
    (journalFits_nil 4096) (by rw [rt_one]; decide) (by decide +kernel) (by decide) (by decide)

/-- **The plant**: ...and one height older (2048) is stale, refused `kernel/refusals` (it should have
been pruned). -/
theorem world_refuses_stale_refusal :
    (world Sim.env Sim.dc).decode ((worldWire Sim.env Sim.dc).bytes (ry 4096 (rt [(.tx 1, .refused 2048 3)]) 4096)) =
      .error (.rejected 0 "kernel/refusals") :=
  world_decode_wire_refusalsRefused u64_lawful.on (ry_one_wireFits 4096 (by decide) _ _ ⟨by decide, by decide⟩)
    (journalFits_nil 4096) (by rw [rt_one]; decide)

/-- A count for the current window (0, at height 7) reads back... -/
theorem world_reads_current_window_count :
    (world Sim.env Sim.dc).decode ((worldWire Sim.env Sim.dc).bytes (ry 7 (rt [(.count 2 0, .count 1)]) 7)) =
      .ok (ofWire (ry 7 (rt [(.count 2 0, .count 1)]) 7)) :=
  world_decode_wire_ok u64_lawful.on (ry_one_wireFits 7 (by decide) _ _ (show _ < 2 ^ 64 by decide))
    (journalFits_nil 7) (by rw [rt_one]; decide) (by decide +kernel) (by decide) (by decide)

/-- **The plant**: ...and a count for another window (1) is refused `kernel/refusals`. -/
theorem world_refuses_past_window_count :
    (world Sim.env Sim.dc).decode ((worldWire Sim.env Sim.dc).bytes (ry 7 (rt [(.count 2 1, .count 1)]) 7)) =
      .error (.rejected 0 "kernel/refusals") :=
  world_decode_wire_refusalsRefused u64_lawful.on (ry_one_wireFits 7 (by decide) _ _ (show _ < 2 ^ 64 by decide))
    (journalFits_nil 7) (by rw [rt_one]; decide)

/-- **The plant**: a count of 0 (a key the kernel never writes) is refused `kernel/refusals`. -/
theorem world_refuses_zero_count :
    (world Sim.env Sim.dc).decode ((worldWire Sim.env Sim.dc).bytes (ry 7 (rt [(.count 2 0, .count 0)]) 7)) =
      .error (.rejected 0 "kernel/refusals") :=
  world_decode_wire_refusalsRefused u64_lawful.on (ry_one_wireFits 7 (by decide) _ _ (show _ < 2 ^ 64 by decide))
    (journalFits_nil 7) (by rw [rt_one]; decide)

/-- **The plant**: a count key holding a refused leaf is refused `kernel/refusals` (the other misfit). -/
theorem world_refuses_misfit_count_key :
    (world Sim.env Sim.dc).decode ((worldWire Sim.env Sim.dc).bytes (ry 7 (rt [(.count 2 0, .refused 7 3)]) 7)) =
      .error (.rejected 0 "kernel/refusals") :=
  world_decode_wire_refusalsRefused u64_lawful.on (ry_one_wireFits 7 (by decide) _ _ ⟨by decide, by decide⟩)
    (journalFits_nil 7) (by rw [rt_one]; decide)

/-- The accepted twin of `world_refuses_height_past_steps`: the same World with 7 steps reads back. -/
theorem world_reads_height_eq_steps :
    (world Sim.env Sim.dc).decode ((worldWire Sim.env Sim.dc).bytes (rx .empty 7)) =
      .ok (ofWire (rx .empty 7)) :=
  world_decode_wire_ok u64_lawful.on
    (rx_wireFits [] 7 (by decide) (by simp) (by simp) (by simp [rt, Trie.build, Trie.T.toList]) (by simp))
    journalFits_empty (by simp [refusalsFits, Trie.T.toList])
    (by simp [refusalsDisjoint, ofWire, Trie.T.toList]) (by decide) (by decide)

/-- The accepted twin of `world_refuses_refused_and_journaled`: id 1 journaled, id 2 refused. -/
theorem world_reads_refused_not_journaled :
    (world Sim.env Sim.dc).decode ((worldWire Sim.env Sim.dc).bytes
        (.empty, jt [(1, (7, 3))], rt [(.tx 2, .refused 7 3)], 7, 7, 0, 0, 0)) =
      .ok (ofWire (.empty, jt [(1, (7, 3))], rt [(.tx 2, .refused 7 3)], 7, 7, 0, 0, 0)) := by
  have hj := jt_wireFits [(1, (7, 3))] (by decide) (by decide) (jt_one _ _ _) (by decide)
  have hr := rx_wireFits [(.tx 2, .refused 7 3)] 7 (by decide) (by simp [worldMax]) (by simp) (rt_one _ _)
    (by intro p hp; simp at hp; subst hp; exact ⟨by decide, by decide⟩)
  exact world_decode_wire_ok u64_lawful.on
    ⟨hj.1, hj.2.1, hr.2.2.1, hj.2.2.2⟩
    (by show journalFits 7 (jt [(1, (7, 3))]).toList = true
        rw [jt_one]; simp [journalFits, ascendingNat, Bounds.windowMax])
    (by show refusalsFits 7 (rt [(.tx 2, .refused 7 3)]).toList = true
        rw [rt_one]; decide)
    (by decide +kernel) (by decide) (by decide)

/-- **The plant**: a call recorded refused at height 0 (a fold records `height + 1 ≥ 1`) is refused
`kernel/refusals`. -/
theorem world_refuses_refusal_at_zero :
    (world Sim.env Sim.dc).decode ((worldWire Sim.env Sim.dc).bytes (ry 7 (rt [(.tx 1, .refused 0 3)]) 7)) =
      .error (.rejected 0 "kernel/refusals") :=
  world_decode_wire_refusalsRefused u64_lawful.on (ry_one_wireFits 7 (by decide) _ _ ⟨by decide, by decide⟩)
    (journalFits_nil 7) (by rw [rt_one]; decide)

end Nanodregg.Codec.Kernel
