import Codec.Proofs.Refine
import Codec.Proofs.World
import Kernel.Sim

/-!
# Teeth for the refinements' lawfulness theorems (CODEC-28)

Each tooth takes a refinement as built, mutates only its `accept` in the way a careless edit would,
and proves the mutant is NOT lawful on the predicate the refinement's lawfulness theorem states. The
mutant keeps the name, so it keeps the shape and the tag: without the theorem, nothing would refuse
it. The kernel codecs are taken at `Kernel.Sim`'s toy parameters (`D = UInt64`, `dc = u64`).

The last pair is the residue the tag and every theorem miss: `slot` with its two kinds swapped in
BOTH `accept` and `back` is lawful on the same predicate, has the same shape, and writes different
bytes for the same value (`slot_relabel_unseen`).
-/

namespace Nanodregg.Codec.Kernel

open Nanodregg.Kernel Nanodregg.Codec.Stream

/-- `bool` admitting every nonzero byte as `true` (a second spelling of `true`) is not lawful. -/
theorem bool_tooth :
    ¬ LawfulOn (fun _ => True)
      (refine "bool" u8 (fun x => if x = 0 then some false else some true) (fun v => if v then 1 else 0)) :=
  refine_not_lawful_of_respells u8_lawful.on (fun _ _ => trivial) (x := 2) trivial (y := true)
    (by decide) (by decide)

/-- `kernel/discipline` reading every byte past 2 as `value` is not lawful. -/
theorem discipline_tooth :
    ¬ LawfulOn (fun _ => True)
      (refine (β := Discipline) "kernel/discipline" u8
        (fun t => if t = 0 then some .rom else if t = 1 then some .appendOnly else if t = 2 then some .ram
          else some .value)
        (fun | .rom => 0 | .appendOnly => 1 | .ram => 2 | .value => 3)) :=
  refine_not_lawful_of_respells u8_lawful.on (fun _ _ => trivial) (x := 4) trivial (y := .value)
    (by decide) (by decide)

/-- `kernel/leaf-fit` without its check admits a nullifier slot holding a cell entry. -/
theorem leafFit_tooth :
    ¬ LawfulOn (fun l => TrieListFits (fun _ : Sim.D => True) l ∧ ∀ p ∈ l, Leaf.fits p.1 p.2 = true)
      (refine "kernel/leaf-fit" (rawList worldMax (product (slot Sim.dc) leaf)) (fun l => some l) id) :=
  refine_not_lawful_of_admits
    (rawList_lawfulOn (product_lawfulOn (slot_lawfulOn u64_lawful.on) leaf_lawfulOn) worldMax (by decide))
    (fun _ h => ⟨h.1.1, fun p hp => h.1.2 p hp⟩)
    (x := [(.nullifier 0, .entry .tomb)]) ⟨by decide, by simp [Entry.Fits, Leaf.Fits]⟩ rfl
    (fun h => absurd (h.2 _ (List.mem_singleton_self _)) (by decide))

/-- `kernel/trie-order` keeping the rebuild but dropping the listing check admits the two-slot
listing in the wrong order: a second spelling of the same trie. -/
theorem trieOrder_tooth :
    ¬ LawfulOn (CellsFits Sim.env (fun _ => True))
      (refine "kernel/trie-order" (fitList Sim.dc)
        (fun l => some (Trie.build (trieSpec Sim.env) (trieSpec Sim.env).depth 0 l)) Trie.T.toList) :=
  refine_not_lawful_of_respells (fitList_lawfulOn u64_lawful.on) (fun _ h => h.1)
    (x := [(.nullifier 0, .spent), (.cell 0, .entry .tomb)])
    ⟨⟨by decide, by simp [Entry.Fits, Leaf.Fits]⟩, by decide⟩ rfl (by decide +kernel)

/-- `kernel/journal-order` keeping the rebuild but dropping the listing check admits two journal
entries in the wrong order: a second spelling of the same journal trie (KERNEL-41). -/
theorem journalOrder_tooth :
    ¬ LawfulOn (JournalTrieFits Sim.env (fun _ => True))
      (refine "kernel/journal-order" (rawList Bounds.journalMax (product Sim.dc (product nat64 Sim.dc)))
        (fun l => some (Trie.build (journalSpec Sim.env) (journalSpec Sim.env).depth 0 l)) Trie.T.toList) :=
  refine_not_lawful_of_respells
    (rawList_lawfulOn (product_lawfulOn u64_lawful.on (product_lawfulOn nat64_lawfulOn u64_lawful.on))
      Bounds.journalMax (by decide))
    (fun _ h => h.1)
    (x := [(2, (5, 6)), (1, (2, 3))]) ⟨by decide, by decide⟩ rfl (by decide +kernel)

/-! ## An iso refinement: what is refuted, and what is not -/

/-- `kernel/slot` with the kinds swapped in `accept` alone reads a cell id back as a nullifier: not
lawful. -/
theorem slot_tooth :
    ¬ LawfulOn (fun _ : Slot Sim.D => True)
      (refine "kernel/slot" (choice 2 fun _ => Sim.dc)
        (fun | ⟨0, c⟩ => some (.nullifier c) | ⟨1, n⟩ => some (.cell n))
        (fun | .cell c => ⟨0, c⟩ | .nullifier n => ⟨1, n⟩)) :=
  refine_not_lawful_of_respells (choice_lawfulOn 2 (by decide) (P := fun _ _ => True) (fun _ => u64_lawful.on))
    (fun _ _ => trivial) (x := ⟨0, 0⟩) trivial (y := .nullifier 0) rfl (by decide)

/-- **The residue (CODEC-28).** `kernel/slot` with its kinds swapped in BOTH `accept` and `back` is
lawful on the same predicate as `slot`, has the same shape (so the same tag under any label), and
spells the same value differently: a stored cell slot would be read back as a nullifier. No
lawfulness theorem refutes it; only the name could have said so. -/
theorem slot_relabel_unseen :
    let r : Stream (Slot Sim.D) := refine "kernel/slot" (choice 2 fun _ => Sim.dc)
      (fun | ⟨0, n⟩ => some (.nullifier n) | ⟨1, c⟩ => some (.cell c))
      (fun | .nullifier n => ⟨0, n⟩ | .cell c => ⟨1, c⟩)
    LawfulOn (fun _ => True) r ∧ r.shape = (slot Sim.dc).shape ∧ r.bytes (.cell 0) ≠ (slot Sim.dc).bytes (.cell 0) := by
  refine ⟨?_, rfl, by decide⟩
  refine (refine_lawfulOn (choice_lawfulOn 2 (by decide) (P := fun _ _ => True) (fun _ => u64_lawful.on))
    "kernel/slot" ?_ ?_).mono (fun _ _ => trivial) (fun _ _ => trivial)
  · intro y _; cases y <;> rfl
  · intro x y h
    match x, y, h with
    | ⟨0, _⟩, _, h => cases h; rfl
    | ⟨1, _⟩, _, h => cases h; rfl

end Nanodregg.Codec.Kernel
