import Codec.Proofs.World

/-!
# The carried codec (CODEC-22, KERNEL-41): canonical, both tries read back exactly

* `carried_lawfulOn`: the carried codec `trie ‖ allowance ‖ height ‖ journal` is lawful on
  `Carried.CodecFits`, so `decode b = .ok c ↔ b = bytes c` exactly (`carried_decode_iff`): with the
  journal a trie (KERNEL-41), the `CarriedEquiv` of CODEC-22 is gone.
* `carried_decode_journalFits`: a decoded carried journal is the window's at the carried height
  (`kernel/carried-journal`; `carried_decode_wire_refused` is the refusal).
* `carried_decode_canon`: a decoded cells trie is canonical and every slot holds the leaf of its kind;
  `carried_decode_journalCanon`: a decoded journal trie is canonical.
* `carried_fits`: the carried state of a fitting World is in the codec's domain.
-/

namespace Nanodregg.Codec.Kernel

open Nanodregg.Kernel Nanodregg.Codec.Stream

variable {D : Type} [Ord D] [DecidableEq D]

/-- The wire's domain, as the product of its parts. -/
def CarriedWireFits (E : Env D) (PD : D → Prop) (x : CarriedWire D) : Prop :=
  CellsFits E PD x.1 ∧ x.2.1 < 2 ^ 64 ∧ x.2.2.1 < 2 ^ 64 ∧ JournalTrieFits E PD x.2.2.2

/-- A carried state in the codec's domain: a canonical cells trie whose slots hold the leaves of their
kinds, counters below 2^64, a canonical journal trie of at most `Bounds.journalMax` entries, every
digest in the digest codec's domain, and a journal that is the window's at the carried height. -/
def Carried.CodecFits (E : Env D) (PD : D → Prop) (c : Carried D) : Prop :=
  CellsFits E PD c.trie ∧ c.allowance < 2 ^ 64 ∧ c.height < 2 ^ 64 ∧ JournalTrieFits E PD c.journal ∧
    journalFits c.height c.journal.toList = true

omit [Ord D] in
theorem carriedWire_lawfulOn (E : Env D) {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc) :
    LawfulOn (CarriedWireFits E PD) (carriedWire E dc) :=
  (product_lawfulOn (cells_lawfulOn E hd)
    (product_lawfulOn nat64_lawfulOn (product_lawfulOn nat64_lawfulOn (journalTrie_lawfulOn E hd)))).mono
    (fun _ h => h) (fun _ h => h)

omit [Ord D] in
/-- **`kernel/carried-journal` is lawful on exactly the journals `journalFits` admits at the carried
height.** -/
theorem carriedJournalWire_lawfulOn (E : Env D) {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc) :
    LawfulOn (fun x => CarriedWireFits E PD x ∧ journalFits x.2.2.1 x.2.2.2.toList = true)
      (carriedJournalWire E dc) := by
  unfold carriedJournalWire
  refine (refine_lawfulOn_where (carriedWire_lawfulOn E hd) "kernel/carried-journal"
    (Q := fun x : CarriedWire D => journalFits x.2.2.1 x.2.2.2.toList = true) ?_ ?_ ?_).mono
    (fun _ h => h) (fun _ h => h)
  · intro y _ hq; simp [hq]
  · intro x y h; split at h <;> simp_all
  · intro x y h; split at h
    · rename_i hq; cases h; exact hq
    · cases h

/-- **The carried codec is lawful on `Carried.CodecFits`.** -/
theorem carried_lawfulOn (E : Env D) {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc) :
    LawfulOn (Carried.CodecFits E PD) (carried E dc) := by
  unfold carried
  refine (refine_lawfulOn (carriedJournalWire_lawfulOn E hd) "kernel/carried" ?_ ?_).mono ?_ ?_
  · intro y _; rfl
  · intro x y h; cases h; rfl
  · intro c h; exact ⟨h.1.1, h.1.2.1, h.1.2.2.1, h.1.2.2.2, h.2⟩
  · intro c h; exact ⟨⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩, h.2.2.2.2⟩

theorem carried_bytes (E : Env D) (dc : Stream D) (c : Carried D) :
    (carried E dc).bytes c = (carriedWire E dc).bytes (carriedToWire c) := rfl

/-- **A decoded carried state's journal is the window's at its height** (HOST-11's find): an import
never genesis-writes a Store whose base the World codec would then refuse `kernel/journal`. -/
theorem carried_decode_journalFits {E : Env D} {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc)
    {b : ByteArray} {c : Carried D} (h : (carried E dc).decode b = .ok c) :
    journalFits c.height c.journal.toList = true :=
  ((carried_lawfulOn E hd).eq_bytes_of_decode h).1.2.2.2.2

/-- **The refusal**: a carried wire value whose journal is not the window's at its height is refused
`kernel/carried-journal` by name, at offset 0. -/
theorem carried_decode_wire_refused {E : Env D} {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc)
    {x : CarriedWire D} (hx : CarriedWireFits E PD x) (hj : journalFits x.2.2.1 x.2.2.2.toList = false) :
    (carried E dc).decode ((carriedWire E dc).bytes x) = .error (.rejected 0 "kernel/carried-journal") := by
  have hg := (carriedWire_lawfulOn E hd).get_of_occurs x ((carriedWire E dc).bytes x) 0 hx (occursAt_self _)
  simp only [carried, decode, carriedJournalWire, refine, hg, hj]
  rfl

/-- A fitting carried state reads back from its bytes, exactly. -/
theorem carried_decode_bytes {E : Env D} {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc)
    {c : Carried D} (hc : Carried.CodecFits E PD c) : (carried E dc).decode ((carried E dc).bytes c) = .ok c :=
  (carried_lawfulOn E hd).decode_bytes hc

/-- Whatever decodes to `c` is exactly `c`'s bytes. -/
theorem eq_bytes_of_carried_decode {E : Env D} {PD : D → Prop} {dc : Stream D}
    (hd : LawfulOn PD dc) {b : ByteArray} {c : Carried D} (h : (carried E dc).decode b = .ok c) :
    b = (carried E dc).bytes c :=
  ((carried_lawfulOn E hd).eq_bytes_of_decode h).2

/-- **Canonicity, exactly**: for a fitting `c`, `b` decodes to `c` iff `b` is `c`'s bytes. -/
theorem carried_decode_iff {E : Env D} {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc)
    {b : ByteArray} {c : Carried D} (hc : Carried.CodecFits E PD c) :
    (carried E dc).decode b = .ok c ↔ b = (carried E dc).bytes c :=
  ⟨eq_bytes_of_carried_decode hd, fun h => h ▸ carried_decode_bytes hd hc⟩

/-- A decoded cells trie is canonical (the kernel's `Trie.Canon`) and every slot holds the leaf of its kind. -/
theorem carried_decode_canon {E : Env D} {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc)
    {b : ByteArray} {c : Carried D} (h : (carried E dc).decode b = .ok c) :
    Trie.Canon (trieSpec E) 0 c.trie ∧ ∀ p ∈ c.trie.toList, Leaf.fits p.1 p.2 = true :=
  let hf := ((carried_lawfulOn E hd).eq_bytes_of_decode h).1
  ⟨hf.1.2, hf.1.1.2⟩

/-- A decoded journal trie is canonical. -/
theorem carried_decode_journalCanon {E : Env D} {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc)
    {b : ByteArray} {c : Carried D} (h : (carried E dc).decode b = .ok c) :
    Trie.Canon (journalSpec E) 0 c.journal :=
  ((carried_lawfulOn E hd).eq_bytes_of_decode h).1.2.2.2.1.2

/-- The carried state of a fitting World is in the codec's domain. -/
theorem carried_fits {E : Env D} {PD : D → Prop} {w : World D} (hw : World.CodecFits E PD w) :
    Carried.CodecFits E PD w.carried :=
  ⟨hw.cells, Nat.lt_of_le_of_lt (Nat.le_add_left _ _) hw.budget, hw.height, hw.journal, hw.journalFits⟩

end Nanodregg.Codec.Kernel
