import Codec.Proofs.World

/-!
# The carried codec (CODEC-22): canonical, the trie read back exactly, the journal up to `Equiv`

* `carriedWire_lawfulOn`: the wire `trie ‖ allowance ‖ height ‖ journal` is lawful on its domain, so on the
  wire `decode b = .ok x ↔ b = bytes x` exactly (`carriedWire_decode_iff`).
* `carried_decode_iff` — canonicity of the carried state: for a fitting `c`, bytes `b` decode to a state
  `Equiv` to `c` exactly when `b` is `c`'s bytes; `eq_bytes_of_carried_decode`: whatever decodes IS the
  encoding of what it decoded to. (The journal is a `TreeMap`, whose balancing is not its contents, so
  equality of decoded maps is `Equiv`; everything else — the trie, the counters — is `=`.)
* `carried_bytes_equiv`: `Equiv` states have the same bytes, so HOST's byte comparison on import is the
  contents comparison.
* `carried_decode_canon`: a decoded trie is canonical and every slot holds the leaf of its kind.
* `carried_fits`: the carried state of a fitting World whose journal is under `Bounds.journalMax` (every
  reached World: `Kernel.reach_journal_bounded`) is in the codec's domain.
-/

namespace Nanodregg.Codec.Kernel

open Nanodregg.Kernel Nanodregg.Codec.Stream Std

variable {D : Type} [Ord D] [DecidableEq D]

/-- Two carried states with the same trie and counters and `Equiv` journals. -/
def CarriedEquiv (a b : Carried D) : Prop :=
  a.trie = b.trie ∧ a.allowance = b.allowance ∧ a.height = b.height ∧ a.journal.Equiv b.journal

/-- The wire's domain, as the product of its parts. -/
def CarriedWireFits (E : Env D) (PD : D → Prop) (x : CarriedWire D) : Prop :=
  CellsFits E PD x.1 ∧ x.2.1 < 2 ^ 64 ∧ x.2.2.1 < 2 ^ 64 ∧
  ((x.2.2.2.length ≤ Bounds.journalMax ∧ ∀ p ∈ x.2.2.2, PD p.1 ∧ p.2.1 < 2 ^ 64 ∧ PD p.2.2) ∧
    ascendingBy Prod.fst x.2.2.2 = true)

/-- A carried state in the codec's domain: a canonical trie whose slots hold the leaves of their kinds,
counters below 2^64, at most `Bounds.journalMax` journal entries, every digest in the digest codec's domain. -/
def Carried.CodecFits (E : Env D) (PD : D → Prop) (c : Carried D) : Prop :=
  CellsFits E PD c.trie ∧ c.allowance < 2 ^ 64 ∧ c.height < 2 ^ 64 ∧
  (c.journal.toList.length ≤ Bounds.journalMax ∧ ∀ p ∈ c.journal.toList, PD p.1 ∧ p.2.1 < 2 ^ 64 ∧ PD p.2.2)

theorem carriedWire_lawfulOn (E : Env D) {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc) :
    LawfulOn (CarriedWireFits E PD) (carriedWire E dc) :=
  (product_lawfulOn (cells_lawfulOn E hd)
    (product_lawfulOn nat64_lawfulOn (product_lawfulOn nat64_lawfulOn
      (ascendingList_lawfulOn (product_lawfulOn hd (product_lawfulOn nat64_lawfulOn hd)) _ (by decide) _)))).mono
    (fun _ h => h) (fun _ h => h)

/-- On the wire, canonicity is exact. -/
theorem carriedWire_decode_iff (E : Env D) {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc)
    {b : ByteArray} {x : CarriedWire D} (hx : CarriedWireFits E PD x) :
    (carriedWire E dc).decode b = .ok x ↔ b = (carriedWire E dc).bytes x :=
  ⟨fun h => ((carriedWire_lawfulOn E hd).eq_bytes_of_decode h).2,
   fun h => h ▸ (carriedWire_lawfulOn E hd).decode_bytes hx⟩

theorem carried_bytes (E : Env D) (dc : Stream D) (c : Carried D) :
    (carried E dc).bytes c = (carriedWire E dc).bytes (carriedToWire c) := rfl

theorem carried_decode (E : Env D) (dc : Stream D) (b : ByteArray) :
    (carried E dc).decode b = match (carriedWire E dc).decode b with
      | .ok x => .ok (carriedOfWire x)
      | .error e => .error e := by
  unfold decode
  simp only [carried]
  split <;> rename_i h <;> split at h <;> simp_all <;> split <;> simp_all

variable [TransOrd D] [LawfulEqOrd D]

omit [DecidableEq D] [LawfulEqOrd D] in
theorem carriedToWire_fits {E : Env D} {PD : D → Prop} {c : Carried D} (hc : Carried.CodecFits E PD c) :
    CarriedWireFits E PD (carriedToWire c) :=
  ⟨hc.1, hc.2.1, hc.2.2.1, ⟨hc.2.2.2, ascendingBy_iff.mpr TreeMap.ordered_keys_toList⟩⟩

theorem carriedOfWire_toWire_equiv (c : Carried D) : CarriedEquiv (carriedOfWire (carriedToWire c)) c :=
  ⟨rfl, rfl, rfl, TreeMap.equiv_iff_toList_eq.mpr (toList_ofList_of_sorted _ TreeMap.ordered_keys_toList)⟩

theorem carriedToWire_ofWire {E : Env D} {PD : D → Prop} {x : CarriedWire D} (hx : CarriedWireFits E PD x) :
    carriedToWire (carriedOfWire x) = x := by
  obtain ⟨t, a, h, j⟩ := x
  simp only [carriedToWire, carriedOfWire]
  rw [toList_ofList_of_sorted _ (ascendingBy_iff.mp hx.2.2.2.2)]

omit [LawfulEqOrd D] in
/-- `Equiv` carried states have the same bytes. -/
theorem carried_bytes_equiv (E : Env D) (dc : Stream D) {c c' : Carried D} (h : CarriedEquiv c c') :
    (carried E dc).bytes c = (carried E dc).bytes c' := by
  obtain ⟨ht, ha, hh, hj⟩ := h
  rw [carried_bytes, carried_bytes]
  simp only [carriedToWire, ht, ha, hh, hj.toList_eq]

/-- A fitting carried state reads back from its bytes: the same trie and counters, an `Equiv` journal. -/
theorem carried_decode_bytes {E : Env D} {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc)
    {c : Carried D} (hc : Carried.CodecFits E PD c) :
    ∃ c', (carried E dc).decode ((carried E dc).bytes c) = .ok c' ∧ CarriedEquiv c' c := by
  refine ⟨carriedOfWire (carriedToWire c), ?_, carriedOfWire_toWire_equiv c⟩
  rw [carried_decode, carried_bytes, (carriedWire_lawfulOn E hd).decode_bytes (carriedToWire_fits hc)]

/-- Whatever decodes to `c` is exactly `c`'s bytes. -/
theorem eq_bytes_of_carried_decode {E : Env D} {PD : D → Prop} {dc : Stream D}
    (hd : LawfulOn PD dc) {b : ByteArray} {c : Carried D} (h : (carried E dc).decode b = .ok c) :
    b = (carried E dc).bytes c := by
  rw [carried_decode] at h
  split at h
  · rename_i x hx
    cases h
    obtain ⟨hf, rfl⟩ := (carriedWire_lawfulOn E hd).eq_bytes_of_decode hx
    rw [carried_bytes, carriedToWire_ofWire hf]
  · cases h

/-- **Canonicity**: for a fitting `c`, `b` decodes to a state `Equiv` to `c` exactly when `b` is `c`'s
bytes. -/
theorem carried_decode_iff {E : Env D} {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc)
    {b : ByteArray} {c : Carried D} (hc : Carried.CodecFits E PD c) :
    (∃ c', (carried E dc).decode b = .ok c' ∧ CarriedEquiv c' c) ↔ b = (carried E dc).bytes c := by
  constructor
  · rintro ⟨c', h, he⟩
    rw [eq_bytes_of_carried_decode hd h, carried_bytes_equiv E dc he]
  · rintro rfl
    exact carried_decode_bytes hd hc

omit [TransOrd D] [LawfulEqOrd D] in
/-- A decoded trie is canonical (the kernel's `Trie.Canon`) and every slot holds the leaf of its kind. -/
theorem carried_decode_canon {E : Env D} {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc)
    {b : ByteArray} {c : Carried D} (h : (carried E dc).decode b = .ok c) :
    Trie.Canon (trieSpec E) 0 c.trie ∧ ∀ p ∈ c.trie.toList, Leaf.fits p.1 p.2 = true := by
  rw [carried_decode] at h
  split at h
  · rename_i x hx
    cases h
    obtain ⟨hf, _⟩ := (carriedWire_lawfulOn E hd).eq_bytes_of_decode hx
    exact ⟨hf.1.2, hf.1.1.2⟩
  · cases h

omit [TransOrd D] [LawfulEqOrd D] [DecidableEq D] in
/-- The carried state of a fitting World whose journal is under `Bounds.journalMax` is in the codec's domain. -/
theorem carried_fits {E : Env D} {PD : D → Prop} {w : World D} (hw : World.CodecFits E PD w)
    (hj : w.journal.size < Bounds.journalMax) : Carried.CodecFits E PD w.carried :=
  ⟨hw.1, hw.2.2.2.2.1, hw.2.2.1, ⟨Nat.le_of_lt (by rw [TreeMap.length_toList]; exact hj), hw.2.1.2⟩⟩

end Nanodregg.Codec.Kernel
